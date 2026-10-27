module

public import CFSG.Quasithin.Background.JonesParshallBasic
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Quasithin.JonesParshall

section Ext

variable {V : Type} [CommGroup V] [Finite V]

@[expose] noncomputable def muW {L : Subgroup (MulAut V)} {W : Subgroup V}
    (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W) : ↥L →* AddMonoid.End (Additive ↥W) where
  toFun g := AddMonoidHom.mk'
    (fun x => Additive.ofMul (⟨(g : MulAut V) (Additive.toMul x : ↥W), hLW g g.2 _ (Subtype.property _)⟩ : ↥W))
    (fun x y => by
      apply Additive.toMul.injective
      apply Subtype.ext
      simp)
  map_one' := by
    ext x
    rfl
  map_mul' g h := by
    ext x
    rfl

omit [Finite V] in
theorem muW_apply {L : Subgroup (MulAut V)} {W : Subgroup V} (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W)
    (g : ↥L) (x : Additive ↥W) :
    Additive.toMul (muW hLW g x) = ⟨(g : MulAut V) (Additive.toMul x : ↥W),
      hLW g g.2 _ (Subtype.property _)⟩ := rfl

omit [Finite V] in
theorem muW_sub_apply {L : Subgroup (MulAut V)} {W : Subgroup V} (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W)
    (g : ↥L) (x : Additive ↥W) :
    ((Additive.toMul (muW hLW g x - x) : ↥W) : V) =
      (g : MulAut V) ((Additive.toMul x : ↥W) : V) * ((Additive.toMul x : ↥W) : V)⁻¹ := by
  simp [toMul_sub, muW_apply, div_eq_mul_inv]

omit [Finite V] in
theorem cocy_mem_Z1A {L : Subgroup (MulAut V)} {W : Subgroup V} (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W)
    (hc : ∀ g ∈ L, ∀ v : V, g v * v⁻¹ ∈ W) (v : V) :
    (fun g : ↥L => Additive.ofMul (⟨(g : MulAut V) v * v⁻¹, hc g g.2 v⟩ : ↥W)) ∈ Z1A (muW hLW) := by
  intro g h
  apply Additive.toMul.injective
  apply Subtype.ext
  show ((g * h : ↥L) : MulAut V) v * v⁻¹ =
    ((g : MulAut V) v * v⁻¹) * ((g : MulAut V) ((h : MulAut V) v * v⁻¹))
  simp only [Subgroup.coe_mul, MulAut.mul_apply, map_mul, map_inv]
  simp [mul_comm, mul_left_comm]

omit [Finite V] in
theorem mem_sup_fixV_of_B1A {L : Subgroup (MulAut V)} {W : Subgroup V}
    (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W) (hc : ∀ g ∈ L, ∀ v : V, g v * v⁻¹ ∈ W) (v : V)
    (hv : (fun g : ↥L => Additive.ofMul (⟨(g : MulAut V) v * v⁻¹, hc g g.2 v⟩ : ↥W)) ∈ B1A (muW hLW)) :
    v ∈ W ⊔ fixV L := by
  obtain ⟨m, hm⟩ := hv
  have hm' : ∀ g : ↥L, (g : MulAut V) v * v⁻¹ =
      (g : MulAut V) ((Additive.toMul m : ↥W) : V) * ((Additive.toMul m : ↥W) : V)⁻¹ := by
    intro g
    have h1 := congrArg (fun x : Additive ↥W => ((Additive.toMul x : ↥W) : V)) (congrFun hm g)
    simp only [coboundaryA_apply] at h1
    rw [muW_sub_apply] at h1
    exact h1.symm
  have hfix : v * ((Additive.toMul m : ↥W) : V)⁻¹ ∈ fixV L := by
    intro x hx
    have h3 := hm' ⟨x, hx⟩
    have h4 := (div_eq_div_iff_div_eq_div (a := x v) (b := v)
      (c := x ((Additive.toMul m : ↥W) : V)) (d := ((Additive.toMul m : ↥W) : V))).1
      (by simpa [div_eq_mul_inv] using h3)
    rw [map_mul, map_inv]
    simpa [div_eq_mul_inv] using h4
  have : v = (v * ((Additive.toMul m : ↥W) : V)⁻¹) * ((Additive.toMul m : ↥W) : V) := by
    simp
  rw [this, mul_comm]
  exact Subgroup.mul_mem_sup (Additive.toMul m : ↥W).2 hfix

omit [Finite V] in
theorem sup_fixV_eq_top_of_R {L A : Subgroup (MulAut V)} {W : Subgroup V}
    (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W) (hc : ∀ g ∈ L, ∀ v : V, g v * v⁻¹ ∈ W)
    (hA : W ⊔ fixV A = ⊤)
    (hR : ∀ f ∈ Z1A (muW hLW), (∃ m : Additive ↥W, ∀ a : ↥L, (a : MulAut V) ∈ A →
      f a = muW hLW a m - m) → f ∈ B1A (muW hLW)) : W ⊔ fixV L = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hv : v ∈ W ⊔ fixV A := by rw [hA]; trivial
  obtain ⟨w, hw, z, hz, rfl⟩ := Subgroup.mem_sup.1 hv
  refine mem_sup_fixV_of_B1A hLW hc _ (hR _ (cocy_mem_Z1A hLW hc (w * z)) ⟨Additive.ofMul ⟨w, hw⟩, ?_⟩)
  intro a ha
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [muW_sub_apply]
  show (a : MulAut V) (w * z) * (w * z)⁻¹ = (a : MulAut V) w * w⁻¹
  rw [map_mul, hz _ ha, mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]

omit [Finite V] in
theorem muW_two {W : Subgroup V} (hV : ∀ v : V, v ^ 2 = 1) (m : Additive ↥W) : m + m = 0 := by
  apply Additive.toMul.injective
  apply Subtype.ext
  show (Additive.toMul m : ↥W).1 * (Additive.toMul m : ↥W).1 = 1
  rw [← sq]
  exact hV _

theorem sup_fixV_eq_top_of_odd {L S : Subgroup (MulAut V)} {W : Subgroup V}
    (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W) (hc : ∀ g ∈ L, ∀ v : V, g v * v⁻¹ ∈ W)
    (hV : ∀ v : V, v ^ 2 = 1) (hodd : Odd (S.subgroupOf L).index) (hS : W ⊔ fixV S = ⊤) :
    W ⊔ fixV L = ⊤ :=
  sup_fixV_eq_top_of_R hLW hc hS fun _ hf ⟨m, hm⟩ =>
    mem_B1A_of_restrict (μ := muW hLW) (muW_two hV) (H := S.subgroupOf L) hodd hf (m := m) hm

omit [Finite V] in
theorem sup_fixV_eq_top_of_h1 {L : Subgroup (MulAut V)} {W : Subgroup V}
    (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W) (hc : ∀ g ∈ L, ∀ v : V, g v * v⁻¹ ∈ W)
    (hH1 : ∀ f ∈ Z1A (muW hLW), f ∈ B1A (muW hLW)) : W ⊔ fixV L = ⊤ := by
  rw [eq_top_iff]
  intro v _
  exact mem_sup_fixV_of_B1A hLW hc v (hH1 _ (cocy_mem_Z1A hLW hc v))

omit [Finite V] in
theorem exists_proj {X Y W : Subgroup V} (hsup : X ⊔ Y = W) (hinf : X ⊓ Y = ⊥) :
    ∃ p : ↥W →* ↥X, ∀ (x : V) (hx : x ∈ X) (y : V) (hy : y ∈ Y),
      p ⟨x * y, hsup ▸ Subgroup.mul_mem_sup hx hy⟩ = ⟨x, hx⟩ := by
  classical
  have hdec : ∀ w : ↥W, ∃ x ∈ X, ∃ y ∈ Y, x * y = (w : V) := fun w => by
    have h : (w : V) ∈ X ⊔ Y := by rw [hsup]; exact w.2
    exact Subgroup.mem_sup.1 h
  have huniq : ∀ x ∈ X, ∀ x' ∈ X, ∀ y ∈ Y, ∀ y' ∈ Y, x * y = x' * y' → x = x' := by
    intro x hx x' hx' y hy y' hy' h
    have h1 : x'⁻¹ * x ∈ X ⊓ Y := by
      refine ⟨X.mul_mem (X.inv_mem hx') hx, ?_⟩
      have : x'⁻¹ * x = y' * y⁻¹ := by
        have h2 : x = x' * y' * y⁻¹ := by rw [← h]; simp
        rw [h2, mul_assoc, inv_mul_cancel_left]
      rw [this]
      exact Y.mul_mem hy' (Y.inv_mem hy)
    rw [hinf, Subgroup.mem_bot] at h1
    exact (inv_mul_eq_one.1 h1).symm
  refine ⟨
    { toFun := fun w => ⟨(hdec w).choose, (hdec w).choose_spec.1⟩
      map_one' := ?_
      map_mul' := ?_ }, ?_⟩
  · apply Subtype.ext
    obtain ⟨hx, y, hy, hxy⟩ := (hdec 1).choose_spec
    have := huniq _ hx 1 X.one_mem _ hy 1 Y.one_mem (by rw [hxy]; simp)
    exact this
  · intro w w'
    apply Subtype.ext
    obtain ⟨hx, y, hy, hxy⟩ := (hdec w).choose_spec
    obtain ⟨hx', y', hy', hxy'⟩ := (hdec w').choose_spec
    obtain ⟨hx'', y'', hy'', hxy''⟩ := (hdec (w * w')).choose_spec
    refine huniq _ hx'' _ (X.mul_mem hx hx') _ hy'' (y * y') (Y.mul_mem hy hy') ?_
    calc (hdec (w * w')).choose * y'' = (w : V) * (w' : V) := hxy''
      _ = ((hdec w).choose * y) * ((hdec w').choose * y') := by rw [hxy, hxy']
      _ = ((hdec w).choose * (hdec w').choose) * (y * y') := mul_mul_mul_comm _ _ _ _
  · intro x hx y hy
    apply Subtype.ext
    obtain ⟨hx', y', hy', hxy'⟩ := (hdec ⟨x * y, hsup ▸ Subgroup.mul_mem_sup hx hy⟩).choose_spec
    exact huniq _ hx' x hx _ hy' y hy hxy'

omit [Finite V] in
theorem exists_proj_pair {X Y W : Subgroup V} (hsup : X ⊔ Y = W) (hinf : X ⊓ Y = ⊥) :
    ∃ (pX : ↥W →* ↥X) (pY : ↥W →* ↥Y), (∀ w : ↥W, (w : V) = (pX w : V) * (pY w : V)) ∧
      ∀ (w : ↥W) (x : V), x ∈ X → ∀ y : V, y ∈ Y → (w : V) = x * y → (pX w : V) = x := by
  obtain ⟨pX, hpX⟩ := exists_proj hsup hinf
  obtain ⟨pY, hpY⟩ := exists_proj (X := Y) (Y := X) (W := W) (by rw [sup_comm]; exact hsup)
    (by rw [inf_comm]; exact hinf)
  have hdec : ∀ w : ↥W, (w : V) = (pX w : V) * (pY w : V) := by
    intro w
    have h : (w : V) ∈ X ⊔ Y := by rw [hsup]; exact w.2
    obtain ⟨x, hx, y, hy, hxy⟩ := Subgroup.mem_sup.1 h
    have hw : w = ⟨x * y, hsup ▸ Subgroup.mul_mem_sup hx hy⟩ := Subtype.ext hxy.symm
    have hpy := hpY y hy x hx
    have hpy' : pY ⟨x * y, hsup ▸ Subgroup.mul_mem_sup hx hy⟩ = ⟨y, hy⟩ := by
      rw [← hpy]
      exact congrArg pY (Subtype.ext (mul_comm x y))
    rw [hw, hpX x hx y hy, hpy']
  refine ⟨pX, pY, hdec, fun w x hx y hy hw => ?_⟩
  have hw' : w = ⟨x * y, hsup ▸ Subgroup.mul_mem_sup hx hy⟩ := Subtype.ext hw
  rw [hw', hpX x hx y hy]

omit [Finite V] in
theorem hR_of_directSum {L A : Subgroup (MulAut V)} {X Y W : Subgroup V}
    (hsup : X ⊔ Y = W) (hinf : X ⊓ Y = ⊥)
    (hLX : ∀ g ∈ L, ∀ w ∈ X, g w ∈ X) (hLY : ∀ g ∈ L, ∀ w ∈ Y, g w ∈ Y)
    (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W)
    (hRX : ∀ f ∈ Z1A (muW hLX), (∃ m : Additive ↥X, ∀ a : ↥L, (a : MulAut V) ∈ A →
      f a = muW hLX a m - m) → f ∈ B1A (muW hLX))
    (hRY : ∀ f ∈ Z1A (muW hLY), (∃ m : Additive ↥Y, ∀ a : ↥L, (a : MulAut V) ∈ A →
      f a = muW hLY a m - m) → f ∈ B1A (muW hLY)) :
    ∀ f ∈ Z1A (muW hLW), (∃ m : Additive ↥W, ∀ a : ↥L, (a : MulAut V) ∈ A →
      f a = muW hLW a m - m) → f ∈ B1A (muW hLW) := by
  obtain ⟨pX, pY, hdec, huniq⟩ := exists_proj_pair hsup hinf
  have hXW : X ≤ W := hsup ▸ le_sup_left
  have hYW : Y ≤ W := hsup ▸ le_sup_right
  have heqX : ∀ (g : ↥L) (w : ↥W), (pX ⟨(g : MulAut V) w, hLW g g.2 w w.2⟩ : V) =
      (g : MulAut V) (pX w : V) := by
    intro g w
    refine huniq _ _ (hLX g g.2 _ (pX w).2) _ (hLY g g.2 _ (pY w).2) ?_
    show (g : MulAut V) (w : V) = _
    rw [hdec w, map_mul]
  have heqY : ∀ (g : ↥L) (w : ↥W), (pY ⟨(g : MulAut V) w, hLW g g.2 w w.2⟩ : V) =
      (g : MulAut V) (pY w : V) := by
    intro g w
    have h1 := hdec ⟨(g : MulAut V) w, hLW g g.2 w w.2⟩
    rw [heqX g w] at h1
    have h2 : (g : MulAut V) (w : V) = (g : MulAut V) (pX w : V) * (g : MulAut V) (pY w : V) := by
      rw [hdec w, map_mul]
    have h3 : (g : MulAut V) (pX w : V) * (pY ⟨(g : MulAut V) w, hLW g g.2 w w.2⟩ : V) =
        (g : MulAut V) (pX w : V) * (g : MulAut V) (pY w : V) := by
      rw [← h1]
      exact h2
    exact mul_left_cancel h3
  intro f hf ⟨m₀, hm₀⟩
  let fX : ↥L → Additive ↥X := fun a => Additive.ofMul (pX (Additive.toMul (f a)))
  let fY : ↥L → Additive ↥Y := fun a => Additive.ofMul (pY (Additive.toMul (f a)))
  have hfX : fX ∈ Z1A (muW hLX) := by
    intro a b
    apply Additive.toMul.injective
    apply Subtype.ext
    show (pX (Additive.toMul (f (a * b))) : V) =
      (pX (Additive.toMul (f a)) : V) * (a : MulAut V) (pX (Additive.toMul (f b)) : V)
    rw [hf a b, toMul_add, map_mul, Subgroup.coe_mul]
    congr 1
    exact heqX a _
  have hfY : fY ∈ Z1A (muW hLY) := by
    intro a b
    apply Additive.toMul.injective
    apply Subtype.ext
    show (pY (Additive.toMul (f (a * b))) : V) =
      (pY (Additive.toMul (f a)) : V) * (a : MulAut V) (pY (Additive.toMul (f b)) : V)
    rw [hf a b, toMul_add, map_mul, Subgroup.coe_mul]
    congr 1
    exact heqY a _
  have hresX : ∃ m : Additive ↥X, ∀ a : ↥L, (a : MulAut V) ∈ A → fX a = muW hLX a m - m := by
    refine ⟨Additive.ofMul (pX (Additive.toMul m₀)), fun a ha => ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [muW_sub_apply]
    show (pX (Additive.toMul (f a)) : V) =
      (a : MulAut V) (pX (Additive.toMul m₀) : V) * (pX (Additive.toMul m₀) : V)⁻¹
    rw [hm₀ a ha, toMul_sub, muW_apply, map_div, Subgroup.coe_div, heqX a, div_eq_mul_inv]
  have hresY : ∃ m : Additive ↥Y, ∀ a : ↥L, (a : MulAut V) ∈ A → fY a = muW hLY a m - m := by
    refine ⟨Additive.ofMul (pY (Additive.toMul m₀)), fun a ha => ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [muW_sub_apply]
    show (pY (Additive.toMul (f a)) : V) =
      (a : MulAut V) (pY (Additive.toMul m₀) : V) * (pY (Additive.toMul m₀) : V)⁻¹
    rw [hm₀ a ha, toMul_sub, muW_apply, map_div, Subgroup.coe_div, heqY a, div_eq_mul_inv]
  obtain ⟨mX, hmX⟩ := hRX fX hfX hresX
  obtain ⟨mY, hmY⟩ := hRY fY hfY hresY
  refine ⟨Additive.ofMul ⟨(Additive.toMul mX : ↥X) * (Additive.toMul mY : ↥Y),
    hsup ▸ Subgroup.mul_mem_sup (Additive.toMul mX : ↥X).2 (Additive.toMul mY : ↥Y).2⟩, ?_⟩
  funext a
  apply Additive.toMul.injective
  apply Subtype.ext
  have hX := congrArg (fun x : Additive ↥X => ((Additive.toMul x : ↥X) : V)) (congrFun hmX a)
  have hY := congrArg (fun x : Additive ↥Y => ((Additive.toMul x : ↥Y) : V)) (congrFun hmY a)
  simp only [coboundaryA_apply] at hX hY
  rw [muW_sub_apply] at hX hY
  have hX' : (pX (Additive.toMul (f a)) : V) = (a : MulAut V) ((Additive.toMul mX : ↥X) : V) *
      ((Additive.toMul mX : ↥X) : V)⁻¹ := hX.symm
  have hY' : (pY (Additive.toMul (f a)) : V) = (a : MulAut V) ((Additive.toMul mY : ↥Y) : V) *
      ((Additive.toMul mY : ↥Y) : V)⁻¹ := hY.symm
  rw [coboundaryA_apply, muW_sub_apply]
  show (a : MulAut V) (((Additive.toMul mX : ↥X) : V) * ((Additive.toMul mY : ↥Y) : V)) *
    (((Additive.toMul mX : ↥X) : V) * ((Additive.toMul mY : ↥Y) : V))⁻¹ =
      ((Additive.toMul (f a) : ↥W) : V)
  rw [hdec (Additive.toMul (f a)), hX', hY', map_mul, mul_inv, mul_mul_mul_comm]

end Ext

end FFC

end CFSG.Quasithin
