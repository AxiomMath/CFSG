module

public import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
public import CFSG.Fischer.Classification.Orthogonal3.Model

public section

namespace CFSG.StandardType.ZS

open CFSG.Fischer.Classification

section General

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  [Module.Finite (ZMod p) V] {G : Subgroup (V ≃ₗ[ZMod p] V)}

private theorem zlf_inv_maps {W : Submodule (ZMod p) V} {h : V ≃ₗ[ZMod p] V}
    (hh : ∀ x ∈ W, h x ∈ W) : ∀ x ∈ W, h⁻¹ x ∈ W := by
  intro x hx
  let F : ↥W →ₗ[ZMod p] ↥W :=
    { toFun := fun y => ⟨h y, hh y y.2⟩
      map_add' := fun y z => Subtype.ext (map_add _ _ _)
      map_smul' := fun c y => Subtype.ext (map_smul _ c _) }
  have hinj : Function.Injective F := fun y z hyz =>
    Subtype.ext (h.injective (congrArg Subtype.val hyz))
  obtain ⟨y, hy⟩ := LinearMap.surjective_of_injective (f := F) hinj (⟨x, hx⟩ : ↥W)
  have hxy : h (y : V) = x := congrArg Subtype.val hy
  have h2 : h⁻¹ x = (y : V) := by
    apply h.injective
    calc h (h⁻¹ x) = (h * h⁻¹) x := (LinearEquiv.mul_apply h h⁻¹ x).symm
      _ = x := by rw [mul_inv_cancel]; simp
      _ = h (y : V) := hxy.symm
  rw [h2]
  exact y.2

theorem AbsIrred.eq_top_of_closure_mk_image_eq_top (hirr : AbsIrred p G)
    {X : Submodule (ZMod p) V} (hX : X ≠ ⊥) {T : Set ↥G}
    (hT : ∀ t ∈ T, ∀ x ∈ X, (t : V ≃ₗ[ZMod p] V) x ∈ X)
    (htop : Subgroup.closure ((QuotientGroup.mk : ↥G → ↥G ⧸ Subgroup.center ↥G) '' T) = ⊤) :
    X = ⊤ := by
  have hP : ∀ h ∈ Subgroup.closure T, (∀ x ∈ X, (h : V ≃ₗ[ZMod p] V) x ∈ X) ∧
      (∀ x ∈ X, ((h : V ≃ₗ[ZMod p] V))⁻¹ x ∈ X) := by
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem t ht => exact ⟨hT t ht, zlf_inv_maps (hT t ht)⟩
    | one => exact ⟨fun x hx => by simpa using hx, fun x hx => by simpa using hx⟩
    | mul x y hx hy ihx ihy =>
        refine ⟨fun z hz => ?_, fun z hz => ?_⟩
        · have h1 := ihx.1 _ (ihy.1 _ hz)
          simpa [Subgroup.coe_mul, LinearEquiv.mul_apply] using h1
        · have h1 := ihy.2 _ (ihx.2 _ hz)
          simpa [Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply] using h1
    | inv x hx ih => exact ⟨ih.2, fun z hz => by simpa using ih.1 z hz⟩
  have hcenter : ∀ z ∈ Subgroup.center ↥G, ∀ x ∈ X, (z : V ≃ₗ[ZMod p] V) x ∈ X := by
    intro z hz x hx
    obtain ⟨c, hc⟩ := hirr.exists_eq_smul_of_mem_center hz
    have hval : (z : V ≃ₗ[ZMod p] V) x = c • x := by
      have h1 := congrArg (fun f : V →ₗ[ZMod p] V => f x) hc
      simpa using h1
    rw [hval]
    exact Submodule.smul_mem X c hx
  have hHtop : (Subgroup.closure T).map (QuotientGroup.mk' (Subgroup.center ↥G)) = ⊤ := by
    rw [MonoidHom.map_closure]
    simpa only [QuotientGroup.coe_mk'] using htop
  have hpres : ∀ g ∈ G, ∀ x ∈ X, g x ∈ X := by
    intro g hg x hx
    let g' : ↥G := ⟨g, hg⟩
    have hmem : (QuotientGroup.mk g' : ↥G ⧸ Subgroup.center ↥G) ∈
        (Subgroup.closure T).map (QuotientGroup.mk' (Subgroup.center ↥G)) := by
      rw [hHtop]
      exact Subgroup.mem_top _
    obtain ⟨h, hh, hval⟩ := Subgroup.mem_map.mp hmem
    have hval' : (QuotientGroup.mk h : ↥G ⧸ Subgroup.center ↥G) = QuotientGroup.mk g' := by
      simpa only [QuotientGroup.coe_mk'] using hval
    have hcent : g' * h⁻¹ ∈ Subgroup.center ↥G := by
      refine (QuotientGroup.eq_one_iff (N := Subgroup.center ↥G) (g' * h⁻¹)).mp ?_
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hval', mul_inv_cancel]
    have hge : (g' : V ≃ₗ[ZMod p] V) =
        ((g' * h⁻¹ : ↥G) : V ≃ₗ[ZMod p] V) * (h : V ≃ₗ[ZMod p] V) := by
      conv_rhs => rw [← Subgroup.coe_mul]
      congr 1
      group
    have hge' : (g : V ≃ₗ[ZMod p] V) = ((g' * h⁻¹ : ↥G) : V ≃ₗ[ZMod p] V) * ↑h := hge
    rw [hge', LinearEquiv.mul_apply]
    exact hcenter _ hcent _ ((hP h hh).1 x hx)
  rcases hirr.1 X hpres with h | h
  · exact absurd h hX
  · exact h

end General

variable {U : Type} [AddCommGroup U] [Module (ZMod 3) U] [Module.Finite (ZMod 3) U]
  {A : Subgroup (U ≃ₗ[ZMod 3] U)}

omit [Module.Finite (ZMod 3) U] in
private theorem zlf_apply_apply {B : LinearMap.BilinForm (ZMod 3) U} {a b : U}
    {s t : U ≃ₗ[ZMod 3] U} (hs : ∀ x, s x = x + B x a • a)
    (ht : ∀ x, t x = x + B x b • b) (x : U) :
    s (t x) = x + B x b • b + B x a • a + (B x b * B b a) • a := by
  rw [ht, hs, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left]
  simp only [add_smul]
  abel

omit [Module.Finite (ZMod 3) U] in
private theorem zlf_commute_iff_B {B : LinearMap.BilinForm (ZMod 3) U}
    (hBs : ∀ x y, B x y = B y x) {a b : U} (ha : B a a = 1)
    {s t : U ≃ₗ[ZMod 3] U} (hs : ∀ x, s x = x + B x a • a)
    (ht : ∀ x, t x = x + B x b • b) (hst : s ≠ t) :
    Commute s t ↔ B a b = 0 := by
  constructor
  · intro hc
    by_contra hc0
    have hcomm : s (t a) = t (s a) := by
      have h : s * t = t * s := hc
      simpa [LinearEquiv.mul_apply] using congrArg (fun e : U ≃ₗ[ZMod 3] U => e a) h
    have hdiff : s (t a) - t (s a) = B a b • (B a b • a - b) := by
      rw [zlf_apply_apply hs ht a, zlf_apply_apply ht hs a, ha, one_smul, one_mul, hBs b a]
      rw [smul_sub, smul_smul]
      abel
    have h0 : B a b • (B a b • a - b) = 0 := by rw [← hdiff, hcomm, sub_self]
    have hba : b = B a b • a := by
      have h1 := (smul_eq_zero_iff_right (m := B a b • a - b) hc0).mp h0
      exact (sub_eq_zero.mp h1).symm
    have hfix : ∀ x : U, B x (B a b • a) • (B a b • a) = B x a • a := by
      intro x
      calc B x (B a b • a) • (B a b • a) = (B a b * B x a) • (B a b • a) := by
            rw [LinearMap.BilinForm.smul_right]
        _ = ((B a b * B x a) * B a b) • a := by rw [smul_smul]
        _ = B x a • a := by
              rw [mul_comm (B a b) (B x a), mul_assoc, F3.mul_self_of_ne_zero hc0]
              simp
    refine hst (LinearEquiv.ext fun x => ?_)
    rw [hs x, ht x, hba, hfix x]
  · intro hc
    rw [commute_iff_eq]
    apply LinearEquiv.ext
    intro x
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      zlf_apply_apply hs ht x, zlf_apply_apply ht hs x, hBs b a, hc]
    simp only [mul_zero, zero_smul, add_zero]
    abel

omit [Module.Finite (ZMod 3) U] in
private theorem zlf_lift {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    (φ : ↥A ⧸ Subgroup.center ↥A ≃* R3 f)
    (hφ : ∀ g, g ∈ reflImage 3 A ↔ φ g ∈ D3 f) {B : LinearMap.BilinForm (ZMod 3) U}
    (hB : ∀ t ∈ A, IsRefl 3 t → ∃ u, B u u = 1 ∧ ∀ x, t x = x + B x u • u)
    {v : Fin m → ZMod 3} (hv : f v v = 1) :
    ∃ t : ↥A, IsRefl 3 (t : U ≃ₗ[ZMod 3] U) ∧
      φ (QuotientGroup.mk t) = reflBar f v ∧
      ∃ a : U, B a a = 1 ∧ ∀ x, (t : U ≃ₗ[ZMod 3] U) x = x + B x a • a := by
  have hR : φ.symm (reflBar f v) ∈ reflImage 3 A :=
    (hφ _).2 (by rw [MulEquiv.apply_symm_apply]; exact reflBar_mem_D3 hv)
  obtain ⟨t, ht, htmk⟩ := hR
  obtain ⟨a, haa, ha⟩ := hB (t : U ≃ₗ[ZMod 3] U) t.2 ht
  exact ⟨t, ht, by rw [htmk, MulEquiv.apply_symm_apply], a, haa, ha⟩

private theorem zlf_gram_iff (hn : 3 ≤ Module.finrank (ZMod 3) U) (hirr : AbsIrred 3 A)
    {m : ℕ} (hm : 4 ≤ m) {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)} (hf : IsF3Form f)
    (φ : ↥A ⧸ Subgroup.center ↥A ≃* R3 f) {B : LinearMap.BilinForm (ZMod 3) U}
    (hBs : ∀ x y, B x y = B y x) {v w : Fin m → ZMod 3} (hv : f v v = 1) (hw : f w w = 1)
    (hwv : w ≠ v) (hwv' : w ≠ -v) {s t : ↥A}
    (ht : IsRefl 3 (t : U ≃ₗ[ZMod 3] U)) (hsbar : φ (QuotientGroup.mk s) = reflBar f v)
    (htbar : φ (QuotientGroup.mk t) = reflBar f w) {a b : U} (ha : B a a = 1)
    (hsa : ∀ x, (s : U ≃ₗ[ZMod 3] U) x = x + B x a • a)
    (htb : ∀ x, (t : U ≃ₗ[ZMod 3] U) x = x + B x b • b) :
    B a b = 0 ↔ f v w = 0 := by
  have hstA : s ≠ t := by
    intro h1
    have h2 : reflBar f v = reflBar f w := by rw [← hsbar, ← htbar, h1]
    rcases (reflBar_eq_reflBar_iff hf hm hv hw).mp h2 with h | h
    · exact hwv h
    · exact hwv' h
  have hst : (s : U ≃ₗ[ZMod 3] U) ≠ (t : U ≃ₗ[ZMod 3] U) := fun h => hstA (Subtype.ext h)
  have hkey : Commute s t ↔ B a b = 0 := by
    have h1 : Commute s t ↔ Commute (s : U ≃ₗ[ZMod 3] U) (t : U ≃ₗ[ZMod 3] U) := by
      rw [commute_iff_eq, commute_iff_eq]
      constructor
      · intro h
        rw [← Subgroup.coe_mul, h, Subgroup.coe_mul]
      · intro h
        exact Subtype.ext h
    exact h1.trans (zlf_commute_iff_B hBs ha hsa htb hst)
  have hchain : Commute s t ↔ f v w = 0 := by
    have hA : Commute s t ↔ Commute (QuotientGroup.mk s) (QuotientGroup.mk t) :=
      (hirr.commute_mk_iff hn ht).symm
    have hmap : Commute (QuotientGroup.mk s) (QuotientGroup.mk t) ↔
        Commute (φ (QuotientGroup.mk s)) (φ (QuotientGroup.mk t)) :=
      (commute_map_iff (f := (φ : ↥A ⧸ Subgroup.center ↥A →* R3 f)) φ.injective).symm
    have hval : Commute (φ (QuotientGroup.mk s)) (φ (QuotientGroup.mk t)) ↔
        Commute (reflBar f v) (reflBar f w) := by rw [hsbar, htbar]
    have hzero : Commute (reflBar f v) (reflBar f w) ↔ f v w = 0 := by
      rw [commute_iff_eq, reflBar_commute_iff hf hm hv hw]
      constructor
      · rintro (h | h | h)
        · exact h
        · exact absurd h hwv
        · exact absurd h hwv'
      · exact Or.inl
    exact hA.trans (hmap.trans (hval.trans hzero))
  exact hkey.symm.trans hchain

omit [Module.Finite (ZMod 3) U] in
private theorem zlf_adjust_root {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    {B : LinearMap.BilinForm (ZMod 3) U}
    {k : ℕ} {y : Fin k → Fin m → ZMod 3} {v : Fin m → ZMod 3} {u : Fin k → U}
    {a : U} (haa : B a a = 1) {t : U ≃ₗ[ZMod 3] U}
    (hform : ∀ x, t x = x + B x a • a)
    (hiff : ∀ i, B (u i) a = 0 ↔ f (y i) v = 0)
    (huniq : ∀ i i', f (y i) v ≠ 0 → f (y i') v ≠ 0 → i = i') :
    ∃ a' : U, B a' a' = 1 ∧ (∀ i, B (u i) a' = f (y i) v) ∧
      ∀ x, t x = x + B x a' • a' := by
  by_cases hex : ∃ i, f (y i) v ≠ 0
  · obtain ⟨i₀, hi₀⟩ := hex
    have hBne : B (u i₀) a ≠ 0 := fun h => hi₀ ((hiff i₀).mp h)
    have hzero : ∀ i, i ≠ i₀ → B (u i) a = 0 := by
      intro i hi
      exact (hiff i).mpr (by
        by_contra h
        exact hi (huniq i i₀ h hi₀))
    have hεε : (f (y i₀) v * B (u i₀) a) * (f (y i₀) v * B (u i₀) a) = 1 := by
      rw [mul_mul_mul_comm, F3.mul_self_of_ne_zero hi₀, F3.mul_self_of_ne_zero hBne, mul_one]
    have hεx : (f (y i₀) v * B (u i₀) a) * B (u i₀) a = f (y i₀) v := by
      rw [mul_assoc, F3.mul_self_of_ne_zero hBne, mul_one]
    refine ⟨(f (y i₀) v * B (u i₀) a) • a, ?_, ?_, ?_⟩
    · have h1 : B ((f (y i₀) v * B (u i₀) a) • a) ((f (y i₀) v * B (u i₀) a) • a) =
          (f (y i₀) v * B (u i₀) a) * (f (y i₀) v * B (u i₀) a) * B a a := by
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
        ring
      rw [h1, hεε, haa, mul_one]
    · intro i
      by_cases hi : i = i₀
      · subst hi
        rw [LinearMap.BilinForm.smul_right, hεx]
      · have h0 : B (u i) a = 0 := hzero i hi
        rw [LinearMap.BilinForm.smul_right, h0, mul_zero]
        exact ((hiff i).mp h0).symm
    · intro x
      rw [hform x]
      have hmain : B x ((f (y i₀) v * B (u i₀) a) • a) •
          ((f (y i₀) v * B (u i₀) a) • a) = B x a • a := by
        calc B x ((f (y i₀) v * B (u i₀) a) • a) • ((f (y i₀) v * B (u i₀) a) • a)
              = (f (y i₀) v * B (u i₀) a * B x a) •
                  ((f (y i₀) v * B (u i₀) a) • a) := by
                rw [LinearMap.BilinForm.smul_right]
          _ = ((f (y i₀) v * B (u i₀) a * B x a) * (f (y i₀) v * B (u i₀) a)) • a := by
                rw [smul_smul]
          _ = B x a • a := by
                rw [mul_comm (f (y i₀) v * B (u i₀) a) (B x a), mul_assoc, hεε]
                simp
      rw [hmain]
  · have hzero : ∀ i, B (u i) a = 0 := fun i => (hiff i).mpr (by
      by_contra h
      exact hex ⟨i, h⟩)
    exact ⟨a, haa, fun i => by rw [hzero i]; exact ((hiff i).mp (hzero i)).symm, hform⟩

omit [Module.Finite (ZMod 3) U] in
private theorem zlf_snoc_gram {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    (hf : IsF3Form f) {B : LinearMap.BilinForm (ZMod 3) U} (hBs : ∀ x y, B x y = B y x)
    {k : ℕ} {y : Fin k → Fin m → ZMod 3} {v : Fin m → ZMod 3} {u : Fin k → U} {a : U}
    (hgram : ∀ i j, B (u i) (u j) = f (y i) (y j)) (ha : B a a = 1)
    (hnew : ∀ i, B (u i) a = f (y i) v) (hv : f v v = 1) :
    ∀ i j : Fin (k + 1),
      B ((Fin.snoc (α := fun _ => U) u a) i) ((Fin.snoc (α := fun _ => U) u a) j) =
        f ((Fin.snoc (α := fun _ => Fin m → ZMod 3) y v) i)
          ((Fin.snoc (α := fun _ => Fin m → ZMod 3) y v) j) := by
  intro i j
  induction i using Fin.lastCases with
  | last =>
      induction j using Fin.lastCases with
      | last => simp only [Fin.snoc_last]; rw [ha, hv]
      | cast j => simp only [Fin.snoc_last, Fin.snoc_castSucc]; rw [hBs, hnew j, hf.symm]
  | cast i =>
      induction j using Fin.lastCases with
      | last => simp only [Fin.snoc_last, Fin.snoc_castSucc]; rw [hnew i]
      | cast j => simp only [Fin.snoc_castSucc]; exact hgram i j

omit [Module.Finite (ZMod 3) U] in
private theorem zlf_snoc_refl {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    (φ : ↥A ⧸ Subgroup.center ↥A ≃* R3 f) {B : LinearMap.BilinForm (ZMod 3) U}
    {k : ℕ} {y : Fin k → Fin m → ZMod 3} {v : Fin m → ZMod 3} {u : Fin k → U} {a : U}
    {t : ↥A} (ht : IsRefl 3 (t : U ≃ₗ[ZMod 3] U))
    (htbar : φ (QuotientGroup.mk t) = reflBar f v)
    (htform : ∀ x, (t : U ≃ₗ[ZMod 3] U) x = x + B x a • a)
    (hrefl : ∀ i, ∃ s : ↥A, IsRefl 3 (s : U ≃ₗ[ZMod 3] U) ∧
      φ (QuotientGroup.mk s) = reflBar f (y i) ∧
      ∀ x, (s : U ≃ₗ[ZMod 3] U) x = x + B x (u i) • u i) :
    ∀ i : Fin (k + 1), ∃ s : ↥A, IsRefl 3 (s : U ≃ₗ[ZMod 3] U) ∧
      φ (QuotientGroup.mk s) = reflBar f ((Fin.snoc (α := fun _ => Fin m → ZMod 3) y v) i) ∧
      ∀ x, (s : U ≃ₗ[ZMod 3] U) x =
        x + B x ((Fin.snoc (α := fun _ => U) u a) i) • ((Fin.snoc (α := fun _ => U) u a) i) := by
  intro i
  induction i using Fin.lastCases with
  | last => simpa only [Fin.snoc_last] using ⟨t, ht, htbar, htform⟩
  | cast i => simpa only [Fin.snoc_castSucc] using hrefl i

private theorem zlf_step (hn : 3 ≤ Module.finrank (ZMod 3) U) (hirr : AbsIrred 3 A)
    {m : ℕ} (hm : 4 ≤ m) {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)} (hf : IsF3Form f)
    (φ : ↥A ⧸ Subgroup.center ↥A ≃* R3 f) (hφ : ∀ g, g ∈ reflImage 3 A ↔ φ g ∈ D3 f)
    {B : LinearMap.BilinForm (ZMod 3) U} (hBs : ∀ x y, B x y = B y x)
    (hB : ∀ t ∈ A, IsRefl 3 t → ∃ u, B u u = 1 ∧ ∀ x, t x = x + B x u • u)
    {k : ℕ} {y : Fin k → Fin m → ZMod 3} {v : Fin m → ZMod 3} (hy : ∀ i, f (y i) (y i) = 1)
    (hv : f v v = 1) (hnev : ∀ i, v ≠ y i ∧ v ≠ -y i)
    (hfv : ∀ i i', f (y i) v ≠ 0 → f (y i') v ≠ 0 → i = i') {u : Fin k → U}
    (hgram : ∀ i j, B (u i) (u j) = f (y i) (y j))
    (hrefl : ∀ i, ∃ t : ↥A, IsRefl 3 (t : U ≃ₗ[ZMod 3] U) ∧
      φ (QuotientGroup.mk t) = reflBar f (y i) ∧
      ∀ x, (t : U ≃ₗ[ZMod 3] U) x = x + B x (u i) • u i) :
    ∃ a : U, B a a = 1 ∧ (∀ i, B (u i) a = f (y i) v) ∧
      ∃ t : ↥A, IsRefl 3 (t : U ≃ₗ[ZMod 3] U) ∧
        φ (QuotientGroup.mk t) = reflBar f v ∧
        ∀ x, (t : U ≃ₗ[ZMod 3] U) x = x + B x a • a := by
  obtain ⟨t, htrefl, htbar, a, haa, htform⟩ := zlf_lift φ hφ hB hv
  choose s hsrefl hsbar hsform using hrefl
  have hiff : ∀ i, B (u i) a = 0 ↔ f (y i) v = 0 := fun i =>
    zlf_gram_iff hn hirr hm hf φ hBs (hy i) hv (hnev i).1 (hnev i).2
      htrefl (hsbar i) htbar (by rw [hgram i i, hy i]) (hsform i) htform
  obtain ⟨a', haa', hnew', hform'⟩ := zlf_adjust_root haa htform hiff hfv
  exact ⟨a', haa', hnew', t, htrefl, htbar, hform'⟩

private theorem zlf_roots_aux (hn : 3 ≤ Module.finrank (ZMod 3) U) (hirr : AbsIrred 3 A)
    {m : ℕ} (hm : 4 ≤ m) {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)} (hf : IsF3Form f)
    (φ : ↥A ⧸ Subgroup.center ↥A ≃* R3 f) (hφ : ∀ g, g ∈ reflImage 3 A ↔ φ g ∈ D3 f)
    {B : LinearMap.BilinForm (ZMod 3) U} (hBs : ∀ x y, B x y = B y x)
    (hB : ∀ t ∈ A, IsRefl 3 t → ∃ u, B u u = 1 ∧ ∀ x, t x = x + B x u • u) :
    ∀ (k : ℕ) (y : Fin k → Fin m → ZMod 3), (∀ i, f (y i) (y i) = 1) →
      (∀ i j, i ≠ j → y j ≠ y i ∧ y j ≠ -y i) →
      (∀ i i' j, i < j → i' < j → f (y i) (y j) ≠ 0 → f (y i') (y j) ≠ 0 → i = i') →
      ∃ u : Fin k → U, (∀ i j, B (u i) (u j) = f (y i) (y j)) ∧
        ∀ i, ∃ t : ↥A, IsRefl 3 (t : U ≃ₗ[ZMod 3] U) ∧
          φ (QuotientGroup.mk t) = reflBar f (y i) ∧
          ∀ x, (t : U ≃ₗ[ZMod 3] U) x = x + B x (u i) • u i := by
  intro k
  induction k with
  | zero =>
      intro y hy hne hforest
      exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ k ih =>
      intro y hy hne hforest
      set y' : Fin k → Fin m → ZMod 3 := fun i => y i.castSucc with hy'def
      set v : Fin m → ZMod 3 := y (Fin.last k) with hvdef
      have hy' : ∀ i, f (y' i) (y' i) = 1 := fun i => hy i.castSucc
      have hne' : ∀ i j, i ≠ j → y' j ≠ y' i ∧ y' j ≠ -y' i := fun i j hij =>
        hne i.castSucc j.castSucc (fun h => hij (Fin.castSucc_injective k h))
      have hforest' : ∀ i i' j, i < j → i' < j → f (y' i) (y' j) ≠ 0 →
          f (y' i') (y' j) ≠ 0 → i = i' := by
        intro i i' j hij hi'j h1 h2
        exact Fin.castSucc_injective k (hforest i.castSucc i'.castSucc j.castSucc
          (by simpa using hij) (by simpa using hi'j) h1 h2)
      obtain ⟨u, hgram, hrefl⟩ := ih y' hy' hne' hforest'
      have hv : f v v = 1 := hy (Fin.last k)
      have hnev : ∀ i, v ≠ y' i ∧ v ≠ -y' i := fun i =>
        hne i.castSucc (Fin.last k) (Fin.castSucc_ne_last i)
      have hfv : ∀ i i', f (y' i) v ≠ 0 → f (y' i') v ≠ 0 → i = i' := fun i i' h1 h2 =>
        Fin.castSucc_injective k (hforest i.castSucc i'.castSucc (Fin.last k)
          (lt_of_le_of_ne (Fin.le_last i.castSucc) (Fin.castSucc_ne_last i))
          (lt_of_le_of_ne (Fin.le_last i'.castSucc) (Fin.castSucc_ne_last i')) h1 h2)
      obtain ⟨a, haa, hnew, t, htrefl, htbar, htform⟩ :=
        zlf_step hn hirr hm hf φ hφ hBs hB hy' hv hnev hfv hgram hrefl
      have hsnoc : (Fin.snoc y' v : Fin (k + 1) → Fin m → ZMod 3) = y := by
        funext i
        induction i using Fin.lastCases with
        | last => rw [Fin.snoc_last]
        | cast i => rw [Fin.snoc_castSucc]
      refine ⟨Fin.snoc (α := fun _ => U) u a, ?_, ?_⟩
      · rw [← hsnoc]
        exact zlf_snoc_gram hf hBs hgram haa hnew hv
      · rw [← hsnoc]
        exact zlf_snoc_refl φ htrefl htbar htform hrefl

theorem exists_roots_of_forest (hn : 3 ≤ Module.finrank (ZMod 3) U) (hirr : AbsIrred 3 A)
    {m : ℕ} (hm : 4 ≤ m) {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)} (hf : IsF3Form f)
    (φ : ↥A ⧸ Subgroup.center ↥A ≃* R3 f) (hφ : ∀ g, g ∈ reflImage 3 A ↔ φ g ∈ D3 f)
    {B : LinearMap.BilinForm (ZMod 3) U} (hBs : ∀ x y, B x y = B y x)
    (hB : ∀ t ∈ A, IsRefl 3 t → ∃ u, B u u = 1 ∧ ∀ x, t x = x + B x u • u)
    {k : ℕ} (y : Fin k → Fin m → ZMod 3) (hy : ∀ i, f (y i) (y i) = 1)
    (hne : ∀ i j, i ≠ j → y j ≠ y i ∧ y j ≠ -y i)
    (hforest : ∀ i i' j, i < j → i' < j → f (y i) (y j) ≠ 0 → f (y i') (y j) ≠ 0 → i = i') :
    ∃ u : Fin k → U, (∀ i j, B (u i) (u j) = f (y i) (y j)) ∧
      ∀ i, ∃ t : ↥A, IsRefl 3 (t : U ≃ₗ[ZMod 3] U) ∧
        φ (QuotientGroup.mk t) = reflBar f (y i) ∧
        ∀ x, (t : U ≃ₗ[ZMod 3] U) x = x + B x (u i) • u i :=
  zlf_roots_aux hn hirr hm hf φ hφ hBs hB k y hy hne hforest

end CFSG.StandardType.ZS
