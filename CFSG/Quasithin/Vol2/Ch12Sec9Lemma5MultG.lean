module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma5Mult
public import CFSG.Quasithin.Background.Module
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Topology.Order.Hom.Esakia

public section

namespace CFSG.Quasithin.H13.Mult

open Module CFSG.Quasithin

variable {W : Type*} [CommGroup W]

@[expose, instance_reducible] noncomputable def zmodModuleW (hW : ∀ w : W, w ^ 2 = 1) :
    Module (ZMod 2) (Additive W) :=
  AddCommGroup.zmodModule fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hW _

section Lin

variable [Module (ZMod 2) (Additive W)]

@[expose] noncomputable def linEquiv : MulAut W ≃* (Additive W ≃ₗ[ZMod 2] Additive W) where
  toFun f :=
    { AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive f.toMonoidHom) with
      invFun := fun x => Additive.ofMul (f.symm x.toMul)
      left_inv := fun x => by simp [MonoidHom.toAdditive]
      right_inv := fun x => by simp [MonoidHom.toAdditive] }
  invFun g :=
    { toFun := fun w => (g (Additive.ofMul w)).toMul
      invFun := fun w => (g.symm (Additive.ofMul w)).toMul
      left_inv := fun w => by simp
      right_inv := fun w => by simp
      map_mul' := fun a b => by simp only [ofMul_mul, map_add, toMul_add] }
  left_inv f := by
    ext w
    rfl
  right_inv g := by
    ext x
    rfl
  map_mul' f g := by
    ext x
    rfl

theorem linEquiv_apply (f : MulAut W) (x : Additive W) :
    linEquiv f x = Additive.ofMul (f x.toMul) := rfl

@[expose] def toSub (K : Subgroup W) : Submodule (ZMod 2) (Additive W) :=
  AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup K)

theorem mem_toSub {K : Subgroup W} {x : Additive W} : x ∈ toSub K ↔ x.toMul ∈ K := Iff.rfl

@[expose] def toSubIso : Subgroup W ≃o Submodule (ZMod 2) (Additive W) :=
  Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)

theorem toSubIso_apply (K : Subgroup W) : toSubIso K = toSub K := rfl

theorem toSub_map (c : MulAut W) (K : Subgroup W) :
    toSub (K.map c.toMonoidHom) =
      (toSub K).map (linEquiv c : Additive W →ₗ[ZMod 2] Additive W) := by
  ext x
  rw [mem_toSub, Subgroup.mem_map, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact ⟨Additive.ofMul y, hy, by rw [LinearEquiv.coe_coe, linEquiv_apply]; exact congrArg _ hyx⟩
  · rintro ⟨z, hz, hzx⟩
    refine ⟨z.toMul, hz, ?_⟩
    rw [← hzx]
    rfl

theorem card_toSub (K : Subgroup W) : Nat.card (toSub K) = Nat.card K :=
  Nat.card_congr
    { toFun := fun x => ⟨(x : Additive W).toMul, x.2⟩
      invFun := fun y => ⟨Additive.ofMul (y : W), y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end Lin

@[expose] def toMulAutPi (m : ℕ) :
    ((Fin m → ZMod 2) ≃ₗ[ZMod 2] (Fin m → ZMod 2)) →* MulAut (Multiplicative (Fin m → ZMod 2)) where
  toFun f := AddEquiv.toMultiplicative f.toAddEquiv
  map_one' := MulEquiv.ext fun _ => rfl
  map_mul' _ _ := MulEquiv.ext fun _ => rfl

theorem toMulAutPi_apply {m : ℕ} (f : (Fin m → ZMod 2) ≃ₗ[ZMod 2] (Fin m → ZMod 2))
    (v : Multiplicative (Fin m → ZMod 2)) :
    toMulAutPi m f v = Multiplicative.ofAdd (f v.toAdd) := rfl

theorem exists_rep' [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {Ls : Subgroup (MulAut W)}
    {Yg : Subgroup W} (hmaps : ∀ l ∈ Ls, ∀ y ∈ Yg, l y ∈ Yg)
    (honto : ∀ τ : MulAut ↥Yg, ∃ l ∈ Ls, ∀ y : Yg, l (y : W) = (τ y : W))
    {d : ℕ} (hd : 2 ≤ d) (hYd : Nat.card Yg = 2 ^ d)
    (hspan : ⨆ c ∈ Subgroup.centralizer (Ls : Set (MulAut W)), Yg.map c.toMonoidHom = ⊤) :
    ∃ (m : ℕ) (θ : ↥(Subgroup.centralizer (Ls : Set (MulAut W)) ⊔ Ls) →*
        MulAut (Multiplicative (Fin m → ZMod 2))),
      (∀ l (hl : l ∈ Ls), θ ⟨l, Subgroup.mem_sup_right hl⟩ = 1) ∧
      (∀ a (ha : a ∈ Subgroup.centralizer (Ls : Set (MulAut W))),
        θ ⟨a, Subgroup.mem_sup_left ha⟩ = 1 → a = 1) ∧
      (∀ B : Subgroup (MulAut W), B ≤ Subgroup.centralizer (Ls : Set (MulAut W)) →
        Nat.card (fixV B) = Nat.card (fixV ((B.subgroupOf _).map θ)) ^ d) ∧
      Nat.card W = (2 ^ m) ^ d := by
  classical
  let _ : Module (ZMod 2) (Additive W) := zmodModuleW hW
  set e := (linEquiv : MulAut W ≃* (Additive W ≃ₗ[ZMod 2] Additive W)) with he
  set Ls' := Ls.map e.toMonoidHom with hLs'
  set Y' := toSub Yg with hY'
  set C := Subgroup.centralizer (Ls : Set (MulAut W)) with hC
  have hCe : ∀ c ∈ C, e c ∈ Cent Ls' := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    change e l * e c = e c * e l
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hc l hl]
  have hCe' : ∀ c' ∈ Cent Ls', e.symm c' ∈ C := by
    intro c' hc'
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_centralizer_iff.1 hc' (e l) ⟨l, hl, rfl⟩
  have hcardY' : Nat.card Y' = 2 ^ d := (card_toSub Yg).trans hYd
  have hfinY' : finrank (ZMod 2) Y' = d := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Module.Finite (ZMod 2) Y' := Module.Finite.of_finite
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Y')
    rw [Nat.card_zmod, hcardY'] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have hHyp : Hyp Ls' Y' := by
    refine ⟨?_, fun τ => ?_, by rw [hfinY']; exact hd⟩
    · rintro _ ⟨l, hl, rfl⟩ y hy
      exact hmaps l hl _ hy
    ·
      let τg : MulAut ↥Yg :=
        { toFun := fun y => ⟨(τ ⟨Additive.ofMul (y : W), y.2⟩ : Additive W).toMul,
            (τ ⟨Additive.ofMul (y : W), y.2⟩).2⟩
          invFun := fun y => ⟨(τ.symm ⟨Additive.ofMul (y : W), y.2⟩ : Additive W).toMul,
            (τ.symm ⟨Additive.ofMul (y : W), y.2⟩).2⟩
          left_inv := fun y => by
            apply Subtype.ext
            simp only
            have : (⟨Additive.ofMul ((τ ⟨Additive.ofMul (y : W), y.2⟩ : Additive W).toMul),
                (τ ⟨Additive.ofMul (y : W), y.2⟩).2⟩ : Y') = τ ⟨Additive.ofMul (y : W), y.2⟩ :=
              rfl
            rw [this, LinearEquiv.symm_apply_apply]
            rfl
          right_inv := fun y => by
            apply Subtype.ext
            simp only
            have : (⟨Additive.ofMul ((τ.symm ⟨Additive.ofMul (y : W), y.2⟩ :
                Additive W).toMul), (τ.symm ⟨Additive.ofMul (y : W), y.2⟩).2⟩ : Y') =
                  τ.symm ⟨Additive.ofMul (y : W), y.2⟩ := rfl
            rw [this, LinearEquiv.apply_symm_apply]
            rfl
          map_mul' := fun a b => by
            apply Subtype.ext
            have h1 : (⟨Additive.ofMul ((a : W) * (b : W)), (a * b).2⟩ : Y') =
                ⟨Additive.ofMul (a : W), a.2⟩ + ⟨Additive.ofMul (b : W), b.2⟩ := rfl
            show (τ ⟨Additive.ofMul ((a : W) * (b : W)), (a * b).2⟩ : Additive W).toMul = _
            rw [h1, map_add, Submodule.coe_add, toMul_add]
            rfl }
      obtain ⟨l, hl, hlτ⟩ := honto τg
      refine ⟨e l, ⟨l, hl, rfl⟩, fun y => ?_⟩
      have h1 := hlτ ⟨(y : Additive W).toMul, y.2⟩
      rw [he, linEquiv_apply]
      apply Additive.toMul.injective
      rw [toMul_ofMul]
      exact h1
  have hspan' : ∀ x : Additive W,
      x ∈ ⨆ c ∈ Cent Ls', Y'.map (c : Additive W →ₗ[ZMod 2] Additive W) := by
    intro x
    have h1 : toSubIso (⨆ c ∈ C, Yg.map c.toMonoidHom) = ⊤ := by
      rw [hspan, map_top]
    rw [OrderIso.map_iSup₂] at h1
    have h2 : (⊤ : Submodule (ZMod 2) (Additive W)) ≤
        ⨆ c ∈ Cent Ls', Y'.map (c : Additive W →ₗ[ZMod 2] Additive W) := by
      rw [← h1]
      refine iSup₂_le fun c hc => ?_
      rw [toSubIso_apply, toSub_map]
      exact le_iSup₂ (f := fun c' (_ : c' ∈ Cent Ls') =>
        Y'.map (c' : Additive W →ₗ[ZMod 2] Additive W)) (e c) (hCe c hc)
    exact h2 Submodule.mem_top
  obtain ⟨m, c, hc, hbij⟩ := exists_bijective_psi hHyp hspan'
  have hinf := inf_eq_bot hHyp hspan'
  have hsup : ∀ g ∈ C ⊔ Ls, e g ∈ Cent Ls' ⊔ Ls' := by
    intro g hg
    have h1 : e g ∈ (C ⊔ Ls).map e.toMonoidHom := ⟨g, hg, rfl⟩
    rw [Subgroup.map_sup] at h1
    have hle : C.map e.toMonoidHom ≤ Cent Ls' := by
      rintro _ ⟨a, ha, rfl⟩
      exact hCe a ha
    exact (sup_le_sup hle le_rfl : C.map e.toMonoidHom ⊔ Ls' ≤ Cent Ls' ⊔ Ls') h1
  let φ : ↥(C ⊔ Ls) →* ↥(Cent Ls' ⊔ Ls') :=
    (e.toMonoidHom.comp (C ⊔ Ls).subtype).codRestrict _ fun g => hsup g g.2
  have hφ : ∀ g : ↥(C ⊔ Ls), ((φ g : ↥(Cent Ls' ⊔ Ls')) : Additive W ≃ₗ[ZMod 2] _) = e g :=
    fun _ => rfl
  let θ : ↥(C ⊔ Ls) →* MulAut (Multiplicative (Fin m → ZMod 2)) :=
    (toMulAutPi m).comp ((theta hHyp hc hbij).comp ((proj hinf).comp φ))
  have hpC : ∀ a (ha : a ∈ C) (has : a ∈ C ⊔ Ls),
      proj hinf (φ ⟨a, has⟩) = ⟨e a, hCe a ha⟩ := by
    intro a ha has
    have : φ ⟨a, has⟩ = ⟨e a, Subgroup.mem_sup_left (hCe a ha)⟩ := rfl
    rw [this]
    exact proj_of_mem_left hinf (hCe a ha)
  refine ⟨m, θ, fun l hl => ?_, fun a ha h1 => ?_, fun B hB => ?_, ?_⟩
  · show toMulAutPi m (theta hHyp hc hbij (proj hinf (φ ⟨l, _⟩))) = 1
    have : proj hinf (φ ⟨l, Subgroup.mem_sup_right hl⟩) = 1 :=
      proj_of_mem_right hinf (l := e l) ⟨l, hl, rfl⟩
    rw [this, map_one, map_one]
  · change toMulAutPi m (theta hHyp hc hbij (proj hinf (φ ⟨a, Subgroup.mem_sup_left ha⟩))) = 1
      at h1
    rw [hpC a ha] at h1
    have h2 : theta hHyp hc hbij ⟨e a, hCe a ha⟩ = 1 := by
      refine LinearEquiv.ext fun v => ?_
      have := congrArg (fun f : MulAut (Multiplicative (Fin m → ZMod 2)) =>
        (f (Multiplicative.ofAdd v)).toAdd) h1
      exact this
    have h3 := eq_one_of_theta_eq_one hHyp hc hbij h2
    have h4 : e a = 1 := congrArg Subtype.val h3
    exact e.injective (h4.trans (map_one e).symm)
  ·
    set B' : Subgroup ↥(Cent Ls') := (B.map e.toMonoidHom).subgroupOf (Cent Ls') with hB'
    have hmemB' : ∀ b' : ↥(Cent Ls'), b' ∈ B' ↔ e.symm b' ∈ B := by
      intro b'
      rw [hB', Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨b, hb, hbe⟩
        have : e.symm b' = b := by rw [← hbe]; exact e.symm_apply_apply b
        rw [this]
        exact hb
      · intro hb
        exact ⟨_, hb, e.apply_symm_apply _⟩
    have h1 := card_fix hHyp hc hbij B'
    rw [hfinY'] at h1
    have e1 : ↥(fixV B) ≃ {x : Additive W // ∀ b ∈ B', (b : Additive W ≃ₗ[ZMod 2] _) x = x} :=
      { toFun := fun w => ⟨Additive.ofMul (w : W), fun b hb => by
          have h2 := (w.2 : ∀ x ∈ B, x (w : W) = w) (e.symm b) ((hmemB' b).1 hb)
          have h3 : (b : Additive W ≃ₗ[ZMod 2] _) = e (e.symm b) := (e.apply_symm_apply _).symm
          rw [h3, linEquiv_apply, toMul_ofMul, h2]⟩
        invFun := fun x => ⟨(x : Additive W).toMul, fun b hb => by
          have h2 := x.2 ⟨e b, hCe b (hB hb)⟩ ((hmemB' _).2 (by
            show e.symm (e b) ∈ B
            rw [MulEquiv.symm_apply_apply]
            exact hb))
          have h3 := congrArg Additive.toMul h2
          rw [linEquiv_apply, toMul_ofMul] at h3
          exact h3⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have e2 : ↥(fixV ((B.subgroupOf (C ⊔ Ls)).map θ)) ≃
        {v : Fin m → ZMod 2 // ∀ b ∈ B', theta hHyp hc hbij b v = v} :=
      { toFun := fun v => ⟨(v : Multiplicative (Fin m → ZMod 2)).toAdd, fun b hb => by
          have hbB := (hmemB' b).1 hb
          have h2 := (v.2 : ∀ x ∈ (B.subgroupOf (C ⊔ Ls)).map θ,
              x (v : Multiplicative (Fin m → ZMod 2)) = v)
            (θ ⟨e.symm b, Subgroup.mem_sup_left (hB hbB)⟩)
            ⟨⟨e.symm b, Subgroup.mem_sup_left (hB hbB)⟩, hbB, rfl⟩
          change toMulAutPi m (theta hHyp hc hbij
            (proj hinf (φ ⟨e.symm b, Subgroup.mem_sup_left (hB hbB)⟩)))
              (v : Multiplicative (Fin m → ZMod 2)) = v at h2
          rw [hpC _ (hB hbB)] at h2
          have h3 : (⟨e (e.symm b), hCe _ (hB hbB)⟩ : ↥(Cent Ls')) = b :=
            Subtype.ext (e.apply_symm_apply _)
          rw [h3] at h2
          change Multiplicative.ofAdd (theta hHyp hc hbij b
            (v : Multiplicative (Fin m → ZMod 2)).toAdd) = (v : Multiplicative _) at h2
          exact congrArg Multiplicative.toAdd h2⟩
        invFun := fun v => ⟨Multiplicative.ofAdd (v : Fin m → ZMod 2), by
          rintro _ ⟨⟨b, hbS⟩, hbB, rfl⟩
          have hbB' : b ∈ B := hbB
          change toMulAutPi m (theta hHyp hc hbij (proj hinf (φ ⟨b, hbS⟩)))
            (Multiplicative.ofAdd (v : Fin m → ZMod 2)) = _
          rw [hpC b (hB hbB') hbS]
          change Multiplicative.ofAdd (theta hHyp hc hbij _ (v : Fin m → ZMod 2)) = _
          have h2 := v.2 ⟨e b, hCe b (hB hbB')⟩ ((hmemB' _).2 (by
            show e.symm (e b) ∈ B
            rw [MulEquiv.symm_apply_apply]
            exact hbB'))
          rw [h2]⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e1, Nat.card_congr e2]
    exact h1
  · have h1 := card_eq hbij
    rw [hfinY'] at h1
    exact h1

theorem exists_rep [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {Ls : Subgroup (MulAut W)}
    {Yg : Subgroup W} (hmaps : ∀ l ∈ Ls, ∀ y ∈ Yg, l y ∈ Yg)
    (honto : ∀ τ : MulAut ↥Yg, ∃ l ∈ Ls, ∀ y : Yg, l (y : W) = (τ y : W))
    {d : ℕ} (hd : 2 ≤ d) (hYd : Nat.card Yg = 2 ^ d)
    (hspan : ⨆ c ∈ Subgroup.centralizer (Ls : Set (MulAut W)), Yg.map c.toMonoidHom = ⊤) :
    ∃ (m : ℕ) (Vt : Type) (_ : CommGroup Vt) (_ : Finite Vt), (∀ v : Vt, v ^ 2 = 1) ∧
      Nat.card Vt = 2 ^ m ∧
      ∃ θ : ↥(Subgroup.centralizer (Ls : Set (MulAut W)) ⊔ Ls) →* MulAut Vt,
        (∀ l (hl : l ∈ Ls), θ ⟨l, Subgroup.mem_sup_right hl⟩ = 1) ∧
        (∀ a (ha : a ∈ Subgroup.centralizer (Ls : Set (MulAut W))),
          θ ⟨a, Subgroup.mem_sup_left ha⟩ = 1 → a = 1) ∧
        (∀ B : Subgroup (MulAut W), B ≤ Subgroup.centralizer (Ls : Set (MulAut W)) →
          Nat.card (fixV B) = Nat.card (fixV ((B.subgroupOf _).map θ)) ^ d) ∧
        Nat.card W = (2 ^ m) ^ d := by
  obtain ⟨m, θ, h1, h2, h3, h4⟩ := exists_rep' hW hmaps honto hd hYd hspan
  have hsq : ∀ v : Multiplicative (Fin m → ZMod 2), v ^ 2 = 1 := by
    intro v
    apply Multiplicative.toAdd.injective
    funext i
    rw [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply]
    generalize (Multiplicative.toAdd v) i = x
    fin_cases x <;> rfl
  have hcard : Nat.card (Multiplicative (Fin m → ZMod 2)) = 2 ^ m := by
    show Nat.card (Fin m → ZMod 2) = 2 ^ m
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  exact ⟨m, Multiplicative (Fin m → ZMod 2), inferInstance, inferInstance, hsq, hcard, θ, h1, h2,
    h3, h4⟩

end CFSG.Quasithin.H13.Mult
