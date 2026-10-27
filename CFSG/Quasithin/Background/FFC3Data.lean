module

public import CFSG.Quasithin.Background.FFC3Offender
public import CFSG.Quasithin.Background.D2Basic
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin

namespace FFC

open Matrix

abbrev MV (n : ℕ) : Type := Multiplicative (Fin n → ZMod 2)

@[expose] def actN {n : ℕ} (g : GL (Fin n) (ZMod 2)) (x : MV n) : MV n :=
  Multiplicative.ofAdd ((g : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (Multiplicative.toAdd x))

@[expose] def invTGL {n : ℕ} (g : GL (Fin n) (ZMod 2)) : GL (Fin n) (ZMod 2) :=
  ⟨((g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ,
    (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ,
    by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.transpose_one]⟩

@[expose] def actD {n : ℕ} (g : GL (Fin n) (ZMod 2)) (x : MV n) : MV n := actN (invTGL g) x

theorem actN_mul {n : ℕ} (a b : GL (Fin n) (ZMod 2)) (x : MV n) :
    actN (a * b) x = actN a (actN b x) := by
  simp [actN, Matrix.mulVec_mulVec]

theorem actN_one {n : ℕ} (x : MV n) : actN (1 : GL (Fin n) (ZMod 2)) x = x := by
  simp [actN]

theorem invTGL_mul {n : ℕ} (a b : GL (Fin n) (ZMod 2)) : invTGL (a * b) = invTGL a * invTGL b := by
  apply Units.ext
  simp [invTGL, Matrix.transpose_mul]

theorem invTGL_one {n : ℕ} : invTGL (1 : GL (Fin n) (ZMod 2)) = 1 := by
  apply Units.ext
  simp [invTGL]

theorem actD_mul {n : ℕ} (a b : GL (Fin n) (ZMod 2)) (x : MV n) :
    actD (a * b) x = actD a (actD b x) := by
  simp [actD, invTGL_mul, actN_mul]

theorem actD_one {n : ℕ} (x : MV n) : actD (1 : GL (Fin n) (ZMod 2)) x = x := by
  simp [actD, invTGL_one, actN_one]

@[expose] def actNEquiv {n : ℕ} (g : GL (Fin n) (ZMod 2)) : MV n ≃* MV n where
  toFun := actN g
  invFun := actN g⁻¹
  left_inv x := by rw [← actN_mul, inv_mul_cancel, actN_one]
  right_inv x := by rw [← actN_mul, mul_inv_cancel, actN_one]
  map_mul' x y := by
    simp [actN, Matrix.mulVec_add]

@[expose] def actDEquiv {n : ℕ} (g : GL (Fin n) (ZMod 2)) : MV n ≃* MV n where
  toFun := actD g
  invFun := actD g⁻¹
  left_inv x := by rw [← actD_mul, inv_mul_cancel, actD_one]
  right_inv x := by rw [← actD_mul, mul_inv_cancel, actD_one]
  map_mul' x y := by
    simp [actD, actN, Matrix.mulVec_add]

theorem dual_fixed_iff {n : ℕ} (a : GL (Fin n) (ZMod 2)) (w : Fin n → ZMod 2) :
    (((a⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ).mulVec w = w ↔
      ((a : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ).mulVec w = w := by
  constructor
  · intro h
    have h2 := congrArg ((a : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ).mulVec h
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.transpose_one, Matrix.one_mulVec] at h2
    exact h2.symm
  · intro h
    have h2 := congrArg (((a⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ).mulVec h
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.transpose_one, Matrix.one_mulVec] at h2
    exact h2.symm

section Data

variable {V : Type} [CommGroup V] {m : ℕ}

structure SumDualData (m : ℕ) (ρ : GL (Fin (m + 2)) (ZMod 2) →* MulAut V) (C : Subgroup V) where
  Θ : V ≃* MV (m + 2) × MV (m + 2) × ↥C
  equi : ∀ (g : GL (Fin (m + 2)) (ZMod 2)) (v : V),
    Θ (ρ g v) = (actN g (Θ v).1, actD g (Θ v).2.1, (Θ v).2.2)

namespace SumDualData

variable {ρ : GL (Fin (m + 2)) (ZMod 2) →* MulAut V} {C : Subgroup V} (D : SumDualData m ρ C)

@[expose] def twist (h : GL (Fin (m + 2)) (ZMod 2)) :
    SumDualData m (ρ.comp (MulAut.conj h).toMonoidHom) C where
  Θ := D.Θ.trans (MulEquiv.prodCongr (actNEquiv h⁻¹)
    (MulEquiv.prodCongr (actDEquiv h⁻¹) (MulEquiv.refl _)))
  equi g v := by
    have h1 := D.equi (h * g * h⁻¹) v
    have hc : (ρ.comp (MulAut.conj h).toMonoidHom) g = ρ (h * g * h⁻¹) := rfl
    show (actN h⁻¹ (D.Θ ((ρ.comp (MulAut.conj h).toMonoidHom) g v)).1,
      actD h⁻¹ (D.Θ ((ρ.comp (MulAut.conj h).toMonoidHom) g v)).2.1,
      (D.Θ ((ρ.comp (MulAut.conj h).toMonoidHom) g v)).2.2) =
      (actN g (actN h⁻¹ (D.Θ v).1), actD g (actD h⁻¹ (D.Θ v).2.1), (D.Θ v).2.2)
    rw [hc, h1]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · show actN h⁻¹ (actN (h * g * h⁻¹) (D.Θ v).1) = actN g (actN h⁻¹ (D.Θ v).1)
      rw [← actN_mul, ← actN_mul]
      congr 1
      group
    · show actD h⁻¹ (actD (h * g * h⁻¹) (D.Θ v).2.1) = actD g (actD h⁻¹ (D.Θ v).2.1)
      rw [← actD_mul, ← actD_mul]
      congr 1
      group

theorem card_MV (n : ℕ) : Nat.card (MV n) = 2 ^ n := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
    Fintype.card_fin]

include D in
theorem card_V : Nat.card V = 2 ^ (m + 2) * 2 ^ (m + 2) * Nat.card C := by
  rw [Nat.card_congr D.Θ.toEquiv, Nat.card_prod, Nat.card_prod, card_MV, mul_assoc]

theorem fixV_map_iff {A' : Subgroup (GL (Fin (m + 2)) (ZMod 2))} (v : V) :
    v ∈ fixV (A'.map ρ) ↔ Multiplicative.toAdd (D.Θ v).1 ∈ fixNat A' ∧
      Multiplicative.toAdd (D.Θ v).2.1 ∈ fixDual A' := by
  constructor
  · intro h
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · have hv : ρ a v = v := h (ρ a) ⟨a, ha, rfl⟩
      have e := D.equi a v
      rw [hv] at e
      have e1 := congrArg Prod.fst e
      have e2 : Multiplicative.toAdd (D.Θ v).1 =
          (a : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)).mulVec (Multiplicative.toAdd (D.Θ v).1) :=
        congrArg Multiplicative.toAdd e1
      exact e2.symm
    · have hv : ρ a v = v := h (ρ a) ⟨a, ha, rfl⟩
      have e := D.equi a v
      rw [hv] at e
      have e1 := congrArg (fun p => p.2.1) e
      have e2 : Multiplicative.toAdd (D.Θ v).2.1 =
          (((a⁻¹ : GL (Fin (m + 2)) (ZMod 2)) : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2))ᵀ).mulVec
            (Multiplicative.toAdd (D.Θ v).2.1) :=
        congrArg Multiplicative.toAdd e1
      exact (dual_fixed_iff a _).1 e2.symm
  · rintro ⟨h1, h2⟩ x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    apply D.Θ.injective
    rw [D.equi a v]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · exact congrArg Multiplicative.ofAdd (h1 a ha)
    · exact congrArg Multiplicative.ofAdd ((dual_fixed_iff a _).2 (h2 a ha))

include D in
theorem card_fixV_map (A' : Subgroup (GL (Fin (m + 2)) (ZMod 2))) :
    Nat.card (fixV (A'.map ρ)) = Nat.card (fixNat A') * Nat.card (fixDual A') * Nat.card C := by
  let e : ↥(fixV (A'.map ρ)) ≃ ↥(fixNat A') × ↥(fixDual A') × ↥C :=
    { toFun := fun v => (⟨Multiplicative.toAdd (D.Θ v.1).1, ((D.fixV_map_iff v.1).1 v.2).1⟩,
        ⟨Multiplicative.toAdd (D.Θ v.1).2.1, ((D.fixV_map_iff v.1).1 v.2).2⟩, (D.Θ v.1).2.2)
      invFun := fun q => ⟨D.Θ.symm (Multiplicative.ofAdd q.1.1, Multiplicative.ofAdd q.2.1.1, q.2.2), by
        rw [D.fixV_map_iff]
        simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd]
        exact ⟨q.1.2, q.2.1.2⟩⟩
      left_inv := fun v => by
        apply Subtype.ext
        simp
      right_inv := fun q => by
        simp }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod, mul_assoc]

theorem fixV_UT_iff (v : V) :
    v ∈ fixV ((UT (m + 2)).map ρ) ↔
      (∀ j : Fin (m + 2), j ≠ 0 → Multiplicative.toAdd (D.Θ v).1 j = 0) ∧
        ∀ j : Fin (m + 2), j ≠ Fin.last (m + 1) → Multiplicative.toAdd (D.Θ v).2.1 j = 0 := by
  rw [D.fixV_map_iff]
  exact and_congr (fixed_UT_nat (m := m + 1) _) (fixed_UT_dual (m := m + 1) _)

theorem eq_smul_single_zero {x : Fin (m + 2) → ZMod 2} (hx : ∀ j : Fin (m + 2), j ≠ 0 → x j = 0) :
    x = x 0 • (Pi.single 0 1 : Fin (m + 2) → ZMod 2) := by
  funext j
  by_cases hj : j = 0
  · subst hj
    simp
  · simp [hx j hj, Pi.single_eq_of_ne hj]

theorem eq_smul_single_last {x : Fin (m + 2) → ZMod 2}
    (hx : ∀ j : Fin (m + 2), j ≠ Fin.last (m + 1) → x j = 0) :
    x = x (Fin.last (m + 1)) • (Pi.single (Fin.last (m + 1)) 1 : Fin (m + 2) → ZMod 2) := by
  funext j
  by_cases hj : j = Fin.last (m + 1)
  · subst hj
    simp
  · simp [hx j hj, Pi.single_eq_of_ne hj]

include D in
theorem centSub_fixV_UT_iff (s : GL (Fin (m + 2)) (ZMod 2)) :
    ρ s ∈ centSub (fixV ((UT (m + 2)).map ρ)) ↔ s ∈ Pgrp m := by
  constructor
  · intro hs
    have h1 : D.Θ.symm (Multiplicative.ofAdd (Pi.single 0 1), 1, 1) ∈ fixV ((UT (m + 2)).map ρ) := by
      rw [D.fixV_UT_iff]
      simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd, toAdd_one, Pi.zero_apply, implies_true,
        and_true]
      intro j hj
      exact Pi.single_eq_of_ne hj _
    have h2 : D.Θ.symm (1, Multiplicative.ofAdd (Pi.single (Fin.last (m + 1)) 1), 1) ∈
        fixV ((UT (m + 2)).map ρ) := by
      rw [D.fixV_UT_iff]
      simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd, toAdd_one, Pi.zero_apply, implies_true,
        true_and]
      intro j hj
      exact Pi.single_eq_of_ne hj _
    have e1 := hs _ h1
    have e2 := hs _ h2
    have f1 := D.equi s (D.Θ.symm (Multiplicative.ofAdd (Pi.single 0 1), 1, 1))
    have f2 := D.equi s (D.Θ.symm (1, Multiplicative.ofAdd (Pi.single (Fin.last (m + 1)) 1), 1))
    have e1' : ρ s (D.Θ.symm (Multiplicative.ofAdd (Pi.single 0 1), 1, 1)) =
        D.Θ.symm (Multiplicative.ofAdd (Pi.single 0 1), 1, 1) := e1
    have e2' : ρ s (D.Θ.symm (1, Multiplicative.ofAdd (Pi.single (Fin.last (m + 1)) 1), 1)) =
        D.Θ.symm (1, Multiplicative.ofAdd (Pi.single (Fin.last (m + 1)) 1), 1) := e2
    rw [e1', MulEquiv.apply_symm_apply] at f1
    rw [e2', MulEquiv.apply_symm_apply] at f2
    have g1 := congrArg (fun p => Multiplicative.toAdd p.1) f1
    have g2 := congrArg (fun p => Multiplicative.toAdd p.2.1) f2
    simp only [toAdd_ofAdd] at g1 g2
    refine ⟨?_, ?_⟩
    · show (s : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)).mulVec (Pi.single 0 1) = Pi.single 0 1
      exact g1.symm
    · show ((s : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2))ᵀ).mulVec
        (Pi.single (Fin.last (m + 1)) 1) = Pi.single (Fin.last (m + 1)) 1
      have g2' : (((s⁻¹ : GL (Fin (m + 2)) (ZMod 2)) : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2))ᵀ).mulVec
          (Pi.single (Fin.last (m + 1)) 1) = Pi.single (Fin.last (m + 1)) 1 := g2.symm
      exact (dual_fixed_iff s _).1 g2'
  · intro hs u hu
    obtain ⟨hs1, hs2⟩ := hs
    rw [D.fixV_UT_iff] at hu
    obtain ⟨hu1, hu2⟩ := hu
    show ρ s u = u
    apply D.Θ.injective
    rw [D.equi s u]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · show Multiplicative.ofAdd ((s : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)).mulVec
        (Multiplicative.toAdd (D.Θ u).1)) = (D.Θ u).1
      have hx := eq_smul_single_zero hu1
      have : (s : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)).mulVec (Multiplicative.toAdd (D.Θ u).1) =
          Multiplicative.toAdd (D.Θ u).1 := by
        rw [hx, Matrix.mulVec_smul]
        have hs1' : (s : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)).mulVec (Pi.single 0 1) =
          Pi.single 0 1 := hs1
        rw [hs1']
      rw [this]
      rfl
    · show Multiplicative.ofAdd ((((s⁻¹ : GL (Fin (m + 2)) (ZMod 2)) : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2))ᵀ).mulVec
        (Multiplicative.toAdd (D.Θ u).2.1)) = (D.Θ u).2.1
      have hw := eq_smul_single_last hu2
      rw [dual_fixed_iff s _ |>.2 ?_]
      · rfl
      · rw [hw, Matrix.mulVec_smul]
        have hs2' : ((s : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2))ᵀ).mulVec
            (Pi.single (Fin.last (m + 1)) 1) = Pi.single (Fin.last (m + 1)) 1 := hs2
        rw [hs2']

include D in
theorem centSub_fixV_UT_eq {L : Subgroup (MulAut V)} (hL : ρ.range = L) :
    L ⊓ centSub (fixV ((UT (m + 2)).map ρ)) = (Pgrp m).map ρ := by
  ext x
  constructor
  · rintro ⟨hxL, hxc⟩
    rw [← hL] at hxL
    obtain ⟨s, rfl⟩ := hxL
    exact ⟨s, (D.centSub_fixV_UT_iff s).1 hxc, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨hL ▸ ⟨s, rfl⟩, (D.centSub_fixV_UT_iff s).2 hs⟩

section Std

variable {L : Subgroup (MulAut V)}

@[expose] noncomputable def stdIso (hρ : Function.Injective ρ) (hL : ρ.range = L) :
    ↥(Pgrp m) ≃* ↥(L ⊓ centSub (fixV ((UT (m + 2)).map ρ))) :=
  (Subgroup.equivMapOfInjective (Pgrp m) ρ hρ).trans
    (MulEquiv.subgroupCongr (D.centSub_fixV_UT_eq hL).symm)

theorem stdIso_apply (hρ : Function.Injective ρ) (hL : ρ.range = L) (s : ↥(Pgrp m)) :
    ((D.stdIso hρ hL s : ↥(L ⊓ centSub (fixV ((UT (m + 2)).map ρ)))) : MulAut V) = ρ s := rfl

@[expose] noncomputable def stdPsi (hρ : Function.Injective ρ) (hL : ρ.range = L) :
    ↥(L ⊓ centSub (fixV ((UT (m + 2)).map ρ))) →* GL (Fin m) (ZMod 2) :=
  (psi m).comp (D.stdIso hρ hL).symm.toMonoidHom

theorem stdPsi_surjective (hρ : Function.Injective ρ) (hL : ρ.range = L) :
    Function.Surjective (D.stdPsi hρ hL) :=
  (psi_surjective m).comp (D.stdIso hρ hL).symm.surjective

theorem card_ker_stdPsi (hρ : Function.Injective ρ) (hL : ρ.range = L) :
    Nat.card (D.stdPsi hρ hL).ker = 2 ^ (1 + 2 * m) := by
  have h : (D.stdPsi hρ hL).ker = (psi m).ker.map (D.stdIso hρ hL).toMonoidHom := by
    ext x
    constructor
    · intro hx
      refine ⟨(D.stdIso hρ hL).symm x, hx, by simp⟩
    · rintro ⟨p, hp, rfl⟩
      show (psi m) ((D.stdIso hρ hL).symm ((D.stdIso hρ hL) p)) = 1
      rw [MulEquiv.symm_apply_apply]
      exact hp
  rw [h, ← card_ker_psi m]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ (D.stdIso hρ hL).injective).toEquiv).symm

include D in
theorem std_part6_a (hρ : Function.Injective ρ) (hL : ρ.range = L) :
    ∃ R : Subgroup (MulAut V), R ≤ L ⊓ centSub (fixV ((UT (m + 2)).map ρ)) ∧ IsPGroup 2 R ∧
      Nat.card R = 2 ^ (1 + 2 * m) ∧
      ∃ _ : (R.subgroupOf (L ⊓ centSub (fixV ((UT (m + 2)).map ρ)))).Normal,
        Nonempty (↥(L ⊓ centSub (fixV ((UT (m + 2)).map ρ))) ⧸
          R.subgroupOf (L ⊓ centSub (fixV ((UT (m + 2)).map ρ))) ≃* GL (Fin m) (ZMod 2)) := by
  set H := L ⊓ centSub (fixV ((UT (m + 2)).map ρ)) with hH
  let Ψ := D.stdPsi hρ hL
  have hΨ := D.stdPsi_surjective hρ hL
  let R : Subgroup (MulAut V) := Ψ.ker.map H.subtype
  have hRsub : R.subgroupOf H = Ψ.ker :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective H) _
  have hcard : Nat.card R = 2 ^ (1 + 2 * m) := by
    rw [← D.card_ker_stdPsi hρ hL]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv).symm
  have hnorm : (R.subgroupOf H).Normal := by
    rw [hRsub]
    exact MonoidHom.normal_ker Ψ
  refine ⟨R, Subgroup.map_subtype_le _, IsPGroup.of_card hcard, hcard, hnorm, ?_⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hRsub).trans
    (QuotientGroup.quotientKerEquivOfSurjective Ψ hΨ)⟩

include D in
theorem std_part6_b [Finite V] (hρ : Function.Injective ρ) (hL : ρ.range = L) {A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender L A) :
    ¬ A ≤ CFSG.Open.pCoreOf 2 (L ⊓ centSub (fixV ((UT (m + 2)).map ρ))) := by
  intro hAc
  set H := L ⊓ centSub (fixV ((UT (m + 2)).map ρ)) with hH
  let Ψ := D.stdPsi hρ hL
  have hΨ := D.stdPsi_surjective hρ hL
  have hcore : CFSG.Open.pCore 2 ↥H ≤ Ψ.ker := by
    have : (CFSG.Open.pCore 2 ↥H).Normal := CFSG.LieType.BorelTits.pCore_normal 2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact le_ker_of_normal_isPGroup Ψ hΨ (CFSG.LieType.BorelTits.pCore_isPGroup 2)
  have hAR : ∀ a ∈ A, ∃ s ∈ Rgrp m, ρ s = a := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := hAc ha
    have hxk := hcore hx
    refine ⟨((D.stdIso hρ hL).symm x : ↥(Pgrp m)).1, ?_, ?_⟩
    · rw [mem_Rgrp]
      refine ⟨((D.stdIso hρ hL).symm x).2, ?_⟩
      have h1 : psi m ((D.stdIso hρ hL).symm x) = 1 := hxk
      have h2 := congrArg (fun y : GL (Fin m) (ZMod 2) => (y : Matrix (Fin m) (Fin m) (ZMod 2))) h1
      simpa [psi_val] using h2
    · have h3 := D.stdIso_apply hρ hL ((D.stdIso hρ hL).symm x)
      rw [MulEquiv.apply_symm_apply] at h3
      exact h3.symm
  set A' : Subgroup (GL (Fin (m + 2)) (ZMod 2)) := A.comap ρ with hA'
  have hAL : A ≤ L := hA.1
  have hmap : A'.map ρ = A := by
    rw [hA', Subgroup.map_comap_eq, hL]
    exact inf_eq_right.2 hAL
  have hA'R : A' ≤ Rgrp m := by
    intro s hs
    obtain ⟨t, ht, hts⟩ := hAR (ρ s) hs
    have : t = s := hρ hts
    exact this ▸ ht
  have hA'ne : A' ≠ ⊥ := by
    intro h
    apply hA.2.1
    rw [← hmap, h, Subgroup.map_bot]
  have hoff := model_offender hA'R hA'ne
  have hcardA : Nat.card A = Nat.card A' := by
    rw [← hmap]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective A' ρ hρ).toEquiv).symm
  have hfix : Nat.card (fixV A) = Nat.card (fixNat A') * Nat.card (fixDual A') * Nat.card C := by
    rw [← hmap]
    exact D.card_fixV_map A'
  have hbot := hA.2.2.2 ⊥ bot_le
  have hfixbot : fixV (⊥ : Subgroup (MulAut V)) = ⊤ := by
    ext v
    simp [mem_fixV]
  rw [hfixbot, Subgroup.card_bot, Subgroup.card_top, one_mul, hcardA, hfix, D.card_V] at hbot
  have hC : 0 < Nat.card C := Nat.card_pos
  have : Nat.card A' * (Nat.card (fixNat A') * Nat.card (fixDual A') * Nat.card C) <
      2 ^ (m + 2) * 2 ^ (m + 2) * Nat.card C := by
    calc Nat.card A' * (Nat.card (fixNat A') * Nat.card (fixDual A') * Nat.card C)
        = (Nat.card A' * Nat.card (fixNat A') * Nat.card (fixDual A')) * Nat.card C := by ring
      _ < 2 ^ (m + 2) * 2 ^ (m + 2) * Nat.card C := Nat.mul_lt_mul_of_pos_right hoff hC
  omega

end Std

end SumDualData

section Sylow

variable {ρ : GL (Fin (m + 2)) (ZMod 2) →* MulAut V}

theorem conjHom_injective (hρ : Function.Injective ρ) (h : GL (Fin (m + 2)) (ZMod 2)) :
    Function.Injective (ρ.comp (MulAut.conj h).toMonoidHom) :=
  hρ.comp (MulAut.conj h).injective

theorem conjHom_range (h : GL (Fin (m + 2)) (ZMod 2)) :
    (ρ.comp (MulAut.conj h).toMonoidHom).range = ρ.range := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨h * g * h⁻¹, rfl⟩
  · rintro ⟨s, rfl⟩
    refine ⟨h⁻¹ * s * h, ?_⟩
    show ρ (h * (h⁻¹ * s * h) * h⁻¹) = ρ s
    congr 1
    group

theorem sylow_eq_map_UT [Finite V] (hρ : Function.Injective ρ) {L : Subgroup (MulAut V)}
    (hL : ρ.range = L) {T : Subgroup (MulAut V)} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T L) :
    ∃ h : GL (Fin (m + 2)) (ZMod 2),
      T = (UT (m + 2)).map (ρ.comp (MulAut.conj h).toMonoidHom) := by
  obtain ⟨hTL, hT2, hTi⟩ := hT
  have hmem : ∀ s, ρ s ∈ L := fun s => hL ▸ ⟨s, rfl⟩
  let ρ' : GL (Fin (m + 2)) (ZMod 2) →* ↥L := ρ.codRestrict L hmem
  have hρ's : Function.Surjective ρ' := by
    intro x
    obtain ⟨s, hs⟩ := (hL ▸ x.2 : (x : MulAut V) ∈ ρ.range)
    exact ⟨s, Subtype.ext hs⟩
  have hcomap : (T.subgroupOf L).comap ρ' = T.comap ρ := rfl
  have hidx : (T.comap ρ).index = (T.subgroupOf L).index := by
    rw [← hcomap]
    exact Subgroup.index_comap_of_surjective _ hρ's
  have hp : IsPGroup 2 (T.comap ρ) := hT2.comap_of_injective ρ hρ
  obtain ⟨h, hh⟩ := exists_conj_UT hp (by rw [hidx]; exact hTi)
  refine ⟨h, ?_⟩
  ext x
  constructor
  · intro hx
    have hxL : x ∈ ρ.range := hL ▸ hTL hx
    obtain ⟨s, rfl⟩ := hxL
    have hs : s ∈ T.comap ρ := hx
    refine ⟨h⁻¹ * s * h, (hh s).1 hs, ?_⟩
    show ρ (h * (h⁻¹ * s * h) * h⁻¹) = ρ s
    congr 1
    group
  · rintro ⟨u, hu, rfl⟩
    have : h * u * h⁻¹ ∈ T.comap ρ := by
      rw [hh]
      have : h⁻¹ * (h * u * h⁻¹) * h = u := by group
      rw [this]
      exact hu
    exact this

variable {C : Subgroup V} (D : SumDualData m ρ C)

include D in
theorem SumDualData.sylow_part6 [Finite V] {L : Subgroup (MulAut V)} (hρ : Function.Injective ρ)
    (hL : ρ.range = L) {T : Subgroup (MulAut V)}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T L) :
    (∃ R : Subgroup (MulAut V), R ≤ L ⊓ centSub (fixV T) ∧ IsPGroup 2 R ∧
        Nat.card R = 2 ^ (1 + 2 * m) ∧
        ∃ _ : (R.subgroupOf (L ⊓ centSub (fixV T))).Normal,
          Nonempty (↥(L ⊓ centSub (fixV T)) ⧸ R.subgroupOf (L ⊓ centSub (fixV T)) ≃*
            GL (Fin m) (ZMod 2))) ∧
      ∀ A : Subgroup (MulAut V), IsFFStarOffender L A → ¬ A ≤ CFSG.Open.pCoreOf 2 (L ⊓ centSub (fixV T)) := by
  obtain ⟨h, hh⟩ := sylow_eq_map_UT hρ hL hT
  subst hh
  have hρ' := conjHom_injective hρ h
  have hL' : (ρ.comp (MulAut.conj h).toMonoidHom).range = L := by rw [conjHom_range, hL]
  exact ⟨(D.twist h).std_part6_a hρ' hL', fun A hA => (D.twist h).std_part6_b hρ' hL' hA⟩

end Sylow

end Data

end FFC

end CFSG.Quasithin
