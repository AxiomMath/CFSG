module

public import CFSG.Sporadic.SuzRecog.B0GluingPlane

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog.B0Gluing

open Subgroup CFSG.ComponentClassification.AS81.SuzB0 CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
  CFSG.Sporadic.SuzRecog.B0GluingData
open scoped Pointwise

section Chart


@[expose] noncomputable def thetaJ (i : ℕ) : ↥J0 ≃* ↥J0 :=
  (j0Equiv.trans (conjAutS ⟨thetaR i, thetaR_mem i⟩)).trans j0Equiv.symm

theorem thetaJ_tE {i k : ℕ} (hi : i < 36) (hk : k < 64) :
    thetaJ i ⟨tE k, T0_le_J0 (tE_mem hk)⟩ =
      ⟨tE (thetaPerms[i]!)[k]!, T0_le_J0 (tE_mem (theta_spec hi hk).1)⟩ := by
  apply j0Equiv.injective
  apply Subtype.ext
  rw [thetaJ, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, MulEquiv.trans_apply,
    conjAutS_apply, j0Equiv_apply, j0Equiv_apply, (theta_spec hi hk).2]

theorem thetaJ_symm_mem {i : ℕ} (hi : i < 36) {x : ↥J0} (hx : (x : Equiv.Perm (Fin 1782)) ∈ T0) :
    (((thetaJ i).symm x : ↥J0) : Equiv.Perm (Fin 1782)) ∈ T0 := by
  obtain ⟨k, hk, hxk⟩ := exists_tE hx
  obtain ⟨hq, hpq⟩ := (theta_parts hi).2.2.2 k hk
  have e := thetaJ_tE hi hq
  have hx' : x = ⟨tE (thetaPerms[i]!)[(thetaInvPerms[i]!)[k]!]!,
      T0_le_J0 (tE_mem (theta_spec hi hq).1)⟩ := Subtype.ext (by
    show (x : Equiv.Perm (Fin 1782)) = tE (thetaPerms[i]!)[(thetaInvPerms[i]!)[k]!]!
    rw [hpq, hxk])
  rw [hx', ← e, MulEquiv.symm_apply_apply]
  exact tE_mem hq

theorem factorization_card_J0 : (Nat.card ↥J0).factorization 2 = 6 := by
  rw [card_J0, show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem exists_conj_T0 (β : ↥T0 →* ↥J0) (hβ : Function.Injective β) :
    ∃ g : ↥J0, ∀ y : ↥T0, ((g * β y * g⁻¹ : ↥J0) : Equiv.Perm (Fin 1782)) ∈ T0 := by
  have hP : Nat.card β.range = 2 ^ (Nat.card ↥J0).factorization 2 := by
    rw [factorization_card_J0, ← Nat.card_congr (MonoidHom.ofInjective hβ).toEquiv, card_T0]
    norm_num
  have hQ : Nat.card (T0.subgroupOf J0) = 2 ^ (Nat.card ↥J0).factorization 2 := by
    rw [factorization_card_J0, Nat.card_congr (subgroupOfEquivOfLe T0_le_J0).toEquiv, card_T0]
    norm_num
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥J0 (Sylow.ofCard β.range hP)
    (Sylow.ofCard (T0.subgroupOf J0) hQ)
  refine ⟨g, fun y => ?_⟩
  have hmem : MulAut.conj g • β y ∈ MulAut.conj g • (Sylow.ofCard β.range hP : Subgroup ↥J0) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ (by rw [Sylow.coe_ofCard]; exact ⟨y, rfl⟩)
  rw [← Sylow.coe_subgroup_smul, hg, Sylow.coe_ofCard] at hmem
  exact mem_subgroupOf.mp hmem

theorem exists_chart {G : Type*} [Group G] (φ : ↥(invE 1) →* G) (hφ : Function.Injective φ)
    (ι : ↥J0 →* G) (hι : Function.Injective ι)
    (hT : ∀ y (hy : y ∈ T0), φ ⟨y, T0_le_invE hy⟩ ∈ ι.range)
    (hR : ∀ y (hy : y ∈ Model.R0) (x : ↥J0),
      φ ⟨y, R0_le_invE hy⟩ * ι x = ι x * φ ⟨y, R0_le_invE hy⟩)
    (hz : ∀ g : G, g * φ ⟨suzInv 1, suzInv_mem_invE⟩ = φ ⟨suzInv 1, suzInv_mem_invE⟩ * g →
      g ∈ φ.range) :
    ∃ ι' : ↥J0 →* G, Function.Injective ι' ∧ ι'.range = ι.range ∧
      ∀ y (hy : y ∈ T0), ι' ⟨y, T0_le_J0 hy⟩ = φ ⟨y, T0_le_invE hy⟩ := by
  classical
  let φT : ↥T0 →* G := φ.comp (inclusion T0_le_invE)
  have hφT : ∀ y, φT y ∈ ι.range := fun y => hT y.1 y.2
  let eι := MonoidHom.ofInjective hι
  let β₀ : ↥T0 →* ↥J0 := eι.symm.toMonoidHom.comp (φT.codRestrict ι.range hφT)
  have hβ₀ : ∀ y, ι (β₀ y) = φT y := fun y => by
    have h := MonoidHom.ofInjective_apply hι (x := β₀ y)
    rw [show eι (β₀ y) = φT.codRestrict ι.range hφT y from eι.apply_symm_apply _] at h
    exact h.symm
  have hβ₀inj : Function.Injective β₀ := fun y y' h => by
    have h1 := hβ₀ y
    rw [h, hβ₀ y'] at h1
    exact (inclusion_injective T0_le_invE) (hφ h1.symm)
  obtain ⟨g, hg⟩ := exists_conj_T0 β₀ hβ₀inj
  let f : Equiv.Perm (Fin 1782) → Equiv.Perm (Fin 1782) := fun x =>
    if h : x ∈ T0 then ((g * β₀ ⟨x, h⟩ * g⁻¹ : ↥J0) : Equiv.Perm (Fin 1782)) else 1
  have hf : ∀ x (hx : x ∈ T0), f x = ((g * β₀ ⟨x, hx⟩ * g⁻¹ : ↥J0) : Equiv.Perm (Fin 1782)) :=
    fun x hx => dite_eq_left hx
  have hfmem : ∀ x ∈ T0, f x ∈ T0 := fun x hx => by rw [hf x hx]; exact hg _
  have hfmul : ∀ x ∈ T0, ∀ y ∈ T0, f (x * y) = f x * f y := fun x hx y hy => by
    rw [hf _ (mul_mem hx hy), hf x hx, hf y hy, ← Subgroup.coe_mul]
    congr 1
    rw [show (⟨x * y, mul_mem hx hy⟩ : ↥T0) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, map_mul]
    group
  have hfsurj : ∀ y ∈ T0, ∃ x ∈ T0, f x = y := by
    let F : ↥T0 → ↥T0 := fun x => ⟨f x, hfmem x x.2⟩
    have hF : Function.Injective F := fun x x' h => by
      have h1 : f x = f x' := congrArg Subtype.val h
      rw [hf x x.2, hf x' x'.2] at h1
      have h2 := mul_right_cancel (mul_left_cancel (Subtype.ext h1 : g * β₀ ⟨x, x.2⟩ * g⁻¹ =
        g * β₀ ⟨x', x'.2⟩ * g⁻¹))
      exact hβ₀inj h2
    intro y hy
    obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp hF) ⟨y, hy⟩
    exact ⟨x, x.2, congrArg Subtype.val hx⟩
  let ι₁ : ↥J0 →* G := ι.comp (MulAut.conj g⁻¹).toMonoidHom
  have hι₁ : ∀ x (hx : x ∈ T0), ι₁ ⟨f x, T0_le_J0 (hfmem x hx)⟩ = φ ⟨x, T0_le_invE hx⟩ := by
    intro x hx
    have e : (⟨f x, T0_le_J0 (hfmem x hx)⟩ : ↥J0) = g * β₀ ⟨x, hx⟩ * g⁻¹ :=
      Subtype.ext (hf x hx)
    show ι (MulAut.conj g⁻¹ _) = _
    rw [e, MulAut.conj_apply, inv_inv]
    rw [show g⁻¹ * (g * β₀ ⟨x, hx⟩ * g⁻¹) * g = β₀ ⟨x, hx⟩ by group, hβ₀]
    rfl
  obtain ⟨i, hi, t, ht, r, hr, hdec⟩ := exists_decomp hfmem hfmul hfsurj
  let tJ : ↥J0 := ⟨tE t, T0_le_J0 (tE_mem ht)⟩
  let ε : ↥J0 ≃* ↥J0 := (MulAut.conj tJ).trans (thetaJ i)
  let ι₂ : ↥J0 →* G := ι₁.comp ε.toMonoidHom
  let f₂ : Equiv.Perm (Fin 1782) → Equiv.Perm (Fin 1782) := fun x =>
    if h : x ∈ T0 then ((ε.symm ⟨f x, T0_le_J0 (hfmem x h)⟩ : ↥J0) : Equiv.Perm (Fin 1782)) else 1
  have hf₂ : ∀ x (hx : x ∈ T0),
      f₂ x = ((ε.symm ⟨f x, T0_le_J0 (hfmem x hx)⟩ : ↥J0) : Equiv.Perm (Fin 1782)) :=
    fun x hx => dite_eq_left hx
  have hεsymm : ∀ y : ↥J0, (ε.symm y : ↥J0) = tJ⁻¹ * (thetaJ i).symm y * tJ := fun y => by
    show (MulAut.conj tJ).symm ((thetaJ i).symm y) = _
    rw [MulAut.conj_symm_apply]
  have hf₂mem : ∀ x (hx : x ∈ T0), f₂ x ∈ T0 := fun x hx => by
    rw [hf₂ x hx, hεsymm]
    exact mul_mem (mul_mem (inv_mem (tE_mem ht)) (thetaJ_symm_mem hi (hfmem x hx))) (tE_mem ht)
  have hf₂mul : ∀ x ∈ T0, ∀ y ∈ T0, f₂ (x * y) = f₂ x * f₂ y := fun x hx y hy => by
    have e : (⟨f (x * y), T0_le_J0 (hfmem _ (mul_mem hx hy))⟩ : ↥J0) =
        ⟨f x, T0_le_J0 (hfmem x hx)⟩ * ⟨f y, T0_le_J0 (hfmem y hy)⟩ :=
      Subtype.ext (hfmul x hx y hy)
    rw [hf₂ _ (mul_mem hx hy), hf₂ x hx, hf₂ y hy, e, map_mul, Subgroup.coe_mul]
  have hι₂ : ∀ x (hx : x ∈ T0), ι₂ ⟨f₂ x, T0_le_J0 (hf₂mem x hx)⟩ = φ ⟨x, T0_le_invE hx⟩ := by
    intro x hx
    have e : (⟨f₂ x, T0_le_J0 (hf₂mem x hx)⟩ : ↥J0) = ε.symm ⟨f x, T0_le_J0 (hfmem x hx)⟩ :=
      Subtype.ext (hf₂ x hx)
    show ι₁ (ε _) = _
    rw [e, MulEquiv.apply_symm_apply, hι₁ x hx]
  have hgen : ∀ j < 4, f₂ (t0Gen j) = tE (gammaGen r j) := by
    intro j hj
    have hgg := gammaGen_lt hr hj
    have hct := tE_mulP (tE_mulP ht hgg).1 (tE_invP ht).1
    have hctP : ctGamma t r j < 64 := hct.1
    have e1 : (⟨f (t0Gen j), T0_le_J0 (hfmem _ (t0Gen_mem_T0 hj))⟩ : ↥J0) =
        ε ⟨tE (gammaGen r j), T0_le_J0 (tE_mem hgg)⟩ := by
      apply Subtype.ext
      show f (t0Gen j) = ((thetaJ i (MulAut.conj tJ ⟨tE (gammaGen r j), _⟩) : ↥J0) :
        Equiv.Perm (Fin 1782))
      have e2 : MulAut.conj tJ ⟨tE (gammaGen r j), T0_le_J0 (tE_mem hgg)⟩ =
          ⟨tE (ctGamma t r j), T0_le_J0 (tE_mem hctP)⟩ := by
        rw [MulAut.conj_apply]
        apply Subtype.ext
        show tE t * tE (gammaGen r j) * (tE t)⁻¹ = tE (ctGamma t r j)
        rw [ctGamma, hct.2, (tE_mulP ht hgg).2, (tE_invP ht).2]
      rw [e2, thetaJ_tE hi hctP, hdec j hj]
    rw [hf₂ _ (t0Gen_mem_T0 hj), e1, MulEquiv.symm_apply_apply]
  have htree := gamma_tree hf₂mul hr hgen
  let Φ : Equiv.Perm (Fin 1782) → G := fun x => if h : x ∈ invE 1 then φ ⟨x, h⟩ else 1
  let Ι : Equiv.Perm (Fin 1782) → G := fun x => if h : x ∈ J0 then ι₂ ⟨x, h⟩ else 1
  have hΦ : ∀ x (hx : x ∈ invE 1), Φ x = φ ⟨x, hx⟩ := fun x hx => dite_eq_left hx
  have hΙ : ∀ x (hx : x ∈ J0), Ι x = ι₂ ⟨x, hx⟩ := fun x hx => dite_eq_left hx
  have hr0 : r = 0 := by
    refine plane_test (Φ := Φ) (Ι := Ι) (fun x hx y hy => ?_) (fun x hx y hy h => ?_)
      (fun x hx y hy => ?_) (fun y hy x hx => ?_) (fun g' hg' => ?_) hr (fun k hk => ?_)
    · rw [hΦ _ (mul_mem hx hy), hΦ x hx, hΦ y hy, ← map_mul]
      rfl
    · rw [hΦ x hx, hΦ y hy] at h
      exact congrArg Subtype.val (hφ h)
    · rw [hΙ _ (mul_mem hx hy), hΙ x hx, hΙ y hy, ← map_mul]
      rfl
    · rw [hΦ y (R0_le_invE hy), hΙ x hx]
      exact hR y hy _
    · rw [hΦ _ suzInv_mem_invE] at hg'
      obtain ⟨k, hk⟩ := hz g' hg'
      exact ⟨k, k.2, by rw [hΦ _ k.2]; exact hk⟩
    · obtain ⟨hk', hfk⟩ := htree k hk
      rw [hΦ _ (T0_le_invE (tE_mem hk)), hΙ _ (T0_le_J0 (tE_mem hk')), ← hι₂ _ (tE_mem hk)]
      congr 1
      exact Subtype.ext hfk
  subst hr0
  have hgen0 : ∀ j < 4, f₂ (t0Gen j) = t0Gen j := fun j hj => by
    have hz0 : (gammaReps.getD 0 []).getD j 0 = 0 := by interval_cases j <;> rfl
    rw [hgen j hj, gammaGen, hz0, zI_zero, (tE_mulP (gP_spec hj).1 tE_oneI.1).2, tE_oneI.2,
      mul_one, (gP_spec hj).2]
  have hid : ∀ x ∈ closure {g | ∃ i < 4, t0Gen i = g}, f₂ x = x := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      exact hgen0 j hj
    | one => exact hom_one hf₂mul
    | mul x y hx hy ihx ihy =>
      rw [hf₂mul x (closure_t0Gen_le_T0 hx) y (closure_t0Gen_le_T0 hy), ihx, ihy]
    | inv x hx ihx => rw [hom_inv hf₂mul (closure_t0Gen_le_T0 hx), ihx]
  refine ⟨ι₂, ?_, ?_, fun y hy => ?_⟩
  · intro x x' h
    have h1 : ι (MulAut.conj g⁻¹ (ε x)) = ι (MulAut.conj g⁻¹ (ε x')) := h
    exact ε.injective ((MulAut.conj g⁻¹).injective (hι h1))
  · show (ι.comp ((MulAut.conj g⁻¹).toMonoidHom.comp ε.toMonoidHom)).range = ι.range
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _ (fun y =>
      ⟨ε.symm ((MulAut.conj g⁻¹).symm y), by
        show MulAut.conj g⁻¹ (ε (ε.symm _)) = y
        rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]⟩), ← MonoidHom.range_eq_map]
  · have h1 := hι₂ y hy
    have e : (⟨f₂ y, T0_le_J0 (hf₂mem y hy)⟩ : ↥J0) = ⟨y, T0_le_J0 hy⟩ := Subtype.ext (by
      rw [T0_eq] at hy
      exact hid y hy)
    rw [e] at h1
    exact h1

end Chart

end CFSG.Sporadic.SuzRecog.B0Gluing
