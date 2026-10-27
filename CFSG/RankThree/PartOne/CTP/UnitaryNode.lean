module

public import CFSG.RankThree.PartOne.CTP.UnitaryTransfer
public import CFSG.RankThree.PartOne.CTP.UnitaryForm
public import CFSG.RankThree.PartOne.CTP.NodeMatrix

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.Universal.Unitary (SUid conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.ClassicalGroups.Unitary (herm isUnitaryInvolution_unitaryInvolution)
open scoped MatrixGroups

section FieldLemmas

theorem exists_primitiveRoot_q_sub_one {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 2 ≤ q) : ∃ g : K, IsPrimitiveRoot g (q - 1) := by
  obtain ⟨g, hg⟩ := exists_primitiveRoot_card_sub_one (F := K)
  rw [hK] at hg
  have hsq : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    zify [show 1 ≤ q by omega, show 1 ≤ q ^ 2 by nlinarith]
    ring
  have hdvd : q + 1 ∣ q ^ 2 - 1 := ⟨q - 1, hsq⟩
  have := hg.pow_of_dvd (by omega) hdvd
  have e : (q ^ 2 - 1) / (q + 1) = q - 1 := by
    rw [hsq, Nat.mul_div_cancel_left _ (by omega)]
  rw [e] at this
  exact ⟨_, this⟩

theorem ringEquiv_eq_one_of_fix_unitary {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) (hq : 2 ≤ p ^ f) {τ : K ≃+* K}
    (hτ : Odd (orderOf τ)) {μ : K} (hμ : IsPrimitiveRoot μ (p ^ f - 1)) (hτμ : τ μ = μ) :
    τ = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have : NeZero (p ^ f - 1) := ⟨by omega⟩
  have hq2 : ∀ x : K, (x ^ p ^ f) ^ p ^ f = x := by
    intro x
    rw [← pow_mul, ← sq]
    have := FiniteField.pow_card x
    rwa [← Nat.card_eq_fintype_card, hK] at this
  have hfixF : ∀ y : K, y ^ p ^ f = y → τ y = y := by
    intro y hy
    by_cases hy0 : y = 0
    · rw [hy0, map_zero]
    · have h1 : y ^ (p ^ f - 1) = 1 := by
        have : y * y ^ (p ^ f - 1) = y * 1 := by
          rw [← pow_succ', Nat.sub_add_cancel (by omega), hy, mul_one]
        exact mul_left_cancel₀ hy0 this
      obtain ⟨i, -, rfl⟩ := hμ.eq_pow_of_pow_eq_one h1
      rw [map_pow, hτμ]
  have hroot : ∀ x : K, τ x = x ∨ τ x = x ^ p ^ f := by
    intro x
    have ht : (x + x ^ p ^ f) ^ p ^ f = x + x ^ p ^ f := by
      rw [add_pow_char_pow, hq2, add_comm]
    have hn : (x * x ^ p ^ f) ^ p ^ f = x * x ^ p ^ f := by
      rw [mul_pow, hq2, mul_comm]
    have e1 := hfixF _ ht
    have e2 := hfixF _ hn
    have key : (τ x - x) * (τ x - x ^ p ^ f) = 0 := by
      have : τ (x ^ 2 - (x + x ^ p ^ f) * x + x * x ^ p ^ f) = 0 := by
        have : x ^ 2 - (x + x ^ p ^ f) * x + x * x ^ p ^ f = 0 := by ring
        rw [this, map_zero]
      rw [map_add, map_sub, map_mul, map_pow, e1, e2] at this
      linear_combination this
    rcases mul_eq_zero.mp key with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  have hinv : ∀ x : K, τ (τ x) = x := by
    intro x
    rcases hroot x with h | h
    · rw [h, h]
    · rw [h, map_pow, h, hq2]
  have hsq : τ ^ 2 = 1 := by
    refine RingEquiv.ext fun x => ?_
    change τ (τ x) = x
    exact hinv x
  have h2 : orderOf τ ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hτ
    exact absurd hτ (by decide)

end FieldLemmas

section Node

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)

theorem unitary_node_commute (hq : 4 ≤ 2 ^ f) {K₀ : Type} [Field K₀] [Finite K₀]
    (hK₀ : Nat.card K₀ = 2 ^ f) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (φ : SL(2, K₀) →* SUid (unitaryInvolution K 2 f) 3) (hφ : Function.Injective φ)
    (α : MulAut (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) (hα : α ^ r = 1)
    (hfix : ∀ a, α (suProj h (φ a)) = suProj h (φ a)) :
    ∃ A : primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
      α = primeFormConjHom h _ A ∧ ∀ a,
        ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            ((φ a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          ((φ a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  classical
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  have hnq : ¬ (3 = 3 ∧ 2 ^ f = 2) := by rintro ⟨-, h2⟩; omega
  obtain ⟨⟨A, τ⟩, hx⟩ := primeFormPsi_surjective h hC le_rfl hnq α
  rw [primeFormPsi_apply] at hx
  have hτr : τ ^ r = 1 := by
    have := congrArg (primeFormFieldFactor h hC le_rfl hnq) hα
    rw [map_pow, ← hx, primeFormFieldFactor_apply, map_one] at this
    exact this
  have hτodd : Odd (orderOf τ) := by
    have h1 : orderOf τ ∣ r := orderOf_dvd_of_pow_eq_one hτr
    rcases (Nat.dvd_prime hr).mp h1 with h2 | h2
    · rw [h2]; exact odd_one
    · rw [h2]; exact hr.odd_of_ne_two hr2
  have hα_mk : ∀ g : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
      α (QuotientGroup.mk g) =
        QuotientGroup.mk (primeFormConjSU h _ A (primeFormFieldSU h hC τ g)) := by
    intro g
    rw [← hx, MulAut.mul_apply]
    change primeFormConjAut h _ A (primeFormFieldAut h hC τ (QuotientGroup.mk g)) = _
    rw [primeFormFieldAut_mk, primeFormConjAut_mk]
  let ι : SL(2, K₀) →* gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    (suEquiv h).toMonoidHom.comp φ
  let ψ₁ : SL(2, K₀) →* gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    ((primeFormConjSU h _ A).toMonoidHom.comp (primeFormFieldSU h hC τ).toMonoidHom).comp ι
  have hψ : ψ₁ = ι := by
    have hperf : Group.IsPerfect SL(2, K₀) := isPerfect_sl2 (by rw [hK₀]; exact hq)
    refine CFSG.LieType.Steinberg.eq_of_comp_eq_of_isPerfect
      (π := QuotientGroup.mk' (normOneScalars h
        (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) 3)) ?_ ?_
    · rw [QuotientGroup.ker_mk']
      exact normOneScalars_le_center h _ 3
    · ext a
      have h1 := hfix a
      change α (QuotientGroup.mk (ι a)) = QuotientGroup.mk (ι a) at h1
      rw [hα_mk] at h1
      exact h1
  have hmat : ∀ a, (A : GL (Fin 3) K) * glAut τ (φ a : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹ =
      (φ a : GL (Fin 3) K) := fun a => congrArg Subtype.val (DFunLike.congr_fun hψ a)
  have hmat' : ∀ a, (A : GL (Fin 3) K) * glAut τ (φ a : GL (Fin 3) K) =
      (φ a : GL (Fin 3) K) * (A : GL (Fin 3) K) := fun a => by
    calc (A : GL (Fin 3) K) * glAut τ (φ a : GL (Fin 3) K)
        = ((A : GL (Fin 3) K) * glAut τ (φ a : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹) *
            (A : GL (Fin 3) K) := by group
      _ = (φ a : GL (Fin 3) K) * (A : GL (Fin 3) K) := by rw [hmat a]
  have hτ1 : τ = 1 := by
    let ψ : SL(2, K₀) →* SL(3, K) := (suToSL (unitaryInvolution K 2 f)).comp φ
    have hψinj : Function.Injective ψ := (suToSL_injective _).comp hφ
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := K₀ˣ)
    have hord : orderOf (ψ (CFSG.ClassicalInvolution.WeakCT.torusHom K₀ g)) = 2 ^ f - 1 := by
      rw [orderOf_injective ψ hψinj, orderOf_injective
        (CFSG.ClassicalInvolution.WeakCT.torusHom K₀)
        (CFSG.ClassicalInvolution.WeakCT.torusHom_injective (K := K₀)) g,
        orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK₀]
    obtain ⟨μ, hμ, hτμ⟩ := sigma_fixes_generator τ hτodd
      (ψ (CFSG.ClassicalInvolution.WeakCT.torusHom K₀ g)) (ψ (weyl2 K₀))
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) (A : GL (Fin 3) K).isUnit (2 ^ f - 1)
      (by omega) hord (exists_primitiveRoot_q_sub_one h.card_eq_sq (by omega))
      (by rw [← map_mul, ← map_inv, ← map_mul, weyl2_torus, map_inv, map_inv])
      (by
        have e := congrArg (fun u : GL (Fin 3) K => (u : Matrix (Fin 3) (Fin 3) K))
          (hmat' (CFSG.ClassicalInvolution.WeakCT.torusHom K₀ g))
        simp only [Units.val_mul, coe_glAut] at e
        exact e)
    exact ringEquiv_eq_one_of_fix_unitary h.card_eq_sq (by omega) hτodd hμ hτμ
  subst hτ1
  rw [map_one, mul_one] at hx
  refine ⟨A, hx.symm, fun a => ?_⟩
  have e := hmat' a
  rw [map_one, MulAut.one_apply] at e
  have e' := congrArg (fun u : GL (Fin 3) K => (u : Matrix (Fin 3) (Fin 3) K)) e
  simpa using e'

theorem unitary_conjTr_mul
    (A : primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
    conjTr (unitaryInvolution K 2 f) ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
  have hσ : (⇑(unitaryInvolution K 2 f) : K → K) = ⇑h.bar :=
    funext fun c => by rw [unitaryInvolution_apply, h.bar_apply]
  have e : (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * 1 *
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := mem_primeFormUnitary.mp A.2
  rw [Matrix.mul_one] at e
  have e2 : conjTr (unitaryInvolution K 2 f) ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ := by
    simp only [conjTr, hσ]
  rw [e2]
  exact e

include h in
theorem card_suid_two_eq {K₀ : Type} [Field K₀] [Finite K₀] (hK₀ : Nat.card K₀ = 2 ^ f) :
    Nat.card (SUid (unitaryInvolution K 2 f) 2) = Nat.card SL(2, K₀) := by
  obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix h.card_eq_sq 2
  rw [← Nat.card_congr (CFSG.LieType.Universal.Unitary.conjEquiv P hP).toEquiv,
    CFSG.LieType.Steinberg.card_SU_two h.card_eq_sq,
    CFSG.LieType.Steinberg.card_specialLinearGroup_fin_two, hK₀]

theorem unitary_node_lemma (hq : 4 ≤ 2 ^ f) {K₀ : Type} [Field K₀] [Finite K₀]
    (hK₀ : Nat.card K₀ = 2 ^ f) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrq : r ∣ 2 ^ f + 1)
    (φ : SL(2, K₀) →* SUid (unitaryInvolution K 2 f) 3) (hφ : Function.Injective φ)
    (α : MulAut (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) (hα : α ^ r = 1)
    (hα1 : α ≠ 1) (hfix : ∀ a, α (suProj h (φ a)) = suProj h (φ a)) :
    ∃ (A : primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
      (W ℓ : Submodule K (Fin 3 → K)) (a b : K),
      α = primeFormConjHom h _ A ∧ IsCompl W ℓ ∧ Module.finrank K W = 2 ∧ a ≠ b ∧
      (∀ w ∈ W, ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w = a • w) ∧
      (∀ u ∈ ℓ, ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ u = b • u) ∧
      (∀ w ∈ W, ∀ u ∈ ℓ, herm (unitaryInvolution K 2 f) w u = 0) ∧
      φ.range = ublkGroup (unitaryInvolution K 2 f) W ℓ := by
  classical
  obtain ⟨A, hαA, hcomm⟩ := unitary_node_commute h hq hK₀ hr hr2 φ hφ α hα hfix
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  set M : Matrix (Fin 3) (Fin 3) K := ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hMdef
  have hσ : (⇑(unitaryInvolution K 2 f) : K → K) = ⇑h.bar :=
    funext fun c => by rw [unitaryInvolution_apply, h.bar_apply]
  have hMu : conjTr (unitaryInvolution K 2 f) M * M = 1 := unitary_conjTr_mul h A
  have hMp : ∃ c : Kˣ, h.norm (c : K) = 1 ∧
      ((A ^ r : primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
        GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) c := by
    have h1 : primeFormPsi h hC ⟨A ^ r, 1⟩ = 1 := by
      rw [primeFormPsi_apply, map_one, mul_one, map_pow, ← hαA, hα]
    exact ((primeFormPsi_eq_one_iff h hC le_rfl ⟨A ^ r, 1⟩).mp h1).2
  obtain ⟨c, hcN, hc⟩ := hMp
  have hMpm : M ^ r = (c : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    have e := congrArg (fun u : GL (Fin 3) K => (u : Matrix (Fin 3) (Fin 3) K)) hc
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val,
      Matrix.GeneralLinearGroup.coe_scalar] at e
    rw [hMdef, e]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  have hns : ¬ ∃ s : K, M = s • (1 : Matrix (Fin 3) (Fin 3) K) := by
    rintro ⟨s, hs⟩
    have hs0 : s ≠ 0 := by
      rintro rfl
      have := (A : GL (Fin 3) K).isUnit
      rw [← hMdef, hs, zero_smul] at this
      exact not_isUnit_zero this
    apply hα1
    have hnorm : h.norm s = 1 := by
      have e := congrFun (congrFun hMu 0) 0
      rw [hs] at e
      simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply,
        Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] at e
      rw [hσ] at e
      simp at e
      rw [UnitaryFieldData.norm, mul_comm]
      exact e
    have hA : ((A : GL (Fin 3) K)) = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 s hs0) := by
      refine Units.ext ?_
      rw [← hMdef, hs]
      ext i j
      simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
        Matrix.one_apply]
    have h1 : primeFormPsi h hC ⟨A, 1⟩ = 1 :=
      (primeFormPsi_eq_one_iff h hC le_rfl ⟨A, 1⟩).mpr ⟨rfl, Units.mk0 s hs0, hnorm, hA⟩
    rw [primeFormPsi_apply, map_one, mul_one] at h1
    rw [hαA]
    exact h1
  have hr3 : 3 ≤ r := by
    have := hr.two_le
    omega
  have hpq : r ∣ Nat.card K - 1 := by
    rw [h.card_eq_sq]
    have e : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      zify [show 1 ≤ 2 ^ f by omega, show 1 ≤ (2 ^ f) ^ 2 by nlinarith]
      ring
    rw [e]
    exact Dvd.dvd.mul_right hrq _
  have hdiag : ∃ (b : Module.Basis (Fin 3) K (Fin 3 → K)) (d : Fin 3 → K),
      ∀ i, M.mulVec (b i) = d i • b i := by
    rcases eigenbasis_or_commutative hr hr3 hpq M (c : K) c.ne_zero hMpm with hd | hcm
    · exact hd
    · exfalso
      obtain ⟨a, b, hab⟩ := exists_noncomm_sl2 K₀
      apply hab
      apply hφ
      rw [map_mul, map_mul]
      refine Subtype.ext (Units.ext ?_)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
      exact hcm _ _ (hcomm a).symm (hcomm b).symm
  let ψ : SL(2, K₀) →* SL(3, K) := (suToSL (unitaryInvolution K 2 f)).comp φ
  have hψinj : Function.Injective ψ := (suToSL_injective _).comp hφ
  have hperfK0 : Group.IsPerfect SL(2, K₀) := isPerfect_sl2 (by rw [hK₀]; exact hq)
  have hperfR : Group.IsPerfect ψ.range :=
    Group.IsPerfect.ofSurjective (f := ψ.rangeRestrict) (MonoidHom.rangeRestrict_surjective ψ)
  have hnb : ψ.range ≠ ⊥ := by
    intro hb
    obtain ⟨a, b, hab⟩ := exists_noncomm_sl2 K₀
    apply hab
    apply hψinj
    have h1 : ψ a ∈ ψ.range := ⟨a, rfl⟩
    have h2 : ψ b ∈ ψ.range := ⟨b, rfl⟩
    rw [hb, Subgroup.mem_bot] at h1 h2
    rw [map_mul, map_mul, h1, h2]
  obtain ⟨W, ℓ, a₀, b₀, hWℓ, hrk, hab, hW, hℓ, hHle⟩ :=
    exists_le_blkGroup ψ.range hnb M hdiag hns (by
      rintro _ ⟨x, rfl⟩
      exact (hcomm x).symm)
  have hσU : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution (unitaryInvolution K 2 f) :=
    isUnitaryInvolution_unitaryInvolution h.card_eq_sq
  have horth := orth_of_eigen_unitary hσU hMu hWℓ hrk hab hW hℓ
  have hle : φ.range ≤ ublkGroup (unitaryInvolution K 2 f) W ℓ := by
    rintro _ ⟨x, rfl⟩
    rw [mem_ublkGroup_iff]
    exact hHle ⟨x, rfl⟩
  have hcard : Nat.card (ublkGroup (unitaryInvolution K 2 f) W ℓ) = Nat.card φ.range := by
    rw [card_ublkGroup hσU hWℓ hrk horth, card_suid_two_eq h hK₀,
      ← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]
  exact ⟨A, W, ℓ, a₀, b₀, hαA, hWℓ, hrk, hab, hW, hℓ, horth,
    Subgroup.eq_of_le_of_card_ge hle hcard.le⟩

end Node

end CFSG.RankThree.PartOne.CTP
