module

public import CFSG.LocalAnalysis.StandardType.GGQTwoChartDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerCenter
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivKindDiag
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosBlockAux3
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerTypeADvdModel
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteFSEnds
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer
public import CFSG.LocalAnalysis.StandardType.GGQTwoSU34Aux7
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.IsComponentOfMap
public import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
public import Mathlib.LinearAlgebra.Matrix.Trace

public noncomputable section

namespace CFSG.StandardType.QTwo

section Trace

open CFSG.ClassicalInvolution.Phan Matrix
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.ClassicalInvolution.Balance.StrongBalance.Linear

variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {m : ℕ}

theorem qTwoFour_natCast_sq (k : ℕ) : (k : F0) ^ 2 = (k : F0) := by
  induction k with
  | zero => simp
  | succ k hk =>
    rw [Nat.cast_succ, add_sq, hk]
    simp [show (2 : F0) = 0 from CharP.cast_eq_zero F0 2]

theorem qTwoFour_cube_sq_add_nat_ne_zero {ω : F0} (hω : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) (k : ℕ) : ω ^ 2 + (k : F0) ≠ 0 := by
  intro h
  have hω0 : ω ≠ 0 := by intro h0; simp [h0] at hω
  have heq : ω ^ 2 = (k : F0) := by
    have h' := eq_neg_of_add_eq_zero_left h
    simpa [CharTwo.neg_eq] using h'
  have h4 : ω ^ 4 = ω := by
    calc ω ^ 4 = ω ^ 3 * ω := by ring
         _ = ω := by rw [hω, one_mul]
  have h2 : ω ^ 2 = ω := by
    calc ω ^ 2 = (k : F0) := heq
         _ = (k : F0) ^ 2 := (qTwoFour_natCast_sq k).symm
         _ = (ω ^ 2) ^ 2 := by rw [heq]
         _ = ω := by rw [← pow_mul]; exact h4
  have hω1' : ω = 1 := by
    apply mul_left_cancel₀ hω0
    simpa [pow_two] using h2
  exact hω1 hω1'

theorem qTwoFour_separating_trace_ne_zero {I : Finset (Fin m)} (hI : I.card = 4)
    {j : Fin m} (hj : j ∉ I) {ω : F0} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    {t : Su F0 2 1 m}
    (ht : ((t : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      Matrix.diagonal (fun i => if i ∈ I then ω else if i = j then ω ^ 2 else 1)) :
    (((t : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)).trace ≠ 0 := by
  classical
  rw [ht, Matrix.trace_diagonal]
  let d : Fin m → F0 := fun i => if i ∈ I then ω else if i = j then ω ^ 2 else 1
  change (∑ i : Fin m, d i) ≠ 0
  have hsplit : (∑ i : Fin m, d i) =
      (∑ i ∈ I, d i) + (∑ i ∈ Finset.univ \ I, d i) :=
    (Finset.sum_add_sum_compl I d).symm
  have hsumI : (∑ i ∈ I, d i) = 0 := by
    have he : (∑ i ∈ I, d i) = (I.card : F0) * ω := by
      rw [Finset.sum_congr rfl (fun i hi => (show d i = ω by simp [d, hi]))]
      simp [nsmul_eq_mul]
    rw [he, hI]
    have h2 : (2 : F0) = 0 := CharP.cast_eq_zero F0 2
    have h4 : ((4 : ℕ) : F0) = 0 := by
      calc ((4 : ℕ) : F0) = (2 : F0) + (2 : F0) := by norm_num
           _ = 0 := by rw [h2, add_zero]
    rw [h4, zero_mul]
  have hjU : j ∈ Finset.univ \ I := by simp [hj]
  have hsumRest : (∑ i ∈ (Finset.univ \ I) \ {j}, d i) =
      (((Finset.univ \ I) \ {j}).card : F0) := by
    have he : ∀ i ∈ (Finset.univ \ I) \ {j}, d i = 1 := by
      intro i hi
      obtain ⟨hi, hij⟩ := Finset.mem_sdiff.mp hi
      obtain ⟨_, hiI⟩ := Finset.mem_sdiff.mp hi
      have hij' : i ≠ j := by simpa using hij
      simp [d, hiI, hij']
    simp_rw [Finset.sum_congr rfl he]
    simp
  rw [hsplit, hsumI, zero_add,
    Finset.sum_eq_add_sum_sdiff_singleton_of_mem hjU, hsumRest]
  simp only [d, if_neg hj, if_pos rfl]
  exact qTwoFour_cube_sq_add_nat_ne_zero hω hω1 _

theorem qTwoFour_comm_of_map_comm_of_trace_ne_zero (hF0 : Nat.card F0 = 4)
    (hm : 4 ≤ m) {G : Type} [Group G] (ψ : Su F0 2 1 m →* G)
    (hker : ψ.ker ≤ Subgroup.center (Su F0 2 1 m)) {v t : Su F0 2 1 m}
    (ht : (((t : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)).trace ≠ 0)
    (hcomm : ψ v * ψ t = ψ t * ψ v) : v * t = t * v := by
  let z : Su F0 2 1 m := v * t * v⁻¹ * t⁻¹
  have hzker : z ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    simp only [z, map_mul, map_inv]
    rw [hcomm]
    group
  obtain ⟨c, hc⟩ := qTwoLMDivCoordInner_center_scalar hF0 hm (hker hzker)
  have hvt : v * t * v⁻¹ = z * t := by dsimp [z]; group
  have hmat : (v : GL (Fin m) F0) * (t : GL (Fin m) F0) * (v : GL (Fin m) F0)⁻¹ =
      (z : GL (Fin m) F0) * (t : GL (Fin m) F0) := congrArg Subtype.val hvt
  have htrace : (((t : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)).trace =
      c * (((t : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)).trace := by
    have hmat' := congrArg (fun w : GL (Fin m) F0 =>
      (w : Matrix (Fin m) (Fin m) F0)) hmat
    simp only [Units.val_mul] at hmat'
    have htr := congrArg Matrix.trace hmat'
    rw [Matrix.trace_units_conj, hc] at htr
    simpa only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul, Finset.mul_sum] using htr
  have hc1 : c = 1 := by
    apply mul_right_cancel₀ ht
    simpa using htrace.symm
  have hz1 : z = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [hc, hc1]
    simp
  rw [hz1, one_mul] at hvt
  exact mul_inv_eq_iff_eq_mul.mp hvt

theorem qTwoFour_eq_of_square_one_of_map_eq (hF0 : Nat.card F0 = 4) (hm : 4 ≤ m)
    {G : Type} [Group G] (ψ : Su F0 2 1 m →* G)
    (hker : ψ.ker ≤ Subgroup.center (Su F0 2 1 m))
    {u v : Su F0 2 1 m} (hu : u * u = 1) (hv : v * v = 1) (hψ : ψ u = ψ v) : u = v := by
  let z : Su F0 2 1 m := u⁻¹ * v
  have hzker : z ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    simp only [z, map_mul, map_inv, hψ, inv_mul_cancel]
  have hzcent := hker hzker
  have huv : v = u * z := by dsimp [z]; group
  have heq : v * v = (u * u) * (z * z) := by
    rw [huv]
    calc (u * z) * (u * z) = u * (z * u) * z := by group
         _ = u * (u * z) * z := by rw [← Subgroup.mem_center_iff.mp hzcent u]
         _ = (u * u) * (z * z) := by group
  have hz2 : z * z = 1 := by simpa [hu, hv] using heq.symm
  obtain ⟨c, hc⟩ := qTwoLMDivCoordInner_center_scalar hF0 hm hzcent
  have hmpos : 0 < m := by omega
  have hc2 : c ^ 2 = 1 := by
    have he := congrArg (fun w : Su F0 2 1 m =>
      ((w : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) ⟨0, hmpos⟩ ⟨0, hmpos⟩) hz2
    simpa [Subgroup.coe_mul, Units.val_mul, hc, Matrix.diagonal_mul_diagonal, pow_two] using he
  have hc1 : c = 1 := CharTwo.sq_inj.mp (by simpa using hc2)
  have hz1 : z = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [hc, hc1]
    simp
  simpa [hz1] using huv.symm

theorem qTwoFour_compIndicator_comm_of_comm_diagonal {I : Finset (Fin m)}
    {t v : Su F0 2 1 m} {d : Fin m → F0}
    (ht : ((t : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = Matrix.diagonal d)
    (hv : v * t = t * v)
    (hd : ∀ i ∈ I, ∀ j ∉ I, d i ≠ d j) :
    compIndicator F0 I * ((v : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      ((v : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) * compIndicator F0 I := by
  classical
  have hzero (i j : Fin m) (hij : d i ≠ d j) :
      ((v : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) i j = 0 := by
    have he := congrArg (fun w : Su F0 2 1 m =>
      ((w : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) i j) hv
    simp only [Subgroup.coe_mul, Units.val_mul, ht, Matrix.diagonal_mul, Matrix.mul_diagonal] at he
    have hz : (d i - d j) *
        ((v : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) i j = 0 := by
      linear_combination -he
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hij)
  ext i j
  rw [compIndicator_mul_apply, mul_compIndicator_apply]
  by_cases hi : i ∈ I <;> by_cases hj : j ∈ I
  · simp [hi, hj]
  · simp [hi, hj, hzero i j (hd i hi j hj)]
  · simp [hi, hj, hzero i j (Ne.symm (hd j hj i hi))]
  · simp [hi, hj]

end Trace

section Torus

open CFSG.StandardType CFSG.StandardType.TableB CFSG.ClassicalInvolution.Phan

variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
variable {G : Type} [Group G] [Finite G] {m : ℕ} {L : Subgroup G}

theorem qTwoFour_exists_noncyclic_three (hF0 : Nat.card F0 = 4) (hm : 5 ≤ m)
    (ψ : Su F0 2 1 m →* G) (hrange : ψ.range = L)
    (hker : ψ.ker ≤ Subgroup.center (Su F0 2 1 m)) :
    ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S := by
  let T := qTwoLMDivKind_diag F0 m
  have hp : IsPGroup 3 T := by
    intro u
    refine ⟨1, Subtype.ext ?_⟩
    simpa using qTwoLMDivKind_pow_three_of_mem_diag hF0 u.2
  refine ⟨T.map ψ, ?_, hp.map ψ, ?_⟩
  · rw [← hrange]
    rintro u ⟨v, _, rfl⟩
    exact ⟨v, rfl⟩
  · intro hcyc
    have hpow : ∀ u ∈ T.map ψ, u ^ 3 = 1 := by
      rintro u ⟨v, hv, rfl⟩
      rw [← map_pow, qTwoLMDivKind_pow_three_of_mem_diag hF0 hv, map_one]
    have hcard : Nat.card (T.map ψ) ≤ 3 := card_le_of_isCyclic (by norm_num) hcyc hpow
    have hkT : ψ.ker ≤ T := hker.trans (qTwoLMDivKind_center_le_diag hF0 (by omega))
    have hkerCard : Nat.card (ψ.domRestrict T).ker ≤ 3 := by
      rw [MonoidHom.ker_domRestrict,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkT).toEquiv]
      exact (Subgroup.card_le_of_le hker).trans (qTwoLMDivKind_card_center_le hF0 (by omega))
    have hmul : Nat.card (ψ.domRestrict T).ker * Nat.card (T.map ψ) = 3 ^ (m - 1) := by
      have hTcard : Nat.card T = 3 ^ (m - 1) :=
        qTwoLMDivKind_card_diag (m := m) hF0 (by omega)
      simpa only [MonoidHom.domRestrict_range, hTcard] using
        Subgroup.card_ker_mul_card_range (ψ.domRestrict T)
    have hbound : 3 ^ (m - 1) ≤ 9 := by
      rw [← hmul]
      exact Nat.mul_le_mul hkerCard hcard
    have h81 : 81 ≤ 3 ^ (m - 1) := by
      calc 81 = (3 : ℕ) ^ 4 := by norm_num
           _ ≤ 3 ^ (m - 1) :=
             (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).2 (by omega)
    omega

end Torus

section Diagonal

open CFSG.StandardType
open CFSG.StandardType.QTwo
open CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
open scoped MatrixGroups

variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]

theorem qTwoFour_exists_cube_root (hF0 : Nat.card F0 = 4) :
    ∃ ω : F0, ω ^ 3 = 1 ∧ ω ≠ 1 ∧ ω ≠ 0 := by
  have hcard : Nat.card F0ˣ = 3 := by
    have h := Nat.card_units F0
    omega
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := F0ˣ)
  rw [hcard] at hζ
  refine ⟨(ζ : F0), ?_, ?_, ?_⟩
  · have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
    rw [← Units.val_pow_eq_pow_val, hζ3, Units.val_one]
  · intro h
    have hζ1 : ζ = 1 := Units.ext h
    rw [hζ1] at hζ
    have : (1 : ℕ) = 3 := by simpa using hζ
    omega
  · exact ζ.ne_zero

theorem qTwoFour_exists_separating_diagonal (hF0 : Nat.card F0 = 4) {m : ℕ} (hm : 5 ≤ m) {I : Finset (Fin m)} (hI : I.card = 4)
    {j : Fin m} (hj : j ∉ I) {ω : F0} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hω0 : ω ≠ 0) :
    ∃ t : Su F0 2 1 m,
      t ^ 3 = 1 ∧
      t ∈ qTwoLMDivKind_diag F0 m ∧
      ((t : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
        Matrix.diagonal (fun i => if i ∈ I then ω else if i = j then ω ^ 2 else 1) ∧
      Matrix.trace (((t : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) ≠ 0 := by
  classical
  let d : Fin m → F0 := fun i => if i ∈ I then ω else if i = j then ω ^ 2 else 1
  have hprodI : ∏ i ∈ I, d i = ω ^ I.card := by
    rw [Finset.prod_congr rfl (fun i hi => (show d i = ω by simp [d, hi]))]
    rw [Finset.prod_const]
  have hprodC : ∏ i ∈ Iᶜ, d i = ω ^ 2 := by
    have hjC : j ∈ Iᶜ := by simp [hj]
    rw [← Finset.insert_erase hjC]
    rw [Finset.prod_insert (Finset.notMem_erase j Iᶜ)]
    have hdj : d j = ω ^ 2 := by simp [d, hj]
    rw [hdj]
    have hrest : ∏ i ∈ Iᶜ.erase j, d i = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      have hiI : i ∉ I := Finset.mem_compl.mp (Finset.mem_erase.mp hi).2
      have hij : i ≠ j := (Finset.mem_erase.mp hi).1
      simp [d, hiI, hij]
    rw [hrest, mul_one]
  have hprod : ∏ i, d i = 1 := by
    rw [← Finset.prod_mul_prod_compl I d, hprodI, hprodC, hI]
    rw [show ω ^ 4 * ω ^ 2 = (ω ^ 3) ^ 2 by ring, hω3, one_pow]
  have hunit : ∀ i, unitaryInvolution F0 2 1 (d i) * d i = 1 := by
    intro i
    by_cases hi : i ∈ I
    · have hdi : d i = ω := by simp [d, hi]
      rw [hdi]
      exact qTwoLMDivKind_norm_eq_one hF0 hω0
    · by_cases hij : i = j
      · have hdi : d i = ω ^ 2 := by simp [d, hi, hij, hj]
        rw [hdi]
        exact qTwoLMDivKind_norm_eq_one hF0 (pow_ne_zero 2 hω0)
      · have hdi : d i = 1 := by simp [d, hi, hij]
        rw [hdi]
        simp
  let t : Su F0 2 1 m := ggNSPosPB2_diagSU d hprod hunit
  have htmat : ((t : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = Matrix.diagonal d := by
    simp [t]
  have htdiag : t ∈ qTwoLMDivKind_diag F0 m := ⟨d, htmat⟩
  have ht3 : t ^ 3 = 1 := qTwoLMDivKind_pow_three_of_mem_diag hF0 htdiag
  refine ⟨t, ht3, htdiag, htmat, ?_⟩
  exact qTwoFour_separating_trace_ne_zero hI hj hω3 hω1 htmat

theorem qTwoFour_perm_comm_separator {m : ℕ} {I : Finset (Fin m)} {j : Fin m}
    (hj : j ∉ I) {ω : F0}
    {σ : Equiv.Perm (Fin m)} (hσ : ∀ y, y ∉ I → σ y = y)
    {t : Su F0 2 1 m}
    (htmat : ((t : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      Matrix.diagonal (fun i => if i ∈ I then ω else if i = j then ω ^ 2 else 1)) :
    ggPermSU σ * t = t * ggPermSU σ := by
  classical
  let d : Fin m → F0 := fun i => if i ∈ I then ω else if i = j then ω ^ 2 else 1
  have hdmat : ((t : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = Matrix.diagonal d := by
    simpa [d] using htmat
  have hσI : ∀ i : Fin m, i ∈ I ↔ σ i ∈ I := by
    intro i
    constructor
    · intro hi
      by_contra h
      have hfix : σ (σ i) = σ i := hσ (σ i) h
      have hsi : σ i = i := by
        have := congrArg (fun e => σ.symm e) hfix
        simpa using this
      exact h (by simpa [hsi] using hi)
    · intro hi
      by_contra h
      have hfix : σ i = i := hσ i h
      exact h (by simpa [hfix] using hi)
  have hd_inv : ∀ i : Fin m, d (σ i) = d i := by
    intro i
    by_cases hi : i ∈ I
    · have hi' : σ i ∈ I := (hσI i).mp hi
      simp [d, hi, hi']
    · have hfix : σ i = i := hσ i hi
      simp [d, hi, hfix]
  have hprod : σ⁻¹.permMatrix F0 * σ.permMatrix F0 = 1 := by
    have h := Matrix.permMatrix_mul (σ := σ) (τ := σ⁻¹) (R := F0)
    simpa using h.symm
  have hPinv : (σ.permMatrix F0)⁻¹ = σ⁻¹.permMatrix F0 :=
    Matrix.inv_eq_left_inv hprod
  have hu_coe : (((ggPermSU (K := F0) (f := 1) σ : Su F0 2 1 m) : GL (Fin m) F0) :
      Matrix (Fin m) (Fin m) F0) = σ.permMatrix F0 := rfl
  have hu_inv_coe : ((((ggPermSU (K := F0) (f := 1) σ : Su F0 2 1 m)⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) :
      Matrix (Fin m) (Fin m) F0) = σ⁻¹.permMatrix F0 := by
    rw [Subgroup.coe_inv]
    change (((((ggPermSU (K := F0) (f := 1) σ : Su F0 2 1 m) : GL (Fin m) F0)⁻¹ : GL (Fin m) F0) :
      Matrix (Fin m) (Fin m) F0)) = σ⁻¹.permMatrix F0
    rw [Matrix.GeneralLinearGroup.coe_inv, hu_coe, hPinv]
  have hconj_gl : ((ggPermSU (K := F0) (f := 1) σ : Su F0 2 1 m) : GL (Fin m) F0) *
      (t : GL (Fin m) F0) *
      (((ggPermSU (K := F0) (f := 1) σ : Su F0 2 1 m) : GL (Fin m) F0))⁻¹ =
      (t : GL (Fin m) F0) := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.GeneralLinearGroup.coe_inv, hu_coe, hPinv, hdmat,
      CFSG.StandardType.TypeANbrDvd.permMatrix_mul_diagonal_mul_inv]
    congr 1
    funext i
    exact hd_inv i
  have hconj : ggPermSU σ * t * (ggPermSU σ)⁻¹ = t := Subtype.ext hconj_gl
  calc ggPermSU σ * t = (ggPermSU σ * t * (ggPermSU σ)⁻¹) * ggPermSU σ := by group
    _ = t * ggPermSU σ := by rw [hconj]

theorem qTwoFour_supported_native {m n : ℕ} {ε : Fin m ↪ Fin (n + 1)}
    {I : Finset (Fin m)} {τ : Equiv.Perm (Fin (n + 1))}
    (hτ : ∀ y, y ∉ I.map ε → τ y = y) :
    ∃ σ : Equiv.Perm (Fin m),
      (∀ i, i ∉ I → σ i = i) ∧
      σ.extendDomain (Equiv.ofInjective ε ε.injective) = τ := by
  classical
  let e : Fin m ≃ Set.range ε := Equiv.ofInjective ε ε.injective
  have hsub : ∀ x : Fin (n + 1), x ∈ I.map ε → x ∈ Set.range ε := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
    exact ⟨i, rfl⟩
  have hτI : ∀ y : Fin (n + 1), y ∈ I.map ε → τ y ∈ I.map ε := by
    intro y hy
    by_contra h
    have hfix := hτ (τ y) h
    have hyfix : τ y = y := by
      have := congrArg (fun z => τ.symm z) hfix
      simpa using this
    exact h (by simpa [hyfix] using hy)
  have hiff : ∀ x : Fin (n + 1),
      τ x ∈ Set.range ε ↔ x ∈ Set.range ε := by
    intro x
    constructor
    · intro hx
      by_cases hxI : x ∈ I.map ε
      · exact hsub x hxI
      · have hfix := hτ x hxI
        simpa [hfix] using hx
    · intro hx
      by_cases hxI : x ∈ I.map ε
      · exact hsub (τ x) (hτI x hxI)
      · have hfix := hτ x hxI
        simpa [hfix] using hx
  let τ' : Equiv.Perm (Set.range ε) := τ.subtypePerm hiff
  let σ : Equiv.Perm (Fin m) := e.trans (τ'.trans e.symm)
  have hσ : ∀ i, i ∉ I → σ i = i := by
    intro i hi
    have hεi : ε i ∉ I.map ε := by
      intro h
      obtain ⟨k, hk, hki⟩ := Finset.mem_map.mp h
      exact hi (by simpa [ε.injective hki] using hk)
    have hfix := hτ (ε i) hεi
    have hτ'e : τ' (e i) = e i := by
      apply Subtype.ext
      simpa [τ', e] using hfix
    have he : e (σ i) = e i := by
      simp [σ, hτ'e]
    exact e.injective he
  refine ⟨σ, hσ, ?_⟩
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ Set.range ε
  · obtain ⟨i, rfl⟩ := hx
    change (σ.extendDomain (Equiv.ofInjective ε ε.injective))
      (Equiv.ofInjective ε ε.injective i) = τ (ε i)
    rw [Equiv.Perm.extendDomain_apply_image]
    have hτ'e : τ' (e i) = e (σ i) := by simp [σ]
    have hval : (e (σ i) : Fin (n + 1)) = τ (ε i) := by
      have := congrArg Subtype.val hτ'e
      simpa [e, τ'] using this.symm
    simpa [e] using hval
  · rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ hx]
    have hxI : x ∉ I.map ε := fun h => hx (hsub x h)
    exact (hτ x hxI).symm

theorem qTwoFour_eq_native_perm_of_basis_action {m : ℕ} {σ : Equiv.Perm (Fin m)}
    {u : Su F0 2 1 m}
    (hu : ∀ i : Fin m, Matrix.mulVec (((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0))
      (Pi.single i 1) = Pi.single (σ i) 1) :
    u = ggPermSU σ⁻¹ := by
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [hu i]
  rw [show ((((ggPermSU (K := F0) (f := 1) σ⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) :
      Matrix (Fin m) (Fin m) F0)) = (σ⁻¹).permMatrix F0 by rfl]
  rw [Matrix.permMatrix_mulVec]
  ext j
  simp [Pi.single_apply, Equiv.symm_apply_eq]

section NativeNormalization

variable {G : Type} [Group G] [Finite G]
variable {m : ℕ} {ψ : Su F0 2 1 m →* G}

theorem qTwoFour_indicator_comm_of_map_comm (hF0 : Nat.card F0 = 4) (hm : 5 ≤ m)
    {I : Finset (Fin m)} (hI : I.card = 4) {j : Fin m} (hj : j ∉ I)
    {ω : F0} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hω0 : ω ≠ 0)
    (hker : ψ.ker ≤ Subgroup.center (Su F0 2 1 m))
    {t v : Su F0 2 1 m}
    (htmat : ((t : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      Matrix.diagonal (fun i => if i ∈ I then ω else if i = j then ω ^ 2 else 1))
    (hcomm : ψ v * ψ t = ψ t * ψ v) :
    compIndicator F0 I * ((v : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      ((v : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) * compIndicator F0 I := by
  classical
  have htrace : (((t : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)).trace ≠ 0 :=
    qTwoFour_separating_trace_ne_zero hI hj hω3 hω1 htmat
  have hvt : v * t = t * v :=
    qTwoFour_comm_of_map_comm_of_trace_ne_zero hF0 (by omega : 4 ≤ m) ψ hker htrace hcomm
  have hsep : ∀ i ∈ I, ∀ j' ∉ I,
      (fun i => if i ∈ I then ω else if i = j then ω ^ 2 else 1) i ≠
        (fun i => if i ∈ I then ω else if i = j then ω ^ 2 else 1) j' := by
    intro i hi j' hj'
    have hdi : (fun i => if i ∈ I then ω else if i = j then ω ^ 2 else 1) i = ω := by
      simp [hi]
    have hω2ne : ω ≠ ω ^ 2 := by
      intro h
      have h1 : ω * 1 = ω * ω := by
        rw [mul_one]
        simpa [pow_two] using h
      exact hω1 (mul_left_cancel₀ hω0 h1).symm
    by_cases hjj : j' = j
    · have hdj : (fun i => if i ∈ I then ω else if i = j then ω ^ 2 else 1) j' = ω ^ 2 := by
        simp [hj', hjj, hj]
      rw [hdi, hdj]
      exact hω2ne
    · have hdj : (fun i => if i ∈ I then ω else if i = j then ω ^ 2 else 1) j' = 1 := by
        simp [hj', hjj]
      rw [hdi, hdj]
      exact hω1
  exact qTwoFour_compIndicator_comm_of_comm_diagonal (d := fun i =>
    if i ∈ I then ω else if i = j then ω ^ 2 else 1) htmat hvt hsep

theorem qTwoFour_conj_mem_block_of_map_comm (hF0 : Nat.card F0 = 4) (hm : 5 ≤ m)
    {I : Finset (Fin m)} (hI : I.card = 4) {j : Fin m} (hj : j ∉ I)
    {ω : F0} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hω0 : ω ≠ 0)
    (hker : ψ.ker ≤ Subgroup.center (Su F0 2 1 m))
    {t v g : Su F0 2 1 m}
    (htmat : ((t : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      Matrix.diagonal (fun i => if i ∈ I then ω else if i = j then ω ^ 2 else 1))
    (hcomm : ψ v * ψ t = ψ t * ψ v) (hg : g ∈ coordBlockSU F0 2 1 I) :
    v * g * v⁻¹ ∈ coordBlockSU F0 2 1 I :=
  conj_mem_coordBlockSU (qTwoFour_indicator_comm_of_map_comm hF0 hm hI hj hω3 hω1 hω0
    hker htmat hcomm) hg

end NativeNormalization

section FixI

variable {G : Type} [Group G] [Finite G]
variable {B Bs L D J : Subgroup G} {x : G} {𝒦 : Finset (Subgroup G)}
variable {m n : ℕ} {S : QTwoChartSetting B Bs x L D J 𝒦 m n}
variable {ψ : Su F0 2 1 m →* G} {ε : Fin m ↪ Fin (n + 1)}

theorem qTwoFour_separator_mem_fixI (hF0 : Nat.card F0 = 4) (hm : 5 ≤ m)
    {I : Finset (Fin m)} (hI : I.card = 4) {j : Fin m} (hj : j ∉ I)
    {ω : F0} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hω0 : ω ≠ 0)
    (hε : QTwoFrameMatch S ψ ε) {t : Su F0 2 1 m}
    (htmat : ((t : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      Matrix.diagonal (fun i => if i ∈ I then ω else if i = j then ω ^ 2 else 1))
    (hψt : ψ t ∈ Bs) :
    ψ t ∈ qTwoFixI S.ρA (qTwoFrameSet ε (1 : Equiv.Perm (Fin (n + 1))) I) := by
  classical
  let I' : Finset (Fin (n + 1)) := qTwoFrameSet ε (1 : Equiv.Perm (Fin (n + 1))) I
  have hI' : I' = I.map ε := by
    simp [I', qTwoFrameSet, Equiv.toEmbedding]
  have hfix_gen : ∀ τ : Equiv.Perm (Fin (n + 1)),
      (∀ y, y ∉ I' → τ y = y) →
      ((((S.ρA τ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) ⟨ψ t, hψt⟩) =
        ⟨ψ t, hψt⟩ := by
    intro τ hτ
    have hτ' : ∀ y, y ∉ I.map ε → τ y = y := by simpa [hI'] using hτ
    obtain ⟨σ, hσ, hτeq⟩ := qTwoFour_supported_native (m := m) hτ'
    obtain ⟨u, hu_smul, hLift⟩ := hε σ
    have hu_eq : u = ggPermSU σ⁻¹ := qTwoFour_eq_native_perm_of_basis_action hu_smul
    have hσinv : ∀ y, y ∉ I → σ⁻¹ y = y := by
      intro y hy
      apply σ.injective
      simpa [hσ y hy]
    have hcomm_t : ggPermSU σ⁻¹ * t = t * ggPermSU σ⁻¹ :=
      qTwoFour_perm_comm_separator hj hσinv htmat
    have hcomm_u_t : u * t = t * u := by simpa [hu_eq] using hcomm_t
    have hψu_comm : ψ u * ψ t = ψ t * ψ u := by
      simpa [map_mul] using congrArg ψ hcomm_u_t
    have hLiftτ : QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA (ψ u) τ := by
      simpa [hτeq] using hLift
    apply Subtype.ext
    rw [hLiftτ.2.2 ⟨ψ t, hψt⟩]
    rw [hψu_comm]
    group
  have hfix_closure : ∀ τ ∈ Subgroup.closure
      {σ : Equiv.Perm (Fin (n + 1)) | ∀ y, y ∉ I' → σ y = y},
      ((((S.ρA τ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) ⟨ψ t, hψt⟩) =
        ⟨ψ t, hψt⟩ := by
    intro τ hτ
    let act : Equiv.Perm (Fin (n + 1)) →* MulAut ↥Bs :=
      (Subgroup.subtype (ggAutomizerJoin L Bs 𝒦)).comp S.ρA.toMonoidHom
    let x : ↥Bs := ⟨ψ t, hψt⟩
    change act τ x = x
    refine Subgroup.closure_induction (p := fun τ _ => act τ x = x) ?_ ?_ ?_ ?_ hτ
    · intro σ hσ
      exact hfix_gen σ hσ
    · simp [act, x]
    · intro a b _ _ ha hb
      rw [map_mul, MulAut.mul_apply, hb, ha]
    · intro a _ ha
      apply (act a).injective
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply, ha]
  rw [qTwoFixI, Subgroup.mem_map]
  refine ⟨⟨ψ t, hψt⟩, ?_, rfl⟩
  rw [Subgroup.mem_iInf]
  intro s
  change ((s : MulAut ↥Bs) ⟨ψ t, hψt⟩) = ⟨ψ t, hψt⟩
  have hs : (s : MulAut ↥Bs) ∈ qTwoSymI S.ρA I' := s.2
  change (s : MulAut ↥Bs) ∈
    (Subgroup.closure {σ : Equiv.Perm (Fin (n + 1)) | ∀ y, y ∉ I' → σ y = y}).map
      ((Subgroup.subtype (ggAutomizerJoin L Bs 𝒦)).comp S.ρA.toMonoidHom) at hs
  obtain ⟨τ, hτ, hτs⟩ := Subgroup.mem_map.mp hs
  rw [← hτs]
  exact hfix_closure τ hτ

end FixI

section Model


variable {G : Type} [Group G] [Finite G]
variable {B Bs L : Subgroup G} {m : ℕ} {ψ : Su F0 2 1 m →* G}

theorem qTwoFour_separator_mem_Bstar (hF0 : Nat.card F0 = 4) (hm : 5 ≤ m)
    {I : Finset (Fin m)} (hI : I.card = 4) {j : Fin m} (hj : j ∉ I)
    {ω : F0} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hω0 : ω ≠ 0)
    (hBs : GGBstar 3 B Bs) (hψ : QTwoOrdModel Bs L ψ)
    {t : Su F0 2 1 m} (ht3 : t ^ 3 = 1)
    (htmat : ((t : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      Matrix.diagonal (fun i => if i ∈ I then ω else if i = j then ω ^ 2 else 1)) :
    ψ t ∈ Bs := by
  classical
  simp only [QTwoOrdModel] at hψ
  obtain ⟨hrange, hker, hdiag⟩ := hψ
  have htdiag : t ∈ qTwoLMDivKind_diag F0 m := ⟨_, htmat⟩
  have hcentral : ψ t ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨g, hgdiag, hgu⟩ := hdiag ⟨b, hb⟩
    obtain ⟨u', hu'eq, hψu'⟩ := hgu t
    obtain ⟨e, he⟩ := hgdiag
    obtain ⟨d, hd⟩ := htdiag
    have hcomm_gl : g * (t : GL (Fin m) F0) = (t : GL (Fin m) F0) * g := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, he, hd]
      exact Matrix.commute_diagonal e d
    have hu't : u' = t := by
      apply Subtype.ext
      apply Units.ext
      rw [hu'eq, hcomm_gl]
      group
    have hψeq : ψ t = (b : G) * ψ t * (b : G)⁻¹ := by
      rw [← hψu', hu't]
    calc b * ψ t = (b * ψ t * b⁻¹) * b := by group
      _ = ψ t * b := by rw [← hψeq]
  have hpow : (ψ t) ^ 3 = 1 := by
    rw [← map_pow, ht3, map_one]
  exact hBs.2.2.2 (ψ t) hcentral hpow

end Model

section ImageNormal

variable {G : Type} [Group G] [Finite G]
variable {B Bs L D J : Subgroup G} {x : G} {𝒦 : Finset (Subgroup G)}
variable {m n : ℕ} {S : QTwoChartSetting B Bs x L D J 𝒦 m n}
variable {ψ : Su F0 2 1 m →* G} {ε : Fin m ↪ Fin (n + 1)}

theorem qTwoFour_block_image_normal (hF0 : Nat.card F0 = 4) (hm : 5 ≤ m)
    {I : Finset (Fin m)} (hI : I.card = 4) {j : Fin m} (hj : j ∉ I)
    {ω : F0} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hω0 : ω ≠ 0)
    (hψ : QTwoOrdModel Bs L ψ) (hε : QTwoFrameMatch S ψ ε)
    {t : Su F0 2 1 m} (ht3 : t ^ 3 = 1)
    (htmat : ((t : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      Matrix.diagonal (fun i => if i ∈ I then ω else if i = j then ω ^ 2 else 1))
    (hblock_le : ((coordBlockSU F0 2 1 I).map ψ) ≤
      L ⊓ Subgroup.centralizer (qTwoFixI S.ρA
        (qTwoFrameSet ε (1 : Equiv.Perm (Fin (n + 1))) I) : Set G)) :
    (((coordBlockSU F0 2 1 I).map ψ).subgroupOf
      (L ⊓ Subgroup.centralizer (qTwoFixI S.ρA
        (qTwoFrameSet ε (1 : Equiv.Perm (Fin (n + 1))) I) : Set G))).Normal := by
  classical
  have hBs : GGBstar 3 B Bs := S.hcfg.1.1.2.1
  obtain ⟨hrange, hker, hdiag⟩ := hψ
  have hψt : ψ t ∈ Bs :=
    qTwoFour_separator_mem_Bstar hF0 hm hI hj hω3 hω1 hω0 hBs ⟨hrange, hker, hdiag⟩ ht3 htmat
  have hfix : ψ t ∈ qTwoFixI S.ρA
      (qTwoFrameSet ε (1 : Equiv.Perm (Fin (n + 1))) I) :=
    qTwoFour_separator_mem_fixI hF0 hm hI hj hω3 hω1 hω0 hε htmat hψt
  rw [Subgroup.normal_subgroupOf_iff hblock_le]
  intro h k hh hk
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hh
  have hkL : k ∈ L := hk.1
  have hkC : k ∈ Subgroup.centralizer (qTwoFixI S.ρA
      (qTwoFrameSet ε (1 : Equiv.Perm (Fin (n + 1))) I) : Set G) := hk.2
  rw [← hrange] at hkL
  obtain ⟨v, hv⟩ := hkL
  have hkcomm : ψ t * k = k * ψ t :=
    Subgroup.mem_centralizer_iff.mp hkC (ψ t) hfix
  have hcomm : ψ v * ψ t = ψ t * ψ v := by
    rw [hv]
    exact hkcomm.symm
  refine Subgroup.mem_map.mpr ⟨v * g * v⁻¹,
    qTwoFour_conj_mem_block_of_map_comm hF0 hm hI hj hω3 hω1 hω0 hker htmat hcomm hg, ?_⟩
  rw [map_mul, map_mul, map_inv, hv]

theorem qTwoFour_block_image_normal_exists (hF0 : Nat.card F0 = 4) (hm : 5 ≤ m)
    {I : Finset (Fin m)} (hI : I.card = 4) {j : Fin m} (hj : j ∉ I)
    {S : QTwoChartSetting B Bs x L D J 𝒦 m n}
    (hψ : QTwoOrdModel Bs L ψ) (hε : QTwoFrameMatch S ψ ε)
    (hblock_le : ((coordBlockSU F0 2 1 I).map ψ) ≤
      L ⊓ Subgroup.centralizer (qTwoFixI S.ρA
        (qTwoFrameSet ε (1 : Equiv.Perm (Fin (n + 1))) I) : Set G)) :
    (((coordBlockSU F0 2 1 I).map ψ).subgroupOf
      (L ⊓ Subgroup.centralizer (qTwoFixI S.ρA
        (qTwoFrameSet ε (1 : Equiv.Perm (Fin (n + 1))) I) : Set G))).Normal := by
  obtain ⟨ω, hω3, hω1, hω0⟩ := qTwoFour_exists_cube_root hF0
  obtain ⟨t, ht3, -, htmat, -⟩ := qTwoFour_exists_separating_diagonal hF0 hm hI hj hω3 hω1 hω0
  exact qTwoFour_block_image_normal hF0 hm hI hj hω3 hω1 hω0 hψ hε ht3 htmat hblock_le

end ImageNormal

end Diagonal

section Fixed

open CFSG.StandardType
open CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open scoped Pointwise Matrix

variable {G : Type} [Group G] [Finite G]
variable {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {m n : ℕ}
variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]

variable (S : QTwoChartSetting B Bs x L D J 𝒦 m n)

theorem qTwoFour_mem_qTwoFixI_iff {I : Finset (Fin (n + 1))} {y : G} :
    y ∈ qTwoFixI S.ρA I ↔
      ∃ b : ↥Bs, (∀ s : qTwoSymI S.ρA I, (s : MulAut ↥Bs) b = b) ∧ (b : G) = y := by
  classical
  constructor
  · intro hy
    rw [qTwoFixI, Subgroup.mem_map] at hy
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨b, ?_, hby⟩
    intro s
    have h := (Subgroup.mem_iInf.mp hb) s
    simpa using h
  · rintro ⟨b, hb, rfl⟩
    rw [qTwoFixI, Subgroup.mem_map]
    refine ⟨b, ?_, rfl⟩
    rw [Subgroup.mem_iInf]
    intro s
    simpa using hb s

theorem qTwoFour_mem_Bs_of_mem_qTwoFixI {I : Finset (Fin (n + 1))} {y : G}
    (hy : y ∈ qTwoFixI S.ρA I) : y ∈ Bs := by
  rw [qTwoFixI, Subgroup.mem_map] at hy
  obtain ⟨b, _, hb⟩ := hy
  rw [← hb]
  exact b.2

theorem qTwoFour_qTwoFixI_apply_eq_self {I : Finset (Fin (n + 1))} {y : G}
    (hy : y ∈ qTwoFixI S.ρA I) {s : MulAut ↥Bs} (hs : s ∈ qTwoSymI S.ρA I) :
    s ⟨y, qTwoFour_mem_Bs_of_mem_qTwoFixI S hy⟩ =
      ⟨y, qTwoFour_mem_Bs_of_mem_qTwoFixI S hy⟩ := by
  classical
  rw [qTwoFour_mem_qTwoFixI_iff] at hy
  obtain ⟨b, hb, hby⟩ := hy
  have hb_eq : b = ⟨y, qTwoFour_mem_Bs_of_mem_qTwoFixI S hy⟩ := Subtype.ext hby
  have h := hb ⟨s, hs⟩
  simpa [hb_eq] using h

theorem qTwoFour_frameSet_one {ε : Fin m ↪ Fin (n + 1)} (I : Finset (Fin m)) :
    qTwoFrameSet ε 1 I = I.map ε := by
  ext x
  simp only [qTwoFrameSet, Finset.mem_map, Equiv.toEmbedding_apply,
    Equiv.Perm.coe_one, id_eq]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨ε z, ⟨z, hz, rfl⟩, rfl⟩

theorem qTwoFour_square_one_of_mulVec_single {σ : Equiv.Perm (Fin m)} {u : Su F0 2 1 m}
    (hσ : σ * σ = 1)
    (hu : ∀ i : Fin m,
      ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1 =
        Pi.single (σ i) 1) :
    u * u = 1 := by
  classical
  let U : Matrix (Fin m) (Fin m) F0 := ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)
  have hU : U * U = 1 := by
    refine Matrix.ext_of_mulVec_single (M := U * U) (N := 1) ?_
    intro k
    change (U * U) *ᵥ Pi.single k 1 = (1 : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single k 1
    rw [← Matrix.mulVec_mulVec]
    change U *ᵥ (U *ᵥ Pi.single k 1) = (1 : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single k 1
    rw [hu k, hu (σ k)]
    have hσσ : σ (σ k) = k := by
      have h := congrArg (fun e : Equiv.Perm (Fin m) => e k) hσ
      simpa [Equiv.Perm.mul_apply] using h
    rw [hσσ, Matrix.one_mulVec]
  apply Subtype.ext
  apply Units.ext
  simpa [U] using hU

theorem qTwoFour_psi_comm_of_mem_qTwoFixI {ε : Fin m ↪ Fin (n + 1)}
    {ψ : Su F0 2 1 m →* G} {I : Finset (Fin m)} {f : G}
    (hf : f ∈ qTwoFixI S.ρA (qTwoFrameSet ε 1 I))
    {σ : Equiv.Perm (Fin m)} (hσ : ∀ k, k ∉ I → σ k = k) {u : Su F0 2 1 m}
    (hu : QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA (ψ u)
      (σ.extendDomain (Equiv.ofInjective ε ε.injective))) :
    ψ u * f = f * ψ u := by
  classical
  let τ : Equiv.Perm (Fin (n + 1)) := σ.extendDomain (Equiv.ofInjective ε ε.injective)
  have hτfix : ∀ y, y ∉ qTwoFrameSet ε 1 I → τ y = y := by
    intro y hy
    rw [qTwoFour_frameSet_one] at hy
    by_cases hrange : y ∈ Set.range ε
    · obtain ⟨k, rfl⟩ := hrange
      have hk : k ∉ I := by
        intro hk
        exact hy (Finset.mem_map.mpr ⟨k, hk, rfl⟩)
      have himg : τ (ε k) = ε (σ k) := by
        dsimp [τ]
        simpa using Equiv.Perm.extendDomain_apply_image (e := σ)
          (p := fun y : Fin (n + 1) => y ∈ Set.range ε)
          (f := Equiv.ofInjective ε ε.injective) k
      rw [himg, hσ k hk]
    · dsimp [τ]
      exact Equiv.Perm.extendDomain_apply_not_subtype
        (p := fun y : Fin (n + 1) => y ∈ Set.range ε) _ _ hrange
  have hτmem : ((S.ρA τ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈
      qTwoSymI S.ρA (qTwoFrameSet ε 1 I) := by
    refine Subgroup.mem_map.mpr ⟨τ, Subgroup.subset_closure hτfix, rfl⟩
  have hfBs : f ∈ Bs := qTwoFour_mem_Bs_of_mem_qTwoFixI S hf
  have hfix := qTwoFour_qTwoFixI_apply_eq_self S hf hτmem
  have hconj : ψ u * f * (ψ u)⁻¹ = f := by
    have h1 := hu.2.2 ⟨f, hfBs⟩
    have h2 := congrArg (fun b : ↥Bs => (b : G)) hfix
    rw [h2] at h1
    exact h1.symm
  exact mul_inv_eq_iff_eq_mul.mp hconj

theorem qTwoFour_diagonal_eq_of_comm {d : Fin m → F0} {U : Matrix (Fin m) (Fin m) F0}
    {i j : Fin m} (hcomm : Matrix.diagonal d * U = U * Matrix.diagonal d)
    (hUij : U i j = 1) : d i = d j := by
  have h := congrFun (congrFun hcomm i) j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, hUij, mul_one, one_mul] at h
  exact h

theorem qTwoFour_diagonal_eq_on_fourSet (hF0 : Nat.card F0 = 4) (hm : 4 ≤ m)
    {ε : Fin m ↪ Fin (n + 1)} {ψ : Su F0 2 1 m →* G}
    (hε : QTwoFrameMatch S ψ ε)
    (hker : ψ.ker ≤ Subgroup.center (Su F0 2 1 m))
    {I : Finset (Fin m)} {f : G} (hf : f ∈ qTwoFixI S.ρA (qTwoFrameSet ε 1 I))
    {d : GL (Fin m) F0} {dvec : Fin m → F0}
    (hdmat : ((d : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = Matrix.diagonal dvec)
    (hact : ∀ u : Su F0 2 1 m, ∃ u' : Su F0 2 1 m,
      (u' : GL (Fin m) F0) = d * (u : GL (Fin m) F0) * d⁻¹ ∧
        ψ u' = f * ψ u * f⁻¹)
    {i j : Fin m} (hi : i ∈ I) (hj : j ∈ I) : dvec i = dvec j := by
  classical
  by_cases hij : i = j
  · subst j
    rfl
  · let σ : Equiv.Perm (Fin m) := Equiv.swap i j
    obtain ⟨u, huVec, huLift⟩ := hε σ
    have hσ : ∀ k, k ∉ I → σ k = k := by
      intro k hk
      exact Equiv.swap_apply_of_ne_of_ne (fun h => hk (h ▸ hi))
        (fun h => hk (h ▸ hj))
    have hcomm : ψ u * f = f * ψ u :=
      qTwoFour_psi_comm_of_mem_qTwoFixI S hf hσ huLift
    have hu2 : u * u = 1 :=
      qTwoFour_square_one_of_mulVec_single (by simpa [σ] using Equiv.swap_mul_self i j) huVec
    obtain ⟨u', hu'gl, hu'psi⟩ := hact u
    have hψeq : ψ u' = ψ u := by
      rw [hu'psi]
      have hconj : f * ψ u * f⁻¹ = ψ u := by
        rw [← hcomm]
        group
      exact hconj
    have huGL2 : (u : GL (Fin m) F0) * (u : GL (Fin m) F0) = 1 := by
      have h := congrArg (fun x : Su F0 2 1 m => (x : GL (Fin m) F0)) hu2
      simpa using h
    have hu'2 : u' * u' = 1 := by
      apply Subtype.ext
      apply Units.ext
      have hGL : (u' : GL (Fin m) F0) * (u' : GL (Fin m) F0) = 1 := by
        rw [hu'gl]
        calc d * (u : GL (Fin m) F0) * d⁻¹ * (d * (u : GL (Fin m) F0) * d⁻¹) =
            d * ((u : GL (Fin m) F0) * (u : GL (Fin m) F0)) * d⁻¹ := by group
          _ = 1 := by rw [huGL2]; group
      simpa only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one]
        using congrArg (fun x : GL (Fin m) F0 => ((x : Matrix (Fin m) (Fin m) F0))) hGL
    have hu'eq : u' = u :=
      qTwoFour_eq_of_square_one_of_map_eq hF0 hm ψ hker (u := u') (v := u)
        hu'2 hu2 hψeq
    have hdu : d * (u : GL (Fin m) F0) = (u : GL (Fin m) F0) * d := by
      have hgl := hu'gl
      rw [hu'eq] at hgl
      calc d * (u : GL (Fin m) F0) = (d * (u : GL (Fin m) F0) * d⁻¹) * d := by group
        _ = (u : GL (Fin m) F0) * d := by rw [← hgl]
    let U : Matrix (Fin m) (Fin m) F0 := ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)
    have hmat : Matrix.diagonal dvec * U = U * Matrix.diagonal dvec := by
      have h := congrArg (fun x : GL (Fin m) F0 =>
        ((x : Matrix (Fin m) (Fin m) F0))) hdu
      simpa [U, hdmat] using h
    have hUij : U i j = 1 := by
      have h := congrFun (huVec j) i
      have hσj : σ j = i := by simp [σ]
      simpa [U, Matrix.mulVec_single_one, hσj] using h
    exact qTwoFour_diagonal_eq_of_comm hmat hUij

theorem qTwoFour_block_le_centralizer_fix (hF0 : Nat.card F0 = 4)
    {ψ : Su F0 2 1 m →* G} (hψ : QTwoOrdModel Bs L ψ)
    {ε : Fin m ↪ Fin (n + 1)} (hε : QTwoFrameMatch S ψ ε)
    {I : Finset (Fin m)} (hI : I.card = 4) :
    qTwoBlockOf ψ 1 I ≤
      Subgroup.centralizer (qTwoFixI S.ρA (qTwoFrameSet ε 1 I) : Set G) := by
  classical
  have hm : 4 ≤ m := by
    have := S.hm
    omega
  rintro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  rw [qTwoBlockOf, Subgroup.mem_map] at hy
  obtain ⟨w, hw, hwψ⟩ := hy
  have hy_eq : ψ w = y := by
    simpa [MulAut.conj_apply] using hwψ
  rw [← hy_eq]
  have hfBs : f ∈ Bs := qTwoFour_mem_Bs_of_mem_qTwoFixI S hf
  obtain ⟨g, hgdiag, hact⟩ := hψ.2.2 ⟨f, hfBs⟩
  obtain ⟨dvec, hdmat⟩ := hgdiag
  have hd_eq : ∀ i ∈ I, ∀ j ∈ I, dvec i = dvec j :=
    fun i hi j hj =>
      qTwoFour_diagonal_eq_on_fourSet S hF0 hm hε hψ.2.1 hf hdmat hact hi hj
  have hcomm_block : Matrix.diagonal dvec *
      ((w : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      ((w : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) * Matrix.diagonal dvec :=
    diagonal_mul_comm_of_mem_coordBlockSU hw hd_eq
  obtain ⟨w', hw'gl, hw'psi⟩ := hact w
  have hw'eq : w' = w := by
    apply Subtype.ext
    apply Units.ext
    have hgl : g * (w : GL (Fin m) F0) = (w : GL (Fin m) F0) * g := by
      apply Units.ext
      simpa [hdmat] using hcomm_block
    have hGL : (w' : GL (Fin m) F0) = (w : GL (Fin m) F0) := by
      rw [hw'gl]
      calc g * (w : GL (Fin m) F0) * g⁻¹ = (w : GL (Fin m) F0) * g * g⁻¹ := by
            rw [hgl]
        _ = (w : GL (Fin m) F0) := by group
    simpa only [Subgroup.coe_one, Units.val_one]
      using congrArg (fun x : GL (Fin m) F0 => ((x : Matrix (Fin m) (Fin m) F0))) hGL
  have hpsi_eq : ψ w = f * ψ w * f⁻¹ := by
    have h := hw'psi
    rw [hw'eq] at h
    exact h
  have hconj : f * ψ w * f⁻¹ = ψ w := hpsi_eq.symm
  have hcomm : f * ψ w = ψ w * f := mul_inv_eq_iff_eq_mul.mp hconj
  exact hcomm

end Fixed

section Components

open CFSG.StandardType CFSG.Assembly CFSG.Open
open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open scoped Pointwise Matrix commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {m n : ℕ}

theorem qTwoChart_L_normal_of_noncyclic (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    (hnc : ∃ S₀ : Subgroup G, S₀ ≤ L ∧ IsPGroup 3 S₀ ∧ ¬ IsCyclic S₀) :
    (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal := by
  have hSstar : LargeEvenSStar 3 B x L :=
    (CFSG.StandardType.FrameRoute.sStar_of_restHyp S.hcfg.1).2
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hSstar.2.2.2.1.1
  rw [Subgroup.normal_subgroupOf_iff hLx]
  intro h k hh hk
  have hknorm : k ∈ Subgroup.normalizer (L : Set G) :=
    mem_normalizer_of_sstar hSstar hnc hk
  exact (Subgroup.mem_normalizer_iff.mp hknorm h).mp hh

theorem qTwoChart_L_normal (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    (hF0 : Nat.card F0 = 4) (ψ : Su F0 2 1 m →* G)
    (hψ : QTwoOrdModel Bs L ψ) :
    (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal := by
  exact qTwoChart_L_normal_of_noncyclic S
    (qTwoFour_exists_noncyclic_three hF0 S.hm ψ hψ.1 hψ.2.1)

theorem qTwoChart_mem_qTwoFixI_base (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    (ψ : Su F0 2 1 m →* G) (hψ : QTwoOrdModel Bs L ψ)
    (ε0 : Fin m ↪ Fin (n + 1)) (hε0 : QTwoFrameMatch S ψ ε0) (J : Finset (Fin m)) :
    x ∈ qTwoFixI S.ρA (J.map ε0) := by
  let I₀ : Finset (Fin (n + 1)) := J.map ε0
  have hx : x ∈ Bs := S.hLocal.mem
  let Stab : Subgroup (MulAut ↥Bs) :=
    MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs)
  have hqSym_le : qTwoSymI S.ρA I₀ ≤ Stab := by
    rw [qTwoSymI]
    refine Subgroup.map_le_iff_le_comap.mpr ?_
    refine (Subgroup.closure_le _).mpr ?_
    intro τ hτ
    obtain ⟨σ, -, heq⟩ := qTwoFour_supported_native hτ
    have hτeq := heq.symm
    obtain ⟨u, -, hu_lift⟩ := hε0 σ
    have hψuL : ψ u ∈ L := by
      rw [← hψ.1]
      exact ⟨u, rfl⟩
    have hψuN : ψ u ∈ Subgroup.normalizer (Bs : Set G) := hu_lift.2.1
    have hρ : (((S.ρA τ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) =
        ggConjAut Bs hψuN := by
      ext b
      rw [ggConjAut_apply]
      simpa [hτeq] using hu_lift.2.2 b
    have haut : (((S.ρA τ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) ∈
        ggAutomizer L Bs := by
      simpa [hρ] using
        (ggConjAut_mem_ggAutomizer (H := L) (Bs := Bs) hψuL hψuN)
    change (((S.ρA τ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) ⟨x, hx⟩ = ⟨x, hx⟩
    exact S.hLocal.fixes _ haut
  rw [qTwoFixI]
  refine Subgroup.mem_map.mpr ⟨⟨x, hx⟩, ?_, rfl⟩
  rw [Subgroup.mem_iInf]
  intro s
  change (s : MulAut ↥Bs) ⟨x, hx⟩ = ⟨x, hx⟩
  exact hqSym_le (show (s : MulAut ↥Bs) ∈ qTwoSymI S.ρA I₀ from s.2)

theorem qTwoChart_centralizer_normal {F : Subgroup G}
    (hxF : x ∈ F)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hLnorm : (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal) :
    ((L ⊓ Subgroup.centralizer (F : Set G)).subgroupOf
      (Subgroup.centralizer (F : Set G))).Normal := by
  have hCx : Subgroup.centralizer (F : Set G) ≤
      Subgroup.centralizer ({x} : Set G) := by
    refine Subgroup.centralizer_le ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hxF
  rw [Subgroup.normal_subgroupOf_iff inf_le_right]
  intro h k hh hk
  have hhL : h ∈ L := hh.1
  have hconjL : k * h * k⁻¹ ∈ L :=
    (Subgroup.normal_subgroupOf_iff hLx).mp hLnorm h k hhL (hCx hk)
  have hkC : k ∈ Subgroup.centralizer (F : Set G) := hk
  have hkNorm : k ∈ Subgroup.normalizer (Subgroup.centralizer (F : Set G) : Set G) :=
    Subgroup.le_normalizer hkC
  have hconjC : k * h * k⁻¹ ∈ Subgroup.centralizer (F : Set G) :=
    (Subgroup.mem_normalizer_iff.mp hkNorm h).mp hh.2
  exact ⟨hconjL, hconjC⟩

theorem qTwoChart_block_component_of_normal {F : Subgroup G} {U : Subgroup G}
    (hxF : x ∈ F)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hLnorm : (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal)
    (hUle : U ≤ L ⊓ Subgroup.centralizer (F : Set G))
    (hUnormal : (U.subgroupOf (L ⊓ Subgroup.centralizer (F : Set G))).Normal)
    (hUq : CFSG.Open.IsQuasisimple U) :
    CFSG.Open.IsComponentOf U (Subgroup.centralizer (F : Set G)) := by
  have hCnormal : ((L ⊓ Subgroup.centralizer (F : Set G)).subgroupOf
      (Subgroup.centralizer (F : Set G))).Normal :=
    qTwoChart_centralizer_normal hxF hLx hLnorm
  refine ⟨hUle.trans inf_le_right, ?_, hUq⟩
  exact CFSG.Open.IsSubnormal.step hUle hUnormal
    (CFSG.Open.IsSubnormal.step inf_le_right hCnormal
      (CFSG.Open.IsSubnormal.refl _))

theorem qTwoChart_qTwoBlock_quasisimple
    {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    (hF0 : Nat.card F0 = 4) (ψ : Su F0 2 1 m →* G)
    (hψ : QTwoOrdModel Bs L ψ) {J : Finset (Fin m)} (hJ4 : J.card = 4) :
    CFSG.Open.IsQuasisimple ↥(qTwoBlockOf ψ 1 J) := by
  have hKq : CFSG.IsQuasisimple ↥(coordBlockSU F0 2 1 J) :=
    qTwoS34_isQuasisimple_coordBlockSU hF0 hJ4
  have hnonab : ∃ a b : ↥(coordBlockSU F0 2 1 J), a * b ≠ b * a := by
    obtain ⟨-, -, a', b', hab'⟩ := hKq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a'
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b'
    exact ⟨a, b, fun h => hab' (by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
  have hnotle : ¬ coordBlockSU F0 2 1 J ≤ ψ.ker := by
    intro hsub
    obtain ⟨a, b, hne⟩ := hnonab
    have hza : ((a : Su F0 2 1 m) : Su F0 2 1 m) ∈
        Subgroup.center (Su F0 2 1 m) := hψ.2.1 (hsub a.2)
    have hcomm : (a : Su F0 2 1 m) * (b : Su F0 2 1 m) =
        (b : Su F0 2 1 m) * (a : Su F0 2 1 m) :=
      (Subgroup.mem_center_iff.mp hza (b : Su F0 2 1 m)).symm
    exact hne (Subtype.ext hcomm)
  have hnat : CFSG.IsQuasisimple ↥((coordBlockSU F0 2 1 J).map ψ) :=
    CFSG.LocalCores.isQuasisimple_map hKq ψ hnotle
  have hmap : qTwoBlockOf ψ 1 J = (coordBlockSU F0 2 1 J).map ψ := by
    ext x
    simp [qTwoBlockOf]
  have hnat' : CFSG.IsQuasisimple ↥(qTwoBlockOf ψ 1 J) := by
    rwa [hmap]
  exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).1
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hnat')

theorem qTwoChart_baseBlock_component (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    (hF0 : Nat.card F0 = 4) (ψ : Su F0 2 1 m →* G)
    (hψ : QTwoOrdModel Bs L ψ)
    (ε0 : Fin m ↪ Fin (n + 1)) (hε0 : QTwoFrameMatch S ψ ε0)
    {J : Finset (Fin m)} (hJ4 : J.card = 4)
    (hUle : qTwoBlockOf ψ 1 J ≤
      L ⊓ Subgroup.centralizer ((qTwoFixI S.ρA (J.map ε0) : Subgroup G) : Set G))
    (hUnormal : ((qTwoBlockOf ψ 1 J).subgroupOf
      (L ⊓ Subgroup.centralizer ((qTwoFixI S.ρA (J.map ε0) : Subgroup G) : Set G))).Normal) :
    CFSG.Open.IsComponentOf (qTwoBlockOf ψ 1 J)
      (Subgroup.centralizer ((qTwoFixI S.ρA (J.map ε0) : Subgroup G) : Set G)) := by
  have hSstar : LargeEvenSStar 3 B x L :=
    (CFSG.StandardType.FrameRoute.sStar_of_restHyp S.hcfg.1).2
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hSstar.2.2.2.1.1
  have hLnorm : (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal :=
    qTwoChart_L_normal S hF0 ψ hψ
  have hfix : x ∈ qTwoFixI S.ρA (J.map ε0) :=
    qTwoChart_mem_qTwoFixI_base S ψ hψ ε0 hε0 J
  have hUq : CFSG.Open.IsQuasisimple ↥(qTwoBlockOf ψ 1 J) :=
    qTwoChart_qTwoBlock_quasisimple hF0 ψ hψ hJ4
  exact qTwoChart_block_component_of_normal hfix hLx hLnorm hUle hUnormal hUq

end Components

section Transport

open CFSG.StandardType
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]
variable {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {𝒦 : Finset (Subgroup G)} {m n : ℕ}

theorem qTwoFour_mem_fixI_iff
    (ρA : Equiv.Perm (Fin (n + 1)) ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (I : Finset (Fin (n + 1))) (b : Bs) :
    (b : G) ∈ qTwoFixI ρA I ↔
      ∀ σ : Equiv.Perm (Fin (n + 1)), (∀ y, y ∉ I → σ y = y) →
        ((ρA σ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut Bs) b = b := by
  classical
  let act : Equiv.Perm (Fin (n + 1)) →* MulAut Bs :=
    (ggAutomizerJoin L Bs 𝒦).subtype.comp ρA.toMonoidHom
  constructor
  · intro hb σ hσ
    obtain ⟨b', hb', heq⟩ := Subgroup.mem_map.mp hb
    have hbb : b' = b := Subtype.ext heq
    subst b'
    have hs : act σ ∈ qTwoSymI ρA I :=
      Subgroup.mem_map.mpr ⟨σ, Subgroup.subset_closure hσ, rfl⟩
    have h := (Subgroup.mem_iInf.mp hb') ⟨act σ, hs⟩
    exact h
  · intro hb
    have hclosure : ∀ σ ∈ Subgroup.closure
        {σ : Equiv.Perm (Fin (n + 1)) | ∀ y, y ∉ I → σ y = y}, act σ b = b := by
      intro σ hσ
      refine Subgroup.closure_induction (p := fun σ _ => act σ b = b)
        (fun σ hσ => hb σ hσ) ?_ ?_ ?_ hσ
      · simp
      · intro σ τ _ _ hσ hτ
        rw [map_mul, MulAut.mul_apply, hτ, hσ]
      · intro σ _ hσ
        apply (act σ).injective
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply, hσ]
    refine Subgroup.mem_map.mpr ⟨b, Subgroup.mem_iInf.mpr ?_, rfl⟩
    intro s
    obtain ⟨σ, hσ, heq⟩ := Subgroup.mem_map.mp s.2
    change (s : MulAut Bs) b = b
    rw [← heq]
    exact hclosure σ hσ

theorem qTwoFour_supported_conj (I : Finset (Fin (n + 1)))
    (π σ : Equiv.Perm (Fin (n + 1)))
    (hσ : ∀ y, y ∉ I → σ y = y) :
    ∀ y, y ∉ I.map π.toEmbedding → (π * σ * π⁻¹) y = y := by
  classical
  intro y hy
  have hpre : π⁻¹ y ∉ I := by
    intro h
    exact hy (Finset.mem_map.mpr ⟨π⁻¹ y, h, by simp⟩)
  simp only [Equiv.Perm.mul_apply, hσ _ hpre]
  simp

theorem qTwoFour_fixI_action_mem
    (ρA : Equiv.Perm (Fin (n + 1)) ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (I : Finset (Fin (n + 1))) (π : Equiv.Perm (Fin (n + 1)))
    (b : Bs) (hb : (b : G) ∈ qTwoFixI ρA I) :
    ((((ρA π : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut Bs) b : Bs) : G) ∈
      qTwoFixI ρA (I.map π.toEmbedding) := by
  classical
  rw [qTwoFour_mem_fixI_iff]
  intro σ hσ
  have hmap : (I.map π.toEmbedding).map (π⁻¹).toEmbedding = I := by
    ext y
    simp [Equiv.Perm.inv_def]
  have hsupp : ∀ y, y ∉ I → (π⁻¹ * σ * π) y = y := by
    simpa [hmap] using qTwoFour_supported_conj (I.map π.toEmbedding) π⁻¹ σ hσ
  have hfixed := (qTwoFour_mem_fixI_iff ρA I b).mp hb (π⁻¹ * σ * π) hsupp
  have heq := congrArg (fun c : Bs => ((ρA π : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut Bs) c) hfixed
  simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply,
    MulAut.inv_apply, MulEquiv.apply_symm_apply] using heq

theorem qTwoFour_fixI_conj
    (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    {g : G} {π : Equiv.Perm (Fin (n + 1))}
    (hg : QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g π)
    (I : Finset (Fin (n + 1))) :
    (qTwoFixI S.ρA I).map (MulAut.conj g).toMonoidHom =
      qTwoFixI S.ρA (I.map π.toEmbedding) := by
  classical
  apply le_antisymm
  · rintro z ⟨b, hb, rfl⟩
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    have h := qTwoFour_fixI_action_mem S.ρA I π b'
      (Subgroup.mem_map.mpr ⟨b', hb', rfl⟩)
    simpa [hg.2.2 b', MulAut.conj_apply] using h
  · intro z hz
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hz
    let c : Bs := (((S.ρA π : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut Bs)⁻¹) b
    have hc : (c : G) ∈ qTwoFixI S.ρA I := by
      have hbG : (b : G) ∈ qTwoFixI S.ρA (I.map π.toEmbedding) :=
        Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
      have h := qTwoFour_fixI_action_mem S.ρA (I.map π.toEmbedding) π⁻¹ b hbG
      have hmap : (I.map π.toEmbedding).map (π⁻¹).toEmbedding = I := by
        ext y
        simp [Equiv.Perm.inv_def]
      simpa [hmap, c] using h
    refine Subgroup.mem_map.mpr ⟨(c : G), hc, ?_⟩
    have h := hg.2.2 c
    simpa [c, MulAut.conj_apply] using h.symm

end Transport

section Swaps

open Matrix CFSG.StandardType CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open scoped MatrixGroups Pointwise

variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]

theorem qTwoFour_extend_swap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (ε : α → β) (hε : Function.Injective ε)
    [DecidablePred (fun x : β => x ∈ Set.range ε)] (i j : α) :
    (Equiv.swap i j).extendDomain (Equiv.ofInjective ε hε) =
      Equiv.swap (ε i) (ε j) := by
  classical
  ext x
  by_cases hx : x ∈ Set.range ε
  · obtain ⟨y, rfl⟩ := hx
    change ((Equiv.swap i j).extendDomain (Equiv.ofInjective ε hε))
        (↑((Equiv.ofInjective ε hε) y)) =
      Equiv.swap (ε i) (ε j) (↑((Equiv.ofInjective ε hε) y))
    rw [Equiv.Perm.extendDomain_apply_image]
    by_cases hyi : y = i
    · subst y; simp
    · by_cases hyj : y = j
      · subst y; simp
      · rw [Equiv.swap_apply_of_ne_of_ne hyi hyj]
        change (ε y) = Equiv.swap (ε i) (ε j) (ε y)
        rw [Equiv.swap_apply_of_ne_of_ne (fun h => hyi (hε h))
          (fun h => hyj (hε h))]
  · rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ hx]
    rw [Equiv.swap_apply_of_ne_of_ne]
    · rintro rfl; exact hx ⟨i, rfl⟩
    · rintro rfl; exact hx ⟨j, rfl⟩

theorem qTwoFour_mem_block_of_basis_action {m : ℕ} {I : Finset (Fin m)}
    {σ : Equiv.Perm (Fin m)} {u : Su F0 2 1 m}
    (hu : ∀ i : Fin m,
      ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1 =
        Pi.single (σ i) 1)
    (hσ : ∀ i : Fin m, i ∉ I → σ i = i) :
    u ∈ coordBlockSU F0 2 1 I := by
  rw [mem_coordBlockSU_iff]
  have hσinv : ∀ i : Fin m, i ∉ I → σ.symm i = i := by
    intro i hi
    have h := congrArg σ.symm (hσ i hi)
    simpa using h.symm
  intro i j hij
  have hentry : ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) i j =
      if i = σ j then 1 else 0 := by
    have h := congrFun (hu j) i
    simpa [Matrix.mulVec_single_one, Pi.single_apply] using h
  rw [hentry]
  by_cases hj : j ∈ I
  · have hi : i ∉ I := by tauto
    have hiff : (i = σ j) ↔ (i = j) := by
      constructor
      · intro h
        have h' := congrArg σ.symm h
        simpa [hσinv i hi] using h'
      · intro h
        rw [← h]
        exact (hσ i hi).symm
    by_cases h : i = j
    · subst j
      simp [hσ i hi]
    · have h' : i ≠ σ j := fun hc => h (hiff.mp hc)
      simp [h, h']
  · have hσj : σ j = j := hσ j hj
    simp [hσj]

section Lifts

variable {G : Type} [Group G] [Finite G]
variable {B Bs L D J : Subgroup G} {x : G} {𝒦 : Finset (Subgroup G)} {m n : ℕ}
variable (S : QTwoChartSetting B Bs x L D J 𝒦 m n)

theorem qTwoFour_conj_induces
    {g u : G} {π τ : Equiv.Perm (Fin (n + 1))}
    (hg : QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g π)
    (hu : QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA u τ) (b : Bs) :
    ((((S.ρA (π * τ * π⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) b : Bs) : G) =
      (g * u * g⁻¹) * (b : G) * (g * u * g⁻¹)⁻¹ := by
  have hg' : g ∈ QTwoH L 𝒦 ∧ g ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ b : Bs,
        ((((S.ρA π : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) b : Bs) : G) =
          g * (b : G) * g⁻¹ := hg
  have hu' : u ∈ QTwoH L 𝒦 ∧ u ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ b : Bs,
        ((((S.ρA τ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) b : Bs) : G) =
          u * (b : G) * u⁻¹ := hu
  let bπ : Bs := (((S.ρA π : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)⁻¹) b
  have hbπ : (bπ : G) = g⁻¹ * (b : G) * g := by
    have h := hg'.2.2 bπ
    have hb : ((((S.ρA π : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) bπ : Bs) : G) =
        (b : G) := by
      simp [bπ]
    rw [hb] at h
    rw [h]
    group
  have hL :
      ((((S.ρA (π * τ * π⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) b : Bs) : G) =
        g * (u * (bπ : G) * u⁻¹) * g⁻¹ := by
    have hmap :
        ((((S.ρA (π * τ * π⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) b : Bs)) =
          (((S.ρA π : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)
            ((((S.ρA τ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) bπ : Bs))) := by
      dsimp [bπ]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
        MulAut.mul_apply, MulAut.inv_apply]
    rw [congrArg Subtype.val hmap]
    rw [hg'.2.2 ((((S.ρA τ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) bπ))]
    rw [hu'.2.2 bπ]
  rw [hL, hbπ]
  group

variable {ψ : Su F0 2 1 m →* G}

omit [Finite G] in
theorem qTwoFour_conj_mem_block {g : G} {u : Su F0 2 1 m} {I : Finset (Fin m)}
    (hu : u ∈ coordBlockSU F0 2 1 I) :
    g * ψ u * g⁻¹ ∈ qTwoBlockOf ψ g I := by
  have hmap : g * ψ u * g⁻¹ ∈
      (coordBlockSU F0 2 1 I).map ((MulAut.conj g).toMonoidHom.comp ψ) := by
    refine Subgroup.mem_map.mpr ⟨u, hu, ?_⟩
    simp [MulAut.conj_apply]
  exact hmap

theorem qTwoFour_exists_overlapping_swap_elements
    (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    {ψ : Su F0 2 1 m →* G} (ε0 : Fin m ↪ Fin (n + 1))
    (hfm : QTwoFrameMatch S ψ ε0)
    {I I' : Finset (Fin m)} (hI : I.card = 4) (_hI' : I'.card = 4)
    {g g' : G} {π π' : Equiv.Perm (Fin (n + 1))}
    (hg : QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g π)
    (hg' : QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g' π')
    (hsame : qTwoFrameSet ε0 π I = qTwoFrameSet ε0 π' I') :
    ∃ (x x' : G) (a b c : Fin (n + 1)),
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      x ∈ qTwoBlockOf ψ g I ∧
      x' ∈ qTwoBlockOf ψ g' I' ∧
      (∀ y : Bs,
        ((((S.ρA (Equiv.swap a b) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) y : Bs) : G) =
          x * (y : G) * x⁻¹) ∧
      (∀ y : Bs,
        ((((S.ρA (Equiv.swap b c) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) y : Bs) : G) =
          x' * (y : G) * x'⁻¹) := by
  classical
  have hAcard : (qTwoFrameSet ε0 π I).card = 4 := by
    simpa [qTwoFrameSet] using hI
  have h2 : 2 < (qTwoFrameSet ε0 π I).card := by omega
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card_iff.mp h2
  have ha' : a ∈ qTwoFrameSet ε0 π' I' := by
    rw [← hsame]; exact ha
  have hb' : b ∈ qTwoFrameSet ε0 π' I' := by
    rw [← hsame]; exact hb
  have hc' : c ∈ qTwoFrameSet ε0 π' I' := by
    rw [← hsame]; exact hc
  obtain ⟨i1, hi1, hpi1⟩ : ∃ i ∈ I, π (ε0 i) = a := by
    rw [qTwoFrameSet] at ha
    obtain ⟨x, hx, hxa⟩ := Finset.mem_map.mp ha
    obtain ⟨i, hi, hix⟩ := Finset.mem_map.mp hx
    exact ⟨i, hi, by simpa [hix] using hxa⟩
  obtain ⟨i2, hi2, hpi2⟩ : ∃ i ∈ I, π (ε0 i) = b := by
    rw [qTwoFrameSet] at hb
    obtain ⟨x, hx, hxa⟩ := Finset.mem_map.mp hb
    obtain ⟨i, hi, hix⟩ := Finset.mem_map.mp hx
    exact ⟨i, hi, by simpa [hix] using hxa⟩
  obtain ⟨j2, hj2, hpj2⟩ : ∃ j ∈ I', π' (ε0 j) = b := by
    rw [qTwoFrameSet] at hb'
    obtain ⟨x, hx, hxa⟩ := Finset.mem_map.mp hb'
    obtain ⟨j, hj, hjx⟩ := Finset.mem_map.mp hx
    exact ⟨j, hj, by simpa [hjx] using hxa⟩
  obtain ⟨j3, hj3, hpj3⟩ : ∃ j ∈ I', π' (ε0 j) = c := by
    rw [qTwoFrameSet] at hc'
    obtain ⟨x, hx, hxa⟩ := Finset.mem_map.mp hc'
    obtain ⟨j, hj, hjx⟩ := Finset.mem_map.mp hx
    exact ⟨j, hj, by simpa [hjx] using hxa⟩
  let σ : Equiv.Perm (Fin m) := Equiv.swap i1 i2
  let σ' : Equiv.Perm (Fin m) := Equiv.swap j2 j3
  have hσsupp : ∀ i : Fin m, i ∉ I → σ i = i := by
    intro i hi
    dsimp [σ]
    exact Equiv.swap_apply_of_ne_of_ne (by rintro rfl; exact hi hi1)
      (by rintro rfl; exact hi hi2)
  have hσ'supp : ∀ j : Fin m, j ∉ I' → σ' j = j := by
    intro j hj
    dsimp [σ']
    exact Equiv.swap_apply_of_ne_of_ne (by rintro rfl; exact hj hj2)
      (by rintro rfl; exact hj hj3)
  obtain ⟨u, hu_mat, hu_lift⟩ := hfm σ
  obtain ⟨u', hu'_mat, hu'_lift⟩ := hfm σ'
  have hu_block : u ∈ coordBlockSU F0 2 1 I :=
    qTwoFour_mem_block_of_basis_action hu_mat hσsupp
  have hu'_block : u' ∈ coordBlockSU F0 2 1 I' :=
    qTwoFour_mem_block_of_basis_action hu'_mat hσ'supp
  let x : G := g * ψ u * g⁻¹
  let x' : G := g' * ψ u' * g'⁻¹
  have hxmem : x ∈ qTwoBlockOf ψ g I := by
    dsimp [x]
    exact qTwoFour_conj_mem_block (ψ := ψ) (g := g) (I := I) hu_block
  have hx'mem : x' ∈ qTwoBlockOf ψ g' I' := by
    dsimp [x']
    exact qTwoFour_conj_mem_block (ψ := ψ) (g := g') (I := I') hu'_block
  have hσconj : π * (σ.extendDomain (Equiv.ofInjective ε0 ε0.injective)) * π⁻¹ =
      Equiv.swap a b := by
    dsimp [σ]
    rw [qTwoFour_extend_swap ε0 ε0.injective i1 i2]
    ext z
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    rw [Function.Injective.map_swap π.injective (ε0 i1) (ε0 i2) (π⁻¹ z)]
    rw [Equiv.Perm.inv_def, π.apply_symm_apply, hpi1, hpi2]
  have hσ'conj : π' * (σ'.extendDomain (Equiv.ofInjective ε0 ε0.injective)) * π'⁻¹ =
      Equiv.swap b c := by
    dsimp [σ']
    rw [qTwoFour_extend_swap ε0 ε0.injective j2 j3]
    ext z
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    rw [Function.Injective.map_swap π'.injective (ε0 j2) (ε0 j3) (π'⁻¹ z)]
    rw [Equiv.Perm.inv_def, π'.apply_symm_apply, hpj2, hpj3]
  have hxact : ∀ y : Bs,
      ((((S.ρA (Equiv.swap a b) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) y : Bs) : G) =
        x * (y : G) * x⁻¹ := by
    intro y
    have h := qTwoFour_conj_induces (S := S) hg hu_lift y
    rw [hσconj] at h
    simpa [x] using h
  have hx'act : ∀ y : Bs,
      ((((S.ρA (Equiv.swap b c) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) y : Bs) : G) =
        x' * (y : G) * x'⁻¹ := by
    intro y
    have h := qTwoFour_conj_induces (S := S) hg' hu'_lift y
    rw [hσ'conj] at h
    simpa [x'] using h
  exact ⟨x, x', a, b, c, hab, hbc, hac, hxmem, hx'mem, hxact, hx'act⟩


theorem qTwoFour_rho_mul_action_eq_of_conj_mul_eq
    (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    {x x' : G} {a b c : Fin (n + 1)}
    (hx : ∀ y : Bs,
      ((((S.ρA (Equiv.swap a b) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) y : Bs) : G) =
        x * (y : G) * x⁻¹)
    (hx' : ∀ y : Bs,
      ((((S.ρA (Equiv.swap b c) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) y : Bs) : G) =
        x' * (y : G) * x'⁻¹)
    (hcomm : x * x' = x' * x) (y : Bs) :
    ((((S.ρA (Equiv.swap a b * Equiv.swap b c) :
        ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) y : Bs) : G) =
      ((((S.ρA (Equiv.swap b c * Equiv.swap a b) :
        ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) y : Bs) : G) := by
  have hL :
      ((((S.ρA (Equiv.swap a b * Equiv.swap b c) :
        ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) y : Bs) : G) =
        x * (x' * (y : G) * x'⁻¹) * x⁻¹ := by
    have hmap :
        ((((S.ρA (Equiv.swap a b * Equiv.swap b c) :
          ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) y : Bs)) =
          (((S.ρA (Equiv.swap a b) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)
            ((((S.ρA (Equiv.swap b c) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) y : Bs))) := by
      simp only [map_mul, Subgroup.coe_mul, MulAut.mul_apply]
    rw [congrArg Subtype.val hmap]
    rw [hx ((((S.ρA (Equiv.swap b c) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) y))]
    rw [hx' y]
  have hR :
      ((((S.ρA (Equiv.swap b c * Equiv.swap a b) :
        ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) y : Bs) : G) =
        x' * (x * (y : G) * x⁻¹) * x'⁻¹ := by
    have hmap :
        ((((S.ρA (Equiv.swap b c * Equiv.swap a b) :
          ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) y : Bs)) =
          (((S.ρA (Equiv.swap b c) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)
            ((((S.ρA (Equiv.swap a b) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) y : Bs))) := by
      simp only [map_mul, Subgroup.coe_mul, MulAut.mul_apply]
    rw [congrArg Subtype.val hmap]
    rw [hx' ((((S.ρA (Equiv.swap a b) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) y))]
    rw [hx y]
  have hcomm_inv : x'⁻¹ * x⁻¹ = x⁻¹ * x'⁻¹ := by
    simpa only [_root_.mul_inv_rev] using congrArg Inv.inv hcomm
  rw [hL, hR]
  calc
    x * (x' * (y : G) * x'⁻¹) * x⁻¹
        = (x * x') * (y : G) * (x'⁻¹ * x⁻¹) := by group
    _ = (x' * x) * (y : G) * (x⁻¹ * x'⁻¹) := by rw [hcomm, hcomm_inv]
    _ = x' * (x * (y : G) * x⁻¹) * x'⁻¹ := by group


end Lifts


end Swaps

section Assembly

open CFSG.StandardType CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open scoped Pointwise Matrix

variable {G : Type} [Group G] [Finite G]
variable {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {𝒦 : Finset (Subgroup G)} {m n : ℕ}

theorem qTwoChart_fourBlock_component
    (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] (hF0 : Nat.card F0 = 4)
    (ψ : Su F0 2 1 m →* G) (hψ : QTwoOrdModel Bs L ψ)
    (ε0 : Fin m ↪ Fin (n + 1)) (hε0 : QTwoFrameMatch S ψ ε0)
    {g : G} {π : Equiv.Perm (Fin (n + 1))} {I : Finset (Fin m)}
    (hg : QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g π) (hI4 : I.card = 4) :
    CFSG.Open.IsComponentOf (qTwoBlockOf ψ g I)
      (Subgroup.centralizer (qTwoFixI S.ρA (qTwoFrameSet ε0 π I) : Set G)) := by
  classical
  have hbase : qTwoBlockOf ψ 1 I = (coordBlockSU F0 2 1 I).map ψ := by
    ext z
    simp [qTwoBlockOf]
  have hUL : qTwoBlockOf ψ 1 I ≤ L := by
    rw [hbase, ← hψ.1]
    rintro z ⟨u, _, rfl⟩
    exact ⟨u, rfl⟩
  have hUC := qTwoFour_block_le_centralizer_fix S hF0 hψ hε0 hI4
  have hUle : qTwoBlockOf ψ 1 I ≤
      L ⊓ Subgroup.centralizer (qTwoFixI S.ρA (I.map ε0) : Set G) := by
    simpa [qTwoFour_frameSet_one] using le_inf hUL hUC
  obtain ⟨j, hj⟩ : ∃ j : Fin m, j ∉ I := by
    have hlt : I.card < Fintype.card (Fin m) := by
      rw [Fintype.card_fin, hI4]
      exact lt_of_lt_of_le (by norm_num : 4 < 5) S.hm
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := I) (t := Finset.univ) (by simpa using hlt)
    exact ⟨j, hj⟩
  have hUnormal : ((qTwoBlockOf ψ 1 I).subgroupOf
      (L ⊓ Subgroup.centralizer (qTwoFixI S.ρA (I.map ε0) : Set G))).Normal := by
    have hle : (coordBlockSU F0 2 1 I).map ψ ≤
        L ⊓ Subgroup.centralizer (qTwoFixI S.ρA (qTwoFrameSet ε0 1 I) : Set G) := by
      rw [qTwoFour_frameSet_one, ← hbase]
      exact hUle
    have h := qTwoFour_block_image_normal_exists
      (S := S) hF0 S.hm hI4 hj hψ hε0 hle
    rwa [qTwoFour_frameSet_one, ← hbase] at h
  have hcomp := qTwoChart_baseBlock_component S hF0 ψ hψ ε0 hε0 hI4 hUle hUnormal
  have hconj := CFSG.isComponentOf_map_mulEquiv (MulAut.conj g) hcomp
  have hblock : (qTwoBlockOf ψ 1 I).map (MulAut.conj g).toMonoidHom =
      qTwoBlockOf ψ g I := by
    rw [hbase, Subgroup.map_map]
    rfl
  have hcentralizer :
      (Subgroup.centralizer (qTwoFixI S.ρA (I.map ε0) : Set G)).map
        (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer (qTwoFixI S.ρA (qTwoFrameSet ε0 π I) : Set G) := by
    rw [← CFSG.StandardSubgroupAPI.centralizer_map_mulEquiv,
      qTwoFour_fixI_conj S hg]
    rfl
  rwa [hblock, hcentralizer] at hconj

theorem qTwoChart_fourBlock_unique (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] (hF0 : Nat.card F0 = 4)
    (ψ : Su F0 2 1 m →* G) (hψ : QTwoOrdModel Bs L ψ)
    (ε0 : Fin m ↪ Fin (n + 1)) (hε0 : QTwoFrameMatch S ψ ε0)
    {g g' : G} {π π' : Equiv.Perm (Fin (n + 1))} {J J' : Finset (Fin m)}
    (hg : QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g π)
    (hg' : QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g' π')
    (hJ4 : J.card = 4) (hJ'4 : J'.card = 4)
    (hframe : qTwoFrameSet ε0 π J = qTwoFrameSet ε0 π' J') :
    qTwoBlockOf ψ g J = qTwoBlockOf ψ g' J' := by
  have hAc := qTwoChart_fourBlock_component S hF0 ψ hψ ε0 hε0 hg hJ4
  have hBc := qTwoChart_fourBlock_component S hF0 ψ hψ ε0 hε0 hg' hJ'4
  rw [← hframe] at hBc
  have hA := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    hAc.1).mp
    ((CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).mpr hAc)
  have hB := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    hBc.1).mp
    ((CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).mpr hBc)
  rcases CFSG.LocalCores.distinct_components_commute hA hB with heq | hcomm
  · have h := Subgroup.subgroupOf_inj.mp heq
    simpa [inf_eq_left.mpr hAc.1, inf_eq_left.mpr hBc.1] using h
  · obtain ⟨u, v, a, b, c, hab, hbc, hac, hu, hv, huact, hvact⟩ :=
      qTwoFour_exists_overlapping_swap_elements S ε0 hε0 hJ4 hJ'4 hg hg' hframe
    have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have huv : u * v = v * u := by
      have h := Subgroup.mem_centralizer_iff.mp
        (hcent (show (⟨u, hAc.1 hu⟩ : ↥(Subgroup.centralizer
          (qTwoFixI S.ρA (qTwoFrameSet ε0 π J) : Set G))) ∈
          (qTwoBlockOf ψ g J).subgroupOf _ from hu))
        ⟨v, hBc.1 hv⟩ hv
      exact (congrArg Subtype.val h).symm
    have hact := qTwoFour_rho_mul_action_eq_of_conj_mul_eq S huact hvact huv
    have hAut : (((S.ρA (Equiv.swap a b * Equiv.swap b c) :
        ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) =
      (((S.ρA (Equiv.swap b c * Equiv.swap a b) :
        ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) := by
      ext y
      exact hact y
    have hswap := S.ρA.injective (Subtype.ext hAut)
    have h := congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ c) hswap
    have hab' : a = b := by
      simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm] using h
    exact (hab hab').elim

end Assembly

end CFSG.StandardType.QTwo

end
