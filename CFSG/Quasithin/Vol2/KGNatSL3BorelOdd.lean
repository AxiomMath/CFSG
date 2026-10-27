module

public import CFSG.Quasithin.Vol2.KGNatSL3Row
public import CFSG.Quasithin.Vol2.KGNatSL2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidualLin
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.CGT.Timmesfeld75 (utri ltri utriElt ltriElt wElt borel)
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def blockHom0 : SL(2, F) →* SpecialLinearGroup (Fin 3) F where
  toFun := blockSL
  map_one' := Subtype.ext (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blockSL])
  map_mul' A B := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blockSL, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two])

@[expose] def blockSL1 (A : SL(2, F)) : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 0, 0; 0, A 0 0, A 0 1; 0, A 1 0, A 1 1], by
    have hA := A.2
    rw [Matrix.det_fin_two] at hA
    rw [Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
      Matrix.tail_cons, Matrix.head_fin_const]
    linear_combination hA⟩

@[expose] def blockHom1 : SL(2, F) →* SpecialLinearGroup (Fin 3) F where
  toFun := blockSL1
  map_one' := Subtype.ext (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blockSL1])
  map_mul' A B := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blockSL1, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two])

theorem blockHom0_apply (A : SL(2, F)) : blockHom0 A = blockSL A := rfl

theorem blockHom1_apply (A : SL(2, F)) : blockHom1 A = blockSL1 A := rfl

theorem coe_blockSL (A : SL(2, F)) :
    ((blockSL A : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1] := rfl

theorem coe_blockSL1 (A : SL(2, F)) :
    ((blockSL1 A : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0; 0, A 0 0, A 0 1; 0, A 1 0, A 1 1] := rfl

theorem blockHom0_injective : Function.Injective (blockHom0 (F := F)) := by
  intro A B h
  rw [blockHom0_apply, blockHom0_apply] at h
  have h' := congrArg (fun C : SpecialLinearGroup (Fin 3) F => (C : Matrix (Fin 3) (Fin 3) F)) h
  simp only [coe_blockSL] at h'
  apply Subtype.ext
  ext i j
  have := congrFun (congrFun h' (Fin.castSucc i)) (Fin.castSucc j)
  fin_cases i <;> fin_cases j <;> simpa using this

theorem blockHom1_injective : Function.Injective (blockHom1 (F := F)) := by
  intro A B h
  rw [blockHom1_apply, blockHom1_apply] at h
  have h' := congrArg (fun C : SpecialLinearGroup (Fin 3) F => (C : Matrix (Fin 3) (Fin 3) F)) h
  simp only [coe_blockSL1] at h'
  apply Subtype.ext
  ext i j
  have := congrFun (congrFun h' i.succ) j.succ
  fin_cases i <;> fin_cases j <;> simpa using this

theorem blockHom0_utri (s : F) : blockHom0 (utriElt s) ∈ unitriangular 3 F := by
  rw [blockHom0_apply]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [coe_blockSL]
    fin_cases i <;> fin_cases j <;> simp_all [CFSG.CGT.Timmesfeld75.utriElt_apply_10]
  · rw [coe_blockSL]
    fin_cases i <;> simp [CFSG.CGT.Timmesfeld75.utriElt_apply_00,
      CFSG.CGT.Timmesfeld75.utriElt_apply_11]

theorem blockHom1_utri (s : F) : blockHom1 (utriElt s) ∈ unitriangular 3 F := by
  rw [blockHom1_apply]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [coe_blockSL1]
    fin_cases i <;> fin_cases j <;> simp_all [CFSG.CGT.Timmesfeld75.utriElt_apply_10]
  · rw [coe_blockSL1]
    fin_cases i <;> simp [CFSG.CGT.Timmesfeld75.utriElt_apply_00,
      CFSG.CGT.Timmesfeld75.utriElt_apply_11]

theorem blockHom0_ltri (t : F) :
    blockHom0 (ltriElt t) = SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) t := by
  apply Subtype.ext
  rw [SpecialLinearGroup.transvection_coe, blockHom0_apply, coe_blockSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CFSG.CGT.Timmesfeld75.ltriElt_apply_00,
    CFSG.CGT.Timmesfeld75.ltriElt_apply_01, CFSG.CGT.Timmesfeld75.ltriElt_apply_10,
    CFSG.CGT.Timmesfeld75.ltriElt_apply_11]

theorem blockHom1_ltri (t : F) :
    blockHom1 (ltriElt t) = SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) t := by
  apply Subtype.ext
  rw [SpecialLinearGroup.transvection_coe, blockHom1_apply, coe_blockSL1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CFSG.CGT.Timmesfeld75.ltriElt_apply_00,
    CFSG.CGT.Timmesfeld75.ltriElt_apply_01, CFSG.CGT.Timmesfeld75.ltriElt_apply_10,
    CFSG.CGT.Timmesfeld75.ltriElt_apply_11]

theorem exists_SL2_le_of_refl_mem {Y : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hU : unitriangular 3 F ≤ Y) {i : ℕ} (hi : 1 ≤ i) (hin : i < 3)
    (hr : reflection 3 F i hi hin ∈ Y) :
    ∃ φ : SL(2, F) →* SpecialLinearGroup (Fin 3) F, Function.Injective φ ∧ ∀ A, φ A ∈ Y := by
  have hR : CFSG.QuasithinUnique.Setup.X7a.reflGroup 3 F i ≤ Y := sup_le hU
    ((Subgroup.closure_le _).mpr (by
      rintro _ rfl
      rw [reflElt_of_lt hi hin]
      exact hr))
  have htop : utri F ⊔ ltri F = ⊤ := by
    rw [← CFSG.CGT.Timmesfeld75.conjSubgroup_wElt_utri,
      utri_sup_conj_eq_top CFSG.CGT.Timmesfeld75.wElt_not_mem_borel]
  obtain rfl | rfl : i = 1 ∨ i = 2 := by omega
  · refine ⟨blockHom0, blockHom0_injective, fun A => ?_⟩
    have hle : utri F ⊔ ltri F ≤ Y.comap blockHom0 := by
      refine sup_le (fun u hu => ?_) (fun l hl => ?_)
      · obtain ⟨s, rfl⟩ := CFSG.CGT.Timmesfeld75.mem_utri_iff.mp hu
        exact hU (blockHom0_utri s)
      · obtain ⟨t, rfl⟩ := CFSG.CGT.Timmesfeld75.mem_ltri_iff.mp hl
        rw [Subgroup.mem_comap, blockHom0_ltri]
        exact hR (CFSG.QuasithinUnique.Setup.X7a.lower_transvection_mem_reflGroup (n := 3)
          (K := F) (by norm_num) (by norm_num) (show (1 : Fin 3) ≠ 0 by decide) rfl rfl t)
    exact hle (htop ▸ Subgroup.mem_top A)
  · refine ⟨blockHom1, blockHom1_injective, fun A => ?_⟩
    have hle : utri F ⊔ ltri F ≤ Y.comap blockHom1 := by
      refine sup_le (fun u hu => ?_) (fun l hl => ?_)
      · obtain ⟨s, rfl⟩ := CFSG.CGT.Timmesfeld75.mem_utri_iff.mp hu
        exact hU (blockHom1_utri s)
      · obtain ⟨t, rfl⟩ := CFSG.CGT.Timmesfeld75.mem_ltri_iff.mp hl
        rw [Subgroup.mem_comap, blockHom1_ltri]
        exact hR (CFSG.QuasithinUnique.Setup.X7a.lower_transvection_mem_reflGroup (n := 3)
          (K := F) (by norm_num) (by norm_num) (show (2 : Fin 3) ≠ 1 by decide) rfl rfl t)
    exact hle (htop ▸ Subgroup.mem_top A)

theorem exists_prime_order_dvd_succ [Finite F] :
    ∃ (x : SL(2, F)) (p : ℕ), p.Prime ∧ orderOf x = p ∧ p ∣ Nat.card F + 1 := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hp : (Nat.card F + 1).minFac.Prime := Nat.minFac_prime (by omega)
  have : Fact (Nat.card F + 1).minFac.Prime := ⟨hp⟩
  have hpq : (Nat.card F + 1).minFac ∣ Nat.card F + 1 := Nat.minFac_dvd _
  have hsq : (Nat.card F - 1) * (Nat.card F + 1) = Nat.card F ^ 2 - 1 := by
    refine Nat.eq_sub_of_add_eq ?_
    obtain ⟨m, hm⟩ : ∃ m, Nat.card F = m + 1 := ⟨Nat.card F - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel]
    ring
  have hdvd : (Nat.card F + 1).minFac ∣ Nat.card SL(2, F) := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, ← hsq]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left hpq _) _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' _ hdvd
  exact ⟨x, _, hp, hx, hpq⟩

theorem factBorelOddSL3_holds : Ch11.SecC.FactBorelOddSL3 := by
  intro F _ _ n hn hF Y U hUY hU2 hUcard hodd
  have : CharP F 2 := charP_two_of_card (by omega) hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
  have hcard : Nat.card U = Nat.card P₀ := by
    rw [hUcard, hP₀, card_unitriangular, hF, ← pow_mul]
    norm_num [mul_comm]
  have hidx : U.index = (P₀ : Subgroup (SpecialLinearGroup (Fin 3) F)).index := by
    have h1 := Subgroup.card_mul_index U
    have h2 := Subgroup.card_mul_index (P₀ : Subgroup (SpecialLinearGroup (Fin 3) F))
    rw [← h2, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hUi : ¬ 2 ∣ U.index := by rw [hidx]; exact P₀.not_dvd_index
  obtain ⟨g, hg⟩ := CFSG.CGT.Timmesfeld75.exists_conjSubgroup_eq_of_sylow P₀ (hU2.toSylow hUi)
  rw [IsPGroup.toSylow_coe] at hg
  set Y' := Y.comap (MulAut.conj g).toMonoidHom with hY'
  have hmemY' : ∀ z, z ∈ Y' ↔ g * z * g⁻¹ ∈ Y := fun z => Iff.rfl
  have hUY' : unitriangular 3 F ≤ Y' := by
    intro u hu
    rw [hmemY']
    refine hUY (hg ▸ CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mpr ?_)
    rw [show g⁻¹ * (g * u * g⁻¹) * g = u by group, hP₀]
    exact hu
  have hY'B : Y' ≤ upperTriangular 3 F := by
    by_contra hcon
    have key : ∀ i (hi : 1 ≤ i) (hin : i < 3), reflection 3 F i hi hin ∈ Y' → False := by
      intro i hi hin hr
      obtain ⟨φ, hφ, hφY⟩ := exists_SL2_le_of_refl_mem hUY' hi hin hr
      obtain ⟨x, p, hp, hx, hpq⟩ := exists_prime_order_dvd_succ (F := F)
      have hy : g * φ x * g⁻¹ ∈ Y := (hmemY' _).mp (hφY x)
      have hord : orderOf (g * φ x * g⁻¹) = p := by
        rw [show g * φ x * g⁻¹ = (MulAut.conj g).toMonoidHom (φ x) from rfl,
          orderOf_injective _ (MulAut.conj g).injective, orderOf_injective φ hφ, hx]
      have hp2 : p ≠ 2 := by
        rintro rfl
        rw [hF] at hpq
        have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
        omega
      have hpodd : Odd p := hp.odd_of_ne_two hp2
      have h1 := hodd _ hy (by rw [hord]; exact hpodd)
      have h3 : p ∣ 2 ^ n - 1 := hord ▸ orderOf_dvd_of_pow_eq_one h1
      rw [hF] at hpq
      have h4 : p ∣ 2 := by
        have h5 := Nat.dvd_sub hpq h3
        rwa [show 2 ^ n + 1 - (2 ^ n - 1) = 2 by
          have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
          omega] at h5
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h4)
    have hcuts : borelOvergroupCuts Y' = {1, 2} := by
      ext i
      constructor
      · rintro ⟨hi, hin, -⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        omega
      · intro hi
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
        refine ⟨by omega, by omega, fun hr => key i (by omega) (by omega) hr⟩
    apply hcon
    have h1 := ((CFSG.QuasithinUnique.Setup.X7a.linear_unitriangular_overgroup_subflag_containment
      (n := 3) (K := F)).1 Y' hUY').1
    rwa [hcuts, ← CFSG.QuasithinUnique.Setup.X7a.upperTriangular_eq_flagStabilizer] at h1
  intro y hy
  rw [← hg, mem_normalizer_conjSubgroup, hP₀, normalizer_unitriangular]
  exact hY'B ((hmemY' _).mpr (by rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group]))

end CFSG.Quasithin.Vol2.KGNat
