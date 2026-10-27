module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartC
public import CFSG.Quasithin.Vol2.Ch5Sec1Hall
public import CFSG.Quasithin.Vol2.Ch11SecAKind
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidualLin

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open Matrix CFSG.Open CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem usl_eq_unitriangular : Usl K = unitriangular 3 K := by
  ext B
  constructor
  · rintro ⟨a, b, c, rfl⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp_all [coe_uSL, uMat]
    · fin_cases i <;> simp [coe_uSL, uMat]
  · rintro ⟨hlt, hd⟩
    refine ⟨(B : Matrix (Fin 3) (Fin 3) K) 0 1, (B : Matrix (Fin 3) (Fin 3) K) 0 2,
      (B : Matrix (Fin 3) (Fin 3) K) 1 2, Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_⟩
    have h10 := hlt 1 0 (by decide)
    have h20 := hlt 2 0 (by decide)
    have h21 := hlt 2 1 (by decide)
    have h0 := hd 0
    have h1 := hd 1
    have h2 := hd 2
    fin_cases i <;> fin_cases j <;> simp_all [coe_uSL, uMat]

theorem diagSL_eq_torus3 : CFSG.QuasithinUnique.Setup.X7a.diagSL 3 K = torus3 K := by
  ext d
  constructor
  · intro hd
    have hdg := (CFSG.QuasithinUnique.Setup.X7a.mem_diagSL.mp hd).diagonal_diag
    have hdet := d.2
    rw [← hdg, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
    have h0 : (d : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := fun h => by
      simp only [Matrix.diag_apply, h, zero_mul] at hdet
      exact zero_ne_one hdet
    have h1 : (d : Matrix (Fin 3) (Fin 3) K) 1 1 ≠ 0 := fun h => by
      simp only [Matrix.diag_apply, h, mul_zero, zero_mul] at hdet
      exact zero_ne_one hdet
    refine ⟨(Units.mk0 _ h0, Units.mk0 _ h1), Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_⟩
    rw [coe_tSL]
    conv_rhs => rw [← hdg]
    simp only [Matrix.diag_apply] at hdet
    fin_cases i <;> fin_cases j <;> simp [tvec]
    field_simp
    first | linear_combination hdet | linear_combination -hdet
  · rintro ⟨t, rfl⟩
    refine CFSG.QuasithinUnique.Setup.X7a.mem_diagSL.mpr ?_
    rw [coe_tSL]
    exact Matrix.isDiag_diagonal _

theorem unitriangular_inf_diagSL :
    unitriangular 3 K ⊓ CFSG.QuasithinUnique.Setup.X7a.diagSL 3 K = ⊥ := by
  rw [eq_bot_iff]
  rintro d ⟨⟨-, hd1⟩, hd⟩
  rw [Subgroup.mem_bot]
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_one]
  by_cases hij : i = j
  · subst hij
    rw [hd1 i, Matrix.one_apply_eq]
  · rw [CFSG.QuasithinUnique.Setup.X7a.mem_diagSL.mp hd hij, Matrix.one_apply_ne hij]

variable [Finite K] [CharP K 2]

theorem exists_conj_torus3_of_isHall {D : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (hD : CFSG.QuasithinUnique.Lin2.IsHallTwoPrimeOf D (upperTriangular 3 K)) :
    ∃ x ∈ unitriangular 3 K, D = (torus3 K).map (MulAut.conj x).toMonoidHom := by
  obtain ⟨hDB, hDodd, k, hk⟩ := hD
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
  have hU2 : IsPGroup 2 (unitriangular 3 K) := hP ▸ P.isPGroup'
  have hUB : unitriangular 3 K ≤ upperTriangular 3 K := unitriangular_le_upperTriangular 3 K
  have hBN : upperTriangular 3 K ≤
      Subgroup.normalizer (unitriangular 3 K : Set (SpecialLinearGroup (Fin 3) K)) :=
    (normalizer_unitriangular (n := 3) (K := K)).ge
  have hodd : Odd ((unitriangular 3 K).relIndex (upperTriangular 3 K)) := by
    have h1 : ¬ 2 ∣ (P : Subgroup (SpecialLinearGroup (Fin 3) K)).index := P.not_dvd_index
    rw [hP] at h1
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h =>
      h1 (h.trans (Subgroup.relIndex_dvd_index_of_le hUB)))
  have hT := CFSG.QuasithinUnique.Setup.X7a.diagSL_le_upperTriangular (n := 3) (K := K)
  have hUTs : unitriangular 3 K ⊔ CFSG.QuasithinUnique.Setup.X7a.diagSL 3 K =
      upperTriangular 3 K :=
    le_antisymm (sup_le hUB hT) CFSG.QuasithinUnique.Setup.X7a.upperTriangular_le_sup_diagSL
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hU2
  have hUD : unitriangular 3 K ⊓ D = ⊥ := (Subgroup.disjoint_of_coprime_natCard (by
    rw [hm]
    exact Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hDodd))).eq_bot
  have hcU := Subgroup.relIndex_mul_card (unitriangular 3 K) (upperTriangular 3 K)
  have hcD := Subgroup.relIndex_mul_card D (upperTriangular 3 K)
  rw [inf_of_le_left hUB, hm] at hcU
  rw [inf_of_le_left hDB, hk] at hcD
  have hmk : m = k := CFSG.Quasithin.Vol2.Ch11.SecA.eq_of_two_pow_mul_odd
    (m := (unitriangular 3 K).relIndex (upperTriangular 3 K)) (m' := Nat.card D) hodd hDodd
    (by rw [mul_comm, hcU, ← hcD])
  subst hmk
  have hB : Nat.card ↥(upperTriangular 3 K) = Nat.card ↥(unitriangular 3 K) * Nat.card D := by
    rw [hm, ← hcD]
  have hUDs : unitriangular 3 K ⊔ D = upperTriangular 3 K := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hUB hDB) ?_
    rw [hB]
    refine Nat.le_of_dvd Nat.card_pos (Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_
      (Subgroup.card_dvd_of_le le_sup_left) (Subgroup.card_dvd_of_le le_sup_right))
    rw [hm]
    exact Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hDodd)
  obtain ⟨x, hx, hxD⟩ := CFSG.Quasithin.H13.exists_mem_conj_of_complements hUB hBN hU2 hodd hT
    unitriangular_inf_diagSL hUTs hDB hUD hUDs
  exact ⟨x, hx, by rw [hxD, diagSL_eq_torus3]⟩

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
