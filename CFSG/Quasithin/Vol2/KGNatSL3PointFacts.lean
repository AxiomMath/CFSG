module

public import CFSG.Quasithin.Vol2.KGNatSL3Point
public import CFSG.Quasithin.Vol2.Ch11SecAFacts11
public import CFSG.Quasithin.Vol2.Ch11SecAFacts15

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL
  specialLinearGroupEquivStatedSL_coe)
open CFSG.LieType.SteinbergBR CFSG.LieType.SteinbergBR.BlockPar
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K]

theorem commutator_SL2_eq_top [Finite K] (h4 : 4 ≤ Nat.card K) :
    commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤ := by
  have := Fintype.ofFinite K
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
  exact (CFSG.LinearGroups.special_linear_dimension_two_perfect ⟨s, hs⟩).commutator_eq_top

omit [Field K] in
theorem four_le_card {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) : 4 ≤ Nat.card K := by
  rw [hK]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem uMat_mulVec_e0 (a b c : K) : uMat a b c *ᵥ ![1, 0, 0] = ![1, 0, 0] := by
  rw [uMat_mulVec]
  exact vec3_eq (by simp) (by simp) (by simp)

theorem gconj_mulVec (g B : Matrix.SpecialLinearGroup (Fin 3) K) (x : Fin 3 → K) :
    ((g * B * g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x =
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x)) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]

theorem g_ginv_mulVec (g : Matrix.SpecialLinearGroup (Fin 3) K) (x : Fin 3 → K) :
    (g : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem ginv_g_mulVec (g : Matrix.SpecialLinearGroup (Fin 3) K) (x : Fin 3 → K) :
    ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem factPointSL3_holds : Ch11.SecA.FactPointSL3 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP U hU
  have hSL := commutator_SL2_eq_top (four_le_card hn hK)
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf hP
  rw [← hK] at hU
  rw [eq_U1_of_isFlagW hW hf hg hU]
  intro h hh u hu
  obtain ⟨B, hB, rfl⟩ := (mem_perfectCore_HU1_iff hSL hf g h).mp hh
  have hu' : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f u ∈
      flagSpace 3 K 1 := mem_gmap.mp hu
  rw [← hf.ker, hf.map_mul_inv, hf.act3, gconj_mulVec, mulVec_eq_of_fix_e0 hB hu',
    g_ginv_mulVec, sub_self]

theorem factSylowLeviSL3_holds : Ch11.SecA.FactSylowLeviSL3 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP U hU
  have hSL := commutator_SL2_eq_top (four_le_card hn hK)
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf hP
  rw [← hK] at hU
  rw [eq_U1_of_isFlagW hW hf hg hU]
  intro x hx
  rw [mem_perfectCore_HU1_iff hSL hf g]
  obtain ⟨u, ⟨a, b, c, rfl⟩, rfl⟩ := (hg x).mp hx
  exact ⟨uSL a b c, uMat_mulVec_e0 a b c, rfl⟩

theorem factPointCentralizerSL3_holds : Ch11.SecA.FactPointCentralizerSL3 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP U hU h hh hfix
  have hSL := commutator_SL2_eq_top (four_le_card hn hK)
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf hP
  rw [← hK] at hU
  rw [eq_U1_of_isFlagW hW hf hg hU] at hfix ⊢
  rw [mem_perfectCore_HU1_iff hSL hf g]
  obtain ⟨A, hA⟩ := (rho3_bijective hf).2 ⟨h, hh⟩
  have hhA : h = ((rho3 π A : ↥H) : MulAut W) := by rw [hA]
  obtain ⟨u, hu⟩ := hf.surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0])
  have hu1 : u ∈ hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup := by
    show f u ∈ gmap g _
    rw [mem_gmap, hu, ginv_g_mulVec, ← stdLine_eq_flagSpace]
    exact ⟨rfl, rfl⟩
  have h1 := hfix u hu1
  rw [← hf.ker, hf.map_mul_inv, hhA, hf.act3, hu, sub_eq_zero] at h1
  refine ⟨g⁻¹ * A * g, ?_, ?_⟩
  · rw [← mulVec_gconj, h1, ginv_g_mulVec]
  · rw [hhA, show g * (g⁻¹ * A * g) * g⁻¹ = A by group]

end CFSG.Quasithin.Vol2.KGNat
