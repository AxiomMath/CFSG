module

public import CFSG.Quasithin.Background.SmithC27RLieBasic
public import CFSG.Quasithin.EmptyFaithful.SzN2Sp

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a

variable {K : Type} [Field K] [Finite K] {a : ℕ}

noncomputable def topSLEquivStatedSL (n : ℕ) (K : Type) [Field K] :
    ↥(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin n) K)) ≃* ↥(⊤ : Subgroup ↥(StatedSL n K)) :=
  Subgroup.topEquiv.trans ((specialLinearGroupEquivStatedSL n K).trans Subgroup.topEquiv.symm)

theorem isRadicalParabolic_statedSL (d : ℕ) (hK : Nat.card K = 2 ^ a) :
    IsRadicalParabolic (⊤ : Subgroup ↥(StatedSL d K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq hK
  exact isRadicalParabolic_top_of_holds (CFSG.LieType.BorelTits.holds_statedSL d K 2)

theorem isRadicalParabolic_statedSp (hK : Nat.card K = 2 ^ a) :
    IsRadicalParabolic (⊤ : Subgroup ↥(StatedSp 2 K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq hK
  exact isRadicalParabolic_top_of_holds (CFSG.LieType.BorelTits.holds_statedSp 2 K 2)

theorem sl3_borel_overgroup (hK : Nat.card K = 2 ^ a)
    (M : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K))
    (hNM : Subgroup.normalizer
      ((unitriangular 3 K : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)) :
        Set (Matrix.SpecialLinearGroup (Fin 3) K)) ≤ M) (hMt : M ≠ ⊤) :
    M = Subgroup.normalizer
      ((unitriangular 3 K : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)) :
        Set (Matrix.SpecialLinearGroup (Fin 3) K)) ∨ IsCoatom M := by
  rw [normalizer_unitriangular] at hNM ⊢
  obtain ⟨C, hC, hMC⟩ := exists_isCoatom_ge hMt
  have hUC : unitriangular 3 K ≤ C :=
    ((unitriangular_le_upperTriangular 3 K).trans hNM).trans hMC
  obtain ⟨j, rfl⟩ :=
    ((SzN2.sl3_residualOvergroupsAt ⟨a, hK⟩).2.2.1 C hUC).mp (covBy_top_iff.mpr hC)
  rcases (covBy_Q3 j).eq_or_eq hNM hMC with h | h
  · exact Or.inl h
  · exact Or.inr (h ▸ hC)

theorem maxParabolicMaximal_statedSL_three (hK : Nat.card K = 2 ^ a) :
    MaxParabolicMaximal (⊤ : Subgroup ↥(StatedSL 3 K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq hK
  rw [← maxParabolicMaximal_congr (topSLEquivStatedSL 3 K)]
  exact maxParabolicMaximal_top_of_sylow (SzN2.isSylowTwoOf_unitriangular (by norm_num))
    (sl3_borel_overgroup hK)

theorem sp4_borel_overgroup (hK : Nat.card K = 2 ^ a) (M : Subgroup ↥(StatedSp 2 K))
    (hNM : Subgroup.normalizer
      ((SymplecticFlag.unipotent 2 K : Subgroup ↥(StatedSp 2 K)) : Set ↥(StatedSp 2 K)) ≤ M)
    (hMt : M ≠ ⊤) :
    M = Subgroup.normalizer
      ((SymplecticFlag.unipotent 2 K : Subgroup ↥(StatedSp 2 K)) : Set ↥(StatedSp 2 K)) ∨
      IsCoatom M := by
  rw [SymplecticHigher.normalizer_unipotent] at hNM ⊢
  obtain ⟨C, hC, hMC⟩ := exists_isCoatom_ge hMt
  have hUC : SymplecticFlag.unipotent 2 K ≤ C :=
    (SymplecticFlag.unipotent_le_borelSubgroup.trans hNM).trans hMC
  obtain ⟨j, rfl⟩ :=
    ((SzN2.sp4_residualOvergroupsAt ⟨a, hK⟩).2.2.1 C hUC).mp (covBy_top_iff.mpr hC)
  rcases (covBy_Q2 j).eq_or_eq hNM hMC with h | h
  · exact Or.inl h
  · exact Or.inr (h ▸ hC)

theorem maxParabolicMaximal_statedSp (hK : Nat.card K = 2 ^ a) :
    MaxParabolicMaximal (⊤ : Subgroup ↥(StatedSp 2 K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq hK
  exact maxParabolicMaximal_top_of_sylow SzN2.isSylowTwoOf_unipotent (sp4_borel_overgroup hK)

theorem sl2_le_normalizer_of_unitriangular_le {F : Type} [Field F]
    {M : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)} (hUM : unitriangular 2 F ≤ M)
    (hMt : M ≠ ⊤) :
    M ≤ Subgroup.normalizer
      ((unitriangular 2 F : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) :
        Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
  rw [normalizer_unitriangular]
  obtain ⟨hle, hiff⟩ :=
    (linear_unitriangular_overgroup_subflag_containment (n := 2) (K := F)).1 M hUM
  refine SzN2.le_upperTriangular_of_cuts hle fun i hi1 hin => ?_
  have hi : i = 1 := by omega
  subst hi
  by_contra h1
  refine hMt (hiff.mp (Set.eq_empty_of_forall_notMem fun j hj => ?_))
  obtain ⟨hj1, hjn, -⟩ := id hj
  have hj' : j = 1 := by omega
  subst hj'
  exact h1 hj

theorem parabolicIsBorel_statedSL_two (hK : Nat.card K = 2 ^ a) :
    ParabolicIsBorel (⊤ : Subgroup ↥(StatedSL 2 K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq hK
  rw [← parabolicIsBorel_congr (topSLEquivStatedSL 2 K)]
  exact parabolicIsBorel_top_of_sylow (SzN2.isSylowTwoOf_unitriangular (by norm_num))
    fun M hUM hMt => sl2_le_normalizer_of_unitriangular_le hUM hMt

end CFSG.Quasithin.SmithC27
