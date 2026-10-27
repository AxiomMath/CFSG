module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aL3B

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X6 CFSG.LieType.SteinbergBR.BlockPar

variable {K : Type} [Field K] [Finite K]

theorem isPSL_projectiveSL (hK : Nat.card K = 4) : IsPSL 3 2 2 (projectiveSL 3 K) :=
  ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩, K, inferInstance,
    inferInstance, by rw [hK]; norm_num,
    ⟨(CFSG.QuasithinUnique.Setup.X7a.statedSLEquivProjectiveSL 3 K).symm⟩⟩

theorem isSimpleGroup_projectiveSL_four (hK : Nat.card K = 4) : IsSimpleGroup (projectiveSL 3 K) :=
  (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2 (isPSL_projectiveSL hK)).2

theorem isSylowTwoOf_projU [CharP K 2] :
    QuasithinUnique.IsSylowTwoOf (projUnitriangular 3 K) ⊤ := by
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  exact hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P

theorem residual_std [CharP K 2] (hK : Nat.card K = 4) :
    ResidualOvergroupsAt (projectiveSL 3 K) (projUnitriangular 3 K) (parab34 K) :=
  CFSG.QuasithinUnique.Setup.X7a.linear_three_residualOvergroupsAt ⟨2, by rw [hK]; norm_num⟩

theorem parab34_covBy [CharP K 2] (hK : Nat.card K = 4) (j : Fin 2) : parab34 K j ⋖ ⊤ :=
  ((residual_std hK).2.2.1 (parab34 K j) ((residual_std hK).2.1 j)).mpr ⟨j, rfl⟩

theorem dInf_parab34 [CharP K 2] (hK : Nat.card K = 4) (j : Fin 2) :
    dInf (parab34 K j) = parab34 K j := by
  have := isSimpleGroup_projectiveSL_four hK
  exact eq_of_le_of_card_eq_960 (card_projectiveSL_four hK) (dInf_le _) (parab34_covBy hK j).lt.ne
    (parab34_structure hK j).1

theorem parab34_perfect [CharP K 2] (hK : Nat.card K = 4) (j : Fin 2) :
    ⁅parab34 K j, parab34 K j⁆ = parab34 K j := by
  have h := Subgroup.isPerfect_iff.mp (dInf_isPerfect (parab34 K j))
  rwa [dInf_parab34 hK j] at h

theorem pCoreOf_parab34 [CharP K 2] (hK : Nat.card K = 4) (j : Fin 2) :
    pCoreOf 2 (parab34 K j) = (radU K (flagSpace 3 K ((j : ℕ) + 1))).map (proj 3 K) := by
  have hd : 1 ≤ (j : ℕ) + 1 := by omega
  have hdn : (j : ℕ) + 1 < 3 := by omega
  have hF : Even (Nat.card K) := by rw [hK]; decide
  have hW := finrank_flagSpace (n := 3) (K := K) (i := (j : ℕ) + 1) hdn.le
  obtain ⟨-, -, hrad, hpcore, hsolv, -⟩ :=
    CFSG.LieType.linear_small_parabolic_perfect_residual_structure hF hd hdn
      (Or.inl ⟨rfl, hK.ge⟩) (flagSpace 3 K ((j : ℕ) + 1)) hW (P := parab34 K j)
      (B := dInf (parab34 K j)) rfl rfl
  rw [← dInf_parab34 hK j, pCoreOf, hpcore,
    hsolv, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hrad]

theorem classify_std [CharP K 2] (hK : Nat.card K = 4) (X : Subgroup (projectiveSL 3 K))
    (hX1 : X ≠ ⊥) (hXp : ⁅X, X⁆ = X)
    (hSX : projUnitriangular 3 K ≤ Subgroup.normalizer (X : Set (projectiveSL 3 K))) :
    X = parab34 K 0 ∨ X = parab34 K 1 ∨ X = ⊤ := by
  have hsimp := isSimpleGroup_projectiveSL_four hK
  obtain ⟨-, -, -, -, hC2, -⟩ := residual_std hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSs : Group.IsSolvable ↥(projUnitriangular 3 K) := by
    have := (isSylowTwoOf_projU (K := K)).2.1.isNilpotent
    infer_instance
  have hcore : perfectCore (X ⊔ projUnitriangular 3 K) = X := perfectCore_sup_eq hXp hSs hSX
  by_cases htop : X ⊔ projUnitriangular 3 K = ⊤
  · right; right
    have hXn : X.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
      exact sup_le Subgroup.le_normalizer hSX
    exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal X).resolve_left hX1
  · have hns : ¬ Group.IsSolvable ↥(X ⊔ projUnitriangular 3 K) := by
      intro hsol
      have hXs : Group.IsSolvable ↥X :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion le_sup_left)
          (Subgroup.inclusion_injective (le_sup_left : X ≤ X ⊔ projUnitriangular 3 K))
      apply hX1
      rw [← perfectCore_eq_self_of_perfect hXp]
      exact (isSolvable_iff_perfectCore_eq_bot X).mp hXs
    obtain ⟨j, -, hdj⟩ := hC2 (X ⊔ projUnitriangular 3 K) le_sup_right htop hns
    rw [CFSG.QuasithinUnique.Vol2Native.A312L.dInf_eq_perfectCore, hcore, dInf_parab34 hK j]
      at hdj
    fin_cases j
    · exact Or.inl hdj
    · exact Or.inr (Or.inl hdj)

theorem commutator_top_projectiveSL [CharP K 2] (hK : Nat.card K = 4) :
    ⁅(⊤ : Subgroup (projectiveSL 3 K)), (⊤ : Subgroup (projectiveSL 3 K))⁆ = ⊤ := by
  have hsimp := isSimpleGroup_projectiveSL_four hK
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ⁅(⊤ : Subgroup (projectiveSL 3 K)), (⊤ : Subgroup (projectiveSL 3 K))⁆ with h | h
  · exfalso
    have h1 : parab34 K 0 = ⊥ := by
      rw [← parab34_perfect hK 0, ← le_bot_iff, ← h]
      exact Subgroup.commutator_mono le_top le_top
    have h2 := (parab34_structure hK 0).1
    rw [dInf_parab34 hK 0, h1, Subgroup.card_bot] at h2
    norm_num at h2
  · exact h

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
