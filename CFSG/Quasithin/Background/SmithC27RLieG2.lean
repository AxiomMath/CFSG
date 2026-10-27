module

public import CFSG.Quasithin.Background.SmithC27RLieBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ResidualG2
public import CFSG.Quasithin.Background.SmithB42G2Id

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley

theorem subgroupOf_covBy_subgroupOf {G : Type*} [Group G] {C A B : Subgroup G} (hA : A ≤ C)
    (hB : B ≤ C) (h : A ⋖ B) : A.subgroupOf C ⋖ B.subgroupOf C := by
  refine ⟨?_, fun D hAD hDB => ?_⟩
  · rw [← Subgroup.map_subtype_lt_map_subtype, Subgroup.map_subgroupOf_eq_of_le hA,
      Subgroup.map_subgroupOf_eq_of_le hB]
    exact h.lt
  · have h1 := Subgroup.map_subtype_lt_map_subtype.mpr hAD
    have h2 := Subgroup.map_subtype_lt_map_subtype.mpr hDB
    rw [Subgroup.map_subgroupOf_eq_of_le hA] at h1
    rw [Subgroup.map_subgroupOf_eq_of_le hB] at h2
    exact h.2 h1 h2

theorem maxParabolicMaximal_adjointGroupG2
    {K : Type} [Field K] [Finite K] [CharP K 2] :
    MaxParabolicMaximal (⊤ : Subgroup ↥(adjointGroup Tag.G2 K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hUC : posUnipotent Tag.G2 K ≤ adjointGroup Tag.G2 K := posUnipotent_le_adjointGroup
  have hBC : borelGroup Tag.G2 K ≤ adjointGroup Tag.G2 K :=
    (borelGroup_le_parabolicSubgroup ∅).trans (parabolicSubgroup_le_adjointGroup _ _ _)
  have hU₀ : IsSylowTwoOf ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) ⊤ :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_subgroupOf_top
      (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.2
        (CFSG.QuasithinUnique.Setup.X6.unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K)
          2).1)
  have hN : Subgroup.normalizer
      (((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) :
        Subgroup ↥(adjointGroup Tag.G2 K)) : Set ↥(adjointGroup Tag.G2 K)) =
      (borelGroup Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hUC, ← Subgroup.inf_subgroupOf_left,
      (borel_self_normalizers Tag.G2 K).1]
  have hres := CFSG.QuasithinUnique.Setup.X6.G2_residualOvergroupsAt (K := K)
  obtain ⟨hcov, -, -⟩ := exceptional_ordinary_minimal_Borel_intersections Tag.G2 K
  refine maxParabolicMaximal_top_of_sylow hU₀ fun M hNM hMt => ?_
  have hUM := Subgroup.le_normalizer.trans hNM
  rw [hN] at hNM ⊢
  obtain ⟨D, hD, hMD⟩ := exists_isCoatom_ge hMt
  obtain ⟨j, rfl⟩ := (hres.2.2.1 D (hUM.trans hMD)).mp (covBy_top_iff.mpr hD)
  have hPC := parabolicSubgroup_le_adjointGroup Tag.G2 K
    {CFSG.QuasithinUnique.Setup.X6.g2Index j}
  have hcj := (hcov _ hPC).2 ⟨_, rfl⟩
  rcases (subgroupOf_covBy_subgroupOf hBC hPC hcj).eq_or_eq hNM hMD with h | h
  · exact Or.inl h
  · exact Or.inr (h ▸ hD)

theorem nonempty_quasithinG2_mulEquiv_adjointGroup
    {K : Type} [Field K] [Finite K] {a : ℕ} (hK : Nat.card K = 2 ^ a) (ha : 2 ≤ a) :
    Nonempty (↥(quasithinG2 K) ≃* ↥(adjointGroup Tag.G2 K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq hK
  obtain ⟨e⟩ := B42G2Id.nonempty_quasithinG2_mulEquiv_adjointQuotient hK ha
  exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
    QuotientGroup.quotientBot)⟩

theorem maxParabolicMaximal_quasithinG2
    {K : Type} [Field K] [Finite K] {a : ℕ} (hK : Nat.card K = 2 ^ a) (ha : 2 ≤ a) :
    MaxParabolicMaximal (⊤ : Subgroup ↥(quasithinG2 K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq hK
  obtain ⟨e⟩ := nonempty_quasithinG2_mulEquiv_adjointGroup hK ha
  exact (maxParabolicMaximal_congr
    (Subgroup.topEquiv.trans (e.symm.trans Subgroup.topEquiv.symm))).mp
    maxParabolicMaximal_adjointGroupG2

theorem isRadicalParabolic_quasithinG2
    {K : Type} [Field K] [Finite K] {a : ℕ} (hK : Nat.card K = 2 ^ a) (ha : 2 ≤ a) :
    IsRadicalParabolic (⊤ : Subgroup ↥(quasithinG2 K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq hK
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  obtain ⟨e⟩ := B42G2Id.nonempty_quasithinG2_mulEquiv_adjointQuotient hK ha
  have : Finite ↥(quasithinG2 K) := Finite.of_equiv _ e.symm.toEquiv
  exact isRadicalParabolic_top_of_holds
    ((CFSG.LieType.BorelTits.holds_adjointQuotient Tag.G2 K 2).of_mulEquiv e.symm)

end CFSG.Quasithin.SmithC27
