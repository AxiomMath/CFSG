module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p20a_exists_max_ge {H : Subgroup G} (hH : IsTwoLocal H) :
    ∃ N : Subgroup G, rankThreeIsMaxTwoLocal N ∧ H ≤ N := by
  haveI : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
  haveI : WellFoundedGT (Subgroup G) := Finite.to_wellFoundedGT
  obtain ⟨N, hge, hmax⟩ :=
    exists_maximal_ge_of_wellFoundedGT (fun K : Subgroup G => IsTwoLocal K) H hH
  exact ⟨N, ⟨hmax.1, fun K hK hle => le_antisymm (hmax.2 hK hle) hle⟩, hge⟩

theorem uc22p20a_M_ne_top (D : Data G) : D.M ≠ ⊤ := by
  haveI := D.standing.simple
  exact CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab D.maxLocal.1

theorem uc22p20a_pCoreOf_ne_bot {T M H : Subgroup G} (hH : H ∈ hSet T M) : pCoreOf 2 H ≠ ⊥ := by
  intro h
  apply hH.2.1
  intro x hx
  have hx' : x ∈ H ⊓ centralizer (pCoreOf 2 H : Set G) := by
    refine ⟨hx, mem_centralizer_iff.2 fun g hg => ?_⟩
    rw [h] at hg
    have hg1 : g = 1 := Subgroup.mem_bot.1 hg
    rw [hg1]
    simp
  have h1 := hH.2.2 hx'
  rw [h] at h1
  have hx1 : x = 1 := Subgroup.mem_bot.1 h1
  rw [hx1]
  exact M.one_mem

theorem uc22p20a_exists_mem_calMOf (D : Data G) {H : Subgroup G} (hH : H ∈ hSet D.T D.M) :
    ∃ N : Subgroup G, N ∈ calMOf D.T ∧ H ≤ N := by
  have hloc : IsTwoLocal (normalizer (pCoreOf 2 H : Set G)) :=
    ⟨pCoreOf 2 H, uc22p20a_pCoreOf_ne_bot hH, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H, rfl⟩
  have hHle : H ≤ normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  obtain ⟨N, hN, hge⟩ := uc22p20a_exists_max_ge hloc
  exact ⟨N, ⟨hN, hH.1.trans (hHle.trans hge)⟩, hHle.trans hge⟩

theorem s20_1_12 (D : Data G) (h66 : UC6.R6_6 D) :
    ∀ H ∈ hSet D.T D.M, CFSG.Open.pRank 3 H ≤ 3 ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 → 3 < CFSG.Open.pRank p H →
        CFSG.Open.pRank p (H ⊓ D.M) ≤ 1) := by
  intro H hH
  obtain ⟨N, hN, hHN⟩ := uc22p20a_exists_mem_calMOf D hH
  have hnotM : ¬ H ≤ D.M := hH.2.1
  refine ⟨?_, fun p hp hp2 h4 => ?_⟩
  · by_contra h
    have h4 : 3 < CFSG.Open.pRank 3 H := by omega
    have h4' : 4 ≤ CFSG.Open.pRank 3 N := by
      have := CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three hHN
      omega
    exact hnotM (((h66 3 Nat.prime_three (by norm_num)).2.2 rfl N hN h4') ▸ hHN)
  · by_contra h
    have h4' : 4 ≤ CFSG.Open.pRank p N := by
      have := CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp hHN
      omega
    have h2 : 2 ≤ CFSG.Open.pRank p (D.M ⊓ N) := by
      have := CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp
        (le_inf inf_le_right (inf_le_left.trans hHN) : H ⊓ D.M ≤ D.M ⊓ N)
      omega
    exact hnotM (((h66 p hp hp2).2.1 N hN.1 h4' h2) ▸ hHN)

@[expose] def ListBNonabelian : Prop :=
  ∀ (L : Type) [Group L], Asc1930ListB L → ∃ a b : L, a * b ≠ b * a

theorem uc22p20a_le_normalizer_oinf (H : Subgroup G) : H ≤ normalizer (OInf H : Set G) := by
  have hle : OInf H ≤ H := Subgroup.map_subtype_le _
  rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  have h : (OInf H).subgroupOf H = CFSG.solvableRadical ↥H := by
    unfold OInf
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  rw [h]
  exact CFSG.SignalizerFunctorTheorem.Nonsolvable.instNormalSolvableRadical

theorem uc22p20a_isSolvable_oinf (H : Subgroup G) : Group.IsSolvable ↥(OInf H) := by
  haveI : Group.IsSolvable ↥(CFSG.solvableRadical ↥H) :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  exact CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_of_mulEquiv
    (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective)

theorem uc22p20a_pCoreOf_le_oinf (H : Subgroup G) : pCoreOf 2 H ≤ OInf H := by
  have hp : IsPGroup 2 ↥(CFSG.pCore 2 ↥H) := CFSG.pCore_isPGroup
  haveI : Group.IsNilpotent ↥(CFSG.pCore 2 ↥H) := hp.isNilpotent
  exact Subgroup.map_mono (CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical
    (CFSG.pCore_normal (p := 2) (G := ↥H)) inferInstance)

theorem uc22p20a_isSolvable_sup (H T : Subgroup G) (hTH : T ≤ H) (hT : IsPGroup 2 T) :
    Group.IsSolvable ↥(OInf H ⊔ T) := by
  have hSH : OInf H ≤ H := Subgroup.map_subtype_le _
  have hHn : H ≤ normalizer (OInf H : Set G) := uc22p20a_le_normalizer_oinf H
  have hTn : T ≤ normalizer (OInf H : Set G) := hTH.trans hHn
  have hLH : OInf H ⊔ T ≤ H := sup_le hSH hTH
  have hM : (( OInf H).subgroupOf (OInf H ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 (hLH.trans hHn)
  haveI := hM
  haveI hS : Group.IsSolvable ↥(OInf H) := uc22p20a_isSolvable_oinf H
  haveI hMs : Group.IsSolvable ↥((OInf H).subgroupOf (OInf H ⊔ T)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (le_sup_left : OInf H ≤ OInf H ⊔ T)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe le_sup_left).injective
  haveI hTs : Group.IsSolvable ↥T := by
    haveI : Group.IsNilpotent ↥T := hT.isNilpotent
    infer_instance
  let f : ↥T →* ↥(OInf H ⊔ T) ⧸ (OInf H).subgroupOf (OInf H ⊔ T) :=
    (QuotientGroup.mk' ((OInf H).subgroupOf (OInf H ⊔ T))).comp
      (Subgroup.inclusion (le_sup_right : T ≤ OInf H ⊔ T))
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective ((OInf H).subgroupOf (OInf H ⊔ T)) y
    have hx' : x ∈ ((OInf H ⊔ T : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left (OInf H) T hTn] at hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [f, MonoidHom.comp_apply]
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hb' : b⁻¹ * a * b ∈ OInf H := (mem_normalizer_iff''.1 (hTn hb) a).1 ha
    simpa [mul_assoc] using hb'
  haveI : Group.IsSolvable (↥(OInf H ⊔ T) ⧸ (OInf H).subgroupOf (OInf H ⊔ T)) :=
    Group.isSolvable_of_surjective hf
  exact Group.isSolvable_of_subgroup_quotient ((OInf H).subgroupOf (OInf H ⊔ T))

theorem uc22p20a_abelian_of_compositionFactor {X L : Type} [Group X] [Group L] [Finite X]
    (hX : Group.IsSolvable X) (h : CFSG.Quasithin.E1.IsCompositionFactor X L) :
    ∀ a b : L, a * b = b * a := by
  obtain ⟨N, M, hNM, -, -, -, hsimple, ⟨e⟩⟩ := h
  haveI := hNM
  haveI := hsimple
  haveI := hX
  have hs : Group.IsSolvable (↥M ⧸ N.subgroupOf M) := inferInstance
  have hcomm : ∀ a b : ↥M ⧸ N.subgroupOf M, a * b = b * a :=
    IsSimpleGroup.comm_iff_isSolvable.2 hs
  intro a b
  apply e.symm.injective
  rw [map_mul, map_mul]
  exact hcomm _ _

theorem uc22p20a_oinf_sup_mem_hSet {T M H : Subgroup G} (hH : H ∈ hSet T M)
    (hnot : ¬ OInf H ≤ M) : OInf H ⊔ T ∈ hSet T M := by
  have hSH : OInf H ≤ H := Subgroup.map_subtype_le _
  have hH1H : OInf H ⊔ T ≤ H := sup_le hSH hH.1
  refine ⟨le_sup_right, fun h => hnot (le_sup_left.trans h), ?_⟩
  have hP : pCoreOf 2 H ≤ pCoreOf 2 (OInf H ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((uc22p20a_pCoreOf_le_oinf H).trans le_sup_left)
      (hH1H.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
  intro x hx
  have hx1 : x ∈ H := hH1H hx.1
  have hx2 : x ∈ centralizer (pCoreOf 2 H : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hP) hx.2
  exact hP (hH.2.2 ⟨hx1, hx2⟩)

theorem uc22p20a_oinf_le (D : Data G) (hB : ListBNonabelian) (h1930 : H1930 D) {H : Subgroup G}
    (hH : H ∈ hSet D.T D.M) : OInf H ≤ D.M := by
  by_contra hnot
  have hmem := uc22p20a_oinf_sup_mem_hSet hH hnot
  obtain ⟨L, _, hL, hLB⟩ := (h1930 _ hmem).1
  obtain ⟨a, b, hab⟩ := hB L hLB
  exact hab (uc22p20a_abelian_of_compositionFactor
    (uc22p20a_isSolvable_sup H D.T hH.1 D.sylowM.isPGroup) hL a b)

@[expose] def S20_1_124 (D : Data G) : Prop :=
  H1930 D → ∀ H ∈ hSet D.T D.M,
    CFSG.Open.pRank 3 H ≤ 3 ∧
    (∀ p : ℕ, p.Prime → p ≠ 2 → 3 < CFSG.Open.pRank p H → CFSG.Open.pRank p (H ⊓ D.M) ≤ 1) ∧
    OInf H ≤ D.M

theorem s20_1_124 (D : Data G) (h66 : UC6.R6_6 D) (hB : ListBNonabelian) : S20_1_124 D := by
  intro h1930 H hH
  obtain ⟨h1, h2⟩ := s20_1_12 D h66 H hH
  exact ⟨h1, h2, uc22p20a_oinf_le D hB h1930 hH⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
