module

public import CFSG.RankThree.PartOne.S12.Assembly
public import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.RankThree.PartOne.S10.ThetaNodesUnconditional
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.RankThree.PartOne.S10.Defs

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.LocalAnalysis.ComponentInitial

@[expose] def Sec11OneIndeed : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G), SteinbergBM.SectionTenSetup G p A →
    ∀ L ∈ sectionTenZeroStar p A ∩ sectionTenTwo p A,
      ∃ K ∈ sectionTenZeroStar p A ∩ sectionTenOne p A, A ⊓ L ≤ K

variable {G : Type} [Group G] [Finite G]

theorem exists_star_above (hS : SchreierFor InCatalog) {p : ℕ} {A : Subgroup G}
    (h : SteinbergBM.SectionTenSetup G p A) {L : Subgroup G}
    (hL : L ∈ thetaComponentFamily p A) :
    ∃ M ∈ sectionTenStar p A, sectionTenRel p L M := by
  classical
  have hfin : (thetaComponentFamily p A).Finite := Set.toFinite _
  have hp := sectionTenSetup_prime h
  have hp3 := sectionTenSetup_three_lt h
  have : IsSimpleGroup G := h.1
  have htrans : ∀ X ∈ thetaComponentFamily p A, ∀ Y ∈ thetaComponentFamily p A,
      ∀ Z ∈ thetaComponentFamily p A, sectionTenRel p X Y → sectionTenRel p Y Z →
        sectionTenRel p X Z := fun X hX Y hY Z hZ hXY hYZ =>
    section_ten_component_supplement_transitivity hS G h.2.1 h.2.2.1
      (sectionTenSetup_evenRank_eq h).le p hp hp3 A h.2.2.2.2.2.2.1 X hX Y hY Z hZ hXY hYZ
  let U : Subgroup G → Set (Subgroup G) := fun K =>
    {J | J ∈ thetaComponentFamily p A ∧ sectionTenRel p K J}
  have hUfin : ∀ K, (U K).Finite := fun K => hfin.subset fun J hJ => hJ.1
  let S : Set (Subgroup G) := {K | K ∈ thetaComponentFamily p A ∧ sectionTenRel p L K}
  have hSne : S.Nonempty := ⟨L, hL, sectionTenRel_refl p L⟩
  obtain ⟨K, hKS, hKmin⟩ := Set.exists_min_image S (fun K => (hUfin K).toFinset.card)
    (hfin.subset fun J hJ => hJ.1) hSne
  refine ⟨K, ⟨hKS.1, fun J hJ hKJ => ?_⟩, hKS.2⟩
  by_contra hJK
  have hJS : J ∈ S := ⟨hJ, htrans L hL K hKS.1 J hJ hKS.2 hKJ⟩
  have hsub : U J ⊆ U K := fun X hX =>
    ⟨hX.1, htrans K hKS.1 J hJ X hX.1 hKJ hX.2⟩
  have hKnot : K ∈ U K := ⟨hKS.1, sectionTenRel_refl p K⟩
  have hKnotJ : K ∉ U J := fun hK => hJK hK.2
  have hlt : (hUfin J).toFinset.card < (hUfin K).toFinset.card := by
    apply Finset.card_lt_card
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [Set.Finite.mem_toFinset] at hx ⊢
      exact hsub hx
    · intro hcon
      have : K ∈ (hUfin J).toFinset := hcon (by rw [Set.Finite.mem_toFinset]; exact hKnot)
      rw [Set.Finite.mem_toFinset] at this
      exact hKnotJ this
  exact absurd (hKmin J hJS) (not_le.mpr hlt)

theorem exists_zeroStar_above_of_zero (hS : SchreierFor InCatalog) {p : ℕ} {A : Subgroup G}
    (h : SteinbergBM.SectionTenSetup G p A) {L : Subgroup G} (hL : L ∈ sectionTenZero p A) :
    ∃ M ∈ sectionTenZeroStar p A, sectionTenRel p L M := by
  obtain ⟨M, hMstar, hLM⟩ := exists_star_above hS h hL.1
  refine ⟨M, ⟨?_, hMstar⟩, hLM⟩
  exact section_ten_moving_two_stratum_upward_closure G (sectionTenSetup_evenRank_eq h).le p
    (sectionTenSetup_prime h) (sectionTenSetup_three_lt h) (sectionTenSetup_vanishing h) A
    h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1 L hL.1 M hMstar.1 hLM hL

theorem sec11One_of_indeed (hS : SchreierFor InCatalog) (h105 : InSec10FivePlus)
    (hindeed : Sec11OneIndeed) : Sec11One := by
  intro G _ _ p A h
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hA : A = ⊥ := (Subgroup.eq_bot_iff_forall A).mpr hcon
    have hcard := h.2.2.2.2.2.2.2.1
    rw [hA, Subgroup.card_bot] at hcard
    have hp := sectionTenSetup_prime h
    have : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  obtain ⟨L, hL0, -⟩ := h105 G p A h a haA ha1
  obtain ⟨M, hM0, -⟩ := exists_zeroStar_above_of_zero hS h hL0
  by_cases hM1 : M ∈ sectionTenOne p A
  · exact ⟨M, hM0, hM1⟩
  · have hM2 : M ∈ sectionTenTwo p A := ⟨(sectionTenZeroStar_subset p A).2.2.1 hM0.2, hM1⟩
    obtain ⟨K, hK, -⟩ := hindeed G p A h M ⟨hM0, hM2⟩
    exact ⟨K, hK.1, hK.2⟩

end CFSG.RankThree.PartOne
