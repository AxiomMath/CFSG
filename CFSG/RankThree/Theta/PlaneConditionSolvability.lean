module

public import CFSG.RankThree.Theta.SignalizerCompleteness
public import CFSG.RankThree.Theta.CompletionCentralizers
public import CFSG.RankThree.Coprime.ThetaCentralizerSignalizer
public import CFSG.RankThree.LocalRank.ThetaPlaneCentralLine
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.RankThree.Theta

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThreeEvenClassification.Helpers

variable {X : Type*} [Group X] [Finite X]

theorem raw_plane_containment_of_central_line {p : ℕ} (hp : p.Prime) (A : Subgroup X)
    (hA : CFSG.Assembly.IsElemAbelian p A) (hAcard : Nat.card A = p ^ 3) {a : X} (ha : a ∈ A)
    (ha1 : a ≠ 1)
    (hq : thetaAlpha p ((A.subgroupOf (centralizer ({a} : Set X))).map
        (QuotientGroup.mk' (centralLine a))) ≤
      aschbacherSolvableCore p (centralizer ({a} : Set X) ⧸ centralLine a))
    {E : Subgroup X} (hE : E ≤ A) (hEcard : Nat.card E = p ^ 2) :
    thetaPlaneAlpha p (E.subgroupOf (centralizer ({a} : Set X))) ≤
      solvablePrimeComplementCore (centralizer ({a} : Set X)) p := by
  have : Fact p.Prime := ⟨hp⟩
  have hAC := commutative_plane_le_element_centralizer A hA.1 a ha
  have hkerLe : (QuotientGroup.mk' (centralLine a)).ker ≤
      A.subgroupOf (centralizer ({a} : Set X)) := by
    rw [QuotientGroup.ker_mk']
    exact zpowers_le.mpr (mem_subgroupOf.mpr ha)
  have hkerCard : Nat.card (QuotientGroup.mk' (centralLine a)).ker = p := by
    rw [QuotientGroup.ker_mk', centralLine, Nat.card_zpowers, orderOf_mk]
    exact orderOf_eq_prime (hA.2 a ha) ha1
  have hactorCard : Nat.card (A.subgroupOf (centralizer ({a} : Set X))) = p ^ 3 := by
    rw [← hAcard]
    exact Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv
  have hcentral : (QuotientGroup.mk' (centralLine a)).ker ≤
      center (centralizer ({a} : Set X)) := by
    rw [QuotientGroup.ker_mk']
    exact centralLine_le_center a
  have hplaneLe : E.subgroupOf (centralizer ({a} : Set X)) ≤
      A.subgroupOf (centralizer ({a} : Set X)) := fun x hx =>
    mem_subgroupOf.mpr (hE (mem_subgroupOf.mp hx))
  have hcomm : IsMulCommutative (E.subgroupOf (centralizer ({a} : Set X))) :=
    elementary_plane_commutative_of_le p _ _
      (isElemAbelian_subgroupOf p A (centralizer ({a} : Set X)) hA) hplaneLe
  have hplaneCard : Nat.card (E.subgroupOf (centralizer ({a} : Set X))) = p ^ 2 := by
    rw [← hEcard]
    exact Nat.card_congr (subgroupOfEquivOfLe (hE.trans hAC)).toEquiv
  rw [thetaAlpha_eq_thetaPlaneAlpha hp,
    aschbacherSolvableCore_eq_solvablePrimeComplementCore hp] at hq
  exact thetaPlaneAlpha_le_of_rank_three_quotient_actor p hp _ (QuotientGroup.mk'_surjective _)
    hcentral hkerCard _ _ hplaneLe hkerLe hcomm hplaneCard hactorCard hq

theorem thetaPlaneAlpha_le_of_raw_local {p : ℕ} (hp : p.Prime) (A : Subgroup X)
    (hab : CFSG.Open.IsElemAbelian p A) {B D : Subgroup X} (hBA : B ≤ A) (hDA : D ≤ A)
    (hB : Nat.card B = p ^ 2) (hD : Nat.card D = p ^ 2)
    (hmixed : ∀ first ∈ A, first ≠ 1 → ∀ second ∈ A, second ≠ 1 →
      ⁅centralizer ({second} : Set X) ⊓ thetaCoreOf p (centralizer ({first} : Set X)), A⁆ ≤
        thetaCoreOf p (centralizer ({second} : Set X)))
    (hlocal : ∀ d ∈ D, d ∉ B → thetaPlaneAlpha p (B.subgroupOf (centralizer ({d} : Set X))) ≤
      solvablePrimeComplementCore (centralizer ({d} : Set X)) p) :
    thetaPlaneAlpha p B ≤ thetaPlaneAlpha p D := by
  have hDpow : ∀ member : D, member ^ p = 1 :=
    fun member => Subtype.ext (hab.2 member (hDA member.property))
  have hnontrivial : B ≠ ⊥ := by
    intro heq
    have hone := card_eq_one.mpr heq
    rw [hB] at hone
    nlinarith [hp.two_le]
  obtain ⟨element, hne⟩ := ne_bot_iff_exists_ne_one.mp hnontrivial
  have hneX : (element : X) ≠ 1 := fun heq => hne (Subtype.ext heq)
  apply sup_le
  · refine iSup_le fun member => iSup_le fun hmember => iSup_le fun hmemberNe => ?_
    exact thetaPlaneCommutator_le_other_alpha_of_mixed p hp A B D hab.1 hBA hDA hB hDpow hD hmixed
      member hmember hmemberNe
  · apply thetaPlaneIntersection_le_alpha_of_fixed_theta p hp A B D hab.1 hBA hDA hDpow hD
      element element.property hneX
    intro member hmember hmemberNe
    by_cases hmemberB : member ∈ B
    · exact inf_le_left.trans (thetaPlaneIntersection_le p B member hmemberB hmemberNe)
    · exact thetaPlaneIntersection_fixed_le_element_theta_of_local p hp B member
        (hlocal member hmember hmemberB)

theorem part_two_plane_condition_solvability_and_comparison (A : Subgroup X)
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hAcard : Nat.card A = 27)
    (hplane : ∀ E : Subgroup X, E ≤ A → Nat.card E = 9 → ∀ e ∈ E, e ≠ 1 →
      ⁅inSubgroup (aschbacherSolvableCore 3) (centralizer (E : Set X)), A⁆ ≤
        inSubgroup (aschbacherSolvableCore 3) (centralizer ({e} : Set X)))
    {B D : Subgroup X} (hBA : B ≤ A) (hB : Nat.card B = 9) (hDA : D ≤ A)
    (hD : Nat.card D = 9) :
    Group.IsSolvable (thetaAlpha 3 B) ∧ Nat.Coprime 3 (Nat.card (thetaAlpha 3 B)) ∧
      (thetaAlpha 3 B ≤ thetaAlpha 3 D ∨
        ∃ d ∈ D, d ∉ B ∧ ¬ thetaAlpha 3 ((A.subgroupOf (centralizer ({d} : Set X))).map
            (QuotientGroup.mk' (centralLine d))) ≤
          aschbacherSolvableCore 3 (centralizer ({d} : Set X) ⧸ centralLine d)) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have h27 : Nat.card A = 3 ^ 3 := by rw [hAcard]; norm_num
  have h9 : ∀ K : Subgroup X, Nat.card K = 9 → Nat.card K = 3 ^ 2 := fun K hK => by
    rw [hK]; norm_num
  have hcond : ThetaPlaneCondition 3 A := by
    intro E hE hEcard e he he1
    have h := hplane E hE (by rw [hEcard]; norm_num) e he he1
    rwa [inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp,
      inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp] at h
  have hmixed : ∀ first ∈ A, first ≠ 1 → ∀ second ∈ A, second ≠ 1 →
      ⁅centralizer ({second} : Set X) ⊓ thetaCoreOf 3 (centralizer ({first} : Set X)), A⁆ ≤
        thetaCoreOf 3 (centralizer ({second} : Set X)) :=
    fun first hfirst hfirst1 second hsecond hsecond1 =>
      ThetaPlaneCondition.mixed_balance 3 hp A hA hcond first second hfirst hsecond hfirst1
        hsecond1
  have hAel : IsElementaryAbelian 3 A :=
    (SectionRank.isElementaryAbelian_iff_isElemAbelian 3 A).2 hA
  have hmixed' : ∀ c ∈ A, c ≠ 1 → ∀ d ∈ A, d ≠ 1 →
      ⁅inSubgroup (aschbacherSolvableCore 3) (centralizer ({d} : Set X)) ⊓
          centralizer ({c} : Set X), A⁆ ≤
        inSubgroup (aschbacherSolvableCore 3) (centralizer ({c} : Set X)) := by
    intro c hc hc1 d hd hd1
    rw [inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp,
      inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp, inf_comm]
    exact hmixed d hd hd1 c hc hc1
  have hdatum := Coprime.theta_centralizer_full_actor_signalizer_datum hp A hAel
    (by rw [hAcard]; norm_num) hmixed'
  have hcomplete := completion_centralizers hdatum
    (prime_three_solvable_signalizer_completeness hdatum (by rw [hAcard]))
  obtain ⟨-, hWs, hWc, -⟩ := hcomplete
  have hW : (⨆ (a : A) (_ : a ≠ 1),
      (⁅inSubgroup (aschbacherSolvableCore 3) (centralizer ({(a : X)} : Set X)), A⁆ ⊔
        inSubgroup (aschbacherSolvableCore 3) (centralizer (A : Set X)))) =
      thetaActorGenerated 3 A := by
    have hγ : ∀ x : X, ⁅inSubgroup (aschbacherSolvableCore 3) (centralizer ({x} : Set X)), A⁆ ⊔
        inSubgroup (aschbacherSolvableCore 3) (centralizer (A : Set X)) =
        thetaActorSignalizer 3 A x := fun x => by
      rw [inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp,
        inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp]
      rfl
    apply le_antisymm
    · refine iSup_le fun a => iSup_le fun ha => ?_
      rw [hγ]
      exact thetaActorSignalizer_le_generated 3 A a a.2 fun h => ha (Subtype.ext h)
    · refine iSup_le fun x => iSup_le fun hx => iSup_le fun hx1 => ?_
      rw [← hγ]
      exact le_iSup_of_le (⟨x, hx⟩ : A) (le_iSup_of_le (fun h => hx1 (congrArg Subtype.val h))
        le_rfl)
  rw [hW] at hWs hWc
  have hBne : B ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hB
    omega
  obtain ⟨⟨b, hbB⟩, hb1⟩ := ne_bot_iff_exists_ne_one.mp hBne
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  refine ⟨?_, ?_, ?_⟩
  · rw [thetaAlpha_eq_thetaPlaneAlpha hp]
    exact thetaPlaneAlpha_solvable_of_generated_solvable 3 hp A B hA hBA b hbB hb1' hWs
  · rw [thetaAlpha_eq_thetaPlaneAlpha hp, Nat.Prime.coprime_iff_not_dvd hp]
    exact thetaPlaneAlpha_prime_complement_of_generated_prime_complement 3 hp A B hA hBA b hbB
      hb1' ((Nat.Prime.coprime_iff_not_dvd hp).1 hWc)
  · classical
    by_cases hquot : ∀ d ∈ D, d ∉ B →
        thetaAlpha 3 ((A.subgroupOf (centralizer ({d} : Set X))).map
            (QuotientGroup.mk' (centralLine d))) ≤
          aschbacherSolvableCore 3 (centralizer ({d} : Set X) ⧸ centralLine d)
    · left
      rw [thetaAlpha_eq_thetaPlaneAlpha hp, thetaAlpha_eq_thetaPlaneAlpha hp]
      exact thetaPlaneAlpha_le_of_raw_local hp A hA hBA hDA (h9 B hB) (h9 D hD) hmixed
        fun d hd hdB => raw_plane_containment_of_central_line hp A hA h27 (hDA hd)
          (fun h => hdB (h ▸ one_mem B)) (hquot d hd hdB) hBA (h9 B hB)
    · right
      push Not at hquot
      exact hquot

end CFSG.RankThree.Theta
