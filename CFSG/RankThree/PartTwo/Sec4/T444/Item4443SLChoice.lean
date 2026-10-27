module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item4443SLLayer
public import CFSG.RankThree.PartTwo.Sec4.T444.Item4443SL447
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
import CFSG.RankThree.PartTwo.Sec4.T444.Step450
import CFSG.RankThree.PartTwo.Sec4.T444.Step452
import CFSG.RankThree.PartTwo.Sec4.Steps448
import CFSG.RankThree.PartOne.S10.ThetaFreeNormalizedLayerEmbedding
import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCover
import CFSG.RankThree.PartTwo.Sec18.Components
public import CFSG.RankThree.PartTwo.Sec4.T444.Item4443SLInner
public import CFSG.RankThree.PartTwo.Sec4.T444.Item4443SLTools

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item4443SL

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutatorElement_mem_normalizer {L : Subgroup G} {i a : G}
    (ha : a ∈ normalizer (L : Set G))
    (ha' : a ∈ normalizer ((L.map (MulAut.conj i⁻¹).toMonoidHom : Subgroup G) : Set G)) :
    ⁅i, a⁆ ∈ normalizer (L : Set G) := by
  have hmem : ∀ x, x ∈ L.map (MulAut.conj i⁻¹).toMonoidHom ↔ i * x * i⁻¹ ∈ L := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro hx
      exact ⟨i * x * i⁻¹, hx, by simp [mul_assoc]⟩
  have h1 : i * a * i⁻¹ ∈ normalizer (L : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    have e1 := hmem (i⁻¹ * x * i)
    have e2 := mem_normalizer_iff.mp ha' (i⁻¹ * x * i)
    have e3 := hmem (a * (i⁻¹ * x * i) * a⁻¹)
    rw [show i * (i⁻¹ * x * i) * i⁻¹ = x by group] at e1
    rw [show i * (a * (i⁻¹ * x * i) * a⁻¹) * i⁻¹ = i * a * i⁻¹ * x * (i * a * i⁻¹)⁻¹ by
      group] at e3
    rw [← e1, e2, e3]
  rw [commutatorElement_def]
  exact mul_mem h1 (inv_mem ha)

theorem le_normalizer_of_commutator_eq {I A L : Subgroup G} (hIA : ⁅I, A⁆ = I)
    (hA : ∀ L' ∈ thetaComponents 3 G, A ≤ normalizer (L' : Set G))
    (hL : L ∈ thetaComponents 3 G) : I ≤ normalizer (L : Set G) := by
  rw [← hIA, commutator_le]
  intro i _ a ha
  exact commutatorElement_mem_normalizer (hA L hL ha)
    (hA _ (map_mulEquiv_mem_thetaComponents Nat.prime_three (MulAut.conj i⁻¹) hL) ha)

omit [Finite G] in
theorem le_centralizer_of_commutator_eq {I Q O : Subgroup G} [O.Normal] (hIQ : ⁅I, Q⁆ = I)
    (hQO : Q ≤ centralizer (O : Set G)) : I ≤ centralizer (O : Set G) := by
  have hQO' : ⁅Q, O⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hQO
  have h1 : ⁅⁅Q, O⁆, I⁆ = ⊥ := by rw [hQO', commutator_bot_left]
  have h2 : ⁅⁅O, I⁆, Q⁆ = ⊥ := by
    have hOQ : ⁅O, Q⁆ = ⊥ := by rw [commutator_comm]; exact hQO'
    exact eq_bot_iff.mpr ((commutator_mono (commutator_le_left O I) le_rfl).trans hOQ.le)
  have h3 := commutator_commutator_eq_bot_of_rotate h1 h2
  rw [hIQ] at h3
  exact commutator_eq_bot_iff_le_centralizer.mp h3

theorem inner_of_isComponent {X : Type} [Group X] [Finite X]
    (hS : SchreierFor CFSG.Assembly.InCatalog) (hK : CFSG.IsKGroup X) {Y J : Subgroup X}
    (hJ : IsComponent J) (hYJ : Y ≤ normalizer (J : Set X)) (hYp : ⁅Y, Y⁆ = Y) :
    ∀ y ∈ Y, ∃ c ∈ J, ∀ z ∈ J, y * z * y⁻¹ = c * z * c⁻¹ := by
  have : IsSimpleGroup (J ⧸ center J) := hJ.1.2.1
  exact PartOne.ThetaFreeEmbedding.inner_action_of_perfect hJ.1
    (hS (J ⧸ center J) hJ.1.2.2 (hK J (center J) inferInstance)) hYJ hYp

theorem not_perfectResidual_le {A M H : Subgroup G} (h : Ctx444 G A M)
    (hH : H ∈ Late.scriptH₀ A M) : ¬ inSubgroup perfectResidual H ≤ M := by
  intro hIM
  apply Sec18.inf_ne_of_mem_scriptH₀ hH
  refine inf_eq_left.mpr (le_trans (le_of_eq hH.1) ?_)
  exact sup_le (sup_le hIM h.le) ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right)

section Ctx


theorem Ctx4443.le_normalizer_of_commutator_eq (h45 : Item4_5) {A M H : Subgroup G} {s : G}
    (h : Ctx4443 G A M H s) (hIA : ⁅inSubgroup perfectResidual H, A⁆ = inSubgroup perfectResidual H)
    {L : Subgroup G} (hL : L ∈ thetaComponents 3 G) :
    inSubgroup perfectResidual H ≤ normalizer (L : Set G) :=
  Item4443SL.le_normalizer_of_commutator_eq hIA
    (fun _ hL' => h.ctx444.le_normalizer_of_mem_thetaComponents h45 hL') hL

theorem Ctx4443.map_le_sSup (hSz : KFacts.KPSz) (hS : SchreierFor CFSG.Assembly.InCatalog)
    (h45 : Item4_5) {A M H : Subgroup G} {s : G} (h : Ctx4443 G A M H s)
    (hIA : ⁅inSubgroup perfectResidual H, A⁆ = inSubgroup perfectResidual H)
    (hIq : CFSG.IsQuasisimple (inSubgroup perfectResidual H ⧸
      CFSG.pCore 2 (inSubgroup perfectResidual H))) :
    (inSubgroup perfectResidual H).map (starQuot G) ≤
      sSup {K : Subgroup (G ⧸ CFSG.pPrimeCore 3 G) | IsComponent K ∧
        ¬ (inSubgroup perfectResidual H).map (starQuot G) ≤
          centralizer (K : Set (G ⧸ CFSG.pPrimeCore 3 G))} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set I := inSubgroup perfectResidual H with hI
  set π := starQuot G with hπ
  set Is := I.map π with hIs
  have hIp : ⁅I, I⁆ = I := Sec18.commutator_inSubgroup_perfectResidual H
  have hIsp : ⁅Is, Is⁆ = Is := by rw [hIs, ← map_commutator, hIp]
  have hIQ := Ctx4443.commutator_zpowers_eq h hIq
  have hX : CFSG.pPrimeCore 3 (G ⧸ CFSG.pPrimeCore 3 G) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3
  have hIsQ : ⁅Is, (zpowers s).map π⁆ = Is := by rw [hIs, ← map_commutator, hIQ]
  have : (CFSG.pCore 3 (G ⧸ CFSG.pPrimeCore 3 G)).Normal := CFSG.pCore_normal
  have hQO : (zpowers s).map π ≤
      centralizer (CFSG.pCore 3 (G ⧸ CFSG.pPrimeCore 3 G) : Set (G ⧸ CFSG.pPrimeCore 3 G)) := by
    rw [MonoidHom.map_zpowers, zpowers_le]
    exact rank3II_4_48_3 G A M H s h
  have hIsF : Is ≤ centralizer (fittingSubgroup (G ⧸ CFSG.pPrimeCore 3 G) :
      Set (G ⧸ CFSG.pPrimeCore 3 G)) := fun y hy =>
    centralizer_le (fittingSubgroup_le_pCore_three_of_pPrimeCore_eq_bot hX)
      (le_centralizer_of_commutator_eq hIsQ hQO hy)
  have hKX : CFSG.IsKGroup (G ⧸ CFSG.pPrimeCore 3 G) :=
    CFSG.SectionRank.K_group_section_closure_inCatalog h.ctx444.sectionFourHyp.kGroup ⊤ _
      (Census.quotientTopEquiv (CFSG.pPrimeCore 3 G))
  refine le_sSup_components_of_inner hIsp hIsF fun K hK => ?_
  obtain ⟨L, hL, rfl⟩ := exists_mem_thetaComponents_map_eq hSz h.ctx444.sectionFourHyp.kGroup
    (localRank_theta_quotient_le h.ctx444.sectionFourHyp) hK
  exact inner_of_isComponent hS hKX hK
    ((map_mono (Ctx4443.le_normalizer_of_commutator_eq h45 h hIA hL)).trans
      (le_normalizer_map π)) hIsp

theorem Ctx4443.map_le_layer (hSz : KFacts.KPSz) (hS : SchreierFor CFSG.Assembly.InCatalog)
    (h45 : Item4_5) {A M H : Subgroup G} {s : G} (h : Ctx4443 G A M H s)
    (hIA : ⁅inSubgroup perfectResidual H, A⁆ = inSubgroup perfectResidual H)
    (hIq : CFSG.IsQuasisimple (inSubgroup perfectResidual H ⧸
      CFSG.pCore 2 (inSubgroup perfectResidual H))) :
    (inSubgroup perfectResidual H).map (starQuot G) ≤ layer (G ⧸ CFSG.pPrimeCore 3 G) :=
  (Ctx4443.map_le_sSup hSz hS h45 h hIA hIq).trans (sSup_le_sSup fun _ hK => hK.1)

theorem Ctx4443.exists_mem_thetaComponents_of_commutator_eq (hSz : KFacts.KPSz)
    (hS : SchreierFor CFSG.Assembly.InCatalog) (h45 : Item4_5) {A M H : Subgroup G} {s : G}
    (h : Ctx4443 G A M H s)
    (hIA : ⁅inSubgroup perfectResidual H, A⁆ = inSubgroup perfectResidual H)
    (hIq : CFSG.IsQuasisimple (inSubgroup perfectResidual H ⧸
      CFSG.pCore 2 (inSubgroup perfectResidual H))) :
    ∃ L ∈ thetaComponents 3 G, 3 ∣ Nat.card L ∧ ¬ L ≤ M ∧
      inSubgroup perfectResidual H ≤ normalizer (L : Set G) ∧
      (inSubgroup perfectResidual H).map (starQuot G) ≤
        L.map (starQuot G) ⊔ centralizer (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G)) ∧
      ¬ (inSubgroup perfectResidual H).map (starQuot G) ≤
        centralizer (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G)) ∧
      s ∈ normalizer (L : Set G) ∧
      ¬ (zpowers s).map (starQuot G) ≤
        centralizer (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set I := inSubgroup perfectResidual H with hI
  set π := starQuot G with hπ
  set Is := I.map π with hIs
  have hIQ := Ctx4443.commutator_zpowers_eq h hIq
  have hIsQ : ⁅Is, (zpowers s).map π⁆ = Is := by rw [hIs, ← map_commutator, hIQ]
  have hX : CFSG.pPrimeCore 3 (G ⧸ CFSG.pPrimeCore 3 G) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3
  have hlay := Ctx4443.map_le_sSup hSz hS h45 h hIA hIq
  obtain ⟨K, ⟨hK, hKI⟩, hKM⟩ : ∃ K ∈ {K : Subgroup (G ⧸ CFSG.pPrimeCore 3 G) | IsComponent K ∧
      ¬ Is ≤ centralizer (K : Set (G ⧸ CFSG.pPrimeCore 3 G))}, ¬ K ≤ M.map π := by
    by_contra hno
    push Not at hno
    apply not_perfectResidual_le h.ctx444 h.mem_scriptH₀
    have hle : Is ≤ M.map π := hlay.trans (sSup_le fun K hK => hno K hK)
    intro x hx
    obtain ⟨m, hm, hme⟩ := hle (mem_map_of_mem π hx)
    rw [hπ, starQuot, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hme
    have h1 : x = m * (m⁻¹ * x) := by group
    rw [h1]
    exact M.mul_mem hm (h.ctx444.pPrimeCore_le hme)
  obtain ⟨L, hL, rfl⟩ := exists_mem_thetaComponents_map_eq hSz h.ctx444.sectionFourHyp.kGroup
    (localRank_theta_quotient_le h.ctx444.sectionFourHyp) hK
  have h3 : 3 ∣ Nat.card L := (three_dvd_card_of_isComponent hX hK).trans (card_map_dvd L π)
  have hLM : ¬ L ≤ M := fun hLM => hKM (map_mono hLM)
  have hIL := Ctx4443.le_normalizer_of_commutator_eq h45 h hIA hL
  have hIsL : Is ≤ normalizer (L.map π : Set (G ⧸ CFSG.pPrimeCore 3 G)) :=
    (map_mono hIL).trans (le_normalizer_map π)
  have hIC : Is ≤ L.map π ⊔ centralizer (L.map π : Set (G ⧸ CFSG.pPrimeCore 3 G)) := by
    refine hlay.trans (sSup_le fun K' hK' => ?_)
    rcases distinct_components_commute hK'.1 hK with heq | hcomm
    · rw [heq]
      exact le_sup_left
    · exact (commutator_eq_bot_iff_le_centralizer.mp hcomm).trans le_sup_right
  refine ⟨L, hL, h3, hLM, hIL, hIC, hKI, mem_normalizer_of_mem_centralizer h45 h.ctx444
    h.concl4442.2.1 (Ctx4443.not_three_dvd_card_zpowers h) hL hLM, fun hsC => hKI ?_⟩
  rw [← hIsQ, commutator_le]
  intro i hi q hq
  rw [commutatorElement_def]
  exact mul_mem (conj_mem_centralizer (hIsL hi) (hsC hq)) (inv_mem (hsC hq))

end Ctx

end CFSG.RankThree.PartTwo.Sec4.Item4443SL
