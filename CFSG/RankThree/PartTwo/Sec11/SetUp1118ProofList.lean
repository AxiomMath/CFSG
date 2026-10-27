module

public import CFSG.RankThree.PartTwo.Sec11.LaterSteps
public import CFSG.RankThree.PartTwo.Sec11.SetUp1118ProofCarrier
public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents
import CFSG.RankThree.PartTwo.Sec11.Item1117Proof
import CFSG.RankThree.PartTwo.Sec11.Item119Used
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item13Models

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)

@[expose] def KFact1118Triality46 : Prop :=
  ∀ (X : Type) [Group X], Sec4.IsList46 X → ∀ (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group) → q.p = 2

namespace SetUp1118Proof


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G}

theorem charTwo_of_trialityD4 (h46 : Sec4.Item4_6) (hD4 : KFact1118Triality46)
    (h : Sec11Std G A c L a R Y) {q : TauCeti.PrimePower}
    {hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid}
    (φ : Y ⧸ aschbacherSolvableCore 3 Y ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group) :
    q.p = 2 := by
  have hG := h.toTheoremFourHyp
  have := hG.isSimpleGroup
  set C := Subgroup.centralizer ({a} : Set G) with hC
  obtain ⟨hYC, hY'⟩ := mem_thetaComponentsIn_iff.mp h.mem_thetaComponentsAt_Y
  have hC4 : SectionFourHyp C := hG.sectionFourHyp
    (PartOne.EmbeddingFixedResidual.centralizer_ne_top_of_simple hG.nonabelian h.a_ne_one)
  have haC : a ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have ha3 : orderOf (⟨a, haC⟩ : C) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (h.mem_partTwoF.1.2 a h.a_mem) h.a_ne_one
  have h3 : 3 ∣ Nat.card (Subgroup.center C) := by
    have := Subgroup.orderOf_dvd_natCard (Subgroup.center C) (mk_mem_center_centralizer a)
    rwa [ha3] at this
  have hL := h46 C hC4 h3 (Y.subgroupOf C) hY'
  set e := Subgroup.subgroupOfEquivOfLe hYC
  have η := QuotientGroup.congr _ _ e
    (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three e)
  exact hD4 _ hL q hq ⟨η.trans φ⟩


theorem isList_of_not_field (h45 : Sec4.Item4_5) (h46 : Sec4.Item4_6) (h119 : Item119)
    (hD4 : KFact1118Triality46) {d x s r g : G} (h : Sec11Data G A c L a R Y d x s r g)
    (hnf : ¬ KFacts.InducesStdKind Y c .field) (hx : 9 < orderOf x) :
    (∃ q : TauCeti.PrimePower, Sec4.IsoGTwo (Y ⧸ aschbacherSolvableCore 3 Y) q) ∨
      (∃ n : ℕ, Sec8.IsoTrialityD4 (Y ⧸ aschbacherSolvableCore 3 Y) n) ∨
      Sec13.IsLThreePi (Y ⧸ aschbacherSolvableCore 3 Y) := by
  have hAe := h.mem_partTwoF.1
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hAC : A ≤ Subgroup.centralizer ({a} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc y hy a h.a_mem)
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hAe h.a_mem h.a_ne_one Y
      h.mem_thetaComponentsAt_Y
  have hbar : ∀ (X : Type) [Group X], (sec11YA a Y A ≃* Multiplicative (ZMod 3) × X) →
      Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* _root_.commutator X) := fun X _ e =>
    Item1116Proof.nonempty_thetaQuot_equiv_commutator h.mem_thetaComponentsAt_Y hAC hAY hAc e
  have hperf : ∀ (X : Type) [Group X], Group.IsPerfect X →
      (sec11YA a Y A ≃* Multiplicative (ZMod 3) × X) →
        Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* X) := by
    intro X _ hX e
    obtain ⟨φ⟩ := hbar X e
    exact ⟨φ.trans ((MulEquiv.subgroupCongr (Group.isPerfect_def.mp hX)).trans
      Subgroup.topEquiv)⟩
  have hQS := Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y
  have hsolv : ∀ (X : Type) [Group X], Group.IsSolvable X →
      (sec11YA a Y A ≃* Multiplicative (ZMod 3) × X) → False := by
    intro X _ hXs e
    obtain ⟨φ⟩ := hbar X e
    have : Group.IsSolvable (Y ⧸ aschbacherSolvableCore 3 Y) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (_root_.commutator X).subtype.comp φ.toMonoidHom)
        ((_root_.commutator X).subtype_injective.comp φ.injective)
    have : Group.IsPerfect (Y ⧸ aschbacherSolvableCore 3 Y) := hQS.1
    have := hQS.2.1
    have : Nontrivial (Y ⧸ aschbacherSolvableCore 3 Y) :=
      (QuotientGroup.mk'_surjective (Subgroup.center _)).nontrivial
    exact Group.IsPerfect.not_isSolvable (Y ⧸ aschbacherSolvableCore 3 Y) inferInstance
  rcases h119 G A c L a R Y h.toSec11Std d h.inf_eq h.closure_eq with
    ⟨hf, -⟩ | ⟨⟨q, hq, ⟨e⟩⟩ | ⟨q, hq, ⟨e⟩⟩, -⟩ | ⟨hL3 | hPGL, -⟩ | ⟨-, ⟨eK⟩, -⟩
  · exact absurd hf hnf
  ·
    exact Or.inl ⟨q, hq, hperf _ (isPerfect_lie_G2 q hq) e⟩
  ·
    obtain ⟨φ⟩ := hperf _ (isPerfect_lie_trialityD4 q hq) e
    exact Or.inr (Or.inl ⟨q.exponent, q, hq, charTwo_of_trialityD4 h46 hD4 h.toSec11Std φ, rfl,
      ⟨φ⟩⟩)
  ·
    obtain ⟨p, f, hp, hf1, ⟨hpf, ⟨e⟩⟩ | ⟨hpf, ⟨e⟩⟩⟩ := hL3
    · obtain ⟨φ⟩ := hperf _ (Sec13.isPerfect_center_projSL p f hf1 hpf).1 e
      exact Or.inr (Or.inr ⟨p, f, hp, hf1, Or.inl ⟨hpf, ⟨φ⟩⟩⟩)
    · by_cases hq2 : 2 < p ^ f
      · obtain ⟨φ⟩ := hperf _ (Sec13.isPerfect_center_projSU p f hf1 hpf hq2).1 e
        exact Or.inr (Or.inr ⟨p, f, hp, hf1, Or.inr ⟨hpf, ⟨φ⟩⟩⟩)
      · exfalso
        have h2 : p ^ f = 2 := by
          have : 2 ≤ p ^ f := hp.out.two_le.trans (Nat.le_self_pow (by omega) p)
          omega
        obtain ⟨rfl, rfl⟩ := Sec13.eq_two_one_of_pow_eq_two hp.out h2
        have hs : Group.IsSolvable (projSU 3 2 1) := Sec13.isSolvable_projSU_two
        exact hsolv _ hs e
  ·
    obtain ⟨π, p, f, K, _, hK, hmod, ⟨e⟩⟩ := hPGL
    have hq2 : 2 < p ^ f := by
      by_contra hle
      have h2 : p ^ f = 2 := by
        have hf : f ≠ 0 := by have := hK.one_le; omega
        have : 2 ≤ p ^ f := le_trans hK.prime.two_le (Nat.le_self_pow hf _)
        omega
      cases π
      · exact hsolv _ (Sec13.isSolvable_projImage_glPi_two hK h2) e
      · change p ^ f % 3 = 1 at hmod
        omega
    obtain ⟨φ⟩ := hbar _ e
    have hSP : projImage (Sec4.slPi π 3 (p ^ f) K) ≤ projImage (Sec4.glPi π 3 (p ^ f) K) :=
      Subgroup.map_mono (Sec4.slPi_le_glPi fun hπ => by subst hπ; exact hK.unitary)
    exact Or.inr (Or.inr (Sec13.isLThreePi_of_mulEquiv
      (φ.trans ((MulEquiv.subgroupCongr (Sec13.commutator_projImage_glPi hK hq2)).trans
        (Subgroup.subgroupOfEquivOfLe hSP)))
      (Sec13.isLThreePi_projImage_slPi hK hmod)))
  ·
    exact (Item1117Proof.false_of_card_L32 h hx eK).elim

end SetUp1118Proof

end CFSG.RankThree.PartTwo.Sec11
