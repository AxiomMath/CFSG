module

public import CFSG.OddTranspositions.PartThree.Nine.FiveUnitaryLocal
public import CFSG.OddTranspositions.PartThree.Nine.Goldschmidt
import CFSG.OddTranspositions.PartThree.Nine.FiveUnitaryComponent
import CFSG.OddTranspositions.PartThree.Nine.FiveUnitaryTransfer
import CFSG.OddTranspositions.PartThree.Nine.FinalBender
import CFSG.OddTranspositions.PartThree.Nine.FinalSetup
import CFSG.ClassicalInvolution.AschTight.StronglyClosed
import CFSG.Timmesfeld.Bridge.Asc72Central
import CFSG.OddTranspositions.PartFour.Fourteen.ModelBenderDistinct
import CFSG.ClassicalInvolution.Asc77.Lemma310
import CFSG.ClassicalInvolution.Asc77.ThmEStatement
import CFSG.ClassicalInvolution.Asc77.WP1Section6
import CFSG.ClassicalInvolution.AschTight.CSMD
import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
import CFSG.ClassicalInvolution.Balance.Theorem5Models
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
import CFSG.GH74.GLS.Defs
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartOne
import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullOrbit
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityCoercions
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityTransport
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorQuotientModel
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremTwoFixedDegree
import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SectionRank.TitsCover
import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsFrame
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
import CFSG.LocalAnalysis.SignalizerFunctor
import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian_models
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.Sporadic.J4.Simple
import CFSG.Sporadic.J4Base
import CFSG.Sporadic.Mathieu.M12
import CFSG.Sporadic.Mathieu.M24
import CFSG.StronglyEmbedded.UniqueCoset
import CFSG.Walter.J1
import CFSG.Walter.J1Recog
import CFSG.Walter.Ree.Thompson2.BaseFin
import CFSG.Walter.ReeOrder.WardLocal
import CFSG.Walter.W67.Section8.Prop83

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.BenderSuzuki

variable {G : Type} [Group G] [Finite G] {D : Set G}

private theorem le_commutator_of_isBenderGroup {J : Subgroup G} (hJ : IsBenderGroup J) :
    J ≤ commutator G := by
  have h := congrArg (Subgroup.map J.subtype) (IsBenderGroup.commutator_eq_top hJ)
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  rw [← h, commutator_def]
  exact Subgroup.commutator_mono le_top le_top

section Chain

variable {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)} {S : Sylow 2 G}
  {U : Subgroup G} {n : ℕ}

namespace IsTranslationSubgroup

variable {L L₀ Y V : Subgroup G} {Γ : Set G}

theorem mul_mem_of_commute (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC) (h4 : Conclusion9_4 D hC T S) (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n)
    (hUn : Nat.card U = 2 ^ n) (hL : UnitaryCentralizerData hC T S U n L L₀)
    (hΓ : Γ = {d | Reach ((Subgroup.centralizer (L : Set G) : Set G) ∩ D) hC.d d})
    (hY : Y = Subgroup.closure Γ) (hV : IsTranslationSubgroup hC S U Y V n) {z : G}
    (hz : z ∈ U) (hz1 : z ≠ 1) {d e : G} (hd : d ∈ D) (he : e ∈ D) (_hde : d ≠ e)
    (hc : Commute d e) (hdz : Commute (d * e) z) : d * e ∈ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxN : d * e ∈ Subgroup.normalizer ((S : Set G) ∩ D) :=
    hU.centralizer_le_normalizer_of_center hH h3 hL.center_eq hz hz1
      (Subgroup.mem_centralizer_singleton_iff.mpr hdz.eq)
  have hx2 : d * e * (d * e) = 1 := by
    rw [mul_assoc, ← mul_assoc e d e, ← hc.eq, mul_assoc, hC.setup.oddT.mul_self_eq_one he,
      mul_one, hC.setup.oddT.mul_self_eq_one hd]
  have hSeq := sylow_eq_sup hH h3 h4 hU hCH eH hUn hL hΓ hY hV
  obtain ⟨-, -, hQn, -⟩ := normal hH h3 hU hCH eH hUn hL hΓ hY hV rfl
  have hxNS : d * e ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    rw [hSeq]
    refine ⟨hQn _ hxN w, fun hw => ?_⟩
    have h := hQn _ (Subgroup.inv_mem _ hxN) _ hw
    simpa [mul_assoc] using h
  have hp : IsPGroup 2 (Subgroup.zpowers (d * e)) := by
    have hx2' : (d * e) ^ 2 = 1 := by rw [pow_two]; exact hx2
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx2') with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hmem : d * e ∈ Subgroup.zpowers (d * e) ⊓ Subgroup.normalizer (S : Set G) :=
    ⟨Subgroup.mem_zpowers _, hxNS⟩
  rw [hp.inf_normalizer_sylow S] at hmem
  obtain ⟨hSK, -⟩ := inter_commutator_eq hH h3 h4 hU hCH eH hUn hL hΓ hY hV rfl
  have hxRV : d * e ∈ ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) ⊔ V := by
    rw [← hSK]
    exact ⟨hmem.2, hC.setup.mul_mem_commutator hd he⟩
  exact (card_sup_and_mem hH h3 hU hCH eH hUn hL hΓ hY hV rfl).2.1 _ hxRV hx2

theorem isMulCommutative_wcl (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC) (h4 : Conclusion9_4 D hC T S) (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n)
    (hUn : Nat.card U = 2 ^ n) (hL : UnitaryCentralizerData hC T S U n L L₀)
    (hΓ : Γ = {d | Reach ((Subgroup.centralizer (L : Set G) : Set G) ∩ D) hC.d d})
    (hY : Y = Subgroup.closure Γ) (hV : IsTranslationSubgroup hC S U Y V n) {z : G}
    (hz : z ∈ U) (hz1 : z ≠ 1) (hzK : z ∈ commutator G) :
    IsMulCommutative (CFSG.LargeExtraspecial.S11.wcl (⟨z, hzK⟩ : commutator G)) := by
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have huzD : hC.d * z ∈ D := by
    have h : hC.d * z ∈ (S : Set G) ∩ D := hU.sylow_inter ▸ ⟨z, hz, rfl⟩
    exact h.2
  have huz : Commute hC.d z :=
    (Subgroup.mem_centralizer_singleton_iff.mp
      (PartThree.Halpha_le_centralizer_d hC
        (Subgroup.map_subtype_le _ (hU.le_pResidualOf hz)))).symm
  have hne : hC.d ≠ hC.d * z := fun h => hz1 (by simpa using h.symm)
  have hWV : CFSG.LargeExtraspecial.S11.wcl z ≤ V := by
    rw [CFSG.LargeExtraspecial.S11.wcl, Subgroup.closure_le]
    rintro _ ⟨m, rfl, hyz⟩
    have hsplit : m * hC.d * m⁻¹ * (m * (hC.d * z) * m⁻¹) = m * z * m⁻¹ := by
      calc m * hC.d * m⁻¹ * (m * (hC.d * z) * m⁻¹) = m * (hC.d * hC.d) * z * m⁻¹ := by group
        _ = m * z * m⁻¹ := by rw [hu2, mul_one]
    rw [← hsplit]
    refine mul_mem_of_commute hH h3 h4 hU hCH eH hUn hL hΓ hY hV hz hz1
      (hC.setup.conj_mem m hC.hd) (hC.setup.conj_mem m huzD)
      (fun h => hne (mul_left_cancel (mul_right_cancel h)))
      ((Commute.conj_iff m).mpr ((Commute.refl _).mul_right huz)) ?_
    rw [hsplit]
    exact hyz
  have := hV.isElementaryAbelian
  have hW : IsMulCommutative (CFSG.LargeExtraspecial.S11.wcl z) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    have h := congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := V)).comm ⟨a, hWV a.2⟩ ⟨b, hWV b.2⟩)
    exact Subtype.ext h
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have ha := wcl_map_le (⟨z, hzK⟩ : commutator G) (Subgroup.mem_map_of_mem _ a.2)
  have hb := wcl_map_le (⟨z, hzK⟩ : commutator G) (Subgroup.mem_map_of_mem _ b.2)
  have h := congrArg Subtype.val (hW.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
  exact Subtype.ext h


theorem isBenderGroup_commutator (hH : Th91Hyp D hC)
    (hs : IsSimpleGroup (commutator G)) (h3 : Conclusion9_3 D hC) (h4 : Conclusion9_4 D hC T S)
    (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n)
    (hUn : Nat.card U = 2 ^ n) (hL : UnitaryCentralizerData hC T S U n L L₀)
    (hΓ : Γ = {d | Reach ((Subgroup.centralizer (L : Set G) : Set G) ∩ D) hC.d d})
    (hY : Y = Subgroup.closure Γ) (hV : IsTranslationSubgroup hC S U Y V n) :
    IsBenderGroup (commutator G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := commutator G with hKdef
  have : IsSimpleGroup K := hs
  obtain ⟨hn, -⟩ := hU.two_le_and_card_eq_of_psu3 hH ⟨eH⟩
  obtain ⟨eJ⟩ := nonempty_pResidualOf_mulEquiv_psu3 h3 hCH eH
  have hLB : IsBenderGroup (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) := .isPSU3 n hn eJ
  have hLK := le_commutator_of_isBenderGroup hLB
  have hnonab : ∃ a b : K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := IsBenderGroup.exists_not_commute hLB
    refine ⟨⟨a, hLK a.2⟩, ⟨b, hLK b.2⟩, fun h => hab ?_⟩
    have h' := congrArg (fun x : K => (x : G)) h
    exact Subtype.ext h'
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU.ne_bot
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzK : z ∈ K := mem_commutator_of_mem_omega hU hz
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have huD : hC.d ∈ (S : Set G) ∩ D := hU.sylow_inter ▸ ⟨1, U.one_mem, mul_one _⟩
  have huzD : hC.d * z ∈ (S : Set G) ∩ D := hU.sylow_inter ▸ ⟨z, hz, rfl⟩
  have hzS : z ∈ (S : Subgroup G) := by
    have := (S : Subgroup G).mul_mem huD.1 huzD.1
    rwa [← mul_assoc, hu2, one_mul] at this
  obtain ⟨hSK, -⟩ := inter_commutator_eq hH h3 h4 hU hCH eH hUn hL hΓ hY hV rfl
  obtain ⟨hcard, -, -⟩ := card_sup_and_mem hH h3 hU hCH eH hUn hL hΓ hY hV rfl
  have hRVz : ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) ⊔ V ≤
        Subgroup.centralizer ({z} : Set G) := by
    refine sup_le (fun r hr => ?_) (fun v hv => ?_)
    · have hrB : r ∈ Subgroup.centralizer ((S : Set G) ∩ D) :=
        hL.centralizer_eq ▸ Subgroup.mem_sup_left hr.1
      have h1 : Commute r hC.d := (Subgroup.mem_centralizer_iff.mp hrB _ huD).symm
      have h2 : Commute r (hC.d * z) := (Subgroup.mem_centralizer_iff.mp hrB _ huzD).symm
      have h12 := h1.mul_right h2
      rw [← mul_assoc, hu2, one_mul] at h12
      exact Subgroup.mem_centralizer_singleton_iff.mpr h12.eq
    · have := hV.isElementaryAbelian
      have h := congrArg Subtype.val
        ((IsMulCommutative.is_comm (M := V)).comm ⟨v, hv⟩ ⟨z, hV.le hz⟩)
      exact Subgroup.mem_centralizer_singleton_iff.mpr h
  obtain ⟨P, hP⟩ := CFSG.DisconnectedInvolutionGraph.Helpers.normal_subgroup_sylow_intersection
    2 K S
  have hPeq : ((P : Subgroup K)).map K.subtype = (S : Subgroup G) ⊓ K := by
    rw [hP, Subgroup.subgroupOf_map_subtype]
  have hz'P : (⟨z, hzK⟩ : K) ∈ (P : Subgroup K) := by
    rw [hP]
    exact Subgroup.mem_subgroupOf.mpr hzS
  refine isBenderGroup_of_wcl_abelian hnonab P hz'P (fun h => hz1' (congrArg Subtype.val h))
    (fun x hx => Subtype.ext ?_)
    (isMulCommutative_wcl hH h3 h4 hU hCH eH hUn hL hΓ hY hV hz hz1' hzK) ?_
  · have hxRV : (x : G) ∈ ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) ⊔ V := by
      rw [← hSK, ← hKdef, ← hPeq]
      exact ⟨x, hx, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (hRVz hxRV)
  · rw [← Subgroup.card_map_of_injective K.subtype_injective, hPeq, hKdef, hSK, hcard]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (4 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)

end IsTranslationSubgroup

open scoped commutatorElement in
private theorem false_of_isBenderGroup_commutator_of_psu3
    (hH : Th91Hyp D hC) (hs : IsSimpleGroup (commutator G))
    (hB : IsBenderGroup (commutator G)) (hn : 2 ≤ n)
    (eJ : CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ≃* PSU3Model n) : False := by
  classical
  set K := commutator G with hKdef
  set L := CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) with hLdef
  have hLB : IsBenderGroup L := .isPSU3 n hn eJ
  have : IsSimpleGroup L := IsBenderGroup.isSimpleGroup hLB
  have hLns : ¬ Group.IsSolvable L := fun hsol => by
    obtain ⟨a, b, hab⟩ := IsBenderGroup.exists_not_commute hLB
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsol a b)
  have hLK : L ≤ K := le_commutator_of_isBenderGroup hLB
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hLu : ∀ l ∈ L, Commute hC.d l := fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.mp
      (PartThree.Halpha_le_centralizer_d hC (Subgroup.map_subtype_le _ hl))).symm
  have huK : hC.d ∉ K := by
    intro huK
    apply hLns
    have hord : orderOf (⟨hC.d, huK⟩ : K) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hC.setup.oddT.orderOf_eq_two hC.hd
    have hsol :=
      CFSG.ClassicalInvolution.Disconnected.AschTight.isSolvable_centralizer_of_isBenderGroup
        hB hord
    let f : L →* Subgroup.centralizer ({(⟨hC.d, huK⟩ : K)} : Set K) :=
      { toFun := fun x => ⟨⟨x, hLK x.2⟩, by
          rw [Subgroup.mem_centralizer_singleton_iff]
          apply Subtype.ext
          exact (Subgroup.mem_centralizer_singleton_iff.mp (PartThree.Halpha_le_centralizer_d hC
            (Subgroup.map_subtype_le _ x.2)))⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact Group.isSolvable_of_isSolvable_injective (f := f) (fun a b h => by
      have := congrArg Subtype.val (congrArg Subtype.val h)
      exact Subtype.ext this)
  have hnonabK : ∃ a b : K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := IsBenderGroup.exists_not_commute hLB
    refine ⟨⟨a, hLK a.2⟩, ⟨b, hLK b.2⟩, fun h => hab ?_⟩
    have h' := congrArg (fun x : K => (x : G)) h
    exact Subtype.ext h'
  have hKn : K.Normal := (inferInstance : (commutator G).Normal)
  have hKC : Subgroup.centralizer (K : Set G) = ⊥ := by
    set C := Subgroup.centralizer (K : Set G) with hCdef
    have hCn : C.Normal := Subgroup.normal_centralizer
    have hCK : ∀ x ∈ C, x ∈ K → x = 1 := by
      intro x hxC hxK
      have hZ : (⟨x, hxK⟩ : K) ∈ Subgroup.center K := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.mp hxC y y.2
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
      · rw [h, Subgroup.mem_bot] at hZ
        exact congrArg Subtype.val hZ
      · exfalso
        obtain ⟨a, b, hab⟩ := hnonabK
        apply hab
        have ha : a ∈ Subgroup.center K := h ▸ Subgroup.mem_top a
        exact (Subgroup.mem_center_iff.mp ha b).symm
    have hCab : ∀ a b : C, a * b = b * a := by
      intro a b
      have hcK : ⁅(a : G), (b : G)⁆ ∈ K := by
        rw [hKdef, commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      have hcC : ⁅(a : G), (b : G)⁆ ∈ C := by
        rw [commutatorElement_def]
        exact C.mul_mem (C.mul_mem (C.mul_mem a.2 b.2) (C.inv_mem a.2)) (C.inv_mem b.2)
      have h1 := hCK _ hcC hcK
      rw [commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
      exact Subtype.ext h1
    exact hH.solv C hCn (Group.isSolvable_of_comm hCab)
  have hLn : ∀ c ∈ K, Commute hC.d c → ∀ l ∈ L, c * l * c⁻¹ ∈ L := by
    intro c _ hc l hl
    have hgv : c * hC.d * c⁻¹ ∈ hC.alpha := by
      rw [← hc.eq, mul_inv_cancel_right]
      exact hC.d_mem_alpha
    have hcα : c ∈ Subgroup.normalizer hC.alpha := by
      by_contra hg
      exact Set.disjoint_left.mp (hC.isBlock_alpha.disjoint_conj hg) hgv ⟨hC.d, hC.d_mem_alpha, rfl⟩
    have hcH := normalizer_le_normalizer_Halpha hC.setup.normal hcα
    have hcL := CFSG.Quasithin.normalizer_le_normalizer_pResidualOf 2 _ hcH
    exact (Subgroup.mem_normalizer_iff.mp hcL l).mp hl
  rcases outer_involution_fixed_cases hB hKC hu2 huK hLK hLu hLn hLns with
      ⟨m, -, -, ⟨eLm⟩⟩ | ⟨m, -, -, ⟨eLm⟩⟩ <;>
    exact CFSG.OddTranspositions.PartFour.false_of_mulEquiv_psu3Model_of_mulEquiv_psl2Model hn eJ
      eLm

theorem IsTranslationSubgroup.false_of_isBenderGroup_commutator
    {L L₀ Y V : Subgroup G} {Γ : Set G} (hH : Th91Hyp D hC) (hs : IsSimpleGroup (commutator G))
    (h3 : Conclusion9_3 D hC) (_h4 : Conclusion9_4 D hC T S) (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n)
    (_hUn : Nat.card U = 2 ^ n) (_hL : UnitaryCentralizerData hC T S U n L L₀)
    (_hΓ : Γ = {d | Reach ((Subgroup.centralizer (L : Set G) : Set G) ∩ D) hC.d d})
    (_hY : Y = Subgroup.closure Γ) (_hV : IsTranslationSubgroup hC S U Y V n)
    (hB : IsBenderGroup (commutator G)) : False := by
  obtain ⟨hn, -⟩ := hU.two_le_and_card_eq_of_psu3 hH ⟨eH⟩
  obtain ⟨eJ⟩ := nonempty_pResidualOf_mulEquiv_psu3 h3 hCH eH
  exact false_of_isBenderGroup_commutator_of_psu3 hH hs hB hn eJ

end Chain

theorem not_exists_mulEquiv_psu3 (hC : HypothesisC D) (hH : Th91Hyp D hC)
    (hs : IsSimpleGroup (commutator G)) (hIH : Th91Below (Nat.card G)) (h3 : Conclusion9_3 D hC)
    (T : Sylow 2 (Halpha D hC.alpha)) (S : Sylow 2 G)
    (hTS : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤ S)
    (h4 : Conclusion9_4 D hC T S)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d) :
    ¬ ∃ n : ℕ, Nonempty (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃*
      PSU3Model n) := by
  rintro ⟨n, ⟨eH⟩⟩
  obtain ⟨U, hU⟩ := exists_deltaSetup hC hH h3 T S hTS
  obtain ⟨-, hUn⟩ := hU.two_le_and_card_eq_of_psu3 hH ⟨eH⟩
  obtain ⟨L, L₀, hL⟩ := exists_unitaryCentralizerData hH h3 h4 hU hCH eH hUn
  obtain ⟨P, hΔP, -, S', -, hPS', hS'⟩ := exists_sylow_centralizerComponent hH h3 hU hL rfl rfl
  have h4' := h4.of_inter_eq hS'
  have hU' := hU.of_inter_eq hS'
  have hL' := hL.of_inter_eq hS'
  obtain ⟨V, -, hV⟩ := exists_translationSubgroup hH hIH h3 hU' hCH eH hUn hL' rfl rfl P
    (hS'.subset.trans hΔP) hPS'
  exact hV.false_of_isBenderGroup_commutator hH hs h3 h4' hU' hCH eH hUn hL' rfl rfl
    (hV.isBenderGroup_commutator hH hs h3 h4' hU' hCH eH hUn hL' rfl rfl)

end CFSG.OddTranspositions.PartThree.Nine
