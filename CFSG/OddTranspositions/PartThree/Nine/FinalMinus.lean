module

public import CFSG.OddTranspositions.PartThree.Nine.FinalLocal
public import CFSG.OddTranspositions.PartThree.Nine.FinalBender
public import CFSG.OddTranspositions.PartThree.Nine.Goldschmidt
public import CFSG.ClassicalInvolution.AschTight.StronglyClosed
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.WP1Section6
public import CFSG.ClassicalInvolution.AschTight.CSMD
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.GH74.GLS.Defs
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian_models
public import CFSG.Open.QuasithinDefs
public import CFSG.StronglyEmbedded.UniqueCoset
public import CFSG.Walter.J1Recog
public import CFSG.Walter.Ree.Thompson2.BaseFin
public import CFSG.Walter.ReeOrder.WardLocal
public import CFSG.Walter.W67.Section8.Prop83

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {D : Set G}


theorem minus_or_unitary_of_wcl_abelian (hC : HypothesisC D) (hH : Th91Hyp D hC)
    (hs : IsSimpleGroup (commutator G)) (h3 : Conclusion9_3 D hC)
    {T : Sylow 2 (Halpha D hC.alpha)} {S : Sylow 2 G}
    (h4 : Conclusion9_4 D hC T S) (h5 : Conclusion9_5 D hC T S)
    {Q : Subgroup G} (hQ : IsRegularCore ((S : Set G) ∩ D) Q)
    {U : Subgroup G} (hU : DeltaSetup hC T S U) {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1)
    (hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s)
    (hW : IsMulCommutative (CFSG.LargeExtraspecial.S11.wcl z)) :
    (∃ f : ℕ, 2 ≤ f ∧
        Nonempty (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSL2Model f) ∧
        Nonempty (↥(commutator G) ≃* PSL2Model (2 * f)) ∧ (commutator G).index = 2) ∨
      (∃ n : ℕ, 2 ≤ n ∧
        Nonempty (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSL2Model n) ∧
        Nonempty (↥(commutator G) ≃* PSU3Model n) ∧ (commutator G).index = 2 ∧
        hC.d ∉ commutator G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := commutator G with hKdef
  set L := CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) with hLdef
  obtain ⟨eL⟩ := nonempty_pResidualOf_mulEquiv h3 hU h5.1
  have hLB : IsBenderGroup L := isBenderGroup_of_mulEquiv eL hH.bender
  have hLK : L ≤ K := pResidualOf_le_commutator hH h3 hU h5.1
  have hLns : ¬ Group.IsSolvable L := by
    intro hsol
    obtain ⟨a, b, hab⟩ := IsBenderGroup.exists_not_commute hLB
    have hc := IsBenderGroup.commutator_eq_top hLB
    obtain ⟨n, hn⟩ := hsol.solvable
    have htop : ∀ k, derivedSeries L k = ⊤ := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [derivedSeries_succ, ih, ← commutator_def, hc]
    rw [htop n] at hn
    have ha : a = 1 := by
      have : a ∈ (⊥ : Subgroup L) := hn ▸ Subgroup.mem_top a
      exact this
    exact hab (by rw [ha]; exact Commute.one_left b)
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have huD : hC.d ∈ (S : Set G) ∩ D := hU.sylow_inter ▸ ⟨1, U.one_mem, mul_one _⟩
  have hzK : z ∈ K := mem_commutator_of_mem_omega hU hzU
  have hzS' : z ∈ (S : Subgroup G) := by
    have huz : hC.d * z ∈ (S : Set G) ∩ D := hU.sylow_inter ▸ ⟨z, hzU, rfl⟩
    have := (S : Subgroup G).mul_mem huD.1 huz.1
    rwa [← mul_assoc, hu2, one_mul] at this
  have hnonabK : ∃ a b : K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := IsBenderGroup.exists_not_commute hLB
    refine ⟨⟨a, hLK a.2⟩, ⟨b, hLK b.2⟩, fun h => hab ?_⟩
    have h' := congrArg (fun x : K => (x : G)) h
    exact Subtype.ext h'
  obtain ⟨P, hP⟩ := CFSG.DisconnectedInvolutionGraph.Helpers.normal_subgroup_sylow_intersection
    2 K S
  set z' : K := ⟨z, hzK⟩ with hz'
  have hz'P : z' ∈ (P : Subgroup K) := by
    rw [hP]
    exact Subgroup.mem_subgroupOf.mpr hzS'
  have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hz'c : ∀ x ∈ (P : Subgroup K), x * z' = z' * x := by
    intro x hx
    rw [hP, Subgroup.mem_subgroupOf] at hx
    exact Subtype.ext (hzS _ hx)
  have hW' : IsMulCommutative (CFSG.LargeExtraspecial.S11.wcl z') := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have ha := wcl_map_le z' (Subgroup.mem_map_of_mem _ a.2)
    have hb := wcl_map_le z' (Subgroup.mem_map_of_mem _ b.2)
    have h := congrArg Subtype.val (hW.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
    exact Subtype.ext h
  have hq4 : 4 ≤ Nat.card U := by
    obtain ⟨e, he, hcard⟩ := hU.exists_card
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hΔcard : ((S : Set G) ∩ D).ncard = Nat.card U := by
    rw [hU.sylow_inter, Set.ncard_image_of_injective _ (fun a b h => mul_left_cancel h),
      ← Nat.card_coe_set_eq]
    rfl
  have hQcard := card_regularCore_eq hQ huD
  rw [hΔcard, h5.1] at hQcard
  have hTcard := two_mul_card_le_card_sylow_map h3 hU
  have hQS := regularCore_le_sylow hQ S h4.2.1
  have hS32 : 32 ≤ Nat.card (S : Subgroup G) := by
    have h1 : Nat.card Q ≤ Nat.card (S : Subgroup G) := Subgroup.card_le_of_le hQS
    have h2 : 2 * Nat.card U * Nat.card U ≤ Nat.card Q := by
      rw [hQcard, mul_comm (Nat.card U)]
      exact Nat.mul_le_mul_right _ hTcard
    nlinarith
  have hP16 : 16 ≤ Nat.card (P : Subgroup K) := by
    have hrel := Subgroup.relIndex_mul_card (H := K) (K := (S : Subgroup G))
    have hidx : K.relIndex (S : Subgroup G) ≤ 2 :=
      (Nat.le_of_dvd (by
        have := Subgroup.index_ne_zero_of_finite (H := K)
        omega) (Subgroup.relIndex_dvd_index_of_normal (H := K) (K := (S : Subgroup G)))).trans
        hC.setup.index_commutator_le_two
    have hPeq : Nat.card (P : Subgroup K) = Nat.card (K ⊓ (S : Subgroup G) : Subgroup G) := by
      rw [hP, ← Subgroup.card_map_of_injective K.subtype_injective, Subgroup.subgroupOf_map_subtype,
        inf_comm]
    rw [hPeq]
    nlinarith
  have : IsSimpleGroup K := hs
  have hKB : IsBenderGroup K := isBenderGroup_of_wcl_abelian hnonabK P hz'P hz'1 hz'c hW' hP16
  have huK : hC.d ∉ K := by
    intro huK
    apply hLns
    have hord : orderOf (⟨hC.d, huK⟩ : K) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hC.setup.oddT.orderOf_eq_two hC.hd
    have hsol :=
      CFSG.ClassicalInvolution.Disconnected.AschTight.isSolvable_centralizer_of_isBenderGroup
        hKB hord
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
  have hidx : K.index = 2 := by
    have hle : K.index ≤ 2 := hC.setup.index_commutator_le_two
    have hne : K.index ≠ 1 := fun h => huK (Subgroup.index_eq_one.mp h ▸ Subgroup.mem_top _)
    have hpos := Subgroup.index_ne_zero_of_finite (H := K)
    omega
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
  have hLu : ∀ l ∈ L, Commute hC.d l := fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.mp
      (PartThree.Halpha_le_centralizer_d hC (Subgroup.map_subtype_le _ hl))).symm
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
  rcases outer_involution_fixed_cases hKB hKC hu2 huK hLK hLu hLn hLns with
    ⟨m, hm, ⟨eK⟩, ⟨eLm⟩⟩ | ⟨n, hn, ⟨eK⟩, ⟨eLn⟩⟩
  · exact Or.inl ⟨m, hm, ⟨eL.symm.trans eLm⟩, ⟨eK⟩, hidx⟩
  · exact Or.inr ⟨n, hn, ⟨eL.symm.trans eLn⟩, ⟨eK⟩, hidx, huK⟩

end CFSG.OddTranspositions.PartThree.Nine
