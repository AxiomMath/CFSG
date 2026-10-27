module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res11ProofU38
import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofGammaInner
import CFSG.RankThree.PartTwo.Sec8.Item87ProofOrders

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (thetaQuotMulAut compAction InducesOuterTheta)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial


theorem u38_centralizer_facts {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} {a b : G} {X : Subgroup G} {n : ℕ} (h : Sec8Pair G A c L a b X n)
    (h3 : IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3)
    (haN : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : a ^ 3 = 1) :
    Nat.card (barCentralizer (Subgroup.zpowers a) L) = 216 ∧
      (∃ u ∈ barCentralizer (Subgroup.zpowers a) L, u ^ 4 = 1 ∧ u ^ 2 ≠ 1) ∧
      Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L) := by
  classical
  have hq8 : 2 < 2 ^ 3 := by norm_num
  have hwit : ∀ {M : Type} [Group M], Item812Res11.U38Witness M →
      ∃ u : M, u ^ 4 = 1 ∧ u ^ 2 ≠ 1 := by
    rintro M _ ⟨u, s, hu, -, -, hw1⟩
    refine ⟨u, hu, fun hu2 => hw1 ?_⟩
    rw [hu2]
    simp
  rcases h3 with ⟨⟨e₁⟩⟩ | hS
  ·
    have hU : UnitaryFieldData 2 3 (GaloisField 2 (2 * 3)) :=
      ⟨Nat.prime_two, by norm_num, GaloisField.card 2 (2 * 3) (by norm_num)⟩
    set E := e₁.trans (Sec4.projSUEquivUnitaryPSU 2 3 hU) with hE
    have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
      KFacts.center_eq_bot_of_mulEquiv_fwd E.symm (KFacts.center_unitaryPSU_three_eq_bot hU hq8)
    have hcard : Nat.card (L ⧸ aschbacherSolvableCore 3 L) = CFSG.Open.ordTwistedA 2 (2 ^ 3) :=
      (Nat.card_congr e₁.toEquiv).trans (KFacts.card_projSU_three_two (by norm_num))
    have hodd := KFacts.not_oddCharStdModel_of_mulEquiv_projSU (by norm_num : 2 ≤ 3) e₁
    have hPa : IsoPGUThree (barCentralizer (Subgroup.zpowers a) L) (2 ^ 1) := by
      rcases h.inducesStdKind with hk | hk
      · rcases KFacts.inducesKindPSU3_or_oddCharStdModel (by decide : Odd 3) hcard hZ hk with
          ⟨K, _, hK, hq, hkK⟩ | hO
        · obtain ⟨f₀, hf₀, hC⟩ := KFacts.isoPGUThree_barCentralizer_of_field hq ha3 hkK
          obtain rfl : f₀ = 1 := by omega
          exact hC
        · exact (hodd hO).elim
      · rcases KFacts.inducesKindPSU3_or_oddCharStdModel (by decide : Odd 3) hcard hZ hk with
          ⟨K, _, hK, -, hkK⟩ | hO
        · exact (KFacts.not_inducesKindPSU3_graphField hK hkK).elim
        · exact (hodd hO).elim
    have hCa : Nat.card (barCentralizer (Subgroup.zpowers a) L) = 216 := by
      rw [Item812Res8.card_of_isoPGUThree le_rfl hPa]
      norm_num
    have hW : Item812Res11.U38Witness (barCentralizer (Subgroup.zpowers a) L) := by
      obtain ⟨K₀, _, _, hK₀, ⟨ψ⟩⟩ := hPa
      have hU₀ : UnitaryFieldData 2 1 K₀ := ⟨Nat.prime_two, le_rfl, by rw [hK₀]; norm_num⟩
      exact (Item812Res11.u38Witness_pgu hU₀).of_mulEquiv ψ
    have hperf : Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L) := by
      have := KFacts.isPerfect_unitarySU_three hU hq8
      have hP : Group.IsPerfect (unitaryPSU hU 3) :=
        Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (unitaryScalars hU 3))
          (QuotientGroup.mk'_surjective _)
      exact Group.IsPerfect.ofSurjective (f := E.symm.toMonoidHom) E.symm.surjective
    obtain ⟨u, hu4, hu2⟩ := hwit hW
    exact ⟨hCa, ⟨u, u.2, by rw [← Subgroup.coe_pow, hu4, Subgroup.coe_one], fun h1 =>
      hu2 (Subtype.ext (by rw [Subgroup.coe_pow, h1, Subgroup.coe_one]))⟩, hperf⟩
  ·
    obtain ⟨K, _, _, hK, ⟨eS⟩⟩ := id hS
    have hU : UnitaryFieldData 2 3 K := ⟨Nat.prime_two, by norm_num, by rw [hK]; norm_num⟩
    set eK : L ⧸ aschbacherSolvableCore 3 L ≃* unitarySU 2 3 K 3 := eS with heK
    have hSa : IsoSUThree (barCentralizer (Subgroup.zpowers a) L) (2 ^ 1) := by
      rcases h.inducesStdKind with hk | hk
      · exact KFacts.isoSUThree_barCentralizer_of_inducesStdKind (n := 1) odd_one hS ha3 hk
      · exact (KFacts.not_inducesStdKind_graphField_of_isoSUThree (m := 3) (by norm_num)
          (by norm_num) hS hk).elim
    have hCa : Nat.card (barCentralizer (Subgroup.zpowers a) L) = 216 := by
      rw [Item812Res8.card_of_isoSUThree hSa]
      norm_num
    have hW : Item812Res11.U38Witness (barCentralizer (Subgroup.zpowers a) L) := by
      obtain ⟨K₀, _, _, hK₀, ⟨ψ⟩⟩ := hSa
      have hU₀ : UnitaryFieldData 2 1 K₀ := ⟨Nat.prime_two, le_rfl, by rw [hK₀]; norm_num⟩
      exact (Item812Res11.u38Witness_statedSU hU₀).of_mulEquiv ψ
    have hperf : Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L) := by
      have := KFacts.isPerfect_unitarySU_three hU hq8
      exact Group.IsPerfect.ofSurjective (f := eK.symm.toMonoidHom) eK.symm.surjective
    obtain ⟨u, hu4, hu2⟩ := hwit hW
    exact ⟨hCa, ⟨u, u.2, by rw [← Subgroup.coe_pow, hu4, Subgroup.coe_one], fun h1 =>
      hu2 (Subtype.ext (by rw [Subgroup.coe_pow, h1, Subgroup.coe_one]))⟩, hperf⟩

theorem u38_pair_data (h45 : Sec4.Item4_5) {G : Type} [Group G] [Finite G] {A : Subgroup G}
    {c : G} {L : Subgroup G} {a b : G} {X : Subgroup G} {n : ℕ} (h : Sec8Pair G A c L a b X n)
    (h3 : IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3) :
    ∃ (haN : a ∈ Subgroup.normalizer (L : Set G)) (hbN : b ∈ Subgroup.normalizer (L : Set G)),
      a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a * b = b * a ∧ InducesOuterTheta a L ∧
      Nat.card (barCentralizer (Subgroup.zpowers a) L) = 216 ∧
      (∃ u ∈ barCentralizer (Subgroup.zpowers a) L, u ^ 4 = 1 ∧ u ^ 2 ≠ 1) ∧
      thetaQuotMulAut L (compAction L ⟨b, hbN⟩) ≠ 1 ∧
      7 ∣ Nat.card (barCentralizer (Subgroup.zpowers b) L) ∧
      Odd (Nat.card ((aschbacherSolvableCore 3 L).map L.subtype)) := by
  classical
  have hAab := h.mem_partTwoF.1
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have haA : a ∈ A := h.a_mem
  have ha3 : a ^ 3 = 1 := hAab.2 a haA
  have hbA : b ∈ A := h.isGammaIndex.1
  have hb3 : b ^ 3 = 1 := hAab.2 b hbA
  have hcA : c ∈ A := h.mem_A
  have hc1 : c ≠ 1 := h.ne_one
  have hc3 : c ^ 3 = 1 := hAab.2 c hcA
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAab.2 g g.2)⟩
  have hAcC : A ≤ Subgroup.centralizer ({c} : Set G) := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu c hcA)
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp hc3 hc1 hAp hAcC L
      h.mem_thetaComponentsAt
  have haN := hAL haA
  have hbN := hAL hbA
  have haL : InducesOuterTheta a L := by
    rcases h.inducesStdKind with hk | hk
    · exact KFacts.InducesStdKind.inducesOuterTheta L hk (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta L hk (by decide)
  obtain ⟨hCa, hu4, hperf⟩ := u38_centralizer_facts h h3 haN ha3
  have hn1 : 1 ≤ n := h.isGammaIndex.2.2.1
  have hU3n := isUnitaryTwo_three_mul_of_isGammaIndex h.isGammaIndex h3
  have hn : n = 1 := by
    have := Item812Res10.eq_of_isUnitaryTwo (by norm_num) (by omega) h3 hU3n
    omega
  subst hn
  obtain ⟨ι⟩ := Item86ResProof.projSL_of_isGammaIndex_of_isUnitaryTwo h.isGammaIndex h3
  have hK504 : Nat.card (imageModTheta L
      (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)))) = 504 := by
    rw [Nat.card_congr ι.toEquiv, Item87Proof.card_projSL_two_three le_rfl]
    norm_num
  have h504 : 504 ∣ Nat.card (barCentralizer (Subgroup.zpowers b) L) := by
    rw [← hK504, KFacts.imageModTheta_perfectResidual_centralizer_eq hbN
      ⟨1, by rw [pow_one]; exact hb3⟩]
    exact Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _)
  refine ⟨haN, hbN, ha3, hb3, hAc a haA b hbA, haL, hCa, hu4, ?_, ?_, ?_⟩
  · intro h1
    have hL := Item812Res11.card_imageModTheta_eq_of_trivial hbN hb3 h1 hperf
    rw [hK504] at hL
    have h216 : 216 ∣ Nat.card (L ⧸ aschbacherSolvableCore 3 L) := by
      rw [← hCa]
      exact Subgroup.card_subgroup_dvd_card _
    rw [← hL] at h216
    norm_num at h216
  · exact (by norm_num : 7 ∣ 504).trans h504
  · have hθ3 : ¬ 3 ∣ Nat.card ((aschbacherSolvableCore 3 L).map L.subtype) := by
      rw [Subgroup.card_map_of_injective L.subtype_injective]
      exact KFacts.not_three_dvd_card_aschbacherSolvableCore L
    exact odd_card_of_le_normalizer h.toTheoremFourHyp.localRank_three.le hAab h.card_eq hθ3
      (hAL.trans (KFacts.normalizer_le_normalizer_theta L))

theorem u38_K_card {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} {a b : G} {X : Subgroup G} {n : ℕ} (h : Sec8Pair G A c L a b X n)
    (h3 : IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3) :
    Nat.card (imageModTheta L
      (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)))) = 504 := by
  have hn1 : 1 ≤ n := h.isGammaIndex.2.2.1
  have hU3n := isUnitaryTwo_three_mul_of_isGammaIndex h.isGammaIndex h3
  have hn : n = 1 := by
    have := Item812Res10.eq_of_isUnitaryTwo (by norm_num) (by omega) h3 hU3n
    omega
  subst hn
  obtain ⟨ι⟩ := Item86ResProof.projSL_of_isGammaIndex_of_isUnitaryTwo h.isGammaIndex h3
  rw [Nat.card_congr ι.toEquiv, Item87Proof.card_projSL_two_three le_rfl]
  norm_num

theorem u38_n_eq_one {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} {a b : G} {X : Subgroup G} {n : ℕ} (h : Sec8Pair G A c L a b X n)
    (h3 : IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3) : n = 1 := by
  have hn1 : 1 ≤ n := h.isGammaIndex.2.2.1
  have hU3n := isUnitaryTwo_three_mul_of_isGammaIndex h.isGammaIndex h3
  have := Item812Res10.eq_of_isUnitaryTwo (by norm_num) (by omega) h3 hU3n
  omega

end CFSG.RankThree.PartTwo.Sec8
