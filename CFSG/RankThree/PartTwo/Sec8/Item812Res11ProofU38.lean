module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res10ProofUnitary
public import CFSG.RankThree.PartTwo.Sec8.Item812Res11ProofU38Core
public import CFSG.RankThree.PartTwo.Sec8.Item812Res11ProofU38Mat
import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofGammaInner
import CFSG.RankThree.PartTwo.Sec8.Item87ProofOrders
import CFSG.RankThree.PartTwo.KFacts.K71Item89

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (thetaQuotMulAut compAction)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

namespace Item812Res11

theorem eq_one_of_psuConj_of_fixed {f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)
    (hf : Odd f) (hq : 2 < 2 ^ f) {A : KFacts.unitaryIsom3 h}
    (hA3 : KFacts.psuConj h A ^ 3 = 1) {y : unitaryPSU h 3} (hy : KFacts.psuConj h A y = y)
    (hy4 : y ^ 4 = 1) (hy2 : y ^ 2 ≠ 1) : KFacts.psuConj h A = 1 := by
  have hA3' : KFacts.suConj h A ^ 3 = 1 :=
    KFacts.eq_of_suDescend_eq h hq (by rw [map_pow, KFacts.suDescend_suConj, hA3, map_one])
  obtain ⟨T, rfl⟩ := QuotientGroup.mk_surjective y
  have hZ3 : ∀ z ∈ unitaryScalars h 3, z ^ 3 = 1 := by
    rintro z ⟨c, -, hc3, hzc⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow, hzc, ← map_pow, hc3, map_one, Subgroup.coe_one]
  have hZc : ∀ z ∈ unitaryScalars h 3, ∀ g : unitarySU 2 f F 3, g * z = z * g :=
    fun z hz g => Subgroup.mem_center_iff.mp (unitaryScalars_le_center h 3 hz) g
  have hZfix : ∀ z ∈ unitaryScalars h 3, KFacts.suConj h A z = z := by
    rintro z ⟨c, -, -, hzc⟩
    apply Subtype.ext
    rw [KFacts.coe_suConj, hzc, Subgroup.coe_inv, (commute_scalar c _).eq, mul_inv_cancel_right]
  have hT4 : T ^ 4 ∈ unitaryScalars h 3 := by
    have h1 : ((T ^ 4 : unitarySU 2 f F 3) : unitaryPSU h 3) = 1 := by
      rw [QuotientGroup.mk_pow, hy4]
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hμ3 : (T ^ 4) ^ 3 = 1 := hZ3 _ hT4
  have hμ2 : (T ^ 4) ^ 2 ∈ unitaryScalars h 3 := Subgroup.pow_mem _ hT4 2
  set T' : unitarySU 2 f F 3 := T * (T ^ 4) ^ 2 with hT'
  have hT'4 : T' ^ 4 = 1 := by
    have hc : Commute T ((T ^ 4) ^ 2) := hZc _ hμ2 T
    rw [hT', hc.mul_pow, ← pow_mul, ← pow_succ', show 2 * 4 + 1 = 3 * 3 by rfl, pow_mul, hμ3,
      one_pow]
  have hT'proj : (T' : unitaryPSU h 3) = (T : unitaryPSU h 3) := by
    rw [hT', QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hμ2, mul_one]
  have hfix : ((KFacts.suConj h A T : unitarySU 2 f F 3) : unitaryPSU h 3) =
      (T : unitaryPSU h 3) := by
    rw [← KFacts.psuConj_mk]
    exact hy
  have hz₀ : T⁻¹ * KFacts.suConj h A T ∈ unitaryScalars h 3 := QuotientGroup.eq.mp hfix.symm
  obtain ⟨z₀, hz₀m, hAT⟩ : ∃ z₀ ∈ unitaryScalars h 3, KFacts.suConj h A T = T * z₀ :=
    ⟨_, hz₀, by rw [mul_inv_cancel_left]⟩
  have hAT' : KFacts.suConj h A T' = T' * z₀ := by
    rw [hT', map_mul, hAT, hZfix _ hμ2, mul_assoc, mul_assoc, hZc z₀ hz₀m]
  have hz₀1 : z₀ = 1 := by
    have h1 : (KFacts.suConj h A T') ^ 4 = 1 := by rw [← map_pow, hT'4, map_one]
    have hc : Commute T' z₀ := hZc z₀ hz₀m T'
    rw [hAT', hc.mul_pow, hT'4, one_mul, pow_succ, hZ3 z₀ hz₀m, one_mul] at h1
    exact h1
  have hfixT' : KFacts.suConj h A T' = T' := by rw [hAT', hz₀1, mul_one]
  have hT'2 : T' ^ 2 ≠ 1 := by
    intro h1
    apply hy2
    calc (T : unitaryPSU h 3) ^ 2 = (T' : unitaryPSU h 3) ^ 2 := by rw [hT'proj]
      _ = ((T' ^ 2 : unitarySU 2 f F 3) : unitaryPSU h 3) := by rw [QuotientGroup.mk_pow]
      _ = 1 := by rw [h1, QuotientGroup.mk_one]
  have hc1 := Item8KFacts2Proof.eq_one_of_suConj_of_fixed h hf hA3' hfixT' hT'4 hT'2
  rw [← KFacts.suDescend_suConj h hq, hc1, map_one]

variable {G : Type} [Group G] [Finite G]

theorem exists_not_mem_theta_of_u38Witness {L : Subgroup G} {a b : G}
    (haN : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : a ^ 3 = 1)
    (hU3 : IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3)
    (hbN : b ∈ Subgroup.normalizer (L : Set G))
    (hbI : b ∈ Subgroup.normalizer (sec8I L a : Set G)) (hb3 : b ^ 3 = 1)
    (hW : U38Witness (barCentralizer (Subgroup.zpowers a) L))
    (hB : ∀ z ∈ barCentralizer (Subgroup.zpowers b) L, z ^ 4 = 1 → z ^ 2 = 1) :
    ∃ i ∈ sec8I L a, b * i * b⁻¹ * i⁻¹ ∉
      ((aschbacherSolvableCore 3 ↥(sec8I L a)).map (sec8I L a).subtype : Subgroup G) := by
  obtain ⟨u, s, hu4, hs4, hw3, hw1⟩ := hW
  have hu4' : (u : L ⧸ aschbacherSolvableCore 3 L) ^ 4 = 1 := by
    rw [← Subgroup.coe_pow, hu4, Subgroup.coe_one]
  have hs4' : (s : L ⧸ aschbacherSolvableCore 3 L) ^ 4 = 1 := by
    rw [← Subgroup.coe_pow, hs4, Subgroup.coe_one]
  obtain ⟨t, ht⟩ := exists_mem_sec8I_of_pow_four haN ha3 hU3 u.2 hu4'
  obtain ⟨s', hs'⟩ := exists_mem_sec8I_of_pow_four haN ha3 hU3 s.2 hs4'
  have key : Item87Proof.modThetaHom sec8I_le_L t ^ 2 *
      (Item87Proof.modThetaHom sec8I_le_L s' * Item87Proof.modThetaHom sec8I_le_L t ^ 2 *
        (Item87Proof.modThetaHom sec8I_le_L s')⁻¹) =
      ((u ^ 2 * (s * u ^ 2 * s⁻¹) : barCentralizer (Subgroup.zpowers a) L) :
        L ⧸ aschbacherSolvableCore 3 L) := by
    rw [ht, hs']
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv]
  refine exists_not_mem_theta_of_witness sec8I_le_L hbN hbI hb3 t s' ?_ ?_ ?_ hB
  · rw [ht]
    exact hu4'
  · rw [key, ← Subgroup.coe_pow, hw3, Subgroup.coe_one]
  · rw [key]
    intro h1
    exact hw1 (Subtype.ext h1)

theorem card_imageModTheta_eq_of_trivial {L : Subgroup G} {b : G}
    (hbN : b ∈ Subgroup.normalizer (L : Set G)) (hb3 : b ^ 3 = 1)
    (h1 : thetaQuotMulAut L (compAction L ⟨b, hbN⟩) = 1)
    (hperf : Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L)) :
    Nat.card (imageModTheta L
        (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)))) =
      Nat.card (L ⧸ aschbacherSolvableCore 3 L) := by
  have htop : barCentralizer (Subgroup.zpowers b) L = ⊤ := by
    ext z
    simp only [Subgroup.mem_top, iff_true]
    rw [KFacts.mem_barCentralizer_zpowers_iff hbN, h1, MulAut.one_apply]
  rw [KFacts.imageModTheta_perfectResidual_centralizer_eq hbN ⟨1, by rw [pow_one]; exact hb3⟩,
    htop, inSubgroup, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  have hperf' : Group.IsPerfect (⊤ : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) :=
    Group.IsPerfect.ofSurjective
      (f := (Subgroup.topEquiv (G := L ⧸ aschbacherSolvableCore 3 L)).symm.toMonoidHom)
      (Subgroup.topEquiv (G := L ⧸ aschbacherSolvableCore 3 L)).symm.surjective
  rw [KFacts.perfectResidual_eq_top_of_isPerfect hperf', Subgroup.card_top, Subgroup.card_top]

end Item812Res11

open Item812Res11


theorem kF89BNotCentIU38_of (h45 : Sec4.Item4_5) : KF89BNotCentIU38 := by
  intro G _ _ A c L a b X n h h3
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
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
  have hAa : A ≤ Subgroup.centralizer ({a} : Set G) := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu a haA)
  have hbI : b ∈ Subgroup.normalizer (sec8I L a : Set G) :=
    Item812Res7.mem_normalizer_sec8I
      (Late.le_normalizer_inf hAL (hAa.trans Subgroup.le_normalizer) hbA)
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
  have hq8 : 2 < 2 ^ 3 := by norm_num
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
    have hW : U38Witness (barCentralizer (Subgroup.zpowers a) L) := by
      obtain ⟨K₀, _, _, hK₀, ⟨ψ⟩⟩ := hPa
      have hU₀ : UnitaryFieldData 2 1 K₀ := ⟨Nat.prime_two, le_rfl, by rw [hK₀]; norm_num⟩
      exact (u38Witness_pgu hU₀).of_mulEquiv ψ
    have hperf : Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L) := by
      have := KFacts.isPerfect_unitarySU_three hU hq8
      have hP : Group.IsPerfect (unitaryPSU hU 3) :=
        Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (unitaryScalars hU 3))
          (QuotientGroup.mk'_surjective _)
      exact Group.IsPerfect.ofSurjective (f := E.symm.toMonoidHom) E.symm.surjective
    set β := KFacts.inducedAutHom L E ⟨b, hbN⟩ with hβ
    have hβ3 : β ^ 3 = 1 := KFacts.inducedAutHom_pow_eq_one L E hbN hb3
    have hD : β ∈ (KFacts.psuConj hU).range := by
      by_contra hD
      have hfield := KFacts.isField_psu3_of_pow_three_eq_one hq8 hβ3 hD
      have hk : KFacts.InducesKindPSU3 hU L b .field :=
        ⟨E, hbN, (KFacts.PinnedAut.hasKind_field _).mpr hfield⟩
      obtain ⟨f₀, hf₀, hC⟩ := KFacts.isoPGUThree_barCentralizer_of_field hq8 hb3 hk
      obtain rfl : f₀ = 1 := by omega
      rw [Item812Res8.card_of_isoPGUThree le_rfl hC] at h504
      norm_num at h504
    obtain ⟨Am, hAm⟩ := hD
    have hB : ∀ z ∈ barCentralizer (Subgroup.zpowers b) L, z ^ 4 = 1 → z ^ 2 = 1 := by
      intro z hz hz4
      by_contra hz2
      have hzfix := (KFacts.mem_barCentralizer_zpowers_iff hbN z).mp hz
      have hy : KFacts.psuConj hU Am (E z) = E z := by
        rw [hAm, hβ]
        show E (thetaQuotMulAut L (compAction L ⟨b, hbN⟩) (E.symm (E z))) = E z
        rw [MulEquiv.symm_apply_apply, hzfix]
      have hy4 : (E z) ^ 4 = 1 := by rw [← map_pow, hz4, map_one]
      have hy2 : (E z) ^ 2 ≠ 1 := by
        rw [← map_pow]
        exact fun h1 => hz2 ((MulEquiv.map_eq_one_iff E).mp h1)
      have hAm3 : KFacts.psuConj hU Am ^ 3 = 1 := by rw [hAm]; exact hβ3
      have hβ1 : β = 1 := by
        rw [← hAm]
        exact eq_one_of_psuConj_of_fixed hU (by decide) hq8 hAm3 hy hy4 hy2
      have h1 : thetaQuotMulAut L (compAction L ⟨b, hbN⟩) = 1 := by
        have h2 : MulAut.congr E (thetaQuotMulAut L (compAction L ⟨b, hbN⟩)) = 1 := hβ1
        rwa [MulEquiv.map_eq_one_iff] at h2
      have hL := card_imageModTheta_eq_of_trivial hbN hb3 h1 hperf
      rw [hK504] at hL
      have h216 : 216 ∣ Nat.card (L ⧸ aschbacherSolvableCore 3 L) := by
        rw [← hCa]
        exact Subgroup.card_subgroup_dvd_card _
      rw [← hL] at h216
      norm_num at h216
    exact exists_not_mem_theta_of_u38Witness haN ha3 (Or.inl ⟨e₁⟩) hbN hbI hb3 hW hB
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
    have hW : U38Witness (barCentralizer (Subgroup.zpowers a) L) := by
      obtain ⟨K₀, _, _, hK₀, ⟨ψ⟩⟩ := hSa
      have hU₀ : UnitaryFieldData 2 1 K₀ := ⟨Nat.prime_two, le_rfl, by rw [hK₀]; norm_num⟩
      exact (u38Witness_statedSU hU₀).of_mulEquiv ψ
    have hperf : Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L) := by
      have := KFacts.isPerfect_unitarySU_three hU hq8
      exact Group.IsPerfect.ofSurjective (f := eK.symm.toMonoidHom) eK.symm.surjective
    set β := KFacts.inducedAutHom L eK ⟨b, hbN⟩ with hβ
    have hβ3 : β ^ 3 = 1 := KFacts.inducedAutHom_pow_eq_one L eK hbN hb3
    have hB : ∀ z ∈ barCentralizer (Subgroup.zpowers b) L, z ^ 4 = 1 → z ^ 2 = 1 := by
      intro z hz hz4
      by_contra hz2
      have hzfix := (KFacts.mem_barCentralizer_zpowers_iff hbN z).mp hz
      have hu : β (eK z) = eK z := by
        rw [hβ]
        show eK (thetaQuotMulAut L (compAction L ⟨b, hbN⟩) (eK.symm (eK z))) = eK z
        rw [MulEquiv.symm_apply_apply, hzfix]
      have hu4 : (eK z) ^ 4 = 1 := by rw [← map_pow, hz4, map_one]
      have hu2 : (eK z) ^ 2 ≠ 1 := by
        rw [← map_pow]
        exact fun h1 => hz2 ((MulEquiv.map_eq_one_iff eK).mp h1)
      by_cases hβ1 : β = 1
      · have h1 : thetaQuotMulAut L (compAction L ⟨b, hbN⟩) = 1 := by
          have h2 : MulAut.congr eK (thetaQuotMulAut L (compAction L ⟨b, hbN⟩)) = 1 := hβ1
          rwa [MulEquiv.map_eq_one_iff] at h2
        have hL := card_imageModTheta_eq_of_trivial hbN hb3 h1 hperf
        rw [hK504] at hL
        have h216 : 216 ∣ Nat.card (L ⧸ aschbacherSolvableCore 3 L) := by
          rw [← hCa]
          exact Subgroup.card_subgroup_dvd_card _
        rw [← hL] at h216
        norm_num at h216
      · have hfield := Item8KFacts2Proof.hasKind_field_of_fixed_order_four hU (by decide) hq8
          hβ3 hβ1 hu hu4 hu2
        have hk : KFacts.InducesStdKind L b .field := .su3 hU hq8 ⟨eK, hbN, hfield⟩
        have hC := KFacts.isoSUThree_barCentralizer_of_inducesStdKind (n := 1) odd_one hS hb3 hk
        rw [Item812Res8.card_of_isoSUThree hC] at h504
        norm_num at h504
    exact exists_not_mem_theta_of_u38Witness haN ha3 (Or.inr hS) hbN hbI hb3 hW hB

end CFSG.RankThree.PartTwo.Sec8
