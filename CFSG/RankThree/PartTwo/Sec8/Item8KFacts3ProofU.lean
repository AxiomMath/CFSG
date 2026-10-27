module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res11ProofOmega
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofUFix
import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofOmegaD4
import CFSG.RankThree.PartTwo.Sec8.Item82OneProofCases
import CFSG.RankThree.PartTwo.KFacts.K71Item89

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (thetaQuotMulAut compAction InducesOuterTheta)
open CFSG.RankThree.PartTwo.KFacts (IsInnerAut OutThreeCyclic psuConj stdPinnedPSU3
  stdPinnedPSU3_separated)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projSL projSU)


namespace Item8KFacts3U

theorem unitaryModel_of_isUnitaryTwo {G : Type} [Group G] [Finite G] {L : Subgroup G} {x : G}
    {m : ℕ} (hm : 1 ≤ m) (hU : IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) (3 * m))
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1)
    (hk : KFacts.InducesStdKind L x .field ∨ KFacts.InducesStdKind L x .graphField) :
    UnitaryModel (L ⧸ aschbacherSolvableCore 3 L) m
      (thetaQuotMulAut L (compAction L ⟨x, hxN⟩)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hout : InducesOuterTheta x L := by
    rcases hk with hk | hk
    · exact KFacts.InducesStdKind.inducesOuterTheta L hk (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta L hk (by decide)
  have h3m : 1 ≤ 3 * m := by omega
  have hq : 2 < 2 ^ (3 * m) :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * m))
  have hpsu : ∀ e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSU 3 2 (3 * m),
      UnitaryModel (L ⧸ aschbacherSolvableCore 3 L) m
        (thetaQuotMulAut L (compAction L ⟨x, hxN⟩)) := by
    intro e₁
    have hU₀ := Sec4.unitaryFieldData_galoisField 2 (3 * m) h3m
    set E₀ := e₁.trans (Sec4.projSUEquivUnitaryPSU 2 (3 * m) hU₀)
    rcases Nat.even_or_odd m with hme | hmo
    · have hq3 := Item82OneProof.two_pow_mod_three_of_even (hme.mul_left 3)
      rcases KFacts.inducesKindPSU3_diagonal_or_field (h := hU₀) L hq hx3 hout E₀ with hd | hf
      · exact (Sec4.false_of_inducesKind_diagonal (Sec4.psu3_inndiag_cube (by omega)) hd
          hx3).elim
      · obtain ⟨_, hf⟩ := hf
        exact unitaryModel_of_psu hU₀ hq E₀
          ((stdPinnedPSU3_separated hU₀).not_mem_inndiag_of_isField hf)
    · have hmo3 : Odd (3 * m) := Nat.odd_mul.mpr ⟨by decide, hmo⟩
      have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
        KFacts.center_eq_bot_of_mulEquiv_fwd E₀.symm (KFacts.center_unitaryPSU_three_eq_bot hU₀ hq)
      have hcard : Nat.card (L ⧸ aschbacherSolvableCore 3 L) =
          CFSG.Open.ordTwistedA 2 (2 ^ (3 * m)) :=
        (Nat.card_congr e₁.toEquiv).trans (KFacts.card_projSU_three_two h3m)
      have hodd := KFacts.not_oddCharStdModel_of_mulEquiv_projSU (by omega : 2 ≤ 3 * m) e₁
      rcases hk with hk | hk
      · rcases KFacts.inducesKindPSU3_or_oddCharStdModel hmo3 hcard hZ hk with
          ⟨K, _, hK, hqK, E, _, hf⟩ | hO
        · exact unitaryModel_of_psu hK hqK E
            ((stdPinnedPSU3_separated hK).not_mem_inndiag_of_isField hf)
        · exact (hodd hO).elim
      · rcases KFacts.inducesKindPSU3_or_oddCharStdModel hmo3 hcard hZ hk with
          ⟨K, _, hK, -, hkK⟩ | hO
        · exact (KFacts.not_inducesKindPSU3_graphField hK hkK).elim
        · exact (hodd hO).elim
  rcases hU with ⟨⟨e₁⟩⟩ | hS
  · exact hpsu e₁
  · rcases Nat.even_or_odd m with hme | hmo
    · obtain ⟨K, _, _, hK, ⟨e₁⟩⟩ := hS
      obtain ⟨e₂⟩ := Item82OneProof.nonempty_statedSU_mulEquiv_projSU h3m
        (Item82OneProof.two_pow_mod_three_of_even (hme.mul_left 3)) hK
      exact hpsu (e₁.trans e₂)
    · have h3 := KFacts.three_dvd_two_pow_three_mul_add_one hmo
      rcases hk with hk | hk
      · obtain ⟨K, _, hK, hqK, E, _, hf⟩ :=
          KFacts.inducesKindSU3_of_inducesStdKind (by omega) h3 hS hk
        exact unitaryModel_of_su hK hqK E
          ((stdPinnedPSU3_separated hK).not_mem_inndiag_of_isField hf)
      · exact (KFacts.not_inducesStdKind_graphField_of_isoSUThree (by omega) h3 hS hk).elim

end Item8KFacts3U


open Item8KFacts3U

theorem kF89OmegaFixInvUnitary_of (h45 : Sec4.Item4_5) : KF89OmegaFixInvUnitary := by
  intro G _ _ A c L a b X n h p hp hUk w hw hwe
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hU⟩ := hUk
  obtain ⟨e, Le⟩ := p
  obtain ⟨heA, he1, hLe, ⟨x, hxA, hxk⟩, -, ⟨d, m, hdm⟩⟩ := hp
  have hAel := h.mem_partTwoF.1
  have h3 : ∀ u ∈ A, u ^ 3 = 1 := hAel.2
  have hA3 : IsPGroup 3 A := fun u => ⟨1, Subtype.ext (by simpa using h3 u u.2)⟩
  have hAe : A ≤ Subgroup.centralizer ({e} : Set G) := fun z hz =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAel.1.is_comm.comm ⟨z, hz⟩ ⟨e, heA⟩))
  have hAN : A ≤ Subgroup.normalizer (Le : Set G) :=
    Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp (h3 e heA) he1
      hA3 hAe Le hLe
  have hdA := hdm.1
  have hdN := hAN hdA
  have hd3 := h3 d hdA
  have hxN := hAN hxA
  have hm1 : 1 ≤ m := Item86ResProof.one_le_of_isGammaIndex hdm
  have hU3 := isUnitaryTwo_three_mul_of_isGammaIndex hdm hU
  obtain ⟨ι⟩ := Item86ResProof.projSL_of_isGammaIndex_of_isUnitaryTwo hdm hU3
  have himg := KFacts.imageModTheta_perfectResidual_centralizer_eq hdN
    ⟨1, by rw [pow_one]; exact hd3⟩
  have hxout : InducesOuterTheta x Le := by
    rcases hxk with hk | hk
    · exact KFacts.InducesStdKind.inducesOuterTheta Le hk (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta Le hk (by decide)
  set ρ : A →* MulAut (Le ⧸ aschbacherSolvableCore 3 Le) :=
    (thetaQuotMulAut Le).comp ((compAction Le).comp (Subgroup.inclusion hAN))
  have hρapply : ∀ y : A, ρ y = thetaQuotMulAut Le (compAction Le ⟨y, hAN y.2⟩) := fun y => rfl
  have hekr : ρ ⟨e, heA⟩ = 1 := by
    rw [hρapply]
    have h1 : compAction Le ⟨e, hAN heA⟩ = 1 := by
      refine MulEquiv.ext fun z => Subtype.ext ?_
      change e * (z : G) * e⁻¹ = (z : G)
      have hze : (z : G) * e = e * z :=
        Subgroup.mem_centralizer_singleton_iff.mp
          (le_centralizer_of_mem_thetaComponentsAt_three hLe z.2)
      rw [← hze, mul_inv_cancel_right]
    rw [h1, map_one]
  have hwA : w ∈ A := hw.1
  have hwkr : ρ ⟨w, hwA⟩ = 1 := by
    rw [hρapply, Item812Res8.thetaQuotMulAut_eq_one_of_mem_sectionCentralizer hw (hAN hwA)]
  have hR9 : Nat.card ρ.range ≤ 9 :=
    Item812Res11.card_range_le_nine h.card_eq ρ (Subtype.ext (by simpa using h3 e heA))
      (fun h1 => he1 (by simpa using congrArg Subtype.val h1)) hekr hwkr
      (fun hmem => hwe (by
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
        exact ⟨j, by simpa using congrArg Subtype.val hj⟩))
  have hRc : ∀ β ∈ ρ.range, ∀ γ ∈ ρ.range, β * γ = γ * β := by
    rintro _ ⟨y, rfl⟩ _ ⟨y', rfl⟩
    rw [← map_mul, ← map_mul, hAel.1.is_comm.comm y y']
  have hR3 : ∀ β ∈ ρ.range, β ^ 3 = 1 := by
    rintro _ ⟨y, rfl⟩
    rw [← map_pow, show y ^ 3 = 1 from Subtype.ext (by simpa using h3 y y.2), map_one]
  set α := ρ ⟨x, hxA⟩
  have hαR : α ∈ ρ.range := ⟨_, rfl⟩
  have hαout : ¬ IsInnerAut α := hxout.2
  have hα3 : α ^ 3 = 1 := hR3 α hαR
  have hQ := Sec6.isQuasisimple_of_mem_thetaComponentsAt hLe
  have hO : OutThreeCyclic (Le ⧸ aschbacherSolvableCore 3 Le) := by
    rcases hU3 with ⟨⟨e₁⟩⟩ | ⟨K, _, _, hK, ⟨e₁⟩⟩
    · exact KFacts.outThreeCyclic_of_projSU hQ (by omega) e₁
    · exact KFacts.outThreeCyclic_of_statedSU hQ (by omega) hK e₁
  have htri := trichotomy_of_outThreeCyclic hO ρ.range hRc hR3 hαR hαout
  obtain ⟨K, _, hK, hq, D, π, hDin, hπ, hker, hαD⟩ :=
    unitaryModel_of_isUnitaryTwo hm1 hU3 hxN (h3 x hxA) hxk
  replace hαD : D α ∉ (psuConj hK).range := hαD
  set δ := ρ ⟨d, hdA⟩
  have hδR : δ ∈ ρ.range := ⟨_, rfl⟩
  have hFd : Sec4.autFix δ = barCentralizer (Subgroup.zpowers d) Le :=
    (Sec4.barCentralizer_zpowers_eq_autFix hdN).symm
  set Sd := inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers d) Le) with hSd
  have ψd : Sd ≃* projSL 2 (GaloisField 2 (3 * m)) := (MulEquiv.subgroupCongr himg.symm).trans ι
  have hSdfix : ∀ s ∈ Sd, δ s = s := fun s hs => by
    have hs' : s ∈ barCentralizer (Subgroup.zpowers d) Le := Subgroup.map_subtype_le _ hs
    rw [← hFd] at hs'
    exact hs'
  have hZd : Subgroup.center Sd = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    exact Sec21.eq_one_of_forall_commute_of_mulEquiv_projSL ψd fun t =>
      Subgroup.mem_center_iff.mp hz t
  have hcardd : Nat.card Sd = 2 ^ (3 * m) * ((2 ^ (3 * m)) ^ 2 - 1) := by
    rw [Nat.card_congr ψd.toEquiv, Sec21.card_projSL_two _ (by omega)]
  have hδin : IsInnerAut δ := by
    rcases htri δ hδR with hin | hin | hin
    · exact hin
    · exfalso
      obtain ⟨g, hg⟩ := hin
      refine false_of_forall_fixed_of_model hm1 hq hπ hker (hR3 δ hδR) (fun hmem => hαD ?_)
        hSdfix hZd hcardd
      have he : D α = (D (MulAut.conj g))⁻¹ * D δ := by
        rw [hg, map_mul, map_inv]
        group
      rw [he]
      exact mul_mem (inv_mem (hDin g)) hmem
    · exfalso
      obtain ⟨g, hg⟩ := hin
      refine false_of_forall_fixed_of_model hm1 hq hπ hker (hR3 δ hδR) (fun hmem => hαD ?_)
        hSdfix hZd hcardd
      have he : D α = (D δ)⁻¹ * D (MulAut.conj g) := by
        rw [hg, map_mul]
        group
      rw [he]
      exact mul_mem (inv_mem hmem) (hDin g)
  obtain ⟨w₀, hw₀⟩ := hδin
  have hc1 : MulAut.conj w₀ ≠ 1 := by
    intro h1
    rw [hw₀] at h1
    have hC : barCentralizer (Subgroup.zpowers d) Le = ⊤ := by
      rw [← hFd]
      refine eq_top_iff.mpr fun z _ => ?_
      rw [Sec4.mem_autFix, h1]
      rfl
    have hperf : Group.IsPerfect (Le ⧸ aschbacherSolvableCore 3 Le) := hQ.1
    have hcard : Nat.card (Le ⧸ aschbacherSolvableCore 3 Le) =
        2 ^ (3 * m) * ((2 ^ (3 * m)) ^ 2 - 1) := by
      rw [← hcardd, hSd, hC, inSubgroup,
        Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
        KFacts.perfectResidual_eq_top_of_isPerfect
          (hperf.ofSurjective (f := (Subgroup.topEquiv).symm.toMonoidHom)
            (MulEquiv.surjective _)),
        Subgroup.card_top, Subgroup.card_top]
    have hodd2 : Odd ((2 ^ (3 * m)) ^ 2 - 1) := by
      have h1 : 1 ≤ (2 ^ (3 * m)) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      have h2 : Even ((2 ^ (3 * m)) ^ 2) := by
        rw [← pow_mul]
        exact Nat.even_pow.mpr ⟨even_two, by omega⟩
      exact Nat.Even.sub_odd h1 h2 odd_one
    have hSig : Item86ResProof.SigU (Le ⧸ aschbacherSolvableCore 3 Le) m := by
      rcases hU3 with ⟨⟨e₁⟩⟩ | hS
      · exact Item86ResProof.sigU_of_unitarySig
          (Item86ResProof.unitarySig_of_projSU (by omega) e₁)
      · exact Item86ResProof.sigU_of_unitarySig
          (Item86ResProof.unitarySig_of_isoSUThree (by omega) hS)
    exact hSig.profile.ne_of_ne hodd2 (by omega) hcard
  have hαw : α * MulAut.conj w₀ = MulAut.conj w₀ * α := by
    rw [hw₀]
    exact hRc α hαR δ hδR
  have hCw : barCentralizer (Subgroup.zpowers d) Le =
      Subgroup.centralizer ({w₀} : Set (Le ⧸ aschbacherSolvableCore 3 Le)) := by
    rw [← hFd, ← hw₀]
    exact Item812Res8.autFix_conj_eq_centralizer w₀
  have ψ : perfectResidual (Subgroup.centralizer ({w₀} : Set (Le ⧸ aschbacherSolvableCore 3 Le)))
      ≃* projSL 2 (GaloisField 2 (3 * m)) :=
    (Item812Res8.perfectResidualCongr (MulEquiv.subgroupCongr hCw)).symm.trans
      ((Item812Res8.inSubgroupPerfectResidualEquiv _).symm.trans ψd)
  obtain ⟨v, hv1, hv2, hαv, hvw⟩ :=
    exists_fixed_involution_of_model hm1 hq hDin hπ hker hα3 hαD hαw ψ
  have hw₀R : MulAut.conj w₀ ∈ ρ.range := by
    rw [hw₀]
    exact hδR
  have hfix := fixed_of_trichotomy_conj' ρ.range hRc hR3 hR9 hαR hαout htri hw₀R hc1 hαv hvw
  exact ⟨v, orderOf_eq_prime hv2 hv1, fun u hu huA => hfix _ ⟨⟨u, huA⟩, rfl⟩⟩

end CFSG.RankThree.PartTwo.Sec8
