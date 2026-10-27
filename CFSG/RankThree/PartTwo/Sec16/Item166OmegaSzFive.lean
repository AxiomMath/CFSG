module

public import CFSG.RankThree.PartTwo.Sec16.Item166Res3ProofCtr
import CFSG.RankThree.PartTwo.Sec16.Item16KFactsProofNoSz
import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools
import CFSG.RankThree.PartTwo.Sec17.PropUCover
import CFSG.RankThree.PartTwo.Sec17.G1724Five
import CFSG.RankThree.PartTwo.Sec11.FixedCentralizer
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.Quasithin.Background.PRankCommuteMod
public import CFSG.RankThree.PartTwo.Sec16.Item166Res2ProofTheta

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise commutatorElement

namespace Proof166SzFive

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem exists_mem_thetaComponentsIn_of_suzukiModel
    {K₀ : Subgroup G} {m : ℕ}
    (hSz : CFSG.Blueprint.SuzukiModel (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) 2 m) :
    ∃ K ∈ thetaComponentsIn K₀,
      CFSG.Blueprint.SuzukiModel (↥K ⧸ aschbacherSolvableCore 3 ↥K) 2 m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q := ↥K₀ ⧸ CFSG.pCore 2 ↥K₀ with hQ
  have hsimpleQ : IsSimpleGroup Q := isSimpleGroup_of_suzukiModel hSz
  haveI : IsSimpleGroup Q := hsimpleQ
  have hperfQ : Group.IsPerfect Q := KSL3PiNoSzProof.isPerfect_of_suzukiModel hSz
  haveI : Group.IsPerfect Q := hperfQ
  have hnonabQ : ∃ a b : Q, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact (Group.IsPerfect.not_isSolvable Q) (Group.isSolvable_of_comm h)
  have hQq : CFSG.IsQuasisimple Q :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnonabQ).1
  have hcenterQ : Subgroup.center Q = ⊥ :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnonabQ).2
  have hθQ : aschbacherSolvableCore 3 Q = ⊥ := by
    refine CFSG.RankThree.PartTwo.Sec13.aschbacherSolvableCore_eq_bot_of_isQuasisimple hQq ?_
    rw [hcenterQ]
    exact IsPGroup.of_bot
  let π : ↥K₀ →* Q := QuotientGroup.mk' (CFSG.pCore 2 ↥K₀)
  have hπsurj : Function.Surjective π := by
    intro x
    exact QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K₀) x
  have htopQ : CFSG.perfectResidual Q = ⊤ := by
    refine top_le_iff.mp
      (CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidual
        (⊤ : Subgroup Q) ?_)
    exact Group.IsPerfect.top_iff.mpr hperfQ
  have hAmap : (CFSG.perfectResidual ↥K₀).map π = ⊤ :=
    (CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq π hπsurj).trans htopQ
  let f : ↥(CFSG.perfectResidual ↥K₀) →* Q :=
    π.comp (CFSG.perfectResidual ↥K₀).subtype
  have hfr : f.range = (CFSG.perfectResidual ↥K₀).map π := by
    rw [MonoidHom.range_eq_map]
    change (⊤ : Subgroup ↥(CFSG.perfectResidual ↥K₀)).map
      (π.comp (CFSG.perfectResidual ↥K₀).subtype) =
      (CFSG.perfectResidual ↥K₀).map π
    rw [← Subgroup.map_map (K := ⊤) (g := π)
      (f := (CFSG.perfectResidual ↥K₀).subtype), Subgroup.map_top,
      Subgroup.range_subtype]
  have hsurj : Function.Surjective f :=
    MonoidHom.range_eq_top.mp (by rw [hfr, hAmap])
  have hpCore2 : IsPGroup 2 (↥(CFSG.pCore 2 ↥K₀)) :=
    CFSG.pCore_isPGroup (p := 2) (G := ↥K₀)
  haveI : Group.IsNilpotent (↥(CFSG.pCore 2 ↥K₀)) := IsPGroup.isNilpotent hpCore2
  have hPsolv : Group.IsSolvable (↥(CFSG.pCore 2 ↥K₀)) := inferInstance
  have hP3 : ¬ 3 ∣ Nat.card (↥(CFSG.pCore 2 ↥K₀)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpCore2
    rw [hn]
    intro h
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    norm_num at h32
  have hker := CFSG.RankThree.PartTwo.Sec13.ker_facts_of_injective f
    (CFSG.perfectResidual ↥K₀).subtype (CFSG.perfectResidual ↥K₀).subtype_injective
    (CFSG.pCore 2 ↥K₀) (fun y hy => by
      have hy' : (QuotientGroup.mk' (CFSG.pCore 2 ↥K₀)
          ((CFSG.perfectResidual ↥K₀).subtype y)) = 1 := by
        simpa only [f, π, MonoidHom.comp_apply] using hy
      exact (QuotientGroup.eq_one_iff ((CFSG.perfectResidual ↥K₀).subtype y)).mp hy')
    hPsolv hP3
  obtain ⟨hks, hk3⟩ := hker
  obtain ⟨eQ⟩ := CFSG.RankThree.PartTwo.Sec13.nonempty_quotTheta_equiv_of_surjective
    f hsurj hks hk3 hθQ
  set K : Subgroup G := (CFSG.perfectResidual ↥K₀).map K₀.subtype with hK
  let eAK : ↥(CFSG.perfectResidual ↥K₀) ≃* ↥K :=
    Subgroup.equivMapOfInjective (CFSG.perfectResidual ↥K₀) K₀.subtype
      K₀.subtype_injective
  have hθe : (aschbacherSolvableCore 3 ↥(CFSG.perfectResidual ↥K₀)).map eAK.toMonoidHom =
      aschbacherSolvableCore 3 ↥K :=
    CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three eAK
  let eQuot : (↥(CFSG.perfectResidual ↥K₀) ⧸
        aschbacherSolvableCore 3 ↥(CFSG.perfectResidual ↥K₀)) ≃*
      (↥K ⧸ aschbacherSolvableCore 3 ↥K) :=
    QuotientGroup.congr (aschbacherSolvableCore 3 ↥(CFSG.perfectResidual ↥K₀))
      (aschbacherSolvableCore 3 ↥K) eAK hθe
  let eFinal : (↥K ⧸ aschbacherSolvableCore 3 ↥K) ≃* Q := eQuot.symm.trans eQ
  have hKSz : CFSG.Blueprint.SuzukiModel
      (↥K ⧸ aschbacherSolvableCore 3 ↥K) 2 m :=
    suzukiModel_of_mulEquiv eFinal hSz
  have hKperf : Group.IsPerfect ↥K := by
    rw [hK]
    have hAperf : Group.IsPerfect ↥(CFSG.perfectResidual ↥K₀) :=
      (perfect_residual_characterization (G := ↥K₀)).2.2.1
    haveI : Group.IsPerfect ↥(CFSG.perfectResidual ↥K₀) := hAperf
    exact Group.IsPerfect.ofSurjective (f := eAK.toMonoidHom) eAK.surjective
  have hKsn : (K.subgroupOf K₀).IsSubnormal := by
    have hnorm : (K.subgroupOf K₀).Normal := by
      rw [hK]
      change (((CFSG.perfectResidual ↥K₀).map K₀.subtype).comap K₀.subtype).Normal
      rw [Subgroup.comap_map_eq_self_of_injective K₀.subtype_injective
        (CFSG.perfectResidual ↥K₀)]
      infer_instance
    exact hnorm.isSubnormal
  have hKq : CFSG.IsQuasisimple (↥K ⧸ aschbacherSolvableCore 3 ↥K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eFinal.symm hQq
  have hKmem : K ∈ thetaComponentsIn K₀ :=
    Sec6.mem_thetaComponentsIn_of (by rw [hK]; exact Subgroup.map_subtype_le _)
      hKperf hKsn hKq
  exact ⟨K, hKmem, hKSz⟩

theorem exists_mem_orderOf_eq_five_of_suzukiModel
    {K : Subgroup G} {N : Subgroup ↥K} [N.Normal] {p f : ℕ}
    (hSz : CFSG.Blueprint.SuzukiModel (↥K ⧸ N) p f) : ∃ e ∈ K, orderOf e = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5 : 5 ∣ Nat.card (↥K ⧸ N) :=
    KSL3PiNoSzProof.five_dvd_card_of_suzukiModel hSz
  have h5K : 5 ∣ Nat.card ↥K := h5.trans (Subgroup.card_quotient_dvd_card N)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 5 h5K
  refine ⟨(x : G), x.2, ?_⟩
  rw [Subgroup.orderOf_coe]
  exact hx

theorem false_of_orderOf_five_mem_sectionCentralizer (h : Sec17Std G A c L Y₀)
    (hrk : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup ↥Y₀))
    (hZ : Subgroup.center (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) = ⊥) {e : G}
    (he : e ∈ Late.sectionCentralizer (Subgroup.normalizer (Y₀ : Set G)) Y₀
      (CFSG.Open.pCoreOf 2 Y₀))
    (he5 : orderOf e = 5) : False := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.Open.pCoreOf 2 Y₀ with hQ
  set M := Subgroup.normalizer (Y₀ : Set G) with hM
  have hQle : Q ≤ Y₀ := CFSG.LieType.BorelTits.pCoreOf_le 2 Y₀
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀
  have hQne : Q ≠ ⊥ := h.mem_y0Star.prop.2.2
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀
  have heM : e ∈ M := he.1
  have heNQ : e ∈ Subgroup.normalizer (Q : Set G) := hMQ heM
  have hQ5 : ¬ 5 ∣ Nat.card Q := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ2
    rw [hn]
    intro h5
    have h52 : 5 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h5
    norm_num at h52
  let S := CFSG.RankThree.PartTwo.Sec11.sectionCentralizerSubgroup M Y₀ Q le_rfl hMQ
  have heSub : e ∈ S :=
    CFSG.RankThree.PartTwo.Sec11.mem_sectionCentralizerSubgroup.mpr he
  obtain ⟨E, -, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 5) (G := ↥Y₀) (by norm_num)
      (⊤ : Subgroup ↥Y₀)
  set E' : Subgroup G := E.map Y₀.subtype with hE'
  have hE'ea : CFSG.Open.IsElemAbelian 5 E' :=
    CFSG.SectionRank.isElemAbelian_map hE Y₀.subtype
  have hE'card : Nat.card E' = 5 ^ CFSG.Open.pRank 5 (⊤ : Subgroup ↥Y₀) := by
    rw [hE', Subgroup.card_map_of_injective Y₀.subtype_injective]
    exact hEcard
  have hE'Y : E' ≤ Y₀ := Subgroup.map_subtype_le E
  have hE'N : E' ≤ Subgroup.normalizer (Q : Set G) :=
    hE'Y.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀)
  have hsupY : E' ⊔ Q ≤ Y₀ := sup_le hE'Y hQle
  have hcomm : ⁅E', Subgroup.zpowers e⁆ ≤ Q := by
    refine Subgroup.commutator_le.mpr ?_
    intro x hx g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hxY : x ∈ Y₀ := hE'Y hx
    have hk : e ^ k ∈ S := S.zpow_mem heSub k
    have hmem : e ^ k * x * (e ^ k)⁻¹ * x⁻¹ ∈ Q := hk.2 x hxY
    have hinv : (e ^ k * x * (e ^ k)⁻¹ * x⁻¹)⁻¹ = x * e ^ k * x⁻¹ * (e ^ k)⁻¹ := by
      group
    rw [commutatorElement_def, ← hinv]
    exact Q.inv_mem hmem
  have hfE : e ∉ E' ⊔ Q := by
    intro heE
    have heY : e ∈ Y₀ := hsupY heE
    have hcen : (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) ⟨e, heY⟩) ∈
        Subgroup.center (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) := by
      rw [Subgroup.mem_center_iff]
      intro z
      induction z using QuotientGroup.induction_on with
      | H y =>
        change (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)) y *
            (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)) ⟨e, heY⟩ =
          (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)) ⟨e, heY⟩ *
            (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)) y
        rw [← map_mul, ← map_mul]
        change ((y * ⟨e, heY⟩ : ↥Y₀) : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) =
          ((⟨e, heY⟩ * y : ↥Y₀) : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)
        rw [QuotientGroup.eq_iff_div_mem]
        have hmem : e * (y : G) * e⁻¹ * (y : G)⁻¹ ∈ Q := he.2 (y : G) y.2
        have hdiv : (y * ⟨e, heY⟩) / (⟨e, heY⟩ * y) ∈ CFSG.pCore 2 ↥Y₀ := by
          rw [Step163Alt.mem_pCore_two_iff]
          have hcoe : (((y * ⟨e, heY⟩) / (⟨e, heY⟩ * y) : ↥Y₀) : G)
              = (e * (y : G) * e⁻¹ * (y : G)⁻¹)⁻¹ := by
            simp only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv]
            rw [div_eq_mul_inv]
            group
          rw [hcoe]
          exact Q.inv_mem hmem
        exact hdiv
    have heQ : e ∈ Q := by
      have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) ⟨e, heY⟩) = 1 := by
        rw [hZ] at hcen
        exact Subgroup.mem_bot.mp hcen
      have h2 : (⟨e, heY⟩ : ↥Y₀) ∈ CFSG.pCore 2 ↥Y₀ :=
        (QuotientGroup.eq_one_iff (⟨e, heY⟩ : ↥Y₀)).mp h1
      exact (Step163Alt.mem_pCore_two_iff ⟨e, heY⟩).mp h2
    have hord : orderOf (⟨e, heY⟩ : ↥Y₀) = 5 := by
      rw [← Subgroup.orderOf_coe (⟨e, heY⟩ : ↥Y₀)]
      exact he5
    have h5Q : 5 ∣ Nat.card Q := by
      let eQ : ↥Q := ⟨e, heQ⟩
      have hordQ : orderOf eQ = 5 := by
        rw [← Subgroup.orderOf_coe eQ]
        exact he5
      have hdvd := Subgroup.card_subgroup_dvd_card (Subgroup.zpowers eQ)
      simpa [Nat.card_zpowers, hordQ] using hdvd
    exact hQ5 h5Q
  have hfp : e ^ 5 = 1 := by
    rw [← he5]
    exact pow_orderOf_eq_one e
  have hle : CFSG.Open.pRank 5 (⊤ : Subgroup ↥Y₀) + 1 ≤
      CFSG.Open.pRank 5 (Subgroup.normalizer (Q : Set G)) :=
    CFSG.Quasithin.succ_le_pRank_of_commute_mod (p := 5)
      (X := Subgroup.normalizer (Q : Set G)) (Q := Q) (E := E')
      (a := CFSG.Open.pRank 5 (⊤ : Subgroup ↥Y₀)) (f := e)
      hQ5 hE'N heNQ hE'ea hE'card hfp hcomm hfE hE'N heNQ Subgroup.le_normalizer
  have hloc : CFSG.Open.IsTwoLocal (Subgroup.normalizer (Q : Set G)) :=
    ⟨Q, hQne, hQ2, rfl⟩
  have hbound := CFSG.RankThree.Classical.pRank_le_localRank (p := 5) (by norm_num) hloc
  have hlt := h.toTheoremFourHyp.localRank_lt 5 Nat.prime_five (by norm_num)
  omega

theorem false_of_suzuki_of_five_rank (h : Sec17Std G A c L Y₀)
    (hgen : Gen166 A c) (hnosz : NoSz166 Y₀)
    (hrk : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup ↥Y₀))
    (hZ : Subgroup.center (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) = ⊥) {K₀ Z : Subgroup G}
    (hK₀ : K₀ = delta A (lB A) K₀)
    (hSz : ∃ m : ℕ, CFSG.Blueprint.SuzukiModel (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) 2 m)
    (hK₀Z : K₀ ≤ Z) (hZ3 : Z ∈ scriptY3Star A (lB A)) : False := by
  obtain ⟨m, hSz⟩ := hSz
  have hZne : Z ≠ ⊤ := hZ3.prop.1.1.1
  have hK₀ne : K₀ ≠ ⊤ := fun htop => hZne (top_le_iff.mp (htop ▸ hK₀Z))
  have hK₀Y : K₀ ∈ scriptY A := by
    refine ⟨hK₀ne, ?_⟩
    rw [hK₀]
    exact CFSG.RankThree.PartTwo.Sec14.le_normalizer_delta K₀
  obtain ⟨K, hKmem, hKSz⟩ := exists_mem_thetaComponentsIn_of_suzukiModel hSz
  obtain ⟨-, hKcen⟩ := rank3II_16_6_1_of h step166Theta hgen hnosz hK₀Y hK₀ hKmem
    ⟨m, hKSz⟩
  obtain ⟨e, heK, he5⟩ := exists_mem_orderOf_eq_five_of_suzukiModel
    (K := K) (N := aschbacherSolvableCore 3 ↥K) hKSz
  exact false_of_orderOf_five_mem_sectionCentralizer h hrk hZ (hKcen heK) he5

theorem omega166A5_of_five_rank (h : Sec17Std G A c L Y₀)
    (hgen : Gen166 A c) (hnosz : NoSz166 Y₀)
    (hrk : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup ↥Y₀))
    (hZ : Subgroup.center (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) = ⊥) : Omega166A5 A Y₀ := by
  intro K₀ Z hK₀ hSz hK₀Z hZ3 hO X' hX' hX'Z J hJ hJ0 hX'J hA5
  exact (false_of_suzuki_of_five_rank h hgen hnosz hrk hZ hK₀ hSz hK₀Z hZ3).elim

theorem omega166Three_of_five_rank (h : Sec17Std G A c L Y₀)
    (hgen : Gen166 A c) (hnosz : NoSz166 Y₀)
    (hrk : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup ↥Y₀))
    (hZ : Subgroup.center (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) = ⊥) : Omega166Three A Y₀ := by
  intro K₀ Z hK₀ hSz hK₀Z hZ3 hO
  exact (false_of_suzuki_of_five_rank h hgen hnosz hrk hZ hK₀ hSz hK₀Z hZ3).elim

theorem five_rank_center_of_j2
    (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hY : Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀) :
    2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup ↥Y₀) ∧
      Subgroup.center (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) = ⊥ := by
  have hYJ := CFSG.RankThree.PartTwo.Sec17.PropU.nonempty_quotient_J2 h hJ hY
  refine ⟨?_, ?_⟩
  · have hcov : Y₀ = Y₀ ⊔ CFSG.Open.pCoreOf 2 Y₀ :=
      (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 Y₀)).symm
    exact CFSG.RankThree.PartTwo.Sec17.G1724.two_le_pRank_five_of_cover
      (D := Y₀) (Y := Y₀) le_rfl hcov hYJ
  · exact CFSG.RankThree.PartTwo.KFacts.KS14.Native.center_eq_bot_of_j2 hYJ

end Proof166SzFive

end CFSG.RankThree.PartTwo.Sec16
