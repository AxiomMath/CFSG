module

public import CFSG.RankThree.PartTwo.Sec13.Item13ResProofReduce
import CFSG.RankThree.PartTwo.Sec13.Item13ResProofQuot
import CFSG.RankThree.PartTwo.Sec13.Item13ResProofTypes
import CFSG.RankThree.PartTwo.Sec13.Item13ResProofCore44
import CFSG.RankThree.PartTwo.Sec13.Item13ResProofRank3
import CFSG.RankThree.PartTwo.Sec13.Item13ResProofE9
import CFSG.RankThree.PartTwo.Sec13.Item13ResProofL3
import CFSG.RankThree.PartTwo.Sec13.Item136E
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeCover
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
import CFSG.RankThree.PartTwo.Sec4.Census.Transfer
import CFSG.RankThree.PartTwo.Sec4.Census.Item44Mathieu
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
import CFSG.RankThree.PartOne.S12.ModelTransport
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec13.ResProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage projSL projSU localRank)
open CFSG.RankThree.PartTwo.Sec4 (PiField ModThree slPi)

theorem isoLThreePi_projImage_slPi {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    ∃ _ : Fact p.Prime, Sec4.IsoLThreePi (projImage (slPi π 3 (p ^ f) K)) p f := by
  have : Fact p.Prime := ⟨hK.prime⟩
  have := hK.finite
  have hf := hK.one_le
  refine ⟨inferInstance, ?_⟩
  cases π
  · right
    refine ⟨hq, ?_⟩
    have hcard : Nat.card K = p ^ (2 * f) := by
      rw [hK.card]
      simp only [Sec4.piCard, Bool.cond_false]
      rw [← pow_mul, mul_comm]
    let φ : K ≃+* GaloisField p (2 * f) :=
      CFSG.ClassicalModels.finiteFieldEquivGaloisField K p (2 * f) (by omega) hcard
    rw [projSU_eq]
    exact ⟨(CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk _).symm.trans
      (CFSG.RankThree.PartOne.statedProjEquivOfGLEquiv
        (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
        (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU φ 3 (p ^ f))
        (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ) rfl)⟩
  · left
    refine ⟨hq, ?_⟩
    have hcard : Nat.card K = p ^ f := hK.card
    let φ : K ≃+* GaloisField p f :=
      CFSG.ClassicalModels.finiteFieldEquivGaloisField K p f (by omega) hcard
    rw [projSL_eq]
    exact ⟨(CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk _).symm.trans
      (CFSG.RankThree.PartOne.statedProjEquivOfGLEquiv
        (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
        (CFSG.ClassicalInvolution.Upgrade.glCongr_statedSL φ 3)
        (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ) rfl)⟩

theorem localRank_le_open_pRank {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) :
    localRank p X ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  refine csSup_le' ?_
  rintro _ ⟨H, -, rfl⟩
  exact CFSG.SectionRank.pRank_mono hp.one_lt le_top

theorem sectionFourHyp_quotient_of_pRank_three {X : Type} [Group X] [Finite X]
    (N : Subgroup X) [N.Normal] (hX : SectionFourHyp X) (hN3 : Nat.card N = 3)
    (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ N)) ≤ 3) : SectionFourHyp (X ⧸ N) := by
  have hlt : ∀ p : ℕ, p.Prime → 3 < p → localRank p (X ⧸ N) < 3 := fun p hp hp3 =>
    (CFSG.RankThree.Classical2.localRank_quotient_le hp (by omega) N (by
      rw [hN3]
      intro h
      have := Nat.le_of_dvd (by norm_num) h
      omega)).trans_lt (hX.localRank_lt p hp hp3)
  refine ⟨CFSG.SectionRank.K_group_section_closure_inCatalog hX.kGroup ⊤ (N.subgroupOf ⊤)
      (Sec4.Item41Narrow.quotientTopEquiv N),
    Sec4.Census.evenRank_le_of_localRank_le fun p hp hp2 => ?_, hlt⟩
  rcases (show p = 3 ∨ 3 < p by have := hp.two_le; omega) with rfl | hp3
  · exact (localRank_le_open_pRank Nat.prime_three).trans h3
  · exact (hlt p hp hp3).le.trans (by norm_num)

theorem pRank_three_le_two_of_not_dvd {X : Type} [Group X] [Finite X]
    (h27 : ¬ 27 ∣ Nat.card X) : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2 := by
  refine CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEp : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEp
  have hdvd : 3 ^ k ∣ Nat.card X := hk ▸ Subgroup.card_subgroup_dvd_card E
  rw [hk]
  by_contra hlt
  push Not at hlt
  have hk3 : 3 ≤ k := by
    by_contra h
    push Not at h
    interval_cases k <;> norm_num at hlt
  exact h27 ((pow_dvd_pow 3 hk3).trans hdvd)

theorem exists_e9_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∃ E : Subgroup Y, Monoid.exponent E ∣ 3 ∧ Nat.card E = 9) :
    ∃ E : Subgroup X, Monoid.exponent E ∣ 3 ∧ Nat.card E = 9 := by
  obtain ⟨E, hE3, hE9⟩ := h
  refine ⟨E.map e.symm.toMonoidHom, ?_, ?_⟩
  · apply Monoid.exponent_dvd_of_forall_pow_eq_one
    rintro ⟨_, ⟨y, hy, rfl⟩⟩
    apply Subtype.ext
    have hy3 : (⟨y, hy⟩ : E) ^ 3 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hE3 _
    have hy3' : y ^ 3 = 1 := by simpa using congrArg Subtype.val hy3
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, hy3', map_one]
  · rw [Subgroup.card_map_of_injective e.symm.injective, hE9]

theorem centerQuot_facts
    {X : Type} [Group X] [Finite X] (hq : IsQuasisimple X)
    (htype : Sec4.IsSLThreePi X ∨ Sec4.IsTripleCover X (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.M22) :
    (∃ E : Subgroup (X ⧸ Subgroup.center X), Monoid.exponent E ∣ 3 ∧ Nat.card E = 9) ∧
      (∀ m : ℕ, m = 60 ∨ m = 120 ∨ m = 360 ∨ m = 5616 →
        ¬ Nat.card (X ⧸ Subgroup.center X) ∣ m) ∧
      CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ Subgroup.center X)) ≤ 3 := by
  have hQq := isQuasisimple_quotient_center hq
  rcases htype with hSL | hA7 | hM22
  · obtain ⟨q, hSLq⟩ := hSL
    obtain ⟨π, p, f, K, _, hK, hpq, -, ⟨e⟩⟩ := exists_centerQuot_equiv_projImage hSLq
    obtain ⟨hp, hIso⟩ := isoLThreePi_projImage_slPi hK hpq
    obtain ⟨-, -, hbig, E, hE3, hE9⟩ := typeFacts135_isoLThreePi hK.one_le hQq
      (KFacts.OutFixCentralThree.isoLThreePi_of_mulEquiv e hIso)
    exact ⟨⟨E, hE3, hE9⟩, not_dvd_of_lt_card (by omega),
      pRank_three_quotient_center_le_of_isSLThreePi ⟨q, hSLq⟩⟩
  · obtain ⟨-, ⟨e⟩⟩ := hA7
    have hc : Nat.card (X ⧸ Subgroup.center X) = 2520 := by
      rw [Nat.card_congr e.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
    refine ⟨exists_e9_of_mulEquiv e exists_e9_alt7, ?_, ?_⟩
    · rw [hc]
      intro m hm
      rcases hm with rfl | rfl | rfl | rfl <;> decide
    · exact (pRank_three_le_two_of_not_dvd (by rw [hc]; decide)).trans (by norm_num)
  · obtain ⟨-, ⟨e⟩⟩ := hM22
    have hc : Nat.card (X ⧸ Subgroup.center X) = 443520 := by
      rw [Nat.card_congr e.toEquiv, Sec4.Census.card_m22_eq]
    refine ⟨exists_e9_of_mulEquiv e exists_e9_m22, ?_, ?_⟩
    · rw [hc]
      exact not_dvd_of_lt_card (by norm_num)
    · exact (pRank_three_le_two_of_not_dvd (by rw [hc]; decide)).trans (by norm_num)

theorem centerQuot_type {X : Type} [Group X] [Finite X]
    (htype : Sec4.IsSLThreePi X ∨ Sec4.IsTripleCover X (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.M22) :
    (∃ q : ℕ, q % 2 = 1 ∧ Sec4.IsSLThreePiAt X q) ∨
      Sec4.IsTripleCover X (alternatingGroup (Fin 7)) ∨
      Nonempty (X ⧸ Subgroup.center X ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      ∃ f : ℕ, 1 ≤ f ∧ Sec4.IsoLThreePi (X ⧸ Subgroup.center X) 2 f := by
  rcases htype with ⟨q, hSLq⟩ | hA7 | hM22
  · obtain ⟨π, p, f, K, _, hK, hpq, hqe, ⟨e⟩⟩ := exists_centerQuot_equiv_projImage hSLq
    obtain ⟨hp, hIso⟩ := isoLThreePi_projImage_slPi hK hpq
    by_cases hp2 : p = 2
    · subst hp2
      exact Or.inr (Or.inr (Or.inr ⟨f, hK.one_le,
        KFacts.OutFixCentralThree.isoLThreePi_of_mulEquiv e hIso⟩))
    · refine Or.inl ⟨q, ?_, hSLq⟩
      rw [← hqe]
      exact Nat.odd_iff.mp ((hp.out.odd_of_ne_two hp2).pow)
  · exact Or.inr (Or.inl hA7)
  · obtain ⟨-, ⟨e⟩⟩ := hM22
    exact Or.inr (Or.inr (Or.inl ⟨e⟩))

end CFSG.RankThree.PartTwo.Sec13.ResProof

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo ResProof
open CFSG.Assembly.RankThreeEven (projImage)

theorem item135ReduceCentral_of
    (h131a : Item131a) (h44 : Sec4.Item4_4) (hK : KS135TwoRank)
    (hspor : SporadicModels131) : Item135ReduceCentral := by
  intro G _ _ A c L hD _ hcL hnq
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLc := hD.mem_thetaComponentsAt
  have hperf : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hLc
  have hbar : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc
  have htype := types_of_mem h131a hspor hD hcL
  have hZ3 : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3 := by
    rcases htype with hSL | hA7 | hM22
    · exact card_center_of_isSLThreePi hSL
    · exact hA7.1
    · exact hM22.1
  set c' : L := ⟨c, hcL⟩ with hc'
  have hcZ : c' ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer l.2))
  have hc3 : orderOf c' = 3 := by rw [Subgroup.orderOf_mk, hD.orderOf_eq]
  set N := Subgroup.zpowers c' with hNdef
  have hNZ : N ≤ Subgroup.center L := Subgroup.zpowers_le.mpr hcZ
  have : N.Normal := Subgroup.normal_of_le_center hNZ
  have hN3 : Nat.card N = 3 := by rw [Nat.card_zpowers, hc3]
  set θ := aschbacherSolvableCore 3 L with hθ
  set ρ := QuotientGroup.mk' θ with hρ
  have hθL := solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  have hZ : Subgroup.center (L ⧸ θ) = N.map ρ := by
    have hle : N.map ρ ≤ Subgroup.center (L ⧸ θ) := by
      rintro _ ⟨n, hn, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective θ y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hNZ hn) x]
    have hinj : Set.InjOn ρ N := by
      intro a ha b hb hab
      have hmem : a⁻¹ * b ∈ θ := by
        rw [← QuotientGroup.eq]
        exact hab
      have hNmem : a⁻¹ * b ∈ N := N.mul_mem (N.inv_mem ha) hb
      have h1 : orderOf (a⁻¹ * b) ∣ 3 := by
        rw [← hN3, ← Subgroup.orderOf_mk _ hNmem]
        exact orderOf_dvd_natCard _
      have h2 : orderOf (a⁻¹ * b) ∣ Nat.card θ := by
        rw [← Subgroup.orderOf_mk _ hmem]
        exact orderOf_dvd_natCard _
      have hcop : Nat.Coprime 3 (Nat.card θ) :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθL.2.2.1
      have h3 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
      rw [inv_mul_eq_one] at h3
      exact h3
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hZ3, card_map_eq_of_injOn ρ hinj, hN3]
  obtain ⟨eθ⟩ := nonempty_quotient_theta_equiv N hbar hZ
  have hQs : IsSimpleGroup ((L ⧸ θ) ⧸ Subgroup.center (L ⧸ θ)) := hbar.2.1
  have hQZ : Subgroup.center ((L ⧸ θ) ⧸ Subgroup.center (L ⧸ θ)) = ⊥ :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hbar.2.2).2
  have hYs : IsSimpleGroup ((L ⧸ N) ⧸ aschbacherSolvableCore 3 (L ⧸ N)) :=
    eθ.isSimpleGroup
  have hYZ : Subgroup.center ((L ⧸ N) ⧸ aschbacherSolvableCore 3 (L ⧸ N)) = ⊥ :=
    center_eq_bot_of_mulEquiv eθ hQZ
  obtain ⟨hQE, hQcard, hQ3⟩ := centerQuot_facts hbar htype
  obtain ⟨E, hE3, hE9⟩ := exists_e9_of_mulEquiv eθ hQE
  have hYcard : ∀ m : ℕ, m = 60 ∨ m = 120 ∨ m = 360 ∨ m = 5616 →
      ¬ Nat.card ((L ⧸ N) ⧸ aschbacherSolvableCore 3 (L ⧸ N)) ∣ m := by
    rw [Nat.card_congr eθ.toEquiv]
    exact hQcard
  have hθY := solvable_prime_complement_core_characterization (H := L ⧸ N) Nat.prime_three
  have hY3 : CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸ N)) ≤ 3 := by
    rw [← CFSG.SectionRank.pRank_quotient_eq (aschbacherSolvableCore 3 (L ⧸ N)) hθY.2.2.1,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) eθ]
    exact hQ3
  have hY4 := sectionFourHyp_quotient_of_pRank_three N (sectionFourHyp_of_sec13Data hD) hN3 hY3
  have hnqY : ¬ IsQuasisimple ((L ⧸ N) ⧸ CFSG.pCore 2 (L ⧸ N)) := fun h =>
    hnq ((isQuasisimple_quotient_pCore_two_iff N hNZ hN3).mpr h)
  obtain ⟨hO2Y, hmY, hOY⟩ := reduce44_core h44 hY4 hE3 hE9 hYcard hnqY
  have hO2 : CFSG.pCore 2 L = ⊥ := by
    have hmap := pCore_two_quotient_eq_map N hNZ hN3
    rw [hO2Y, eq_comm, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmap
    rw [eq_bot_iff]
    intro t ht
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := L)) ⟨t, ht⟩
    have htk : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have ht3 : t ^ 3 = 1 := pow_three_eq_one_of_mem N hN3 (hmap ht)
    have h1 : orderOf t ∣ Nat.gcd (2 ^ k) 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one htk) (orderOf_dvd_of_pow_eq_one ht3)
    have hg : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left k (by norm_num)
    rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at h1
    exact h1
  have hm : CFSG.Open.pRank 2 (⊤ : Subgroup L) ≤ 2 := by
    rw [← pRank_two_quotient N hN3]
    exact hmY
  have hO : IsQuasisimple (L ⧸ CFSG.oddCore L) := by
    obtain ⟨e⟩ := nonempty_quotient_oddCore_equiv N hN3
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e hOY
  refine ⟨hO2, hm, hO, ?_⟩
  have hbad := fun htype' => three_le_pRank_of_types (X := L ⧸ N) hK hYZ hOY htype'
  rcases centerQuot_type htype with hSL | hA7 | hM22 | ⟨f, hf, hL⟩
  · exact Or.inl hSL
  · exact Or.inr hA7
  · obtain ⟨φ⟩ := hM22
    have := hbad (Or.inr (Or.inr (Or.inl ⟨eθ.trans φ⟩)))
    omega
  · have := hbad (Or.inr (Or.inr (Or.inr ⟨f, hf,
      KFacts.OutFixCentralThree.isoLThreePi_of_mulEquiv eθ hL⟩)))
    omega

theorem item135Reduce_of_items
    (h131a : Item131a) (h44 : Sec4.Item4_4) (hK : KS135TwoRank)
    (hspor : SporadicModels131) : Item135Reduce :=
  item135Reduce_of h131a h44 hK hspor (item135ReduceCentral_of h131a h44 hK hspor)

end CFSG.RankThree.PartTwo.Sec13
