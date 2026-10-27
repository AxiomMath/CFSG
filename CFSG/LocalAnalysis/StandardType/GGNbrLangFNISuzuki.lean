module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIRows
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIRestr
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIOne
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIVacTwisted
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCSuzukiOddCore
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.GroupTheory.PCore.SubgroupCore

public section

namespace CFSG.StandardType

open CFSG.Assembly


private theorem fniSz_false_of_suzuki_centralizer {S : Type} [Group S] [Finite S] {f : ℕ}
    (hS : CFSG.Blueprint.SuzukiModel S 2 f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {s : S}
    (hsp : s ^ p = 1) (hs1 : s ≠ 1) {T : Subgroup S} (hT : ⁅T, T⁆ = T) (hT1 : T ≠ ⊥)
    (hTs : ∀ t ∈ T, t * s = s * t) : False := by
  haveI : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).2 hT1
  haveI : Group.IsPerfect ↥T := Subgroup.isPerfect_iff.2 hT
  have hev : 2 ∣ Nat.card ↥T := by
    by_contra h2
    have hodd : Odd (Nat.card ↥T) := Nat.odd_iff.2 (by omega)
    haveI := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    exact Group.IsPerfect.not_isSolvable ↥T inferInstance
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 hev
  obtain ⟨-, a, ha, K, _, _, hfa, hKcard, ⟨e⟩⟩ := hS
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hKcard
  have ht2 : orderOf (t : S) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  have hyo : orderOf (e (t : S)) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht2
  obtain ⟨S₂, hS₂⟩ :=
    CFSG.ComponentClassification.UnbalancedGS.SuzukiOddCore.suzuki_involution_centralizer_sylow
      hK (e (t : S)) hyo
  have hsS : e s ∈ (S₂ : Subgroup (CFSG.Blueprint.suzukiGroup a K)) := by
    rw [hS₂]
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (by rw [← map_mul, ← map_mul, (hTs t t.2).symm])
  have hsord : orderOf (e s) = p :=
    orderOf_eq_prime (by rw [← map_pow, hsp, map_one])
      (fun h1 => hs1 (e.injective (h1.trans (map_one e).symm)))
  have hpS : IsPGroup 2 (S₂ : Subgroup (CFSG.Blueprint.suzukiGroup a K)) := S₂.isPGroup'
  obtain ⟨k, hk⟩ := hpS ⟨e s, hsS⟩
  have hdvd : p ∣ 2 ^ k := by
    have h1 : orderOf (⟨e s, hsS⟩ : (S₂ : Subgroup (CFSG.Blueprint.suzukiGroup a K))) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one hk
    rwa [Subgroup.orderOf_mk, hsord] at h1
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))

theorem kgFieldRestrictionOn_suzuki : KGFieldRestrictionOn (kgfniRow .suzuki) := by
  intro p lab hp hp2 hlab ht3 hrow
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨htag, hdvd⟩ := hrow
  subst htag
  intro Q hraw
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeSuzuki] at hraw ⊢
  obtain ⟨K, hF, hfin, hK, hQ⟩ := hraw
  letI := hF
  haveI := hfin
  let R := LargeEvenCenterQuot (LargeEvenSzGroup ((n - 1) / 2) K)
  let F := LargeEvenMatFieldImage (LargeEvenCenterMk (LargeEvenSzGroup ((n - 1) / 2) K))
  have hS : KGFNITwistedLabel ⟨.twB2, r, n⟩ := by
    simp [KGFNITwistedLabel]
  have hcongr_refl : ∀ {X : Type} [Group X],
      MulAut.congr (MulEquiv.refl X) = MulEquiv.refl (MulAut X) := by
    intro X _
    ext f x
    simp [MulAut.congr, MulEquiv.trans_apply]
  have hself : LargeEvenRawDatum ⟨.twB2, r, n⟩ (fun R' _ _ F' =>
      ∃ e : R ≃* R', F' = MulAut.congr e '' F) := by
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeSuzuki]
    exact ⟨K, inferInstance, inferInstance, hK,
      ⟨MulEquiv.refl R, by rw [hcongr_refl]; exact (Set.image_id F).symm⟩⟩
  obtain ⟨R', _, _, _, ⟨e, _⟩, hsimple', hna'⟩ :=
    largeEvenRawDatum_exists (kgfni_rawSimple_twisted _ hlab hS _ hself)
  have hsimpleR : IsSimpleGroup R := (MulEquiv.isSimpleGroup_congr e).mpr hsimple'
  have hnaR : ∃ a b : R, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna'
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hcenterR : Subgroup.center R = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R) with hbot | htop
    · exact hbot
    · exfalso
      obtain ⟨a, b, hab⟩ := hnaR
      exact hab (Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top a) b).symm
  refine ⟨K, hF, hfin, hK, ⟨hQ, ?_⟩⟩
  intro f hf hord h hI hhp hcomm J hJ f' hf'
  by_cases h1 : h = 1
  · subst h1
    exact kgFieldRestriction_hOne_of_rawImage hp hp2 hlab (kgfni_rawSimple_twisted _ hlab hS)
      hself f hf hord J hJ f' hf'
  · simp only [LargeEvenInnSet, Set.mem_range] at hI
    obtain ⟨s, rfl⟩ := hI
    have hinj := CFSG.mulAutConj_injective_of_center_eq_bot hcenterR
    have hsp : s ^ p = 1 := by
      apply hinj
      rw [map_pow, hhp, map_one]
    have hs1 : s ≠ 1 := fun hs => h1 (by rw [hs, map_one])
    have hperf : ⁅J, J⁆ = J :=
      Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hJ.2.2.1)
    have hne : J ≠ ⊥ := by
      intro hbot
      have hNontriv : Nontrivial (↥J ⧸ Subgroup.center ↥J) := hJ.2.2.2.toNontrivial
      have hJnt : Nontrivial ↥J :=
        @Function.Surjective.nontrivial ↥J (↥J ⧸ Subgroup.center ↥J) hNontriv _
          (QuotientGroup.mk'_surjective (Subgroup.center ↥J))
      exact (Subgroup.nontrivial_iff_ne_bot J).mp hJnt hbot
    have hcent : ∀ u ∈ J, u * s = s * u := by
      intro u hu
      have hu' : MulAut.conj s u = u := hJ.1 hu
      rw [MulAut.conj_apply] at hu'
      calc u * s = (s * u * s⁻¹) * s := by rw [hu']
        _ = s * u := by group
    have ha : 1 ≤ (n - 1) / 2 := by
      rw [Nat.one_le_div_iff (by norm_num : 0 < 2)]
      have hn3 : 3 ≤ n := hlab.2.2.2
      omega
    haveI : Finite R := inferInstance
    exfalso
    exact fniSz_false_of_suzuki_centralizer
      (suzukiModel_largeEvenSz ha K hK hnaR) hp hp2 hsp hs1 hperf hne hcent

end CFSG.StandardType
