module

public import CFSG.RankThree.PartOne.S11c.HNProps
public import CFSG.RankThree.PartOne.S11c.OuterInner
public import CFSG.RankThree.PartOne.KS.Basic
public import CFSG.Sporadic.HNSchreier.FullAut
public import CFSG.RankThree.OddKernel.SporadicKernelHN
public import CFSG.Sporadic.HN.Local.Main
public import CFSG.RankThree.PartOne.S11.CatalogLeaves

public section

namespace CFSG.RankThree.PartOne.HNRed

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree.GroupTheory
open CFSG.Blueprint.NativeSporadic (Carrier IsSporadic SporadicRep)

theorem originalHNNotIsomorphic_of_inputs (hT : HNSuccessorTransport)
    (hC : FiveFixedExcludesClassical) (hA : FiveFixedExcludesAlternating)
    (hX : FiveFixedExcludesChevalley) (hR : FiveFixedExcludesSuzukiReeTits)
    (hS : FiveFixedSporadicOnlyHN) (hB : HNPrescribedBlockNormalizedTwo) :
    OriginalHNNotIsomorphic := by
  intro G _ _ A h L hL hHN
  obtain ⟨H, X, β, Λ, K, Y, U, hrank, hqs, hcat, hΛe, hΛc, hβΛ, hfix, hYK, hYSL, hU0, hU2,
    hUβ, hUY, hUcl⟩ := hT G A h L hL hHN
  have hsimple : IsSimpleGroup (X ⧸ Subgroup.center X) := hqs.2.1
  have hnab : ∃ a b : X ⧸ Subgroup.center X, a * b ≠ b * a := hqs.2.2
  rcases hcat with ⟨p, hp, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | hclass | hexc | hspor
  ·
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  · exact hA H hrank X hqs β K hfix n hn ⟨e⟩
  · obtain ⟨t, n, ℓ, f, hm⟩ := (Milestones.fam_classical_model_membership_alltags _).1 hclass
    exact hC H hrank X hqs β K hfix t n ℓ f hm
  · rcases hexc with ⟨t, ℓ, f, ht, hm⟩ | ⟨t, ℓ, f, ht, hm⟩ | ⟨ℓ, f, hm⟩
    · exact hX H hrank X hqs β K hfix t ht ℓ f hm
    · exact (hR H hrank X hqs β K hfix).2 t ht ℓ f hm
    · exact (hR H hrank X hqs β K hfix).1 ℓ f hm
  · have hHN' : IsSporadic (X ⧸ Subgroup.center X) .HN :=
      hS H hrank X hqs Λ hΛe hΛc β hβΛ K hfix hspor
    have hKfix : ∀ k ∈ K, β k = k := fun k hk => hfix.2.1.1 hk
    have hcent := hB (X ⧸ Subgroup.center X) hsimple hnab hHN' β hfix.1 K hKfix hfix.2.2 Y hYK
      hYSL U hU2 hUβ hUY
    apply hU0
    rw [← hUcl, eq_bot_iff]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨u, hu, rfl⟩
    rw [hcent u hu, inv_mul_cancel]
    exact Subgroup.one_mem _

section Layer1

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.Assembly (InCatalog)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem eq_five_of_sq_dvd_card_HN {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (h : p ^ 2 ∣ 273030912000000) : p = 5 := by
  have e : (273030912000000 : ℕ) = 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19 := by norm_num
  have h1 : p ∣ 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19 := by
    rw [← e]
    exact (dvd_pow_self p two_ne_zero).trans h
  have hq : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq hpq =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 hpq
  rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
  · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
    · rcases (Nat.Prime.dvd_mul hp).1 h3 with h4 | h4
      · rcases (Nat.Prime.dvd_mul hp).1 h4 with h5 | h5
        · rcases (Nat.Prime.dvd_mul hp).1 h5 with h6 | h6
          · exfalso
            have := hq 2 Nat.prime_two (hp.dvd_of_dvd_pow h6)
            omega
          · exfalso
            have := hq 3 Nat.prime_three (hp.dvd_of_dvd_pow h6)
            omega
        · exact hq 5 Nat.prime_five (hp.dvd_of_dvd_pow h5)
      · exfalso
        have := hq 7 (by norm_num) h4
        subst this
        norm_num at h
    · exfalso
      have := hq 11 (by norm_num) h3
      subst this
      norm_num at h
  · exfalso
    have := hq 19 (by norm_num) h2
    subst this
    norm_num at h

theorem maximalMovingHN_of_inputs
    (hS : SchreierFor InCatalog) (hcover : HNPerfectCoverCenterless)
    (hnot : OriginalHNNotIsomorphic) : MaximalMovingComponentHNQuotientsExcluded := by
  intro G _ _ p A h L hL hHN
  obtain ⟨e⟩ := hHN
  obtain ⟨hq, -, -⟩ := moving_maximal_quasisimple_data hS h hL
  have hsimple : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2.1
  have hnab : ∃ a b : L ⧸ Subgroup.center L, a * b ≠ b * a := hq.2.2
  have hrank : CFSG.twoLocalOddRank G ≤ 3 := h.2.2.2.2.1.le
  have hker : (QuotientGroup.mk' (Subgroup.center L)).ker = ⊥ :=
    hcover G hrank L hq.1 (L ⧸ Subgroup.center L) (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _) ⟨e⟩ (by rw [QuotientGroup.ker_mk'])
  have hZ : Subgroup.center L = ⊥ := by rwa [QuotientGroup.ker_mk'] at hker
  have hp5 : p = 5 := by
    obtain ⟨hAL, U, hpl, -⟩ := moving_maximal_plane_witness hS h hL
    have hp : p.Prime := hpl.prime
    have hcT : Subgroup.center (L ⧸ Subgroup.center L) = ⊥ := center_eq_bot_of_simple hnab
    have hOutT : Nat.card (Outer (L ⧸ Subgroup.center L)) = 2 := by
      rw [Nat.card_congr
        (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
      exact CFSG.Sporadic.HNSchreier.card_outer_HN
    have hOut : ¬ p ∣ Nat.card (Outer (L ⧸ Subgroup.center L)) := by
      rw [hOutT]
      intro hd
      have h2 := Nat.le_of_dvd (by norm_num) hd
      have h3 := hpl.three_lt
      omega
    have hel := hpl.elementary
    have hEin : (centerQuotientAction hAL).range ≤ inner (L ⧸ Subgroup.center L) := by
      intro ε hε
      obtain ⟨b, hb⟩ := exists_inner_of_pow_eq_one_of_not_dvd_card_outer hp hOut ε
        (elemPow_eq_one_of_isElementaryAbelian (A := (centerQuotientAction hAL).range) ε hε)
      exact ⟨b, hb⟩
    have hinj := conj_injective_of_center_eq_bot hcT
    have hcardInn : Nat.card (inner (L ⧸ Subgroup.center L)) =
        Nat.card (L ⧸ Subgroup.center L) :=
      (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    have hdvd : p ^ 2 ∣ Nat.card (L ⧸ Subgroup.center L) := by
      have := Subgroup.card_dvd_of_le hEin
      rwa [hpl.card, hcardInn] at this
    rw [(Nat.card_congr e.toEquiv).trans CFSG.Sporadic.HN.card_HN] at hdvd
    exact eq_five_of_sq_dvd_card_HN hp hpl.three_lt hdvd
  subst hp5
  let eL : (L ⧸ Subgroup.center L) ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact hnot G A h L hL ⟨(eL.symm.trans e).symm⟩

end Layer1

section Layer2a

open CFSG.Sporadic.HN.Local (hnStab hn_point_stabilizer_alternating_twelve)

theorem kernel_coprime_six_of_alternating_stabilizer (hAlt : AlternatingFullCentralKernel)
    {G : Type} [Group G] [Finite G] (hrank : CFSG.twoLocalOddRank G ≤ 3) (X : Subgroup G)
    {S N : Type} [Group S] [Group N] (π : X →* S) (hsurj : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center X) (e : S ≃* N) (H : Subgroup N)
    (θ : H ≃* alternatingGroup (Fin 12)) : Nat.Coprime (Nat.card π.ker) 6 := by
  let π' : X →* N := e.toMonoidHom.comp π
  have hsurj' : Function.Surjective π' := e.surjective.comp hsurj
  have hker' : π'.ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact MulEquiv.map_eq_one_iff e
  let K : Subgroup X := H.comap π'
  let σ : K →* alternatingGroup (Fin 12) := θ.toMonoidHom.comp (π'.subgroupComap H)
  have hσsurj : Function.Surjective σ := by
    intro a
    obtain ⟨x, hx⟩ := hsurj' (θ.symm a : H)
    have hxH : π' x ∈ H := by rw [hx]; exact (θ.symm a).2
    refine ⟨⟨x, hxH⟩, ?_⟩
    show θ ⟨π' x, hxH⟩ = a
    have : (⟨π' x, hxH⟩ : H) = θ.symm a := Subtype.ext hx
    rw [this, MulEquiv.apply_symm_apply]
  have hσker : ∀ k : K, k ∈ σ.ker ↔ (k : X) ∈ π.ker := by
    intro k
    rw [MonoidHom.mem_ker, ← hker', MonoidHom.mem_ker]
    show θ ⟨π' k, k.2⟩ = 1 ↔ π' k = 1
    rw [MulEquiv.map_eq_one_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hσcent : σ.ker ≤ Subgroup.center K := by
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro k'
    have hkX : (k : X) ∈ Subgroup.center X := hC ((hσker k).mp hk)
    exact Subtype.ext ((Subgroup.mem_center_iff.mp hkX) k')
  have hcard : Nat.card σ.ker = Nat.card π.ker := by
    refine Nat.card_congr
      (Equiv.ofBijective (fun k : σ.ker => (⟨(k : K), (hσker k).mp k.2⟩ : π.ker)) ⟨?_, ?_⟩)
    · intro a b hab
      exact Subtype.ext (Subtype.ext (congrArg (fun x : π.ker => ((x : X) : X)) hab))
    · rintro ⟨x, hx⟩
      have hxK : x ∈ K := by
        show π' x ∈ H
        rw [show π' x = 1 from by rw [← MonoidHom.mem_ker, hker']; exact hx]
        exact H.one_mem
      exact ⟨⟨⟨x, hxK⟩, (hσker ⟨x, hxK⟩).mpr hx⟩, rfl⟩
  have hι : Function.Injective (X.subtype.comp K.subtype) := fun a b hab =>
    Subtype.ext (Subtype.ext hab)
  have h3 : ¬ 3 ∣ Nat.card π.ker := fun hd => by
    have := hAlt G K (X.subtype.comp K.subtype) hι 12 (by norm_num) σ hσsurj hσcent
      (Or.inl ⟨by norm_num, hcard ▸ hd⟩)
    omega
  have h2 : ¬ 2 ∣ Nat.card π.ker := fun hd => by
    have := hAlt G K (X.subtype.comp K.subtype) hι 12 (by norm_num) σ hσsurj hσcent
      (Or.inr ⟨by norm_num, hcard ▸ hd⟩)
    omega
  have h2' : Nat.Coprime (Nat.card π.ker) 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2).symm
  have h3' : Nat.Coprime (Nat.card π.ker) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm
  exact Nat.Coprime.mul_right h2' h3'

theorem hnPerfectCoverCenterless_of_inputs
    (hAlt : AlternatingFullCentralKernel)
    (hFive : HNFiveKernelTrivial) : HNPerfectCoverCenterless := by
  intro G _ _ hrank X hperf S _ π hsurj hHN hC
  have : Group.IsPerfect X := hperf
  obtain ⟨e⟩ := hHN
  obtain ⟨-, ⟨θ⟩⟩ := hn_point_stabilizer_alternating_twelve
  have h6 : Nat.Coprime (Nat.card π.ker) 6 :=
    @kernel_coprime_six_of_alternating_stabilizer hAlt G _ _ hrank X S NativeSporadic.HN _
      Units.instGroup π hsurj hC (e.trans (MulEquiv.refl _)) hnStab θ
  have hall5 : ∀ r : ℕ, r.Prime → r ∣ Nat.card π.ker → r = 5 := fun r hr hrC =>
    OddKernel.prime_dvd_of_isSporadic_HN π hsurj hC h6 ⟨e⟩ hr hrC
  have h5 := hFive X hperf S π hsurj ⟨e⟩ hC
  by_contra hne
  have hgt : Nat.card π.ker ≠ 1 := fun h1 => hne (Subgroup.card_eq_one.mp h1)
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hgt
  have := hall5 r hr hrd
  subst this
  exact h5 hrd

end Layer2a

section Composite

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.Assembly (InCatalog)

theorem maximalMovingHN_of_leaves
    (hS : SchreierFor InCatalog) (hAlt : AlternatingFullCentralKernel)
    (hFive : HNFiveKernelTrivial) (hT : HNSuccessorTransport)
    (hC : FiveFixedExcludesClassical) (hA : FiveFixedExcludesAlternating)
    (hX : FiveFixedExcludesChevalley) (hR : FiveFixedExcludesSuzukiReeTits)
    (hSp : FiveFixedSporadicOnlyHN) (hB : HNPrescribedBlockNormalizedTwo) :
    MaximalMovingComponentHNQuotientsExcluded :=
  maximalMovingHN_of_inputs hS (hnPerfectCoverCenterless_of_inputs hAlt hFive)
    (originalHNNotIsomorphic_of_inputs hT hC hA hX hR hSp hB)

end Composite

end CFSG.RankThree.PartOne.HNRed
