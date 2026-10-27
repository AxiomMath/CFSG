module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight8xKLeaves2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight63J2Tits
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneElevenEleven
public import CFSG.GroupTheory.PRankBound

@[expose] public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

theorem exists_E9_of_pRank_three_eq_two {X : Type} [Group X] [Finite X]
    (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2) (S : Subgroup X) (hS : IsSylowOf 3 S ⊤)
    (e : X) (heS : e ∈ S) (he : orderOf e = 3) :
    ∃ E : Subgroup X, e ∈ E ∧ E ≤ S ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := hS
  have hsurj : Function.Surjective (⊤ : Subgroup X).subtype := fun x => ⟨⟨x, mem_top x⟩, rfl⟩
  set P : Sylow 3 X := Q.mapSurjective hsurj with hP
  have hPS : (P : Subgroup X) = S := by rw [hP, Sylow.coe_mapSurjective, hQ]
  have hS3 : IsPGroup 3 S := hPS ▸ P.isPGroup'
  obtain ⟨E₀, hE₀S, hE₀, hE₀9⟩ := CFSG.AGLEmbedding.exists_elem_le_sylow_of_le_pRank
    (p := 3) (k := 2) h3.ge P
  rw [hPS] at hE₀S
  have hSnt : Nontrivial S := by
    refine ⟨⟨⟨e, heS⟩, 1, fun h => ?_⟩⟩
    have : e = 1 := congrArg Subtype.val h
    rw [this, orderOf_one] at he
    exact absurd he (by norm_num)
  have := hS3.center_nontrivial
  obtain ⟨n, hn0, hn⟩ := (IsPGroup.nontrivial_iff_card (hS3.to_subgroup (center S))).mp
    inferInstance
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center S) 3
    (by rw [hn]; exact dvd_pow_self 3 hn0.ne')
  set c : X := ((z : S) : X) with hc
  have hcS : c ∈ S := ((z : S)).2
  have hcomm : ∀ s ∈ S, c * s = s * c := fun s hs => by
    have := Subgroup.mem_center_iff.mp z.2 ⟨s, hs⟩
    exact (congrArg Subtype.val this).symm
  have hco : orderOf c = 3 := by
    rw [hc, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have hsup : ∀ u ∈ S, ∀ v ∈ S, zpowers u ⊔ zpowers v ≤ S := fun u hu v hv =>
    sup_le ((zpowers_le).2 hu) ((zpowers_le).2 hv)
  by_cases hce : c ∈ zpowers e
  ·
    have hez : e ∈ zpowers c := by
      have h1 : zpowers c ≤ zpowers e := (zpowers_le).2 hce
      have h2 : Nat.card (zpowers c) = Nat.card (zpowers e) := by
        rw [Nat.card_zpowers, Nat.card_zpowers, hco, he]
      have := Subgroup.eq_of_le_of_card_ge h1 h2.ge
      rw [this]; exact mem_zpowers e
    have hnle : ¬ E₀ ≤ zpowers e := fun hle => by
      have := Subgroup.card_le_of_le hle
      rw [hE₀9, Nat.card_zpowers, he] at this
      norm_num at this
    obtain ⟨f, hfE, hfe⟩ := Set.not_subset.mp hnle
    have hf1 : f ≠ 1 := fun h => hfe (h ▸ one_mem _)
    have hfo : orderOf f = 3 := orderOf_eq_prime (hE₀.2 f hfE) hf1
    have hfS : f ∈ S := hE₀S hfE
    have hef : e * f = f * e := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hez
      exact ((Commute.zpow_left (hcomm f hfS) k))
    obtain ⟨hab, hcard⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.RankOne.elemAbelian_pair
      Nat.prime_three he hfo hfe hef
    exact ⟨_, mem_sup_left (mem_zpowers e), hsup e heS f hfS, hab, by rw [hcard]; norm_num⟩
  · have hec : e * c = c * e := (hcomm e heS).symm
    obtain ⟨hab, hcard⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.RankOne.elemAbelian_pair
      Nat.prime_three he hco hce hec
    exact ⟨_, mem_sup_left (mem_zpowers e), hsup e heS c hcS, hab, by rw [hcard]; norm_num⟩

theorem list880ThreeInE9_holds : List880ThreeInE9 := by
  intro X _ _ _ h3 S hS e heS he
  exact exists_E9_of_pRank_three_eq_two h3 S hS e heS he

theorem j2FivePRank_holds :
    J2FivePRank := by
  intro X _ _ h
  refine ⟨pRank_five_eq_two_of_isSpor_J2 h, fun p hp hp5 hp5' => ?_⟩
  obtain ⟨e⟩ := h
  have hcard : Nat.card (⊤ : Subgroup X) = 2 ^ 7 * 3 ^ 3 * 5 ^ 2 * 7 := by
    rw [Subgroup.card_top, Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J2.card_J2
  refine CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ hp ?_
  rw [hcard]
  intro hdvd
  have hp1 : p ∣ 2 ^ 7 * 3 ^ 3 * 5 ^ 2 * 7 := dvd_trans (dvd_pow_self p two_ne_zero) hdvd
  rcases (Nat.Prime.dvd_mul hp).mp hp1 with h1 | h7
  · rcases (Nat.Prime.dvd_mul hp).mp h1 with h1 | h5
    · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h3
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2); omega
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3); omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp (hp.dvd_of_dvd_pow h5); omega
  · have h7' := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).mp h7
    subst h7'
    norm_num at hdvd

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
