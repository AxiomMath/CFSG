module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KJ2Nine
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.InvolutionCentralizers

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem k91j2in_isPGroup_of_card_dvd {G : Type} [Group G] (h : Nat.card G ∣ 16) :
    IsPGroup 2 G := by
  obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show Nat.card G ∣ 2 ^ 4 from h)
  exact IsPGroup.of_card hn

private theorem k91j2in_card_stabilizer_dvd {J : Type} [Group J] [Finite J] (K T : Subgroup J)
    (hKN : K ≤ normalizer (T : Set J)) (t : T) :
    Nat.card ((MulAction.stabilizer (MulAut T) t).comap
        (T.normalizerMonoidHom.comp (Subgroup.inclusion hKN))) ∣
      Nat.card (centralizer ({(t : J)} : Set J)) := by
  have hle : ((MulAction.stabilizer (MulAut T) t).comap
        (T.normalizerMonoidHom.comp (Subgroup.inclusion hKN))).map K.subtype ≤
        centralizer ({(t : J)} : Set J) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hk' : (T.normalizerMonoidHom.comp (Subgroup.inclusion hKN)) k t = t := hk
    have := congrArg Subtype.val hk'
    simp only [MonoidHom.comp_apply, normalizerMonoidHom_apply_apply_coe] at this
    simp only [coe_subtype]
    calc (k : J) * t = k * t * (k : J)⁻¹ * k := by group
      _ = t * k := by
        rw [show ((Subgroup.inclusion hKN k : normalizer (T : Set J)) : J) = k from rfl] at this
        rw [this]
  have hdvd := Subgroup.card_dvd_of_le hle
  rwa [Subgroup.card_map_of_injective K.subtype_injective] at hdvd

theorem j2AutCore_eq_bot_of_card_dvd_sixteen
    {J : Type} [Group J] [Finite J] (hJ : IsSpor J .J2)
    (K : Subgroup J) (hK : Nat.card K = 1080)
    (hnorm : ∀ N : Subgroup K, N.Normal → N = ⊤ ∨ N ≤ center K) (hZ : Nat.card (center K) = 3)
    (T : Subgroup J) (hKN : K ≤ normalizer (T : Set J)) (h16 : Nat.card T ∣ 16) : T = ⊥ := by
  by_contra hne
  have : Nontrivial T := (nontrivial_iff_ne_bot T).mpr hne
  obtain ⟨t, ht⟩ := exists_orderOf_eq_two_of_isPGroup (k91j2in_isPGroup_of_card_dvd h16)
  have ht1 : t ≠ 1 := by
    rintro rfl
    simp at ht
  have h9 := j2AutCore_nine_dvd_card_stabilizer
    (T.normalizerMonoidHom.comp (Subgroup.inclusion hKN)) hK hnorm hZ h16 t ht1
  have hdvd := k91j2in_card_stabilizer_dvd K T hKN t
  have htJ : orderOf (t : J) = 2 := by rw [Subgroup.orderOf_coe, ht]
  rcases CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.card_centralizer_of_involution_of_isSporadic_j2
      hJ (t : J) htJ with h | h <;>
    · rw [h] at hdvd
      have := h9.trans hdvd
      omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs
