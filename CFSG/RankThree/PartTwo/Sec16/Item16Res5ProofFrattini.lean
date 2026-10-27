module

public import CFSG.RankThree.PartTwo.Sec16.Item16Res5ProofEndRep
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
import CFSG.RankThree.PartTwo.Sec16.Item16TailEnd
public import CFSG.RankThree.PartTwo.Sec16.Item16TailMore

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)
open scoped Pointwise

namespace Proof1623Frattini

variable {G : Type} [Group G] [Finite G]

theorem isSylowOf_of_maximal {A O S : Subgroup G} (hA3 : IsPGroup 3 A)
    (hAO : A ≤ Subgroup.normalizer (O : Set G)) (hO3 : ¬ 3 ∣ Nat.card O) (hSO : S ≤ O)
    (hS2 : IsPGroup 2 S) (hAS : A ≤ Subgroup.normalizer (S : Set G))
    (hmax : ∀ T : Subgroup G, T ≤ O → IsPGroup 2 T → A ≤ Subgroup.normalizer (T : Set G) →
      S ≤ T → T ≤ S) : IsSylowOf 2 S O := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := O ⊓ Subgroup.normalizer (S : Set G) with hN
  have hSN : S ≤ N := le_inf hSO Subgroup.le_normalizer
  have hAN : A ≤ Subgroup.normalizer (N : Set G) :=
    CFSG.RankThree.PartTwo.Late.le_normalizer_inf hAO (hAS.trans Subgroup.le_normalizer)
  have hNcop : Nat.Coprime 3 (Nat.card N) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 =>
      hO3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  obtain ⟨T₀, hAT₀⟩ := CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow 3 2
    Nat.prime_three Nat.prime_two A N hA3 hAN hNcop
  set T := (T₀ : Subgroup N).map N.subtype with hT
  have hSnorm : (S.comap N.subtype).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSN).mpr inf_le_right
  have hST₀ : S.comap N.subtype ≤ (T₀ : Subgroup N) :=
    IsPGroup.le_sylow_of_normal hS2.comap_subtype T₀
  have hST : S ≤ T := by
    intro x hx
    exact ⟨⟨x, hSN hx⟩, hST₀ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hTN : T ≤ N := Subgroup.map_subtype_le _
  have hT2 : IsPGroup 2 T := T₀.isPGroup'.map _
  have hTS : T = S := le_antisymm (hmax T (hTN.trans inf_le_left) hT2 hAT₀ hST) hST
  have hSylN : IsSylowOf 2 S N := ⟨T₀, hT.symm.trans hTS⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS2
  refine isSylowOf_of_card hSO ?_
  rw [hn]
  congr 1
  have hdvd : 2 ^ n ∣ Nat.card O := hn ▸ Subgroup.card_dvd_of_le hSO
  have hle : n ≤ (Nat.card O).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd
  refine le_antisymm hle ?_
  by_contra hlt
  push Not at hlt
  have hdvd1 : 2 ^ (n + 1) ∣ Nat.card O :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mpr hlt
  have hcardS : Nat.card (S.subgroupOf O) = 2 ^ n := by
    rw [← hn]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSO).toEquiv
  have hnorm := Sylow.prime_pow_dvd_card_normalizer (G := ↥O) hdvd1 hcardS
  rw [← Subgroup.subgroupOf_normalizer_eq hSO] at hnorm
  have hcardN : Nat.card ((Subgroup.normalizer (S : Set G)).subgroupOf O) = Nat.card N := by
    rw [← Subgroup.card_map_of_injective O.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  rw [hcardN] at hnorm
  have hSN' := hSylN.card_eq
  rw [hn] at hSN'
  have hfac : n = (Nat.card N).factorization 2 :=
    Nat.pow_right_injective (le_refl 2) hSN'
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hnorm
  omega

theorem exists_mem_inv_mul_mem_normalizer {H O S : Subgroup G}
    (hn : H ≤ Subgroup.normalizer (O : Set G)) (hS : IsSylowOf 2 S O) {x : G} (hx : x ∈ H) :
    ∃ y ∈ O, y⁻¹ * x ∈ Subgroup.normalizer (S : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxO : x ∈ Subgroup.normalizer (O : Set G) := hn hx
  have hS' : IsSylowOf 2 (S.map (MulAut.conj x).toMonoidHom) O := by
    refine isSylowOf_of_card ?_ ?_
    · rintro _ ⟨p, hp, rfl⟩
      have := (Subgroup.mem_normalizer_iff.1 hxO p).1 (hS.le hp)
      simpa [MulAut.conj_apply] using this
    · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, hS.card_eq]
  obtain ⟨k, hk, hconj⟩ := hS.exists_mem_conj hS'
  refine ⟨k, hk, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro p
  have e1 : x * p * x⁻¹ ∈ S.map (MulAut.conj x).toMonoidHom ↔ p ∈ S := by
    constructor
    · rintro ⟨q, hq, hqp⟩
      have : q = p := by
        have h' : x * q * x⁻¹ = x * p * x⁻¹ := by simpa [MulAut.conj_apply] using hqp
        simpa using h'
      exact this ▸ hq
    · intro hp
      exact ⟨p, hp, by simp [MulAut.conj_apply]⟩
  have e2 := hconj (x * p * x⁻¹)
  have e3 : k⁻¹ * (x * p * x⁻¹) * k = (k⁻¹ * x) * p * (k⁻¹ * x)⁻¹ := by group
  rw [e1, e3] at e2
  exact e2

theorem not_three_dvd_card_sup {O P : Subgroup G} (hPO : P ≤ Subgroup.normalizer (O : Set G))
    (hO3 : ¬ 3 ∣ Nat.card O) (hP2 : IsPGroup 2 P) : ¬ 3 ∣ Nat.card (O ⊔ P : Subgroup G) := by
  set J := O ⊔ P with hJ
  have hOJ : O ≤ J := le_sup_left
  have hPJ : P ≤ J := le_sup_right
  have hJN : J ≤ Subgroup.normalizer (O : Set G) := sup_le Subgroup.le_normalizer hPO
  have : (O.subgroupOf J).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOJ).mpr hJN
  set f : ↥P →* ↥J ⧸ O.subgroupOf J :=
    (QuotientGroup.mk' (O.subgroupOf J)).comp (Subgroup.inclusion hPJ) with hf
  have hfs : Function.Surjective f := by
    intro q
    obtain ⟨⟨j, hj⟩, rfl⟩ := QuotientGroup.mk'_surjective (O.subgroupOf J) q
    have hj' : j ∈ ((O : Set G) * (P : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left O P hPO]
      exact hj
    obtain ⟨o, ho, p, hp, rfl⟩ := hj'
    refine ⟨⟨p, hp⟩, ?_⟩
    rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf]
    change p⁻¹ * (o * p) ∈ O
    have := (Subgroup.mem_normalizer_iff.mp (hPO (P.inv_mem hp)) o).mp ho
    simpa [mul_assoc] using this
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (O.subgroupOf J)
  have hq : Nat.card (↥J ⧸ O.subgroupOf J) ∣ Nat.card P :=
    Subgroup.card_dvd_of_surjective (f := f) hfs
  have hO' : Nat.card (O.subgroupOf J) = Nat.card O :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOJ).toEquiv
  have hP3 : ¬ 3 ∣ Nat.card P := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP2
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  intro h3
  rw [hcard, hO'] at h3
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
  · exact hP3 (h.trans hq)
  · exact hO3 h

end Proof1623Frattini

open Proof1623Frattini

theorem step1623Frattini : Step1623Frattini := by
  intro G _ _ A c L h hLs n hn hU hΩ h21 hH R hRmin hR4 hRc hB9 hRb b hbB hb1 S hS hRS hSB
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Cb := Subgroup.centralizer ({b} : Set G) with hCb
  set O := pPrimeCoreOf 3 Cb with hO
  set P := CFSG.Open.pCoreOf 2 (Subgroup.centralizer (S : Set G)) ⊓ Cb with hP
  have hbA : b ∈ A := hbB.1
  have hA3 : IsPGroup 3 A := h.toSec14Std.isE27.isPGroup
  have hACb : A ≤ Cb := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (h.commute hx hbA)
  have hOCb : O ≤ Cb := pPrimeCoreOf_le 3 Cb
  have hCbO : Cb ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pPrimeCoreOf 3 Cb
  have hAO : A ≤ Subgroup.normalizer (O : Set G) := hACb.trans hCbO
  have hO3 : ¬ 3 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Cb)
  have hSO : S ≤ O := hS.prop.1.2
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hS.prop.2
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
  have hSyl : IsSylowOf 2 S O := by
    refine isSylowOf_of_maximal hA3 hAO hO3 hSO hS2 hAS fun T hTO hT2 hAT hST => ?_
    have hTQ : T ∈ scriptQ A (lB A) :=
      mem_scriptQ_of_le_of_normal hbA hTO hOCb hCbO hO3 hAT
    exact hS.2 ⟨⟨hTQ, hTO⟩, (isPiSubgroup_piOf_iff Nat.prime_two T).mpr hT2⟩ hST
  have hPCb : P ≤ Cb := inf_le_right
  have hNP : Subgroup.normalizer (S : Set G) ⊓ Cb ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.RankThree.PartTwo.Late.le_normalizer_inf
      (inf_le_left.trans ((Proof169.normalizer_le_normalizer_centralizer S).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)))
      (inf_le_right.trans Subgroup.le_normalizer)
  have hJn : Cb ≤ Subgroup.normalizer ((O ⊔ P : Subgroup G) : Set G) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := exists_mem_inv_mul_mem_normalizer hCbO hSyl hx
    have hm : y⁻¹ * x ∈ Cb := Cb.mul_mem (Cb.inv_mem (hOCb hy)) hx
    have hmJ : y⁻¹ * x ∈ Subgroup.normalizer ((O ⊔ P : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_sup O P ⟨hCbO hm, hNP ⟨hyx, hm⟩⟩
    have hyJ : y ∈ Subgroup.normalizer ((O ⊔ P : Subgroup G) : Set G) :=
      Subgroup.le_normalizer (le_sup_left (a := O) hy)
    have := Subgroup.mul_mem _ hyJ hmJ
    simpa using this
  have hP2 : IsPGroup 2 P :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left
  have hJ3 := not_three_dvd_card_sup (hPCb.trans hCbO) hO3 hP2
  have hJO : O ⊔ P ≤ O :=
    le_pPrimeCoreOf (sup_le hOCb hPCb) hJn
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hJ3)
  exact le_sup_right.trans hJO

end CFSG.RankThree.PartTwo.Sec16
