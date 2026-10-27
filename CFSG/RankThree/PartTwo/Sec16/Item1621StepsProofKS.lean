module

public import CFSG.RankThree.PartTwo.Sec16.Item16Tail24
import CFSG.RankThree.PartTwo.Sec21.Item22L2
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] noncomputable def KS1624ParaKP1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (m' : ℕ), 1 ≤ m' →
    Nonempty (↥L ≃* projSL 3 (GaloisField 2 m')) →
    ∀ (b : G) (m p : ℕ) (P V X : Subgroup G), p.Prime → 3 < p → Data1623 L b m p P V X →
      IsShort (kPara1623 L V) ∧ IsTypeScriptL (kPara1623 L V) ∧
      (∀ R : Subgroup G, R ≤ L → IsPGroup 2 R →
        kPara1623 L V ≤ Subgroup.normalizer (R : Set G) → R ≤ V) ∧
      (∀ Y : Subgroup G, kPara1623 L V ≤ Y → Y ≤ L → Y ≠ L →
        inSubgroup perfectResidual Y = kPara1623 L V) ∧
      V = ⁅V, kPara1623 L V⁆

namespace Proof1624KS

variable {G : Type} [Group G] [Finite G]

theorem four_le_card_galoisField {L V X P : Subgroup G} {b : G} {m p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hD : Data1623 L b m p P V X) : 4 ≤ Nat.card (GaloisField 2 m) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := kPara1623 L V with hKdef
  obtain ⟨hVn, ⟨e⟩⟩ := hD.quot
  set V' := V.subgroupOf K with hV'
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2 * m) hD.card
  have hV'2 : IsPGroup 2 V' := hV2.of_equiv (Subgroup.subgroupOfEquivOfLe hD.le_V).symm
  have hpX : p ∣ Nat.card X := by rw [hD.card_X]
  have hpK : p ∣ Nat.card K := hpX.trans (Subgroup.card_dvd_of_le hD.le_K)
  have hpV : ¬ p ∣ Nat.card V' := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hV'2
    rw [hk]
    intro hdvd
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd)
    omega
  have hpQ : p ∣ Nat.card (↥K ⧸ V') := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup V'
    rw [h1] at hpK
    exact (Nat.Prime.dvd_mul hp).mp hpK |>.resolve_right hpV
  set F := GaloisField 2 m with hF
  have hQc : Nat.card (↥K ⧸ V') = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [Nat.card_congr (e.trans (Sec21.projSLTwoEquivSL F)).toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  by_contra hlt
  have h2 : 2 ∣ Nat.card F := by
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact (CharP.cast_eq_zero_iff F 2 _).mp (by simp)
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  have hF2 : Nat.card F = 2 := by omega
  rw [hQc, hF2] at hpQ
  have : p ≤ 6 := Nat.le_of_dvd (by norm_num) hpQ
  interval_cases p
  · norm_num at hp
  · norm_num at hpQ
  · norm_num at hp

theorem normal_eq_of_le {L V X P : Subgroup G} {b : G} {m p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hD : Data1623 L b m p P V X) {N : Subgroup G} (hNK : N ≤ kPara1623 L V)
    (hKN : kPara1623 L V ≤ Subgroup.normalizer (N : Set G)) (hXN : X ≤ N) :
    N = kPara1623 L V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := kPara1623 L V with hKdef
  obtain ⟨hVn, ⟨e⟩⟩ := hD.quot
  set V' := V.subgroupOf K with hV'
  set N' := N.subgroupOf K with hN'
  have hN'n : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hKN
  have hKperf : Group.IsPerfect ↥K :=
    CFSG.RankThree.PartOne.EmbeddingFixedResidual.isPerfect_inSubgroup_perfectResidual _
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2 * m) hD.card
  have hV'2 : IsPGroup 2 V' := hV2.of_equiv (Subgroup.subgroupOfEquivOfLe hD.le_V).symm
  set F := GaloisField 2 m with hF
  have hF4 : 4 ≤ Nat.card F := four_le_card_galoisField hp hp3 hD
  have hsimp : IsSimpleGroup (↥K ⧸ V') := by
    have := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF4
    exact (e.trans (Sec4.projSLEquivPSL F)).isSimpleGroup
  have hmapn : (N'.map (QuotientGroup.mk' V')).Normal :=
    hN'n.map _ (QuotientGroup.mk'_surjective V')
  have htop : N' ⊔ V' = ⊤ := by
    rcases hmapn.eq_bot_or_eq_top with h1 | h1
    · exfalso
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1
      have hXV : X ≤ V := by
        intro x hx
        have hx' : (⟨x, hD.le_K hx⟩ : K) ∈ N' := Subgroup.mem_subgroupOf.mpr (hXN hx)
        exact Subgroup.mem_subgroupOf.mp (h1 hx')
      have := Subgroup.card_dvd_of_le hXV
      rw [hD.card_X] at this
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hV2
      rw [hk] at this
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow this)
      omega
    · have hcomap := Subgroup.comap_map_eq (QuotientGroup.mk' V') N'
      rw [h1, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
      exact hcomap.symm
  have hsurj : Function.Surjective ((QuotientGroup.mk' N').comp V'.subtype) := by
    intro z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective N' z
    have hk : k ∈ N' ⊔ V' := htop ▸ Subgroup.mem_top k
    rw [Subgroup.mem_sup_of_normal_left] at hk
    obtain ⟨n, hn, v, hv, rfl⟩ := hk
    refine ⟨⟨v, hv⟩, ?_⟩
    change (QuotientGroup.mk' N') v = (QuotientGroup.mk' N') (n * v)
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have := hN'n.conj_mem n hn (v : K)⁻¹
    simpa [mul_assoc] using this
  have hQ2 : IsPGroup 2 (↥K ⧸ N') := by
    intro z
    obtain ⟨v, rfl⟩ := hsurj z
    obtain ⟨k, hk⟩ := hV'2 v
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  have hQperf : Group.IsPerfect (↥K ⧸ N') :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N') (QuotientGroup.mk'_surjective N')
  have hQ1 : Subsingleton (↥K ⧸ N') := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    have : Group.IsNilpotent (↥K ⧸ N') := hQ2.isNilpotent
    exact Group.IsPerfect.not_isSolvable (↥K ⧸ N') inferInstance
  have hN'top : N' = ⊤ := by
    rw [eq_top_iff]
    intro k _
    have : (QuotientGroup.mk' N' k) = 1 := Subsingleton.elim _ _
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  apply le_antisymm hNK
  intro k hk
  have : (⟨k, hk⟩ : K) ∈ N' := hN'top ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

end Proof1624KS

open Proof1624KS

theorem ks1624Para_of (h : KS1624ParaKP1) : KS1624Para := by
  intro G _ _ L m' hm' hL b m p P V X hp hp3 hD
  obtain ⟨ha, hty, hc, hd, -⟩ := h G L m' hm' hL b m p P V X hp hp3 hD
  exact ⟨ha, hty, fun N hNK hKN hXN => normal_eq_of_le hp hp3 hD hNK hKN hXN, hc, hd⟩

end CFSG.RankThree.PartTwo.Sec16
