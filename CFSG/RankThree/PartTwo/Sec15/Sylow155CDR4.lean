module

public import CFSG.RankThree.PartTwo.Sec14.Std
import CFSG.RankThree.PartTwo.Sec15.Item15Res6ProofComp
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartTwo.Sec14.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155CD

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem false_of_elemAbelian_quot {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {C : Subgroup G} {N : Subgroup ↥C} [N.Normal] (hN : ¬ 3 ∣ Nat.card N)
    {E T : Subgroup (↥C ⧸ N)} (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE81 : Nat.card E = 81)
    (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hET : E ≤ Subgroup.normalizer (T : Set (↥C ⧸ N))) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hPE, hP, hPcard⟩ := CFSG.RankThree.Classical2.exists_elemAbelian_lift N hN hE
  set D : Subgroup ↥C := T.comap (QuotientGroup.mk' N)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hT1 (Subgroup.card_eq_one.mp (hn.trans (pow_zero 2)))
  have hDcard : Nat.card D = Nat.card N * 2 ^ n := by
    rw [← hn]
    exact QuotientGroup.card_preimage_mk N (T : Set (↥C ⧸ N))
  have hcop : Nat.Coprime 3 (Nat.card D) := by
    rw [hDcard]
    exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN)
      (Nat.Coprime.pow_right n (by norm_num))
  have h2 : 2 ∣ Nat.card D := by
    rw [hDcard]
    exact Dvd.dvd.mul_left (dvd_pow_self 2 hn0) _
  have hPD : P ≤ Subgroup.normalizer (D : Set ↥C) := by
    intro p hp
    have hpE := Subgroup.mem_normalizer_iff.mp (hET (hPE hp))
    rw [Subgroup.mem_normalizer_iff]
    intro x
    change QuotientGroup.mk' N x ∈ T ↔ QuotientGroup.mk' N (p * x * p⁻¹) ∈ T
    rw [map_mul, map_mul, map_inv]
    exact hpE _
  obtain ⟨S, hPS, hS0⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial 3 2
      Nat.prime_three Nat.prime_two P D hP.isPGroup hPD hcop h2
  set S' : Subgroup G := ((S : Subgroup D).map D.subtype).map C.subtype
  have hS'2 : IsPGroup 2 S' := (S.isPGroup'.map D.subtype).map C.subtype
  have hS'1 : S' ≠ ⊥ := fun h0 =>
    hS0 ((Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp h0)
  have hFS : P.map C.subtype ≤ Subgroup.normalizer (S' : Set G) :=
    (Subgroup.map_mono hPS).trans (Subgroup.le_normalizer_map C.subtype)
  have hF : CFSG.Assembly.IsElemAbelian 3 (P.map C.subtype) := hP.map C.subtype
  have hF81 : Nat.card (P.map C.subtype) = 81 := by
    rw [Subgroup.card_map_of_injective C.subtype_injective, hPcard, hE81]
  have hO : CFSG.Open.pCoreOf 2 (Subgroup.normalizer (S' : Set G)) ≠ ⊥ := by
    intro h0
    have hle : S' ≤ CFSG.Open.pCoreOf 2 (Subgroup.normalizer (S' : Set G)) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hS'2
    rw [h0] at hle
    exact hS'1 (le_bot_iff.mp hle)
  exact Proof15Res6.false_of_e81_le h hO hF hF81 hFS

theorem eq_bot_of_normal_quot {C Y : Subgroup G} (hYC : Y ≤ C) (hOY : pPrimeCoreOf 3 C ≤ Y)
    [((pPrimeCoreOf 3 Y).subgroupOf C).Normal]
    {N : Subgroup (↥C ⧸ (pPrimeCoreOf 3 Y).subgroupOf C)} (hN : N.Normal)
    (hN3 : ¬ 3 ∣ Nat.card N) : N = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := pPrimeCoreOf 3 Y
  set K := θ.subgroupOf C with hK
  set π := QuotientGroup.mk' K
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective K
  have hθC : θ ≤ C := (pPrimeCoreOf_le 3 Y).trans hYC
  have hKcard : ¬ 3 ∣ Nat.card K := by
    rw [hK, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hθC).toEquiv]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y)
  set M : Subgroup G := (N.comap π).map C.subtype with hM
  have hNcard : Nat.card (N.comap π) = Nat.card K * Nat.card N :=
    QuotientGroup.card_preimage_mk K (N : Set (↥C ⧸ K))
  have hMcard : ¬ 3 ∣ Nat.card M := by
    rw [hM, Subgroup.card_map_of_injective C.subtype_injective, hNcard]
    intro h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h3 | h3
    exacts [hKcard h3, hN3 h3]
  have hMcop : Nat.Coprime 3 (Nat.card M) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hMcard
  have hMC : M ≤ C := Subgroup.map_subtype_le _
  have hCM : C ≤ Subgroup.normalizer (M : Set G) := by
    have h1 : Subgroup.normalizer ((N.comap π : Subgroup ↥C) : Set ↥C) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr (hN.comap π)
    have h2 := Subgroup.le_normalizer_map (H := N.comap π) C.subtype
    have h3 : (⊤ : Subgroup ↥C).map C.subtype = C := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rwa [h1, h3] at h2
  have hMY : M ≤ Y := (le_pPrimeCoreOf hMC hCM hMcop).trans hOY
  have hMθ : M ≤ θ := le_pPrimeCoreOf hMY (hYC.trans hCM) hMcop
  refine (Subgroup.eq_bot_iff_forall N).mpr fun n hn => ?_
  obtain ⟨x, rfl⟩ := hπs n
  have hxM : (x : G) ∈ M := ⟨x, hn, rfl⟩
  exact (QuotientGroup.eq_one_iff x).mpr (Subgroup.mem_subgroupOf.mpr (hMθ hxM))

theorem pPrimeCoreOf_le_of_le_normalizer {C Y : Subgroup G} (hYC : Y ≤ C)
    (hCY : C ≤ Subgroup.normalizer (Y : Set G)) : pPrimeCoreOf 3 Y ≤ pPrimeCoreOf 3 C := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact le_pPrimeCoreOf ((pPrimeCoreOf_le 3 Y).trans hYC)
    (hCY.trans (normalizer_le_normalizer_pPrimeCoreOf 3 Y)) (coprime_card_pPrimeCoreOf 3 Y)

end CFSG.RankThree.PartTwo.Sec15.Sylow155CD
