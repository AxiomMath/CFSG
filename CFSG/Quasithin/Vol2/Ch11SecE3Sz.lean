module

public import CFSG.Quasithin.Vol2.Ch11SecE3L0
public import CFSG.RankThree.SteinbergR3ESuzukiInvolutionCentralizers
public import CFSG.Quasithin.Background.A3StructureDefs
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3

open CFSG.Open CFSG.Blueprint CFSG.LieType.Ree
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section Suzuki

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem card_le_of_isElemAbelian_suzuki (hK : Nat.card K = 2 ^ (2 * a + 1))
    {A : Subgroup (suzukiGroup a K)} (hA : IsElemAbelian 2 A) : Nat.card A ≤ Nat.card K := by
  have := finite_suzukiGroup hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P := Sylow.ofCard (suzukiU a K) (CFSG.RankThree.card_suzukiU_eq hK)
  obtain ⟨Q, hAQ⟩ := (B2F.isPGroup_of_isElemAbelian hA).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (suzukiGroup a K) P Q
  let f : K → suzukiGroup a K := fun v => g * suzukiSElt a K 0 v * g⁻¹
  have hsub : (A : Set (suzukiGroup a K)) ⊆ Set.range f := by
    intro z hz
    have hzQ : z ∈ (g • P : Sylow 2 (suzukiGroup a K)) := hg ▸ hAQ hz
    rw [CFSG.RankThree.mem_smul_sylow_iff] at hzQ
    by_cases hz1 : g⁻¹ * z * g = 1
    · refine ⟨0, ?_⟩
      have hz' : z = 1 := by
        have := congrArg (fun y => g * y * g⁻¹) hz1
        simpa [mul_assoc] using this
      show g * suzukiSElt a K 0 0 * g⁻¹ = z
      rw [suzukiSElt_zero_zero hK, mul_one, mul_inv_cancel, hz']
    · have hz2 : (g⁻¹ * z * g) ^ 2 = 1 := by
        rw [show g⁻¹ * z * g = (MulAut.conj g⁻¹) z by simp, ← map_pow, hA.2 z hz, map_one]
      obtain ⟨v, -, hv⟩ := CFSG.RankThree.eq_suzukiSElt_zero_of_sq_eq_one hK hzQ hz2 hz1
      refine ⟨v, ?_⟩
      show g * suzukiSElt a K 0 v * g⁻¹ = z
      rw [← hv]
      group
  calc Nat.card A = Nat.card (A : Set (suzukiGroup a K)) := rfl
    _ ≤ Nat.card (Set.range f) := Nat.card_mono (Set.toFinite _) hsub
    _ ≤ Nat.card K := Finite.card_range_le f

theorem suzuki_nonabelian (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ x y : suzukiGroup a K, x * y ≠ y * x := by
  by_contra hc
  push Not at hc
  have hcomm := (suzuki_perfect ha hK).1
  have hbot : commutator (suzukiGroup a K) = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact fun x _ => Subgroup.mem_centralizer_iff.mpr fun y _ => hc y x
  have h1 : (suzukiSElt a K 0 1 : suzukiGroup a K) = 1 := by
    have hmem : suzukiSElt a K 0 1 ∈ commutator (suzukiGroup a K) := hcomm ▸ Subgroup.mem_top _
    rwa [hbot, Subgroup.mem_bot] at hmem
  rw [← suzukiSElt_zero_zero hK, suzukiSElt_inj] at h1
  exact one_ne_zero h1.2

end Suzuki

section OddOuter

variable {G : Type} [Group G] [Finite G]

theorem mem_of_pow_two_pow_eq_one {L : Subgroup G} [L.Normal]
    (hC : Subgroup.centralizer (L : Set G) = ⊥) (hOut : Odd (Nat.card (Outer ↥L))) {t : G}
    {k : ℕ} (ht : t ^ 2 ^ k = 1) : t ∈ L := by
  have : Finite (MulAut ↥L) := MulEquiv.finite_left
  set φ : G →* MulAut ↥L := MulAut.conjNormal with hφ
  set π := QuotientGroup.mk' (inner ↥L) with hπ
  have h1 : (π (φ t)) ^ 2 ^ k = 1 := by rw [← map_pow, ← map_pow, ht, map_one, map_one]
  have h2 : orderOf (π (φ t)) ∣ Nat.card (Outer ↥L) := orderOf_dvd_natCard _
  have h3 : orderOf (π (φ t)) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  have h4 : orderOf (π (φ t)) = 1 := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
    rcases i with _ | i
    · simpa using hi
    · rw [hi] at h2
      exact absurd (dvd_trans (dvd_pow_self 2 (Nat.succ_ne_zero i)) h2) hOut.not_two_dvd_nat
  have h5 : φ t ∈ inner ↥L := (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp h4)
  obtain ⟨l, hl⟩ := h5
  rw [← MulAut.conjNormal_val] at hl
  have h6 : (l : G)⁻¹ * t ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h7 := congrArg (fun α : MulAut ↥L => ((α ⟨x, hx⟩ : ↥L) : G)) hl
    simp only [hφ, MulAut.conjNormal_apply] at h7
    calc x * ((l : G)⁻¹ * t) = (l : G)⁻¹ * ((l : G) * x * (l : G)⁻¹) * t := by group
      _ = (l : G)⁻¹ * (t * x * t⁻¹) * t := by rw [h7]
      _ = (l : G)⁻¹ * t * x := by group
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at h6
  exact h6 ▸ l.2

end OddOuter

section Transport

theorem isElemAbelian_map {X Y : Type*} [Group X] [Group Y] (f : X →* Y) {A : Subgroup X}
    (hA : IsElemAbelian 2 A) : IsElemAbelian 2 (A.map f) := CFSG.SectionRank.isElemAbelian_map hA _

theorem isElemAbelian_subgroupOf {X : Type*} [Group X] {A : Subgroup X} (hA : IsElemAbelian 2 A)
    (H : Subgroup X) : IsElemAbelian 2 (A.subgroupOf H) := CFSG.Open.IsElemAbelian.subgroupOf hA H

end Transport

section Main

variable {G : Type} [Group G] [Finite G]

theorem nParam_le_of_isSz {T : Subgroup G} {n : ℕ} (hSz : IsSz n ↥(CFSG.generalizedFitting G))
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) : E1.nParam (⊤ : Subgroup G) ≤ n := by
  have hOut := (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} _ 2 n
    hSz).1.2.2
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := hSz
  have hnab : ∃ x y : ↥(CFSG.generalizedFitting G), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := suzuki_nonabelian ha hK
    refine ⟨e.symm x, e.symm y, fun h => hxy ?_⟩
    simpa using congrArg e h
  have h := almostSimple_generalizedFitting hs hnab hT.1 hFT
  have := h.normal
  have hTF : T ≤ CFSG.generalizedFitting G := fun t ht => by
    obtain ⟨k, hk⟩ := hT.1 ⟨t, ht⟩
    exact mem_of_pow_two_pow_eq_one h.centralizer_eq hOut (by simpa using congrArg Subtype.val hk)
  have hF : CFSG.generalizedFitting G = ⊤ := by rw [← hFT, sup_eq_left.mpr hTF]
  refine nParam_le_of_card_le hs hnab hT hFT (by omega) fun A hA => ?_
  have hAF : A ≤ CFSG.generalizedFitting G := hF ▸ le_top
  have hA' := isElemAbelian_map e.toMonoidHom (isElemAbelian_subgroupOf hA
    (CFSG.generalizedFitting G))
  have h1 : Nat.card ↥((A.subgroupOf (CFSG.generalizedFitting G)).map e.toMonoidHom) =
      Nat.card A := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAF).toEquiv
  rw [← h1, ← hK]
  exact card_le_of_isElemAbelian_suzuki hK hA'

end Main

end CFSG.Quasithin.Vol2.Ch11.SecE3
