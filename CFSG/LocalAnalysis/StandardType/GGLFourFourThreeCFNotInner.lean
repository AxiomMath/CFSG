module

public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeMarking

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTableBNbrInnerInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
        GGMarkingAll (K := ↥K) fun _ _ _ I _ θ =>
          (∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I) →
          ∀ Y : Subgroup G, Y ≤ Subgroup.centralizer ({y} : Set G) →
            Y ≤ Subgroup.normalizer (Bs : Set G) → Y ≤ Subgroup.normalizer (K : Set G) →
            Subgroup.centralizer (Bs : Set G) ≤ Y →
            (∀ n ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({y} : Set G),
              ∀ g ∈ Y, n * g * n⁻¹ ∈ Y) →
            (∀ g ∈ Y, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (Bs : Set G)) →
            ∀ g ∈ Y, ∀ b ∈ Bs, g * b * g⁻¹ * b⁻¹ ∈ Subgroup.centralizer (K : Set G)

section Count

variable {G : Type} [Group G] [Finite G]

theorem card_mul_card_le_card_mul_card_inf {H B S : Subgroup G} (hHS : H ≤ S) (hBS : B ≤ S) :
    Nat.card H * Nat.card B ≤ Nat.card S * Nat.card (B ⊓ H : Subgroup G) := by
  have h1 : Nat.card (B ⊓ H : Subgroup G) * B.relIndex H = Nat.card H := by
    have h := Subgroup.card_mul_index (B.subgroupOf H)
    rwa [← Subgroup.card_map_of_injective H.subtype_injective,
      Subgroup.subgroupOf_map_subtype] at h
  have h2 : B.relIndex H ≤ B.relIndex S :=
    Subgroup.relIndex_le_of_le_right hHS (Subgroup.index_ne_zero_of_finite (H := B.subgroupOf S))
  have h3 : Nat.card B * B.relIndex S = Nat.card S := by
    have h := Subgroup.card_mul_index (B.subgroupOf S)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBS).toEquiv] at h
  calc Nat.card H * Nat.card B
      = Nat.card (B ⊓ H : Subgroup G) * (B.relIndex H * Nat.card B) := by rw [← h1]; ring
    _ ≤ Nat.card (B ⊓ H : Subgroup G) * (B.relIndex S * Nat.card B) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h2)
    _ = Nat.card S * Nat.card (B ⊓ H : Subgroup G) := by rw [← h3]; ring

theorem false_of_card_bstar_le {p : ℕ} (hp : p.Prime) {B Bs T₀ H : Subgroup G} (hBBs : B ≤ Bs)
    (hT₀H : T₀ ≤ H) (hHBs : H ≤ Bs) (hBH : Nat.card (B ⊓ H : Subgroup G) ≤ p)
    (hcard : Nat.card Bs ≤ p * p * Nat.card T₀) (hB4 : p ^ 4 ≤ Nat.card B) : False := by
  have h1 := card_mul_card_le_card_mul_card_inf hHBs hBBs
  have h2 : Nat.card T₀ ≤ Nat.card H := Subgroup.card_le_of_le hT₀H
  have hT₀pos : 0 < Nat.card T₀ := Nat.card_pos
  have h3 : Nat.card T₀ * Nat.card B ≤ Nat.card T₀ * (p * p * p) := by
    calc Nat.card T₀ * Nat.card B ≤ Nat.card H * Nat.card B := Nat.mul_le_mul_right _ h2
      _ ≤ Nat.card Bs * Nat.card (B ⊓ H : Subgroup G) := h1
      _ ≤ (p * p * Nat.card T₀) * p := Nat.mul_le_mul hcard hBH
      _ = Nat.card T₀ * (p * p * p) := by ring
  have h4 : Nat.card B ≤ p * p * p := Nat.le_of_mul_le_mul_left h3 hT₀pos
  have h5 : p * p * p < p ^ 4 := by
    have h6 : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    calc p * p * p = p ^ 3 := by ring
      _ < p ^ 4 := h6
  omega

end Count

section Config

variable {G : Type} [Group G] [Finite G]

theorem false_of_comm_mem_centralizer {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} (hFC : GGFieldCaseNoBL5 p B Bs x L D J X)
    (hM : GGTableBModule p Bs x L B₂) (h43 : GGL43 Bs x X) (h44ii : GGL44ii Bs x X B₂)
    {y : G} {K : Subgroup G} (hnbr : GGNbr p B x D J y K)
    (hXK : ∀ g ∈ X, g * x * g⁻¹ * x⁻¹ ∈ Subgroup.centralizer (K : Set G)) : False := by
  obtain ⟨hI, hBstar, -⟩ := hFC.1
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hBs : IsElemAbelian p Bs := hBstar.2.1
  have hBBs : B ≤ Bs := hBstar.1
  have hxBs : x ∈ Bs := hBBs hS.2.1
  have hBH : Nat.card (B ⊓ (Bs ⊓ Subgroup.centralizer (K : Set G)) : Subgroup G) ≤ p := by
    have h2 : B ⊓ (Bs ⊓ Subgroup.centralizer (K : Set G)) = Subgroup.zpowers y := by
      rw [← inf_assoc, inf_eq_left.mpr hBBs]
      exact inf_centralizer_eq_zpowers_of_sHat hnbr.1
    have hy : orderOf y = p := orderOf_eq_prime (hnbr.1.1.1.2 y hnbr.1.2.1) hnbr.1.2.2.1
    rw [h2, Nat.card_zpowers, hy]
  have hB4 : p ^ 4 ≤ Nat.card B := by
    rw [hS.1.2.1]
    exact Nat.pow_le_pow_right hp.pos hI.2.2.2.2.2.1.2.2.2
  have hc4 : Nat.card Bs ≤ Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) * p :=
    card_bstar_le_of_ggL43 hBs hxBs hS.2.2.1 h43
  have hcomm : ∀ b : G, (∃ g ∈ X, g * x * g⁻¹ * x⁻¹ = b) →
      b ∈ Bs ⊓ Subgroup.centralizer (K : Set G) := by
    rintro b ⟨g, hg, rfl⟩
    refine ⟨Bs.mul_mem ((Subgroup.mem_normalizer_iff.mp (hFC.2.1 hg) x).mp hxBs)
      (Bs.inv_mem hxBs), hXK g hg⟩
  rcases h44ii with h44a | ⟨-, h44b⟩
  · refine false_of_card_bstar_le hp hBBs (T₀ := Bs ⊓ Subgroup.centralizer (X : Set G))
      (fun b hb => hcomm b ((h44a b).1 hb)) inf_le_left hBH ?_ hB4
    calc Nat.card Bs ≤ Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) * p := hc4
      _ ≤ p * p * Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) := by
          nlinarith [hp.one_lt]
  · have hc3 : Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) ≤
        p * Nat.card (B₂ ⊓ (Bs ⊓ Subgroup.centralizer (X : Set G)) : Subgroup G) :=
      card_le_mul_card_inf inf_le_left hM.2.1 hM.2.2.1
    rw [inf_comm B₂] at hc3
    refine false_of_card_bstar_le hp hBBs
      (T₀ := Bs ⊓ Subgroup.centralizer (X : Set G) ⊓ B₂)
      (fun b hb => hcomm b ((h44b b).1 hb)) inf_le_left hBH ?_ hB4
    calc Nat.card Bs ≤ Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) * p := hc4
      _ ≤ (p * Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) ⊓ B₂ : Subgroup G)) * p :=
          Nat.mul_le_mul_right p hc3
      _ = p * p * Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) ⊓ B₂ : Subgroup G) := by ring

end Config

theorem ggL44iiiNotInnerInput_of_tableB (hL : GGLBalanceInput) (hJp : GGStdSubPrimeInput)
    (hI2 : GGStdSubBstarMeetInput) (hTBK : GGTableBNbrInnerInput) : GGL44iiiNotInnerInput := by
  intro G _ _ p B Bs x L D J X B₂ hFC hM h43 h44 h44ii d hd _ y K hnbr hyd hN P hP
  obtain ⟨hI, hBstar, hDJ⟩ := hFC.1
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hxBs : x ∈ Bs := hBstar.1 hS.2.1
  have hpJ : p ∣ Nat.card J := hJp G p B x L D J hI hDJ
  have hKd : LargeEvenPComponent p (Subgroup.centralizer ({d} : Set G)) K := by
    rw [← centralizer_singleton_eq_of_zpowers_eq hyd]
    exact hnbr.1.2.2.2.2.1
  have hXK : X ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_ggL44i hFC h44 hpJ (hI2 G p B Bs x L D J hFC.1) hd.2.2 hKd
      (le_of_ggNbr hL hI hDJ hpJ hnbr)
  have hXy : X ≤ Subgroup.centralizer ({y} : Set G) := by
    rw [centralizer_singleton_eq_of_zpowers_eq hyd]
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hd.2.2 g hg)
  have hXn : ∀ n ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({y} : Set G),
      ∀ g ∈ X, n * g * n⁻¹ ∈ X := by
    intro n hn g hg
    have := hFC.2.2.2.1.conj_mem ⟨g, hFC.2.1 hg⟩ (Subgroup.mem_subgroupOf.mpr hg) ⟨n, hn.1⟩
    simpa [Subgroup.mem_subgroupOf] using this
  refine largeEvenMarking_mono ?_ (hTBK G p B Bs x L D J hFC.1 y K hnbr hN P hP)
  rintro lab R _ I F θ ⟨hPθ, hQ⟩
  refine ⟨hPθ, fun _ => ?_⟩
  by_contra hcon
  have hall : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => by_contra fun h => hcon ⟨b, hb, h⟩
  have hcK := hQ hall X hXy hFC.2.1 hXK hFC.2.2.1 hXn hFC.2.2.2.2.1
  exact false_of_comm_mem_centralizer hFC hM h43 h44ii hnbr fun g hg => hcK g hg x hxBs

end CFSG.StandardType

end
