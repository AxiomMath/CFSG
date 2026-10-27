module

import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.RankThree.PartTwo.Sec20.OneBasics
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

namespace Res8

variable {G : Type} [Group G] [Finite G]

theorem autIn_le_autIn_inf_centralizer {L B : Subgroup G} {c : G} (hc3 : c ^ 3 = 1)
    (hcL : c ∈ Subgroup.normalizer (L : Set G)) (hcB : ∀ b ∈ B, c * b = b * c)
    (hcent : ∀ x ∈ L, c * x * c⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 L) :
    Sec4.autIn L B ≤ Sec4.autIn (L ⊓ Subgroup.centralizer ({c} : Set G)) B := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Open.pCoreOf 2 L with hO
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hOL : O ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hLO : L ≤ Subgroup.normalizer (O : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hcO : c ∈ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hcL
  set O' := O ⊓ Subgroup.centralizer (B : Set G) with hO'
  set C3 := Subgroup.zpowers c with hC3
  have hlc : ∀ l ∈ L, l * c * l⁻¹ * c⁻¹ ∈ O := by
    intro l hl
    have h1 := hcent l⁻¹ (L.inv_mem hl)
    have h2 := (Subgroup.mem_normalizer_iff.mp (hLO hl) _).mp h1
    have e : l * c * l⁻¹ * c⁻¹ = l * (c * l⁻¹ * c⁻¹ * l⁻¹⁻¹) * l⁻¹ := by group
    rw [e]
    exact h2
  have hcO' : C3 ≤ Subgroup.normalizer (O' : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Sec20.mem_normalizer_inf_of_mem hcO ?_
    rw [Subgroup.mem_normalizer_iff]
    intro z
    simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    constructor
    · intro hz b hb
      have h1 := hz (c⁻¹ * b * c) (by
        have : c⁻¹ * b * c = b := by
          have := hcB b hb
          calc c⁻¹ * b * c = c⁻¹ * (b * c) := by group
            _ = c⁻¹ * (c * b) := by rw [this]
            _ = b := by group
        rw [this]; exact hb)
      have hbc : c⁻¹ * b * c = b := by
        have := hcB b hb
        calc c⁻¹ * b * c = c⁻¹ * (b * c) := by group
          _ = c⁻¹ * (c * b) := by rw [this]
          _ = b := by group
      rw [hbc] at h1
      calc b * (c * z * c⁻¹) = c * (c⁻¹ * b * c) * z * c⁻¹ := by group
        _ = c * b * z * c⁻¹ := by rw [hbc]
        _ = c * (b * z) * c⁻¹ := by group
        _ = c * (z * b) * c⁻¹ := by rw [h1]
        _ = c * z * c⁻¹ * (c * b * c⁻¹) := by group
        _ = c * z * c⁻¹ * b := by
            rw [show c * b * c⁻¹ = b by
              calc c * b * c⁻¹ = (c * b) * c⁻¹ := rfl
                _ = (b * c) * c⁻¹ := by rw [hcB b hb]
                _ = b := by group]
    · intro hz b hb
      have h1 := hz b hb
      have hbc : c * b * c⁻¹ = b := by
        calc c * b * c⁻¹ = (c * b) * c⁻¹ := rfl
          _ = (b * c) * c⁻¹ := by rw [hcB b hb]
          _ = b := by group
      have h2 : c * (b * z) * c⁻¹ = c * (z * b) * c⁻¹ := by
        calc c * (b * z) * c⁻¹ = (c * b * c⁻¹) * (c * z * c⁻¹) := by group
          _ = b * (c * z * c⁻¹) := by rw [hbc]
          _ = (c * z * c⁻¹) * b := h1
          _ = (c * z * c⁻¹) * (c * b * c⁻¹) := by rw [hbc]
          _ = c * (z * b) * c⁻¹ := by group
      have h3 := mul_left_cancel (mul_right_cancel h2)
      exact h3
  have hO'2 : ¬ 3 ∣ Nat.card O' := by
    obtain ⟨k, hk⟩ := (hO2.to_le (inf_le_left : O' ≤ O)).exists_card_eq
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hsyl : CFSG.ABGLocalTools.IsSylowOf 3 C3 (C3 ⊔ O') :=
    Sec20.isSylowOf_sup_of_coprime (Sec20.isPGroup_zpowers_of_pow_three hc3) hO'2 hcO'
  rintro _ ⟨⟨l, hlN⟩, hl, rfl⟩
  have hlL : l ∈ L := (Subgroup.mem_subgroupOf.mp hl).1
  have hlcO' : l * c * l⁻¹ * c⁻¹ ∈ O' := by
    refine ⟨hlc l hlL, ?_⟩
    show l * c * l⁻¹ * c⁻¹ ∈ Subgroup.centralizer (B : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hb' : l⁻¹ * b * l ∈ B := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hlN) b).mp hb
      simpa using this
    have h1 := hcB _ hb'
    have hcb : c * (l⁻¹ * b * l) * c⁻¹ = l⁻¹ * b * l := by
      calc c * (l⁻¹ * b * l) * c⁻¹ = (c * (l⁻¹ * b * l)) * c⁻¹ := rfl
        _ = ((l⁻¹ * b * l) * c) * c⁻¹ := by rw [h1]
        _ = l⁻¹ * b * l := by group
    calc b * (l * c * l⁻¹ * c⁻¹) = l * (l⁻¹ * b * l) * c * l⁻¹ * c⁻¹ := by group
      _ = l * (c * (l⁻¹ * b * l) * c⁻¹) * c * l⁻¹ * c⁻¹ := by rw [hcb]
      _ = l * c * l⁻¹ * b * l * l⁻¹ * c⁻¹ := by group
      _ = l * c * l⁻¹ * (b * c⁻¹) := by group
      _ = l * c * l⁻¹ * (c⁻¹ * b) := by
          rw [show b * c⁻¹ = c⁻¹ * b by
            have := hcB b hb
            calc b * c⁻¹ = c⁻¹ * (c * b) * c⁻¹ := by group
              _ = c⁻¹ * (b * c) * c⁻¹ := by rw [this]
              _ = c⁻¹ * b := by group]
      _ = l * c * l⁻¹ * c⁻¹ * b := by group
  have hlN' : l ∈ Subgroup.normalizer ((C3 ⊔ O' : Subgroup G) : Set G) := by
    apply Sec20.mem_normalizer_of_map_conj_le
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap, Subgroup.zpowers_le, Subgroup.mem_comap]
      change l * c * l⁻¹ ∈ C3 ⊔ O'
      have : l * c * l⁻¹ = (l * c * l⁻¹ * c⁻¹) * c := by group
      rw [this]
      exact (C3 ⊔ O').mul_mem (Subgroup.mem_sup_right hlcO')
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
    · refine le_trans ?_ le_sup_right
      rintro _ ⟨o, ho, rfl⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hLO hlL) o).mp ho.1, ?_⟩
      show l * o * l⁻¹ ∈ Subgroup.centralizer (B : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hb' : l⁻¹ * b * l ∈ B := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hlN) b).mp hb
        simpa using this
      have h1 := (Subgroup.mem_centralizer_iff.mp ho.2) _ hb'
      change b * (l * o * l⁻¹) = l * o * l⁻¹ * b
      calc b * (l * o * l⁻¹) = l * ((l⁻¹ * b * l) * o) * l⁻¹ := by group
        _ = l * (o * (l⁻¹ * b * l)) * l⁻¹ := by rw [h1]
        _ = l * o * l⁻¹ * b := by group
  obtain ⟨w, hw, m, hm, rfl⟩ := Sec18.exists_mul_of_isSylowOf hsyl
    (Subgroup.zpowers_le.mpr hlN') (Subgroup.mem_zpowers l)
  have hw' : w ∈ ((O' ⊔ C3 : Subgroup G) : Set G) := by rw [sup_comm]; exact hw
  rw [Subgroup.coe_mul_of_right_le_normalizer_left O' C3 hcO'] at hw'
  obtain ⟨o, ho, d, hd, rfl⟩ := hw'
  set n := d * m with hn
  have he : n = o⁻¹ * (o * d * m) := by rw [hn]; group
  have hnL : n ∈ L := by
    rw [he]
    exact L.mul_mem (L.inv_mem (hOL ho.1)) hlL
  have hnB : n ∈ Subgroup.normalizer (B : Set G) := by
    rw [he]
    exact mul_mem (Subgroup.centralizer_le_normalizer _ (inv_mem ho.2)) hlN
  have hnc : n ∈ Subgroup.centralizer ({c} : Set G) := by
    have hnN : n ∈ Subgroup.normalizer (C3 : Set G) :=
      mul_mem (Subgroup.le_normalizer hd) hm
    have h1 : n * c * n⁻¹ * c⁻¹ ∈ C3 :=
      C3.mul_mem ((Subgroup.mem_normalizer_iff.mp hnN c).mp (Subgroup.mem_zpowers c))
        (C3.inv_mem (Subgroup.mem_zpowers c))
    have h2 : n * c * n⁻¹ * c⁻¹ ∈ O := hlc n hnL
    have h3 : (C3 ⊓ O : Subgroup G) = ⊥ :=
      Subgroup.eq_bot_of_card_eq _ (Sec20.card_inf_eq_one_of_isPGroup
        (Sec20.isPGroup_zpowers_of_pow_three hc3) hO2)
    have h4 : n * c * n⁻¹ * c⁻¹ = 1 := by
      have : n * c * n⁻¹ * c⁻¹ ∈ (C3 ⊓ O : Subgroup G) := ⟨h1, h2⟩
      rw [h3, Subgroup.mem_bot] at this
      exact this
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h5 : n * c * n⁻¹ = c := mul_inv_eq_one.mp h4
    calc n * c = n * c * n⁻¹ * n := by group
      _ = c * n := by rw [h5]
  refine Sec4.mem_autIn_iff.mpr ⟨n, hnB, ⟨hnL, hnc⟩, ?_⟩
  apply MulEquiv.ext
  intro b
  apply Subtype.ext
  rw [Sec4.normalizerMonoidHom_apply_coe, Sec4.normalizerMonoidHom_apply_coe]
  have hbl : (o * d * m) * (b : G) * (o * d * m)⁻¹ ∈ B :=
    (Subgroup.mem_normalizer_iff.mp hlN b).mp b.2
  have h1 := (Subgroup.mem_centralizer_iff.mp ho.2) _ hbl
  rw [he]
  calc o⁻¹ * (o * d * m) * (b : G) * (o⁻¹ * (o * d * m))⁻¹
      = o⁻¹ * ((o * d * m) * (b : G) * (o * d * m)⁻¹ * o) := by group
    _ = o⁻¹ * (o * ((o * d * m) * (b : G) * (o * d * m)⁻¹)) := by rw [h1]
    _ = (o * d * m) * (b : G) * (o * d * m)⁻¹ := by group

end Res8

end CFSG.RankThree.PartTwo.Sec20
