module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCBase
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Adapters.LieModelUnitaryOuter

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord CFSG.Assembly
open CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G]

private theorem qTwoLMPrimeC_base_card_outer_centerQuot {L : Subgroup G} {m : ℕ}
    (h3 : ¬ 3 ∣ m) (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1) :
    Nat.card (Outer (L ⧸ Subgroup.center L)) = 2 := by
  have h4 : 4 ≤ m := qTwoLMFrameC_four_le hL
  have h := LieModel.card_outer_psu hL (by omega) (by rintro ⟨hm, -⟩; omega)
  rw [h]
  have hcop : Nat.Coprime 3 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
  have hg : Nat.gcd m 3 = 1 := by
    rw [Nat.gcd_comm]
    exact hcop.gcd_eq_one
  rw [show (2 : ℕ) ^ 1 + 1 = 3 by norm_num, hg]

theorem qTwoLMPrimeC_card_ge {B Bs L : Subgroup G} {x : G} (hG : GGThmIHyp 3 B x L)
    (hBs : GGBstar 3 B Bs) : 3 ^ 4 ≤ Nat.card ↥Bs := by
  have hS : LargeEvenSStar 3 B x L := hG.2.2.2.2.2.2.1
  have hBc : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := hS.1.2.1
  have h4 : 4 ≤ LargeEvenTwoLocalRank 3 G := hG.2.2.2.2.2.1.2.2.2
  calc 3 ^ 4 ≤ 3 ^ LargeEvenTwoLocalRank 3 G := Nat.pow_le_pow_right (by norm_num) h4
    _ = Nat.card B := hBc.symm
    _ ≤ Nat.card ↥Bs := Subgroup.card_le_of_le hBs.1

theorem qTwoLMPrimeC_ker {B Bs L : Subgroup G} {x : G} (hG : GGThmIHyp 3 B x L)
    (hBs : GGBstar 3 B Bs) : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x := by
  have hS : LargeEvenSStar 3 B x L := hG.2.2.2.2.2.2.1
  obtain ⟨⟨-, -, -⟩, hxB, hx1, hLC, hcyc⟩ := hS
  have hxBs : x ∈ Bs := hBs.1 hxB
  have hxC : x ∈ Subgroup.centralizer (L : Set G) := mem_centralizer_of_le_centralizer hLC.1
  have hE : IsElemAbelian 3 (Bs ⊓ Subgroup.centralizer (L : Set G)) :=
    TableB.isElemAbelian_mono hBs.2.1 inf_le_left
  have hcE : IsCyclic ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) :=
    hcyc _ inf_le_right (TableB.isPGroup_of_isElemAbelian hE)
  have hle : Subgroup.zpowers x ≤ Bs ⊓ Subgroup.centralizer (L : Set G) :=
    (Subgroup.zpowers_le).mpr ⟨hxBs, hxC⟩
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Nat.card_zpowers, orderOf_eq_prime (hBs.2.1.2 x hxBs) hx1]
  exact TableB.card_le_of_isCyclic (by norm_num) hcE hE.2

theorem qTwoLMPrimeC_inner {B Bs L : Subgroup G} {x : G} {m : ℕ} (hG : GGThmIHyp 3 B x L)
    (hBs : GGBstar 3 B Bs) (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (h3 : ¬ 3 ∣ m)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1) :
    ∀ b ∈ Bs, ∃ e ∈ L, ∀ l ∈ L, b * l * b⁻¹ = e * l * e⁻¹ := by
  intro b hb
  let β : ↥Bs := ⟨b, hb⟩
  let a : MulAut ↥L := ggGamma L hN β
  have hβ3 : β ^ 3 = 1 := by
    apply Subtype.ext
    exact hBs.2.1.2 b hb
  have ha3 : a ^ 3 = 1 := by
    change (ggGamma L hN β) ^ 3 = 1
    rw [← map_pow, hβ3, map_one]
  have hcard_dvd : Nat.card (Outer ↥L) ∣ 2 := by
    haveI : Group.IsPerfect ↥L := ⟨qTwoLMFrameC_perfect hG⟩
    have h1 := Subgroup.card_dvd_of_injective (centerQuotientOuterHom ↥L)
      (centerQuotient_outer_injective ↥L)
    rwa [qTwoLMPrimeC_base_card_outer_centerQuot h3 hL] at h1
  set c : Outer ↥L :=
    QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L) a with hc
  have hc3 : c ^ 3 = 1 := by
    rw [hc]
    rw [← map_pow, ha3, map_one]
  have hc2 : c ^ 2 = 1 := by
    obtain ⟨k, hk⟩ := hcard_dvd
    rw [hk, pow_mul, pow_card_eq_one' (x := c), one_pow]
  have hc1 : c = 1 := by
    have h : c ^ 3 * (c ^ 2)⁻¹ = 1 := by rw [hc3, hc2, inv_one, mul_one]
    rw [← h]
    group
  obtain ⟨e, he⟩ : ∃ e : ↥L, MulAut.conj e = a := by
    have hmem : a ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L := by
      rw [← QuotientGroup.eq_one_iff a]
      simpa using hc.symm.trans hc1
    exact MonoidHom.mem_range.mp (show a ∈ (MulAut.conj : ↥L →* MulAut ↥L).range from hmem)
  refine ⟨(e : G), e.2, ?_⟩
  intro l hl
  have h1 : a ⟨l, hl⟩ = e * ⟨l, hl⟩ * e⁻¹ := by
    rw [← he, MulAut.conj_apply]
  calc b * l * b⁻¹ = ((a ⟨l, hl⟩ : ↥L) : G) := (ggGamma_coe L hN β ⟨l, hl⟩).symm
    _ = ((e * ⟨l, hl⟩ * e⁻¹ : ↥L) : G) := by rw [h1]
    _ = (e : G) * l * (e : G)⁻¹ := rfl

end CFSG.StandardType.QTwo

end
