module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLAType
public import CFSG.Quasithin.H13.VolIA38Orders

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.Orders
open CFSG.Quasithin.H13.VolI

namespace GoldMLB

theorem isPSp4_of_mulEquiv {X Y : Type} [Group X] [Group Y] {p e : ℕ} (h : IsPSp4 p e X)
    (φ : X ≃* Y) : IsPSp4 p e Y := by
  obtain ⟨hadm, K, hK1, hK2, hK, ⟨ψ⟩⟩ := h
  exact ⟨hadm, K, hK1, hK2, hK, ⟨φ.symm.trans ψ⟩⟩

section Types

variable {G : Type} [Group G] [Finite G]

theorem quotModel_of_typeB {L : Subgroup G} (hperf : commutator ↥L = ⊤)
    (hB : (∃ n : ℕ, 1 < n ∧ IsPSL 3 2 n ↥L) ∨ (∃ n : ℕ, 1 < n ∧ IsPSp4 2 n ↥L) ∨
      IsPSL 3 2 2 (↥L ⧸ CFSG.pCore 2 ↥L)) :
    (∃ n : ℕ, 2 ≤ n ∧ IsPSL 3 2 n (↥L ⧸ CFSG.pCore 2 ↥L)) ∨
      (∃ n : ℕ, 2 ≤ n ∧ IsPSp4 2 n (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  rcases hB with ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | h
  · have hs : IsSimpleGroup ↥L := (CFSG.LieType.Simplicity.fam_PSL_simplicity ↥L 3 2 n h).2
    have h0 := GoldMLA.pCore_two_eq_bot_of_simple hperf hs
    left
    exact ⟨n, hn, isPSL_of_mulEquiv h
      ((QuotientGroup.quotientMulEquivOfEq h0).trans QuotientGroup.quotientBot).symm⟩
  · have hs : IsSimpleGroup ↥L :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp ↥L 2 2 n h
    have h0 := GoldMLA.pCore_two_eq_bot_of_simple hperf hs
    right
    exact ⟨n, hn, isPSp4_of_mulEquiv h
      ((QuotientGroup.quotientMulEquivOfEq h0).trans QuotientGroup.quotientBot).symm⟩
  · exact Or.inl ⟨2, le_rfl, h⟩

theorem rankTwoOrder_of_quotModel {Y : Type} [Group Y]
    (h : (∃ n : ℕ, 2 ≤ n ∧ IsPSL 3 2 n Y) ∨ (∃ n : ℕ, 2 ≤ n ∧ IsPSp4 2 n Y)) :
    RankTwoOrder (Nat.card Y) := by
  rcases h with ⟨n, hn, h⟩ | ⟨n, hn, h⟩
  · exact Or.inl ⟨n, hn, (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, by omega,
      (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.2.1 rfl⟩)))

end Types

theorem card_eq_of_simple_image {W V : Type} [Group W] [Finite W] [Group V] (hV : IsSimpleGroup V)
    (ρ : W →* V) (hρ : Function.Surjective ρ) (hk : IsPGroup 2 ρ.ker)
    (hne : Nat.card (W ⧸ CFSG.pCore 2 W) ≠ 1) :
    Nat.card V = Nat.card (W ⧸ CFSG.pCore 2 W) := by
  have hkle : ρ.ker ≤ CFSG.pCore 2 W := le_sSup ⟨ρ.normal_ker, hk⟩
  have hnorm : ((CFSG.pCore 2 W).map ρ).Normal :=
    (CFSG.pCore_normal (G := W) (p := 2)).map ρ hρ
  rcases hV.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 W).map ρ) with h | h
  · have hle : CFSG.pCore 2 W ≤ ρ.ker := by
      intro x hx
      rw [MonoidHom.mem_ker]
      have : ρ x ∈ (CFSG.pCore 2 W).map ρ := ⟨x, hx, rfl⟩
      rw [h] at this
      exact Subgroup.mem_bot.mp this
    have hEq : ρ.ker = CFSG.pCore 2 W := le_antisymm hkle hle
    calc Nat.card V = Nat.card (W ⧸ ρ.ker) :=
          (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).toEquiv).symm
      _ = Nat.card (W ⧸ CFSG.pCore 2 W) := by rw [hEq]
  · exfalso
    have htop : CFSG.pCore 2 W = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : ρ x ∈ (CFSG.pCore 2 W).map ρ := by rw [h]; trivial
      obtain ⟨y, hy, hxy⟩ := hx
      have hker : y⁻¹ * x ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
      have hx' : x = y * (y⁻¹ * x) := by group
      rw [hx']
      exact mul_mem hy (hkle hker)
    apply hne
    rw [htop]
    have := Subgroup.index_top (G := W)
    rwa [Subgroup.index] at this

variable {G : Type} [Group G] [Finite G]

theorem not_a38Types_image
    {X L : Subgroup G} (hLX : L ≤ X)
    (hY : (∃ n : ℕ, 2 ≤ n ∧ IsPSL 3 2 n (↥L ⧸ CFSG.pCore 2 ↥L)) ∨
      (∃ n : ℕ, 2 ≤ n ∧ IsPSp4 2 n (↥L ⧸ CFSG.pCore 2 ↥L))) :
    ¬ A38Types ↥((L.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))) := by
  intro hA
  have hS := isSimpleGroup_of_a38Types hA
  have hord := a38Order_card hA
  have hrk := rankTwoOrder_of_quotModel hY
  set π : ↥X →* ↥X ⧸ CFSG.pCore 2 ↥X := QuotientGroup.mk' (CFSG.pCore 2 ↥X) with hπ
  set ρ₀ : ↥L →* ↥X ⧸ CFSG.pCore 2 ↥X := π.comp (Subgroup.inclusion hLX) with hρ₀
  have hrange : ρ₀.range = (L.subgroupOf X).map π := by
    rw [hρ₀, MonoidHom.range_comp, Subgroup.inclusion_range]
  rw [← hrange] at hA hS hord
  have hker2 : IsPGroup 2 ρ₀.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict, hρ₀, ← MonoidHom.comap_ker, hπ, QuotientGroup.ker_mk']
    exact (CFSG.pCore_isPGroup (G := ↥X) (p := 2)).comap_of_injective _
      (Subgroup.inclusion_injective hLX)
  have hne : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) ≠ 1 := by
    intro h1
    exact rankTwoOrder_ne_one hrk h1
  have hcard := card_eq_of_simple_image hS ρ₀.rangeRestrict ρ₀.rangeRestrict_surjective hker2 hne
  rw [hcard] at hord
  exact a38Order_not_rankTwoOrder hord hrk

end GoldMLB

end CFSG.Quasithin
