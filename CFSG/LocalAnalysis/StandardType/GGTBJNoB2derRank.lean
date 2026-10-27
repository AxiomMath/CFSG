module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derDefs
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpRank
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTwE6
import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeSp

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggB2der_four_le_rank {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {r : ℕ} [NeZero r] {E U : Subgroup (LargeEvenProj (LargeEvenSpGroup K r))}
    (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 27) (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hEU : ∀ a ∈ E, ∀ u ∈ U, a * u * a⁻¹ ∈ U) : 4 ≤ r := by
  have h := SmallRule.card_le_sp_normalizes_two hK hE hU1 hU2 hEU
  rw [hEc] at h
  by_contra hlt
  have h2 : r - 1 ≤ 2 := by omega
  have h3 : 3 ^ (r - 1) ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) h2
  omega

theorem ggB2der_rank_le_four {G : Type} [Group G] [Finite G] {L : Subgroup G} {x : G}
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) {r : ℕ} [NeZero r]
    (hr : 3 ≤ r) {ψ : ↥L →* LargeEvenProj (LargeEvenSpGroup K r)}
    (hψ : Function.Surjective ψ) (hker : ψ.ker = Subgroup.center ↥L)
    (hperf : commutator ↥L = ⊤) (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) (hx1 : x ≠ 1)
    (hx3 : x ^ 3 = 1) (hrank : LargeEvenTwoLocalRank 3 G ≤ 4) : r ≤ 4 := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  obtain ⟨U, E, hU, hU2, hEU, hE, hcard, hEker⟩ :=
    TwoThree.ggTorusLift_sp_two (K := K) (k := k) hK ↥L ψ hψ (le_of_eq hker) hperf
  have hZ : E ⊓ Subgroup.center ↥L = ⊥ := by
    rw [← hker]; exact hEker
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hU' : U.map L.subtype ≠ ⊥ := fun h =>
    hU ((Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).1 h)
  have hU'2 : IsPGroup 2 (U.map L.subtype) := hU2.map L.subtype
  have hE' : CFSG.Open.IsElemAbelian 3 (E.map L.subtype) :=
    CFSG.Open.IsElemAbelian.map hE L.subtype
  have hE'N : E.map L.subtype ≤ Subgroup.normalizer (U.map L.subtype : Set G) :=
    (Subgroup.map_mono hEU).trans (Subgroup.le_normalizer_map L.subtype)
  have hE'card : Nat.card (E.map L.subtype) = Nat.card E :=
    Subgroup.card_map_of_injective L.subtype_injective
  have hEL : ∀ e ∈ E.map L.subtype, e ∈ L := by
    rintro _ ⟨e, -, rfl⟩
    exact e.2
  have hcomm : ∀ e ∈ E.map L.subtype, e * x = x * e := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.1 (hLx (hEL e he))
  have hxE : x ∉ E.map L.subtype := by
    intro hx
    obtain ⟨e, he, hex'⟩ := hx
    have hex : (e : G) = x := hex'
    have hec : e ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      change (l : G) * (e : G) = (e : G) * l
      rw [hex]
      exact Subgroup.mem_centralizer_singleton_iff.1 (hLx l.2)
    have he1 : e = 1 := by
      have : e ∈ E ⊓ Subgroup.center ↥L := ⟨he, hec⟩
      rw [hZ] at this
      exact Subgroup.mem_bot.1 this
    apply hx1
    rw [← hex, he1]
    rfl
  obtain ⟨hab, hcard'⟩ := isElemAbelian_sup_zpowers_of_card hp hE' (k := k)
    (by rw [hE'card, hcard]) hx3 hxE hcomm
  have hxU : x ∈ Subgroup.centralizer (U.map L.subtype : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.1
      (hLx (Subgroup.map_subtype_le _ hh))
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (U.map L.subtype : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _ hxU
  exact (le_twoLocalRank_of_normalizes hp hU' hU'2 hab (sup_le hE'N hxN) hcard').trans hrank

end CFSG.StandardType
