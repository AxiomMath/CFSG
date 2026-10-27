module

public import CFSG.LocalAnalysis.StandardType.GGB36JExcE6Hard
public import CFSG.LocalAnalysis.StandardType.GGResLeaf
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTwE6
import CFSG.HardMathSupport.Solomon.LocalBalance.TwoLocalTools
import CFSG.HardMathSupport.Timmesfeld.Proving.TwoLocalAttain
import CFSG.Assembly.LargeEvenGLABridge
import CFSG.Assembly.OpenBridges

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l48tR_succ_le {G : Type} [Group G] [Finite G] {L : Subgroup G} {x : G}
    (hxL : L ≤ Subgroup.centralizer ({x} : Set G)) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    {U E : Subgroup L} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hEU : E ≤ Subgroup.normalizer (U : Set L)) (hE : CFSG.Open.IsElemAbelian 3 E)
    {k : ℕ} (hcard : Nat.card E = 3 ^ k) (hZ : E ⊓ Subgroup.center L = ⊥) :
    k + 1 ≤ LargeEvenTwoLocalRank 3 G := by
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
    Subgroup.mem_centralizer_singleton_iff.1 (hxL (hEL e he))
  have hxE : x ∉ E.map L.subtype := by
    intro hx
    obtain ⟨e, he, hex'⟩ := hx
    have hex : (e : G) = x := hex'
    have hec : e ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      change (l : G) * (e : G) = (e : G) * l
      rw [hex]
      exact Subgroup.mem_centralizer_singleton_iff.1 (hxL l.2)
    have he1 : e = 1 := by
      have : e ∈ E ⊓ Subgroup.center L := ⟨he, hec⟩
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
      (hxL (Subgroup.map_subtype_le _ hh))
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (U.map L.subtype : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _ hxU
  exact le_twoLocalRank_of_normalizes hp hU' hU'2 hab (sup_le hE'N hxN) hcard'

private theorem l48tR_exists_twoGroup {Y : Type} [Group Y] [Finite Y]
    (h : 5 ≤ LargeEvenTwoLocalRank 3 Y) : ∃ T : Subgroup Y, T ≠ ⊥ ∧ IsPGroup 2 T := by
  by_contra hcon
  have hempty : {k | ∃ H : Subgroup Y, CFSG.Open.IsTwoLocal H ∧ CFSG.Open.pRank 3 H = k} = ∅ := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨H, hH, -⟩
    obtain ⟨T, hT, hT2, -⟩ := hH
    exact hcon ⟨T, hT, hT2⟩
  have h0 : LargeEvenTwoLocalRank 3 Y = 0 := by
    show CFSG.Open.twoLocalPrimeRank 3 Y = 0
    rw [CFSG.Open.twoLocalPrimeRank, hempty, csSup_empty]
    rfl
  omega

theorem ggTBJ_six_le_twoLocalRank_of_E6
    (hβ : GGE6CoverThreeLocalRank) {G : Type} [Group G] [Finite G] {X : Subgroup G} {z : G}
    (hz : z ∈ Subgroup.centralizer (X : Set G)) (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1)
    (hperf : commutator ↥X = ⊤) {n : ℕ} (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n - 1)
    (hlab : GGHasLabel (⟨.E6, 0, n⟩ : LargeEvenLabel) (↥X ⧸ Subgroup.center ↥X)) :
    6 ≤ LargeEvenTwoLocalRank 3 G := by
  by_cases hZ : 3 ∣ Nat.card (Subgroup.center ↥X)
  · exact (hβ ↥X ⟨.E6, 0, n⟩ ⟨hn, rfl⟩ rfl h3 hlab hperf hZ).trans
      (CFSG.HardMathSupport.Solomon.LocalBalance.glaTwoLocalRank_subgroup_le
        Nat.prime_three X)
  · have h5 : 5 ≤ LargeEvenTwoLocalRank 3 ↥X :=
      ggE6TorusLiftFiveRank (X := ↥X) hperf rfl h3 hlab
    obtain ⟨T, hT, hT2, E, hEU, hE, hcard⟩ :=
      CFSG.HardMathSupport.Timmesfeld.Proving.exists_twoLocal_attaining_GLATwoLocalRank
        (G := ↥X) Nat.prime_three (l48tR_exists_twoGroup h5)
    have hZbot : E ⊓ Subgroup.center ↥X = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro e he
      by_contra he1
      have he3 : e ^ 3 = 1 := hE.2 e he.1
      have horder : orderOf e = 3 := orderOf_eq_prime he3 he1
      have hdvd : orderOf e ∣ Nat.card (Subgroup.center ↥X) :=
        Subgroup.orderOf_dvd_natCard (Subgroup.center ↥X) he.2
      rw [horder] at hdvd
      exact hZ hdvd
    have hxL : X ≤ Subgroup.centralizer ({z} : Set G) := by
      intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hz g hg
    have h6 : LargeEvenTwoLocalRank 3 ↥X + 1 ≤ LargeEvenTwoLocalRank 3 G :=
      l48tR_succ_le (k := LargeEvenTwoLocalRank 3 ↥X) hxL hz1 hz3 hT hT2 hEU hE hcard hZbot
    omega

end CFSG.StandardType

end
