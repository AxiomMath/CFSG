module

public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedSLAux
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups
import CFSG.RankThree.Classical.SteinbergBJOrthogonalAveraging
import CFSG.RankThree.PartOne.S11c.J4Extraspecial
import CFSG.Timmesfeld.Bridge.RootStructR2Incidence

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6R77

open CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_zpowers_of_line {p r : ℕ} [hp : Fact p.Prime] [hr : Fact r.Prime]
    (hpr : p ≠ r) {E Z : Subgroup G} (hE : IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2)
    (hZE : Z ≤ E) (hZcard : Nat.card Z = r) {s : G} (hsE : s ∈ normalizer (E : Set G))
    (hsZ : s ∈ normalizer (Z : Set G)) (hs : orderOf s = p) :
    ∃ y ∈ E, y ∉ Z ∧ s ∈ normalizer (zpowers y : Set G) := by
  classical
  haveI : Fintype E := Fintype.ofFinite E
  set S : Set (Subgroup G) := {L | L ≤ E ∧ Nat.card L = r} \ {Z} with hSdef
  have himg : {L : Subgroup G | L ≤ E ∧ Nat.card L = r} = map E.subtype ''
      ↑(Finset.univ.filter fun M : Subgroup E => Nat.card M = r) := by
    ext L
    simp only [Set.mem_setOf_eq, Set.mem_image, Finset.coe_filter, Finset.mem_univ, true_and]
    refine ⟨fun ⟨hLE, hL⟩ => ⟨L.subgroupOf E, ?_, map_subgroupOf_eq_of_le hLE⟩, ?_⟩
    · rw [← hL]
      exact Nat.card_congr (subgroupOfEquivOfLe hLE).toEquiv
    · rintro ⟨M, hM, rfl⟩
      exact ⟨map_subtype_le M, by rw [card_map_of_injective E.subtype_injective, hM]⟩
  have hS : S.ncard = r := by
    rw [hSdef, Set.ncard_sdiff_singleton_of_mem
        (show Z ∈ {L : Subgroup G | L ≤ E ∧ Nat.card L = r} from ⟨hZE, hZcard⟩), himg,
      Set.ncard_image_of_injective _ (map_injective E.subtype_injective), Set.ncard_coe_finset,
      CFSG.RankThree.Classical.card_subgroups_natCard_eq_prime hr.out
        (fun g => Subtype.ext (by simpa using hE.2 g g.2)) hEcard, Nat.add_sub_cancel]
  have hSinv : ∀ g ∈ zpowers s, ∀ L ∈ S, L.map (MulAut.conj g).toMonoidHom ∈ S := by
    rintro g hg L ⟨⟨hLE, hL⟩, hLZ⟩
    have hgE := mem_normalizer_iff_map_conj_eq.mp (zpowers_le.mpr hsE hg)
    have hgZ := mem_normalizer_iff_map_conj_eq.mp (zpowers_le.mpr hsZ hg)
    refine ⟨⟨(map_mono hLE).trans hgE.le,
      by rw [card_map_of_injective (MulAut.conj g).injective, hL]⟩, fun h => hLZ ?_⟩
    exact map_injective (MulAut.conj g).injective ((Set.mem_singleton_iff.mp h).trans hgZ.symm)
  obtain ⟨L, ⟨⟨hLE, hL⟩, hLZ⟩, hLs⟩ := CFSG.Timmesfeld.Bridge.exists_map_conj_eq_of_isPGroup
    (p := p) (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])) hSinv
    (by rw [hS]; exact fun h => hpr ((Nat.prime_dvd_prime_iff_eq hp.out hr.out).mp h))
  obtain ⟨y, hyL, hy1⟩ := (bot_or_exists_ne_one L).resolve_left fun h => by
    rw [h, card_bot] at hL
    exact hr.out.one_lt.ne hL
  have hyL' : zpowers y = L := eq_of_le_of_card_ge (zpowers_le.mpr hyL) (by
    rw [Nat.card_zpowers, orderOf_eq_prime (hE.2 y (hLE hyL)) hy1, hL])
  refine ⟨y, hLE hyL, fun hyZ => hLZ (Set.mem_singleton_iff.mpr ?_), ?_⟩
  · refine eq_of_le_of_card_ge ?_ (by rw [hL, hZcard])
    rw [← hyL']
    exact zpowers_le.mpr hyZ
  · rw [hyL', mem_normalizer_iff_map_conj_eq]
    exact hLs s (mem_zpowers s)

theorem card_inf_centralizer_eq_of_pRank_le_two {r : ℕ} [hr : Fact r.Prime] {X : Subgroup G}
    (hX : IsPGroup r X) (hexp : ∀ x ∈ X, x ^ r = 1) (hcl : ⁅⁅X, X⁆, X⁆ = ⊥)
    (hrank : pRank r X ≤ 2) {a b : G} (ha : a ∈ X) (hb : b ∈ X) (hab : a * b ≠ b * a) :
    Nat.card (X ⊓ centralizer (X : Set G) : Subgroup G) = r ∧
      (⁅X, X⁆ : Subgroup G) ≤ X ⊓ centralizer (X : Set G) ∧
      Nat.card X = Nat.card (⁅X, X⁆ : Subgroup G) * r ^ 2 := by
  have hnc : ∃ x y : X, x * y ≠ y * x :=
    ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  have hX3 : Nat.card X = r ^ 3 := CFSG.AGLEmbedding.card_eq_pow_three_of_not_comm hX
    (fun x => Subtype.ext (by simpa using hexp x x.2))
    ((CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := r) X).symm.trans_le hrank) hnc
  have hZ : Nat.card (X ⊓ centralizer (X : Set G) : Subgroup G) ≤ r := by
    rw [← CFSG.AGLEmbedding.LeviBlock.card_center_eq_card_inf_centralizer]
    exact CFSG.RankThree.PartOne.card_center_le_of_noncomm hX3 hnc
  have hX'Z : (⁅X, X⁆ : Subgroup G) ≤ X ⊓ centralizer (X : Set G) :=
    le_inf (commutator_le.mpr fun x hx y hy =>
        X.mul_mem (X.mul_mem (X.mul_mem hx hy) (X.inv_mem hx)) (X.inv_mem hy))
      (commutator_eq_bot_iff_le_centralizer.mp hcl)
  obtain ⟨j, hj⟩ := (hX.to_le (hX'Z.trans inf_le_left)).exists_card_eq
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hj
    have h1 : ⁅a, b⁆ ∈ (⁅X, X⁆ : Subgroup G) := commutator_mem_commutator ha hb
    rw [eq_bot_of_card_eq _ hj, mem_bot] at h1
    exact hab ((commutatorElement_eq_one_iff_mul_comm (g₁ := a) (g₂ := b)).mp h1)
  have hrj : r ≤ Nat.card (⁅X, X⁆ : Subgroup G) := by
    rw [hj]
    exact Nat.le_self_pow hj0 r
  have hle := card_le_of_le hX'Z
  have hX' : Nat.card (⁅X, X⁆ : Subgroup G) = r := by omega
  exact ⟨by omega, hX'Z, by rw [hX3, hX']; ring⟩

theorem exists_conj_eq_mul_of_not_mem {r : ℕ} [hr : Fact r.Prime] {X : Subgroup G}
    (hZcard : Nat.card (X ⊓ centralizer (X : Set G) : Subgroup G) = r)
    (hX'Z : (⁅X, X⁆ : Subgroup G) ≤ X ⊓ centralizer (X : Set G)) {y z : G} (hyX : y ∈ X)
    (hyZ : y ∉ X ⊓ centralizer (X : Set G)) (hz : z ∈ X ⊓ centralizer (X : Set G)) :
    ∃ g ∈ X, g * y * g⁻¹ = z * y := by
  obtain ⟨g₀, hg₀, hg₀y⟩ : ∃ g₀ ∈ X, g₀ * y ≠ y * g₀ := by
    by_contra h
    push Not at h
    exact hyZ (mem_inf.2 ⟨hyX, mem_centralizer_iff.2 h⟩)
  set c : G := g₀ * y * g₀⁻¹ * y⁻¹ with hc
  have hcZ : c ∈ X ⊓ centralizer (X : Set G) := hX'Z (commutator_mem_commutator hg₀ hyX)
  have hc1 : c ≠ 1 := fun h =>
    hg₀y ((commutatorElement_eq_one_iff_mul_comm (g₁ := g₀) (g₂ := y)).mp h)
  have hcgen : zpowers c = X ⊓ centralizer (X : Set G) := by
    refine eq_of_le_of_card_ge (zpowers_le.mpr hcZ) ?_
    have hdvd := orderOf_dvd_natCard (⟨c, hcZ⟩ : (X ⊓ centralizer (X : Set G) : Subgroup G))
    rw [Subgroup.orderOf_mk, hZcard] at hdvd
    rw [Nat.card_zpowers, hZcard]
    rcases (Nat.dvd_prime hr.out).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hc1
    · exact h.ge
  have hg₀c : g₀ * c = c * g₀ := mem_centralizer_iff.1 (mem_inf.1 hcZ).2 g₀ hg₀
  have hcy : g₀ * y * g₀⁻¹ = c * y := by
    rw [hc]
    group
  have key : ∀ n : ℕ, g₀ ^ n * y * (g₀ ^ n)⁻¹ = c ^ n * y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hcn : g₀ * c ^ n = c ^ n * g₀ := (Commute.pow_right hg₀c n).eq
      calc g₀ ^ (n + 1) * y * (g₀ ^ (n + 1))⁻¹ = g₀ * (g₀ ^ n * y * (g₀ ^ n)⁻¹) * g₀⁻¹ := by
            group
        _ = g₀ * c ^ n * y * g₀⁻¹ := by rw [ih]; group
        _ = c ^ n * (g₀ * y * g₀⁻¹) := by rw [hcn]; group
        _ = c ^ (n + 1) * y := by rw [hcy, pow_succ]; group
  have hzc : z ∈ zpowers c := by
    rw [hcgen]
    exact hz
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff z c).mp (mem_powers_iff_mem_zpowers.mpr hzc)
  exact ⟨g₀ ^ m, X.pow_mem hg₀ m, by rw [key m, hm]⟩

end CFSG.LocalAnalysis.UniquenessCase.UC6R77
