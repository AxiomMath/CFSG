module

public import CFSG.RankThree.OddKernel.SemisimpleSectionTransport
public import CFSG.RankThree.OddKernel.RankOneQuotients

public section

namespace CFSG.RankThree.OddKernel

open Subgroup CFSG.SectionRank
open CFSG.Assembly.RankThreeEven (localRank)

universe u

section EvenCover

variable {p : ℕ}

theorem pRank_le_of_surjective_of_le_one (hp : p.Prime) (hp2 : p ≠ 2) {M L : Type*} [Group M]
    [Group L] [Finite M] [Finite L] (ψ : M →* L) (hψ : Function.Surjective ψ)
    (hM : pRank p M ≤ 1) : pRank p L ≤ pRank p M := by
  have : Fact p.Prime := ⟨hp⟩
  rcases (show pRank p M = 0 ∨ pRank p M = 1 by omega) with h0 | h1
  · rw [h0]
    by_contra hpos
    push Not at hpos
    rw [pRank_eq_open_pRank_top] at hpos
    obtain ⟨B, -, -, hB⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup L)
    have hdvd : p ∣ Nat.card L :=
      (dvd_pow_self p (by omega)).trans (hB ▸ card_subgroup_dvd_card B)
    have hdvdM : p ∣ Nat.card M := hdvd.trans (Subgroup.card_dvd_of_surjective hψ)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvdM
    have h1 : 1 ≤ pRank p M := by
      rw [pRank_eq_open_pRank_top]
      refine CFSG.SectionRank.le_pRank hp.one_lt le_top ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
        (by rw [Nat.card_zpowers, hx, pow_one]) (E := zpowers x)
      · obtain ⟨a, i, rfl⟩ := a
        obtain ⟨b, j, rfl⟩ := b
        exact Subtype.ext (Commute.zpow_zpow_self x i j).eq
      · obtain ⟨i, rfl⟩ := hy
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx,
          pow_orderOf_eq_one, one_zpow]
    omega
  · rw [h1]
    exact pRank_le_one_of_surjective hp hp2 ψ hψ (h1 ▸ le_rfl)

theorem pRank_le_of_surjective_semisimple (hp : p.Prime) (hp3 : 3 < p) {M S : Type*} [Group M]
    [Group S] [Finite M] (hS : CFSG.layer S = ⊤) (ψ : M →* S) (hψ : Function.Surjective ψ)
    (hM : pRank p M ≤ 2) : pRank p S ≤ pRank p M := by
  have : Finite S := Finite.of_surjective ψ hψ
  rcases (show pRank p M ≤ 1 ∨ pRank p M = 2 by omega) with h | h
  · exact pRank_le_of_surjective_of_le_one hp (by omega) ψ hψ h
  · rw [h]
    exact pRank_le_two_of_surjective_semisimple hp hp3 hM hS ψ hψ

theorem minimal_cover_facts {H S : Type*} [Group H] [Group S] [Finite H]
    (hS : CFSG.layer S = ⊤) (ρ : H →* S) (X : Subgroup H) (hXS : X.map ρ = ⊤)
    (hXmin : ∀ U : Subgroup H, U < X → U.map ρ ≠ ⊤) :
    Group.IsPerfect X ∧ Group.IsNilpotent ((center S).comap (ρ.comp X.subtype)) ∧
      (∀ (q : ℕ) [Fact q.Prime] (Q : Sylow q ((center S).comap (ρ.comp X.subtype))),
        ((Q : Subgroup ((center S).comap (ρ.comp X.subtype))).map
          ((center S).comap (ρ.comp X.subtype)).subtype).Normal) := by
  have hπ : Function.Surjective (ρ.comp X.subtype) := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, range_subtype, hXS]
  have hmin : ∀ Y : Subgroup X, Y ≠ ⊤ → Y.map (ρ.comp X.subtype) ≠ ⊤ := by
    intro Y hY hYS
    have hle : Y.map X.subtype ≤ X := map_subtype_le Y
    have hlt : Y.map X.subtype < X := by
      refine lt_of_le_of_ne hle fun heq => hY (eq_top_iff.2 fun x _ => ?_)
      have hx : (x : H) ∈ Y.map X.subtype := by rw [heq]; exact x.2
      obtain ⟨y, hy, hyx⟩ := mem_map.1 hx
      rwa [← Subtype.ext hyx]
    exact hXmin _ hlt (by rw [map_map]; exact hYS)
  obtain ⟨hXp, -, hCnil, hsyl, -⟩ := CFSG.SectionRank.minimal_semisimple_cover hS _ hπ hmin
  exact ⟨hXp, hCnil, hsyl⟩

theorem even_cover_rank_le (hp : p.Prime) (hp3 : 3 < p) {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (N : Subgroup H) [N.Normal] (hS : CFSG.layer (H ⧸ N) = ⊤)
    (X : Subgroup H) (hXS : X.map (QuotientGroup.mk' N) = ⊤)
    (hXmin : ∀ U : Subgroup H, U < X → U.map (QuotientGroup.mk' N) ≠ ⊤)
    (hloc : localRank p G ≤ 2)
    (heven : Even (Nat.card ((center (H ⧸ N)).comap ((QuotientGroup.mk' N).comp X.subtype)))) :
    pRank p (H ⧸ N) ≤ localRank p G ∧ localRank p (H ⧸ N) ≤ localRank p G := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hXp, -, hsyl⟩ := minimal_cover_facts hS (QuotientGroup.mk' N) X hXS hXmin
  obtain ⟨Q⟩ : Nonempty (Sylow 2 ((center (H ⧸ N)).comap ((QuotientGroup.mk' N).comp
    X.subtype))) := inferInstance
  have hQn := hsyl 2 Q
  obtain ⟨K, hKdef⟩ : ∃ K : Subgroup X, K = (Q : Subgroup ((center (H ⧸ N)).comap
      ((QuotientGroup.mk' N).comp X.subtype))).map (Subgroup.subtype _) := ⟨_, rfl⟩
  rw [← hKdef] at hQn
  obtain ⟨Q', hQ'def⟩ : ∃ Q' : Subgroup G, Q' = (K.map X.subtype).map H.subtype := ⟨_, rfl⟩
  have hQ'2 : IsPGroup 2 Q' := hQ'def ▸ hKdef ▸ ((Q.isPGroup'.map _).map _).map _
  have hQ'0 : Q' ≠ ⊥ := by
    intro h
    have hQ1 : (Q : Subgroup ((center (H ⧸ N)).comap ((QuotientGroup.mk' N).comp X.subtype)))
        = ⊥ := by
      rw [hQ'def, hKdef, Subgroup.map_map, Subgroup.map_map,
        Subgroup.map_eq_bot_iff_of_injective _ ((H.subtype_injective.comp
          X.subtype_injective).comp (subtype_injective _))] at h
      exact h
    have hcard := Q.card_eq_multiplicity
    rw [hQ1, card_bot] at hcard
    have hpos := Nat.prime_two.factorization_pos_of_dvd Nat.card_pos.ne'
      (even_iff_two_dvd.1 heven)
    have : 2 ^ (Nat.card ((center (H ⧸ N)).comap ((QuotientGroup.mk' N).comp
        X.subtype))).factorization 2 ≠ 1 := (Nat.one_lt_pow hpos.ne' (by norm_num)).ne'
    exact this hcard.symm
  have hXQ' : X.map H.subtype ≤ normalizer (Q' : Set G) := by
    have h1 : X ≤ normalizer ((K.map X.subtype : Subgroup H) : Set H) := by
      have h := le_normalizer_map (H := K) X.subtype
      rw [normalizer_eq_top_iff.2 hQn, ← MonoidHom.range_eq_map, range_subtype] at h
      exact h
    rw [hQ'def]
    exact (map_mono h1).trans (le_normalizer_map H.subtype)
  have hXrank : pRank p X ≤ localRank p G := by
    have h1 : pRank p X = CFSG.Open.pRank p (X.map H.subtype) := by
      rw [pRank_eq_open_pRank_top, pRank_eq_pRank_top_subgroup (X.map H.subtype)]
      exact pRank_top_eq_of_mulEquiv hp.one_lt (X.equivMapOfInjective _ H.subtype_injective)
    rw [h1]
    exact (CFSG.SectionRank.pRank_mono hp.one_lt hXQ').trans
      (CFSG.RankThree.Classical.pRank_le_localRank hp.one_lt ⟨Q', hQ'0, hQ'2, rfl⟩)
  have hπ : Function.Surjective ((QuotientGroup.mk' N).comp X.subtype) := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, range_subtype, hXS]
  have hSrank := pRank_le_of_surjective_semisimple hp hp3 hS _ hπ (hXrank.trans hloc)
  refine ⟨hSrank.trans hXrank, ?_⟩
  refine le_trans ?_ (hSrank.trans hXrank)
  have h := CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_le_pRank p hp (H ⧸ N)
  refine h.trans ?_
  change CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ N)) ≤ _
  rw [← pRank_eq_open_pRank_top]

end EvenCover

end CFSG.RankThree.OddKernel
