module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.ElementaryAbelian.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# General facts about finite p-groups

This module collects Mathlib-only consequences about maximal (coatom) subgroups
of finite p-groups.

Public items:
- `coatom_normal_of_isPGroup`
- `quotient_subgroup_eq_bot_or_top_of_coatom`
- `card_quotient_coatom_eq_prime`

It also re-exports `Theory.ElementaryAbelian.Basic`.
-/

namespace CFSG.Theory.PGroup

/-- Maximal subgroups of finite p-groups are normal. -/
public lemma coatom_normal_of_isPGroup {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p R)] {K : Subgroup R} (hK : IsCoatom K) : K.Normal := by
  letI : Group.IsNilpotent R := IsPGroup.isNilpotent (p := p) (G := R) (h := Fact.out)
  exact Subgroup.NormalizerCondition.normal_of_coatom K
    (Group.normalizerCondition_of_isNilpotent (G := R)) hK

/-- The quotient of a group by a maximal normal subgroup has only the two trivial subgroups. -/
public lemma quotient_subgroup_eq_bot_or_top_of_coatom {R : Type*} [Group R]
    {K : Subgroup R} [K.Normal] (hK : IsCoatom K) :
    ∀ H : Subgroup (R ⧸ K), H = ⊥ ∨ H = ⊤ := by
  intro H
  have hK_le_comap : K ≤ H.comap (QuotientGroup.mk' K) := by
    intro x hx
    have hx1 : QuotientGroup.mk' K x = 1 := (QuotientGroup.eq_one_iff (N := K) (x := x)).2 hx
    simp [hx1]
  rcases (hK.le_iff.mp hK_le_comap) with htop | hK_eq
  · right
    calc
      H = (H.comap (QuotientGroup.mk' K)).map (QuotientGroup.mk' K) :=
        (Subgroup.map_comap_eq_self_of_surjective (f := QuotientGroup.mk' K)
          (h := QuotientGroup.mk'_surjective K) H).symm
      _ = (⊤ : Subgroup R).map (QuotientGroup.mk' K) := by simp [htop]
      _ = ⊤ := Subgroup.map_top_of_surjective (f := QuotientGroup.mk' K)
        (QuotientGroup.mk'_surjective K)
  · left
    calc
      H = (H.comap (QuotientGroup.mk' K)).map (QuotientGroup.mk' K) :=
        (Subgroup.map_comap_eq_self_of_surjective (f := QuotientGroup.mk' K)
          (h := QuotientGroup.mk'_surjective K) H).symm
      _ = K.map (QuotientGroup.mk' K) := by simp [hK_eq]
      _ = ⊥ := by simp

/-- The quotient of a finite p-group by a maximal subgroup has order `p`. -/
public lemma card_quotient_coatom_eq_prime {R : Type*} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)]
    {K : Subgroup R} (hK : IsCoatom K) : Nat.card (R ⧸ K) = p := by
  letI : K.Normal := coatom_normal_of_isPGroup (p := p) (K := K) hK
  have hq_pgroup : IsPGroup p (R ⧸ K) := (Fact.out : IsPGroup p R).to_quotient K
  rcases hq_pgroup.exists_card_eq with ⟨n, hn⟩
  have hn_ne_zero : n ≠ 0 := by
    intro hn0
    have hcard1 : Nat.card (R ⧸ K) = 1 := by simpa [hn0] using hn
    have hsub : Subsingleton (R ⧸ K) := (Nat.card_eq_one_iff_unique.mp hcard1).1
    exact hK.1 ((QuotientGroup.subsingleton_iff (N := K)).1 hsub)
  have hn_le_one : n ≤ 1 := by
    by_contra hnot
    have hn_ge_two : 2 ≤ n := by omega
    have hp_dvd : p ∣ Nat.card (R ⧸ K) := by
      rw [hn]
      exact dvd_pow_self p (by omega : n ≠ 0)
    -- Cauchy gives an element of order `p`, whose cyclic subgroup contradicts the
    -- trivial-subgroup property of the quotient.
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := R ⧸ K) p hp_dvd
    let H : Subgroup (R ⧸ K) := Subgroup.zpowers x
    have hH_card : Nat.card H = p := by
      simp [H, hx, Nat.card_zpowers]
    have hH_ne_bot : H ≠ ⊥ := by
      intro hbot
      have : Nat.card H = 1 := by simp [hbot]
      exact (Fact.out : Nat.Prime p).ne_one (by simpa [hH_card] using this)
    have hH_ne_top : H ≠ ⊤ := by
      intro htop
      have hp_lt : p < p ^ n := by
        simpa using (Nat.pow_lt_pow_iff_right (show 1 < p from (Fact.out : Nat.Prime p).one_lt)).2
          (by omega : 1 < n)
      have hcard_eq : p = p ^ n := by
        calc
          p = Nat.card H := hH_card.symm
          _ = Nat.card (R ⧸ K) := by simp [htop]
          _ = p ^ n := hn
      exact (ne_of_lt hp_lt) hcard_eq
    exact (quotient_subgroup_eq_bot_or_top_of_coatom (K := K) hK H).elim
      hH_ne_bot hH_ne_top
  have hn_eq_one : n = 1 := by omega
  simp [hn, hn_eq_one]

end CFSG.Theory.PGroup
