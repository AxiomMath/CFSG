module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.S12.TerminalWeylDet
public import CFSG.RankThree.PartOne.S13K.Pair134Basic

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def NoRankThree (p : ℕ) (X : Type) [Group X] : Prop :=
  ¬ ∃ Ē : Subgroup (MulAut X), IsElementaryAbelian p Ē ∧ Nat.card Ē = p ^ 3

theorem NoRankThree.of_mulEquiv {X Y : Type} [Group X] [Group Y] {p : ℕ} (hp : p.Prime)
    (e : X ≃* Y) (h : NoRankThree p Y) : NoRankThree p X := by
  rintro ⟨Ē, hEl, hcard⟩
  have : Fact p.Prime := ⟨hp⟩
  refine h ⟨Ē.map (MulAut.congr e).toMonoidHom, ?_, ?_⟩
  · have := hEl
    exact IsElementaryAbelian.map (MulAut.congr e).toMonoidHom
  · rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, hcard]

theorem le_inner_of_isPGroup_of_not_dvd_outer {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hOut : ¬ p ∣ Nat.card (Outer X)) {P : Subgroup (MulAut X)} (hP : IsPGroup p P) :
    P ≤ inner X := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP
  let φ : ↥P →* Outer X := (QuotientGroup.mk' (inner X)).comp P.subtype
  have h1 : Nat.card φ.range ∣ p ^ k := hk ▸ Subgroup.card_range_dvd φ
  have h2 : Nat.card φ.range ∣ Nat.card (Outer X) := Subgroup.card_subgroup_dvd_card _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 h1
  have hj0 : j = 0 := by
    by_contra hj0
    exact hOut ((dvd_pow_self p hj0).trans (hj ▸ h2))
  have hbot : φ.range = ⊥ := Subgroup.card_eq_one.1 (by rw [hj, hj0, pow_zero])
  intro x hx
  have : φ ⟨x, hx⟩ = 1 := by
    have hmem : φ ⟨x, hx⟩ ∈ φ.range := ⟨⟨x, hx⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  exact (QuotientGroup.eq_one_iff x).1 this

theorem noRankThree_of_inner {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hOut : ¬ p ∣ Nat.card (Outer X)) (hX : ¬ p ^ 3 ∣ Nat.card X) : NoRankThree p X := by
  rintro ⟨Ē, hEl, hcard⟩
  have hEp : IsPGroup p Ē := by
    have := hEl
    exact IsElementaryAbelian.isPGroup p Ē
  have hle := le_inner_of_isPGroup_of_not_dvd_outer hp hOut hEp
  have h1 : Nat.card Ē ∣ Nat.card (inner X) := Subgroup.card_dvd_of_le hle
  have h2 : Nat.card (inner X) ∣ Nat.card X := Subgroup.card_range_dvd _
  exact hX (hcard ▸ h1.trans h2)

end CFSG.RankThree.PartOne.K133
