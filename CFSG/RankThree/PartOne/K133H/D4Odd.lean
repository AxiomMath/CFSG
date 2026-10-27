module

public import CFSG.RankThree.PartOne.K133H.WeylKey
public import CFSG.RankThree.PartOne.K133H.SylowTorus
public import CFSG.RankThree.PartOne.K133H.TorusOdd
public import CFSG.RankThree.PartOne.KGD.D4Weyl

public section

namespace CFSG.RankThree.PartOne.K133H

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.S13K

theorem weylD4_eq_one_or_three (w : WeylGroup Tag.D4) (h : Odd (orderOf w)) :
    orderOf w = 1 ∨ orderOf w = 3 := by
  have hd : orderOf w ∣ 12 := orderOf_dvd_of_pow_eq_one (KGD.d4_weyl_pow_twelve w)
  have hmem : orderOf w ∈ Nat.divisors 12 := Nat.mem_divisors.2 ⟨hd, by norm_num⟩
  have h12 : Nat.divisors 12 = {1, 2, 3, 4, 6, 12} := by decide
  rw [h12] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h2 | h3 | h4 | h6 | h12'
  · exact Or.inl h1
  · exact absurd h (by rw [h2]; decide)
  · exact Or.inr h3
  · exact absurd h (by rw [h4]; decide)
  · exact absurd h (by rw [h6]; decide)
  · exact absurd h (by rw [h12']; decide)

theorem factorization_card_adjointGroup_D4 {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpK : p ∣ Nat.card K - 1) :
    (Nat.card ↥(adjointGroup Tag.D4 K)).factorization p =
      (Nat.card ↥(torusGroup Tag.D4 K)).factorization p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype (WeylGroup Tag.D4) := Fintype.ofFinite _
  have hK1 : 1 ≤ Nat.card K := Nat.card_pos
  have hq1 : ((Nat.card K : ℕ) : ZMod p) = 1 := by
    have h0 := (ZMod.natCast_eq_zero_iff _ _).2 hpK
    rw [Nat.cast_sub hK1, Nat.cast_one, sub_eq_zero] at h0
    exact h0
  have hT0 : Nat.card ↥(torusGroup Tag.D4 K) ≠ 0 := Nat.card_pos.ne'
  have hqN : ¬ p ∣ Nat.card K ^
      {α : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 α ∧ 0 < height α}.ncard := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_pow, hq1, one_pow]
    exact one_ne_zero
  have hS : ¬ p ∣ ∑ᶠ w : WeylGroup Tag.D4, Nat.card K ^ (coxeterSystem Tag.D4).length w := by
    rw [← ZMod.natCast_eq_zero_iff, finsum_eq_sum_of_fintype, Nat.cast_sum]
    simp only [Nat.cast_pow, hq1, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one]
    rw [← Nat.card_eq_fintype_card, ZMod.natCast_eq_zero_iff]
    exact KGD.not_dvd_card_weylGroup_D4 hp (by omega)
  have hqN0 : Nat.card K ^ {α : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 α ∧ 0 < height α}.ncard ≠ 0 :=
    pow_ne_zero _ (by omega)
  have hS0 : ∑ᶠ w : WeylGroup Tag.D4, Nat.card K ^ (coxeterSystem Tag.D4).length w ≠ 0 := by
    intro h0
    exact hS (h0 ▸ dvd_zero p)
  rw [card_adjointGroup, Nat.factorization_mul (mul_ne_zero hT0 hqN0) hS0,
    Nat.factorization_mul hT0 hqN0, Finsupp.add_apply, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hqN, Nat.factorization_eq_zero_of_not_dvd hS, add_zero,
    add_zero]

theorem oddOrderOneOrThree_torusImage_of_embedding_D4 {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : p ∣ Nat.card K - 1) {Q : Type} [Group Q]
    (ι : Q →* ModGL Tag.D4 K) (hι : Function.Injective ι)
    (hιY : ∀ x, ι x ∈ adjointGroup Tag.D4 K) {Ē : Subgroup Q} (hpow : ∀ x ∈ Ē, x ^ p = 1) :
    OddOrderOneOrThree ↥(torusImage Ē ⊤) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL Tag.D4 K) := finite_modGL
  have hTY : torusGroup Tag.D4 K ≤ adjointGroup Tag.D4 K :=
    (Subgroup.closure_le _).2 fun _ ⟨p, hp⟩ => hp ▸ torusElt_mem_adjointGroup p.1 p.2
  obtain ⟨g, hgY, hg⟩ := exists_conj_le_of_sylow (p := p) (Y := adjointGroup Tag.D4 K)
    (H := torusGroup Tag.D4 K) (A := Ē.map ι) hTY
    (by rintro _ ⟨x, -, rfl⟩; exact hιY x)
    (by rintro _ ⟨x, hx, rfl⟩; rw [← map_pow, hpow x hx, map_one])
    (factorization_card_adjointGroup_D4 hp hp5 hpK)
  let ι₁ : Q →* ModGL Tag.D4 K := (MulAut.conj g).toMonoidHom.comp ι
  have hι₁ : Function.Injective ι₁ := (MulAut.conj g).injective.comp hι
  have hV : Ē.map ι₁ = (Ē.map ι).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_map]
  have hι₁Y : ∀ x, ι₁ x ∈ adjointGroup Tag.D4 K := fun x =>
    mul_mem (mul_mem hgY (hιY x)) (inv_mem hgY)
  exact oddOrderOneOrThree_torusImage_of_injective ι₁ hι₁ rfl hι₁Y fun β hβ hodd =>
    eq_one_or_three_of_mem_torusImage (fun w hw => weylD4_eq_one_or_three w hw) (hV ▸ hg) hβ hodd

end CFSG.RankThree.PartOne.K133H
