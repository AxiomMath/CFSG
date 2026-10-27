module

public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoTorus
public import CFSG.RankThree.PartOne.Census3.Interface

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open Subgroup
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem eq_bot_or_eq_of_le_of_mulEquiv_psl2GF {Y : Type} [Group Y] [Finite Y] {p n : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hn : 1 ≤ n) {K : Subgroup Y}
    (e : K ≃* CFSG.AGLEmbedding.PSL2GF p n) {U W : Subgroup Y} (hUK : U ≤ K)
    (hcard : Nat.card U = p ^ n) (hWU : W ≤ U)
    (hW : K ⊓ normalizer (U : Set Y) ≤ normalizer (W : Set Y)) : W = ⊥ ∨ W = U := by
  classical
  obtain ⟨ψ, -, hψU, hc⟩ :=
    CFSG.AGLEmbedding.exists_torus_param_of_mulEquiv_psl2GF hp2 hn e U hUK hcard
  have hmulW : ∀ (μ : (GaloisField p n)ˣ) (a : Multiplicative (GaloisField p n)), ψ a ∈ W →
      ψ (Multiplicative.ofAdd ((μ : GaloisField p n) ^ 2 * Multiplicative.toAdd a)) ∈ W := by
    intro μ a ha
    obtain ⟨c, hcK, hcψ⟩ := hc μ
    have hcU : c ∈ normalizer (U : Set Y) := by
      rw [← hψU]
      refine mem_normalizer_iff.mpr fun y => ⟨?_, ?_⟩
      · rintro ⟨a, rfl⟩
        exact ⟨_, (hcψ a).symm⟩
      · rintro ⟨b, hb⟩
        refine ⟨Multiplicative.ofAdd
          (((μ⁻¹ : (GaloisField p n)ˣ) : GaloisField p n) ^ 2 * Multiplicative.toAdd b), ?_⟩
        have key : (μ : GaloisField p n) ^ 2 *
            (((μ⁻¹ : (GaloisField p n)ˣ) : GaloisField p n) ^ 2 * Multiplicative.toAdd b) =
              Multiplicative.toAdd b := by
          rw [← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]
        have h1 := hcψ (Multiplicative.ofAdd
          (((μ⁻¹ : (GaloisField p n)ˣ) : GaloisField p n) ^ 2 * Multiplicative.toAdd b))
        rw [toAdd_ofAdd, key, ofAdd_toAdd, hb] at h1
        exact mul_left_cancel (mul_right_cancel h1)
    have h2 := (mem_normalizer_iff.mp (hW ⟨hcK, hcU⟩) _).mp ha
    rwa [hcψ] at h2
  rcases bot_or_exists_ne_one W with hW1 | ⟨w, hwW, hw1⟩
  · exact Or.inl hW1
  right
  have hwU : w ∈ ψ.range := hψU ▸ hWU hwW
  obtain ⟨a₀, rfl⟩ := hwU
  have ha : Multiplicative.toAdd a₀ ≠ 0 := by
    intro h
    apply hw1
    rw [show a₀ = 1 from h, map_one]
  have hsq : ∀ s : GaloisField p n,
      ψ (Multiplicative.ofAdd (s ^ 2 * Multiplicative.toAdd a₀)) ∈ W := by
    intro s
    rcases eq_or_ne s 0 with rfl | hs
    · rw [zero_pow two_ne_zero, zero_mul, ofAdd_zero, map_one]
      exact W.one_mem
    · simpa using hmulW (Units.mk0 s hs) a₀ hwW
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  have hodd : Fintype.card (GaloisField p n) % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p n (by omega)]
    exact Nat.odd_iff.mp ((Nat.Prime.odd_of_ne_two Fact.out hp2).pow)
  refine le_antisymm hWU ?_
  rw [← hψU]
  rintro _ ⟨b, rfl⟩
  obtain ⟨s, t, hst⟩ := CFSG.SectionRank.OddCover.exists_sq_add_sq hodd
    (Multiplicative.toAdd b / Multiplicative.toAdd a₀)
  have hb : b = Multiplicative.ofAdd (s ^ 2 * Multiplicative.toAdd a₀) *
      Multiplicative.ofAdd (t ^ 2 * Multiplicative.toAdd a₀) := by
    rw [← ofAdd_add, ← add_mul, hst, div_mul_cancel₀ _ ha, ofAdd_toAdd]
  rw [hb, map_mul]
  exact W.mul_mem (hsq s) (hsq t)

theorem eq_bot_or_eq_of_le_of_isoLie_A1 {Y : Type} [Group Y] [Finite Y]
    {q : TauCeti.PrimePower} (hq2 : q.p ≠ 2) {K : Subgroup Y} (hK : IsoLie ↥K (.A 1 q))
    {U W : Subgroup Y} (hUK : U ≤ K) (hcard : Nat.card U = q.card) (hWU : W ≤ U)
    (hW : K ⊓ normalizer (U : Set Y) ≤ normalizer (W : Set Y)) : W = ⊥ ∨ W = U := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨hv, ⟨e₁⟩⟩ := hK
  obtain ⟨e₂⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex
    (p := q.p) (n := q.exponent) (d := ⟨.A 1 q, hv⟩) ⟨q, rfl, rfl, rfl⟩
  exact eq_bot_or_eq_of_le_of_mulEquiv_psl2GF hq2 q.exponent_pos (e₁.trans e₂) hUK
    (hcard.trans q.card_def) hWU hW

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
