module

public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticTorus
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJCoord
import CFSG.LocalAnalysis.StandardType.GGTBJSpParabolicAut
import CFSG.LocalAnalysis.StandardType.GGTBJFrameCorank

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open (StatedSp)

theorem ggCommonJSpSplit_count {K : Type} [Field K] {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : Kˣ} (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p) (f₀ : Fin r → Multiplicative (ZMod p))
    {J : Subgroup (StatedSp r K)} {lam : Multiplicative (ZMod p)}
    (hfix : ∀ g : Fin r → Multiplicative (ZMod p),
      (∀ j ∈ J,
          TableBSymp.spTorusSp (m := r) hζ g * j = j * TableBSymp.spTorusSp (m := r) hζ g) ↔
        ((lam = 1 ∧ ∀ i, f₀ i = 1 → g i = 1) ∨
          (lam ≠ 1 ∧ ∃ c : Multiplicative (ZMod p), ∀ i,
            (f₀ i = lam → g i = c) ∧ (f₀ i = lam⁻¹ → g i = c⁻¹))))
    (hm : lam ≠ 1 → 1 ≤ Nat.card {i : Fin r // f₀ i = lam ∨ f₀ i = lam⁻¹}) :
    Nat.card ↥((TableBSymp.spTorusSp (m := r) hζ).range ⊓
        Subgroup.centralizer (J : Set (StatedSp r K))) =
      if lam = 1 then p ^ (r - Nat.card {i : Fin r // f₀ i = 1})
      else p ^ (r - Nat.card {i : Fin r // f₀ i = lam ∨ f₀ i = lam⁻¹} + 1) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let τ : (Fin r → Multiplicative (ZMod p)) →* StatedSp r K :=
    TableBSymp.spTorusSp (m := r) hζ
  have hτ : Function.Injective τ := TableBSymp.spTorusSp_injective (m := r) hζ hζo
  change Nat.card ↥(τ.range ⊓ Subgroup.centralizer (J : Set (StatedSp r K))) =
    if lam = 1 then p ^ (r - Nat.card {i : Fin r // f₀ i = 1})
    else p ^ (r - Nat.card {i : Fin r // f₀ i = lam ∨ f₀ i = lam⁻¹} + 1)
  have hfixτ : ∀ g : Fin r → Multiplicative (ZMod p),
      τ g ∈ Subgroup.centralizer (J : Set (StatedSp r K)) ↔
        ((lam = 1 ∧ ∀ i, f₀ i = 1 → g i = 1) ∨
          (lam ≠ 1 ∧ ∃ c : Multiplicative (ZMod p), ∀ i,
            (f₀ i = lam → g i = c) ∧ (f₀ i = lam⁻¹ → g i = c⁻¹))) := by
    intro g
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      exact (hfix g).mp fun j hj => (h j hj).symm
    · intro h j hj
      exact ((hfix g).mpr h j hj).symm
  have hcard : Nat.card ↥(τ.range ⊓ Subgroup.centralizer (J : Set (StatedSp r K))) =
      Nat.card {g : Fin r → Multiplicative (ZMod p) //
        τ g ∈ Subgroup.centralizer (J : Set (StatedSp r K))} := by
    rw [← Subgroup.map_comap_eq (f := τ)
      (H := Subgroup.centralizer (J : Set (StatedSp r K)))]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective
      (Subgroup.comap τ (Subgroup.centralizer (J : Set (StatedSp r K)))) τ hτ).toEquiv).symm
  rw [hcard, Nat.card_congr (Equiv.subtypeEquivRight hfixτ)]
  by_cases hlam : lam = 1
  · rw [if_pos hlam]
    have hiff : ∀ g : Fin r → Multiplicative (ZMod p),
        ((lam = 1 ∧ ∀ i, f₀ i = 1 → g i = 1) ∨
          (lam ≠ 1 ∧ ∃ c : Multiplicative (ZMod p), ∀ i,
            (f₀ i = lam → g i = c) ∧ (f₀ i = lam⁻¹ → g i = c⁻¹))) ↔
        (∀ i, f₀ i = 1 → g i = 1) := by
      intro g
      rw [hlam]
      simp
    rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
    let S : Finset (Fin r) := Finset.univ.filter (fun i => f₀ i = 1)
    have hSet : Nat.card {g : Fin r → Multiplicative (ZMod p) // ∀ i, f₀ i = 1 → g i = 1} =
        Nat.card {g : Fin r → Multiplicative (ZMod p) // ∀ i ∈ S, g i = 1} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp [S])
    rw [hSet, FrameBs.card_frame_trivial_on S]
    have hScard : S.card = Nat.card {i : Fin r // f₀ i = 1} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hScard]
  · rw [if_neg hlam]
    have hne_inv : lam ≠ lam⁻¹ := by
      intro h
      apply hlam
      haveI : Fact p.Prime := ⟨hp⟩
      have hx : Multiplicative.toAdd lam = -Multiplicative.toAdd lam := by
        have := congrArg Multiplicative.toAdd h
        simpa using this
      have h2x : (2 : ZMod p) * Multiplicative.toAdd lam = 0 := by
        rw [two_mul]
        exact eq_neg_iff_add_eq_zero.mp hx
      have h2z : (2 : ZMod p) ≠ 0 := by
        intro h2
        have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2
        rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
        · exact hp.ne_one h1
        · exact hp2 h1
      have hx0 : Multiplicative.toAdd lam = 0 := (mul_eq_zero.mp h2x).resolve_left h2z
      have h1 : Multiplicative.ofAdd (Multiplicative.toAdd lam) = 1 := by
        rw [hx0]
        rfl
      simpa using h1
    have hdisj : ∀ i, f₀ i = lam → f₀ i = lam⁻¹ → False := fun i h1 h2 =>
      hne_inv (h1.symm.trans h2)
    have hne : ∃ i, f₀ i = lam ∨ f₀ i = lam⁻¹ := by
      have hpos : 0 < Nat.card {i : Fin r // f₀ i = lam ∨ f₀ i = lam⁻¹} := by
        have := hm hlam
        omega
      obtain ⟨i, hi⟩ := (Nat.card_pos_iff.mp hpos).1
      exact ⟨i, hi⟩
    have hiff : ∀ g : Fin r → Multiplicative (ZMod p),
        ((lam = 1 ∧ ∀ i, f₀ i = 1 → g i = 1) ∨
          (lam ≠ 1 ∧ ∃ c : Multiplicative (ZMod p), ∀ i,
            (f₀ i = lam → g i = c) ∧ (f₀ i = lam⁻¹ → g i = c⁻¹))) ↔
        (∃ c : Multiplicative (ZMod p), ∀ i,
          (f₀ i = lam → g i = c) ∧ (f₀ i = lam⁻¹ → g i = c⁻¹)) := by
      intro g
      constructor
      · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
        · exact absurd h1 hlam
        · exact h2
      · intro h
        exact Or.inr ⟨hlam, h⟩
    rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
    rw [CommonJ.card_scalar_param (p := p) (r := r) (P := fun i => f₀ i = lam)
      (Q := fun i => f₀ i = lam⁻¹) hdisj hne]
    rw [mul_comm, ← pow_succ]

end CFSG.StandardType

end
