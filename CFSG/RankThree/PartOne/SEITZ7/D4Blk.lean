module

public import CFSG.RankThree.PartOne.SEITZ7.D4Swap

public section

namespace CFSG.RankThree.PartOne.SEITZ7

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
open scoped commutatorElement

variable {K : Type} [Field K] (σ : K →+* K)

@[expose] noncomputable def xA (a : K) : adjointGroup d4 K := xd 0 a * xd 1 (σ a) * xd 3 (σ (σ a))

@[expose] noncomputable def xAB (c : K) : adjointGroup d4 K := xd 5 c * xd 7 (σ c) * xd 9 (σ (σ c))

@[expose] noncomputable def xAAB (c : K) : adjointGroup d4 K :=
  xd 12 c * xd 15 (σ c) * xd 13 (σ (σ c))

@[expose] noncomputable def xB (c : K) : adjointGroup d4 K := xd 2 c

@[expose] noncomputable def xN (c : K) : adjointGroup d4 K := xd 19 c

@[expose] noncomputable def xH (c : K) : adjointGroup d4 K := xd 22 c

@[expose] noncomputable def ordT (c : ℕ → K) : adjointGroup d4 K :=
  xB (c 0) * xA σ (c 1) * xAB σ (c 4) * xAAB σ (c 8) * xN (c 3) * xH (c 7)

theorem ofNat_eq_char2 [CharP K 2] (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : K) = ((n % 2 : ℕ) : K) := by
  rw [← Nat.cast_ofNat]
  exact (CharP.natCast_eq_natCast K 2).2 (Nat.mod_modEq n 2).symm

macro "d4fin" : tactic => `(tactic| (ring_nf; simp [ofNat_eq_char2, xd_zero]; try ring_nf))

theorem conj_xA [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) (c : ℕ → K) (hb : σ (c 0) = c 0)
    (a : K) :
    ordT σ c * xA σ a * (ordT σ c)⁻¹ =
      xA σ a * xAB σ (a * c 0) * xAAB σ (a * σ (c 4) + σ a * c 4 + a * σ a * c 0) *
        xN (a*(σ a)*(σ (σ a))*(c 0) + a*(σ a)*(σ (σ (c 4))) + a*(σ (σ a))*(σ (c 4)) +
            a*(σ (c 1))*(σ (σ (c 4))) + a*(σ (σ (c 1)))*(σ (c 4)) + a*(σ (c 8)) +
            (σ a)*(σ (σ a))*(c 4) + (σ a)*(c 1)*(σ (σ (c 4))) + (σ a)*(σ (σ (c 1)))*(c 4) +
            (σ a)*(σ (σ (c 8))) + (σ (σ a))*(c 1)*(σ (c 4)) + (σ (σ a))*(σ (c 1))*(c 4) +
            (σ (σ a))*(c 8)) *
        xH (a*(σ a)*(c 0)*(σ (σ (c 4))) + a*(σ (σ a))*(c 0)*(σ (c 4)) +
            a*(c 0)*(σ (c 1))*(σ (σ (c 4))) + a*(c 0)*(σ (σ (c 1)))*(σ (c 4)) +
            a*(c 0)*(σ (c 8)) + a*(σ (c 4))*(σ (σ (c 4))) + (σ a)*(σ (σ a))*(c 0)*(c 4) +
            (σ a)*(c 0)*(c 1)*(σ (σ (c 4))) + (σ a)*(c 0)*(σ (σ (c 1)))*(c 4) +
            (σ a)*(c 0)*(σ (σ (c 8))) + (σ a)*(c 4)*(σ (σ (c 4))) +
            (σ (σ a))*(c 0)*(c 1)*(σ (c 4)) + (σ (σ a))*(c 0)*(σ (c 1))*(c 4) +
            (σ (σ a))*(c 0)*(c 8) + (σ (σ a))*(c 4)*(σ (c 4))) := by
  unfold ordT xA xAB xAAB xB xN xH
  simp only [mul_inv_rev, xd_inv, map_add, map_mul, hσ, hb]
  d4coll
  d4fin

theorem conj_xB [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) (c : ℕ → K) (d : K) (hd : σ d = d) :
    ordT σ c * xB d * (ordT σ c)⁻¹ =
      xB d * xAB σ (d * c 1) * xAAB σ (d * c 1 * σ (c 1)) *
        xN (d * (c 1 * σ (c 1) * σ (σ (c 1)))) *
        xH (c 0 * d * (c 1 * σ (c 1) * σ (σ (c 1))) + d ^ 2 * (c 1 * σ (c 1) * σ (σ (c 1))) +
          d * c 3) := by
  unfold ordT xA xAB xAAB xB xN xH
  simp only [mul_inv_rev, xd_inv, map_mul, hσ, hd]
  d4coll
  d4fin

theorem conj_xN [CharP K 2] (c : ℕ → K) (d : K) :
    ordT σ c * xN d * (ordT σ c)⁻¹ = xN d * xH (c 0 * d) := by
  unfold ordT xA xAB xAAB xB xN xH
  simp only [mul_inv_rev, xd_inv]
  d4coll
  d4fin

end CFSG.RankThree.PartOne.SEITZ7
