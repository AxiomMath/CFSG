module

public import CFSG.RankThree.PartOne.KC.OrthogonalBlockDet
public import CFSG.LieType.BorelTits.CompleteFlag

public section

open Polynomial

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.RankThree.PartOne.KCOrthogonal

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem mem_specialBlock_of_pow_two_pow {h : K[X]} (hh : Irreducible h) {g : V ≃ₗ[K] V}
    (hg : g ∈ supportedBlock Q x h) {e : ℕ} (hge : g ^ (2 ^ e) = 1) :
    g ∈ specialBlock Q x h := by
  haveI : Fact (Irreducible h) := ⟨hh⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP (AdjoinRoot h) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot h)).injective 2
  refine mem_specialBlock.mpr ⟨hg, ?_⟩
  have h1 : (⟨g, hg⟩ : ↥(supportedBlock Q x h)) ^ 2 ^ e = 1 :=
    Subtype.ext (by simpa using hge)
  have hc : blockDet Q x h ⟨g, hg⟩ ^ 2 ^ e = 1 := by rw [← map_pow, h1, map_one]
  have h0 : (blockDet Q x h ⟨g, hg⟩ - 1) ^ 2 ^ e = 0 := by
    rw [sub_pow_char_pow, hc, one_pow, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero e (by decide))).mp h0)

end OrthTorus

end CFSG.StandardType

end
