module

public import CFSG.RankThree.PartOne.KE.CTTwisted
public import CFSG.RankThree.PartOne.KE.CTTwistedArith
public import CFSG.RankThree.Lattice.SteinbergBTTwistedE6Phi8
public import CFSG.RankThree.Chevalley.SteinbergBNExceptionalCyclotomicExhaustion

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  Polynomial Matrix
open CFSG.RankThree.Chevalley (exhaustionPhi)
open CFSG.RankThree.E6 (charVal)

theorem twisted_E6_eight_cyclic_sylow {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpf : (p : ℤ) ∣ (exhaustionPhi 8).eval ((ℓ ^ f : ℕ) : ℤ)) :
    7 < p ∧ orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 8 ∧
      ∃ k : ℕ, CyclicSylowConclusion' (twistedE6RootGroup K σ) p
        (((ℓ ^ f) ^ 4 + 1) * ((ℓ ^ f) ^ 2 - 1)) (3 ^ k) := by
  have hq : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have hpf' : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 4 + 1 := by simpa [exhaustionPhi] using hpf
  obtain ⟨hp7, hpq, hord⟩ := CTE6.e6Eight_data hp hp3 hpf'
  refine ⟨hp7, hord, ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  have hx : ((ℓ ^ f : ℕ) : ZMod p) ^ 4 + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (((ℓ ^ f : ℕ) : ℤ) ^ 4 + 1) p).2 hpf'
    simpa using this
  obtain ⟨v, hv⟩ := e6P8_weyl
  obtain ⟨-, -, -, ⟨b, -, hlin, hspan⟩, hreg⟩ :=
    twisted_E6_Phi8_signed_cyclic_lattice_and_regular_root_characters
  have h2 : 1 ≤ (ℓ ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hn₀ : ((ℓ ^ f) ^ 4 + 1) * ((ℓ ^ f) ^ 2 - 1) ≠ 0 := by
    have : 1 < (ℓ ^ f) ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    exact Nat.mul_ne_zero (by omega) (by omega)
  have hev : e6P8U.charpoly.eval ((ℓ ^ f : ℕ) : ℤ) =
      ((((ℓ ^ f) ^ 4 + 1) * ((ℓ ^ f) ^ 2 - 1) : ℕ) : ℤ) := by
    rw [charpoly_e6P8U]
    push_cast [Nat.cast_sub h2]
    simp
  have hnat : (e6P8U.charpoly.eval ((ℓ ^ f : ℕ) : ℤ)).natAbs =
      ((ℓ ^ f) ^ 4 + 1) * ((ℓ ^ f) ^ 2 - 1) := by
    rw [hev, Int.natAbs_natCast]
  have hne : e6P8U.charpoly.eval ((ℓ ^ f : ℕ) : ℤ) ≠ 0 := by
    rw [hev]
    exact_mod_cast hn₀
  have hdet : e6P8U.charpoly.coeff 0 = 1 ∨ e6P8U.charpoly.coeff 0 = -1 := by
    right
    rw [charpoly_e6P8U, coeff_zero_eq_eval_zero]
    simp
  have hreg' : ∀ z : Fin TwistTag.E6.tag.rank → ZMod p, z ≠ 0 →
      ((e6P8U.map (Int.cast : ℤ → ZMod p)).transpose).mulVec z =
        ((ℓ ^ f : ℕ) : ZMod p) • z →
      ∀ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α → charVal z α ≠ 0 :=
    fun z hz0 hz α hα => hreg p hp3 _ hx z hz0 hz α hα
  have hord' : p ^ ((ℓ ^ f) ^ 36 * ((ℓ ^ f) ^ 12 - 1) * ((ℓ ^ f) ^ 9 + 1) * ((ℓ ^ f) ^ 8 - 1) *
        ((ℓ ^ f) ^ 6 - 1) * ((ℓ ^ f) ^ 5 + 1) * ((ℓ ^ f) ^ 2 - 1)).factorization p =
      p ^ (e6P8U.charpoly.eval ((ℓ ^ f : ℕ) : ℤ)).natAbs.factorization p := by
    rw [hnat]
    exact CTTw.ordProj_twisted_eight hp hq hpq hord
  obtain ⟨k, hk⟩ := cyclic_sylow_twisted_E6 hℓ hf K hK σ hσ hp hp7 e6P8U v hv b hlin hspan hdet
    hne hreg' hord'
  exact ⟨k, hnat ▸ hk⟩

end CFSG.RankThree.PartOne.KE
