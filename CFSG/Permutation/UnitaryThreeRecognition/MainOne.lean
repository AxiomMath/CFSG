module

public import CFSG.Permutation.UnitaryThreeRecognition.AssemblyOne
public import CFSG.Permutation.UnitaryThreeRecognition.AbelianQMain
public import CFSG.Permutation.UnitaryThreeRecognition.HeisCoordinates
public import CFSG.Permutation.UnitaryThreeRecognition.Exponent

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model

theorem heis_coordHyp {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G] [Finite Ω]
    {Q : Subgroup G} {a b : Ω} {j s : G} {p f : ℕ}
    (S : StdHyp G Q a b j s p f (Nat.gcd (p ^ f + 1) 3))
    (hnonab : ∃ x ∈ Q, ∃ y ∈ Q, x * y ≠ y * x)
    {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (hK : Nat.card K = (p ^ f) ^ 2)
    (hconj : ∀ x : K, J.conj x = x ^ (p ^ f)) :
    ∃ φ : Q ≃* Coord J, CoordHyp Q a b j J φ := by
  have : Fact p.Prime := ⟨S.hpp⟩
  have hpodd : p ≠ 2 := by have := S.hp; omega
  obtain ⟨φ, h1, h2, h3⟩ := Heisenberg.heisenberg_coordinates Q (pairStab G a b) (centQ Q j)
    (swapFix G a b s) hpodd S.hf rfl (fun t ht x hx => S.root.normal t ht.1 x hx) S.hcomm
    inf_le_left (fun x hx z hz => S.centQ_commute hx hz)
    (fun x hx y hy => S.root.commutator_mem_centQ S.hb S.htwo S.hfaith S.hcomm S.hj S.hj2 S.hj1
      S.hsq S.hpp S.hp S.hf S.hpodd S.hd S.hd3 S.hQcard S.hΩcard S.hTcard S.hsa S.hs2 hx hy)
    (fun x hx => S.root.pow_prime_eq_one S.hb S.htwo S.hfaith S.hcomm S.hj S.hj2 S.hj1 S.hsq
      S.hpp S.hp S.hf S.hpodd S.hd S.hd3 S.hQcard S.hΩcard S.hTcard S.hsa S.hs2 hx)
    hnonab (fun t ht z hz => S.root.conj_mem_centQ S.hcomm S.hj ht hz)
    (fun t ht ht1 x hx htx => S.mem_centQ_of_commute ht ht1 hx htx)
    (fun z₁ hz₁ z₂ hz₂ hz₁1 hz₂1 => S.root.exists_conj_eq_of_mem_centQ S.hb S.htwo S.hfaith
      S.hcomm S.hj S.hj2 S.hj1 S.hsq S.hpp S.hp S.hf S.hpodd S.hd S.hQcard S.hΩcard S.hTcard
      S.hsa S.hs2 hz₁ hz₁1 hz₂ hz₂1)
    (fun w hw => (mem_swapFix.mp hw).1) (fun w hw z hz => S.swapFix_commute hw hz)
    (fun N hZN hNQ hTN => S.root.eq_centQ_or_eq_of_conj_mem S.hb S.htwo S.hfaith S.hcomm S.hj
      S.hj2 S.hj1 S.hsq S.hpp S.hp S.hf S.hpodd S.hd S.hd3 S.hQcard S.hΩcard S.hTcard S.hsa
      S.hs2 N hZN hNQ hTN)
    S.hQcard S.card_centQ S.hTcard
    (S.root.card_swapFix_mul S.hb S.htwo S.hfaith S.hcomm S.hj S.hj2 S.hj1 S.hsq S.hpp S.hp S.hf
      S.hpodd S.hd S.hQcard S.hΩcard S.hTcard S.hsa S.hs2) J hJ hK hconj
  exact ⟨φ, coordHyp_of S φ h1 h2 h3⟩

theorem faithfulSMul_of_stdHyp {G Ω : Type*} [Group G] [MulAction G Ω] {Q : Subgroup G}
    {a b : Ω} {j s : G} {p f d : ℕ} (S : StdHyp G Q a b j s p f d) : FaithfulSMul G Ω :=
  ⟨fun {g₁ g₂} h => by
    have := S.hfaith (g₁⁻¹ * g₂) (fun x => by rw [mul_smul, ← h x, inv_smul_smul])
    rw [inv_mul_eq_one] at this
    exact this⟩

theorem ne_bot_of_stdHyp {G Ω : Type*} [Group G] [MulAction G Ω] {Q : Subgroup G}
    {a b : Ω} {j s : G} {p f d : ℕ} (S : StdHyp G Q a b j s p f d) : Q ≠ ⊥ := by
  intro e
  have := S.hQcard
  rw [e, Subgroup.card_bot] at this
  have : 1 < p ^ (3 * f) := Nat.one_lt_pow (by have := S.hf; omega) (by have := S.hp; omega)
  omega

theorem statedClassicalModel_of_stdHyp_coprime {G Ω : Type} [Group G] [Finite G]
    [IsSimpleGroup G] [MulAction G Ω] [Finite Ω] (h2 : IsMultiplyPretransitive G Ω 2)
    {Q : Subgroup G} {a b : Ω} {j s : G} {p f : ℕ}
    (S : StdHyp G Q a b j s p f (Nat.gcd (p ^ f + 1) 3)) (hd1 : Nat.gcd (p ^ f + 1) 3 = 1) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU 3 p f := by
  have := faithfulSMul_of_stdHyp S
  have h5 : p ^ f ≠ 5 := by intro e; rw [e] at hd1; norm_num at hd1
  have hnonab := AbelianQ.exists_not_commute_of_ne_five S.root S.hb S.htwo S.hfaith S.hcomm S.hj
    S.hj2 S.hj1 S.hsq S.hpp S.hp S.hf S.hpodd rfl S.hQcard S.hΩcard S.hTcard S.hsa S.hs2 h5
  obtain ⟨K, _, _, J, hK, hJ, hconj, hfix⟩ := exists_unitaryModelField p f S.hpp S.hf
  obtain ⟨φ, C⟩ := heis_coordHyp S hnonab J hJ hK hconj
  have hcop : Nat.Coprime 3 (p ^ f + 1) := by rw [Nat.Coprime, Nat.gcd_comm]; exact hd1
  exact statedClassicalModel_of_coordHyp_coprime h2 S (ne_bot_of_stdHyp S) J hJ hK hconj hfix C
    hcop

end CFSG.UnitaryThreeRecognition
