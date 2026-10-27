module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOne
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneLbar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

namespace Case811L4

@[expose] def vA1 : Multiplicative (Fin 4 → ZMod 3) := Multiplicative.ofAdd ![1, 1, -1, -1]

@[expose] def vA2 : Multiplicative (Fin 4 → ZMod 3) := Multiplicative.ofAdd ![1, -1, 0, 0]

@[expose] def vA3 : Multiplicative (Fin 4 → ZMod 3) := Multiplicative.ofAdd ![1, 1, 1, 0]

@[expose] def vD2 : Multiplicative (Fin 4 → ZMod 3) := Multiplicative.ofAdd ![0, 0, 1, -1]

end Case811L4

structure Case811L4 (c : Counterexample4 G) extends Case811Sylow c where
  r : ℕ
  lie : IsLie811 c.Lbar .l4 r 1
  mem_sigma : r ∈ uniqueFourSigma c.S.M
  e : Multiplicative (Fin 4 → ZMod 3) →* G
  range_e : e.range = A
  e_eq_one_iff : ∀ v, e v = 1 ↔ ∃ s : ZMod 3, Multiplicative.toAdd v = fun _ => s
  exists_perm : ∀ σ : Equiv.Perm (Fin 4), ∃ n ∈ c.L, ∀ v,
    n * e v * n⁻¹ = e (Multiplicative.ofAdd fun i => Multiplicative.toAdd v (σ i))
  mem_L : ∀ x ∈ c.S.M, IsPGroup r (Subgroup.zpowers x) → x ∈ c.L
  dvd_card_centralizer : ∀ X : Subgroup G, X ≤ A → Nat.card X = 3 →
    r ∣ Nat.card ↥(c.L ⊓ Subgroup.centralizer (X : Set G))
  factorization_a1 :
    (Nat.card ↥(c.S.M ⊓ Subgroup.centralizer ({e Case811L4.vA1} : Set G))).factorization r = 2
  factorization_a2 :
    (Nat.card ↥(c.S.M ⊓ Subgroup.centralizer ({e Case811L4.vA2} : Set G))).factorization r = 1
  factorization_a3 :
    (Nat.card ↥(c.S.M ⊓ Subgroup.centralizer ({e Case811L4.vA3} : Set G))).factorization r = 3
  two_le_pRank_a1 : 2 ≤ CFSG.Open.pRank r
    (c.L ⊓ Subgroup.centralizer ({e Case811L4.vA1} : Set G) : Subgroup G)
  two_le_pRank_a3 : 2 ≤ CFSG.Open.pRank r
    (c.L ⊓ Subgroup.centralizer ({e Case811L4.vA3} : Set G) : Subgroup G)
  perfect_a1 : ∃ K : Subgroup G,
    K ≤ c.L ⊓ Subgroup.centralizer ({e Case811L4.vA1} : Set G) ∧ ⁅K, K⁆ = K ∧
      3600 < Nat.card K ∧
      ∀ N : Subgroup G, N ≤ K → (N.subgroupOf K).Normal → Odd (Nat.card N) → N = ⊥
  nonsolvable_a3 : ∃ K : Subgroup G,
    K ≤ c.L ⊓ Subgroup.centralizer ({e Case811L4.vA3} : Set G) ∧ ¬ IsSolvable ↥K ∧
      ∀ N : Subgroup G, N ≤ K → (N.subgroupOf K).Normal → Odd (Nat.card N) →
        N ≤ Subgroup.centralizer (K : Set G)
  sylow_a2 : ∃ Q : Subgroup G, A ≤ Q ∧ IsMulCommutative ↥Q ∧
    CFSG.ABGLocalTools.IsSylowOf 3 Q (c.S.M ⊓ Subgroup.centralizer ({e Case811L4.vA2} : Set G))

namespace Case811L4

variable {c : Counterexample4 G} (t : Case811L4 c)

@[expose] def a1 : G := t.e vA1

@[expose] def a2 : G := t.e vA2

@[expose] def a3 : G := t.e vA3

@[expose] def d2 : G := t.e vD2

theorem five_le : 5 ≤ t.r := c.five_le_of_mem_sigma t.mem_sigma

theorem e_mem_A (v : Multiplicative (Fin 4 → ZMod 3)) : t.e v ∈ t.A := by
  rw [← t.range_e]
  exact MonoidHom.mem_range.mpr ⟨v, rfl⟩

theorem e_pow_three (v : Multiplicative (Fin 4 → ZMod 3)) : t.e v ^ 3 = 1 :=
  t.elemAbelian.2 _ (t.e_mem_A v)

theorem orderOf_e {v : Multiplicative (Fin 4 → ZMod 3)}
    (hv : ¬ ∃ s : ZMod 3, Multiplicative.toAdd v = fun _ => s) : orderOf (t.e v) = 3 :=
  orderOf_eq_prime (t.e_pow_three v) fun h => hv ((t.e_eq_one_iff v).mp h)

theorem card_zpowers_e {v : Multiplicative (Fin 4 → ZMod 3)}
    (hv : ¬ ∃ s : ZMod 3, Multiplicative.toAdd v = fun _ => s) :
    Nat.card (Subgroup.zpowers (t.e v)) = 3 := by
  rw [Nat.card_zpowers, t.orderOf_e hv]

end Case811L4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
