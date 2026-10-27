module

public import CFSG.RankThree.PartOne.Q1327S.Witness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness

public section

namespace CFSG.RankThree.PartOne.Q1327S

open CFSG CFSG.RankThree.PartOne CFSG.SectionRank
open scoped commutatorElement

variable {Q : Type} [Group Q]

theorem injective_of_card_sq [Finite Q] {p : ℕ} (hp : p.Prime) {x y : Q} (hx : x ^ p = 1)
    (hy : y ^ p = 1) (hxy : x * y = y * x)
    (hcard : Nat.card (Subgroup.closure ({x, y} : Set Q)) = p ^ 2) :
    Function.Injective fun t : Fin p × Fin p => x ^ (t.1 : ℕ) * y ^ (t.2 : ℕ) := by
  have hxQ : x ∈ Subgroup.closure ({x, y} : Set Q) := Subgroup.subset_closure (by simp)
  have hyQ : y ∈ Subgroup.closure ({x, y} : Set Q) := Subgroup.subset_closure (by simp)
  let F : Fin p × Fin p → Subgroup.closure ({x, y} : Set Q) := fun t =>
    ⟨x ^ (t.1 : ℕ) * y ^ (t.2 : ℕ),
      Subgroup.mul_mem _ (Subgroup.pow_mem _ hxQ _) (Subgroup.pow_mem _ hyQ _)⟩
  have hz : ⁅x, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hxy
  have hsurj : Function.Surjective F := by
    intro g
    obtain ⟨i, j, k, hi, hj, -, hg⟩ := LocalWitness.mem_closure_normalForm hp.pos hx hy
      (by rw [hz]; exact Commute.one_left x) (by rw [hz]; exact Commute.one_left y) g.2
    rw [hz, one_pow, mul_one] at hg
    exact ⟨(⟨i, hi⟩, ⟨j, hj⟩), Subtype.ext hg.symm⟩
  have hc : Nat.card (Fin p × Fin p) ≤ Nat.card (Subgroup.closure ({x, y} : Set Q)) := by
    rw [hcard, Nat.card_prod, Nat.card_fin, sq]
  have hbij : Function.Bijective F := hsurj.bijective_of_nat_card_le hc
  intro s t hst
  exact hbij.1 (Subtype.ext hst)

theorem not_perm3_of_square_witness {p : ℕ} [Fact p.Prime] [Finite Q] {Ē : Subgroup Q}
    (hEcard : Nat.card Ē = p ^ 2) (hQ : ¬ p ^ 3 ∣ Nat.card Q) {x y h : Q} (hx : x ^ p = 1)
    (hy : y ^ p = 1) (hxy : x * y = y * x)
    (hcard : Nat.card (Subgroup.closure ({x, y} : Set Q)) = p ^ 2) {a b c d : ℕ}
    (hhx : h * x * h⁻¹ = x ^ a * y ^ b) (hhy : h * y * h⁻¹ = x ^ c * y ^ d)
    (hbad : (stPair a b c d 6).1 % p ≠ 1 ∨ (stPair a b c d 6).2 % p ≠ 0) :
    ¬ Nonempty (torusImage Ē ⊤ ≃* Equiv.Perm (Fin 3)) := by
  have hp : p.Prime := Fact.out
  have hxQ : x ∈ Subgroup.closure ({x, y} : Set Q) := Subgroup.subset_closure (by simp)
  have hyQ : y ∈ Subgroup.closure ({x, y} : Set Q) := Subgroup.subset_closure (by simp)
  have hx' : h * x * h⁻¹ ∈ Subgroup.closure ({x, y} : Set Q) := by
    rw [hhx]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hxQ _) (Subgroup.pow_mem _ hyQ _)
  have hy' : h * y * h⁻¹ ∈ Subgroup.closure ({x, y} : Set Q) := by
    rw [hhy]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hxQ _) (Subgroup.pow_mem _ hyQ _)
  have hnorm : h ∈ Subgroup.normalizer (Subgroup.closure ({x, y} : Set Q) : Set Q) :=
    mem_normalizer_of_conj_le (conj_closure_le hx' hy')
  refine not_perm3_of_witness hEcard hQ hcard hnorm ?_
  intro heq
  rw [conj_iter hxy hhx hhy 6, pow_eq_pow_mod _ hx, pow_eq_pow_mod _ hy] at heq
  have hinj := injective_of_card_sq hp hx hy hxy hcard
  have h2 := hp.two_le
  have key : (⟨(stPair a b c d 6).1 % p, Nat.mod_lt _ hp.pos⟩, ⟨(stPair a b c d 6).2 % p,
      Nat.mod_lt _ hp.pos⟩) = ((⟨1, by omega⟩ : Fin p), (⟨0, hp.pos⟩ : Fin p)) := by
    apply hinj
    simp only
    rw [heq]
    simp
  rw [Prod.mk.injEq, Fin.mk.injEq, Fin.mk.injEq] at key
  rcases hbad with h1 | h1
  · exact h1 key.1
  · exact h1 key.2

theorem not_perm3_of_square_witness_equiv {G : Type} [Group G] (e : Q ≃* G) {p : ℕ}
    [Fact p.Prime] [Finite Q] {Ē : Subgroup Q} (hEcard : Nat.card Ē = p ^ 2)
    (hQ : ¬ p ^ 3 ∣ Nat.card G) {x y h : G} (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hxy : x * y = y * x) (hcard : Nat.card (Subgroup.closure ({x, y} : Set G)) = p ^ 2)
    {a b c d : ℕ} (hhx : h * x * h⁻¹ = x ^ a * y ^ b) (hhy : h * y * h⁻¹ = x ^ c * y ^ d)
    (hbad : (stPair a b c d 6).1 % p ≠ 1 ∨ (stPair a b c d 6).2 % p ≠ 0) :
    ¬ Nonempty (torusImage Ē ⊤ ≃* Equiv.Perm (Fin 3)) := by
  have hQ' : ¬ p ^ 3 ∣ Nat.card Q := by
    rwa [Nat.card_congr e.toEquiv]
  have hclos : Subgroup.closure ({e.symm x, e.symm y} : Set Q) =
      (Subgroup.closure ({x, y} : Set G)).map e.symm.toMonoidHom := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  have hcard' : Nat.card (Subgroup.closure ({e.symm x, e.symm y} : Set Q)) = p ^ 2 := by
    rw [hclos, Subgroup.card_map_of_injective e.symm.injective, hcard]
  refine not_perm3_of_square_witness hEcard hQ' (x := e.symm x) (y := e.symm y) (h := e.symm h)
    ?_ ?_ ?_ hcard' (a := a) (b := b) (c := c) (d := d) ?_ ?_ hbad
  · rw [← map_pow, hx, map_one]
  · rw [← map_pow, hy, map_one]
  · rw [← map_mul, ← map_mul, hxy]
  · rw [← map_mul, ← map_inv, ← map_mul, hhx, map_mul, map_pow, map_pow]
  · rw [← map_mul, ← map_inv, ← map_mul, hhy, map_mul, map_pow, map_pow]

end CFSG.RankThree.PartOne.Q1327S
