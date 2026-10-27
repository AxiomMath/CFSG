module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeAct

public section

namespace CFSG.StandardType.TwE6SplitRootGen

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def twE6SplitWbar : WeylGroup Tag.F4 :=
  simple Tag.F4 ⟨1, by decide⟩ * simple Tag.F4 ⟨2, by decide⟩

private def matSimple (i : Fin Tag.F4.rank) : Fin Tag.F4.rank → Fin Tag.F4.rank → ℤ :=
  fun r c => (if r = c then 1 else 0) - Tag.F4.cartan i c * (if r = i then 1 else 0)

private def matStep (i : Fin Tag.F4.rank) (M : Fin Tag.F4.rank → Fin Tag.F4.rank → ℤ) :
    Fin Tag.F4.rank → Fin Tag.F4.rank → ℤ :=
  fun r c => M r c - (if r = i then 1 else 0) * ∑ k, Tag.F4.cartan i k * M k c

private def matConj (b : Fin Tag.F4.rank) :
    Fin Tag.F4.rank → Fin Tag.F4.rank → ℤ :=
  matStep ⟨1, by decide⟩ (matStep ⟨2, by decide⟩ (matStep b
    (matStep ⟨2, by decide⟩ (matSimple ⟨1, by decide⟩))))

private theorem torusAct_simple_eq {p : ℕ} [NeZero p] (i : Fin Tag.F4.rank)
    (x : Fin Tag.F4.rank → ZMod p) :
    TableBExc.torusAct .F4 p (simple Tag.F4 i) x =
      x - (∑ j, ((Tag.F4.cartan i j : ℤ) : ZMod p) * x j) • Pi.single i 1 := by
  funext k
  simp only [TableBExc.torusAct, simple_smul, reflect, TableBExc.redMod, TableBExc.liftMod,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  simp only [ZMod.natCast_zmod_val, ZMod.cast_id', id_eq]
  congr 2
  by_cases h : k = i
  · subst h; simp
  · simp [Pi.single_apply, h]

private theorem torusAct_simple_single {p : ℕ} [NeZero p] (i c : Fin Tag.F4.rank) :
    TableBExc.torusAct .F4 p (simple Tag.F4 i) (Pi.single c 1) =
      fun r => ((matSimple i r c : ℤ) : ZMod p) := by
  rw [torusAct_simple_eq]
  have hsum : (∑ j, ((Tag.F4.cartan i j : ℤ) : ZMod p) *
      (Pi.single c 1 : Fin Tag.F4.rank → ZMod p) j) = ((Tag.F4.cartan i c : ℤ) : ZMod p) := by
    rw [Finset.sum_eq_single c]
    · simp
    · intro j _ hj
      simp [Pi.single_apply, hj]
    · simp
  rw [hsum]
  funext r
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, matSimple]
  split_ifs <;> push_cast <;> ring

private theorem torusAct_simple_apply {p : ℕ} [NeZero p] (i c d : Fin Tag.F4.rank) :
    TableBExc.torusAct .F4 p (simple Tag.F4 i) (Pi.single c 1) d =
      ((matSimple i d c : ℤ) : ZMod p) :=
  congrFun (torusAct_simple_single i c) d

private theorem torusAct_simple_step {p : ℕ} [NeZero p] (i : Fin Tag.F4.rank)
    (M : Fin Tag.F4.rank → Fin Tag.F4.rank → ℤ) (c : Fin Tag.F4.rank) :
    TableBExc.torusAct .F4 p (simple Tag.F4 i) (fun r => ((M r c : ℤ) : ZMod p)) =
      fun r => ((matStep i M r c : ℤ) : ZMod p) := by
  rw [torusAct_simple_eq]
  funext r
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, matStep]
  split_ifs <;> push_cast <;> ring

private theorem torusAct_conj_single {p : ℕ} [NeZero p] (b c : Fin Tag.F4.rank) :
    TableBExc.torusAct .F4 p (twE6SplitWbar * simple Tag.F4 b * twE6SplitWbar⁻¹)
        (Pi.single c 1) =
      fun r => ((matConj b r c : ℤ) : ZMod p) := by
  rw [twE6SplitWbar, mul_inv_rev, simple_inv, simple_inv]
  simp only [TableBExc.torusAct_mul]
  rw [torusAct_simple_single, torusAct_simple_step, torusAct_simple_step,
    torusAct_simple_step, torusAct_simple_step]
  rfl

private theorem torusAct_conj_apply {p : ℕ} [NeZero p] (b c d : Fin Tag.F4.rank) :
    TableBExc.torusAct .F4 p (twE6SplitWbar * simple Tag.F4 b * twE6SplitWbar⁻¹)
        (Pi.single c 1) d = ((matConj b d c : ℤ) : ZMod p) :=
  congrFun (torusAct_conj_single b c) d

private theorem intCast_ne_of_odd {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {m₁ m₂ : ℤ}
    (h : m₁ - m₂ = 1 ∨ m₁ - m₂ = -1 ∨ m₁ - m₂ = 2 ∨ m₁ - m₂ = -2) :
    ((m₁ : ℤ) : ZMod p) ≠ ((m₂ : ℤ) : ZMod p) := by
  have hp : p.Prime := Fact.out
  have h1 : (1 : ZMod p) ≠ 0 := by
    intro h1
    have h' : ((1 : ℕ) : ZMod p) = 0 := by simpa using h1
    exact hp.ne_one (Nat.dvd_one.mp ((ZMod.natCast_eq_zero_iff 1 p).mp h'))
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h2
    have h' : ((2 : ℕ) : ZMod p) = 0 := by simpa using h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 p).mp h'))
  intro he
  have hzero : ((m₁ - m₂ : ℤ) : ZMod p) = 0 := by
    push_cast
    exact sub_eq_zero.mpr he
  rcases h with h | h | h | h
  · rw [h] at hzero
    exact h1 (by simpa using hzero)
  · rw [h] at hzero
    exact h1 (by simpa using hzero)
  · rw [h] at hzero
    exact h2 (by simpa using hzero)
  · rw [h] at hzero
    exact h2 (by simpa using hzero)

private theorem exists_witness_simple (a b : Fin Tag.F4.rank) :
    a = b ∨ ∃ c d : Fin Tag.F4.rank,
      matSimple a d c - matSimple b d c = 1 ∨ matSimple a d c - matSimple b d c = -1 ∨
        matSimple a d c - matSimple b d c = 2 ∨ matSimple a d c - matSimple b d c = -2 := by
  fin_cases a <;> fin_cases b <;> decide

private theorem exists_witness_simple_conj (a b : Fin Tag.F4.rank) :
    ∃ c d : Fin Tag.F4.rank,
      matSimple a d c - matConj b d c = 1 ∨ matSimple a d c - matConj b d c = -1 ∨
        matSimple a d c - matConj b d c = 2 ∨ matSimple a d c - matConj b d c = -2 := by
  fin_cases a <;> fin_cases b <;> decide

theorem torusAct_simple_ne_F4 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {a b : Fin Tag.F4.rank}
    (hab : a ≠ b) :
    TableBExc.torusAct .F4 p (simple Tag.F4 a) ≠ TableBExc.torusAct .F4 p (simple Tag.F4 b) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rcases exists_witness_simple a b with h | ⟨c, d, hd⟩
  · exact absurd h hab
  · intro heq
    refine intCast_ne_of_odd hp2 hd ?_
    rw [← torusAct_simple_apply (i := a) (c := c) (d := d),
      ← torusAct_simple_apply (i := b) (c := c) (d := d)]
    exact congrFun (congrFun heq (Pi.single c 1)) d

theorem torusAct_simple_ne_conj_F4 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (a b : Fin Tag.F4.rank) :
    TableBExc.torusAct .F4 p (simple Tag.F4 a) ≠
      TableBExc.torusAct .F4 p (twE6SplitWbar * simple Tag.F4 b * twE6SplitWbar⁻¹) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨c, d, hd⟩ := exists_witness_simple_conj a b
  intro heq
  refine intCast_ne_of_odd hp2 hd ?_
  rw [← torusAct_simple_apply (i := a) (c := c) (d := d),
    ← torusAct_conj_apply (b := b) (c := c) (d := d)]
  exact congrFun (congrFun heq (Pi.single c 1)) d

end CFSG.StandardType.TwE6SplitRootGen

end
