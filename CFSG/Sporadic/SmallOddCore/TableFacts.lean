module

public import CFSG.Monster.B.Co2.PermArr
public import CFSG.Sporadic.Th.TableSpec

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

theorem rep_arrayMap_ofNat {n : ℕ} (hn : n < 2 ^ 32) {a : Array ℕ} {g : Equiv.Perm (Fin n)}
    (h : CFSG.Monster.B.Co2.Rep n a g) : Th.Rep n (a.map UInt32.ofNat) g := by
  intro i hi
  have h1 := h ⟨i, hi⟩
  rw [idx_of_lt _ hi]
  unfold ap
  by_cases hs : i < a.size
  · rw [getElem!_pos (a.map UInt32.ofNat) i (by simpa using hs), Array.getElem_map,
      UInt32.toNat_ofNat', ← getElem!_pos a i hs, h1, Nat.mod_eq_of_lt ((g _).isLt.trans hn)]
    rfl
  · rw [getElem!_neg (a.map UInt32.ofNat) i (by simpa using hs)]
    rw [getElem!_neg a i hs] at h1
    rw [show (g • (⟨i, hi⟩ : Fin n) : Fin n) = g ⟨i, hi⟩ from rfl, ← h1]
    rfl

theorem eq_of_prime_dvd_prod {q : ℕ} (hq : q.Prime) :
    ∀ fs : List (ℕ × ℕ), (∀ f ∈ fs, f.1.Prime) → q ∣ (fs.map fun f => f.1 ^ f.2).prod →
      ∃ f ∈ fs, q = f.1
  | [], _, h => absurd (Nat.eq_one_of_dvd_one (by simpa using h)) hq.ne_one
  | f :: fs, hp, h => by
    rw [List.map_cons, List.prod_cons] at h
    rcases hq.dvd_mul.mp h with h | h
    · exact ⟨f, List.mem_cons_self,
        (Nat.prime_dvd_prime_iff_eq hq (hp f List.mem_cons_self)).mp (hq.dvd_of_dvd_pow h)⟩
    · obtain ⟨g, hg, rfl⟩ :=
        eq_of_prime_dvd_prod hq fs (fun g hg => hp g (List.mem_cons_of_mem _ hg)) h
      exact ⟨g, List.mem_cons_of_mem _ hg, rfl⟩

theorem factorization_two_pow_mul {k m : ℕ} (hm : ¬ 2 ∣ m) : (2 ^ k * m).factorization 2 = k := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero 2)
  rw [Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

end CFSG.Sporadic.SmallOddCore
