module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Local3Sound
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Local3Cover
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness CFSG.Blueprint
  CFSG.CosetTable CFSG.Sporadic.Recognition.CoverRecipe CFSG.AGLEmbedding

theorem factorization_three_pow_mul (k b : Nat) (hb : ¬ 3 ∣ b) (hb0 : b ≠ 0) :
    (3 ^ k * b).factorization 3 = k := by
  rw [Nat.factorization_mul (by positivity) hb0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hb, add_zero]

theorem factorization_three_le {N n k b c : Nat} (hN : N = 3 ^ k * b) (hn : n = 3 ^ k * c)
    (hb : ¬ 3 ∣ b) (hb0 : b ≠ 0) (hc : ¬ 3 ∣ c) (hc0 : c ≠ 0) :
    N.factorization 3 ≤ n.factorization 3 := by
  rw [hN, hn, factorization_three_pow_mul k b hb hb0, factorization_three_pow_mul k c hc hc0]

theorem key2_eq (d : Nat) {u w : Nat} (h : (spec2 d).toVec u = (spec2 d).toVec w) :
    u % 2 ^ d = w % 2 ^ d := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hj : j < d
  · have := congrFun h ⟨j, hj⟩
    simp only [spec2, CFSG.Sporadic.SmallF2.toVecD_apply] at this
    cases hu : u.testBit j <;> cases hw : w.testBit j <;> simp_all
  · simp [hj]

theorem kernelTrivialAt_three_of_local3Check (d : Nat) {m : Nat} (D : Local3Data m) (root : Nat)
    (h : local3Check (ops2 d) (fun v => v % 2 ^ d) D root = true) {k cap : Nat}
    (henum : subsetCheckShortCC
      (cover₃Words D.rels (fun i => [(i, true)]) (fun i => D.ords.getD i 0)) [] k cap D.n = true)
    (hsyl : (Nat.card (NativeSporadic.seedMonoid 2 d 1 D.seedA D.seedB)ˣ).factorization 3 ≤
      D.n.factorization 3) :
    KernelTrivialAt (NativeSporadic.seedMonoid 2 d 1 D.seedA D.seedB)ˣ 3 := by
  obtain ⟨x, hR, hpow, hord, hn⟩ := exists_local3_of_check (spec2 d) D (key := fun v => v % 2 ^ d)
    (root := root) trivial (fun u w hu => key2_eq d hu) h
  have : Finite (NativeSporadic.seedMonoid 2 d 1 D.seedA D.seedB)ˣ :=
    Finite.of_injective (valHom _) (valHom_injective _)
  exact kernelTrivialAt_three_of_local x hR hpow
    (fun i => ⟨(hord i).1, (hord i).2⟩) henum hn hsyl

theorem kernelTrivialAt_three_of_local3Check_card (d : Nat) {m : Nat} (D : Local3Data m)
    (root : Nat) (h : local3Check (ops2 d) (fun v => v % 2 ^ d) D root = true)
    (hPG : Finite (PG m (cover₃Words D.rels (fun i => [(i, true)]) (fun i => D.ords.getD i 0))) ∧
      Nat.card (PG m (cover₃Words D.rels (fun i => [(i, true)]) (fun i => D.ords.getD i 0))) ≤ D.n)
    (hsyl : (Nat.card (NativeSporadic.seedMonoid 2 d 1 D.seedA D.seedB)ˣ).factorization 3 ≤
      D.n.factorization 3) :
    KernelTrivialAt (NativeSporadic.seedMonoid 2 d 1 D.seedA D.seedB)ˣ 3 := by
  obtain ⟨x, hR, hpow, hord, hn⟩ := exists_local3_of_check (spec2 d) D (key := fun v => v % 2 ^ d)
    (root := root) trivial (fun u w hu => key2_eq d hu) h
  have : Finite (NativeSporadic.seedMonoid 2 d 1 D.seedA D.seedB)ˣ :=
    Finite.of_injective (valHom _) (valHom_injective _)
  exact kernelTrivialAt_three_of_local_card x hR hpow
    (fun i => ⟨(hord i).1, (hord i).2⟩) hPG hn hsyl

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
