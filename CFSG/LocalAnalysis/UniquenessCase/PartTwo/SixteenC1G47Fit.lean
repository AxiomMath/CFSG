module

public import CFSG.GroupTheory.Fitting.CoprimeAutomorphisms
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup
open scoped commutatorElement

theorem s16c1_G47_fit {Hs : Type} [Group Hs] [Finite Hs] {N : Subgroup Hs} (hN : N.Normal)
    (hodd : Odd (Nat.card N)) {u : Hs} (hu2 : u * u = 1) (hu : ∃ n ∈ N, u * n * u⁻¹ ≠ n) :
    ∃ (q : ℕ) (P : Subgroup Hs), q.Prime ∧ P ≤ N ∧ P.Normal ∧ IsPGroup q P ∧
      ∃ n ∈ P, u * n * u⁻¹ ≠ n := by
  classical
  haveI : N.Normal := hN
  by_contra hcon
  push Not at hcon
  have hsolv : Group.IsSolvable ↥N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hpow : (MulAut.conjNormal u : MulAut ↥N) ^ 2 = 1 := by
    rw [pow_two, ← map_mul, hu2, map_one]
  have hfixed : ∀ x ∈ CFSG.fittingSubgroup ↥N,
      (MulAut.conjNormal u : MulAut ↥N) x = x := by
    intro x hx
    have hle : CFSG.fittingSubgroup ↥N ≤
        (MulAut.conjNormal u : MulAut ↥N).toMonoidHom.eqLocus (MonoidHom.id ↥N) := by
      rw [CFSG.fitting_eq_sup_pCore]
      refine iSup_le fun p => ?_
      intro y hy
      have hp : (p.1.1 : ℕ).Prime := Nat.prime_of_mem_primeFactors p.1.2
      let P : Subgroup Hs := (CFSG.pCore p.1.1 ↥N).map N.subtype
      have hPle : P ≤ N := Subgroup.map_subtype_le _
      have hPnorm : P.Normal := by
        dsimp [P]
        infer_instance
      have hPp : IsPGroup p.1.1 P := by
        dsimp [P]
        exact IsPGroup.map (CFSG.pCore_isPGroup (p := p.1.1) (G := ↥N)) N.subtype
      have hmemP : (y : Hs) ∈ P := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
      have hcon' := hcon p.1.1 P hp hPle hPnorm hPp (y : Hs) hmemP
      apply Subtype.ext
      change u * (y : Hs) * u⁻¹ = (y : Hs)
      exact hcon'
    exact hle hx
  have hcop : Nat.Coprime 2 (Nat.card (CFSG.fittingSubgroup ↥N)) := by
    have hdvd : Nat.card (CFSG.fittingSubgroup ↥N) ∣ Nat.card ↥N :=
      Subgroup.card_subgroup_dvd_card _
    exact (Nat.coprime_two_left.mpr hodd).coprime_dvd_right hdvd
  have hφ : (MulAut.conjNormal u : MulAut ↥N) = 1 :=
    CFSG.mulAut_eq_one_of_fixes_fittingSubgroup ↥N hsolv (MulAut.conjNormal u) 2 hpow hcop
      hfixed
  rcases hu with ⟨n, hn, hnu⟩
  apply hnu
  have h1 := congrArg (fun f : MulAut ↥N => (f ⟨n, hn⟩ : ↥N)) hφ
  have h2 := congrArg (Subtype.val) h1
  simpa [MulAut.conjNormal_apply] using h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
