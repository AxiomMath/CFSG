
module

public import CFSG.Monster.B.Fischer.Fi22GraphBase
public import CFSG.Monster.B.Fischer.Fi22CentralizerBase
public import CFSG.Certificates.NativeRefine
public import Certificates.Data.CFSGNative.FischerOddCore.Checks

@[expose] public noncomputable section

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.FischerOddCore CFSG.Sporadic.FischerOddCore.Native

theorem fi22P_eq_closure_gens :
    fi22P = Subgroup.closure {g | ∃ k < fi22OrigArrs.size, fi22GenPerm k = g} := by
  rw [fi22P_eq, fi22OrigArrs_size]
  congr 1
  ext g
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, k.2, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩

theorem fi22P_exists_smul
    (x y : Fin 3510) : ∃ g ∈ fi22P, g x = y := by
  have := fi22P_transitive
  obtain ⟨⟨g, hg⟩, h⟩ := MulAction.exists_smul_eq fi22P x y
  exact ⟨g, hg, h⟩

@[expose] def fi22GraphBasePt (s : ℕ) : Fin 3510 := fi22Pt (fi22GraphBase.getD s 0)

@[expose] def fi22GraphStab (s : ℕ) : Subgroup (fi22Graph ≃g fi22Graph) :=
  stabChain fi22GraphBasePt s

theorem mem_fi22GraphStab {s : ℕ} {σ : fi22Graph ≃g fi22Graph} :
    σ ∈ fi22GraphStab s ↔ ∀ j < s, σ (fi22GraphBasePt j) = fi22GraphBasePt j := by
  rw [fi22GraphStab, mem_stabChain]
  rfl

theorem fi22GraphBase_take {s : ℕ} {v : Fin 3510} (hv : (v : ℕ) ∈ fi22GraphBase.take s) :
    ∃ j < s, fi22GraphBasePt j = v := by
  obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hv
  simp only [List.length_take] at hj
  refine ⟨j, by omega, ?_⟩
  rw [fi22GraphBasePt, List.getD_eq_getElem _ _ (by omega), ← List.getElem_take (j := s)]
  · rw [hjv]
    exact Fin.ext (Nat.mod_eq_of_lt v.2)
  · omega

theorem fi22GraphBase_lt {v : ℕ} (hv : v ∈ fi22GraphBase) : v < 3510 := by
  simp only [fi22GraphBase, List.mem_cons, List.not_mem_nil, or_false] at hv
  omega

theorem fi22GraphBasePt_val {s : ℕ} (hs : s < 7) :
    ((fi22GraphBasePt s : Fin 3510) : ℕ) = fi22GraphBase.getD s 0 := by
  rw [fi22GraphBasePt]
  apply Nat.mod_eq_of_lt
  interval_cases s <;> decide

instance : Finite (fi22Graph ≃g fi22Graph) :=
  Finite.of_injective (fun σ : fi22Graph ≃g fi22Graph => σ.toEquiv) fun _ _ h =>
    RelIso.ext fun x => congrArg (fun e : Equiv.Perm (Fin 3510) => e x) h

end CFSG.Monster.B.Fischer
