module

public import CFSG.LocalAnalysis.StandardType.GGL45NtLattice
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313In
public import CFSG.RankThree.PartOne.KE.E7A2NativeModule

public section

namespace CFSG.HardMathSupport.C14Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.E6
open CFSG.HardMathSupport.Lang.E6Descent.DiagWeyl
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313InAux
open CFSG.LieType.Chevalley.C2E6Std
open CFSG.RankThree.PartOne.KE

private structure Lat3SDataE6 where
  k : Fin Tag.E6.rank
  t : Fin 3 → ℤ
  c : Fin Tag.E6.rank → ℤ
  d : Fin Tag.E6.rank → ℤ

private inductive Lat3CertE6 where
  | root (k : Fin 72) (c d : Fin Tag.E6.rank → ℤ)
  | sym (s : Fin 3 → Fin Tag.E6.rank) (data : List Lat3SDataE6)

private def lat3MemS6 (s : Fin 3 → Fin Tag.E6.rank) (k : Fin Tag.E6.rank) : Bool :=
  (List.finRange 3).any fun a => decide (k = s a)

private def Lat3CertOKE6 (M : List (List ℤ)) : Lat3CertE6 → Prop
  | .root k c d =>
      e6Root k = (toMat Tag.E6.rank M).mulVec c - c + 3 • d
  | .sym s data =>
      ∀ k : Fin Tag.E6.rank, lat3MemS6 s k = false →
        ∃ e ∈ data, e.k = k ∧
          (Pi.single k 1 : Fin Tag.E6.rank → ℤ) =
            (toMat Tag.E6.rank M).mulVec e.c - e.c +
              ∑ a : Fin 3, e.t a • (Pi.single (s a) 1 : Fin Tag.E6.rank → ℤ) + 3 • e.d

private def Lat3CertOKE6b (M : List (List ℤ)) : Lat3CertE6 → Bool
  | .root k c d =>
      decide (e6Root k = (toMat Tag.E6.rank M).mulVec c - c + 3 • d)
  | .sym s data =>
      ((List.finRange Tag.E6.rank).filter fun k => !lat3MemS6 s k).all fun k =>
        data.any fun e =>
          (e.k == k) && decide ((Pi.single k 1 : Fin Tag.E6.rank → ℤ) =
            (toMat Tag.E6.rank M).mulVec e.c - e.c +
              ∑ a : Fin 3, e.t a • (Pi.single (s a) 1 : Fin Tag.E6.rank → ℤ) + 3 • e.d)

private theorem Lat3CertOKE6b_eq_true_iff (M : List (List ℤ)) (cert : Lat3CertE6) :
    Lat3CertOKE6b M cert = true ↔ Lat3CertOKE6 M cert := by
  cases cert with
  | root k c d => simp [Lat3CertOKE6b, Lat3CertOKE6]
  | sym s data =>
      simp only [Lat3CertOKE6b, Lat3CertOKE6]
      rw [List.all_eq_true]
      constructor
      · intro h k hk
        have hk' : k ∈ List.filter (fun k => !lat3MemS6 s k) (List.finRange Tag.E6.rank) := by
          rw [List.mem_filter]
          exact ⟨List.mem_finRange k, by simpa using hk⟩
        have := h k hk'
        rw [List.any_eq_true] at this
        obtain ⟨e, he, hb⟩ := this
        rw [Bool.and_eq_true] at hb
        exact ⟨e, he, (beq_iff_eq.mp hb.1), by simpa using hb.2⟩
      · intro h k hk
        rw [List.mem_filter] at hk
        have hk' : lat3MemS6 s k = false := by simpa using hk.2
        obtain ⟨e, he, hke, hcert⟩ := h k hk'
        rw [List.any_eq_true]
        exact ⟨e, he, by rw [Bool.and_eq_true]; exact ⟨beq_iff_eq.mpr hke, by simpa using hcert⟩⟩

private def Lat3OrderThreeE6 (ω : List Bool) : Bool :=
  decide (∀ i j : Fin Tag.E6.rank,
    lget (lmul Tag.E6.rank (lmul Tag.E6.rank (dEval ω) (dEval ω)) (dEval ω)) i j =
      lget (lid Tag.E6.rank) i j)

private def Lat3NonidentityE6 (ω : List Bool) : Bool :=
  decide (∃ i j : Fin Tag.E6.rank, lget (dEval ω) i j ≠ lget (lid Tag.E6.rank) i j)

private def Lat3TableE6 : List (List Bool × Lat3CertE6) := [
  ([false], .sym ![0, 1, 3]
    [⟨2, ![0, 1, 0], ![0, 0, 2, 0, 0, 0], ![0, -1, 1, 0, 0, 0]⟩,
     ⟨4, ![2, 2, 0], ![0, 0, 1, 0, 2, 0], ![0, -1, 1, 0, 1, 0]⟩,
     ⟨5, ![0, 1, 0], ![0, 0, 2, 0, 0, 2], ![0, -1, 0, 0, 0, 1]⟩]),
  ([true], .root 36 ![0, 0, 0, 0, 2, 1] ![0, 0, 0, -1, 0, 0]),
  ([false, false], .sym ![0, 1, 3]
    [⟨2, ![0, 1, 0], ![0, 0, 2, 0, 0, 2], ![0, -1, 1, 0, 0, 0]⟩,
     ⟨4, ![2, 2, 0], ![0, 0, 2, 0, 1, 0], ![-1, -1, 0, -1, 0, -1]⟩,
     ⟨5, ![0, 1, 0], ![0, 0, 0, 0, 0, 2], ![0, -1, 0, 0, 0, 1]⟩]),
  ([true, true], .root 36 ![0, 0, 0, 0, 0, 1] ![0, 0, 0, 0, 0, 0]),
  ([false, false, true, false], .root 71 ![0, 1, 0, 0, 0, 0] ![0, 0, 0, 0, 0, 0]),
  ([false, true, false, false], .root 38 ![0, 0, 2, 0, 0, 2] ![-1, 0, -1, -1, -1, 0]),
  ([true, false, true, true], .sym ![0, 1, 4]
    [⟨2, ![0, 1, 0], ![0, 0, 2, 2, 2, 0], ![0, -1, 1, 0, 0, 0]⟩,
     ⟨3, ![2, 0, 0], ![0, 0, 0, 2, 0, 0], ![0, 0, 0, 1, 0, 0]⟩,
     ⟨5, ![1, 2, 1], ![0, 0, 1, 2, 0, 0], ![0, -1, 0, 0, -1, 0]⟩]),
  ([true, true, false, true], .sym ![0, 1, 3]
    [⟨2, ![0, 1, 0], ![0, 0, 2, 2, 0, 0], ![0, -1, 1, 0, 0, 0]⟩,
     ⟨4, ![0, 2, 1], ![0, 0, 1, 0, 0, 0], ![0, -1, 0, -1, 0, 0]⟩,
     ⟨5, ![1, 1, 1], ![0, 0, 2, 2, 0, 2], ![-1, -1, 0, -1, 0, 1]⟩]),
  ([false, false, true, false, true], .sym ![0, 1, 2]
    [⟨3, ![1, 1, 2], ![0, 1, 0, 0, 2, 0], ![0, 1, 0, 1, 1, 0]⟩,
     ⟨4, ![0, 2, 0], ![0, 0, 0, 0, 2, 0], ![0, 0, 0, 0, 1, 0]⟩,
     ⟨5, ![1, 2, 2], ![0, 1, 0, 0, 2, 2], ![0, 0, 0, 0, 1, 1]⟩]),
  ([false, false, true, true, false], .root 71 ![0, 1, 0, 0, 0, 1] ![0, 0, 0, 0, 0, 0]),
  ([false, true, false, false, true], .sym ![0, 1, 2]
    [⟨3, ![1, 0, 0], ![0, 0, 2, 0, 2, 2], ![-1, 0, 0, -1, 0, 0]⟩,
     ⟨4, ![0, 0, 2], ![0, 0, 0, 0, 2, 0], ![0, 0, 0, 0, 1, 0]⟩,
     ⟨5, ![1, 0, 1], ![0, 0, 2, 0, 2, 1], ![-1, 0, 0, -1, 0, 0]⟩]),
  ([false, true, false, true, false], .sym ![0, 1, 3]
    [⟨2, ![2, 1, 0], ![0, 0, 1, 0, 0, 1], ![-1, -1, 0, -1, -1, 0]⟩,
     ⟨4, ![2, 2, 2], ![0, 0, 1, 0, 0, 0], ![-1, -1, 0, -1, 0, 0]⟩,
     ⟨5, ![1, 1, 2], ![0, 2, 1, 0, 0, 2], ![0, 0, 0, -1, -1, 1]⟩]),
  ([false, true, false, true, true], .sym ![0, 1, 2]
    [⟨3, ![2, 2, 1], ![0, 0, 0, 1, 1, 1], ![-1, -1, -1, 0, 0, 0]⟩,
     ⟨4, ![2, 0, 2], ![0, 0, 0, 1, 2, 1], ![-1, 0, -1, 0, 1, 0]⟩,
     ⟨5, ![0, 0, 1], ![0, 0, 0, 0, 0, 2], ![0, 0, -1, 0, 0, 1]⟩]),
  ([false, true, true, false, false], .root 38 ![0, 0, 0, 0, 0, 2] ![-1, 0, -1, -1, -1, 0]),
  ([false, true, true, false, true], .sym ![0, 1, 2]
    [⟨3, ![2, 1, 2], ![0, 0, 0, 1, 2, 0], ![0, 0, 0, 1, 1, 0]⟩,
     ⟨4, ![2, 0, 2], ![0, 0, 0, 0, 2, 0], ![0, 0, 0, 0, 1, 0]⟩,
     ⟨5, ![0, 0, 1], ![0, 0, 0, 2, 0, 1], ![0, 1, 0, 2, 1, 1]⟩]),
  ([true, false, false, true, true], .sym ![0, 1, 4]
    [⟨2, ![0, 1, 0], ![0, 0, 2, 2, 0, 0], ![0, -1, 1, 0, 0, 0]⟩,
     ⟨3, ![2, 0, 0], ![0, 0, 2, 0, 1, 0], ![0, 1, 2, 2, 2, 1]⟩,
     ⟨5, ![1, 2, 1], ![0, 0, 1, 0, 1, 0], ![0, 0, 1, 1, 1, 1]⟩]),
  ([true, false, true, false, true], .sym ![0, 1, 2]
    [⟨3, ![2, 0, 0], ![0, 0, 0, 1, 1, 2], ![0, 1, 1, 2, 1, 1]⟩,
     ⟨4, ![2, 2, 0], ![0, 0, 0, 0, 1, 2], ![0, 0, 1, 1, 1, 1]⟩,
     ⟨5, ![0, 2, 2], ![0, 0, 0, 2, 2, 0], ![0, 0, 0, 2, 2, 1]⟩]),
  ([true, false, true, true, false], .sym ![0, 1, 2]
    [⟨3, ![2, 0, 0], ![0, 0, 0, 0, 2, 1], ![-1, -1, -1, -1, 0, 0]⟩,
     ⟨4, ![2, 1, 1], ![0, 0, 0, 0, 1, 1], ![-1, -1, -1, -1, 0, 0]⟩,
     ⟨5, ![0, 1, 0], ![0, 0, 0, 2, 2, 2], ![0, -1, 0, 0, 0, 1]⟩]),
  ([true, true, false, false, true], .sym ![0, 1, 3]
    [⟨2, ![0, 1, 0], ![0, 0, 2, 0, 0, 0], ![0, -1, 1, 0, 0, 0]⟩,
     ⟨4, ![0, 2, 1], ![0, 0, 0, 2, 0, 0], ![0, 0, 0, 1, 1, 0]⟩,
     ⟨5, ![1, 1, 1], ![0, 0, 1, 1, 0, 1], ![0, 0, 1, 1, 1, 1]⟩]),
  ([true, true, false, true, false], .sym ![0, 1, 2]
    [⟨3, ![2, 1, 2], ![0, 0, 0, 1, 2, 1], ![-1, -1, -1, 0, 0, 0]⟩,
     ⟨4, ![2, 1, 1], ![0, 0, 0, 0, 1, 1], ![-1, -1, -1, -1, 0, 0]⟩,
     ⟨5, ![0, 1, 0], ![0, 0, 0, 2, 2, 2], ![0, -1, 0, 0, 0, 1]⟩]),
  ([false, false, true, false, true, true], .sym ![0, 1, 2]
    [⟨3, ![2, 2, 1], ![0, 2, 0, 0, 1, 0], ![0, 1, 1, 2, 2, 1]⟩,
     ⟨4, ![2, 1, 1], ![0, 2, 0, 0, 2, 2], ![0, 1, 1, 2, 3, 2]⟩,
     ⟨5, ![0, 1, 0], ![0, 0, 0, 0, 0, 2], ![0, -1, 0, 0, 0, 1]⟩]),
  ([false, false, true, true, false, true], .sym ![0, 1, 2]
    [⟨3, ![2, 2, 1], ![0, 0, 0, 0, 2, 1], ![-1, -1, -1, -1, 0, 0]⟩,
     ⟨4, ![2, 1, 1], ![0, 2, 0, 0, 1, 0], ![-1, 0, -1, -1, 0, -1]⟩,
     ⟨5, ![0, 1, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]⟩]),
  ([false, true, false, false, true, true], .sym ![0, 1, 2]
    [⟨3, ![2, 0, 0], ![0, 0, 1, 0, 0, 0], ![-1, 0, 0, 0, 0, 0]⟩,
     ⟨4, ![2, 0, 2], ![0, 0, 1, 0, 1, 2], ![-1, 0, -1, 0, 1, 1]⟩,
     ⟨5, ![0, 0, 1], ![0, 0, 0, 0, 0, 2], ![0, 0, -1, 0, 0, 1]⟩]),
  ([false, true, false, true, false, true], .sym ![0, 1, 2]
    [⟨3, ![2, 1, 2], ![0, 0, 1, 0, 0, 1], ![-1, -1, -1, -1, -1, 0]⟩,
     ⟨4, ![2, 2, 0], ![0, 0, 1, 0, 1, 1], ![-1, -1, 0, -1, 0, 0]⟩,
     ⟨5, ![0, 2, 2], ![0, 0, 0, 0, 1, 2], ![0, -1, -1, -1, 0, 1]⟩]),
  ([false, true, false, true, true, false], .sym ![0, 1, 3]
    [⟨2, ![0, 1, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]⟩,
     ⟨4, ![1, 2, 2], ![0, 2, 2, 0, 0, 1], ![0, 1, 1, 1, 1, 1]⟩,
     ⟨5, ![2, 1, 2], ![0, 2, 0, 0, 0, 2], ![0, 1, 0, 0, 0, 1]⟩]),
  ([false, true, true, false, false, true], .sym ![0, 1, 2]
    [⟨3, ![2, 0, 0], ![0, 0, 1, 0, 0, 1], ![-1, 0, 0, 0, 0, 0]⟩,
     ⟨4, ![2, 0, 2], ![0, 0, 0, 0, 2, 0], ![0, 0, 0, 0, 1, 0]⟩,
     ⟨5, ![0, 0, 1], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0]⟩]),
  ([false, true, true, false, true, false], .sym ![0, 1, 3]
    [⟨2, ![0, 1, 0], ![0, 0, 2, 0, 0, 0], ![0, -1, 1, 0, 0, 0]⟩,
     ⟨4, ![1, 2, 2], ![0, 0, 2, 0, 0, 2], ![-1, -2, 0, -2, -1, 0]⟩,
     ⟨5, ![2, 1, 2], ![0, 2, 2, 0, 0, 1], ![-1, 0, 1, 0, 0, 1]⟩]),
  ([false, false, true, false, false, true, true], .sym ![0, 1, 2]
    [⟨3, ![2, 0, 0], ![0, 0, 0, 2, 0, 0], ![0, 0, 0, 1, 0, 0]⟩,
     ⟨4, ![2, 1, 1], ![0, 0, 0, 2, 1, 0], ![0, 0, 0, 1, 1, 0]⟩,
     ⟨5, ![0, 1, 0], ![0, 0, 0, 0, 0, 2], ![0, -1, 0, 0, 0, 1]⟩]),
  ([false, false, true, false, true, false, true], .sym ![0, 1, 2]
    [⟨3, ![2, 2, 1], ![0, 0, 0, 2, 0, 1], ![-1, -1, 0, 1, 0, 0]⟩,
     ⟨4, ![2, 2, 0], ![0, 0, 0, 1, 0, 1], ![-1, -1, 0, 0, 0, 0]⟩,
     ⟨5, ![0, 2, 2], ![0, 0, 0, 2, 2, 0], ![0, 0, 0, 2, 2, 1]⟩]),
  ([false, false, true, false, true, true, false], .sym ![0, 1, 2]
    [⟨3, ![2, 1, 2], ![0, 0, 0, 2, 1, 0], ![-1, 0, -1, 1, 0, 0]⟩,
     ⟨4, ![2, 0, 2], ![0, 0, 0, 1, 0, 0], ![-1, 0, -1, 0, 0, 0]⟩,
     ⟨5, ![0, 0, 1], ![0, 0, 0, 2, 2, 2], ![0, 0, -1, 0, 0, 1]⟩]),
  ([false, false, true, true, false, false, true], .sym ![0, 1, 2]
    [⟨3, ![2, 1, 2], ![0, 0, 0, 2, 1, 2], ![-1, 0, 0, 2, 1, 1]⟩,
     ⟨4, ![2, 1, 1], ![0, 0, 0, 1, 1, 2], ![-1, 0, 0, 1, 1, 1]⟩,
     ⟨5, ![0, 1, 0], ![0, 0, 0, 2, 0, 1], ![0, 0, 1, 2, 1, 1]⟩]),
  ([false, false, true, true, false, true, false], .sym ![0, 1, 2]
    [⟨3, ![2, 2, 1], ![0, 0, 0, 1, 1, 0], ![-1, -1, -1, 0, 0, 0]⟩,
     ⟨4, ![2, 0, 2], ![0, 0, 0, 1, 0, 0], ![-1, 0, -1, 0, 0, 0]⟩,
     ⟨5, ![0, 0, 1], ![0, 0, 0, 2, 2, 2], ![0, 0, -1, 0, 0, 1]⟩]),
  ([false, false, true, true, false, true, true], .sym ![0, 1, 2]
    [⟨3, ![1, 1, 2], ![0, 0, 0, 0, 2, 0], ![-1, -1, -2, -1, 0, 0]⟩,
     ⟨4, ![0, 2, 0], ![0, 2, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0]⟩,
     ⟨5, ![1, 2, 2], ![0, 1, 0, 0, 0, 1], ![0, 0, 0, 1, 1, 1]⟩]),
  ([false, true, false, true, false, true, true], .sym ![0, 1, 2]
    [⟨3, ![1, 2, 1], ![0, 0, 2, 0, 2, 1], ![-1, -1, 0, 0, 1, 1]⟩,
     ⟨4, ![0, 1, 1], ![0, 0, 0, 0, 2, 1], ![0, 0, 0, 1, 2, 1]⟩,
     ⟨5, ![1, 1, 0], ![0, 0, 2, 0, 1, 1], ![-1, -1, 0, -1, 0, 1]⟩]),
  ([false, true, false, true, true, false, true], .sym ![0, 1, 2]
    [⟨3, ![0, 2, 1], ![0, 0, 2, 0, 0, 0], ![0, 0, 1, 1, 0, 0]⟩,
     ⟨4, ![1, 1, 1], ![0, 0, 0, 0, 1, 2], ![0, 0, 0, 0, 1, 1]⟩,
     ⟨5, ![2, 1, 0], ![0, 0, 2, 0, 1, 0], ![-1, 0, 1, 0, 0, 0]⟩]),
  ([false, true, true, false, false, true, true], .sym ![0, 1, 2]
    [⟨3, ![1, 0, 0], ![0, 0, 2, 0, 2, 1], ![0, 0, 1, 1, 2, 1]⟩,
     ⟨4, ![0, 0, 2], ![0, 0, 2, 0, 0, 0], ![0, 0, 0, 0, 1, 0]⟩,
     ⟨5, ![1, 0, 1], ![0, 0, 0, 0, 0, 2], ![-1, 0, -1, 0, 0, 1]⟩]),
  ([false, true, true, false, true, false, true], .sym ![0, 1, 2]
    [⟨3, ![0, 1, 2], ![0, 0, 2, 0, 2, 2], ![0, -1, 0, -1, 0, 0]⟩,
     ⟨4, ![1, 2, 0], ![0, 0, 2, 0, 0, 2], ![-1, -2, 0, -2, -1, 0]⟩,
     ⟨5, ![2, 2, 2], ![0, 0, 0, 0, 1, 2], ![-1, -1, -1, -1, 0, 1]⟩]),
  ([false, true, true, false, true, true, false], .sym ![0, 1, 3]
    [⟨2, ![2, 1, 0], ![0, 1, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0]⟩,
     ⟨4, ![2, 2, 2], ![0, 2, 1, 0, 0, 2], ![-1, 1, 1, 1, 1, 1]⟩,
     ⟨5, ![1, 1, 2], ![0, 2, 0, 0, 0, 2], ![-1, 1, 0, 0, 0, 1]⟩]),
  ([false, true, false, true, true, false, true, true], .sym ![0, 1, 2]
    [⟨3, ![0, 1, 2], ![0, 0, 1, 0, 1, 1], ![0, 0, 0, 1, 1, 1]⟩,
     ⟨4, ![1, 2, 0], ![0, 0, 1, 0, 0, 1], ![0, 0, 1, 1, 1, 1]⟩,
     ⟨5, ![2, 2, 2], ![0, 0, 0, 0, 2, 1], ![-1, -1, -1, 0, 1, 1]⟩]),
  ([false, true, true, false, true, false, true, true], .sym ![0, 1, 2]
    [⟨3, ![0, 2, 1], ![0, 0, 1, 0, 0, 0], ![0, -1, 0, 0, 0, 0]⟩,
     ⟨4, ![1, 1, 1], ![0, 0, 0, 0, 2, 1], ![0, 0, 0, 1, 2, 1]⟩,
     ⟨5, ![2, 1, 0], ![0, 0, 1, 0, 2, 0], ![0, 0, 1, 1, 2, 1]⟩]),
  ([false, true, true, false, true, true, false, true], .sym ![0, 1, 2]
    [⟨3, ![1, 2, 1], ![0, 0, 1, 0, 1, 2], ![0, 0, 1, 1, 1, 1]⟩,
     ⟨4, ![0, 1, 1], ![0, 0, 0, 0, 1, 2], ![0, 0, 0, 0, 1, 1]⟩,
     ⟨5, ![1, 1, 0], ![0, 0, 1, 0, 2, 2], ![0, 0, 1, 0, 1, 1]⟩]),
  ([true, true, false, true, true, false, true, true], .sym ![0, 1, 2]
    [⟨3, ![2, 2, 1], ![0, 0, 0, 1, 1, 1], ![-1, -1, -1, 0, 0, 0]⟩,
     ⟨4, ![2, 2, 0], ![0, 0, 0, 2, 0, 2], ![-2, -2, -2, -2, -1, 0]⟩,
     ⟨5, ![0, 2, 2], ![0, 0, 0, 1, 1, 0], ![0, -1, -1, 0, 0, 0]⟩]),
  ([false, true, true, false, true, true, false, true, true], .sym ![0, 1, 2]
    [⟨3, ![2, 1, 2], ![0, 0, 2, 0, 0, 2], ![0, 1, 2, 3, 2, 2]⟩,
     ⟨4, ![2, 2, 0], ![0, 0, 2, 0, 2, 2], ![0, 0, 2, 2, 3, 2]⟩,
     ⟨5, ![0, 2, 2], ![0, 0, 0, 0, 2, 1], ![0, -1, -1, 0, 1, 1]⟩]),
  ([false, false, true, true, false, true, true, false, true, true], .sym ![0, 1, 2]
    [⟨3, ![2, 0, 0], ![0, 0, 0, 2, 0, 0], ![0, 0, 0, 1, 0, 0]⟩,
     ⟨4, ![2, 2, 0], ![0, 0, 0, 0, 2, 1], ![-1, -1, 0, 0, 1, 0]⟩,
     ⟨5, ![0, 2, 2], ![0, 0, 0, 1, 1, 0], ![0, -1, -1, 0, 0, 0]⟩])
]

private def Lat3CheckWordE6 (ω : List Bool) : Bool :=
  bif (Lat3OrderThreeE6 ω && Lat3NonidentityE6 ω) then
    Lat3TableE6.any fun p => (p.1 == ω) && Lat3CertOKE6b (dEval ω) p.2
  else true

private def Lat3TableCheckE6 : Bool := dWords.all Lat3CheckWordE6

private theorem lat3Table_check_E6 : Lat3TableCheckE6 = true := by
  decide +kernel

private structure Lat3SDataE7 where
  k : Fin Tag.E7.rank
  t : Fin 3 → ℤ
  c : Fin Tag.E7.rank → ℤ
  d : Fin Tag.E7.rank → ℤ

private inductive Lat3CertE7 where
  | root (k : Fin 126) (c d : Fin Tag.E7.rank → ℤ)
  | sym (s : Fin 3 → Fin Tag.E7.rank) (data : List Lat3SDataE7)

private def lat3MemS7 (s : Fin 3 → Fin Tag.E7.rank) (k : Fin Tag.E7.rank) : Bool :=
  (List.finRange 3).any fun a => decide (k = s a)

private def Lat3CertOKE7 (M : List (List ℤ)) : Lat3CertE7 → Prop
  | .root k c d =>
      e7RootVec k = (toMat Tag.E7.rank M).mulVec c - c + 3 • d
  | .sym s data =>
      ∀ k : Fin Tag.E7.rank, lat3MemS7 s k = false →
        ∃ e ∈ data, e.k = k ∧
          (Pi.single k 1 : Fin Tag.E7.rank → ℤ) =
            (toMat Tag.E7.rank M).mulVec e.c - e.c +
              ∑ a : Fin 3, e.t a • (Pi.single (s a) 1 : Fin Tag.E7.rank → ℤ) + 3 • e.d

private def Lat3CertOKE7b (M : List (List ℤ)) : Lat3CertE7 → Bool
  | .root k c d =>
      decide (e7RootVec k = (toMat Tag.E7.rank M).mulVec c - c + 3 • d)
  | .sym s data =>
      ((List.finRange Tag.E7.rank).filter fun k => !lat3MemS7 s k).all fun k =>
        data.any fun e =>
          (e.k == k) && decide ((Pi.single k 1 : Fin Tag.E7.rank → ℤ) =
            (toMat Tag.E7.rank M).mulVec e.c - e.c +
              ∑ a : Fin 3, e.t a • (Pi.single (s a) 1 : Fin Tag.E7.rank → ℤ) + 3 • e.d)

private theorem Lat3CertOKE7b_eq_true_iff (M : List (List ℤ)) (cert : Lat3CertE7) :
    Lat3CertOKE7b M cert = true ↔ Lat3CertOKE7 M cert := by
  cases cert with
  | root k c d => simp [Lat3CertOKE7b, Lat3CertOKE7]
  | sym s data =>
      simp only [Lat3CertOKE7b, Lat3CertOKE7]
      rw [List.all_eq_true]
      constructor
      · intro h k hk
        have hk' : k ∈ List.filter (fun k => !lat3MemS7 s k) (List.finRange Tag.E7.rank) := by
          rw [List.mem_filter]
          exact ⟨List.mem_finRange k, by simpa using hk⟩
        have := h k hk'
        rw [List.any_eq_true] at this
        obtain ⟨e, he, hb⟩ := this
        rw [Bool.and_eq_true] at hb
        exact ⟨e, he, (beq_iff_eq.mp hb.1), by simpa using hb.2⟩
      · intro h k hk
        rw [List.mem_filter] at hk
        have hk' : lat3MemS7 s k = false := by simpa using hk.2
        obtain ⟨e, he, hke, hcert⟩ := h k hk'
        rw [List.any_eq_true]
        exact ⟨e, he, by rw [Bool.and_eq_true]; exact ⟨beq_iff_eq.mpr hke, by simpa using hcert⟩⟩

private def Lat3OrderThreeE7M (M : List (List ℤ)) : Bool :=
  (List.finRange Tag.E7.rank).all fun i =>
    (List.finRange Tag.E7.rank).all fun j =>
      lget (lmul Tag.E7.rank (lmul Tag.E7.rank M M) M) i j == lget (lid Tag.E7.rank) i j

private def Lat3NonidentityE7M (M : List (List ℤ)) : Bool :=
  (List.finRange Tag.E7.rank).any fun i =>
    (List.finRange Tag.E7.rank).any fun j =>
      !(lget M i j == lget (lid Tag.E7.rank) i j)

private def Lat3TableE7 : List (List Bool × Lat3CertE7) := [
  ([false], .root 77 ![0, 0, 0, 0, 0, 2, 2] ![-1, -1, -2, -2, -1, 0, 0]),
  ([true], .root 41 ![0, 0, 0, 0, 2, 0, 2] ![0, 0, 0, -1, -1, -1, 0]),
  ([false, false], .root 77 ![0, 0, 2, 0, 1, 1, 1] ![-1, -1, -1, -2, -1, -1, 0]),
  ([true, true], .root 41 ![0, 0, 0, 0, 0, 0, 2] ![0, 0, 0, -1, -1, -1, 0]),
  ([false, false, true, false], .root 107 ![0, 0, 0, 0, 0, 2, 2] ![-1, -2, -2, -3, -2, -1, 0]),
  ([false, true, false, false], .root 45 ![0, 0, 2, 0, 0, 2, 0] ![-1, 0, -1, -1, -1, 0, 0]),
  ([true, false, true, true], .root 94 ![0, 0, 0, 0, 0, 0, 2] ![-1, -1, -2, -2, -2, -1, 0]),
  ([true, true, false, true], .root 101 ![0, 0, 0, 0, 0, 2, 2] ![-1, -1, -2, -3, -2, -1, 0]),
  ([false, false, true, false, true],
    .root 107 ![0, 0, 0, 0, 0, 2, 2] ![-1, -2, -2, -3, -2, -1, 0]),
  ([false, false, true, true, false],
    .root 107 ![0, 0, 0, 0, 0, 0, 2] ![-1, -2, -2, -3, -2, -1, 0]),
  ([false, true, false, false, true], .root 45 ![0, 0, 2, 0, 1, 0, 1] ![-1, 0, 0, -1, -1, -1, 0]),
  ([false, true, false, true, false], .root 107 ![0, 2, 0, 0, 0, 1, 1] ![0, 0, -1, -1, -1, 0, 0]),
  ([false, true, false, true, true], .root 68 ![0, 0, 0, 2, 0, 1, 1] ![-1, -2, -2, -2, -2, -1, 0]),
  ([false, true, true, false, false], .root 45 ![0, 0, 0, 0, 0, 2, 0] ![-1, 0, -1, -1, -1, 0, 0]),
  ([false, true, true, false, true], .root 94 ![0, 0, 0, 0, 2, 0, 1] ![0, -1, -1, -2, -1, -1, 0]),
  ([true, false, false, true, true], .root 94 ![0, 0, 2, 0, 0, 0, 1] ![0, 0, 1, 0, 0, 0, 0]),
  ([true, false, true, false, true], .root 78 ![0, 0, 0, 1, 1, 2, 1] ![0, 0, 0, 0, 0, 0, 0]),
  ([true, false, true, true, false], .root 101 ![0, 0, 0, 2, 0, 1, 1] ![0, 0, 0, 0, -1, 0, 0]),
  ([true, true, false, false, true], .root 101 ![0, 0, 2, 2, 0, 0, 1] ![-1, -1, -1, -1, -1, -1, 0]),
  ([true, true, false, true, false], .root 44 ![0, 0, 0, 0, 2, 0, 1] ![-1, -1, -1, -1, 0, -1, 0]),
  ([false, false, true, false, true, true],
    .root 107 ![0, 0, 0, 0, 0, 2, 2] ![-1, -2, -2, -3, -2, -1, 0]),
  ([false, false, true, true, false, true],
    .root 107 ![0, 2, 0, 0, 1, 0, 1] ![-1, -1, -2, -3, -2, -2, 0]),
  ([false, true, false, false, true, true],
    .root 45 ![0, 0, 2, 0, 1, 0, 1] ![-1, 0, 0, -1, 0, 0, 0]),
  ([false, true, false, true, false, true], .sym ![0, 1, 6]
    [⟨2, ![0, 1, 0], ![0, 0, 2, 0, 2, 1, 1], ![-1, -1, 0, -2, -1, -1, 0]⟩,
     ⟨3, ![2, 0, 0], ![0, 0, 2, 0, 1, 0, 2], ![-2, -1, -1, -2, -2, -2, 0]⟩,
     ⟨4, ![2, 2, 0], ![0, 0, 1, 0, 1, 1, 0], ![-1, -1, 0, -1, 0, 0, 0]⟩,
     ⟨5, ![0, 1, 0], ![0, 0, 1, 0, 2, 1, 2], ![-1, -1, -1, -2, -1, -1, 0]⟩]),
  ([false, true, false, true, true, false],
    .root 107 ![0, 0, 0, 0, 0, 0, 2] ![-1, -2, -2, -3, -2, -1, 0]),
  ([false, true, true, false, false, true],
    .root 45 ![0, 0, 0, 0, 0, 2, 2] ![-1, 0, -1, -1, -1, 0, 0]),
  ([false, true, true, false, true, false],
    .root 107 ![0, 2, 0, 0, 0, 1, 1] ![-1, 0, -1, -1, -1, 0, 0]),
  ([false, false, true, false, false, true, true],
    .root 101 ![0, 0, 0, 0, 0, 0, 2] ![-1, -1, -2, -3, -2, -1, 0]),
  ([false, false, true, false, true, false, true],
    .root 77 ![0, 0, 0, 0, 2, 2, 2] ![-1, -1, -2, -2, -1, 0, 0]),
  ([false, false, true, false, true, true, false],
    .root 94 ![0, 0, 0, 2, 2, 2, 2] ![-1, -1, -2, -2, -2, -1, 0]),
  ([false, false, true, true, false, false, true],
    .root 44 ![0, 0, 0, 2, 2, 2, 2] ![-1, -1, -1, -1, 0, 0, 0]),
  ([false, false, true, true, false, true, false],
    .root 68 ![0, 0, 0, 0, 0, 0, 2] ![-1, -1, -1, -1, -1, -1, 0]),
  ([false, false, true, true, false, true, true],
    .root 107 ![0, 2, 0, 0, 1, 0, 1] ![-1, -1, -2, -3, -1, -1, 0]),
  ([false, true, false, true, false, true, true], .sym ![0, 1, 6]
    [⟨2, ![0, 1, 0], ![0, 0, 2, 0, 0, 2, 1], ![-1, -2, -1, -3, -2, 0, 0]⟩,
     ⟨3, ![1, 0, 0], ![0, 0, 1, 0, 2, 0, 1], ![-1, 0, 0, 0, 1, 0, 0]⟩,
     ⟨4, ![0, 2, 0], ![0, 0, 2, 0, 2, 0, 1], ![-1, -1, 0, -1, 1, 0, 0]⟩,
     ⟨5, ![1, 1, 0], ![0, 0, 2, 0, 1, 1, 0], ![-1, -1, 0, -1, 0, 1, 0]⟩]),
  ([false, true, false, true, true, false, true], .sym ![0, 1, 6]
    [⟨2, ![2, 1, 0], ![0, 0, 1, 0, 2, 0, 2], ![-2, -2, -1, -3, -2, -2, 0]⟩,
     ⟨3, ![2, 0, 0], ![0, 0, 0, 0, 2, 0, 2], ![-2, -2, -2, -3, -2, -2, 0]⟩,
     ⟨4, ![0, 2, 0], ![0, 0, 1, 0, 0, 2, 2], ![0, -1, 0, -1, -1, 0, 0]⟩,
     ⟨5, ![2, 1, 0], ![0, 0, 2, 0, 1, 0, 0], ![-1, 0, 1, 0, 0, 0, 0]⟩]),
  ([false, true, true, false, false, true, true],
    .root 45 ![0, 0, 0, 0, 0, 2, 2] ![-1, 0, -1, -1, -1, 0, 0]),
  ([false, true, true, false, true, false, true], .sym ![0, 1, 6]
    [⟨2, ![2, 1, 0], ![0, 0, 1, 0, 0, 0, 1], ![-1, -1, 0, -1, -1, -1, 0]⟩,
     ⟨3, ![1, 0, 0], ![0, 0, 1, 0, 2, 2, 2], ![-1, -1, -1, -2, -1, -1, 0]⟩,
     ⟨4, ![1, 2, 0], ![0, 0, 2, 0, 0, 2, 0], ![-1, -2, 0, -2, -1, 0, 0]⟩,
     ⟨5, ![0, 1, 0], ![0, 0, 2, 0, 1, 2, 2], ![-1, -2, -1, -3, -2, -1, 0]⟩]),
  ([false, true, true, false, true, true, false],
    .root 107 ![0, 0, 0, 0, 0, 0, 2] ![-1, -2, -2, -3, -2, -1, 0]),
  ([false, true, false, true, true, false, true, true], .sym ![0, 1, 6]
    [⟨2, ![2, 1, 0], ![0, 0, 1, 0, 2, 0, 2], ![-2, -2, -1, -3, -1, -1, 0]⟩,
     ⟨3, ![1, 0, 0], ![0, 0, 0, 0, 2, 1, 1], ![-1, -1, -1, -1, 0, 0, 0]⟩,
     ⟨4, ![1, 2, 0], ![0, 0, 1, 0, 0, 1, 0], ![0, 0, 1, 1, 1, 1, 0]⟩,
     ⟨5, ![0, 1, 0], ![0, 0, 2, 0, 0, 1, 1], ![0, 0, 1, 0, 0, 1, 0]⟩]),
  ([false, true, true, false, true, false, true, true], .sym ![0, 1, 6]
    [⟨2, ![2, 1, 0], ![0, 0, 1, 0, 1, 1, 1], ![-1, -1, 0, -1, 0, 0, 0]⟩,
     ⟨3, ![2, 0, 0], ![0, 0, 2, 0, 1, 1, 1], ![-1, -1, 0, -1, 0, 0, 0]⟩,
     ⟨4, ![0, 2, 0], ![0, 0, 1, 0, 0, 2, 1], ![-1, -2, -1, -2, -1, 0, 0]⟩,
     ⟨5, ![2, 1, 0], ![0, 0, 1, 0, 2, 0, 0], ![0, 0, 1, 1, 2, 1, 0]⟩]),
  ([false, true, true, false, true, true, false, true], .sym ![0, 1, 6]
    [⟨2, ![0, 1, 0], ![0, 0, 2, 0, 1, 1, 2], ![0, -1, 1, -1, -1, -1, 0]⟩,
     ⟨3, ![1, 0, 0], ![0, 0, 0, 0, 2, 0, 2], ![-1, -2, -2, -3, -2, -2, 0]⟩,
     ⟨4, ![0, 2, 0], ![0, 0, 2, 0, 2, 0, 2], ![0, -2, 0, -2, -1, -2, 0]⟩,
     ⟨5, ![1, 1, 0], ![0, 0, 1, 0, 2, 2, 0], ![0, 0, 1, 0, 1, 1, 0]⟩]),
  ([true, true, false, true, true, false, true, true],
    .root 77 ![0, 0, 0, 1, 1, 2, 1] ![-1, -1, -2, -2, -1, 0, 0]),
  ([false, true, true, false, true, true, false, true, true], .sym ![0, 1, 6]
    [⟨2, ![0, 1, 0], ![0, 0, 2, 0, 1, 1, 2], ![0, -1, 1, -1, 0, 0, 0]⟩,
     ⟨3, ![2, 0, 0], ![0, 0, 0, 0, 2, 1, 1], ![-1, -1, -1, -1, 0, 0, 0]⟩,
     ⟨4, ![2, 2, 0], ![0, 0, 2, 0, 2, 2, 0], ![0, 0, 2, 2, 3, 2, 0]⟩,
     ⟨5, ![0, 1, 0], ![0, 0, 1, 0, 1, 0, 1], ![0, -1, 0, -1, 0, 0, 0]⟩]),
  ([false, false, true, true, false, true, true, false, true, true],
    .root 78 ![0, 0, 0, 0, 2, 2, 2] ![-1, -1, -1, -2, -1, -1, 0])
]

private def Lat3CheckWordE7 (ω : List Bool) : Bool :=
  bif (Lat3OrderThreeE7M (dEval7 ω) && Lat3NonidentityE7M (dEval7 ω)) then
    Lat3TableE7.any fun p => (p.1 == ω) && Lat3CertOKE7b (dEval7 ω) p.2
  else true

private def Lat3TableCheckE7 : Bool := dWords.all Lat3CheckWordE7

private theorem lat3Table_check_E7 : Lat3TableCheckE7 = true := by
  decide +kernel

private theorem lat3MemS6_eq_false_iff (s : Fin 3 → Fin Tag.E6.rank) (k : Fin Tag.E6.rank) :
    lat3MemS6 s k = false ↔ k ∉ Finset.univ.image s := by
  rw [lat3MemS6, List.any_eq_false]
  simp [Finset.mem_image, decide_eq_true_iff, List.mem_finRange, eq_comm]

private theorem lat3OrderThree_of_weylMatrix_eq (g : WeylGroup Tag.E6) (M : List (List ℤ))
    (hM : weylMatrix g = toMat Tag.E6.rank M) (hg3 : g ^ 3 = 1) :
    ∀ i j : Fin Tag.E6.rank,
      lget (lmul Tag.E6.rank (lmul Tag.E6.rank M M) M) i j = lget (lid Tag.E6.rank) i j := by
  intro i j
  have h : toMat Tag.E6.rank (lmul Tag.E6.rank (lmul Tag.E6.rank M M) M) =
      toMat Tag.E6.rank (lid Tag.E6.rank) := by
    calc toMat Tag.E6.rank (lmul Tag.E6.rank (lmul Tag.E6.rank M M) M)
        = (toMat Tag.E6.rank M) ^ 3 := by
          rw [toMat_lmul, toMat_lmul, pow_succ, pow_two]
      _ = (weylMatrix g) ^ 3 := by rw [hM]
      _ = weylMatrix (g ^ 3) := by rw [weylMatrix_pow]
      _ = 1 := by rw [hg3, weylMatrix_one]
      _ = toMat Tag.E6.rank (lid Tag.E6.rank) := by simpa using (toMat_lid Tag.E6.rank).symm
  exact congrFun (congrFun h i) j

private theorem lat3Nonidentity_of_weylMatrix_eq (g : WeylGroup Tag.E6) (M : List (List ℤ))
    (hM : weylMatrix g = toMat Tag.E6.rank M) (hgne : g ≠ 1) :
    ∃ i j : Fin Tag.E6.rank, lget M i j ≠ lget (lid Tag.E6.rank) i j := by
  by_contra h
  apply hgne
  apply CFSG.RankThree.E6.weylMatrix_injective
  rw [hM, weylMatrix_one, ← toMat_lid Tag.E6.rank]
  ext i j
  by_contra hij
  exact h ⟨i, j, hij⟩

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem rootChar_sum_smul {τ : Tag} {K : Type} [Field K] (a : Fin τ.rank → Kˣ)
    {ι : Type*} (s : Finset ι) (c : ι → ℤ) (y : ι → Fin τ.rank → ℤ) :
    rootChar a (∑ i ∈ s, c i • y i) = ∏ i ∈ s, rootChar a (y i) ^ c i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rootChar_zero]
  | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.prod_insert hj, rootChar_add, rootChar_zsmul, ih]

private theorem pow_three_eq_one_of_mem_closure {τ : Tag} {K : Type} [Field K] {ι : Type}
    {a : ι → Fin τ.rank → Kˣ} (ha : ∀ i j, a i j ^ 3 = 1)
    {e : Fin τ.rank → Kˣ} (he : e ∈ Subgroup.closure (Set.range a)) (j : Fin τ.rank) :
    e j ^ 3 = 1 := by
  classical
  induction he using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ha i j
  | one => simp [rootChar]
  | mul x y hx hy ihx ihy =>
      rw [Pi.mul_apply, mul_pow, ihx, ihy, one_mul]
  | inv x hx ih =>
      rw [Pi.inv_apply, inv_pow, ih]
      simp

private theorem rootChar_smul_eq_of_mem_closure {τ : Tag} {K : Type} [Field K] {ι : Type}
    {a : ι → Fin τ.rank → Kˣ} {w : WeylGroup τ}
    (hw : w ∈ familyStabilizerSubgroup a)
    {e : Fin τ.rank → Kˣ} (he : e ∈ Subgroup.closure (Set.range a))
    (v : Fin τ.rank → ℤ) :
    rootChar e (w • v) = rootChar e v := by
  classical
  induction he using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact (Subgroup.mem_iInf.1 hw) i v
  | one => simp [rootChar]
  | mul x y hx hy ihx ihy =>
      rw [CFSG.LieType.Chevalley.rootChar_mul_tuple,
          CFSG.LieType.Chevalley.rootChar_mul_tuple, ihx, ihy]
  | inv x hx ih =>
      rw [rootChar_inv_apply, rootChar_inv_apply, ih]

private theorem sum_smul_smul_single {τ : Tag} (v : WeylGroup τ)
    (x : Fin τ.rank → ℤ) :
    x = ∑ k : Fin τ.rank, (v⁻¹ • x) k • (v • (Pi.single k 1 : Fin τ.rank → ℤ)) := by
  ext i
  rw [Finset.sum_apply]
  rw [show x i = (v • (v⁻¹ • x)) i by simp]
  rw [← congrFun (weylMatrix_mulVec v (v⁻¹ • x)) i]
  simp [Matrix.mulVec, dotProduct, weylMatrix_apply, mul_comm, mul_left_comm, mul_assoc]

private theorem eq_of_rootChar_eq_on_three_relation
    {τ : Tag} {K : Type} [Field K] {ι : Type}
    {a : ι → Fin τ.rank → Kˣ} (ha : ∀ i j, a i j ^ 3 = 1)
    {w : WeylGroup τ} (hw : w ∈ familyStabilizerSubgroup a)
    {v : WeylGroup τ} (s : Fin 3 → Fin τ.rank)
    (hrel : ∀ k : Fin τ.rank, k ∉ Finset.univ.image s →
        ∃ (c d : Fin τ.rank → ℤ) (t : Fin 3 → ℤ),
          v • (Pi.single k 1 : Fin τ.rank → ℤ) =
            w • c - c + ∑ a : Fin 3, t a • (v • (Pi.single (s a) 1 : Fin τ.rank → ℤ)) + (3 : ℤ) • d)
    {e e' : Fin τ.rank → Kˣ}
    (he : e ∈ Subgroup.closure (Set.range a))
    (he' : e' ∈ Subgroup.closure (Set.range a))
    (hS : ∀ i : Fin 3,
        rootChar e (v • (Pi.single (s i) 1 : Fin τ.rank → ℤ)) =
          rootChar e' (v • (Pi.single (s i) 1 : Fin τ.rank → ℤ))) :
    e = e' := by
  classical
  have hcube : ∀ j, e j ^ 3 = 1 := fun j => pow_three_eq_one_of_mem_closure ha he j
  have hcube' : ∀ j, e' j ^ 3 = 1 := fun j => pow_three_eq_one_of_mem_closure ha he' j
  have hwinv : ∀ x, rootChar e (w • x) = rootChar e x :=
    fun x => rootChar_smul_eq_of_mem_closure hw he x
  have hwinv' : ∀ x, rootChar e' (w • x) = rootChar e' x :=
    fun x => rootChar_smul_eq_of_mem_closure hw he' x
  have hk_eq : ∀ k, rootChar e (v • (Pi.single k 1 : Fin τ.rank → ℤ)) =
      rootChar e' (v • (Pi.single k 1 : Fin τ.rank → ℤ)) := by
    intro k
    by_cases hk : k ∈ Finset.univ.image s
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hk
      exact hS i
    · obtain ⟨c, d, t, hrelk⟩ := hrel k hk
      have ht_e : rootChar e (v • (Pi.single k 1 : Fin τ.rank → ℤ)) =
          ∏ a : Fin 3, (rootChar e (v • (Pi.single (s a) 1 : Fin τ.rank → ℤ))) ^ t a := by
        rw [hrelk, rootChar_add, rootChar_add, rootChar_sub, rootChar_sum_smul,
          rootChar_zsmul, hwinv]
        have hd3 : rootChar e d ^ 3 = 1 :=
          CFSG.RankThree.Chevalley.rootChar_pow_eq_one hcube d
        simp [hd3]
      have ht_e' : rootChar e' (v • (Pi.single k 1 : Fin τ.rank → ℤ)) =
          ∏ a : Fin 3, (rootChar e' (v • (Pi.single (s a) 1 : Fin τ.rank → ℤ))) ^ t a := by
        rw [hrelk, rootChar_add, rootChar_add, rootChar_sub, rootChar_sum_smul,
          rootChar_zsmul, hwinv']
        have hd3 : rootChar e' d ^ 3 = 1 :=
          CFSG.RankThree.Chevalley.rootChar_pow_eq_one hcube' d
        simp [hd3]
      rw [ht_e, ht_e']
      exact Finset.prod_congr rfl fun a _ => by rw [hS a]
  have hxj : ∀ j : Fin τ.rank, rootChar e ((Pi.single j 1 : Fin τ.rank → ℤ)) =
      rootChar e' ((Pi.single j 1 : Fin τ.rank → ℤ)) := by
    intro j
    rw [sum_smul_smul_single v ((Pi.single j 1 : Fin τ.rank → ℤ)),
        rootChar_sum_smul, rootChar_sum_smul]
    exact Finset.prod_congr rfl fun k _ => by rw [hk_eq k]
  funext j
  have h := hxj j
  rw [show rootChar e (Pi.single j 1 : Fin τ.rank → ℤ) = e j from by
        simpa using rootChar_nsmul_single e j 1,
      show rootChar e' (Pi.single j 1 : Fin τ.rank → ℤ) = e' j from by
        simpa using rootChar_nsmul_single e' j 1] at h
  exact h

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem nat_card_fun_rootsOfUnity_three_le {K : Type} [Field K] {α : Type*}
    (S : Finset α) (hS : S.card ≤ 3) :
    Nat.card (S → rootsOfUnity 3 K) ≤ 3 ^ 3 := by
  calc Nat.card (S → rootsOfUnity 3 K)
      = Nat.card (rootsOfUnity 3 K) ^ Nat.card S := Nat.card_fun
    _ = Nat.card (rootsOfUnity 3 K) ^ S.card := by rw [show Nat.card S = S.card by simp]
    _ ≤ 3 ^ S.card := Nat.pow_le_pow_left (card_rootsOfUnity K 3) S.card
    _ ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hS

private theorem nat_card_closure_le_cube_of_three_relations
    {τ : Tag} {K : Type} [Field K] {ι : Type}
    {a : ι → Fin τ.rank → Kˣ} (ha : ∀ i j, a i j ^ 3 = 1)
    {w : WeylGroup τ} (hw : w ∈ familyStabilizerSubgroup a)
    {v : WeylGroup τ} (s : Fin 3 → Fin τ.rank)
    (hrel : ∀ k : Fin τ.rank, k ∉ Finset.univ.image s →
        ∃ (c d : Fin τ.rank → ℤ) (t : Fin 3 → ℤ),
          v • (Pi.single k 1 : Fin τ.rank → ℤ) =
            w • c - c + ∑ a : Fin 3, t a • (v • (Pi.single (s a) 1 : Fin τ.rank → ℤ)) +
              3 • d) :
    Nat.card (Subgroup.closure (Set.range a)) ≤ 3 ^ 3 := by
  classical
  set E := Subgroup.closure (Set.range a)
  set S : Finset (Fin τ.rank → ℤ) :=
    Finset.univ.image (fun a => v • (Pi.single (s a) 1 : Fin τ.rank → ℤ))
  have hS_card : S.card ≤ 3 := by
    calc S.card ≤ (Finset.univ : Finset (Fin 3)).card := Finset.card_image_le
      _ = 3 := by simp
  let φ : E → (S → rootsOfUnity 3 K) := fun e s =>
    ⟨rootChar (e : Fin τ.rank → Kˣ) (s : Fin τ.rank → ℤ), by
      rw [mem_rootsOfUnity]
      exact CFSG.RankThree.Chevalley.rootChar_pow_eq_one
        (fun j => pow_three_eq_one_of_mem_closure ha e.2 j) _⟩
  have hinj : Function.Injective φ := by
    intro e e' hφ
    apply Subtype.ext
    refine eq_of_rootChar_eq_on_three_relation ha hw s hrel e.2 e'.2 ?_
    intro i
    have hmem : v • (Pi.single (s i) 1 : Fin τ.rank → ℤ) ∈ S :=
      Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩
    have h := congrFun hφ ⟨v • (Pi.single (s i) 1 : Fin τ.rank → ℤ), hmem⟩
    exact congrArg Subtype.val h
  have hcard : Nat.card E ≤ Nat.card (S → rootsOfUnity 3 K) :=
    Nat.card_le_card_of_injective φ hinj
  exact hcard.trans (nat_card_fun_rootsOfUnity_three_le S hS_card)

private theorem smul_transport {τ : Tag} {ι : Type} (v g u : WeylGroup τ) (hgu : u = v * g * v⁻¹)
    (x c d : Fin τ.rank → ℤ) (S : Finset ι) (t : ι → ℤ) (y : ι → Fin τ.rank → ℤ)
    (h : x = g • c - c + ∑ i ∈ S, t i • y i + 3 • d) :
    v • x = u • (v • c) - (v • c) +
      ∑ i ∈ S, t i • (v • (y i)) + 3 • (v • d) := by
  let f : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ) :=
    { toFun := fun x => v • x
      map_zero' := smul_zero v
      map_add' := fun x y => smul_add v x y }
  have hf : ∀ x, f x = v • x := fun x => rfl
  have h1 : f x = f (g • c) - f c + ∑ i ∈ S, t i • f (y i) + 3 • f d := by
    rw [h]
    simp only [map_add, map_sub, map_nsmul, map_sum, map_zsmul]
  have h2 : f (g • c) = u • (v • c) := by
    rw [hf, ← mul_smul]
    rw [show v * g = u * v by rw [hgu]; group]
    rw [mul_smul]
  change f x = u • (v • c) - (v • c) +
    ∑ i ∈ S, t i • (v • (y i)) + 3 • (v • d)
  rw [h1, h2]
  simp only [hf]

private theorem familyReflectionGroup_eq_bot_of_familyKernel_eq_empty
    {τ : Tag} {K : Type} [Field K] {ι : Type}
    {a : ι → Fin τ.rank → Kˣ} (hΦ : familyKernel a = ∅) :
    familyReflectionGroup a = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro w hw
  have hmem : canonicalRep (coxeterSystem τ) K w ∈ familyGroup (K := K) a :=
    canonicalRep_mem_familyGroup hw
  have htor : familyGroup (K := K) a = torusGroup τ K := by
    rw [familyGroup, hΦ]
    simp [rootSpan]
  rw [htor] at hmem
  have h1 : MapsRootLines (canonicalRep (coxeterSystem τ) K w) 1 :=
    mapsRootLines_of_mem_torusGroup hmem
  have h2 : MapsRootLines (canonicalRep (coxeterSystem τ) K w) w :=
    mapsRootLines_canonicalRep w
  have hw1 : w = 1 := MapsRootLines.unique h2 h1
  rw [hw1]
  exact Subgroup.one_mem ⊥

private theorem lat3Table_mem_E6 {ω : List Bool} (hω : ω ∈ dWords)
    (h3 : Lat3OrderThreeE6 ω = true) (hne : Lat3NonidentityE6 ω = true) :
    ∃ cert, (ω, cert) ∈ Lat3TableE6 ∧ Lat3CertOKE6 (dEval ω) cert := by
  have hcheck := List.all_eq_true.mp lat3Table_check_E6 ω hω
  simp only [Lat3CheckWordE6, h3, hne, Bool.true_and, cond_true] at hcheck
  rw [List.any_eq_true] at hcheck
  obtain ⟨p, hp, hb⟩ := hcheck
  rw [Bool.and_eq_true] at hb
  exact ⟨p.2, by rw [← beq_iff_eq.mp hb.1]; exact hp,
    (Lat3CertOKE6b_eq_true_iff _ _).mp hb.2⟩

private theorem mem_familyKernel_of_eq_smul_sub_add_three
    {τ : Tag} {K : Type} [Field K] {ι : Type}
    {a : ι → Fin τ.rank → Kˣ} (ha : ∀ i j, a i j ^ 3 = 1)
    {w : WeylGroup τ} (hw : w ∈ familyStabilizerSubgroup a)
    {β c d : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (h : β = w • c - c + 3 • d) :
    β ∈ familyKernel a := by
  refine ⟨hβ, fun i => ?_⟩
  have hi : w ∈ rootCharStabilizerSubgroup (a i) := (Subgroup.mem_iInf.1 hw) i
  have hwc : rootChar (a i) (w • c) = rootChar (a i) c := hi c
  have hd3 : rootChar (a i) d ^ 3 = 1 :=
    CFSG.RankThree.Chevalley.rootChar_pow_eq_one (ha i) d
  rw [h, rootChar_add, rootChar_sub, ← natCast_zsmul, rootChar_zsmul, hwc]
  simp [hd3]

private def Lat3RelE6 (v u : WeylGroup Tag.E6) (s : Fin 3 → Fin Tag.E6.rank)
    (k : Fin Tag.E6.rank) : Prop :=
  ∃ (c d : Fin Tag.E6.rank → ℤ) (t : Fin 3 → ℤ),
    v • (Pi.single k 1 : Fin Tag.E6.rank → ℤ) =
      u • c - c +
        ∑ a : Fin 3, t a • (v • (Pi.single (s a) 1 : Fin Tag.E6.rank → ℤ)) + 3 • d

private theorem smul_transport_root {τ : Tag} (v g u : WeylGroup τ) (hgu : u = v * g * v⁻¹)
    (β c d : Fin τ.rank → ℤ) (h : β = g • c - c + 3 • d) :
    v • β = u • (v • c) - (v • c) + 3 • (v • d) := by
  let f : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ) :=
    { toFun := fun x => v • x
      map_zero' := smul_zero v
      map_add' := fun x y => smul_add v x y }
  have hf : ∀ x, f x = v • x := fun x => rfl
  have h1 : f β = f (g • c) - f c + 3 • f d := by
    rw [h]
    simp only [map_add, map_sub, map_nsmul]
  have h2 : f (g • c) = u • (v • c) := by
    rw [hf, ← mul_smul]
    rw [show v * g = u * v by rw [hgu]; group]
    rw [mul_smul]
  change f β = u • (v • c) - (v • c) + 3 • (v • d)
  rw [h1, h2]
  simp only [hf]

private theorem Lat3CertOKE6_sym_rel {M : List (List ℤ)} {s : Fin 3 → Fin Tag.E6.rank}
    {data : List Lat3SDataE6} (hcert : Lat3CertOKE6 M (.sym s data))
    {k : Fin Tag.E6.rank} (hk : lat3MemS6 s k = false) :
    ∃ e ∈ data, e.k = k ∧
      (Pi.single k 1 : Fin Tag.E6.rank → ℤ) =
        (toMat Tag.E6.rank M).mulVec e.c - e.c +
          ∑ a : Fin 3, e.t a • (Pi.single (s a) 1 : Fin Tag.E6.rank → ℤ) + 3 • e.d :=
  hcert k hk

private theorem exists_orderThree_of_ne_bot
    {τ : Tag} {K : Type} [Field K] {ι : Type} [Finite ι]
    {a : ι → Fin τ.rank → Kˣ} (ha : ∀ i j, a i j ^ 3 = 1) (hΦ : familyKernel a = ∅)
    (hne : familyStabilizerSubgroup a ≠ ⊥) :
    ∃ u : familyStabilizerSubgroup a, orderOf u = 3 := by
  classical
  haveI : Finite (WeylGroup τ) := (exceptional_Lang_Weyl_chamber_point_stabilizers τ).2.1
  have hgrp : familyReflectionGroup a = ⊥ :=
    familyReflectionGroup_eq_bot_of_familyKernel_eq_empty hΦ
  have hcop_one : ∀ {w : WeylGroup τ}, w ∈ familyStabilizerSubgroup a →
      Nat.Coprime (orderOf w) 3 → w = 1 := by
    intro w hw hcop
    have hw' : w ∈ familyReflectionGroup a :=
      mem_familyReflectionGroup_of_coprime (p := 3) Nat.prime_three ha hw hcop
    rwa [hgrp] at hw'
  obtain ⟨w, hwne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have h3ord : 3 ∣ orderOf (w : WeylGroup τ) := by
    by_contra h3
    have hcop : Nat.Coprime (orderOf (w : WeylGroup τ)) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm
    have h1 : (w : WeylGroup τ) = 1 := hcop_one w.2 hcop
    exact hwne (Subtype.ext h1)
  have h3dvd : 3 ∣ Nat.card (familyStabilizerSubgroup a) :=
    dvd_trans h3ord (Subgroup.orderOf_dvd_natCard (familyStabilizerSubgroup a) w.2)
  obtain ⟨u, huord⟩ := exists_prime_orderOf_dvd_card' (G := familyStabilizerSubgroup a) 3 h3dvd
  exact ⟨u, huord⟩

private theorem e6_root_cert_false
    {K : Type} [Field K] {ι : Type}
    {a : ι → Fin Tag.E6.rank → Kˣ} (ha : ∀ i j, a i j ^ 3 = 1) (hΦ : familyKernel a = ∅)
    {u v g : WeylGroup Tag.E6} (hu : u ∈ familyStabilizerSubgroup a)
    (hgu : u = v * g * v⁻¹)
    {M : List (List ℤ)} (hM : weylMatrix g = toMat Tag.E6.rank M)
    {k : Fin 72} {c d : Fin Tag.E6.rank → ℤ}
    (hcert : e6Root k = (toMat Tag.E6.rank M).mulVec c - c + 3 • d) : False := by
  have hroot : IsRoot Tag.E6 (e6Root k) := isRoot_e6Root k
  have hrelg : e6Root k = g • c - c + 3 • d := by
    rw [hcert, ← hM, CFSG.RankThree.E6.weylMatrix_mulVec]
  have hβroot : IsRoot Tag.E6 (v • e6Root k) := IsRoot.smul hroot v
  have hβmem : v • e6Root k ∈ familyKernel a := by
    apply mem_familyKernel_of_eq_smul_sub_add_three ha hu hβroot
    exact smul_transport_root v g u hgu (e6Root k) c d hrelg
  rw [hΦ] at hβmem
  exact hβmem

private theorem e6_sym_cert_false
    {K : Type} [Field K] {ι : Type}
    {a : ι → Fin Tag.E6.rank → Kˣ} (ha : ∀ i j, a i j ^ 3 = 1)
    (hE : 3 ^ 4 ≤ Nat.card (Subgroup.closure (Set.range a)))
    {u v g : WeylGroup Tag.E6} (hu : u ∈ familyStabilizerSubgroup a)
    (hgu : u = v * g * v⁻¹)
    {M : List (List ℤ)} (hM : weylMatrix g = toMat Tag.E6.rank M)
    {s : Fin 3 → Fin Tag.E6.rank} {data : List Lat3SDataE6}
    (hcert : Lat3CertOKE6 M (.sym s data)) : False := by
  have hrel : ∀ k : Fin Tag.E6.rank, k ∉ Finset.univ.image s →
      Lat3RelE6 v u s k := by
    intro k hk
    have hk' : lat3MemS6 s k = false := (lat3MemS6_eq_false_iff s k).2 hk
    obtain ⟨e, he, hke, hrelk⟩ := Lat3CertOKE6_sym_rel hcert hk'
    refine ⟨v • e.c, v • e.d, e.t, ?_⟩
    have hrelk' : (Pi.single k 1 : Fin Tag.E6.rank → ℤ) =
        g • e.c - e.c +
          ∑ a : Fin 3, e.t a • (Pi.single (s a) 1 : Fin Tag.E6.rank → ℤ) + 3 • e.d := by
      rw [← hM, CFSG.RankThree.E6.weylMatrix_mulVec] at hrelk
      simpa [hke] using hrelk
    have h := smul_transport v g u hgu
      (Pi.single k 1 : Fin Tag.E6.rank → ℤ) e.c e.d Finset.univ e.t
      (fun a : Fin 3 => (Pi.single (s a) 1 : Fin Tag.E6.rank → ℤ)) (by simpa using hrelk')
    simpa using h
  have hcard := nat_card_closure_le_cube_of_three_relations ha hu s hrel
  have h27 : Nat.card (Subgroup.closure (Set.range a)) ≤ 27 := by simpa using hcard
  omega

theorem familyStabilizerSubgroup_eq_bot_of_three_E6
    {K : Type} [Field K] {ι : Type} [Finite ι] {a : ι → Fin Tag.E6.rank → Kˣ}
    (ha : ∀ i j, a i j ^ 3 = 1) (hΦ : familyKernel a = ∅)
    (hE : 3 ^ 4 ≤ Nat.card (Subgroup.closure (Set.range a))) :
    familyStabilizerSubgroup a = ⊥ := by
  classical
  by_contra hne
  obtain ⟨u, huord⟩ := exists_orderThree_of_ne_bot ha hΦ hne
  have hu3 : (u : WeylGroup Tag.E6) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one (u : WeylGroup Tag.E6)
    rwa [Subgroup.orderOf_coe, huord] at h
  have hune : (u : WeylGroup Tag.E6) ≠ 1 := by
    intro h
    have h' : orderOf (u : WeylGroup Tag.E6) = 3 := by rw [Subgroup.orderOf_coe, huord]
    rw [h, orderOf_one] at h'
    norm_num at h'
  obtain ⟨v, hv⟩ := CFSG.HardMathSupport.Lang.E6Descent.DiagWeyl.exists_conj_mem_Pw hu3
  set g := v⁻¹ * (u : WeylGroup Tag.E6) * v with hg
  have hgu : (u : WeylGroup Tag.E6) = v * g * v⁻¹ := by rw [hg]; group
  have hg3 : g ^ 3 = 1 := by
    have := conj_pow (a := v⁻¹) (b := (u : WeylGroup Tag.E6)) (i := 3)
    rw [inv_inv] at this
    rw [hg, this, hu3]
    simp
  have hgne : g ≠ 1 := by
    intro h
    apply hune
    have e : v * g * v⁻¹ = (u : WeylGroup Tag.E6) := by rw [hg]; group
    have h1 : v * g * v⁻¹ = 1 := by rw [h]; simp
    rw [e] at h1
    exact h1
  obtain ⟨ω, hω, hgω⟩ := CFSG.HardMathSupport.Lang.E6Descent.DiagWeyl.mem_Pw_iff.mp hv
  have hM : weylMatrix g = toMat Tag.E6.rank (dEval ω) := by
    rw [hgω]
    exact CFSG.HardMathSupport.Lang.E6Descent.DiagWeyl.weylMatrix_gProd ω
  have h3b : Lat3OrderThreeE6 ω = true :=
    decide_eq_true_iff.mpr (lat3OrderThree_of_weylMatrix_eq g (dEval ω) hM hg3)
  have hneb : Lat3NonidentityE6 ω = true :=
    decide_eq_true_iff.mpr (lat3Nonidentity_of_weylMatrix_eq g (dEval ω) hM hgne)
  obtain ⟨cert, hmem, hcert⟩ := lat3Table_mem_E6 hω h3b hneb
  cases cert with
  | root k c d => exact e6_root_cert_false ha hΦ u.2 hgu hM hcert
  | sym s data => exact e6_sym_cert_false ha hE u.2 hgu hM hcert

private theorem lat3MemS7_eq_false_iff (s : Fin 3 → Fin Tag.E7.rank) (k : Fin Tag.E7.rank) :
    lat3MemS7 s k = false ↔ k ∉ Finset.univ.image s := by
  rw [lat3MemS7, List.any_eq_false]
  simp [Finset.mem_image, decide_eq_true_iff, List.mem_finRange, eq_comm]

private theorem lat3OrderThreeE7_of_weylMatrix_eq (g : WeylGroup Tag.E7) (M : List (List ℤ))
    (hM : weylMatrix g = toMat Tag.E7.rank M) (hg3 : g ^ 3 = 1) :
    ∀ i j : Fin Tag.E7.rank,
      lget (lmul Tag.E7.rank (lmul Tag.E7.rank M M) M) i j = lget (lid Tag.E7.rank) i j := by
  intro i j
  have h : toMat Tag.E7.rank (lmul Tag.E7.rank (lmul Tag.E7.rank M M) M) =
      toMat Tag.E7.rank (lid Tag.E7.rank) := by
    calc toMat Tag.E7.rank (lmul Tag.E7.rank (lmul Tag.E7.rank M M) M)
        = (toMat Tag.E7.rank M) ^ 3 := by
          rw [toMat_lmul, toMat_lmul, pow_succ, pow_two]
      _ = (weylMatrix g) ^ 3 := by rw [hM]
      _ = weylMatrix (g ^ 3) := by rw [weylMatrix_pow]
      _ = 1 := by rw [hg3, weylMatrix_one]
      _ = toMat Tag.E7.rank (lid Tag.E7.rank) := by simpa using (toMat_lid Tag.E7.rank).symm
  exact congrFun (congrFun h i) j

private theorem lat3NonidentityE7_of_weylMatrix_eq (g : WeylGroup Tag.E7) (M : List (List ℤ))
    (hM : weylMatrix g = toMat Tag.E7.rank M) (hgne : g ≠ 1) :
    ∃ i j : Fin Tag.E7.rank, lget M i j ≠ lget (lid Tag.E7.rank) i j := by
  by_contra h
  apply hgne
  apply CFSG.RankThree.E6.weylMatrix_injective
  rw [hM, weylMatrix_one, ← toMat_lid Tag.E7.rank]
  ext i j
  by_contra hij
  exact h ⟨i, j, hij⟩

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private def Lat3RelE7 (v u : WeylGroup Tag.E7) (s : Fin 3 → Fin Tag.E7.rank)
    (k : Fin Tag.E7.rank) : Prop :=
  ∃ (c d : Fin Tag.E7.rank → ℤ) (t : Fin 3 → ℤ),
    v • (Pi.single k 1 : Fin Tag.E7.rank → ℤ) =
      u • c - c +
        ∑ a : Fin 3, t a • (v • (Pi.single (s a) 1 : Fin Tag.E7.rank → ℤ)) + 3 • d

private theorem Lat3CertOKE7_sym_rel {M : List (List ℤ)} {s : Fin 3 → Fin Tag.E7.rank}
    {data : List Lat3SDataE7} (hcert : Lat3CertOKE7 M (.sym s data))
    {k : Fin Tag.E7.rank} (hk : lat3MemS7 s k = false) :
    ∃ e ∈ data, e.k = k ∧
      (Pi.single k 1 : Fin Tag.E7.rank → ℤ) =
        (toMat Tag.E7.rank M).mulVec e.c - e.c +
          ∑ a : Fin 3, e.t a • (Pi.single (s a) 1 : Fin Tag.E7.rank → ℤ) + 3 • e.d :=
  hcert k hk

private theorem lat3Table_mem_E7 {ω : List Bool} (hω : ω ∈ dWords)
    (h3 : Lat3OrderThreeE7M (dEval7 ω) = true) (hne : Lat3NonidentityE7M (dEval7 ω) = true) :
    ∃ cert, (ω, cert) ∈ Lat3TableE7 ∧ Lat3CertOKE7 (dEval7 ω) cert := by
  have hcheck := List.all_eq_true.mp lat3Table_check_E7 ω hω
  simp only [Lat3CheckWordE7, h3, hne, Bool.true_and, cond_true] at hcheck
  rw [List.any_eq_true] at hcheck
  obtain ⟨p, hp, hb⟩ := hcheck
  rw [Bool.and_eq_true] at hb
  exact ⟨p.2, by rw [← beq_iff_eq.mp hb.1]; exact hp,
    (Lat3CertOKE7b_eq_true_iff _ _).mp hb.2⟩

private theorem e7_root_cert_false
    {K : Type} [Field K] {ι : Type}
    {a : ι → Fin Tag.E7.rank → Kˣ} (ha : ∀ i j, a i j ^ 3 = 1) (hΦ : familyKernel a = ∅)
    {u v g : WeylGroup Tag.E7} (hu : u ∈ familyStabilizerSubgroup a)
    (hgu : u = v * g * v⁻¹)
    {M : List (List ℤ)} (hM : weylMatrix g = toMat Tag.E7.rank M)
    {k : Fin 126} {c d : Fin Tag.E7.rank → ℤ}
    (hcert : e7RootVec k = (toMat Tag.E7.rank M).mulVec c - c + 3 • d) : False := by
  have hroot : IsRoot Tag.E7 (e7RootVec k) := isRoot_e7RootVec k
  have hrelg : e7RootVec k = g • c - c + 3 • d := by
    rw [hcert, ← hM, CFSG.RankThree.E6.weylMatrix_mulVec]
  have hβroot : IsRoot Tag.E7 (v • e7RootVec k) := IsRoot.smul hroot v
  have hβmem : v • e7RootVec k ∈ familyKernel a := by
    apply mem_familyKernel_of_eq_smul_sub_add_three ha hu hβroot
    exact smul_transport_root v g u hgu (e7RootVec k) c d hrelg
  rw [hΦ] at hβmem
  exact hβmem

private theorem e7_sym_cert_false
    {K : Type} [Field K] {ι : Type}
    {a : ι → Fin Tag.E7.rank → Kˣ} (ha : ∀ i j, a i j ^ 3 = 1)
    (hE : 3 ^ 4 ≤ Nat.card (Subgroup.closure (Set.range a)))
    {u v g : WeylGroup Tag.E7} (hu : u ∈ familyStabilizerSubgroup a)
    (hgu : u = v * g * v⁻¹)
    {M : List (List ℤ)} (hM : weylMatrix g = toMat Tag.E7.rank M)
    {s : Fin 3 → Fin Tag.E7.rank} {data : List Lat3SDataE7}
    (hcert : Lat3CertOKE7 M (.sym s data)) : False := by
  have hrel : ∀ k : Fin Tag.E7.rank, k ∉ Finset.univ.image s →
      Lat3RelE7 v u s k := by
    intro k hk
    have hk' : lat3MemS7 s k = false := (lat3MemS7_eq_false_iff s k).2 hk
    obtain ⟨e, he, hke, hrelk⟩ := Lat3CertOKE7_sym_rel hcert hk'
    refine ⟨v • e.c, v • e.d, e.t, ?_⟩
    have hrelk' : (Pi.single k 1 : Fin Tag.E7.rank → ℤ) =
        g • e.c - e.c +
          ∑ a : Fin 3, e.t a • (Pi.single (s a) 1 : Fin Tag.E7.rank → ℤ) + 3 • e.d := by
      rw [← hM, CFSG.RankThree.E6.weylMatrix_mulVec] at hrelk
      simpa [hke] using hrelk
    have h := smul_transport v g u hgu
      (Pi.single k 1 : Fin Tag.E7.rank → ℤ) e.c e.d Finset.univ e.t
      (fun a : Fin 3 => (Pi.single (s a) 1 : Fin Tag.E7.rank → ℤ)) (by simpa using hrelk')
    simpa using h
  have hcard := nat_card_closure_le_cube_of_three_relations ha hu s hrel
  have h27 : Nat.card (Subgroup.closure (Set.range a)) ≤ 27 := by simpa using hcard
  omega

private theorem e7_exists_conj_Pw
    {u : WeylGroup Tag.E7} (hu3 : u ^ 3 = 1) :
    ∃ v : WeylGroup Tag.E7, v⁻¹ * u * v ∈
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313InAux.Pw7 := by
  have hB3 : ∀ b ∈ Subgroup.zpowers u, b ^ 3 = 1 := by
    intro b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu3, one_zpow]
  obtain ⟨v, hv⟩ := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313InAux.exists_conj_le_Pw7
    (B := Subgroup.zpowers u) hB3
  exact ⟨v, hv u (Subgroup.mem_zpowers u)⟩

private theorem e7_order3_nonidM {g : WeylGroup Tag.E7} {M : List (List ℤ)}
    (hM : weylMatrix g = toMat Tag.E7.rank M) (hg3 : g ^ 3 = 1) (hgne : g ≠ 1) :
    Lat3OrderThreeE7M M = true ∧ Lat3NonidentityE7M M = true := by
  constructor
  · rw [Lat3OrderThreeE7M, List.all_eq_true]
    intro i _
    rw [List.all_eq_true]
    intro j _
    exact beq_iff_eq.mpr (lat3OrderThreeE7_of_weylMatrix_eq g M hM hg3 i j)
  · rw [Lat3NonidentityE7M, List.any_eq_true]
    obtain ⟨i, j, hij⟩ := lat3NonidentityE7_of_weylMatrix_eq g M hM hgne
    exact ⟨i, List.mem_finRange i, by
      rw [List.any_eq_true]
      exact ⟨j, List.mem_finRange j, by simp [hij]⟩⟩

theorem familyStabilizerSubgroup_eq_bot_of_three_E7
    {K : Type} [Field K] {ι : Type} [Finite ι] {a : ι → Fin Tag.E7.rank → Kˣ}
    (ha : ∀ i j, a i j ^ 3 = 1) (hΦ : familyKernel a = ∅)
    (hE : 3 ^ 4 ≤ Nat.card (Subgroup.closure (Set.range a))) :
    familyStabilizerSubgroup a = ⊥ := by
  classical
  by_contra hne
  obtain ⟨u, huord⟩ := exists_orderThree_of_ne_bot ha hΦ hne
  have hu3 : (u : WeylGroup Tag.E7) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one (u : WeylGroup Tag.E7)
    rwa [Subgroup.orderOf_coe, huord] at h
  have hune : (u : WeylGroup Tag.E7) ≠ 1 := by
    intro h
    have h' : orderOf (u : WeylGroup Tag.E7) = 3 := by rw [Subgroup.orderOf_coe, huord]
    rw [h, orderOf_one] at h'
    norm_num at h'
  obtain ⟨v, hvu⟩ := e7_exists_conj_Pw hu3
  set g := v⁻¹ * (u : WeylGroup Tag.E7) * v with hg
  have hgu : (u : WeylGroup Tag.E7) = v * g * v⁻¹ := by rw [hg]; group
  have hg3 : g ^ 3 = 1 := by
    have := conj_pow (a := v⁻¹) (b := (u : WeylGroup Tag.E7)) (i := 3)
    rw [inv_inv] at this
    rw [hg, this, hu3]
    simp
  have hgne : g ≠ 1 := by
    intro h
    apply hune
    have e : v * g * v⁻¹ = (u : WeylGroup Tag.E7) := by rw [hg]; group
    have h1 : v * g * v⁻¹ = 1 := by rw [h]; simp
    rw [e] at h1
    exact h1
  obtain ⟨ω, hω, hgω⟩ := mem_Pw7_iff.mp hvu
  have hM : weylMatrix g = toMat Tag.E7.rank (dEval7 ω) := by
    rw [hgω]
    exact weylMatrix_gProd7 ω
  obtain ⟨h3b, hneb⟩ := e7_order3_nonidM hM hg3 hgne
  obtain ⟨cert, hmem, hcert⟩ := lat3Table_mem_E7 hω h3b hneb
  cases cert with
  | root k c d => exact e7_root_cert_false ha hΦ u.2 hgu hM hcert
  | sym s data => exact e7_sym_cert_false ha hE u.2 hgu hM hcert

theorem familyStabilizerSubgroup_eq_bot_of_three
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7)
    {K : Type} [Field K] {ι : Type} [Finite ι] {a : ι → Fin τ.rank → Kˣ}
    (ha : ∀ i j, a i j ^ 3 = 1) (hΦ : familyKernel a = ∅)
    (hE : 3 ^ 4 ≤ Nat.card (Subgroup.closure (Set.range a))) :
    familyStabilizerSubgroup a = ⊥ := by
  rcases hτ with rfl | rfl
  · exact familyStabilizerSubgroup_eq_bot_of_three_E6 ha hΦ hE
  · exact familyStabilizerSubgroup_eq_bot_of_three_E7 ha hΦ hE

theorem familyCentralizer_eq_torusGroup_of_three
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7)
    {K : Type} [Field K] {ι : Type} [Finite ι] {a : ι → Fin τ.rank → Kˣ}
    (ha : ∀ i j, a i j ^ 3 = 1) (hΦ : familyKernel a = ∅)
    (hE : 3 ^ 4 ≤ Nat.card (Subgroup.closure (Set.range a))) :
    familyCentralizer τ K a = torusGroup τ K := by
  rw [familyCentralizer_eq_familyGroup a (by
    rw [familyStabilizerSubgroup_eq_bot_of_three hτ ha hΦ hE]; exact bot_le), familyGroup, hΦ]
  simp [rootSpan]

end CFSG.HardMathSupport.C14Lattice
