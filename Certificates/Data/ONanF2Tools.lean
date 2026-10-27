module

public import Certificates.Data.ONanF2Model
public import Mathlib.Algebra.Group.Commutator

public section

namespace CFSG.OddStandard.ONanRec.F2

open scoped commutatorElement

@[expose] def allE : List AlpE :=
  (List.finRange 8).flatMap fun d => (List.finRange 4).flatMap fun a =>
    (List.finRange 4).flatMap fun b => (List.finRange 4).map fun c => ⟨d, a, b, c⟩

section Ball

variable {G : Type*} [Group G] [DecidableEq G]

@[expose] def bfs (gens : List G) : ℕ → List G → List G → List G
  | 0, vis, _ => vis
  | n + 1, vis, fr =>
    let new := (fr.flatMap fun x => gens.map (x * ·)).dedup.filter fun y => y ∉ vis
    if new.isEmpty then vis else bfs gens n (vis ++ new) new

@[expose] def ballFix (gens : List G) : List G := bfs gens 64 [1] [1]

@[expose] def SubOK (gens L : List G) (n : ℕ) : Prop :=
  L = ballFix gens ∧ L.length = n ∧ L.Nodup ∧ ∀ x ∈ L, ∀ g ∈ gens, x * g ∈ L

instance (gens L : List G) (n : ℕ) : Decidable (SubOK gens L n) := by
  unfold SubOK
  infer_instance

@[expose] def bfsC (gens : List G) : ℕ → List G → List G → List G
  | 0, vis, _ => vis
  | n + 1, vis, fr =>
    let new := (fr.flatMap fun x =>
      gens.flatMap fun g => [g⁻¹ * x * g, g * x * g⁻¹]).dedup.filter fun y => y ∉ vis
    if new.isEmpty then vis else bfsC gens n (vis ++ new) new

@[expose] def orbitC (gens : List G) (r : G) : List G := bfsC gens 64 [r] [r]

@[expose] def ClassOK (gens : List G) (r : G) (L : List G) (n : ℕ) : Prop :=
  L = orbitC gens r ∧ L.length = n ∧ L.Nodup ∧
    ∀ x ∈ L, ∀ g ∈ gens, g⁻¹ * x * g ∈ L ∧ g * x * g⁻¹ ∈ L

instance (gens : List G) (r : G) (L : List G) (n : ℕ) : Decidable (ClassOK gens r L n) := by
  unfold ClassOK
  infer_instance

end Ball

section Words

variable {M : Type*} [Group M]

@[expose] def invRep (v1 v2 v3 s t : M) : Fin 7 → M :=
  ![v1 ^ 2 * v3 ^ 2, v1 ^ 2 * v2 ^ 2, v2 ^ 2, s ^ 2 * v1⁻¹, s * t, t, t * v2]

@[expose] def genV0 (v1 v2 v3 : M) : List M := [v1 * v2, v2 * v3, v1 ^ 2]

@[expose] def genMax (v1 v2 v3 s t : M) : Fin 7 → List M :=
  ![[v1, v2, v3, s], [v1, v2, v3, s ^ 2, t], [v1, v2, v3, s ^ 2, s * t],
    genV0 v1 v2 v3 ++ [s ^ 2, s, t], genV0 v1 v2 v3 ++ [s ^ 2, s, v1 * t],
    genV0 v1 v2 v3 ++ [s ^ 2, t, v1 * s], genV0 v1 v2 v3 ++ [s ^ 2, v1 * s, v1 * t]]

@[expose] def genQ (v1 v2 s t : M) : List M := [v1, v2, s * t]

@[expose] def genCent (v1 v2 v3 s t : M) : Fin 3 → List M :=
  ![[v1 * v3, v1 ^ 2 * v2 ^ 2, s ^ 2 * v1⁻¹, t], [v1 * v3⁻¹, v2 ^ 2, s ^ 2 * v1⁻¹, t],
    [v1 * v3⁻¹, v2 ^ 2, s ^ 2 * v1 * v2 * v3, t * v2]]

@[expose] def xel (v1 v2 v3 : M) : M := v1 * v2 ^ 2 * v3⁻¹

end Words

@[expose] def invE : Fin 7 → AlpE :=
  invRep (AlpE.gen 0) (AlpE.gen 1) (AlpE.gen 2) (AlpE.gen 3) (AlpE.gen 4)

@[expose] def genE : List AlpE := [AlpE.gen 0, AlpE.gen 1, AlpE.gen 2, AlpE.gen 3, AlpE.gen 4]

@[expose] def invEL : List AlpE := List.ofFn invE

@[expose] def genV0E : List AlpE := genV0 (AlpE.gen 0) (AlpE.gen 1) (AlpE.gen 2)

@[expose] def genMaxE (i : Fin 7) : List AlpE :=
  genMax (AlpE.gen 0) (AlpE.gen 1) (AlpE.gen 2) (AlpE.gen 3) (AlpE.gen 4) i

@[expose] def genQE : List AlpE := genQ (AlpE.gen 0) (AlpE.gen 1) (AlpE.gen 3) (AlpE.gen 4)

@[expose] def genCentE (i : Fin 3) : List AlpE :=
  genCent (AlpE.gen 0) (AlpE.gen 1) (AlpE.gen 2) (AlpE.gen 3) (AlpE.gen 4) i

@[expose] def genPdE : List AlpE := genV0E ++ [AlpE.gen 3 ^ 2]

@[expose] def genCommE : List AlpE :=
  [⁅AlpE.gen 3, AlpE.gen 4⁆, ⁅AlpE.gen 3, AlpE.gen 0⁆, ⁅AlpE.gen 4, AlpE.gen 0⁆,
    ⁅AlpE.gen 3, AlpE.gen 1⁆]

@[expose] def xE : AlpE := xel (AlpE.gen 0) (AlpE.gen 1) (AlpE.gen 2)

end CFSG.OddStandard.ONanRec.F2
