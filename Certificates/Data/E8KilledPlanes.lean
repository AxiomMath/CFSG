module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeChar
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import Std.Data.HashMap
public import Std.Data.HashSet

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral.E8Plane

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Steinberg

@[expose] def e8PlaneRL (_ : Unit := ()) : Array (List ℤ) :=
  ((List.range 240).map fun k => List.ofFn (e8Certificate.root k)).toArray

@[expose] def e8PlaneRA (_ : Unit := ()) : Array (List ℤ) :=
  ((List.range 240).map fun k => List.ofFn fun i : Fin Tag.E8.rank =>
    ∑ j, Tag.E8.symmetrizedCartan i j * e8Certificate.root k j).toArray

@[expose] def e8PlaneGram (RL RA : Array (List ℤ)) : Array ℤ :=
  ((List.range 57600).map fun p => dotL (RL.getD (p / 240) []) (RA.getD (p % 240) [])).toArray

@[expose] def e8PlanePermOf (rt : Array ℕ) (w : List ℕ) (x : ℕ) : ℕ :=
  w.foldr (fun b y => rt.getD (240 * b + y) 0) x

@[expose] def e8PlaneMaskOf (p : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | k + 1 => e8PlaneMaskOf p k ||| (if p k then 1 <<< k else 0)

@[expose] def e8PlaneDigits (n : ℕ) : List ℤ := (digits3 .E8 n).map fun x : ℕ => (x : ℤ)

@[expose] def e8PlaneDN (_ : Unit := ()) : Array (List ℤ) :=
  ((List.range 6561).map e8PlaneDigits).toArray

@[expose] def e8PlaneKill (RL : Array (List ℤ)) (dn : List ℤ) (r : ℕ) : Bool :=
  decide (dotL (RL.getD r []) dn % 3 = 0)

@[expose] def e8PlaneKM (RL DN : Array (List ℤ)) : Array ℕ :=
  ((List.range 6561).map fun n => e8PlaneMaskOf (e8PlaneKill RL (DN.getD n [])) 240).toArray

@[expose] def e8PlaneCnt (RL DN : Array (List ℤ)) : Array ℕ :=
  ((List.range 6561).map fun n =>
    ((List.range 240).filter (e8PlaneKill RL (DN.getD n []))).length).toArray

@[expose] def e8PlaneFix (rv : List (List ℤ)) (dn : List ℤ) : Bool :=
  (List.range 8).all fun j => decide ((dotL (rv.getD j []) dn - dn.getD j 0) % 3 = 0)

@[expose] def e8PlaneCombo (n₀ n₁ c₀ c₁ : ℕ) : ℕ :=
  (List.range 8).foldr (fun j acc =>
    (c₀ * (n₀ / 3 ^ j % 3) + c₁ * (n₁ / 3 ^ j % 3)) % 3 * 3 ^ j + acc) 0

@[expose] def e8PlaneK78 (CNT : Array ℕ) (n₀ n₁ : ℕ) : Bool :=
  (List.range 8).all fun c => CNT.getD (e8PlaneCombo n₀ n₁ ((c + 1) % 3) ((c + 1) / 3)) 0 == 78

@[expose] def e8PlaneSig (σ : ℕ) : List ℕ := (List.range 240).filter σ.testBit

@[expose] def e8PlaneD2 (P : Array ℕ) (G : Array ℤ) (σ : ℕ) : Bool :=
  let S := e8PlaneSig σ
  let g₀ := S.headD 0
  let g₁ := P.getD g₀ 0
  let g₂ := P.getD g₁ 0
  let blk : ℕ → ℕ := fun a =>
    if G.getD (240 * a + g₀) 0 != 0 then 0 else if G.getD (240 * a + g₁) 0 != 0 then 1 else 2
  σ.testBit g₀ && σ.testBit g₁ && σ.testBit g₂ &&
    S.all (fun a => ((if G.getD (240 * a + g₀) 0 != 0 then 1 else 0) +
      (if G.getD (240 * a + g₁) 0 != 0 then 1 else 0) +
      (if G.getD (240 * a + g₂) 0 != 0 then 1 else 0) : ℕ) == 1) &&
    S.all (fun a => S.all fun b =>
      ((G.getD (240 * a + b) 0 != 0) == (blk a == blk b)) &&
        decide (-2 ≤ G.getD (240 * a + b) 0) && decide (G.getD (240 * a + b) 0 ≤ 2)) &&
    (G.getD (240 * P.getD g₂ 0 + g₀) 0 != 0)

@[expose] def e8PlaneD3 (P : Array ℕ) (G : Array ℤ) (σ : ℕ) : Bool :=
  let S := e8PlaneSig σ
  S.length == 24 && S.all (fun g => P.getD g 0 == g || G.getD (240 * g + P.getD g 0) 0 == 0) &&
  S.any fun d =>
    let d₁ := P.getD d 0
    let d₂ := P.getD d₁ 0
    G.getD (240 * d + d₁) 0 == 0 && G.getD (240 * d + d₂) 0 == 0 && G.getD (240 * d₁ + d₂) 0 == 0

@[expose] def e8PlaneTrip (P : Array ℕ) (G : Array ℤ) (S : List ℕ) : List ℕ :=
  S.filter fun d =>
    let d₁ := P.getD d 0
    let d₂ := P.getD d₁ 0
    G.getD (240 * d + d₁) 0 == 0 && G.getD (240 * d + d₂) 0 == 0 && G.getD (240 * d₁ + d₂) 0 == 0

@[expose] def e8PlaneTR (rt P : Array ℕ) (δ x : ℕ) : ℕ :=
  e8PlanePermOf rt [δ, P.getD δ 0, P.getD (P.getD δ 0) 0] x

@[expose] def e8PlaneD3T (rt P : Array ℕ) (G : Array ℤ) (σ : ℕ) : Bool :=
  let T := e8PlaneTrip P G (e8PlaneSig σ)
  T.all fun d =>
    let tgt := [d, P.getD d 0, P.getD (P.getD d 0) 0]
    T.all fun β => tgt.contains β || T.any (fun δ => tgt.contains (e8PlaneTR rt P δ β)) ||
      T.any fun δ₁ => T.any fun δ₂ => tgt.contains (e8PlaneTR rt P δ₁ (e8PlaneTR rt P δ₂ β))

@[expose] def e8PlaneTri (RL : Array (List ℤ)) (P : Array ℕ) : Bool :=
  (List.range 240).all (fun r => RL.getD (P.getD r 0) [] != RL.getD r []) &&
    (List.range 8).foldr (fun j acc => (RL.getD (P.getD j 0) []).getD j 0 + acc) 0 == -4

@[expose] def e8PlaneL1 : List ℕ := [0, 2]

@[expose] def e8PlaneL2 : List ℕ := [4, 5]

@[expose] def e8PlaneL3 : List ℕ :=
  [3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 3, 1]

@[expose] def e8PlaneL4 : List ℕ :=
  [6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3,
    2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7]

@[expose] def e8PlaneLP : List ℕ := [3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 1, 0]

@[expose] def e8PlaneWord (c : ℕ) : List ℕ :=
  (List.replicate (c % 3) e8PlaneL4).flatten ++ (List.replicate (c / 3 % 3) e8PlaneL1).flatten ++
    (List.replicate (c / 9 % 3) e8PlaneL2).flatten ++
    (List.replicate (c / 27 % 3) e8PlaneL3).flatten ++
    (List.replicate (c / 81 % 3) e8PlaneLP).flatten

@[expose] def e8PlaneWordMask (w : List ℕ) : ℕ := w.foldl (fun acc b => acc ||| 1 <<< b) 0

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral.E8Plane
