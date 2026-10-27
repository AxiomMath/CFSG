module

public import CFSG.Blueprint.ChevalleyRootArtifact

public section

namespace CFSG.StandardType.TwE6NormThree

open CFSG.Blueprint.Chevalley

@[expose] def cv : List ℤ → List ℤ
  | [a, b, c, d, e, f] =>
    [2 * a - c, 2 * b - d, 2 * c - a - d, 2 * d - b - c - e, 2 * e - d - f, 2 * f - e]
  | _ => [0, 0, 0, 0, 0, 0]

@[expose] def dt : List ℤ → List ℤ → ℤ
  | [a, b, c, d, e, f], [a', b', c', d', e', f'] =>
    a * a' + b * b' + c * c' + d * d' + e * e' + f * f'
  | _, _ => 0

@[expose] def phi (y : List ℤ) : List (List ℤ) :=
  TwistTag.E6.tag.artifactRoots.filter fun r => dt r y % 3 == 0

@[expose] def star (y g : List ℤ) : List (List ℤ) :=
  (phi y).filter fun d => dt g (cv d) != 0

@[expose] def addv (u v : List ℤ) : List ℤ := List.zipWith (· + ·) u v

@[expose] def smulv (c : ℤ) (u : List ℤ) : List ℤ := u.map (c * ·)

@[expose] def nz3 (v : List ℤ) : Bool := v.any fun x => x % 3 != 0

@[expose] def axpy (c : ℤ) (p v : List ℤ) : List ℤ :=
  List.zipWith (fun a b => (b - c * a) % 3) p v

@[expose] def reduce (piv : List (List ℤ × ℕ)) (v : List ℤ) : List ℤ :=
  piv.foldl (fun v pi => axpy (v.getD pi.2 0 * pi.1.getD pi.2 0) pi.1 v) v

@[expose] def select : List (List ℤ) → List (List ℤ × ℕ) → List (List ℤ) → List (List ℤ)
  | [], _, acc => acc
  | s :: S, piv, acc =>
    if 4 ≤ acc.length then acc else
    let v := reduce piv ((cv s).map (· % 3))
    match v.findIdx? (· != 0) with
    | some i => select S (piv ++ [(v, i)]) (acc ++ [s])
    | none => select S piv acc

@[expose] def lc4 (a b c d : ℤ) (u₀ u₁ u₂ u₃ : List ℤ) : List ℤ :=
  addv (smulv a u₀) (addv (smulv b u₁) (addv (smulv c u₂) (smulv d u₃)))

@[expose] def indep4 (u₀ u₁ u₂ u₃ : List ℤ) : Bool :=
  (List.range 81).all fun n => n == 0 ||
    nz3 (lc4 (n % 3 : ℕ) (n / 3 % 3 : ℕ) (n / 9 % 3 : ℕ) (n / 27 % 3 : ℕ) u₀ u₁ u₂ u₃)

@[expose] def caseA (y g : List ℤ) : Bool :=
  match (select (star y g) [] []).take 4 with
  | [s₀, s₁, s₂, s₃] =>
    (star y g).contains s₀ && (star y g).contains s₁ && (star y g).contains s₂ &&
      (star y g).contains s₃ && indep4 (cv s₀) (cv s₁) (cv s₂) (cv s₃)
  | _ => false

@[expose] def span2 (g d s : List ℤ) : Bool :=
  [0, 1, 2].any fun a => [0, 1, 2].any fun b =>
    !nz3 (List.zipWith (· - ·) (addv (smulv a g) (smulv b d)) s)

@[expose] def caseB (y g : List ℤ) : Bool :=
  ((star y g).all fun d => (phi y).all fun e => dt d (cv e) == 0 || (star y g).contains e) &&
    (star y g).any fun d => (star y g).all fun s => span2 g d s

@[expose] def good (y g : List ℤ) : Bool := caseA y g || caseB y g

theorem good_single_zero : ∀ a b c d e : ZMod 3,
    good [0, (a.val : ℤ), (b.val : ℤ), (c.val : ℤ), (d.val : ℤ), (e.val : ℤ)]
      [1, 0, 0, 0, 0, 0] = true := by
  decide +kernel

end CFSG.StandardType.TwE6NormThree

end
