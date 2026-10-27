module

public import Certificates.Data.GrSLitL34FactsRealCheck
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34CertInputs

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4.OutCov

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers.L34 CFSG.ComponentClassification.GrSLit
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real

@[expose] def kGensB : List (ZMod 4 × ZMod 4) := [(1, 0), (0, 1), (1, 1), (1, 2), (2, 1), (1, 3)]

@[expose] def inKb (κ : ZMod 4 × ZMod 4) (a b : ZMod 4) : Bool :=
  (List.range 4).any fun m => ((m : ZMod 4) * κ.1 == a) && ((m : ZMod 4) * κ.2 == b)

abbrev El : Type := ℕ × ZMod 4 × ZMod 4

@[expose] def oneE : El := (0, 0, 0)

@[expose] def mulE (x y : El) : El :=
  ((t1Entry x.1 y.1).1, x.2.1 + y.2.1 + ((t1Entry x.1 y.1).2.1 : ZMod 4),
    x.2.2 + y.2.2 + ((t1Entry x.1 y.1).2.2.1 : ZMod 4))

@[expose] def invIdx (t : ℕ) : ℕ :=
  ((List.range 64).find? fun t' => (t1Entry t t').1 == 0).getD 0

@[expose] def invE (t : ℕ) : El :=
  (invIdx t, -((t1Entry t (invIdx t)).2.1 : ZMod 4), -((t1Entry t (invIdx t)).2.2.1 : ZMod 4))

@[expose] def alphaE (i : ℕ) (x : El) : El :=
  ((alphaEntry i x.1).1,
    ((alphaEntry i x.1).2.1 : ZMod 4) +
      (x.2.1 * ((alphaEntry i 64).2.1 : ZMod 4) + x.2.2 * ((alphaEntry i 65).2.1 : ZMod 4)),
    ((alphaEntry i x.1).2.2.1 : ZMod 4) +
      (x.2.1 * ((alphaEntry i 64).2.2.1 : ZMod 4) + x.2.2 * ((alphaEntry i 65).2.2.1 : ZMod 4)))

@[expose] def betaE (t i : ℕ) (x : El) : El := mulE (mulE (t, 0, 0) (alphaE i x)) (invE t)

@[expose] def eqE (κ : ZMod 4 × ZMod 4) (x y : El) : Bool :=
  (x.1 == y.1) && inKb κ (x.2.1 - y.2.1) (x.2.2 - y.2.2)

@[expose] def z4 : List (ZMod 4) := (List.range 4).map fun n => (n : ZMod 4)

@[expose] def els : List El :=
  (List.range 64).flatMap fun k => z4.flatMap fun a => z4.map fun b => (k, a, b)

@[expose] def invar (κ : ZMod 4 × ZMod 4) (i : ℕ) : Bool :=
  inKb κ (κ.1 * ((alphaEntry i 64).2.1 : ZMod 4) + κ.2 * ((alphaEntry i 65).2.1 : ZMod 4))
    (κ.1 * ((alphaEntry i 64).2.2.1 : ZMod 4) + κ.2 * ((alphaEntry i 65).2.2.1 : ZMod 4))

@[expose] def rT (t j : ℕ) : Tab := comp 42 (wordTab (tg t)) (repTab j)

@[expose] def commB (x y : Tab) : Bool := comp 42 x y == comp 42 y x

@[expose] def is2 (x : Tab) : Bool := powTwoTab x 8 == idTab 42

@[expose] def fixK (κ : ZMod 4 × ZMod 4) (t₀ i₀ : ℕ) : List ℕ :=
  (List.range 64).filter fun k =>
    z4.any fun a => z4.any fun b => eqE κ (betaE t₀ i₀ (k, a, b)) (k, a, b)

@[expose] def c3Case (iS : Std.HashMap Tab ℕ) (ES : Array Tab) (κ : ZMod 4 × ZMod 4)
    (t₀ i₀ : ℕ) : Bool :=
  let ρ := rT t₀ i₀
  let F := fixK κ t₀ i₀
  allBelow 64 fun t => allBelow 36 fun j =>
    let r := rT t j
    !(commB r ρ && comp 42 r r == idTab 42 && F.all fun k => commB r (wordTab (tg k))) ||
      found iS ES r || found iS ES (comp 42 r ρ)

@[expose] def liftC (κ : ZMod 4 × ZMod 4) (ρ : Tab) : List (ℕ × ℕ) :=
  ((List.range 64).flatMap fun t => (List.range 36).map fun j => (t, j)).filter fun x =>
    invar κ x.2 && commB (rT x.1 x.2) ρ

@[expose] def invsE (κ : ZMod 4 × ZMod 4) : List El :=
  els.filter fun x => eqE κ (mulE x x) oneE && !(x.1 == 0)

@[expose] def twoOK (r : Tab) (gens : List Tab) : Bool :=
  is2 r && gens.all fun s => is2 (comp 42 r s) && is2 (comp 42 s r)

@[expose] def ftabs (κ : ZMod 4 × ZMod 4) (t₀ i₀ : ℕ) : List Tab :=
  (fixK κ t₀ i₀).map fun k => wordTab (tg k)

@[expose] def inTabs (EB : Array Tab) (x : Tab) : Bool := found (indexOf EB) EB x

@[expose] def c4A (κ : ZMod 4 × ZMod 4) (EB : Array Tab) (L : List (ℕ × ℕ)) (W : List El) :
    Bool :=
  W.any fun w => L.all fun x => !inTabs EB (rT x.1 x.2) || eqE κ (betaE x.1 x.2 w) w

@[expose] def c4B (κ : ZMod 4 × ZMod 4) (ρ : Tab) (EB : Array Tab) (Ft : List Tab)
    (L : List (ℕ × ℕ)) (W : List El) : Bool :=
  L.all fun x₁ => inTabs EB (rT x₁.1 x₁.2) || !is2 (rT x₁.1 x₁.2) ||
    W.any fun w => L.all fun x => eqE κ (betaE x.1 x.2 w) w ||
      !twoOK (rT x.1 x.2) ([rT x₁.1 x₁.2, ρ] ++ Ft)

@[expose] def c4Case (κ : ZMod 4 × ZMod 4) (t₀ i₀ : ℕ) : Bool :=
  let ρ := rT t₀ i₀
  let Ft := ftabs κ t₀ i₀
  let EB := (enumBFS 42 (Ft ++ [ρ]).toArray 64).tabs
  let L := liftC κ ρ
  let W := invsE κ
  c4A κ EB L W && c4B κ ρ EB Ft L W

@[expose] def inverts (κ : ZMod 4 × ZMod 4) (t₀ i₀ : ℕ) : Bool :=
  eqE κ (betaE t₀ i₀ (0, 1, 0)) (0, -1, 0) && eqE κ (betaE t₀ i₀ (0, 0, 1)) (0, 0, -1)

@[expose] def c5Case (κ : ZMod 4 × ZMod 4) (t₀ i₀ : ℕ) : Bool :=
  !inverts κ t₀ i₀ || els.all fun x =>
    !(eqE κ (mulE x x) oneE && eqE κ (betaE t₀ i₀ x) x) ||
      els.any fun v => eqE κ v (mulE (betaE t₀ i₀ v) x)

@[expose] def invOKE : Bool :=
  allBelow 64 fun t => decide (invIdx t < 64) && (t1Entry t (invIdx t)).1 == 0

@[noinline, expose] def outCovOK : Bool :=
  let ES := enumBFS 42 gensS 20160
  let iS := indexOf ES.tabs
  invOKE && kGensB.all fun κ => [r₂T, r₃T, r₄T].all fun ρ => allBelow 64 fun t₀ =>
    allBelow 36 fun i₀ => !(rT t₀ i₀ == ρ && invar κ i₀) ||
      (c3Case iS ES.tabs κ t₀ i₀ && c4Case κ t₀ i₀ && c5Case κ t₀ i₀)

end CFSG.ComponentClassification.GrSLit.GrS4.OutCov
