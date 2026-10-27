module

public import CFSG.LieType.Chevalley.C2E6StdMatrixVec
public import CFSG.LieType.Chevalley.C2E6StdMatrixModelInputs

public section

namespace CFSG.Monster.Existence.StdOdd.Cert

open Matrix CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std.MatrixModel
  CFSG.Monster.B.Classical.E6Adjoint

abbrev M78 : Type := Matrix (Fin 78) (Fin 78) K

@[expose] def wM (w : List (ℕ × Bool)) : M78 := toMat (Native.wordMat nativeAB.1 nativeAB.2 w)

@[expose] def monAB : Submonoid M78 := Submonoid.closure {toMat nativeAB.1, toMat nativeAB.2}

@[expose] def monL (Ms : List M78) : Submonoid M78 := Submonoid.closure {M | M ∈ Ms}

@[expose] def fsum (u w : Fin 78 → K) : K :=
  ∑ a : Fin 78, ∑ c : Fin 78, if fbit a c then u a * w c else 0

@[expose] def mPt (m : ℕ) : Fin 78 → K := fun k => if m.testBit k then 1 else 0

@[expose] def bsum (u w : Fin 78 → K) : Fin 78 → K :=
  ∑ a : Fin 78, ∑ c : Fin 78, (u a * w c) • mPt (brMask a c)

open Classical in
@[expose] noncomputable def rhoC (u w : Fin 78 → K) : ℕ :=
  if u = w then 0 else if fsum u w ≠ 0 then 4 else if bsum u w ≠ 0 then 3 else 5

@[expose] def SiftFails (p : ℕ) (β : ℕ → Fin 78 → K) (reg : ℕ → List M78)
    (B : ℕ → Finset (Fin 78 → K)) (t1 : ℕ → Fin 78 → K) : Prop :=
  ∃ (m : ℕ) (t : ℕ → ℕ → Fin 78 → K) (f : ℕ → M78), 1 ≤ m ∧ m < p ∧
    (∀ i < p, t 1 i = t1 i) ∧ t 1 0 = β 0 ∧
    (∀ j, 1 ≤ j → j < m → f j ∈ monL (reg j) ∧ f j *ᵥ t j j = β j ∧
      ∀ i < p, t (j + 1) i = f j *ᵥ t j i) ∧
    t m m ∉ B m

structure CentFacts (p N : ℕ) (xw d0 : List (ℕ × Bool)) (e : ℕ → ℕ) (K1 Kall : List (ℕ × ℕ)) :
    Prop where
  e0 : e 0 = 0
  e_lt : ∀ i < p, e i < p
  cover : ∀ j < p, ∃ i < p, e i = j
  facts : ∃ (reg : ℕ → List M78) (B : ℕ → Finset (Fin 78 → K)) (L : List M78)
    (opts : ℕ → Fin 78 → K) (H : List M78) (sl st : ℕ → Fin 78 → K) (s m₀ : ℕ),
    (∀ i, ∀ M ∈ reg i, M ∈ monAB) ∧
    (∀ i < p, ∀ M ∈ reg i, ∀ j < i, M *ᵥ (wM xw ^ e j *ᵥ (wM d0 *ᵥ Pi.single 7 1)) =
      wM xw ^ e j *ᵥ (wM d0 *ᵥ Pi.single 7 1)) ∧
    (∀ i, 1 ≤ i → i < p → ∀ y ∈ B i, ∃ g ∈ monL (reg i),
      g *ᵥ y = wM xw ^ e i *ᵥ (wM d0 *ᵥ Pi.single 7 1)) ∧
    (∀ M ∈ L, M ∈ monAB ∧ M * wM xw = wM xw * M ∧ ∀ j < p,
      M *ᵥ (wM xw ^ e j *ᵥ (wM d0 *ᵥ Pi.single 7 1)) = wM xw ^ e j *ᵥ (wM d0 *ᵥ Pi.single 7 1)) ∧
    L.Nodup ∧ Nat.Coprime L.length p ∧
    3968055 * (∏ i ∈ Finset.Ico 1 p, (B i).card) * L.length = 76532479683774853939200 ∧
    (∃ r < 3968055, opts r = Pi.single 7 1) ∧
    (∀ i < 3968055, ∃ j < 3968055, opts j = toMat nativeAB.1 *ᵥ opts i) ∧
    (∀ i < 3968055, ∃ j < 3968055, opts j = toMat nativeAB.2 *ᵥ opts i) ∧
    (∀ q ∈ K1, rhoC (wM d0 *ᵥ Pi.single 7 1) (wM xw ^ q.1 *ᵥ (wM d0 *ᵥ Pi.single 7 1)) = q.2) ∧
    (∀ q ∈ Kall, rhoC (wM d0 *ᵥ Pi.single 7 1) (wM xw ^ q.1 *ᵥ (wM d0 *ᵥ Pi.single 7 1)) = q.2) ∧
    (∀ i < 3968055, ∀ j < 3968055, opts i = opts j → i = j) ∧
    (∃ dep : ℕ → ℕ, (∀ i < 3968055, dep i = 0 → opts i = Pi.single 7 1) ∧
      ∀ i < 3968055, 0 < dep i → ∃ j < 3968055, dep j < dep i ∧
        (opts i = toMat nativeAB.1 *ᵥ opts j ∨ opts i = toMat nativeAB.2 *ᵥ opts j ∨
          opts j = toMat nativeAB.2 *ᵥ opts i)) ∧
    ((Finset.range 3968055).filter fun i => ∀ q ∈ K1, rhoC (opts i) (wM xw ^ q.1 *ᵥ opts i) = q.2).card
      = s ∧
    (∀ j < s, ∀ q ∈ K1, rhoC (sl j) (wM xw ^ q.1 *ᵥ sl j) = q.2) ∧
    (∀ j < s, ∃ g ∈ monAB, g *ᵥ sl j = wM d0 *ᵥ Pi.single 7 1) ∧
    (∀ j < s, ∀ j' < s, sl j = sl j' → j = j') ∧
    (∀ M ∈ H, M ∈ monAB ∧ M * wM xw = wM xw * M) ∧
    (∀ j < s, ∃ g ∈ monL H, g *ᵥ sl j = st j) ∧
    ((Finset.range s).filter fun j => st j = wM d0 *ᵥ Pi.single 7 1).card = m₀ ∧
    N = m₀ * L.length ∧
    (∀ j < s, st j ≠ wM d0 *ᵥ Pi.single 7 1 →
      (∃ q ∈ Kall, rhoC (sl j) (wM xw ^ q.1 *ᵥ sl j) ≠ q.2) ∨
      ∃ g ∈ monAB, g *ᵥ st j = wM d0 *ᵥ Pi.single 7 1 ∧
        SiftFails p (fun i => wM xw ^ e i *ᵥ (wM d0 *ᵥ Pi.single 7 1)) reg B
          (fun i => g *ᵥ (wM xw ^ e i *ᵥ st j)))

end CFSG.Monster.Existence.StdOdd.Cert

end
