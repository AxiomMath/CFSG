module

public import CFSG.LocalAnalysis.StandardType.PhanELocalSys
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry CFSG.LieType.BorelTits Module

section Vocabulary

variable (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]

noncomputable abbrev sg : K ≃+* K := unitaryInvolution K 2 f

@[expose] noncomputable def sgv (n : ℕ) : (Fin n → K) →ₛₗ[(sg K f : K →+* K)] (Fin n → K) where
  toFun v i := sg K f (v i)
  map_add' v w := by ext i; simp
  map_smul' c v := by ext i; simp

@[expose] noncomputable def sgS (n : ℕ) (U : Submodule K (Fin n → K)) :
    Submodule K (Fin n → K) :=
  U.comap (sgv K f n)

variable {K}

@[expose] def Vsub (n c : ℕ) : Submodule K (Fin n → K) where
  carrier := {v | ∀ j : Fin n, c ≤ j.val → v j = 0}
  add_mem' := fun ha hb j hj => by simp [ha j hj, hb j hj]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun a _ hv j hj => by simp [hv j hj]

variable (K)

@[expose] noncomputable def hermLin (n lo hi : ℕ) (u : Fin n → K) : (Fin n → K) →ₗ[K] K :=
  ∑ i : Fin n, if lo ≤ i.val ∧ i.val < hi then (sg K f (u i)) • LinearMap.proj i else 0

@[expose] noncomputable def perpB (n lo hi : ℕ) (U : Submodule K (Fin n → K)) :
    Submodule K (Fin n → K) :=
  ⨅ (u : Fin n → K) (_ : u ∈ U), LinearMap.ker (hermLin K f n lo hi u)

structure FlagK (n : ℕ) where
  E : ℕ → Submodule K (Fin n → K)
  mono : Monotone E
  dim : ∀ j, j ≤ n → finrank K (E j) = j
  top : ∀ j, n ≤ j → E j = ⊤

@[expose] noncomputable def flagSys (m : ℕ) : ChamberSystem (Fin m) (FlagK K (m + 1)) where
  adj i x y := ∀ j, j ≠ i.val + 1 → x.E j = y.E j
  equivalence i := ⟨fun _ _ _ => rfl, fun h j hj => (h j hj).symm,
    fun h h' j hj => (h j hj).trans (h' j hj)⟩

variable {K}

@[expose] def farSet (n : ℕ) (d : List ℕ) : Set (FlagK K n) :=
  {x | ∀ i, i < d.length → ∀ j, j ≤ n →
    finrank K ↥(x.E j ⊓ Vsub n (d.getD i 0)) = j + d.getD i 0 - n}

variable (K)

@[expose] def blockU (n : ℕ) (d : List ℕ) (E : ℕ → Submodule K (Fin n → K)) (i r : ℕ) :
    Submodule K (Fin n → K) :=
  (E (n - d.getD (i + 1) 0 + r) ⊓ Vsub n (d.getD (i + 1) 0)) ⊔ Vsub n (d.getD i 0)

@[expose] noncomputable def blockOK (n : ℕ) (d : List ℕ) (pol : List Bool)
    (E : ℕ → Submodule K (Fin n → K)) (i : ℕ) : Prop :=
  ∀ r, r ≤ d.getD (i + 1) 0 - d.getD i 0 →
    if pol.getD i false then
      blockU K n d E i r ⊓ perpB K f n (d.getD i 0) (d.getD (i + 1) 0) (blockU K n d E i r) =
        Vsub n (d.getD i 0)
    else
      blockU K n d E i r ⊓ sgS K f n
        (blockU K n d E i (d.getD (i + 1) 0 - d.getD i 0 - r)) = Vsub n (d.getD i 0)

@[expose] noncomputable def genSet (n : ℕ) (d : List ℕ) (pol : List Bool) : Set (FlagK K n) :=
  {x | x ∈ farSet n d ∧ ∀ i, i + 1 < d.length → blockOK K f n d pol x.E i}

@[expose] noncomputable def set22x : Set (FlagK K 4) :=
  {x | x ∈ farSet 4 [0, 2, 4] ∧ blockU K 4 [0, 2, 4] x.E 1 1 ≠
    Vsub 4 2 ⊔ Submodule.span K ((fun v : Fin 4 → K => (![0, 0, sg K f (v 0), sg K f (v 1)] :
      Fin 4 → K)) '' (blockU K 4 [0, 2, 4] x.E 0 1 : Set (Fin 4 → K)))}

@[expose] noncomputable def setA2A1 : Set (FlagK K 3 × FlagK K 2) :=
  {c | c.1 ∈ farSet 3 [0, 1, 3] ∧ blockU K 3 [0, 1, 3] c.1.E 1 1 ≠
    Vsub 3 1 ⊔ Submodule.span K ((fun v : Fin 2 → K => (![0, sg K f (v 0), sg K f (v 1)] :
      Fin 3 → K)) '' ((c.2.E 1 : Submodule K (Fin 2 → K)) : Set (Fin 2 → K)))}

end Vocabulary

inductive PhanCode : Type
  | a1far | a1moved
  | a2chamber | a2panel | a2coll | a2pol
  | a3_1111 | a3_211 | a3_121 | a3_22p | a3_22x | a3_13c | a3_13p | a3_4c | a3_4p
  | exchA1A1 | exchA2A1
  | prod : PhanCode → PhanCode → PhanCode

namespace PhanCode

@[expose] def rank : PhanCode → ℕ
  | a1far | a1moved => 1
  | a2chamber | a2panel | a2coll | a2pol | exchA1A1 => 2
  | a3_1111 | a3_211 | a3_121 | a3_22p | a3_22x | a3_13c | a3_13p | a3_4c | a3_4p | exchA2A1 => 3
  | prod c c' => c.rank + c'.rank

@[expose] def ι : PhanCode → Type
  | a1far | a1moved => Fin 1
  | a2chamber | a2panel | a2coll | a2pol => Fin 2
  | a3_1111 | a3_211 | a3_121 | a3_22p | a3_22x | a3_13c | a3_13p | a3_4c | a3_4p => Fin 3
  | exchA1A1 => Fin 1 ⊕ Fin 1
  | exchA2A1 => Fin 2 ⊕ Fin 1
  | prod c c' => c.ι ⊕ c'.ι

variable (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]

@[expose] def Ω : PhanCode → Type
  | a1far | a1moved => FlagK K 2
  | a2chamber | a2panel | a2coll | a2pol => FlagK K 3
  | a3_1111 | a3_211 | a3_121 | a3_22p | a3_22x | a3_13c | a3_13p | a3_4c | a3_4p => FlagK K 4
  | exchA1A1 => FlagK K 2 × FlagK K 2
  | exchA2A1 => FlagK K 3 × FlagK K 2
  | prod c c' => c.Ω × c'.Ω

@[expose] noncomputable def sys : (c : PhanCode) → ChamberSystem c.ι (c.Ω K)
  | a1far | a1moved => flagSys K 1
  | a2chamber | a2panel | a2coll | a2pol => flagSys K 2
  | a3_1111 | a3_211 | a3_121 | a3_22p | a3_22x | a3_13c | a3_13p | a3_4c | a3_4p => flagSys K 3
  | exchA1A1 => (flagSys K 1).prod (flagSys K 1)
  | exchA2A1 => (flagSys K 2).prod (flagSys K 1)
  | prod c c' => c.sys.prod c'.sys

@[expose] noncomputable def set : (c : PhanCode) → Set (c.Ω K)
  | a1far => genSet K f 2 [0, 1, 2] []
  | a1moved => genSet K f 2 [0, 2] [false]
  | a2chamber => genSet K f 3 [0, 1, 2, 3] []
  | a2panel => genSet K f 3 [0, 1, 3] []
  | a2coll => genSet K f 3 [0, 3] [false]
  | a2pol => genSet K f 3 [0, 3] [true]
  | a3_1111 => genSet K f 4 [0, 1, 2, 3, 4] []
  | a3_211 => genSet K f 4 [0, 2, 3, 4] []
  | a3_121 => genSet K f 4 [0, 1, 3, 4] []
  | a3_22p => genSet K f 4 [0, 2, 4] []
  | a3_22x => set22x K f
  | a3_13c => genSet K f 4 [0, 1, 4] []
  | a3_13p => genSet K f 4 [0, 1, 4] [false, true]
  | a3_4c => genSet K f 4 [0, 4] [false]
  | a3_4p => genSet K f 4 [0, 4] [true]
  | exchA1A1 => {c | c.1.E 1 ≠ sgS K f 2 (c.2.E 1)}
  | exchA2A1 => setA2A1 K f
  | prod c c' => c.set ×ˢ c'.set

end PhanCode

end CFSG.ClassicalInvolution.Phan.PhanE

end
