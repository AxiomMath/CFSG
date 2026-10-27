module

public import CFSG.Sporadic.SuzOddCore.GraphArraysCheck
public import CFSG.Sporadic.SuzOddCore.Perms
public import CFSG.Blueprint.NativeSporadic

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def suzH0 : Subgroup (Equiv.Perm (Fin 22880)) :=
  Subgroup.closure {g | ∃ j ∈ certStabIdx, suzS j = g}

@[expose] def strongWord (w : List ℤ) : Equiv.Perm (Fin 22880) :=
  Quiver.SchreierGraph.evalWord (fun h : Fin 10 => suzS h) (toLetters 10 w)

@[expose] def suzZ : Equiv.Perm (Fin 22880) := strongWord zWord ^ zPower

@[expose] def suzQ : Subgroup (Equiv.Perm (Fin 22880)) := Subgroup.zpowers suzZ

@[expose] def suzDeltaΩ : Set (Fin 22880) := {i | suzZ i = i ∧ i ≠ 0}

@[expose] def suzGamma : SimpleGraph (Fin 22880) :=
  SimpleGraph.fromEdgeSet {e | ∃ g ∈ suzP, ∃ i ∈ suzDeltaΩ, e = s(g 0, g i)}

theorem suzDeltaΩ_ends_ne {g : Equiv.Perm (Fin 22880)} {i : Fin 22880} (hi : i ∈ suzDeltaΩ) :
    g 0 ≠ g i := fun h => hi.2 (g.injective h).symm

theorem suzGamma_adj (x y : Fin 22880) :
    suzGamma.Adj x y ↔ ∃ g ∈ suzP, ∃ i ∈ suzDeltaΩ,
      (g 0 = x ∧ g i = y) ∨ (g 0 = y ∧ g i = x) := by
  rw [suzGamma, SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨⟨g, hg, i, hi, he⟩, -⟩
    refine ⟨g, hg, i, hi, ?_⟩
    rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h2.symm, h1.symm⟩
  · rintro ⟨g, hg, i, hi, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨⟨g, hg, i, hi, rfl⟩, suzDeltaΩ_ends_ne hi⟩
    · exact ⟨⟨g, hg, i, hi, Sym2.eq_swap⟩, (suzDeltaΩ_ends_ne hi).symm⟩

@[expose] def localBase : List (Fin 280) := localBaseNat.map (pt 280)

theorem localBase_nodup : localBase.Nodup := by decide

theorem localGen_le_strong : localGenArrs.size ≤ localStrongArrs.size := by
  simp [localGenArrs, localStrongArrs]

@[expose] def localChain : RawSchreierDatum 280 :=
  rawOfArrays 280 (by norm_num) localGenArrs localStrongArrs localGen_le_strong localBase
    localBase_nodup localDerivs

@[expose] def fullExtList : ℕ → List (Equiv.Perm (Fin 22880))
  | 0 => localStrongIdx.map suzS
  | k + 1 =>
    let L := fullExtList k
    L ++ [Quiver.SchreierGraph.evalWord (fun h : Fin (8 + k) => L.getD h 1)
      (toLetters (8 + k) (localDerivs.getD (8 + k) []))]

@[expose] def fullExt (j : ℕ) : Equiv.Perm (Fin 22880) := (fullExtList 6).getD j 1

@[expose] def suzSylowT (i : ℕ) : Equiv.Perm (Fin 22880) :=
  Quiver.SchreierGraph.evalWord (fun h : Fin 14 => fullExt h)
    (toLetters 14 (sylowQuotWords.getD i []))

@[expose] def suzS3 : Subgroup (Equiv.Perm (Fin 22880)) :=
  Subgroup.closure (insert suzZ {g | ∃ i < 5, suzSylowT i = g})

@[expose] def centerFullPerm (r : ℕ) : Equiv.Perm (Fin 22880) := permC 22880 (centerFull r)

@[expose] def centerCompactPerm (r : ℕ) : Equiv.Perm (Fin 280) := permC 280 (centerCompact r)

@[expose] def suzOuter : Equiv.Perm (Fin 22880) := permC 22880 outerArr

@[expose] def suzR : Subgroup (Equiv.Perm (Fin 22880)) :=
  Subgroup.closure (insert suzOuter (suzP : Set (Equiv.Perm (Fin 22880))))

@[expose] def suzC : Matrix (Fin 64) (Fin 64) (ZMod 3) :=
  CFSG.Blueprint.NativeSporadic.decode 3 64 1 suzd2F3r64aM1Text

theorem rep_suzOuter : Rep 22880 outerArr suzOuter :=
  (rep_permC (Bool.and_eq_true_iff.1 graphArrays_check.1).2).1

theorem rep_centerFull
    {r : ℕ} (hr : r < 9) : Rep 22880 (centerFull r) (centerFullPerm r) :=
  (rep_permC (Bool.and_eq_true_iff.1 (graphArrays_check.2.2.1 r hr).1).2).1

theorem rep_centerCompact {r : ℕ} (hr : r < 9) :
    Rep 280 (centerCompact r) (centerCompactPerm r) :=
  (rep_permC (Bool.and_eq_true_iff.1 (graphArrays_check.2.2.1 r hr).2).2).1

end CFSG.Sporadic.SuzOddCore
