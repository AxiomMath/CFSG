
module

public import CFSG.Quasithin.Vol2.KGFactC31RuScanData
public import CFSG.Quasithin.Vol2.KGFactC31RuRefDefs
public import CFSG.Quasithin.Vol2.KGFactC31RuReps

public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.RuSchreier CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
  CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native

@[expose] noncomputable def refU (τ : ℕ) : Subgroup (Equiv.Perm (Fin 4060)) :=
  [uE, u64, u3, u16, u32].getD τ ⊥

@[expose] noncomputable def refG (τ : ℕ) : List (Equiv.Perm (Fin 4060)) :=
  [List.ofFn vE, List.ofFn v64, List.ofFn v3, List.ofFn v16, List.ofFn v32].getD τ []

@[expose] noncomputable def candElts (c : ℕ × List ℤ) : List (Equiv.Perm (Fin 4060)) :=
  (refG c.1).map fun b => wG c.2 * b * (wG c.2)⁻¹

@[expose] noncomputable def candsG (i p : ℕ) : List (List (Equiv.Perm (Fin 4060))) :=
  ((candData.getD i []).filter fun c => refPrime c.1 == p).map candElts

@[expose] noncomputable def cosetH (i : ℕ) : Equiv.Perm (Fin 4060) := abG (cosetWords.getD i [])

@[expose] def ruGroups : List (List ℕ × ℕ) := [([125], 5), ([7], 7), ([13, 29], 0)]

@[expose] def CandConcl (i : ℕ) (y τ : Equiv.Perm (Fin 4060)) (es : List ℕ) (q : ℕ) : Prop :=
  (∃ e ∈ es, y ^ e = 1) → (∀ j : ℕ, τ * (y ^ j * τ * (y ^ j)⁻¹) = y ^ j * τ * (y ^ j)⁻¹ * τ) →
    ∃ cg ∈ candsG i q, (∀ x ∈ cg, x ∈ orbSub y τ) ∧
      ∀ x ∈ cg, y * x * y⁻¹ ∈ Subgroup.closure {x | x ∈ cg}

end CFSG.Quasithin.KGC31.Ru

end
