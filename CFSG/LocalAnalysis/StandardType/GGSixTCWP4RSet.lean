module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RDict
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs2
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Flag
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Orbit
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4TwistOuter

public section

namespace CFSG.StandardType.TableCRes

open Certificates.TcRes CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Assembly (LargeEvenLabel LargeEvenLieTag LargeEvenSplit LargeEvenHalfSplit
  LargeEvenUntwisted LargeEvenInLambda2)

@[expose] def tcrSet (S : TcrSys) (τ : Tag) (c : List ℕ) : Set (Fin τ.rank → ℤ) :=
  {γ | ∃ i ∈ c, i < S.tcrN ∧ tcrRv S τ i = γ}

end CFSG.StandardType.TableCRes

namespace CFSG.StandardType.TableCRes

open Certificates.TcRes

theorem tcr_set_getElem! (a : Array Bool) (b w : ℕ) :
    (a.set! b true)[w]! = true ↔ (b < a.size ∧ w = b) ∨ a[w]! = true := by
  by_cases hw : w = b
  · rw [hw]
    by_cases hb : b < a.size
    · simp [hb]
    · have h1 : ¬ b < (a.set! b true).size := by rwa [Array.size_set!]
      rw [getElem!_neg (a.set! b true) b h1, getElem!_neg a b hb]
      simp [hb]
  · rw [Array.getElem!_set!_ne a b w true (Ne.symm hw)]
    simp [hw]

theorem tcr_replicate_getElem! (n i : ℕ) : (Array.replicate n false)[i]! = false := by
  by_cases h : i < n
  · rw [getElem!_pos (Array.replicate n false) i (by simpa using h)]
    simp
  · rw [getElem!_neg (Array.replicate n false) i (by simpa using h)]
    rfl

theorem tcrSetFold_getElem! (l : List ℕ) : ∀ (a : Array Bool) (i : ℕ),
    (l.foldl (fun a i => a.set! i true) a)[i]! = true ↔ (i < a.size ∧ i ∈ l) ∨ a[i]! = true := by
  induction l with
  | nil => intro a i; simp
  | cons x l ih =>
    intro a i
    simp only [List.foldl_cons]
    rw [ih, tcr_set_getElem!, Array.size_set!, List.mem_cons]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | h)
      · exact Or.inl ⟨h1, Or.inr h2⟩
      · exact Or.inl ⟨by omega, Or.inl h2⟩
      · exact Or.inr h
    · rintro (⟨h1, h2 | h2⟩ | h)
      · exact Or.inr (Or.inl ⟨by omega, h2⟩)
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr (Or.inr h)

theorem tcrMaskOf_getElem! (n : ℕ) (l : List ℕ) (i : ℕ) :
    (tcrMaskOf n l)[i]! = true ↔ i < n ∧ i ∈ l := by
  unfold tcrMaskOf
  rw [tcrSetFold_getElem!, Array.size_replicate, tcr_replicate_getElem!]
  simp

theorem tcrFold_size (l : List ℕ) : ∀ (a : Array Bool),
    (l.foldl (fun a i => a.set! i true) a).size = a.size := by
  induction l with
  | nil => intro a; rfl
  | cons x l ih => intro a; simp only [List.foldl_cons]; rw [ih, Array.size_set!]

theorem tcrMaskOf_size (n : ℕ) (l : List ℕ) : (tcrMaskOf n l).size = n := by
  unfold tcrMaskOf
  rw [tcrFold_size, Array.size_replicate]

end CFSG.StandardType.TableCRes

end
