module

public import CFSG.YGroups.Y443.Native.Words
public import CFSG.Monster.B.Short.AxisOrbit
public import Certificates.Data.CFSGNative.YGroups.Y443.AlignWords

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B CFSG.Monster.B.Short CFSG.YGroups.Y443Native

@[expose] def toGenA (r : Array ℕ) : Native.Gen :=
  match r[0]! with
  | 0 => .rho (r[1]! != 0, r[2]!, r[3]!)
  | 1 => .perm alignPerms[r[2]!]!
  | 2 => .xi
  | _ => .tau

@[expose] def omegaWord : List Native.Gen := alignLetters.map toGenA

@[expose] def tWord : List Native.Gen := [.rho (false, 0, 191)]

theorem wordLin_tWord : wordLin tWord = tStar := by
  have h1 : Model.dualN (2 ^ ((0 : Fin 24) : ℕ) ||| 2 ^ ((1 : Fin 24) : ℕ)) = 191 := by decide
  have h2 := Rep4371.pauliQ_minus (i := 0) (j := 1) (by decide)
  rw [h1] at h2
  show wordLin [Native.Gen.rho (false, 0, 191)] = tStar
  rw [wordLin_cons, wordLin_nil, one_mul, Native.Gen.toLin_rho]
  unfold tStar
  rw [rStar_eq_rMinus, ← h2]

@[expose] def slet : List ℕ :=
  (List.replicate 9 [0, 1, 2, 3, 5, 6, 9]).flatten ++
    (List.replicate 9 [0, 9, 10, 11, 1, 2, 5]).flatten

@[expose] def Lw (s : ℕ) : List Native.Gen := if s = 0 then [] else L (s - 1)

@[expose] def invWs (s : ℕ) : List Native.Gen := if s = 0 then [] else invW (s - 1)

@[expose] def pairUp : List ℕ → List (ℕ × ℕ)
  | a :: b :: l => (a, b) :: pairUp l
  | _ => []

@[expose] def pairFactor (p : ℕ × ℕ) : List Native.Gen := Lw p.2 ++ invWs p.1

@[expose] def wcWordOf (l : List ℕ) : List Native.Gen := ((pairUp l).map pairFactor).reverse.flatten

@[expose] def wcWord : List Native.Gen := wcWordOf slet

@[expose] def eqWords (w₁ w₂ : List Native.Gen) (v : Native.DVec) : Bool :=
  w₁.all Native.Gen.validB && w₂.all Native.Gen.validB &&
    (Native.evalWordC (Native.mkCtx ()) w₁ v).eqv (Native.evalWordC (Native.mkCtx ()) w₂ v)

theorem eqWords_sound {w₁ w₂ : List Native.Gen} {v : Native.DVec}
    (h : eqWords w₁ w₂ v = true) : wordLin w₁ (interp v) = wordLin w₂ (interp v) := by
  unfold eqWords at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hv₁, hv₂⟩, he⟩ := h
  have hw₁ : ∀ g ∈ w₁, g.validB = true := fun g hg => List.all_eq_true.1 hv₁ g hg
  have hw₂ : ∀ g ∈ w₂, g.validB = true := fun g hg => List.all_eq_true.1 hv₂ g hg
  rw [← evalWordC_sound w₁ hw₁ v, ← evalWordC_sound w₂ hw₂ v]
  exact eqv_sound he

theorem eq_of_eqWords
    {w₁ w₂ : List Native.Gen} (ha : eqWords w₁ w₂ (aV ()) = true)
    (hb : eqWords w₁ w₂ (bV ()) = true) (hw : eqWords w₁ w₂ (wV ()) = true) :
    wordLin w₁ = wordLin w₂ := by
  have key : (wordLin w₂)⁻¹ * wordLin w₁ = 1 := by
    refine separation_witnesses _ (mul_mem (inv_mem (wordLin_mem_Gmat w₂)) (wordLin_mem_Gmat w₁))
      ?_ ?_ ?_
    · show (wordLin w₂)⁻¹ (wordLin w₁ (interp (aV ()))) = interp (aV ())
      rw [eqWords_sound ha]
      exact LinearEquiv.symm_apply_apply _ _
    · show (wordLin w₂)⁻¹ (wordLin w₁ (interp (bV ()))) = interp (bV ())
      rw [eqWords_sound hb]
      exact LinearEquiv.symm_apply_apply _ _
    · show (wordLin w₂)⁻¹ (wordLin w₁ (interp (wV ()))) = interp (wV ())
      rw [eqWords_sound hw]
      exact LinearEquiv.symm_apply_apply _ _
  exact (inv_mul_eq_one.1 key).symm

end CFSG.YGroups.Y443
