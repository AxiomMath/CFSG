module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafGen

public section

namespace CFSG.StandardType.ClassicalPosition.NbrLeaf

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.ClassicalPosition

open scoped commutatorElement

local notation "Ix" n:max => (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
local notation "Mx" n:max f:max => Matrix (Ix n) (Ix n) (GaloisField 2 f)
set_option quotPrecheck false in
local notation "UK" n:max f:max => (ggU .POmegaMinus n f).K
set_option quotPrecheck false in
local notation "ρm" n:max f:max => Spin.spinMatrix
  (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
set_option quotPrecheck false in
local notation "Gm" n:max f:max => LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin
  (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))
local notation "AdS" f:max S:max => Algebra.adjoin (GaloisField 2 f) (Units.val '' S)
local notation "Fadj" n:max f:max e:max => formAdj (RingHom.id (GaloisField 2 f)) (Gm n f) e
local notation "BlkC" n:max f:max S:max ε:max =>
  (glBlockCentralizer (ρm n f) S ε : Subgroup (UK n f))
local notation "rk" f:max e:max =>
  Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e))

theorem nbrpmmx_isPrimIdemIn_formAdj (n f : ℕ) (S' : Set (GL (Ix n) (GaloisField 2 f)))
    (hSU' : ∀ s ∈ S', s ∈ (ρm n f).range) (hS' : ∀ s ∈ S', ∀ s'' ∈ S', Commute s s'')
    {e' : Mx n f} (he' : IsPrimIdemIn (AdS f S') e') :
    IsPrimIdemIn (AdS f S') (Fadj n f e') := by
  have hG : IsUnit (Gm n f).det := gram_det n f
  have hSU'_iso : ∀ s ∈ S',
      Matrix.transpose ((s : Mx n f).map (RingHom.id (GaloisField 2 f))) * Gm n f *
        (s : Mx n f) = Gm n f :=
    fun s hs => gram_iso n f (hSU' s hs)
  have hGh : Matrix.transpose ((Gm n f).map (RingHom.id (GaloisField 2 f))) = Gm n f :=
    gram_transpose n f
  have hA'comm : ∀ {a b : Mx n f}, a ∈ AdS f S' → b ∈ AdS f S' → a * b = b * a :=
    fun ha hb => (adjoin_comm hS' _ ha _ hb).eq
  refine ⟨Geo.formAdj_mem_adjoin (RingHom.id (GaloisField 2 f)) hG hSU'_iso he'.1, ?_, ?_, ?_⟩
  · rw [IsIdempotentElem, ← Geo.formAdj_mul (RingHom.id (GaloisField 2 f)) hG e' e',
      he'.2.1.eq]
  · intro h0
    have h := congrArg (formAdj (RingHom.id (GaloisField 2 f)) (Gm n f)) h0
    rw [Geo.formAdj_formAdj (RingHom.id (GaloisField 2 f)) (fun x => rfl) hG hGh e',
      show Fadj n f 0 = 0 by simp [formAdj]] at h
    exact he'.2.2.1 h
  · intro x hx hxidem hxe
    have hx' : Fadj n f x ∈ AdS f S' :=
      Geo.formAdj_mem_adjoin (RingHom.id (GaloisField 2 f)) hG hSU'_iso hx
    have hx'idem : IsIdempotentElem (Fadj n f x) := by
      rw [IsIdempotentElem, ← Geo.formAdj_mul (RingHom.id (GaloisField 2 f)) hG x x,
        hxidem.eq]
    have hx'e : Fadj n f x * e' = Fadj n f x := by
      have h := congrArg (formAdj (RingHom.id (GaloisField 2 f)) (Gm n f)) hxe
      rw [Geo.formAdj_mul (RingHom.id (GaloisField 2 f)) hG x (Fadj n f e'),
        Geo.formAdj_formAdj (RingHom.id (GaloisField 2 f)) (fun x => rfl) hG hGh e'] at h
      rw [hA'comm hx' he'.1]
      exact h
    rcases he'.2.2.2 (Fadj n f x) hx' hx'idem hx'e with h | h
    · left
      have h2 := congrArg (formAdj (RingHom.id (GaloisField 2 f)) (Gm n f)) h
      rw [Geo.formAdj_formAdj (RingHom.id (GaloisField 2 f)) (fun x => rfl) hG hGh x,
        show Fadj n f 0 = 0 by simp [formAdj]] at h2
      exact h2
    · right
      have h2 := congrArg (formAdj (RingHom.id (GaloisField 2 f)) (Gm n f)) h
      rw [Geo.formAdj_formAdj (RingHom.id (GaloisField 2 f)) (fun x => rfl) hG hGh x] at h2
      exact h2

end CFSG.StandardType.ClassicalPosition.NbrLeaf
