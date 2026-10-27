module

public import CFSG.Open.QuasithinDefs
public import CFSG.Quasithin.Recognition.CertF8

public section

open scoped MatrixGroups

namespace CFSG.Quasithin

open CFSG.Open

@[expose] def trialityElt (a : GF8) (s : Bool) : Matrix (Fin 8) (Fin 8) GF8 :=
  quasithinRootElt (quasithinD4Root 0 s) a * quasithinRootElt (quasithinD4Root 2 s) (a ^ 2) *
    quasithinRootElt (quasithinD4Root 3 s) (a ^ 4)

@[expose] def trialityMid (s : Bool) : Matrix (Fin 8) (Fin 8) GF8 :=
  quasithinRootElt (quasithinD4Root 1 s) 1

@[expose] def trialityGens8 : Set (Matrix (Fin 8) (Fin 8) GF8) :=
  {M | ∃ (a : GF8) (s : Bool), M = trialityElt a s} ∪ {M | ∃ s : Bool, M = trialityMid s}

@[expose] def trialityGroup8 : Subgroup (GL (Fin 8) GF8) :=
  Subgroup.closure {A | (A : Matrix (Fin 8) (Fin 8) GF8) ∈ trialityGens8}

noncomputable def gf8EquivGaloisField : GF8 ≃+* GaloisField 2 3 :=
  haveI : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, GaloisField.card 2 3 (by norm_num),
      Nat.card_eq_fintype_card]
    decide)

private theorem map_quasithinRootElt {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L)
    (pos : List (Fin 8 × Fin 8)) (t : K) :
    (quasithinRootElt pos t).map f = quasithinRootElt pos (f t) := by
  ext r c
  simp only [quasithinRootElt, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

private theorem map_rootProd {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L) (a : K)
    (s : Bool) :
    (quasithinRootElt (quasithinD4Root 0 s) a * quasithinRootElt (quasithinD4Root 2 s) (a ^ 2) *
      quasithinRootElt (quasithinD4Root 3 s) (a ^ 4)).map f =
    quasithinRootElt (quasithinD4Root 0 s) (f a) *
      quasithinRootElt (quasithinD4Root 2 s) (f a ^ 2) *
      quasithinRootElt (quasithinD4Root 3 s) (f a ^ 4) := by
  rw [Matrix.map_mul, Matrix.map_mul, map_quasithinRootElt, map_quasithinRootElt,
    map_quasithinRootElt, map_pow, map_pow]

private theorem coe_map_gl {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L)
    (A : GL (Fin 8) K) :
    ((Matrix.GeneralLinearGroup.map f A : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) =
      (A : Matrix (Fin 8) (Fin 8) K).map f := by
  simp [Matrix.GeneralLinearGroup.map]

theorem card_quasithinTrialityD4Two_eq :
    Nat.card quasithinTrialityD4Two = Nat.card trialityGroup8 := by
  let e := gf8EquivGaloisField
  let f : GaloisField 2 3 →+* GF8 := e.symm.toRingHom
  let g : GF8 →+* GaloisField 2 3 := e.toRingHom
  let ψ : GL (Fin 8) (GaloisField 2 3) →* GL (Fin 8) GF8 := Matrix.GeneralLinearGroup.map f
  have hinj : Function.Injective ψ := by
    refine Units.map_injective (f := (f.mapMatrix : Matrix (Fin 8) (Fin 8) (GaloisField 2 3) →+*
      Matrix (Fin 8) (Fin 8) GF8).toMonoidHom) ?_
    intro M N h
    exact Matrix.map_injective e.symm.injective h
  have hset : ψ '' {A : GL (Fin 8) (GaloisField 2 3) |
      (A : Matrix (Fin 8) (Fin 8) (GaloisField 2 3)) ∈ quasithinTrialityGens} =
      {A : GL (Fin 8) GF8 | (A : Matrix (Fin 8) (Fin 8) GF8) ∈ trialityGens8} := by
    ext B
    constructor
    · rintro ⟨A, hA, rfl⟩
      rcases hA with ⟨a, s, hs⟩ | ⟨s, hs⟩
      · refine Or.inl ⟨f a, s, ?_⟩
        show ((Matrix.GeneralLinearGroup.map f A : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = _
        rw [coe_map_gl, hs, map_rootProd]
        rfl
      · refine Or.inr ⟨s, ?_⟩
        show ((Matrix.GeneralLinearGroup.map f A : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = _
        rw [coe_map_gl, hs, map_quasithinRootElt, map_one]
        rfl
    · intro hB
      let A : GL (Fin 8) (GaloisField 2 3) := Matrix.GeneralLinearGroup.map g B
      have hA : (A : Matrix (Fin 8) (Fin 8) (GaloisField 2 3)) =
          (B : Matrix (Fin 8) (Fin 8) GF8).map g := coe_map_gl g B
      have hψA : ψ A = B := by
        apply Units.ext
        show ((Matrix.GeneralLinearGroup.map f A : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = _
        rw [coe_map_gl, hA, Matrix.map_map]
        ext i j
        simp [f, g]
      refine ⟨A, ?_, hψA⟩
      rcases hB with ⟨a, s, hs⟩ | ⟨s, hs⟩
      · refine Or.inl ⟨g a, s, ?_⟩
        rw [hA, hs]
        exact map_rootProd g a s
      · refine Or.inr ⟨s, ?_⟩
        rw [hA, hs]
        show (quasithinRootElt (quasithinD4Root 1 s) (1 : GF8)).map g = _
        rw [map_quasithinRootElt, map_one]
  have hmap : quasithinTrialityD4Two.map ψ = trialityGroup8 := by
    rw [quasithinTrialityD4Two, trialityGroup8, MonoidHom.map_closure, hset]
  rw [← hmap, Subgroup.card_map_of_injective hinj]

end CFSG.Quasithin
