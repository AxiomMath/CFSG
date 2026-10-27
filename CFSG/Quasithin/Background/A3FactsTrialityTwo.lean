module

public import CFSG.Quasithin.Recognition.CertD4Bridge
public import CFSG.Quasithin.Background.A3FactsA134

public section

open scoped MatrixGroups

namespace CFSG.Quasithin

namespace A3Facts

open CFSG.Open (quasithinRootElt quasithinD4Root quasithinTrialityD4Two)
open CFSG.Blueprint CFSG.Blueprint.Chevalley

@[expose] def d4Gen (s : Bool) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  quasithinRootElt (quasithinD4Root 0 s) 1 * quasithinRootElt (quasithinD4Root 2 s) 1 *
    quasithinRootElt (quasithinD4Root 3 s) 1

@[expose] def d4GenInv (s : Bool) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  quasithinRootElt (quasithinD4Root 3 s) 1 * quasithinRootElt (quasithinD4Root 2 s) 1 *
    quasithinRootElt (quasithinD4Root 0 s) 1

@[expose] def d4Mid (s : Bool) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  quasithinRootElt (quasithinD4Root 1 s) 1

theorem d4Gen_mul_inv : ∀ s : Bool, d4Gen s * d4GenInv s = 1 ∧ d4GenInv s * d4Gen s = 1 := by
  decide +kernel

theorem d4Mid_mul_self : ∀ s : Bool, d4Mid s * d4Mid s = 1 := by
  decide +kernel

@[expose] def d4GenU (s : Bool) : GL (Fin 8) (ZMod 2) :=
  Units.mk (d4Gen s) (d4GenInv s) (d4Gen_mul_inv s).1 (d4Gen_mul_inv s).2

@[expose] def d4MidU (s : Bool) : GL (Fin 8) (ZMod 2) :=
  Units.mk (d4Mid s) (d4Mid s) (d4Mid_mul_self s) (d4Mid_mul_self s)

@[expose] def wX : Matrix (Fin 8) (Fin 8) (ZMod 2) := d4Gen true * d4Gen false

@[expose] def wY : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  d4Gen true * d4Mid true * d4Gen true * d4Mid true * d4Gen true * d4Mid false *
    d4Gen false * d4Gen true * d4Mid true * d4Mid false * d4Gen false * d4Mid false

theorem wX_cube : wX * wX * wX = 1 := by decide +kernel

theorem wY_cube : wY * wY * wY = 1 := by decide +kernel

theorem wXY_comm : wX * wY = wY * wX := by decide +kernel

theorem wX_ne_one : wX ≠ 1 := by decide +kernel

theorem wY_ne_one : wY ≠ 1 := by decide +kernel

theorem wY_ne_wX : wY ≠ wX := by decide +kernel

theorem wY_ne_wX_sq : wY ≠ wX * wX := by decide +kernel

@[expose] def d4X : GL (Fin 8) (ZMod 2) := d4GenU true * d4GenU false

@[expose] def d4Y : GL (Fin 8) (ZMod 2) :=
  d4GenU true * d4MidU true * d4GenU true * d4MidU true * d4GenU true * d4MidU false *
    d4GenU false * d4GenU true * d4MidU true * d4MidU false * d4GenU false * d4MidU false

theorem coe_d4X : (d4X : Matrix (Fin 8) (Fin 8) (ZMod 2)) = wX := rfl

theorem coe_d4Y : (d4Y : Matrix (Fin 8) (Fin 8) (ZMod 2)) = wY := rfl

theorem d4X_pow_three : d4X ^ 3 = 1 := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, coe_d4X, Units.val_one, pow_three']
  exact wX_cube

theorem d4Y_pow_three : d4Y ^ 3 = 1 := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, coe_d4Y, Units.val_one, pow_three']
  exact wY_cube

theorem d4X_comm : d4X * d4Y = d4Y * d4X := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_d4X, coe_d4Y]
  exact wXY_comm

theorem d4X_ne_one : d4X ≠ 1 := fun h =>
  wX_ne_one (by simpa [coe_d4X] using congrArg Units.val h)

theorem d4Y_ne_one : d4Y ≠ 1 := fun h =>
  wY_ne_one (by simpa [coe_d4Y] using congrArg Units.val h)

theorem d4X_pow_ne (n : ℕ) : d4X ^ n ≠ d4Y := by
  intro h
  rw [pow_eq_pow_mod n d4X_pow_three] at h
  have hn : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  have h' := congrArg Units.val h
  rcases hn with h0 | h1 | h2
  · rw [h0, pow_zero, Units.val_one, coe_d4Y] at h'
    exact wY_ne_one h'.symm
  · rw [h1, pow_one, coe_d4X, coe_d4Y] at h'
    exact wY_ne_wX h'.symm
  · rw [h2, pow_two, Units.val_mul, coe_d4X, coe_d4Y] at h'
    exact wY_ne_wX_sq h'.symm

section Transport

noncomputable def d4φ : ZMod 2 →+* GaloisField 2 3 := ZMod.castHom (dvd_refl 2) (GaloisField 2 3)

noncomputable def d4ψ : GL (Fin 8) (ZMod 2) →* GL (Fin 8) (GaloisField 2 3) :=
  Matrix.GeneralLinearGroup.map d4φ

theorem d4ψ_injective : Function.Injective d4ψ := by
  refine Units.map_injective (f := (d4φ.mapMatrix : Matrix (Fin 8) (Fin 8) (ZMod 2) →+*
    Matrix (Fin 8) (Fin 8) (GaloisField 2 3)).toMonoidHom) ?_
  intro M N h
  exact Matrix.map_injective d4φ.injective h

theorem coe_d4ψ (A : GL (Fin 8) (ZMod 2)) :
    ((d4ψ A : GL (Fin 8) (GaloisField 2 3)) : Matrix (Fin 8) (Fin 8) (GaloisField 2 3)) =
      (A : Matrix (Fin 8) (Fin 8) (ZMod 2)).map d4φ := by
  simp [d4ψ, Matrix.GeneralLinearGroup.map]

theorem map_rootElt {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L)
    (pos : List (Fin 8 × Fin 8)) (t : K) :
    (quasithinRootElt pos t).map f = quasithinRootElt pos (f t) := by
  ext r c
  simp only [quasithinRootElt, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem d4ψ_genU_mem (s : Bool) : d4ψ (d4GenU s) ∈ quasithinTrialityD4Two := by
  refine Subgroup.subset_closure (Or.inl ⟨1, s, ?_⟩)
  show ((d4ψ (d4GenU s) : GL (Fin 8) (GaloisField 2 3)) :
    Matrix (Fin 8) (Fin 8) (GaloisField 2 3)) = _
  rw [coe_d4ψ]
  change (d4Gen s).map d4φ = _
  simp only [d4Gen, Matrix.map_mul, map_rootElt, map_one, one_pow]

theorem d4ψ_midU_mem (s : Bool) : d4ψ (d4MidU s) ∈ quasithinTrialityD4Two := by
  refine Subgroup.subset_closure (Or.inr ⟨s, ?_⟩)
  show ((d4ψ (d4MidU s) : GL (Fin 8) (GaloisField 2 3)) :
    Matrix (Fin 8) (Fin 8) (GaloisField 2 3)) = _
  rw [coe_d4ψ]
  change (d4Mid s).map d4φ = _
  simp only [d4Mid, map_rootElt, map_one]

theorem d4ψ_X_mem : d4ψ d4X ∈ quasithinTrialityD4Two := by
  rw [d4X, map_mul]
  exact mul_mem (d4ψ_genU_mem true) (d4ψ_genU_mem false)

theorem d4ψ_Y_mem : d4ψ d4Y ∈ quasithinTrialityD4Two := by
  have hE1 := d4ψ_genU_mem true
  have hE0 := d4ψ_genU_mem false
  have hM1 := d4ψ_midU_mem true
  have hM0 := d4ψ_midU_mem false
  simp only [d4Y, map_mul]
  exact (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
    (mul_mem (mul_mem hE1 hM1) hE1) hM1) hE1) hM0) hE0) hE1) hM1) hM0) hE0) hM0)

theorem oddRankTwo_quasithinTrialityD4Two : OddRankTwo quasithinTrialityD4Two := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (GL (Fin 8) (GaloisField 2 3)) :=
    Finite.of_injective Units.val Units.val_injective
  refine ⟨3, Nat.prime_three, by norm_num, two_le_pRank_of_gens
    (x := (⟨d4ψ d4X, d4ψ_X_mem⟩ : quasithinTrialityD4Two))
    (y := (⟨d4ψ d4Y, d4ψ_Y_mem⟩ : quasithinTrialityD4Two)) ?_ ?_ ?_ ?_ ?_⟩
  · refine Subtype.ext ?_
    change d4ψ d4X ^ 3 = 1
    rw [← map_pow, d4X_pow_three, map_one]
  · refine Subtype.ext ?_
    change d4ψ d4Y ^ 3 = 1
    rw [← map_pow, d4Y_pow_three, map_one]
  · refine Subtype.ext ?_
    change d4ψ d4X * d4ψ d4Y = d4ψ d4Y * d4ψ d4X
    rw [← map_mul, ← map_mul, d4X_comm]
  · intro h
    refine d4X_ne_one (d4ψ_injective ?_)
    have h' := congrArg Subtype.val h
    change d4ψ d4X = 1 at h'
    rw [h', map_one]
  · intro n h
    refine d4X_pow_ne n (d4ψ_injective ?_)
    have h' := congrArg Subtype.val h
    change d4ψ d4X ^ n = d4ψ d4Y at h'
    rw [← map_pow] at h'
    exact h'

end Transport

theorem trialityTwoOddRankTwo
    : TrialityTwoOddRankTwo := by
  intro S _ _ h
  have hL : LieModel S .trialityD4 0 2 1 := Or.inr (Or.inl ⟨rfl, by decide, h⟩)
  obtain ⟨e⟩ := trialityD4ModelBridge_of_lieModel S hL
  have : Finite (GL (Fin 8) (GaloisField 2 3)) :=
    Finite.of_injective Units.val Units.val_injective
  exact OddRankTwo.of_mulEquiv e oddRankTwo_quasithinTrialityD4Two

theorem rankOneList
    : RankOneList :=
  rankOneList_of_triality_two trialityTwoOddRankTwo

end A3Facts

end CFSG.Quasithin
