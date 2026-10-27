module

public import CFSG.RankThree.PartOne.N143.O7Data
public import CFSG.RankThree.PartOne.K159.CoverLift

public section

namespace CFSG.RankThree.PartOne.N143.O7

open Matrix

set_option maxRecDepth 100000

section Generic

variable {R : Type} [CommRing R]

@[expose] def vecR (a0 a1 a2 b0 b1 b2 c : R) : Idx → R
  | .inl 0 => a0 | .inl 1 => a1 | .inl 2 => a2
  | .inr (.inl 0) => b0 | .inr (.inl 1) => b1 | .inr (.inl 2) => b2
  | .inr (.inr _) => c

@[expose] def qfR (v : Idx → R) : R :=
  v (.inl 0) * v (.inr (.inl 0)) + v (.inl 1) * v (.inr (.inl 1)) +
    v (.inl 2) * v (.inr (.inl 2)) + v (.inr (.inr ())) ^ 2

@[expose] def gvR (v : Idx → R) : Idx → R
  | .inl k => v (.inr (.inl k))
  | .inr (.inl k) => v (.inl k)
  | .inr (.inr _) => 2 * v (.inr (.inr ()))

@[expose] def eichR (x w : Idx → R) : Matrix Idx Idx R :=
  Matrix.of fun a b => (if a = b then 1 else 0) + w a * gvR x b - x a * gvR w b - qfR w * x a * gvR x b

@[expose] def eMR (a0 a1 a2 : R) : Matrix Idx Idx R :=
  eichR (vecR 1 0 0 0 0 0 0) (vecR 0 a2 (a0 + a2) 0 (-a2) (a1 + a2) 0)

set_option maxHeartbeats 2000000 in
theorem eMR_add (a0 a1 a2 b0 b1 b2 : R) :
    eMR (a0 + b0) (a1 + b1) (a2 + b2) = eMR a0 a1 a2 * eMR b0 b1 b2 := by
  ext i j
  simp only [eMR, eichR, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three,
    Finset.univ_unique, Finset.sum_singleton, Matrix.of_apply]
  rcases i with (i | i | i) <;> rcases j with (j | j | j) <;>
    (try fin_cases i) <;> (try fin_cases j) <;>
    simp [vecR, qfR, gvR] <;> ring

end Generic

@[expose] def eM (a : Fin 3 → ZMod 3) : Matrix Idx Idx (ZMod 3) := eMR (a 0) (a 1) (a 2)

theorem eM_add (a b : Fin 3 → ZMod 3) : eM (a + b) = eM a * eM b := eMR_add _ _ _ _ _ _

theorem eM_zero : eM 0 = 1 := by decide +kernel

theorem eM_neg_mul (a : Fin 3 → ZMod 3) : eM a * eM (-a) = 1 := by
  have h : a + -a = 0 := by funext i; exact add_neg_cancel (a i)
  rw [← eM_add, h, eM_zero]

theorem eM_neg_mul' (a : Fin 3 → ZMod 3) : eM (-a) * eM a = 1 := by
  have h : -a + a = 0 := by funext i; exact neg_add_cancel (a i)
  rw [← eM_add, h, eM_zero]

@[expose] def thetaGL : Multiplicative (Fin 3 → ZMod 3) →* GL Idx (ZMod 3) where
  toFun a := ⟨eM a.toAdd, eM (-a.toAdd), eM_neg_mul _, eM_neg_mul' _⟩
  map_one' := Units.ext (by simpa using eM_zero)
  map_mul' a b := Units.ext (by simpa using eM_add a.toAdd b.toAdd)

theorem thetaGL_val (a : Multiplicative (Fin 3 → ZMod 3)) :
    ((thetaGL a : GL Idx (ZMod 3)) : Matrix Idx Idx (ZMod 3)) = eM a.toAdd := rfl

@[expose] def gen (j : Fin 3) : GL Idx (ZMod 3) := thetaGL (.ofAdd (Pi.single j 1))

theorem gen_val (j : Fin 3) : ((gen j : GL Idx (ZMod 3)) : Matrix Idx Idx (ZMod 3)) = eM (Pi.single j 1) := rfl

theorem gen_gram : ∀ j : Fin 3, (eM (Pi.single j 1))ᵀ * gramM * eM (Pi.single j 1) = gramM := by
  decide +kernel

theorem gen_mem_iso (j : Fin 3) : gen j ∈ Iso :=
  mem_iso_of_gram (by rw [gen_val]; exact gen_gram j)

theorem hGL_inv : ∀ j : Fin 3, (hGL : Matrix Idx Idx (ZMod 3)) * eM (Pi.single j 1) =
    eM (Pi.single j 1) * eM (Pi.single j 1) * (hGL : Matrix Idx Idx (ZMod 3)) := by
  decide +kernel

theorem gen_mem_om (j : Fin 3) : gen j ∈ Om :=
  mem_om_of_inverted (gen_mem_iso j) (om_le_iso hGL_mem)
    (Units.ext (by simp only [Units.val_mul, gen_val]; exact hGL_inv j))

theorem range_thetaGL : thetaGL.range = Subgroup.closure (Set.range gen) := by
  have h1 : (Subgroup.closure (Set.range fun j : Fin 3 =>
      (Multiplicative.ofAdd (Pi.single j (1 : ZMod 3)) :
        Multiplicative (Fin 3 → ZMod 3)))).map thetaGL = Subgroup.closure (Set.range gen) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  rw [← h1, CFSG.RankThree.PartOne.K159.closure_range_ofAdd_single, ← MonoidHom.range_eq_map]

theorem thetaGL_mem_om (a : Multiplicative (Fin 3 → ZMod 3)) : thetaGL a ∈ Om := by
  have : thetaGL a ∈ thetaGL.range := ⟨a, rfl⟩
  rw [range_thetaGL] at this
  exact (Subgroup.closure_le Om).2 (by rintro _ ⟨j, rfl⟩; exact gen_mem_om j) this

theorem eM_eq_one : ∀ a : Fin 3 → ZMod 3, eM a = 1 → a = 0 := by decide +kernel

theorem thetaGL_injective : Function.Injective thetaGL := by
  refine (injective_iff_map_eq_one thetaGL).2 fun a ha => ?_
  have h : eM a.toAdd = 1 := by
    have := congrArg (fun u : GL Idx (ZMod 3) => (u : Matrix Idx Idx (ZMod 3))) ha
    simpa [thetaGL_val] using this
  exact Multiplicative.toAdd.injective (eM_eq_one _ h)

@[expose] def thetaOm : Multiplicative (Fin 3 → ZMod 3) →* ↥Om :=
  thetaGL.codRestrict Om thetaGL_mem_om

theorem thetaOm_injective : Function.Injective thetaOm := fun _ _ h =>
  thetaGL_injective (congrArg Subtype.val h)

@[expose] def s12Om : ↥Om := ⟨s12GL, s12GL_mem⟩
@[expose] def s13Om : ↥Om := ⟨s13GL, s13GL_mem⟩
@[expose] def s23Om : ↥Om := ⟨s23GL, s23GL_mem⟩
@[expose] def hOm : ↥Om := ⟨hGL, hGL_mem⟩
@[expose] def tOm : ↥Om := ⟨tGL, tGL_mem⟩

theorem swap_of (s : ↥Om) (j k : Fin 3)
    (h1 : ((s : GL Idx (ZMod 3)) : Matrix Idx Idx (ZMod 3)) * eM (Pi.single j 1) =
      eM (Pi.single k 1) * ((s : GL Idx (ZMod 3)) : Matrix Idx Idx (ZMod 3)))
    (h2 : ((s : GL Idx (ZMod 3)) : Matrix Idx Idx (ZMod 3)) * eM (Pi.single k 1) =
      eM (Pi.single j 1) * ((s : GL Idx (ZMod 3)) : Matrix Idx Idx (ZMod 3))) :
    s * thetaOm (.ofAdd (Pi.single j 1)) * s⁻¹ = thetaOm (.ofAdd (Pi.single k 1)) ∧
      s * thetaOm (.ofAdd (Pi.single k 1)) * s⁻¹ = thetaOm (.ofAdd (Pi.single j 1)) := by
  refine ⟨?_, ?_⟩
  · rw [mul_inv_eq_iff_eq_mul]
    exact Subtype.ext (Units.ext (by simpa [thetaOm, thetaGL_val] using h1))
  · rw [mul_inv_eq_iff_eq_mul]
    exact Subtype.ext (Units.ext (by simpa [thetaOm, thetaGL_val] using h2))

theorem swap12 : ((s12GL : GL Idx (ZMod 3)) : Matrix Idx Idx (ZMod 3)) * eM (Pi.single 0 1) =
      eM (Pi.single 1 1) * (s12GL : Matrix Idx Idx (ZMod 3)) ∧
    ((s12GL : GL Idx (ZMod 3)) : Matrix Idx Idx (ZMod 3)) * eM (Pi.single 1 1) =
      eM (Pi.single 0 1) * (s12GL : Matrix Idx Idx (ZMod 3)) := by decide +kernel

theorem swap13 : ((s13GL : GL Idx (ZMod 3)) : Matrix Idx Idx (ZMod 3)) * eM (Pi.single 0 1) =
      eM (Pi.single 2 1) * (s13GL : Matrix Idx Idx (ZMod 3)) ∧
    ((s13GL : GL Idx (ZMod 3)) : Matrix Idx Idx (ZMod 3)) * eM (Pi.single 2 1) =
      eM (Pi.single 0 1) * (s13GL : Matrix Idx Idx (ZMod 3)) := by decide +kernel

theorem swap23 : ((s23GL : GL Idx (ZMod 3)) : Matrix Idx Idx (ZMod 3)) * eM (Pi.single 1 1) =
      eM (Pi.single 2 1) * (s23GL : Matrix Idx Idx (ZMod 3)) ∧
    ((s23GL : GL Idx (ZMod 3)) : Matrix Idx Idx (ZMod 3)) * eM (Pi.single 2 1) =
      eM (Pi.single 1 1) * (s23GL : Matrix Idx Idx (ZMod 3)) := by decide +kernel

theorem thetaOm_swap : ∀ j k : Fin 3, j ≠ k → ∃ w : ↥Om,
    w * thetaOm (.ofAdd (Pi.single j 1)) * w⁻¹ = thetaOm (.ofAdd (Pi.single k 1)) ∧
      w * thetaOm (.ofAdd (Pi.single k 1)) * w⁻¹ = thetaOm (.ofAdd (Pi.single j 1)) := by
  intro j k hjk
  fin_cases j <;> fin_cases k
  · exact absurd rfl hjk
  · exact ⟨s12Om, swap_of s12Om 0 1 swap12.1 swap12.2⟩
  · exact ⟨s13Om, swap_of s13Om 0 2 swap13.1 swap13.2⟩
  · exact ⟨s12Om, (swap_of s12Om 0 1 swap12.1 swap12.2).symm⟩
  · exact absurd rfl hjk
  · exact ⟨s23Om, swap_of s23Om 1 2 swap23.1 swap23.2⟩
  · exact ⟨s13Om, (swap_of s13Om 0 2 swap13.1 swap13.2).symm⟩
  · exact ⟨s23Om, (swap_of s23Om 1 2 swap23.1 swap23.2).symm⟩
  · exact absurd rfl hjk

theorem thetaOm_inv : ∀ j : Fin 3, ∃ w : ↥Om,
    w * thetaOm (.ofAdd (Pi.single j 1)) * w⁻¹ = (thetaOm (.ofAdd (Pi.single j 1)))⁻¹ := by
  intro j
  refine ⟨hOm, ?_⟩
  set g : Multiplicative (Fin 3 → ZMod 3) := .ofAdd (Pi.single j 1) with hg
  have h3 : g * g * g = 1 := by
    apply Multiplicative.toAdd.injective
    funext i
    simp only [toAdd_mul, toAdd_one, hg, toAdd_ofAdd, Pi.add_apply, Pi.zero_apply]
    generalize (Pi.single j (1 : ZMod 3) : Fin 3 → ZMod 3) i = x
    revert x
    decide +kernel
  have h3' : thetaOm g * thetaOm g * thetaOm g = 1 := by
    have := congrArg thetaOm h3
    simpa [map_mul] using this
  have hinv : (thetaOm g)⁻¹ = thetaOm g * thetaOm g :=
    inv_eq_of_mul_eq_one_right ((mul_assoc _ _ _).symm.trans h3')
  rw [hinv, mul_inv_eq_iff_eq_mul]
  exact Subtype.ext (Units.ext (by simpa [thetaOm, thetaGL_val, hg, hOm] using hGL_inv j))

theorem tGL_ne_one : ((tGL : GL Idx (ZMod 3)) : Matrix Idx Idx (ZMod 3)) ≠ 1 := by decide +kernel

theorem tGL_sq : ((tGL : GL Idx (ZMod 3)) : Matrix Idx Idx (ZMod 3)) *
    ((tGL : GL Idx (ZMod 3)) : Matrix Idx Idx (ZMod 3)) = 1 := by decide +kernel

theorem tGL_gen : ∀ j : Fin 3, ((tGL : GL Idx (ZMod 3)) : Matrix Idx Idx (ZMod 3)) * eM (Pi.single j 1) =
    eM (Pi.single j 1) * ((tGL : GL Idx (ZMod 3)) : Matrix Idx Idx (ZMod 3)) := by decide +kernel

theorem tOm_ne_one : tOm ≠ 1 := fun h =>
  tGL_ne_one (by simpa [tOm] using congrArg (fun u : ↥Om => ((u : GL Idx (ZMod 3)) : Matrix Idx Idx (ZMod 3))) h)

theorem tOm_sq : tOm ^ 2 = 1 :=
  Subtype.ext (Units.ext (by simpa [tOm, pow_two] using tGL_sq))

theorem tOm_commute (a : Multiplicative (Fin 3 → ZMod 3)) : Commute tOm (thetaOm a) := by
  have hC : thetaGL a ∈ Subgroup.centralizer {tGL} := by
    have : thetaGL a ∈ thetaGL.range := ⟨a, rfl⟩
    rw [range_thetaGL] at this
    refine (Subgroup.closure_le (Subgroup.centralizer {tGL})).2 ?_ this
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro _ rfl
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, gen_val]
    exact tGL_gen j
  rw [Subgroup.mem_centralizer_iff] at hC
  exact Subtype.ext (hC tGL rfl)

end CFSG.RankThree.PartOne.N143.O7
