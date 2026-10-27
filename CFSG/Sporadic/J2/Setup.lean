module

public import CFSG.Sporadic.Bridge.J2Native
public import CFSG.Certificates.SchreierStabilizerGenerators
public import CFSG.Sporadic.J1.VecSpec
public import CFSG.Sporadic.J2.Certificate

public section

namespace CFSG.Sporadic.J2

open CFSG.Blueprint Matrix
open CFSG.Sporadic.J1 (toV toM toM_mulL toM_idL toM_powL)
open CFSG.Sporadic.J1.Native (wfM mulL idL powL)

noncomputable abbrev J : Subgroup (GL (Fin 14) (ZMod 5)) := Bridge.J2.seedGroup

@[expose] noncomputable def a : J := ⟨Bridge.J2.uA, Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] noncomputable def b : J :=
  ⟨Bridge.J2.uB, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

noncomputable abbrev mat (g : J) : Matrix (Fin 14) (Fin 14) (ZMod 5) :=
  ((g : GL (Fin 14) (ZMod 5)) : Matrix (Fin 14) (Fin 14) (ZMod 5))

theorem mA_eq : Native.mA = Bridge.J2.mA := rfl

theorem mB_eq : Native.mB = Bridge.J2.mB := rfl

theorem mat_a : mat a = toM 5 14 Native.mA := by rw [mA_eq]; rfl

theorem mat_b : mat b = toM 5 14 Native.mB := by rw [mB_eq]; rfl

theorem mat_mul (g h : J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one : mat (1 : J) = 1 := rfl

theorem mat_pow (g : J) (n : ℕ) : mat (g ^ n) = mat g ^ n := by
  simp [mat, Units.val_pow_eq_pow_val]

theorem mat_injective : Function.Injective mat := fun _ _ e => Subtype.ext (Units.ext e)

theorem smul_def (g : J) (v : Fin 14 → ZMod 5) : g • v = mat g *ᵥ v := rfl

theorem closure_ab : Subgroup.closure ({a, b} : Set J) = ⊤ := by
  have h := CFSG.Certificates.schreier_subtype_generators_generate
    ({Bridge.J2.uA, Bridge.J2.uB} : Set (GL (Fin 14) (ZMod 5)))
  convert h using 2
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, Subgroup.coe_subtype]
  constructor
  · rintro (rfl | rfl) <;> simp [a, b]
  · rintro (h | h)
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h

noncomputable def nativeEquiv : NativeSporadic.J2 ≃* J := Bridge.J2.nativeEquiv

theorem certificate_parts : Native.matrixChecks = true ∧
    Native.actionChecks (Native.orbitData ()) 3 = true := by
  have h := j2_certificate
  unfold Native.j2Certificate at h
  simpa only [Bool.and_eq_true] using h

theorem matrix_parts :
    wfM 14 Native.mA = true ∧ wfM 14 Native.mB = true ∧
    mulL 5 14 Native.mA Native.mA = idL 14 ∧ powL 5 14 Native.mB 3 = idL 14 ∧
    powL 5 14 (mulL 5 14 Native.mA Native.mB) 7 = idL 14 := by
  have h := certificate_parts.1
  unfold Native.matrixChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem a_sq : a ^ 2 = 1 := by
  obtain ⟨hA, -, hAA, -, -⟩ := matrix_parts
  apply mat_injective
  rw [mat_pow, mat_one, mat_a, pow_two, ← toM_mulL hA hA, hAA, toM_idL]

theorem b_cube : b ^ 3 = 1 := by
  obtain ⟨-, hB, -, hB3, -⟩ := matrix_parts
  apply mat_injective
  rw [mat_pow, mat_one, mat_b, ← toM_powL hB, hB3, toM_idL]

theorem ab_pow : (a * b) ^ 7 = 1 := by
  obtain ⟨hA, hB, -, -, hAB⟩ := matrix_parts
  apply mat_injective
  rw [mat_pow, mat_one, mat_mul, mat_a, mat_b, ← toM_mulL hA hB,
    ← toM_powL (CFSG.Sporadic.J1.wfM_mulL hA), hAB, toM_idL]

end CFSG.Sporadic.J2
