module

public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.He.OrbitSpec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import CFSG.Sporadic.He.Certificate
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.He

open Native Matrix
open CFSG.Sporadic.Th.Native (Table ap compT powT invT invOK invoOK wordT)
open CFSG.Perm.Native (Tree chainOK chainTrees levelLetters orbitSizes)
open CFSG.Sporadic.Fi23.Native (slpOK)

instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

noncomputable abbrev mA : Matrix (Fin 50) (Fin 50) (ZMod 7) :=
  Blueprint.NativeSporadic.decode 7 50 1 Blueprint.NativeSporadic.HeSeed1

noncomputable abbrev mB : Matrix (Fin 50) (Fin 50) (ZMod 7) :=
  Blueprint.NativeSporadic.decode 7 50 1 Blueprint.NativeSporadic.HeSeed2

private theorem seedA_eq' : seedA = Blueprint.NativeSporadic.HeSeed1 := rfl

private theorem seedB_eq' : seedB = Blueprint.NativeSporadic.HeSeed2 := rfl

theorem seedA_eq : seedA = Blueprint.NativeSporadic.HeSeed1 := seedA_eq'

theorem seedB_eq : seedB = Blueprint.NativeSporadic.HeSeed2 := seedB_eq'

theorem toMat_matA : toMat 7 50 matA = mA := by
  unfold matA; rw [toMat_rowsOf, seedA_eq]

theorem toMat_matB : toMat 7 50 matB = mB := by
  unfold matB; rw [toMat_rowsOf, seedB_eq]

@[expose] noncomputable def orb : VOrbit := orbitData ()

theorem certificate_parts : matrixChecks = true ∧
    vecOrbitOK 7 50 matA matB rootVec orb 3 = true ∧ actionChecks orb 3 = true := by
  have h := he_certificate
  unfold heCertificate at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem mA_sq : mA * mA = 1 := by
  have h := certificate_parts.1
  unfold matrixChecks at h
  simp only [Bool.and_eq_true] at h
  have e := toMat_eq_of_beq (p := 7) (d := 50) h.1
  rwa [toMat_mulM, toMat_idM, toMat_matA] at e

theorem mB_pow : mB ^ 7 = 1 := by
  have h := certificate_parts.1
  unfold matrixChecks at h
  simp only [Bool.and_eq_true] at h
  have e := toMat_eq_of_beq (p := 7) (d := 50) h.2
  rwa [toMat_powM, toMat_idM, toMat_matB] at e

theorem det_mA_ne_zero : mA.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det mA_sq
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem det_mB_ne_zero : mB.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det mB_pow
  rw [Matrix.det_pow, h, Matrix.det_one, zero_pow (by norm_num)] at this
  exact zero_ne_one this

noncomputable abbrev gA : GL (Fin 50) (ZMod 7) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero mA det_mA_ne_zero

noncomputable abbrev gB : GL (Fin 50) (ZMod 7) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero mB det_mB_ne_zero

noncomputable abbrev J :
    Subgroup (GL (Fin 50) (ZMod 7)) := Subgroup.closure {gA, gB}

@[expose] noncomputable def a :
    J := ⟨gA, Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] noncomputable def b :
    J := ⟨gB, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

noncomputable abbrev mat
    (g : J) : Matrix (Fin 50) (Fin 50) (ZMod 7) :=
  ((g : GL (Fin 50) (ZMod 7)) : Matrix (Fin 50) (Fin 50) (ZMod 7))

theorem mat_mul (g h : J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one : mat (1 : J) = 1 := rfl

theorem mat_injective : Function.Injective mat := by
  intro g h e
  exact Subtype.ext (Units.ext e)

theorem mat_a : mat a = mA := rfl

theorem mat_b : mat b = mB := rfl

theorem closure_ab : Subgroup.closure ({a, b} : Set J) = ⊤ := by
  have h := CFSG.Certificates.schreier_subtype_generators_generate
    ({gA, gB} : Set (GL (Fin 50) (ZMod 7)))
  convert h using 2
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, Subgroup.coe_subtype]
  constructor
  · rintro (rfl | rfl) <;> simp [a, b]
  · rintro (h | h)
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h

noncomputable def heEquivJ : Blueprint.NativeSporadic.He ≃* J :=
  Blueprint.NativeSporadic.matrixSeedEquiv 7 50 (by norm_num) mA mB det_mA_ne_zero
    det_mB_ne_zero

theorem mat_heEquivJ
    (u : Blueprint.NativeSporadic.He) : mat (heEquivJ u) = u.val.val :=
  Blueprint.NativeSporadic.matrixSeedEquiv_val 7 50 (by norm_num) mA mB det_mA_ne_zero
    det_mB_ne_zero u

theorem vecFacts :
    VecFacts 7 50 matA matB orb := vecOrbitOK_facts certificate_parts.2.1

noncomputable abbrev letters : Array Table := chainLetters orb

noncomputable abbrev trees : Array Tree := chainTrees 8330 letters chainBase

noncomputable abbrev lv1 : Array ℕ := levelLetters letters chainBase 1

noncomputable abbrev subTs : Array Tree := subTrees letters lv1

noncomputable abbrev labs : Array ℕ := labelsOf subTs

noncomputable abbrev tabW : Table := wordT 8330 (genTables orb) witWord

noncomputable abbrev tabAB : Table := compT 8330 orb.alpha orb.beta

structure ActionFacts : Prop where
  keys_size : orb.keys.size = 8330
  alpha_size : orb.alpha.size = 8330
  beta_size : orb.beta.size = 8330
  alpha_invo : invoOK 8330 orb.alpha = true
  beta_inv : invOK 8330 orb.beta (invT 8330 orb.beta) = true
  basis : basisCheck orb = true
  slp_ok : slpOK chainWords = true
  words_size : 2 ≤ chainWords.size
  word0 : chainWords[0]! = [1]
  word1 : chainWords[1]! = [2]
  chain : chainOK 8330 letters chainBase chainQ chainQb trees 3 = true
  sizes : orbitSizes trees = [8330, 4480, 27, 2, 2]
  sub : subChecks letters lv1 subTs labs = true
  wit0 : labs[ap tabW 0]! = 5
  wit1 : labs[21]! = 3
  wit1' : labs[ap tabW 21]! = 1
  wit2 : labs[24]! = 4
  wit2' : labs[ap tabW 24]! = 3
  a_ne : isIdT orb.alpha = false
  b_pow : isIdT (powT 8330 7 orb.beta) = true
  b_ne : isIdT orb.beta = false
  ab_pow : isIdT (powT 8330 17 tabAB) = true
  ab_ne : isIdT tabAB = false

theorem actionFacts : ActionFacts := by
  have h := certificate_parts.2.2
  unfold actionChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩,
    h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h23⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23⟩

theorem orb_size : orb.keys.size = 8330 := actionFacts.keys_size

end CFSG.Sporadic.He
