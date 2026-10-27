module

public import CFSG.Open.GLADefs

public section

namespace CFSG.ShultStronglyClosedTI

open Matrix CFSG.Open

universe u v w

section GeneralLinear

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {R : Type v} {S : Type w} [CommRing R] [CommRing S]

@[expose] def glFieldEquiv (e : R ≃+* S) : GL ι R ≃* GL ι S :=
  Units.mapEquiv e.mapMatrix.toMulEquiv

@[simp] theorem coe_glFieldEquiv (e : R ≃+* S) (A : GL ι R) :
    (glFieldEquiv e A : Matrix ι ι S) = (A : Matrix ι ι R).map e := rfl

@[simp] theorem glFieldEquiv_symm (e : R ≃+* S) :
    (glFieldEquiv (ι := ι) e).symm = glFieldEquiv e.symm := rfl

def quotientCenterEquiv {A : Type v} {B : Type w} [Group A] [Group B]
    (e : A ≃* B) : A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

def pglFieldEquiv (e : R ≃+* S) : ProjGenLinGroup ι R ≃* ProjGenLinGroup ι S :=
  quotientCenterEquiv (glFieldEquiv e)

@[simp] theorem pglFieldEquiv_mk (e : R ≃+* S) (A : GL ι R) :
    pglFieldEquiv e (ProjGenLinGroup.mk A) = ProjGenLinGroup.mk (glFieldEquiv e A) :=
  QuotientGroup.congr_mk' _ _ _ (Subgroup.map_center_eq (glFieldEquiv e)) A

end GeneralLinear

section ScalarQuotient

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {K : Type} [Field K]

noncomputable def scalarQuotientEquivImage (H : Subgroup (GL ι K)) :
    GLAProj H ≃* H.map ProjGenLinGroup.mk := by
  let q : H →* ProjGenLinGroup ι K := ProjGenLinGroup.mk.comp H.subtype
  have hker : q.ker = (GLAScalars ι K).subgroupOf H := by
    ext A
    change ProjGenLinGroup.mk (A : GL ι K) = 1 ↔ (A : GL ι K) ∈ GLAScalars ι K
    rw [ProjGenLinGroup.mk_eq_one, GLAScalars, CFSG.Assembly.largeEvenScalars_def,
      GeneralLinearGroup.center_eq_range_scalar]
  have hrange : q.range = H.map ProjGenLinGroup.mk := by
    change (ProjGenLinGroup.mk.comp H.subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange q).trans (MulEquiv.subgroupCongr hrange))

end ScalarQuotient

section SubgroupTransport

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {K L : Type} [Field K] [Field L]

def projectiveImageEquiv (e : GL ι K ≃* GL κ L)
    (H : Subgroup (GL ι K)) (J : Subgroup (GL κ L))
    (hmap : H.map e.toMonoidHom = J) :
    H.map ProjGenLinGroup.mk ≃* J.map ProjGenLinGroup.mk := by
  let ep : ProjGenLinGroup ι K ≃* ProjGenLinGroup κ L := quotientCenterEquiv e
  have hcomm : ep.toMonoidHom.comp ProjGenLinGroup.mk =
      ProjGenLinGroup.mk.comp e.toMonoidHom := by
    ext A
    exact QuotientGroup.congr_mk' _ _ _ (Subgroup.map_center_eq e) A
  have hp : (H.map ProjGenLinGroup.mk).map ep.toMonoidHom =
      J.map ProjGenLinGroup.mk := by
    rw [Subgroup.map_map, hcomm, ← Subgroup.map_map, hmap]
  exact (ep.subgroupMap _).trans (MulEquiv.subgroupCongr hp)

noncomputable def scalarQuotientEquivOfGLMap (e : GL ι K ≃* GL κ L)
    (H : Subgroup (GL ι K)) (J : Subgroup (GL κ L))
    (hmap : H.map e.toMonoidHom = J) : GLAProj H ≃* GLAProj J :=
  (scalarQuotientEquivImage H).trans
    ((projectiveImageEquiv e H J hmap).trans (scalarQuotientEquivImage J).symm)

end SubgroupTransport

section Linear

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {K L : Type} [Field K] [Field L]

@[expose] def slFieldEquiv (e : K ≃+* L) :
    SpecialLinearGroup ι K ≃* SpecialLinearGroup ι L where
  toFun := SpecialLinearGroup.map e.toRingHom
  invFun := SpecialLinearGroup.map e.symm.toRingHom
  left_inv A := by
    apply Subtype.ext
    ext i j
    exact e.symm_apply_apply ((A : Matrix ι ι K) i j)
  right_inv A := by
    apply Subtype.ext
    ext i j
    exact e.apply_symm_apply ((A : Matrix ι ι L) i j)
  map_mul' A B := map_mul (SpecialLinearGroup.map e.toRingHom) A B

def pslFieldEquiv (e : K ≃+* L) :
    ProjectiveSpecialLinearGroup ι K ≃* ProjectiveSpecialLinearGroup ι L :=
  quotientCenterEquiv (slFieldEquiv e)

def glaSLQuotientEquivPSL :
    GLAProj (GLASLGroup ι K) ≃* ProjectiveSpecialLinearGroup ι K := by
  let e : SpecialLinearGroup ι K ≃* GLASLGroup ι K := SpecialLinearGroup.toGLKerEquiv
  have hcenter : (Subgroup.center (SpecialLinearGroup ι K)).map e.toMonoidHom =
      (GLAScalars ι K).subgroupOf (GLASLGroup ι K) := by
    ext A
    rw [Subgroup.mem_map_equiv]
    change e.symm A ∈ Subgroup.center (SpecialLinearGroup ι K) ↔
      (A : GL ι K) ∈ GLAScalars ι K
    rw [← SpecialLinearGroup.toGL_mem_center_iff]
    have hcoe : SpecialLinearGroup.toGL (e.symm A) = (A : GL ι K) :=
      congrArg Subtype.val (e.apply_symm_apply A)
    rw [hcoe, GeneralLinearGroup.center_eq_range_scalar]
    rfl
  exact (QuotientGroup.congr _ _ e hcenter).symm

end Linear

section UnitaryField

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {K L : Type} [Field K] [Field L]

@[expose] def powerAdjoint (q : ℕ) (A : Matrix ι ι K) : Matrix ι ι K :=
  (A.map (· ^ q)).transpose

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem map_powerAdjoint (e : K ≃+* L) (q : ℕ) (A : Matrix ι ι K) :
    (powerAdjoint q A).map e = powerAdjoint q (A.map e) := by
  ext i j
  exact map_pow e (A j i) q

theorem unitaryField_condition_iff (e : K ≃+* L) (q : ℕ) (A : GL ι K) :
    ((glFieldEquiv e A : Matrix ι ι L).det = 1 ∧
      powerAdjoint q (glFieldEquiv e A : Matrix ι ι L) *
        (glFieldEquiv e A : Matrix ι ι L) = 1) ↔
    ((A : Matrix ι ι K).det = 1 ∧
      powerAdjoint q (A : Matrix ι ι K) * (A : Matrix ι ι K) = 1) := by
  have hd : (glFieldEquiv e A : Matrix ι ι L).det = e (A : Matrix ι ι K).det :=
    (e.toRingHom.map_det _).symm
  have hm : powerAdjoint q (glFieldEquiv e A : Matrix ι ι L) *
      (glFieldEquiv e A : Matrix ι ι L) =
      (powerAdjoint q (A : Matrix ι ι K) * (A : Matrix ι ι K)).map e := by
    rw [Matrix.map_mul, map_powerAdjoint, coe_glFieldEquiv]
  rw [hd, ← e.map_one, e.injective.eq_iff, hm]
  have hone : (1 : Matrix ι ι L) = (1 : Matrix ι ι K).map e :=
    (e.mapMatrix (m := ι)).map_one.symm
  rw [hone]
  exact and_congr_right fun _ => e.mapMatrix.injective.eq_iff

theorem map_glaSUGroup (e : K ≃+* L) (q : ℕ) :
    (GLASUGroup ι K q).map (glFieldEquiv e).toMonoidHom = GLASUGroup ι L q := by
  rw [GLASUGroup, CFSG.Assembly.LargeEvenSUGroup, CFSG.Assembly.LargeEvenSUGroup,
    MonoidHom.map_closure]
  apply congrArg Subgroup.closure
  ext B
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact (unitaryField_condition_iff e q A).mpr hA
  · intro hB
    change (B : Matrix ι ι L).det = 1 ∧
      powerAdjoint q (B : Matrix ι ι L) * (B : Matrix ι ι L) = 1 at hB
    refine ⟨(glFieldEquiv e).symm B, ?_, (glFieldEquiv e).apply_symm_apply B⟩
    exact (unitaryField_condition_iff e q _).mp
      (by simpa only [MulEquiv.apply_symm_apply] using hB)

noncomputable def glaSUFieldEquiv (e : K ≃+* L) (q : ℕ) :
    GLAProj (GLASUGroup ι K q) ≃* GLAProj (GLASUGroup ι L q) :=
  scalarQuotientEquivOfGLMap (glFieldEquiv e) _ _ (map_glaSUGroup e q)

end UnitaryField

section UnitaryGram

variable {K : Type} [Field K] [CharP K 2]

@[expose] def unitaryGramChangeGL : GL (Fin 3) K where
  val := !![1, 1, 0; 1, 1, 1; 0, 1, 1]
  inv := !![0, 1, 1; 1, 1, 1; 1, 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

@[expose] def unitaryAntidiagonal : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem unitaryGramChange_gram (f : ℕ) :
    powerAdjoint (2 ^ f) (unitaryGramChangeGL (K := K) : Matrix (Fin 3) (Fin 3) K) *
      (unitaryGramChangeGL (K := K) : Matrix (Fin 3) (Fin 3) K) = unitaryAntidiagonal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [powerAdjoint, unitaryGramChangeGL, unitaryAntidiagonal,
      Matrix.mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

theorem powerAdjoint_mul (f : ℕ) (A B : Matrix (Fin 3) (Fin 3) K) :
    powerAdjoint (2 ^ f) (A * B) =
      powerAdjoint (2 ^ f) B * powerAdjoint (2 ^ f) A := by
  change ((A * B).map (iterateFrobenius K 2 f)).transpose = _
  rw [Matrix.map_mul, Matrix.transpose_mul]
  rfl

@[simp] theorem powerAdjoint_one (f : ℕ) :
    powerAdjoint (2 ^ f) (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  change ((1 : Matrix (Fin 3) (Fin 3) K).map (iterateFrobenius K 2 f)).transpose = 1
  rw [Matrix.map_one, Matrix.transpose_one]
  all_goals simp

@[expose] def unitaryGramConj : GL (Fin 3) K ≃* GL (Fin 3) K :=
  MulAut.conj (unitaryGramChangeGL (K := K))⁻¹

theorem powerAdjoint_inv_mul (f : ℕ) (B : GL (Fin 3) K) :
    powerAdjoint (2 ^ f) ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      powerAdjoint (2 ^ f) (B : Matrix (Fin 3) (Fin 3) K) = 1 := by
  rw [← powerAdjoint_mul]
  simp only [Units.mul_inv, powerAdjoint_one]

theorem unitaryGramConj_condition_iff (f : ℕ) (A : GL (Fin 3) K) :
    powerAdjoint (2 ^ f) (unitaryGramConj A : Matrix (Fin 3) (Fin 3) K) *
        unitaryAntidiagonal * (unitaryGramConj A : Matrix (Fin 3) (Fin 3) K) =
      unitaryAntidiagonal ↔
    powerAdjoint (2 ^ f) (A : Matrix (Fin 3) (Fin 3) K) *
      (A : Matrix (Fin 3) (Fin 3) K) = 1 := by
  let P : GL (Fin 3) K := unitaryGramChangeGL
  let M : Matrix (Fin 3) (Fin 3) K := P
  let N : Matrix (Fin 3) (Fin 3) K := (P⁻¹ : GL (Fin 3) K)
  let D : Matrix (Fin 3) (Fin 3) K → Matrix (Fin 3) (Fin 3) K := powerAdjoint (2 ^ f)
  have hMN : M * N = 1 := P.mul_inv
  have hNM : N * M = 1 := P.inv_mul
  have hDNM : D N * D M = 1 := powerAdjoint_inv_mul f P
  have hDmn : D M * D N = 1 := by
    rw [← powerAdjoint_mul, hNM, powerAdjoint_one]
  have hgram : D M * M = unitaryAntidiagonal := unitaryGramChange_gram f
  have hT : (unitaryGramConj A : Matrix (Fin 3) (Fin 3) K) =
      N * (A : Matrix (Fin 3) (Fin 3) K) * M := by
    change (((P⁻¹ * A * (P⁻¹)⁻¹ : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) = _
    simp only [inv_inv, Units.val_mul]
    rfl
  have htransport :
      D (unitaryGramConj A : Matrix (Fin 3) (Fin 3) K) * unitaryAntidiagonal *
        (unitaryGramConj A : Matrix (Fin 3) (Fin 3) K) =
      D M * (D (A : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K)) * M := by
    rw [hT, ← hgram]
    dsimp only [D]
    simp only [powerAdjoint_mul, mul_assoc]
    rw [← mul_assoc (powerAdjoint (2 ^ f) N) (powerAdjoint (2 ^ f) M), hDNM,
      one_mul, ← mul_assoc M N, hMN, one_mul]
  change D (unitaryGramConj A : Matrix (Fin 3) (Fin 3) K) * unitaryAntidiagonal *
      (unitaryGramConj A : Matrix (Fin 3) (Fin 3) K) = unitaryAntidiagonal ↔ _
  rw [htransport, ← hgram]
  constructor
  · intro h
    have hc := congrArg (fun B => D N * B * N) h
    simpa only [mul_assoc, ← mul_assoc (D N) (D M), hDNM, one_mul,
      ← mul_assoc _ M N, hMN, mul_one] using hc
  · intro h
    rw [h, mul_one]

theorem unitaryGramConj_det (A : GL (Fin 3) K) :
    GeneralLinearGroup.det (unitaryGramConj A) = GeneralLinearGroup.det A := by
  simp [unitaryGramConj, map_mul, map_inv, mul_comm]

@[expose] def unitaryAntidiagonalGroup (f : ℕ) : Subgroup (GL (Fin 3) K) :=
  Subgroup.closure {A |
    powerAdjoint (2 ^ f) (A : Matrix (Fin 3) (Fin 3) K) * unitaryAntidiagonal *
        (A : Matrix (Fin 3) (Fin 3) K) = unitaryAntidiagonal ∧
      GeneralLinearGroup.det A = 1}

theorem unitaryGramConj_generator_iff (f : ℕ) (A : GL (Fin 3) K) :
    (powerAdjoint (2 ^ f) (unitaryGramConj A : Matrix (Fin 3) (Fin 3) K) *
          unitaryAntidiagonal * (unitaryGramConj A : Matrix (Fin 3) (Fin 3) K) =
        unitaryAntidiagonal ∧ GeneralLinearGroup.det (unitaryGramConj A) = 1) ↔
    ((A : Matrix (Fin 3) (Fin 3) K).det = 1 ∧
      powerAdjoint (2 ^ f) (A : Matrix (Fin 3) (Fin 3) K) *
        (A : Matrix (Fin 3) (Fin 3) K) = 1) := by
  rw [unitaryGramConj_condition_iff, unitaryGramConj_det]
  have hd : GeneralLinearGroup.det A = 1 ↔ (A : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    constructor
    · intro h
      exact congrArg Units.val h
    · intro h
      exact Units.ext h
  rw [hd, and_comm]

theorem map_unitaryGramConj_glaSUGroup (f : ℕ) :
    (GLASUGroup (Fin 3) K (2 ^ f)).map unitaryGramConj.toMonoidHom =
      unitaryAntidiagonalGroup f := by
  rw [GLASUGroup, CFSG.Assembly.LargeEvenSUGroup, unitaryAntidiagonalGroup,
    MonoidHom.map_closure]
  apply congrArg Subgroup.closure
  ext B
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact (unitaryGramConj_generator_iff f A).mpr hA
  · intro hB
    change powerAdjoint (2 ^ f) (B : Matrix (Fin 3) (Fin 3) K) * unitaryAntidiagonal *
        (B : Matrix (Fin 3) (Fin 3) K) = unitaryAntidiagonal ∧
      GeneralLinearGroup.det B = 1 at hB
    refine ⟨unitaryGramConj.symm B, ?_, unitaryGramConj.apply_symm_apply B⟩
    exact (unitaryGramConj_generator_iff f _).mp
      (by simpa only [MulEquiv.apply_symm_apply] using hB)

noncomputable def glaSUGramEquiv (f : ℕ) :
    GLAProj (GLASUGroup (Fin 3) K (2 ^ f)) ≃*
      (unitaryAntidiagonalGroup (K := K) f).map ProjGenLinGroup.mk :=
  (scalarQuotientEquivImage _).trans
    (projectiveImageEquiv unitaryGramConj _ _ (map_unitaryGramConj_glaSUGroup f))

end UnitaryGram

section SuzukiField

variable {K L : Type} [Field K] [Field L]

theorem map_mem_glaSzGens (e : K ≃+* L) (a : ℕ)
    (M : Matrix (Fin 4) (Fin 4) K) (hM : M ∈ GLASzGens a K) :
    M.map e ∈ GLASzGens a L := by
  rcases hM with ⟨u, v, rfl⟩ | ⟨l, rfl⟩ | rfl
  · left
    refine ⟨e u, e v, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · right
    left
    refine ⟨Units.mapEquiv e.toMulEquiv l, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Units.coe_mapEquiv]
  · right
    right
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem map_mem_glaSzGens_iff (e : K ≃+* L) (a : ℕ)
    (M : Matrix (Fin 4) (Fin 4) K) :
    M.map e ∈ GLASzGens a L ↔ M ∈ GLASzGens a K := by
  constructor
  · intro hM
    have h := map_mem_glaSzGens e.symm a _ hM
    have hcancel : (M.map e).map e.symm = M := by
      ext i j
      exact e.symm_apply_apply (M i j)
    simpa only [hcancel] using h
  · exact map_mem_glaSzGens e a M

theorem map_glaSzGroup (e : K ≃+* L) (a : ℕ) :
    (GLASzGroup a K).map (glFieldEquiv e).toMonoidHom = GLASzGroup a L := by
  rw [GLASzGroup, CFSG.Assembly.LargeEvenSzGroup, CFSG.Assembly.LargeEvenSzGroup,
    MonoidHom.map_closure]
  apply congrArg Subgroup.closure
  ext B
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact (map_mem_glaSzGens_iff e a _).mpr hA
  · intro hB
    change (B : Matrix (Fin 4) (Fin 4) L) ∈ GLASzGens a L at hB
    refine ⟨(glFieldEquiv e).symm B, ?_, (glFieldEquiv e).apply_symm_apply B⟩
    exact (map_mem_glaSzGens_iff e a _).mp
      (by simpa only [← coe_glFieldEquiv, MulEquiv.apply_symm_apply] using hB)

def glaSzFieldEquiv (e : K ≃+* L) (a : ℕ) : GLASzGroup a K ≃* GLASzGroup a L :=
  ((glFieldEquiv e).subgroupMap _).trans (MulEquiv.subgroupCongr (map_glaSzGroup e a))

end SuzukiField

section FiniteField

variable {K : Type} [Field K] [Finite K]

noncomputable def binaryFieldEquiv (f : ℕ) (hf : 0 < f)
    (hcard : Nat.card K = 2 ^ f) : K ≃+* GaloisField 2 f := by
  let : Fintype K := Fintype.ofFinite K
  let : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  exact FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard,
      GaloisField.card 2 f (by omega)])

noncomputable def glaSL2EquivNative (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = 2 ^ f) :
    GLAProj (GLASLGroup (Fin 2) K) ≃*
      ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f) :=
  glaSLQuotientEquivPSL.trans (pslFieldEquiv (binaryFieldEquiv f (by omega) hcard))

end FiniteField

end CFSG.ShultStronglyClosedTI
