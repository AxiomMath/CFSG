module

public import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.Basic

public section

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag Matrix

namespace CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut

section Frob4

variable {p : ℕ}

private theorem natCard_galoisField_two_mul (hp : 1 ≤ p) :
    Nat.card (GaloisField 2 (2 * p)) = 4 ^ p := by
  rw [GaloisField.card 2 (2 * p) (by omega), pow_mul]
  norm_num

theorem frob4_pow_apply (n : ℕ) (z : GaloisField 2 (2 * p)) : (frob4 p ^ n) z = z ^ 4 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, ih, frob4_apply, ← pow_mul, ← pow_succ]

theorem frob4_pow_eq_one (hp : 1 ≤ p) : frob4 p ^ p = 1 := by
  ext z
  rw [frob4_pow_apply, RingHom.one_def, RingHom.id_apply]
  have : Fintype (GaloisField 2 (2 * p)) := Fintype.ofFinite _
  have h := FiniteField.pow_card z
  rwa [← Nat.card_eq_fintype_card, natCard_galoisField_two_mul hp] at h

theorem frob4_bar (hp : 1 ≤ p) (z : GaloisField 2 (2 * p)) :
    frob4 p ((unitaryFieldData_galoisField hp).bar z) =
      (unitaryFieldData_galoisField hp).bar (frob4 p z) := by
  rw [frob4_apply, UnitaryFieldData.bar_apply, UnitaryFieldData.bar_apply, frob4_apply,
    ← pow_mul, ← pow_mul, mul_comm (2 ^ p) 4]

end Frob4

theorem projGenLinGroup_map_injective_of_pow_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R] (σ : R →+* R) {m : ℕ} (hm : m ≠ 0) (h : σ ^ m = 1) :
    Function.Injective (ProjGenLinGroup.map (n := n) σ) := by
  refine Function.LeftInverse.injective (g := ProjGenLinGroup.map (σ ^ (m - 1))) fun x => ?_
  rw [← MonoidHom.comp_apply, ← ProjGenLinGroup.map_comp, ← RingHom.mul_def, ← pow_succ,
    Nat.sub_add_cancel (Nat.pos_of_ne_zero hm), h, RingHom.one_def, ProjGenLinGroup.map_id]
  rfl

section Frob4Aut

variable {p : ℕ}

theorem map_frob4_mem_psu3 (hp : 1 ≤ p) {x : ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * p))}
    (hx : x ∈ PSU3 2 p) : ProjGenLinGroup.map (frob4 p) x ∈ PSU3 2 p := by
  rw [psu3_eq_map_gramSU hp, Subgroup.mem_map] at hx ⊢
  obtain ⟨A, hA, rfl⟩ := hx
  refine ⟨GeneralLinearGroup.map (frob4 p) A, ?_, ProjGenLinGroup.map_mk _ _⟩
  have := map_mem_gramSU (frob4 p) (frob4_bar hp) _ hA
  rwa [antidiagGram_map] at this

private noncomputable def frob4End (hp : 1 ≤ p) : PSU3 2 p →* PSU3 2 p :=
  ((ProjGenLinGroup.map (frob4 p)).comp (PSU3 2 p).subtype).codRestrict (PSU3 2 p)
    fun x => map_frob4_mem_psu3 hp x.2

private theorem frob4End_injective (hp : 1 ≤ p) : Function.Injective (frob4End hp) :=
  fun _ _ hxy => Subtype.ext (projGenLinGroup_map_injective_of_pow_eq_one (frob4 p)
    (by omega) (frob4_pow_eq_one hp) (congrArg Subtype.val hxy))

noncomputable def frob4Aut (hp : 1 ≤ p) : MulAut (PSU3 2 p) :=
  MulEquiv.ofBijective (frob4End hp) (Finite.injective_iff_bijective.1 (frob4End_injective hp))

theorem coe_frob4Aut (hp : 1 ≤ p) (x : PSU3 2 p) :
    ((frob4Aut hp x : PSU3 2 p) : ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * p))) =
      ProjGenLinGroup.map (frob4 p) (x : ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * p))) := by
  simp [frob4Aut, frob4End]

theorem coe_frob4Aut_pow (hp : 1 ≤ p) (n : ℕ) (x : PSU3 2 p) :
    (((frob4Aut hp ^ n) x : PSU3 2 p) : ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * p))) =
      ProjGenLinGroup.map (frob4 p ^ n) (x : ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * p))) := by
  induction n generalizing x with
  | zero => simp [RingHom.one_def]
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih, coe_frob4Aut, ← MonoidHom.comp_apply,
      ← ProjGenLinGroup.map_comp, ← RingHom.mul_def, ← pow_succ]

theorem frob4Aut_pow_eq_one (hp : 1 ≤ p) : frob4Aut hp ^ p = 1 := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [coe_frob4Aut_pow, frob4_pow_eq_one hp, RingHom.one_def, ProjGenLinGroup.map_id]
  rfl

end Frob4Aut

section Torus

variable {q f : ℕ} {K : Type*} [Field K] (h : UnitaryFieldData q f K)

private noncomputable def torusMat (a : K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.diagonal ![a, h.bar a / a, (h.bar a)⁻¹]

private theorem det_torusMat {a : K} (ha : a ≠ 0) : (torusMat h a).det = 1 := by
  have hb : h.bar a ≠ 0 := (map_ne_zero h.bar).2 ha
  rw [torusMat, Matrix.det_diagonal, Fin.prod_univ_three]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  field_simp

private theorem torusMat_isometry {a : K} (ha : a ≠ 0) :
    ((torusMat h a).map h.bar)ᵀ * antidiagGram K * torusMat h a = antidiagGram K := by
  have hb : h.bar a ≠ 0 := (map_ne_zero h.bar).2 ha
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusMat, antidiagGram, Matrix.mul_apply, Matrix.diagonal_apply,
      UnitaryFieldData.bar_bar, ha, hb]

private noncomputable def torusGL {a : K} (ha : a ≠ 0) : GL (Fin 3) K :=
  GeneralLinearGroup.mkOfDetNeZero (torusMat h a) (by rw [det_torusMat h ha]; exact one_ne_zero)

private theorem coe_torusGL {a : K} (ha : a ≠ 0) :
    (torusGL h ha : Matrix (Fin 3) (Fin 3) K) = torusMat h a :=
  rfl

private theorem torusGL_mem_gramSU {a : K} (ha : a ≠ 0) :
    torusGL h ha ∈ gramSU h (antidiagGram K) :=
  mem_gramSU.2 ⟨by rw [coe_torusGL]; exact torusMat_isometry h ha,
    by rw [coe_torusGL]; exact det_torusMat h ha⟩

end Torus

private theorem pow_nine_eq_one_of_map_frob4_eq {p : ℕ} (hp : 1 ≤ p)
    {a : GaloisField 2 (2 * p)} (ha : a ≠ 0)
    (hfix : ProjGenLinGroup.map (frob4 p)
        (ProjGenLinGroup.mk (torusGL (unitaryFieldData_galoisField hp) ha)) =
      ProjGenLinGroup.mk (torusGL (unitaryFieldData_galoisField hp) ha)) : a ^ 9 = 1 := by
  rw [ProjGenLinGroup.map_mk, ProjGenLinGroup.mk_eq_mk_iff] at hfix
  obtain ⟨u, hu⟩ := hfix
  have h00 : a ^ 4 * (u : GaloisField 2 (2 * p)) = a := by
    simpa [torusGL, torusMat, frob4_apply] using
      congrArg (fun g : GL (Fin 3) (GaloisField 2 (2 * p)) =>
        (g : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * p))) 0 0) hu
  have hdet := congrArg GeneralLinearGroup.det hu
  rw [map_mul, GeneralLinearGroup.map_det, GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
  have hdetg : GeneralLinearGroup.det (torusGL (unitaryFieldData_galoisField hp) ha) = 1 :=
    Units.ext (by
      rw [GeneralLinearGroup.val_det_apply, coe_torusGL, det_torusMat _ ha]
      rfl)
  rw [hdetg, map_one, one_mul] at hdet
  have hu3 : (u : GaloisField 2 (2 * p)) ^ 3 = 1 := by
    simpa [Units.ext_iff] using hdet
  have h1 : a ^ 3 * (u : GaloisField 2 (2 * p)) = 1 :=
    mul_left_cancel₀ ha (by linear_combination h00)
  linear_combination (a ^ 6 * (u : GaloisField 2 (2 * p)) ^ 2 + a ^ 3 * u + 1) * h1 - a ^ 9 * hu3

private theorem exists_map_frob4_ne {p : ℕ} (hp : 2 ≤ p) :
    ∃ x ∈ PSU3 2 p, ProjGenLinGroup.map (frob4 p) x ≠ x := by
  have hp1 : 1 ≤ p := by omega
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := (GaloisField 2 (2 * p))ˣ)
  have hord : orderOf a = 4 ^ p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ha, Nat.card_units,
      natCard_galoisField_two_mul hp1]
  have ha9 : a ^ 9 ≠ 1 := by
    intro h9
    have hd := orderOf_dvd_of_pow_eq_one h9
    rw [hord] at hd
    have hle := Nat.le_of_dvd (by norm_num) hd
    have h16 : 4 ^ 2 ≤ 4 ^ p := Nat.pow_le_pow_right (by norm_num) hp
    omega
  have ha0 : (a : GaloisField 2 (2 * p)) ≠ 0 := a.ne_zero
  refine ⟨ProjGenLinGroup.mk (torusGL (unitaryFieldData_galoisField hp1) ha0), ?_,
    fun hfix => ha9 ?_⟩
  · rw [psu3_eq_map_gramSU hp1]
    exact ⟨_, torusGL_mem_gramSU _ ha0, rfl⟩
  · exact Units.ext (by simpa using pow_nine_eq_one_of_map_frob4_eq hp1 ha0 hfix)

theorem frob4Aut_ne_one {p : ℕ} (hp : 2 ≤ p) : frob4Aut (one_le_two.trans hp) ≠ 1 := by
  intro h1
  obtain ⟨x, hx, hne⟩ := exists_map_frob4_ne hp
  refine hne ?_
  have h2 := congrArg (fun τ : MulAut (PSU3 2 p) =>
    ((τ ⟨x, hx⟩ : PSU3 2 p) : ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * p)))) h1
  simpa [coe_frob4Aut] using h2

theorem orderOf_frob4Aut {p : ℕ} (hp : p.Prime) : orderOf (frob4Aut hp.one_le) = p := by
  have := Fact.mk hp
  exact orderOf_eq_prime (frob4Aut_pow_eq_one hp.one_le) (frob4Aut_ne_one hp.two_le)

theorem exists_mulAut_frob4 {p : ℕ} (hp : p.Prime) :
    ∃ τ : MulAut (PSU3 2 p), orderOf τ = p ∧
      ∀ x : PSU3 2 p, ((τ x : PSU3 2 p) : ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * p))) =
        ProjGenLinGroup.map (frob4 p) (x : ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * p))) :=
  ⟨frob4Aut hp.one_le, orderOf_frob4Aut hp, coe_frob4Aut hp.one_le⟩

end CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut
