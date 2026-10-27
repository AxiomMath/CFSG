module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2Generation
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3Pgl

public section

namespace CFSG.Quasithin.B45Exc

open Matrix CFSG CFSG.GorensteinWalter CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Setup.Family
  CFSG.QuasithinUnique.Setup.X3 CFSG.SectionRank.OddCover

section PGL

variable {K : Type*} [Field K]

@[expose] noncomputable def p2PSL (K : Type*) [Field K] :
    projectiveSL 2 K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
  QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 2 K)

@[expose] noncomputable def p2PGL (K : Type*) [Field K] : projectiveSL 2 K →* PGL2 K :=
  (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).comp (p2PSL K).toMonoidHom

theorem p2PGL_proj (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    p2PGL K (proj 2 K M) = ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL M) := rfl

theorem p2PGL_injective : Function.Injective (p2PGL K) :=
  Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp (p2PSL K).injective

theorem mem_pglS_iff_p2PGL {x : PGL2 K} : x ∈ pglS K ↔ ∃ s : projectiveSL 2 K, p2PGL K s = x := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨s, rfl⟩ := (p2PSL K).surjective y
    exact ⟨s, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨p2PSL K s, rfl⟩

@[expose] noncomputable def glA : GL (Fin 2) K :=
  Matrix.SpecialLinearGroup.toGL (slA : Matrix.SpecialLinearGroup (Fin 2) K)

theorem coe_glA : ((glA : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, -1; 1, 0] := rfl

theorem scalar_fin_two (u : K) : Matrix.scalar (Fin 2) u = !![u, 0; 0, u] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]

theorem coe_eq_of_entries (V : GL (Fin 2) K) :
    (V : Matrix (Fin 2) (Fin 2) K) = !![(V : Matrix (Fin 2) (Fin 2) K) 0 0,
      (V : Matrix (Fin 2) (Fin 2) K) 0 1; (V : Matrix (Fin 2) (Fin 2) K) 1 0,
      (V : Matrix (Fin 2) (Fin 2) K) 1 1] :=
  Matrix.eta_fin_two _

theorem entries_of_mul_glA {V : GL (Fin 2) K} {u : Kˣ}
    (h : V * glA * Matrix.GeneralLinearGroup.scalar (Fin 2) u = glA * V) :
    (V : Matrix (Fin 2) (Fin 2) K) 1 1 = (V : Matrix (Fin 2) (Fin 2) K) 0 0 * u ∧
      (V : Matrix (Fin 2) (Fin 2) K) 1 0 = -((V : Matrix (Fin 2) (Fin 2) K) 0 1 * u) ∧
      (V : Matrix (Fin 2) (Fin 2) K) 0 0 = (V : Matrix (Fin 2) (Fin 2) K) 1 1 * u ∧
      (V : Matrix (Fin 2) (Fin 2) K) 0 1 = -((V : Matrix (Fin 2) (Fin 2) K) 1 0 * u) := by
  have hm := congrArg (fun X : GL (Fin 2) K => (X : Matrix (Fin 2) (Fin 2) K)) h
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, coe_glA] at hm
  rw [coe_eq_of_entries V, scalar_fin_two] at hm
  simp only [Matrix.mul_fin_two] at hm
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  have e10 := congrFun (congrFun hm 1) 0
  have e11 := congrFun (congrFun hm 1) 1
  simp at e00 e01 e10 e11
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination -e01
  · linear_combination e00
  · linear_combination -e10
  · linear_combination -e11

theorem first_row_ne_zero (V : GL (Fin 2) K) :
    (V : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 ∨ (V : Matrix (Fin 2) (Fin 2) K) 0 1 ≠ 0 := by
  by_contra h
  push Not at h
  have hdet := (Matrix.GeneralLinearGroup.det V).ne_zero
  apply hdet
  change Matrix.det (V : Matrix (Fin 2) (Fin 2) K) = 0
  rw [Matrix.det_fin_two, h.1, h.2]
  ring

theorem mk_eq_one_of_entries {V : GL (Fin 2) K} (h01 : (V : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (h10 : (V : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h11 : (V : Matrix (Fin 2) (Fin 2) K) 1 1 = (V : Matrix (Fin 2) (Fin 2) K) 0 0) :
    ProjGenLinGroup.mk V = 1 := by
  rw [ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar]
  have h00 : (V : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := by
    rcases first_row_ne_zero V with h | h
    · exact h
    · exact absurd h01 h
  refine ⟨Units.mk0 _ h00, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, scalar_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h10, h11]

theorem mk_eq_mk_glA_of_entries {V : GL (Fin 2) K} (h00 : (V : Matrix (Fin 2) (Fin 2) K) 0 0 = 0)
    (h11 : (V : Matrix (Fin 2) (Fin 2) K) 1 1 = 0)
    (h10 : (V : Matrix (Fin 2) (Fin 2) K) 1 0 = -(V : Matrix (Fin 2) (Fin 2) K) 0 1) :
    ProjGenLinGroup.mk V = ProjGenLinGroup.mk glA := by
  have h01 : (V : Matrix (Fin 2) (Fin 2) K) 0 1 ≠ 0 := by
    rcases first_row_ne_zero V with h | h
    · exact absurd h00 h
    · exact h
  rw [ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨Units.mk0 (-((V : Matrix (Fin 2) (Fin 2) K) 0 1)⁻¹) (neg_ne_zero.2 (inv_ne_zero h01)), ?_⟩
  apply Units.ext
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, coe_glA,
    scalar_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h00, h11, h10, h01]

theorem pgl2_conj_rotation (h2 : (2 : K) ≠ 0) {V : GL (Fin 2) K}
    (hv2 : ProjGenLinGroup.mk V * ProjGenLinGroup.mk V = 1) (hv1 : ProjGenLinGroup.mk V ≠ 1)
    (hva : ProjGenLinGroup.mk V ≠ ProjGenLinGroup.mk glA)
    (hvc : ProjGenLinGroup.mk V * ProjGenLinGroup.mk glA =
      ProjGenLinGroup.mk glA * ProjGenLinGroup.mk V)
    {R : GL (Fin 2) K}
    (hR11 : (R : Matrix (Fin 2) (Fin 2) K) 1 1 = (R : Matrix (Fin 2) (Fin 2) K) 0 0)
    (hR10 : (R : Matrix (Fin 2) (Fin 2) K) 1 0 = -(R : Matrix (Fin 2) (Fin 2) K) 0 1) :
    ProjGenLinGroup.mk V * ProjGenLinGroup.mk R * ProjGenLinGroup.mk V =
      (ProjGenLinGroup.mk R)⁻¹ := by
  rw [← map_mul, ← map_mul, ProjGenLinGroup.mk_eq_mk_iff] at hvc
  obtain ⟨u, hu⟩ := hvc
  obtain ⟨e11, e10, e00, e01⟩ := entries_of_mul_glA hu
  set a := (V : Matrix (Fin 2) (Fin 2) K) 0 0 with ha
  set b := (V : Matrix (Fin 2) (Fin 2) K) 0 1 with hb
  have hu2 : (u : K) ^ 2 = 1 := by
    have h1 : a * ((u : K) ^ 2 - 1) = 0 := by
      linear_combination -e00 - (u : K) * e11
    have h2' : b * ((u : K) ^ 2 - 1) = 0 := by
      linear_combination -e01 + (u : K) * e10
    rcases first_row_ne_zero V with h | h
    · exact sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left h)
    · exact sub_eq_zero.1 ((mul_eq_zero.1 h2').resolve_left h)
  have hu' : (u : K) = 1 ∨ (u : K) = -1 := by
    have : ((u : K) - 1) * ((u : K) + 1) = 0 := by linear_combination hu2
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases hu' with hu1 | hum
  ·
    exfalso
    rw [hu1, mul_one] at e11 e10
    rw [← map_mul, ProjGenLinGroup.mk_eq_one,
      Matrix.GeneralLinearGroup.center_eq_range_scalar] at hv2
    obtain ⟨w, hw⟩ := hv2
    have hm := congrArg (fun X : GL (Fin 2) K => (X : Matrix (Fin 2) (Fin 2) K)) hw
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] at hm
    rw [coe_eq_of_entries V, e11, e10, scalar_fin_two, Matrix.mul_fin_two] at hm
    have h01 := congrFun (congrFun hm 0) 1
    simp at h01
    have hab : a * b = 0 := by
      have : (2 : K) * (a * b) = 0 := by linear_combination -h01
      exact (mul_eq_zero.1 this).resolve_left h2
    rcases mul_eq_zero.1 hab with h0 | h0
    · exact hva (mk_eq_mk_glA_of_entries h0 (by rw [e11, h0]) (by rw [e10]))
    · exact hv1 (mk_eq_one_of_entries h0 (by rw [e10, h0, neg_zero]) e11)
  ·
    rw [hum] at e11 e10
    simp only [mul_neg, mul_one, neg_neg] at e11 e10
    have hVRVR : ProjGenLinGroup.mk (V * R * V * R) = 1 := by
      rw [ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar]
      set r := (R : Matrix (Fin 2) (Fin 2) K) 0 0 with hr
      set s := (R : Matrix (Fin 2) (Fin 2) K) 0 1 with hs
      have hdetV : a ^ 2 + b ^ 2 ≠ 0 := by
        have hd := (Matrix.GeneralLinearGroup.det V).ne_zero
        intro h0
        apply hd
        change Matrix.det (V : Matrix (Fin 2) (Fin 2) K) = 0
        rw [Matrix.det_fin_two, e11, e10]
        linear_combination -h0
      have hdetR : r ^ 2 + s ^ 2 ≠ 0 := by
        have hd := (Matrix.GeneralLinearGroup.det R).ne_zero
        intro h0
        apply hd
        change Matrix.det (R : Matrix (Fin 2) (Fin 2) K) = 0
        rw [Matrix.det_fin_two, hR11, hR10]
        linear_combination h0
      refine ⟨Units.mk0 ((a ^ 2 + b ^ 2) * (r ^ 2 + s ^ 2)) (mul_ne_zero hdetV hdetR), ?_⟩
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
      simp only [Units.val_mul]
      rw [coe_eq_of_entries V, coe_eq_of_entries R, e11, e10, hR11, hR10, scalar_fin_two]
      simp only [Matrix.mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> ring
    have h1 : ProjGenLinGroup.mk V * ProjGenLinGroup.mk R * ProjGenLinGroup.mk V *
        ProjGenLinGroup.mk R = 1 := by
      rw [← map_mul, ← map_mul, ← map_mul]
      exact hVRVR
    exact eq_inv_of_mul_eq_one_left h1

theorem slMk_rot_mul_slA (c d : K) (h : c * c - d * -d = 1) :
    slMk c d (-d) c h * slA = slA * slMk c d (-d) c h := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_slMk, coe_slA]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem p2_conj_rotation (h2 : (2 : K) ≠ 0) {v : projectiveSL 2 K} (hv2 : v * v = 1)
    (hv1 : v ≠ 1) (hva : v ≠ proj 2 K slA) (hvc : v * proj 2 K slA = proj 2 K slA * v) {c d : K}
    (h : c * c - d * -d = 1) :
    v * proj 2 K (slMk c d (-d) c h) * v = (proj 2 K (slMk c d (-d) c h))⁻¹ := by
  apply p2PGL_injective
  rw [map_mul, map_mul, map_inv, p2PGL_proj]
  obtain ⟨V, hV⟩ := ProjGenLinGroup.mk_surjective (p2PGL K v)
  rw [← hV]
  have hA : p2PGL K (proj 2 K slA) = ProjGenLinGroup.mk glA := rfl
  refine pgl2_conj_rotation h2 ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hV, ← map_mul, hv2, map_one]
  · rw [hV]
    intro h1
    exact hv1 (p2PGL_injective (by rw [h1, map_one]))
  · rw [hV, ← hA]
    exact fun h1 => hva (p2PGL_injective h1)
  · rw [hV, ← hA, ← map_mul, ← map_mul, hvc]
  · simp [coe_slMk]
  · simp [coe_slMk]

end PGL

end CFSG.Quasithin.B45Exc
