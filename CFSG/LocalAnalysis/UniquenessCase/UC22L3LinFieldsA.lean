module

public import CFSG.LocalAnalysis.UniquenessCase.UC22L3LinBasic
public import CFSG.LocalAnalysis.UniquenessCase.UC22L3LinPGL
import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoprimeCentral

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.L3Lin

open Matrix Subgroup CFSG.GH74.KGroups.L3Eps CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] noncomputable def bG : GL (Fin 2) F →* GL (Fin 3) F where
  toFun M :=
    { val := bM (M : Matrix (Fin 2) (Fin 2) F)
      inv := bM ((M⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      val_inv := by rw [← bM_mul, Units.mul_inv, bM_one]
      inv_val := by rw [← bM_mul, Units.inv_mul, bM_one] }
  map_one' := Units.ext bM_one
  map_mul' M N := Units.ext (by simp only [Units.val_mul]; exact bM_mul _ _)

theorem coe_bG (M : GL (Fin 2) F) :
    ((bG M : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = bM (M : Matrix (Fin 2) (Fin 2) F) :=
  rfl

theorem bG_mem_CenG (M : GL (Fin 2) F) : bG M ∈ CenG F :=
  mem_CenG_of_entries (by simp [coe_bG, bM]) (by simp [coe_bG, bM]) (by simp [coe_bG, bM])
    (by simp [coe_bG, bM])

theorem blk_bM (M : Matrix (Fin 2) (Fin 2) F) : blk (bM M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk, bM]

theorem blkHom_bG (h2 : (2 : F) ≠ 0) (M : GL (Fin 2) F) :
    blkHom h2 ⟨bG M, bG_mem_CenG M⟩ = M :=
  Units.ext (by rw [coe_blkHom, coe_bG, blk_bM])

theorem rho_surjective [Finite F] (h2 : (2 : F) ≠ 0) :
    Function.Surjective (rho h2 (F := F)) := by
  intro g
  obtain ⟨M, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  exact ⟨piC ⟨bG M, bG_mem_CenG M⟩, by rw [rho_piC, blkHom_bG]⟩

theorem eight_dvd_card_range_rho [Finite F] (h2 : (2 : F) ≠ 0) (hq : Odd (Nat.card F)) :
    8 ∣ Nat.card (rho h2 (F := F)).range := by
  have : Fintype F := Fintype.ofFinite F
  rw [MonoidHom.range_eq_top_of_surjective _ (rho_surjective h2), Subgroup.card_top]
  exact eight_dvd_card_pgl_two (by rwa [← Nat.card_eq_fintype_card])

variable (F) in
noncomputable abbrev ZS : Subgroup (MulAut (projectiveSL 3 F)) :=
  CS F ⊓ centralizer (CS F : Set (MulAut (projectiveSL 3 F)))

theorem mem_ZS_iff {x : MulAut (projectiveSL 3 F)} :
    x ∈ ZS F ↔ x ∈ CS F ∧ ∀ y ∈ CS F, x * y = y * x := by
  rw [mem_inf, mem_centralizer_iff]
  exact and_congr_right fun _ => forall₂_congr fun _ _ => eq_comm

@[expose] noncomputable def t1 : GL (Fin 2) F :=
  ⟨!![1, 0; 0, -1], !![1, 0; 0, -1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [mul_fin_two_apply], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [mul_fin_two_apply]⟩

@[expose] noncomputable def t2 : GL (Fin 2) F :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [mul_fin_two_apply], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [mul_fin_two_apply]⟩

theorem rho_eq_one_iff [Finite F] (h2 : (2 : F) ≠ 0) (x : ↥(CS F)) :
    rho h2 x = 1 ↔ (x : MulAut (projectiveSL 3 F)) ∈ ZS F := by
  obtain ⟨A, rfl⟩ := piC_surjective x
  rw [rho_piC, pgl_mk_eq_one_iff, coe_blkHom, mem_ZS_iff]
  obtain ⟨h02, h12, h20, h21⟩ := entries_of_mem_CenG h2 A.2
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨(piC A).2, fun y hy => ?_⟩
    obtain ⟨B, hB⟩ := piC_surjective ⟨y, hy⟩
    have hyB : y = (piC B : MulAut (projectiveSL 3 F)) := congrArg Subtype.val hB.symm
    obtain ⟨k02, k12, k20, k21⟩ := entries_of_mem_CenG h2 B.2
    have c00 := congrFun (congrFun hc 0) 0
    have c01 := congrFun (congrFun hc 0) 1
    have c10 := congrFun (congrFun hc 1) 0
    have c11 := congrFun (congrFun hc 1) 1
    simp [blk] at c00 c01 c10 c11
    rw [hyB, coe_piC, coe_piC, ← map_mul, ← map_mul]
    congr 1
    apply Units.ext
    simp only [Units.val_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, h02, h12, h20, h21, k02, k12, k20, k21, c00,
        c01, c10, c11] <;> ring
  · rintro ⟨-, hcent⟩
    have hT : ∀ M : GL (Fin 2) F, A * ⟨bG M, bG_mem_CenG M⟩ = ⟨bG M, bG_mem_CenG M⟩ * A :=
      fun M => commute_of_piC h2 (Subtype.ext (hcent _ (piC ⟨bG M, bG_mem_CenG M⟩).2))
    have hm : ∀ M : GL (Fin 2) F, ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        bM (M : Matrix (Fin 2) (Fin 2) F) =
          bM (M : Matrix (Fin 2) (Fin 2) F) * ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) :=
      fun M => by
        have h := congrArg (fun B : ↥(CenG F) => ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
          (hT M)
        simpa only [Subgroup.coe_mul, Units.val_mul, coe_bG] using h
    have m1 := hm t1
    have m2 := hm t2
    have a01 := congrFun (congrFun m1 0) 1
    have a10 := congrFun (congrFun m1 1) 0
    have a00 := congrFun (congrFun m2 0) 1
    simp [t1, t2, bM, Matrix.mul_apply, Fin.sum_univ_three] at a01 a10 a00
    refine ⟨((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blk] <;> grind

theorem exists_of_mem_ZS [Finite F] (h2 : (2 : F) ≠ 0) {x : MulAut (projectiveSL 3 F)}
    (hx : x ∈ ZS F) :
    ∃ a : Fˣ, x = conjAut 3 F (bG (GeneralLinearGroup.scalar (Fin 2) a)) := by
  obtain ⟨A, hA⟩ := piC_surjective (⟨x, hx.1⟩ : ↥(CS F))
  have hxA : x = conjAut 3 F (A : GL (Fin 3) F) := (congrArg Subtype.val hA).symm
  have hρ := (rho_eq_one_iff h2 ⟨x, hx.1⟩).2 hx
  rw [← hA, rho_piC, pgl_mk_eq_one_iff, coe_blkHom] at hρ
  obtain ⟨c, hc⟩ := hρ
  obtain ⟨h02, h12, h20, h21⟩ := entries_of_mem_CenG h2 A.2
  have c00 := congrFun (congrFun hc 0) 0
  have c01 := congrFun (congrFun hc 0) 1
  have c10 := congrFun (congrFun hc 1) 0
  have c11 := congrFun (congrFun hc 1) 1
  simp [blk] at c00 c01 c10 c11
  set d := ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 with hd
  have hd0 : d ≠ 0 := corner_ne_zero h2 A.2
  have hc0 : c ≠ 0 := by
    intro h0
    have hdet := det_eq_of_mem_CenG h2 A.2
    rw [Matrix.det_fin_two] at hdet
    simp only [blk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at hdet
    rw [c00, c01, c10, c11, h0] at hdet
    simp only [mul_zero, sub_zero, zero_mul] at hdet
    exact (A : GL (Fin 3) F).isUnit.map Matrix.detMonoidHom |>.ne_zero hdet
  refine ⟨Units.mk0 (c / d) (div_ne_zero hc0 hd0), ?_⟩
  have hsc : (A : GL (Fin 3) F) = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 d hd0) *
      bG (GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (c / d) (div_ne_zero hc0 hd0))) := by
    apply Units.ext
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_bG]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [bM, h02, h12, h20, h21, c00, c01, c10, c11, ← hd] <;> field_simp
  rw [hxA, hsc, map_mul, (ProjectivePlane.conjAut_eq_one_iff (by norm_num) _).2 ⟨_, rfl⟩, one_mul]

theorem isCyclic_ZS [Finite F] (h2 : (2 : F) ≠ 0) : IsCyclic ↥(ZS F) := by
  set f : Fˣ →* MulAut (projectiveSL 3 F) :=
    (conjAut 3 F).comp (bG.comp (GeneralLinearGroup.scalar (Fin 2))) with hf
  have hle : ZS F ≤ f.range := fun x hx => by
    obtain ⟨a, ha⟩ := exists_of_mem_ZS h2 hx
    exact ⟨a, ha.symm⟩
  have : IsCyclic ↥f.range := isCyclic_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  exact isCyclic_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

variable (F) in
noncomputable abbrev KS : Subgroup (MulAut (projectiveSL 3 F)) :=
  (blockSub (F := F)).map (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F))

theorem toGL_bSL_mem_CenG (B : SL(2, F)) : SpecialLinearGroup.toGL (bSL B) ∈ CenG F := by
  rw [mem_centralizer_singleton_iff]
  rw [dG, ← map_mul, ← map_mul, bSL_mul_dNeg]

theorem piC_bSL (B : SL(2, F)) :
    (piC ⟨SpecialLinearGroup.toGL (bSL B), toGL_bSL_mem_CenG B⟩ : MulAut (projectiveSL 3 F)) =
      MulAut.conj (blockEmb B) := by
  rw [coe_piC, conjAut_toGL_eq]
  rfl

theorem blk_bSL (B : SL(2, F)) :
    blk (((SpecialLinearGroup.toGL (bSL B) : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) =
      (B : Matrix (Fin 2) (Fin 2) F) := by
  rw [SpecialLinearGroup.coe_GL_coe_matrix, coe_bSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk]

theorem KS_le_CS : KS F ≤ CS F := by
  rintro _ ⟨s, ⟨B, rfl⟩, rfl⟩
  rw [← piC_bSL]
  exact (piC _).2

theorem conj_injective_Y : Function.Injective
    (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)) := by
  intro a b hab
  have hc : b⁻¹ * a ∈ Subgroup.center (projectiveSL 3 F) := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h : a * z * a⁻¹ = b * z * b⁻¹ := by
      simpa only [MulAut.conj_apply] using congrArg (fun φ : MulAut _ => φ z) hab
    calc z * (b⁻¹ * a) = b⁻¹ * (b * z * b⁻¹) * a := by group
      _ = b⁻¹ * (a * z * a⁻¹) * a := by rw [h]
      _ = b⁻¹ * a * z := by group
  rw [center_projectiveSL_three_eq_bot, Subgroup.mem_bot] at hc
  calc a = b * (b⁻¹ * a) := by group
    _ = b := by rw [hc, mul_one]

theorem eq_one_of_mem_KS_ZS [Finite F] (h2 : (2 : F) ≠ 0) {x : MulAut (projectiveSL 3 F)}
    (hxK : x ∈ KS F) (hxZ : x ∈ ZS F) (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨s, ⟨B, rfl⟩, rfl⟩ := hxK
  have hρ := (rho_eq_one_iff h2 ⟨_, (piC ⟨_, toGL_bSL_mem_CenG B⟩).2⟩).2
    (by rw [piC_bSL]; exact hxZ)
  have hpi : (⟨_, (piC ⟨_, toGL_bSL_mem_CenG B⟩).2⟩ : ↥(CS F)) =
      piC ⟨_, toGL_bSL_mem_CenG B⟩ := rfl
  rw [hpi, rho_piC, pgl_mk_eq_one_iff, coe_blkHom, blk_bSL] at hρ
  obtain ⟨c, hc⟩ := hρ
  have hdet : c * c = 1 := by
    have := B.2
    rw [hc, Matrix.det_fin_two] at this
    simpa using this
  have hc1 : c = 1 ∨ c = -1 := by
    have : (c - 1) * (c + 1) = 0 := by linear_combination hdet
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases hc1 with rfl | rfl
  · have hB : B = 1 := Subtype.ext (by rw [hc, one_smul]; rfl)
    rw [hB, map_one, map_one]
  · exfalso
    have hB : B = -1 := Subtype.ext (by rw [hc]; simp)
    rw [hB, blockEmb_neg_one] at hodd
    have h2' : (MulAut.conj (tInv : projectiveSL 3 F)) ^ 2 = 1 := by
      rw [← map_pow, sq, tInv_mul_self, map_one]
    have hne : MulAut.conj (tInv : projectiveSL 3 F) ≠ 1 := fun h =>
      tInv_ne_one h2 (conj_injective_Y (by rw [h, map_one]))
    have hord : orderOf (MulAut.conj (tInv : projectiveSL 3 F)) = 2 :=
      orderOf_eq_prime h2' hne
    rw [hord] at hodd
    exact (Nat.not_odd_iff_even.2 even_two) hodd

theorem toGL_eSL_mem_CenG : SpecialLinearGroup.toGL (eSL : SL(3, F)) ∈ CenG F := by
  rw [mem_centralizer_singleton_iff, dG, ← map_mul, ← map_mul, ← eSL_sq, sq, mul_assoc]

theorem toGL_rSL_mem_CenG : SpecialLinearGroup.toGL (rSL : SL(3, F)) ∈ CenG F := by
  rw [mem_centralizer_singleton_iff, dG, ← map_mul, ← map_mul]
  congr 1
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_rSL, rMat, coe_dNeg, Matrix.mul_apply, Fin.sum_univ_three]

theorem eA_eq_piC :
    eA F = ((piC ⟨SpecialLinearGroup.toGL (eSL : SL(3, F)), toGL_eSL_mem_CenG⟩ : ↥(CS F)) :
      MulAut (projectiveSL 3 F)) := by
  rw [coe_piC, conjAut_toGL_eq]
  rfl

theorem rA_eq_piC :
    rA F = ((piC ⟨SpecialLinearGroup.toGL (rSL : SL(3, F)), toGL_rSL_mem_CenG⟩ : ↥(CS F)) :
      MulAut (projectiveSL 3 F)) := by
  rw [coe_piC, conjAut_toGL_eq]
  rfl

theorem coe_blkHom_eSL (h2 : (2 : F) ≠ 0) :
    ((blkHom h2 ⟨SpecialLinearGroup.toGL eSL, toGL_eSL_mem_CenG⟩ : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] := by
  rw [coe_blkHom]
  simp only [SpecialLinearGroup.coe_GL_coe_matrix, coe_eSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk, eMat]

theorem coe_blkHom_rSL (h2 : (2 : F) ≠ 0) :
    ((blkHom h2 ⟨SpecialLinearGroup.toGL rSL, toGL_rSL_mem_CenG⟩ : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = !![1, 0; 0, -1] := by
  rw [coe_blkHom]
  simp only [SpecialLinearGroup.coe_GL_coe_matrix, coe_rSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk, rMat]

theorem coe_blkHom_eSL_inv (h2 : (2 : F) ≠ 0) :
    (((blkHom h2 ⟨SpecialLinearGroup.toGL eSL, toGL_eSL_mem_CenG⟩)⁻¹ : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := by
  have h : blkHom h2 ⟨SpecialLinearGroup.toGL eSL, toGL_eSL_mem_CenG⟩ *
      ⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by
        ext i j; fin_cases i <;> fin_cases j <;> simp [mul_fin_two_apply], by
        ext i j; fin_cases i <;> fin_cases j <;> simp [mul_fin_two_apply]⟩ = 1 := by
    apply Units.ext
    rw [Units.val_mul, coe_blkHom_eSL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_fin_two_apply]
  rw [inv_eq_of_mul_eq_one_right h]

theorem rho_eA [Finite F] (h2 : (2 : F) ≠ 0) (he : eA F ∈ CS F) :
    rho h2 ⟨eA F, he⟩ =
      Matrix.ProjGenLinGroup.mk (blkHom h2 ⟨SpecialLinearGroup.toGL eSL, toGL_eSL_mem_CenG⟩) := by
  rw [← rho_piC]
  congr 1
  exact Subtype.ext eA_eq_piC

theorem rho_rA [Finite F] (h2 : (2 : F) ≠ 0) (hr : rA F ∈ CS F) :
    rho h2 ⟨rA F, hr⟩ =
      Matrix.ProjGenLinGroup.mk (blkHom h2 ⟨SpecialLinearGroup.toGL rSL, toGL_rSL_mem_CenG⟩) := by
  rw [← rho_piC]
  congr 1
  exact Subtype.ext rA_eq_piC

theorem rho_ne_lin [Finite F] (h2 : (2 : F) ≠ 0) (he : eA F ∈ CS F) (hr : rA F ∈ CS F) :
    rho h2 ⟨eA F, he⟩ ≠ 1 ∧ rho h2 ⟨rA F, hr⟩ ≠ 1 ∧ rho h2 ⟨eA F, he⟩ ≠ rho h2 ⟨rA F, hr⟩ := by
  rw [rho_eA h2 he, rho_rA h2 hr]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨c, hc⟩ := pgl_mk_eq_one_iff.1 h
    rw [coe_blkHom_eSL] at hc
    have := congrFun (congrFun hc 0) 1
    simp at this
  · obtain ⟨c, hc⟩ := pgl_mk_eq_one_iff.1 h
    rw [coe_blkHom_rSL] at hc
    have h0 := congrFun (congrFun hc 0) 0
    have h1 := congrFun (congrFun hc 1) 1
    simp at h0 h1
    apply h2
    linear_combination h0 - h1
  · obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.1 h
    have h0 := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) hu
    simp only [Units.val_mul, coe_blkHom_eSL, coe_blkHom_rSL, GeneralLinearGroup.coe_scalar] at h0
    simp at h0

theorem sq_eq_one_of_comm_rho [Finite F] (h2 : (2 : F) ≠ 0) (he : eA F ∈ CS F)
    (hr : rA F ∈ CS F) (g : PGL(Fin 2, F)) (h1 : g * rho h2 ⟨eA F, he⟩ = rho h2 ⟨eA F, he⟩ * g)
    (h2' : g * rho h2 ⟨rA F, hr⟩ = rho h2 ⟨rA F, hr⟩ * g) : g ^ 2 = 1 := by
  rw [rho_eA h2 he] at h1
  rw [rho_rA h2 hr] at h2'
  exact pgl_sq_eq_one_of_comm h2 (coe_blkHom_eSL h2) (coe_blkHom_rSL h2) g h1 h2'

theorem not_unip_lin [Finite F] {p : ℕ} [hp : Fact p.Prime] [CharP F p] (hp2 : p ≠ 2)
    (h2 : (2 : F) ≠ 0) (u : ↥(CS F)) (hρ : orderOf (rho h2 u) = p)
    (he : (u : MulAut (projectiveSL 3 F)) * (eA F * u * (eA F)⁻¹) = eA F * u * (eA F)⁻¹ * u)
    (hr : (u : MulAut (projectiveSL 3 F)) * (rA F * u * (rA F)⁻¹) = rA F * u * (rA F)⁻¹ * u) :
    False := by
  obtain ⟨A, rfl⟩ := piC_surjective u
  set E : ↥(CenG F) := ⟨SpecialLinearGroup.toGL eSL, toGL_eSL_mem_CenG⟩ with hE
  set R : ↥(CenG F) := ⟨SpecialLinearGroup.toGL rSL, toGL_rSL_mem_CenG⟩ with hR
  have hcE : A * (E * A * E⁻¹) = E * A * E⁻¹ * A := by
    refine commute_of_piC h2 (Subtype.ext ?_)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    rw [← eA_eq_piC]
    exact he
  have hcR : A * (R * A * R⁻¹) = R * A * R⁻¹ * A := by
    refine commute_of_piC h2 (Subtype.ext ?_)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    rw [← rA_eq_piC]
    exact hr
  have hRinv : R⁻¹ = R := by
    apply Subtype.ext
    simp only [Subgroup.coe_inv, hR, ← map_inv, rSL_inv]
  rw [hRinv] at hcR
  have mE := congrArg (fun B => ((blkHom h2 B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) hcE
  have mR := congrArg (fun B => ((blkHom h2 B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) hcR
  simp only [map_mul, map_inv, Units.val_mul] at mE mR
  rw [coe_blkHom_eSL_inv, coe_blkHom_eSL] at mE
  rw [coe_blkHom_rSL] at mR
  have hp1 : (rho h2 (piC A)) ^ p = 1 := by rw [← hρ]; exact pow_orderOf_eq_one _
  rw [rho_piC, ← map_pow, pgl_mk_eq_one_iff, Units.val_pow_eq_pow_val] at hp1
  obtain ⟨s, hs⟩ := hp1
  obtain ⟨c, hc⟩ := eq_scalar_of_comm_conj hp2 (by simpa only [mul_assoc] using mE)
    (by simpa only [mul_assoc] using mR) hs
  have h1 : rho h2 (piC A) = 1 := by
    rw [rho_piC, pgl_mk_eq_one_iff]
    exact ⟨c, hc⟩
  rw [h1, orderOf_one] at hρ
  exact hp.out.one_lt.ne hρ

@[expose] noncomputable def chiHom (h2 : (2 : F) ≠ 0) : ↥(CenG F) →* Fˣ where
  toFun A := Matrix.GeneralLinearGroup.det (blkHom h2 A) * (cornerHom h2 A ^ 2)⁻¹
  map_one' := by simp
  map_mul' A B := by
    simp only [map_mul, mul_pow, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

theorem chiHom_scalar (h2 : (2 : F) ≠ 0) (u : Fˣ) :
    chiHom h2 ⟨GeneralLinearGroup.scalar (Fin 3) u, scalar_mem_CenG u⟩ = 1 := by
  have hdet : Matrix.GeneralLinearGroup.det
      (blkHom h2 ⟨GeneralLinearGroup.scalar (Fin 3) u, scalar_mem_CenG u⟩) = u ^ 2 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, coe_blkHom, GeneralLinearGroup.coe_scalar,
      Matrix.det_fin_two]
    simp [blk, sq]
  have hc : cornerHom h2 ⟨GeneralLinearGroup.scalar (Fin 3) u, scalar_mem_CenG u⟩ = u := by
    apply Units.ext
    rw [coe_cornerHom, GeneralLinearGroup.coe_scalar]
    simp
  show Matrix.GeneralLinearGroup.det _ * (cornerHom h2 _ ^ 2)⁻¹ = 1
  rw [hdet, hc, mul_inv_cancel]

theorem mem_KS_of_inv [Finite F] (h2 : (2 : F) ≠ 0) (x w : ↥(CS F)) (hx : Odd (orderOf x))
    (hw : w * x * w⁻¹ = x⁻¹) : (x : MulAut (projectiveSL 3 F)) ∈ KS F := by
  obtain ⟨A, rfl⟩ := piC_surjective x
  obtain ⟨W, rfl⟩ := piC_surjective w
  have h1 : piC (W * A * W⁻¹ * A) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, hw, inv_mul_cancel]
  obtain ⟨u, hu⟩ := (ProjectivePlane.conjAut_eq_one_iff (by norm_num) _).1
    (congrArg Subtype.val h1)
  have hsq : chiHom h2 A ^ 2 = 1 := by
    have e : W * A * W⁻¹ * A = ⟨GeneralLinearGroup.scalar (Fin 3) u, scalar_mem_CenG u⟩ :=
      Subtype.ext hu
    have h := congrArg (chiHom h2) e
    rw [chiHom_scalar] at h
    simp only [map_mul, map_inv] at h
    rw [mul_right_comm (chiHom h2 W) (chiHom h2 A), mul_inv_cancel, one_mul] at h
    rw [sq, h]
  obtain ⟨k, hk⟩ := hx
  have hm : piC (A ^ orderOf (piC A)) = 1 := by rw [map_pow, pow_orderOf_eq_one]
  obtain ⟨v, hv⟩ := (ProjectivePlane.conjAut_eq_one_iff (by norm_num) _).1
    (congrArg Subtype.val hm)
  have hpow : chiHom h2 A ^ orderOf (piC A) = 1 := by
    have e : A ^ orderOf (piC A) = ⟨GeneralLinearGroup.scalar (Fin 3) v, scalar_mem_CenG v⟩ :=
      Subtype.ext hv
    rw [← map_pow, e, chiHom_scalar]
  have hχ : chiHom h2 A = 1 := by
    rw [hk, pow_succ, pow_mul, hsq, one_pow, one_mul] at hpow
    exact hpow
  set c := cornerHom h2 A with hc
  set A' : ↥(CenG F) := ⟨GeneralLinearGroup.scalar (Fin 3) c⁻¹, scalar_mem_CenG c⁻¹⟩ * A with hA'
  have hcs : cornerHom h2 ⟨GeneralLinearGroup.scalar (Fin 3) c⁻¹, scalar_mem_CenG c⁻¹⟩ = c⁻¹ :=
    Units.ext (by rw [coe_cornerHom, GeneralLinearGroup.coe_scalar]; simp)
  have hc' : cornerHom h2 A' = 1 := by rw [hA', map_mul, hcs, ← hc, inv_mul_cancel]
  have hχ' : chiHom h2 A' = 1 := by rw [hA', map_mul, chiHom_scalar, hχ, one_mul]
  have hdetb : Matrix.GeneralLinearGroup.det (blkHom h2 A') = 1 := by
    have h : Matrix.GeneralLinearGroup.det (blkHom h2 A') * (cornerHom h2 A' ^ 2)⁻¹ = 1 := hχ'
    rwa [hc', one_pow, inv_one, mul_one] at h
  have hdet : ((A' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [det_eq_of_mem_CenG h2 A'.2]
    have e1 : (blk ((A' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).det = 1 := by
      have := congrArg Units.val hdetb
      rwa [Matrix.GeneralLinearGroup.val_det_apply, coe_blkHom] at this
    have e2 : ((A' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by
      have := congrArg Units.val hc'
      rwa [coe_cornerHom] at this
    rw [e1, e2, mul_one]
  set g : SL(3, F) := ⟨((A' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F), hdet⟩ with hg
  have hgD : g ∈ CenD F := by
    rw [mem_CenD]
    exact Subtype.ext (mul_dG_of_mem A'.2)
  have hg22 : (g : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by
    have h := congrArg Units.val hc'
    rwa [coe_cornerHom] at h
  obtain ⟨B, hB⟩ := exists_bSL_of_g22 h2 hgD hg22
  refine ⟨blockEmb B, ⟨B, rfl⟩, ?_⟩
  have hAg : (A' : GL (Fin 3) F) = SpecialLinearGroup.toGL g :=
    Units.ext (by rw [SpecialLinearGroup.coe_GL_coe_matrix])
  have hconj : conjAut 3 F (A : GL (Fin 3) F) = conjAut 3 F (A' : GL (Fin 3) F) := by
    rw [hA', Subgroup.coe_mul, map_mul,
      (ProjectivePlane.conjAut_eq_one_iff (by norm_num) _).2 ⟨_, rfl⟩, one_mul]
  rw [coe_piC, hconj, hAg, ← hB, conjAut_toGL_eq]
  rfl

end CFSG.LocalAnalysis.UniquenessCase.UC22.L3Lin
