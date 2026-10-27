module

public import CFSG.RankThree.Classical2.SLnRootAutomorphism

public import CFSG.LocalAnalysis.UniquenessCase.UC22L3LinL5
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismTransport
import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoprimeCentral
import CFSG.GH74.KGroups.L3EpsLin
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3L125Cop
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3L125W
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1OddL3Inputs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
import CFSG.GroupTheory.PCore.SubgroupCore
import CFSG.HardMathSupport.Solomon.LocalBalance.Defs
import CFSG.LocalAnalysis.GLTheoremB.UniqInputs
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.Walter.Defs
import Certificates.Certificate1
import Certificates.Certificate2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.L3Lin

open Matrix Subgroup CFSG.GH74.KGroups.L3Eps CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem mul_conj_mul_inv_Y (α : MulAut (projectiveSL 3 F)) (y : projectiveSL 3 F) :
    α * MulAut.conj y * α⁻¹ = MulAut.conj (α y) := by
  ext z
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem inn_normal_Y :
    (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range.Normal :=
  ⟨fun _ ⟨y, hy⟩ α => ⟨α y, by rw [← hy, mul_conj_mul_inv_Y]⟩⟩

theorem inndiag_normal_Y [Finite F] : (conjAut 3 F).range.Normal := by
  rw [← linearAutGroup_eq_range]
  exact linearAutGroup_normal_of_three_le (by norm_num)

theorem inn_le_inndiag_Y :
    (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range ≤ (conjAut 3 F).range := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨g, rfl⟩ := proj_surjective 3 F x
  exact ⟨SpecialLinearGroup.toGL g, conjAut_toGL_eq g⟩

theorem mem_inn_of_two_pow [Finite F] {g : MulAut (projectiveSL 3 F)}
    (hg : g ∈ (conjAut 3 F).range) {n : ℕ} (hn : g ^ 2 ^ n = 1) :
    g ∈ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range := by
  obtain ⟨A, rfl⟩ := hg
  obtain ⟨x, hx⟩ := conj_pow_inner A hn
  exact ⟨proj 3 F x, hx.symm⟩

theorem ringEquiv_eq_one_of_card_prime [Finite F] {p : ℕ} [hp : Fact p.Prime] [CharP F p]
    (hcard : Nat.card F = p) (σ : F ≃+* F) : σ = 1 := by
  have : Fintype F := Fintype.ofFinite F
  let f : ZMod p →+* F := ZMod.castHom (dvd_refl p) F
  have hsurj : Function.Surjective f := by
    have hc : Fintype.card (ZMod p) = Fintype.card F := by
      rw [ZMod.card, ← Nat.card_eq_fintype_card, hcard]
    exact ((Fintype.bijective_iff_injective_and_card f).2 ⟨f.injective, hc⟩).2
  have h := RingHom.ext_zmod ((σ : F →+* F).comp f) f
  apply RingEquiv.ext
  intro x
  obtain ⟨a, rfl⟩ := hsurj x
  exact RingHom.congr_fun h a

theorem dualAut_mul_self : dualAut 3 F * dualAut 3 F = 1 :=
  (standard_automorphism_transport (K := F) (n := 3)).2.2.2.1

theorem mem_inndiag_or_mul_dual [Finite F] (hσ : ∀ σ : F ≃+* F, σ = 1)
    (α : MulAut (projectiveSL 3 F)) :
    α ∈ (conjAut 3 F).range ∨ α * dualAut 3 F ∈ (conjAut 3 F).range := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := F) (n := 3) (by norm_num)
  obtain ⟨A, σ, ε, hε, rfl⟩ := hgen α
  rw [hσ σ, map_one, mul_one]
  interval_cases ε
  · exact Or.inl ⟨A, by rw [pow_zero, mul_one]⟩
  · exact Or.inr ⟨A, by rw [pow_one, mul_assoc, dualAut_mul_self, mul_one]⟩

theorem mul_mem_of_not_mem_lin [Finite F] (hσ : ∀ σ : F ≃+* F, σ = 1)
    {g h : MulAut (projectiveSL 3 F)} (hg : g ∉ (conjAut 3 F).range)
    (hh : h ∉ (conjAut 3 F).range) : g * h ∈ (conjAut 3 F).range := by
  have hg' := (mem_inndiag_or_mul_dual hσ g).resolve_left hg
  have hh' := (mem_inndiag_or_mul_dual hσ h).resolve_left hh
  have hδi : (dualAut 3 F)⁻¹ = dualAut 3 F := (eq_inv_of_mul_eq_one_left dualAut_mul_self).symm
  have hn := inndiag_normal_Y (F := F)
  have h1 : (dualAut 3 F)⁻¹ * (h * dualAut 3 F) * dualAut 3 F ∈ (conjAut 3 F).range := by
    have := hn.conj_mem _ hh' (dualAut 3 F)⁻¹
    rwa [inv_inv] at this
  have e : g * h = (g * dualAut 3 F) * ((dualAut 3 F)⁻¹ * (h * dualAut 3 F) * dualAut 3 F) := by
    rw [hδi]
    calc g * h = g * (dualAut 3 F * dualAut 3 F) * h * (dualAut 3 F * dualAut 3 F) := by
          rw [dualAut_mul_self, mul_one, mul_one]
      _ = (g * dualAut 3 F) * (dualAut 3 F * (h * dualAut 3 F) * dualAut 3 F) := by group
  rw [e]
  exact mul_mem hg' h1

theorem eA_sq_ne_one (h2 : (2 : F) ≠ 0) : eA F ^ 2 ≠ 1 := by
  rw [eA, ← map_pow, ← map_pow]
  intro h1
  have := conj_injective_Y (h1.trans (map_one _).symm)
  rw [eSL_sq] at this
  exact tInv_ne_one h2 (by rw [tInv, this])

theorem isPGroup_D8_lin :
    IsPGroup 2 ↥(Subgroup.closure ({eA F, rA F} : Set (MulAut (projectiveSL 3 F)))) :=
  isPGroup_closure_dihedral eA_pow_four rA_sq rA_eA

theorem isCyclic_cent_lin [Finite F] (h2 : (2 : F) ≠ 0) :
    IsCyclic ↥((MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range ⊓
      centralizer ({eA F, rA F} : Set (MulAut (projectiveSL 3 F)))) := by
  set f : Fˣ →* MulAut (projectiveSL 3 F) := MulAut.conj.comp psiLin with hf
  have hle : (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range ⊓
      centralizer ({eA F, rA F} : Set (MulAut (projectiveSL 3 F))) ≤ f.range := by
    intro x hx
    obtain ⟨⟨y, rfl⟩, hy⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨Y, rfl⟩ := proj_surjective 3 F y
    rw [mem_centralizer_iff] at hy
    have he := hy (eA F) (Set.mem_insert _ _)
    have hr := hy (rA F) (Set.mem_insert_of_mem _ rfl)
    rw [← conjAut_toGL_eq, eA_eq_conjAut] at he
    rw [← conjAut_toGL_eq, rA_eq_conjAut] at hr
    have he' := commute_of_conjAut (by
      rw [SpecialLinearGroup.coe_GL_coe_matrix, coe_eSL]
      simp [eMat, Matrix.trace_fin_three]) he.symm
    have hr' := commute_of_conjAut (by
      rw [SpecialLinearGroup.coe_GL_coe_matrix, coe_rSL]
      simp [rMat, Matrix.trace_fin_three]) hr.symm
    have hem : (Y : Matrix (Fin 3) (Fin 3) F) * eMat = eMat * (Y : Matrix (Fin 3) (Fin 3) F) := by
      have h := congrArg Units.val he'
      rwa [Units.val_mul, Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix,
        SpecialLinearGroup.coe_GL_coe_matrix, coe_eSL] at h
    have hrm : (Y : Matrix (Fin 3) (Fin 3) F) * rMat = rMat * (Y : Matrix (Fin 3) (Fin 3) F) := by
      have h := congrArg Units.val hr'
      rwa [Units.val_mul, Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix,
        SpecialLinearGroup.coe_GL_coe_matrix, coe_rSL] at h
    have hdiag := commute_diag h2 hem hrm
    have hdet : (Y : Matrix (Fin 3) (Fin 3) F).det = 1 := Y.2
    rw [hdiag, Matrix.det_diagonal] at hdet
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      mul_one] at hdet
    have ha0 : (Y : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := by
      intro h0
      rw [h0] at hdet
      simp at hdet
    refine ⟨Units.mk0 _ ha0, ?_⟩
    rw [hf, MonoidHom.comp_apply, psiLin, MonoidHom.comp_apply]
    congr 2
    have hb : (Y : Matrix (Fin 3) (Fin 3) F) 2 2 =
        ((Y : Matrix (Fin 3) (Fin 3) F) 0 0 * (Y : Matrix (Fin 3) (Fin 3) F) 0 0)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      linear_combination hdet
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [coe_diagHom]
    have hij := congrFun (congrFun hdiag i) j
    rw [hij]
    fin_cases i <;> fin_cases j <;> simp [hb]
  have : IsCyclic ↥f.range := isCyclic_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  exact Subgroup.isCyclic_of_le hle

theorem eA_sq_eq_conj_tInv : eA F ^ 2 = MulAut.conj (tInv : projectiveSL 3 F) := by
  rw [eA, ← map_pow, ← map_pow, eSL_sq]
  rfl

theorem fix_tInv_of_comm {g : MulAut (projectiveSL 3 F)} (hg : g * eA F ^ 2 = eA F ^ 2 * g) :
    g (tInv : projectiveSL 3 F) = tInv := by
  apply conj_injective_Y
  rw [← mul_conj_mul_inv_Y, ← eA_sq_eq_conj_tInv, hg, mul_inv_cancel_right]

theorem commutator_blockSub [Finite F] (h4 : 4 ≤ Nat.card F) :
    ⁅blockSub (F := F), blockSub (F := F)⁆ = blockSub (F := F) := by
  have : Group.IsPerfect ↥(blockSub (F := F)) := (isQuasisimple_blockSub (F := F) h4).1
  have h := congrArg (Subgroup.map (blockSub (F := F)).subtype)
    (Group.IsPerfect.commutator_eq_top (G := ↥(blockSub (F := F))))
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact h

theorem blockSub_eq_commutator [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) :
    (blockSub : Subgroup (projectiveSL 3 F)) =
      ⁅centralizer ({tInv} : Set (projectiveSL 3 F)),
        centralizer ({tInv} : Set (projectiveSL 3 F))⁆ := by
  apply le_antisymm
  · rw [← commutator_blockSub h4]
    exact Subgroup.commutator_mono blockSub_le_centralizer blockSub_le_centralizer
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    exact commutator_mem_blockSub h2 hx hy

theorem conj_mem_KS_lin [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    {g : MulAut (projectiveSL 3 F)} (hg : g * eA F ^ 2 = eA F ^ 2 * g)
    {x : MulAut (projectiveSL 3 F)} (hx : x ∈ KS F) : g * x * g⁻¹ ∈ KS F := by
  obtain ⟨b, hb, rfl⟩ := hx
  rw [mul_conj_mul_inv_Y]
  refine ⟨g b, ?_, rfl⟩
  have hfix := fix_tInv_of_comm hg
  have hN : (centralizer ({tInv} : Set (projectiveSL 3 F))).map
      (g : projectiveSL 3 F →* projectiveSL 3 F) ≤
        centralizer ({tInv} : Set (projectiveSL 3 F)) := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y * tInv = tInv * y := Subgroup.mem_centralizer_singleton_iff.1 hy
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    show g y * tInv = tInv * g y
    rw [← hfix, ← map_mul, ← map_mul, hy']
  rw [blockSub_eq_commutator h2 h4] at hb ⊢
  have hmap := Subgroup.map_commutator (centralizer ({tInv} : Set (projectiveSL 3 F)))
    (centralizer ({tInv} : Set (projectiveSL 3 F))) (g : projectiveSL 3 F →* projectiveSL 3 F)
  have hle : (⁅centralizer ({tInv} : Set (projectiveSL 3 F)),
      centralizer ({tInv} : Set (projectiveSL 3 F))⁆).map
        (g : projectiveSL 3 F →* projectiveSL 3 F) ≤
      ⁅centralizer ({tInv} : Set (projectiveSL 3 F)),
        centralizer ({tInv} : Set (projectiveSL 3 F))⁆ := by
    rw [hmap]
    exact Subgroup.commutator_mono hN hN
  exact hle ⟨b, hb, rfl⟩


theorem bSL_transpose (C : SL(2, F)) : (bSL C).transpose = bSL C.transpose := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_transpose, coe_bSL, coe_bSL,
    Matrix.SpecialLinearGroup.coe_transpose]
  fin_cases i <;> fin_cases j <;> simp


theorem dualAut_blockEmb (B : SL(2, F)) :
    dualAut 3 F (blockEmb B) =
      conjAut 3 F (SpecialLinearGroup.toGL (bSL (jSL : SL(2, F)))) (blockEmb B) := by
  rw [blockEmb_apply, dualAut_proj, conjAut_toGL_eq, MulAut.conj_apply, ← map_inv, ← map_mul,
    ← map_mul, ← map_inv, bSL_transpose, sl2_inv_transpose, map_mul, map_mul, map_inv]

theorem dualAut_tInv : dualAut 3 F (tInv : projectiveSL 3 F) = tInv := by
  rw [tInv, dualAut_proj]
  congr 1
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have h : (dNeg : SL(3, F))⁻¹ = dNeg := inv_eq_of_mul_eq_one_right dNeg_mul_self
  rw [h, Matrix.SpecialLinearGroup.coe_transpose, coe_dNeg]
  fin_cases i <;> fin_cases j <;> simp

theorem exists_conj_KS_lin [Finite F] (hσ : ∀ σ : F ≃+* F, σ = 1)
    {v : MulAut (projectiveSL 3 F)} (hv : v * eA F ^ 2 = eA F ^ 2 * v) :
    ∃ g ∈ CS F, ∀ x ∈ KS F, v * x * v⁻¹ = g * x * g⁻¹ := by
  rcases mem_inndiag_or_mul_dual hσ v with hvP | hvP
  · exact ⟨v, Subgroup.mem_inf.2 ⟨hvP, mem_centralizer_singleton_iff.2 hv⟩, fun _ _ => rfl⟩
  · obtain ⟨A, hA⟩ := hvP
    have hδi : (dualAut 3 F)⁻¹ = dualAut 3 F := (eq_inv_of_mul_eq_one_left dualAut_mul_self).symm
    have hvA : v = conjAut 3 F A * dualAut 3 F := by
      rw [hA, mul_assoc, dualAut_mul_self, mul_one]
    set J₃ := SpecialLinearGroup.toGL (bSL (jSL : SL(2, F))) with hJ₃
    refine ⟨conjAut 3 F (A * J₃), Subgroup.mem_inf.2 ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
    · rw [mem_centralizer_singleton_iff, map_mul]
      have hδ : dualAut 3 F * eA F ^ 2 = eA F ^ 2 * dualAut 3 F := by
        rw [eA_sq_eq_conj_tInv]
        calc dualAut 3 F * MulAut.conj tInv =
            dualAut 3 F * MulAut.conj tInv * (dualAut 3 F)⁻¹ * dualAut 3 F := by group
          _ = MulAut.conj tInv * dualAut 3 F := by rw [mul_conj_mul_inv_Y, dualAut_tInv]
      have hAz : conjAut 3 F A * eA F ^ 2 = eA F ^ 2 * conjAut 3 F A := by
        have h1 : conjAut 3 F A = v * (dualAut 3 F)⁻¹ := by rw [hvA, mul_inv_cancel_right]
        rw [h1, hδi]
        calc v * dualAut 3 F * eA F ^ 2 = v * (dualAut 3 F * eA F ^ 2) := by group
          _ = v * (eA F ^ 2 * dualAut 3 F) := by rw [hδ]
          _ = (v * eA F ^ 2) * dualAut 3 F := by group
          _ = eA F ^ 2 * (v * dualAut 3 F) := by rw [hv]; group
      have hJz := conjAut_comm_e_sq_of_mem (toGL_bSL_mem_CenG (jSL : SL(2, F)))
      calc conjAut 3 F A * conjAut 3 F J₃ * eA F ^ 2 =
          conjAut 3 F A * (conjAut 3 F J₃ * eA F ^ 2) := by group
        _ = conjAut 3 F A * (eA F ^ 2 * conjAut 3 F J₃) := by rw [hJz]
        _ = (conjAut 3 F A * eA F ^ 2) * conjAut 3 F J₃ := by group
        _ = eA F ^ 2 * (conjAut 3 F A * conjAut 3 F J₃) := by rw [hAz]; group
    · rintro _ ⟨b, ⟨B, rfl⟩, rfl⟩
      rw [mul_conj_mul_inv_Y, mul_conj_mul_inv_Y, hvA, MulAut.mul_apply, dualAut_blockEmb, map_mul,
        MulAut.mul_apply]

theorem comm_of_coprime_six_lin [Finite F] {p : ℕ} (hp2 : p ≠ 2)
    (hY : CFSG.Open.StatedClassicalModel (projectiveSL 3 F) .PSL 3 p 1)
    {y : MulAut (projectiveSL 3 F)} (hy6 : Nat.Coprime (orderOf y) 6)
    {R : Subgroup (MulAut (projectiveSL 3 F))} (hR : IsPGroup 2 R)
    (hyR : y ∈ normalizer (R : Set (MulAut (projectiveSL 3 F)))) :
    ∀ x ∈ R, y * x = x * y := by
  have : Finite (projectiveSL 3 F) := Finite.of_surjective (proj 3 F) (proj_surjective 3 F)
  exact CFSG.RankThree.PartTwo.Sec15.Sylow155R3.res3L125_centralizes_of_normalizes
    center_projectiveSL_three_eq_bot
    (CFSG.RankThree.PartTwo.Sec15.Sylow155R1.res1OddL3_odd_commutator_outer (Or.inl hY))
    (CFSG.RankThree.PartTwo.Sec15.Sylow155R1.res1OddL3_abelian_index_le_two hp2 (Or.inl hY))
    (CFSG.RankThree.PartTwo.Sec15.Sylow155R1.res1OddL3_card_elemAbelian_le_four hp2 (Or.inl hY))
    (fun _ _ _ hR' _ hA hidx hE _ hβ =>
      CFSG.RankThree.PartTwo.Sec15.Sylow155R3.res3L125_eq_one_of_coprime_six hR' hA hidx hE hβ)
    hR hyR hy6

end CFSG.LocalAnalysis.UniquenessCase.UC22.L3Lin
