module

public import CFSG.GH74.GLS.IVK.Proofs2.Std44
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L3Facts
import CFSG.GH74.GLS.LU.Local.L3InvLin

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open Subgroup CFSG.Open CFSG.GH74.GLS.IVK CFSG.RankThree.CentralCover
  CFSG.RankThree.SubgroupLists
open CFSG.GH74.GLS.IVK.Proofs2
open CFSG.GH74.GLS.IVK.Proofs2.LinGenAux

variable {F : Type} [Field F] [Finite F]

theorem psl3_orderOf_linU₀ (hF : Odd (Nat.card F)) : orderOf (linU₀ F) = 2 := by
  have ht₃ : t₃ F * t₃ F = 1 := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, coe_t₃]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hsq : linU₀ F * linU₀ F = 1 := by
    rw [← projSL_t₃, ← map_mul, ht₃, map_one]
  have hne : linU₀ F ≠ 1 := by
    intro h1
    have hmem : t₃ F ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) :=
      (projSL_eq_one_iff F _).1 (by rw [projSL_t₃]; exact h1)
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hmem
    have h00 := congrFun (congrFun hr 0) 0
    have h22 := congrFun (congrFun hr 2) 2
    simp [coe_t₃] at h00 h22
    have hneg : (-1 : F) = 1 := h00.symm.trans h22
    have h2 : (2 : F) = 0 := by
      calc (2 : F) = 1 - (-1) := by ring
        _ = 1 - 1 := by rw [hneg]
        _ = 0 := by ring
    exact (CFSG.GorensteinWalter.two_ne_zero_of_odd_card F hF) h2
  exact orderOf_eq_prime (by simpa [sq] using hsq) hne

theorem psl3_conj (hF : Odd (Nat.card F)) (t : StatedProj (StatedSL 3 F)) (ht : orderOf t = 2) :
    ∃ g : StatedProj (StatedSL 3 F), g * linU₀ F * g⁻¹ = t := by
  have h2 : (2 : F) ≠ 0 := CFSG.GorensteinWalter.two_ne_zero_of_odd_card F hF
  have ht1 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht, sq] at this
  obtain ⟨a, ha, haeq⟩ := linConj_lift_involution (statedProjMk (StatedSL 3 F))
    (statedProjMk_surjective _) (fun z hz => linConj_ker_pow_three z hz) ht1
  have haGL : (a : GL (Fin 3) F) * (a : GL (Fin 3) F) = 1 := by
    simpa using congrArg Subtype.val ha
  have hneGL : (a : GL (Fin 3) F) ≠ 1 := by
    intro h
    have ha1 : a = 1 := Subtype.ext h
    have ht1 : t = 1 := by rw [← haeq, ha1, map_one]
    rw [ht1, orderOf_one] at ht
    omega
  have hdet : ((a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 :=
    (CFSG.Open.StatedAPI.mem_statedSL_iff).mp a.2
  obtain ⟨P, hP⟩ := CFSG.RankThree.SubgroupLists.exists_conj_negDiag3 h2 haGL hneGL hdet
  set δ : F := ((P : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det with hδ
  have hδ0 : δ ≠ 0 := by
    rw [hδ]
    exact (Matrix.isUnit_iff_isUnit_det _ |>.mp P.isUnit).ne_zero
  let Dm : Matrix (Fin 3) (Fin 3) F := Matrix.diagonal ![δ⁻¹, 1, 1]
  have hDdet : Dm.det = δ⁻¹ := by
    simp [Dm, Matrix.det_diagonal, Fin.prod_univ_three]
  let D : GL (Fin 3) F :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero Dm (by rw [hDdet]; exact inv_ne_zero hδ0)
  have hDcomm : D * negDiag3 F = negDiag3 F * D := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_negDiag3,
      Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Dm, Matrix.mul_apply, Fin.sum_univ_three]
  let M : GL (Fin 3) F := P * D
  have hMdet : ((M : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    change (((P * D : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F).det = 1
    rw [Units.val_mul, Matrix.det_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hDdet,
      hδ.symm, mul_inv_cancel₀ hδ0]
  have hM : M⁻¹ * (a : GL (Fin 3) F) * M = negDiag3 F := by
    change (P * D)⁻¹ * (a : GL (Fin 3) F) * (P * D) = negDiag3 F
    calc (P * D)⁻¹ * (a : GL (Fin 3) F) * (P * D)
        = D⁻¹ * (P⁻¹ * (a : GL (Fin 3) F) * P) * D := by group
      _ = D⁻¹ * negDiag3 F * D := by rw [hP]
      _ = negDiag3 F := by
          calc D⁻¹ * negDiag3 F * D = D⁻¹ * (negDiag3 F * D) := by group
            _ = D⁻¹ * (D * negDiag3 F) := by rw [hDcomm.symm]
            _ = negDiag3 F := by group
  let m : StatedSL 3 F := ⟨M, CFSG.Open.StatedAPI.mem_statedSL_of_det hMdet⟩
  let b : StatedSL 3 F := ⟨negDiag3 F, CFSG.Open.StatedAPI.mem_statedSL_of_det (by
    rw [coe_negDiag3, Matrix.det_diagonal, Fin.prod_univ_three]; norm_num)⟩
  have hm : m⁻¹ * a * m = b := Subtype.ext hM
  have hsl : slOdd₃ F = b := by
    refine Subtype.ext (Units.ext ?_)
    change ((oddDiag₃ F : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((negDiag3 F : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
    rw [linConj_coe_oddDiag₃, coe_negDiag3]
  have hm' : m * slOdd₃ F * m⁻¹ = a := by
    rw [hsl, ← hm]
    group
  have hlin : linU₀ F = statedProjMk (StatedSL 3 F) (slOdd₃ F) := rfl
  refine ⟨statedProjMk (StatedSL 3 F) m, ?_⟩
  calc statedProjMk (StatedSL 3 F) m * linU₀ F * (statedProjMk (StatedSL 3 F) m)⁻¹
      = statedProjMk (StatedSL 3 F) m * statedProjMk (StatedSL 3 F) (slOdd₃ F) *
          (statedProjMk (StatedSL 3 F) m)⁻¹ := by rw [hlin]
    _ = statedProjMk (StatedSL 3 F) (m * slOdd₃ F * m⁻¹) := by
          simp only [map_mul, map_inv]
    _ = statedProjMk (StatedSL 3 F) a := by rw [hm']
    _ = t := haeq

theorem psl3_quasi (hF : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) :
    CFSG.Open.IsQuasisimple ↥(derivedCent (linU₀ F)) := by
  have h2 : (2 : F) ≠ 0 := CFSG.GorensteinWalter.two_ne_zero_of_odd_card F hF
  have h4 : 4 ≤ Nat.card F := by omega
  let C : Subgroup (StatedProj (StatedSL 3 F)) :=
    Subgroup.centralizer ({linU₀ F} : Set (StatedProj (StatedSL 3 F)))
  let R : Subgroup (StatedProj (StatedSL 3 F)) := ((projSL F).comp (β₃ F)).range
  have hcomm_le : derivedCent (linU₀ F) ≤ R := by
    change ⁅C, C⁆ ≤ R
    rw [Subgroup.commutator_le]
    intro x hx y hy
    exact CFSG.GH74.GLS.LU.Local.L3InvLin.comm_mem_range₃ h2 hx hy
  have hR_le_C : R ≤ C := by
    rintro _ ⟨A, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← projSL_t₃, MonoidHom.comp_apply,
      ← map_mul, ← map_mul, β₃_commute]
  have hperfect : ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)),
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))⁆ = ⊤ :=
    Group.isPerfect_def.mp (CFSG.GH74.GLS.IVK.Lifted.isQuasisimple_sl2' h4).1
  have hRperf : ⁅R, R⁆ = R := by
    have h := Subgroup.map_commutator
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
      ((projSL F).comp (β₃ F))
    rw [hperfect] at h
    simpa [R, MonoidHom.range_eq_map] using h.symm
  have hR_le_derived : R ≤ derivedCent (linU₀ F) := by
    change R ≤ ⁅C, C⁆
    calc R = ⁅R, R⁆ := hRperf.symm
      _ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hR_le_C hR_le_C
  have hder : derivedCent (linU₀ F) = R := le_antisymm hcomm_le hR_le_derived
  have hinj : Function.Injective ((projSL F).comp (β₃ F)) := projSL_comp_β₃_injective F
  have e : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥(derivedCent (linU₀ F)) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hder.symm)
  have hSL2 : CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F) :=
    ⟨Group.isPerfect_def.mp (CFSG.GH74.GLS.IVK.Lifted.isQuasisimple_sl2' h4).1,
      (CFSG.GH74.GLS.IVK.Lifted.isQuasisimple_sl2' h4).2.1⟩
  exact CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hSL2

theorem psl3_gen (hF : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) (t : StatedProj (StatedSL 3 F))
    (ht : orderOf t = 2) (hc : linU₀ F * t = t * linU₀ F) (hne : linU₀ F ≠ t) :
    derivedCent (linU₀ F) ⊔ derivedCent t = ⊤ := by
  have h3 : 3 < Nat.card F := by omega
  obtain ⟨g, hg1, hg2⟩ := linConj F hF (linU₀ F) t (psl3_orderOf_linU₀ hF) ht hne hc
  have hg1' : (MulAut.conj g) (linU₀ F) = linU₀ F := by
    simpa [MulAut.conj_apply] using hg1
  have hg2' : (MulAut.conj g) t = linU₀' F := by
    simpa [MulAut.conj_apply] using hg2
  have hgen : Subgroup.closure ((Ez (linU₀ F) : Set (StatedProj (StatedSL 3 F))) ∪
      (Ez t : Set (StatedProj (StatedSL 3 F)))) = ⊤ :=
    closure_union_eq_top_of_map (MulAut.conj g) (Ez (linU₀ F)) (Ez t)
      (Ez (linU₀ F)) (Ez (linU₀' F))
      (by rw [Ez_map, hg1']) (by rw [Ez_map, hg2']) ((linGen F hF).1 h3)
  have hEz_le : ∀ z : StatedProj (StatedSL 3 F), Ez z ≤ derivedCent z := by
    intro z
    let C : Subgroup (StatedProj (StatedSL 3 F)) :=
      Subgroup.centralizer ({z} : Set (StatedProj (StatedSL 3 F)))
    change (CFSG.layer C).map C.subtype ≤ ⁅C, C⁆
    calc (CFSG.layer C).map C.subtype
        = (⁅CFSG.layer C, CFSG.layer C⁆).map C.subtype := by
            rw [CFSG.LocalCores.layer_perfect]
      _ = ⁅(CFSG.layer C).map C.subtype, (CFSG.layer C).map C.subtype⁆ := by
            rw [Subgroup.map_commutator (CFSG.layer C) (CFSG.layer C) C.subtype]
      _ ≤ ⁅C, C⁆ := Subgroup.commutator_mono (Subgroup.map_subtype_le _)
            (Subgroup.map_subtype_le _)
  rw [eq_top_iff, ← hgen]
  exact (Subgroup.closure_le _).mpr (Set.union_subset
    (fun x hx => Subgroup.mem_sup_left (hEz_le (linU₀ F) hx))
    (fun x hx => Subgroup.mem_sup_right (hEz_le t hx)))

theorem psl3_four (hF : Odd (Nat.card F)) :
    ∃ g : StatedProj (StatedSL 3 F), orderOf (linU₀ F * (g * linU₀ F * g⁻¹)) = 4 := by
  have h2 : (2 : F) ≠ 0 := CFSG.GorensteinWalter.two_ne_zero_of_odd_card F hF
  let t₁ : Matrix.SpecialLinearGroup (Fin 3) F :=
    ⟨!![-1, 0, 0; 0, 0, 1; 0, 1, 0], by
      rw [Matrix.det_fin_three]
      norm_num⟩
  let d : Matrix.SpecialLinearGroup (Fin 3) F :=
    ⟨Matrix.diagonal ![1, -1, -1], by
      simp [Matrix.det_diagonal, Fin.prod_univ_three]⟩
  have ht₁sq : t₁ * t₁ = 1 := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;> simp [t₁, Matrix.mul_apply, Fin.sum_univ_three]
  have ht₁notcenter : t₁ ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) := by
    intro hc
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
    have h00 := congrFun (congrFun hr 0) 0
    have h11 := congrFun (congrFun hr 1) 1
    simp [t₁] at h00 h11
    have h10 : (-1 : F) = 0 := h00.symm.trans h11
    exact one_ne_zero (neg_eq_zero.mp h10)
  have ht₁ne : t₁ ≠ 1 := fun h => ht₁notcenter (by rw [h]; exact Subgroup.one_mem _)
  have hdnot : d ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) := by
    intro hc
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
    have h00 := congrFun (congrFun hr 0) 0
    have h11 := congrFun (congrFun hr 1) 1
    simp [d] at h00 h11
    have hneg : (1 : F) = -1 := h00.symm.trans h11
    have h2' : (2 : F) = 0 := by
      calc (2 : F) = 1 - (-1) := by ring
        _ = 1 - 1 := congrArg (fun x : F => 1 - x) hneg.symm
        _ = 0 := by ring
    exact h2 h2'
  have hsq : (t₃ F * t₁) ^ 2 = d := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul, coe_t₃]
    fin_cases i <;> fin_cases j <;>
      simp [t₁, d, Matrix.mul_apply, Fin.sum_univ_three, pow_two]
  have hd2 : d * d = 1 := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;> simp [d, Matrix.mul_apply, Fin.sum_univ_three]
  have hu4 : (t₃ F * t₁) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hsq, pow_two, hd2]
  have hpow : (projSL F (t₃ F * t₁)) ^ 4 = 1 := by
    rw [← map_pow, hu4, map_one]
  have hnot : (projSL F (t₃ F * t₁)) ^ 2 ≠ 1 := by
    intro h
    have h' : projSL F ((t₃ F * t₁) ^ 2) = 1 := by
      rw [map_pow]
      exact h
    have hmem : (t₃ F * t₁) ^ 2 ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) :=
      (projSL_eq_one_iff F _).1 h'
    rw [hsq] at hmem
    exact hdnot hmem
  have hord : orderOf (projSL F t₁) = 2 := by
    apply orderOf_eq_prime
    · simp [sq, ← map_mul, ht₁sq]
    · intro h1
      exact ht₁notcenter ((projSL_eq_one_iff F t₁).1 h1)
  obtain ⟨g, hg⟩ := psl3_conj hF (projSL F t₁) hord
  refine ⟨g, ?_⟩
  rw [hg]
  have hprod : linU₀ F * projSL F t₁ = projSL F (t₃ F * t₁) := by
    rw [← projSL_t₃, ← map_mul]
  have h4 : orderOf (projSL F (t₃ F * t₁)) = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) hnot hpow
    simpa using this
  simpa [hprod] using h4

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
