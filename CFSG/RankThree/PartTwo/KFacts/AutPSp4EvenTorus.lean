module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
public import CFSG.Quasithin.H13.L32ACSkPfSp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveSp

public section

namespace CFSG.RankThree.PartTwo.KFacts

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.QuasithinUnique.Lin2.Five CFSG.Quasithin.H13.L32A.C.SkPf
open Matrix
open scoped CharTwo

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem projEquiv_apply (x : StatedSp 2 K) : projEquiv K x = proj 2 K x := rfl

omit [Finite K] [CharP K 2] in
theorem torusHom_sub_scalar (t : Fin 2 → Kˣ) (c : K) :
    (((torusHom t : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) - c • 1 =
      Matrix.diagonal (fun i => Sum.elim (fun j : Fin 2 => (t j : K))
        (fun j : Fin 2 => ((t j)⁻¹ : K)) i - c) := by
  rw [coe_torusHom, Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_sub]
  congr 1
  funext i
  simp [Pi.sub_apply]

omit [Finite K] [CharP K 2] in
theorem det_torusHom_sub_scalar (t : Fin 2 → Kˣ) (c : K) :
    ((((torusHom t : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) - c • 1).det =
      ∏ i, (Sum.elim (fun j : Fin 2 => (t j : K))
        (fun j : Fin 2 => ((t j)⁻¹ : K)) i - c) := by
  rw [torusHom_sub_scalar, Matrix.det_diagonal]

omit [Finite K] [CharP K 2] in
theorem det_torusHom_one_sub_scalar (a : Kˣ) (c : K) :
    ((((torusHom ![a, 1] : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) - c • 1).det =
      ((a : K) - c) * (1 - c) * (((a : K)⁻¹) - c) * (1 - c) := by
  rw [det_torusHom_sub_scalar, Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_two]
  simp
  ring

omit [Finite K] [CharP K 2] in
theorem det_torusHom_diag_sub_scalar (s : Kˣ) (c : K) :
    ((((torusHom ![s, s] : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) - c • 1).det =
      ((s : K) - c) * ((s : K) - c) * (((s : K)⁻¹) - c) * (((s : K)⁻¹) - c) := by
  rw [det_torusHom_sub_scalar, Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_two]
  simp
  ring

omit [Finite K] [CharP K 2] in
theorem det_torusHom_sub_scalar_eq_of_conj {s t : Fin 2 → Kˣ} {Y : StatedSp 2 K}
    (h : Y * torusHom t * Y⁻¹ = torusHom s) (c : K) :
    ((((torusHom s : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) - c • 1).det =
      ((((torusHom t : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) - c • 1).det := by
  set Ymat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
    ((Y : GL (Fin 2 ⊕ Fin 2) K)).1
  set Smat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
    ((torusHom s : GL (Fin 2 ⊕ Fin 2) K)).1
  set Tmat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
    ((torusHom t : GL (Fin 2 ⊕ Fin 2) K)).1
  have hmat : Ymat * Tmat * Ymat⁻¹ = Smat := by
    have := congrArg (fun z : StatedSp 2 K => ((z : GL (Fin 2 ⊕ Fin 2) K)).1) h
    simpa [Ymat, Smat, Tmat, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul,
      Units.val_inv_eq_inv_val] using this
  have hY : Ymat * Ymat⁻¹ = 1 := by
    rw [show Ymat⁻¹ = ((Y : GL (Fin 2 ⊕ Fin 2) K)⁻¹).1 from
      (Matrix.GeneralLinearGroup.coe_inv (A := (Y : GL (Fin 2 ⊕ Fin 2) K))).symm]
    rw [show Ymat = ((Y : GL (Fin 2 ⊕ Fin 2) K)).1 from rfl]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hcs : Ymat * (c • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) * Ymat⁻¹ =
      c • 1 := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hY]
  have hconj : Smat - c • 1 = Ymat * (Tmat - c • 1) * Ymat⁻¹ := by
    rw [← hmat, Matrix.mul_sub, Matrix.sub_mul, hcs]
  rw [hconj]
  simpa [Ymat, Matrix.GeneralLinearGroup.coe_inv] using
    Matrix.det_units_conj (Y : GL (Fin 2 ⊕ Fin 2) K) (Tmat - c • 1)

omit [Finite K] [CharP K 2] in
theorem sp4T_fieldAut_one (σ : K ≃+* K) (a : Kˣ) :
    fieldAut 2 K σ (sp4T K ![a, 1]) = sp4T K ![Units.map σ.toRingHom.toMonoidHom a, 1] := by
  rw [fieldAut_sp4T]
  congr 1
  funext i
  fin_cases i <;> simp

theorem sp4T_fieldAut_tauAut_diag (σ : K ≃+* K) (s : Kˣ) :
    (fieldAut 2 K σ * (tauAut : MulAut (StatedProj (StatedSp 2 K)))) (sp4T K ![s, s]) =
      sp4T K ![(Units.map σ.toRingHom.toMonoidHom s) ^ 2, 1] := by
  rw [MulAut.mul_apply, tauAut_sp4T, fieldAut_sp4T]
  congr 1
  funext i
  fin_cases i <;> simp [spTau, pow_two]

theorem conj_mul_fieldAut_tauAut_sp4T_diag (y : StatedProj (StatedSp 2 K)) (σ : K ≃+* K)
    (s : Kˣ) :
    (MulAut.conj y * (fieldAut 2 K σ * (tauAut : MulAut (StatedProj (StatedSp 2 K)))))
      (sp4T K ![s, s]) =
      y * sp4T K ![(Units.map σ.toRingHom.toMonoidHom s) ^ 2, 1] * y⁻¹ := by
  conv_lhs => rw [MulAut.mul_apply]
  rw [MulAut.conj_apply, sp4T_fieldAut_tauAut_diag]

omit [Finite K] in
theorem lift_torus_eq {y : StatedProj (StatedSp 2 K)} {Y : StatedSp 2 K}
    (hY : projEquiv K Y = y) {s t : Fin 2 → Kˣ}
    (h : y * sp4T K t * y⁻¹ = sp4T K s) : Y * torusHom t * Y⁻¹ = torusHom s := by
  apply (projEquiv K).injective
  calc projEquiv K (Y * torusHom t * Y⁻¹)
      = y * sp4T K t * y⁻¹ := by
        rw [map_mul, map_mul, map_inv, hY, projEquiv_apply]
        rfl
    _ = sp4T K s := h
    _ = projEquiv K (torusHom s) := by rw [projEquiv_apply]; rfl

omit [Finite K] in
theorem fieldAut_apply_eq_self_or_one_or_inv {a : Kˣ} {σ : K ≃+* K} {Y : StatedSp 2 K}
    (h : Y * torusHom ![Units.map σ.toRingHom.toMonoidHom a, 1] * Y⁻¹ =
      torusHom ![a, 1]) :
    σ (a : K) = (a : K) ∨ σ (a : K) = 1 ∨ σ (a : K) = ((a : K)⁻¹) := by
  set c : K := σ (a : K)
  have hdet := det_torusHom_sub_scalar_eq_of_conj h c
  have hzero : ((((torusHom ![Units.map σ.toRingHom.toMonoidHom a, 1] : StatedSp 2 K) :
      GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) - c • 1).det = 0 := by
    rw [det_torusHom_one_sub_scalar]
    simp [c]
  have hdet0 : ((((torusHom ![a, 1] : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) - c • 1).det = 0 := hdet.trans hzero
  rw [det_torusHom_one_sub_scalar] at hdet0
  rcases mul_eq_zero.mp hdet0 with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl (sub_eq_zero.mp h).symm
      · exact Or.inr (Or.inl (sub_eq_zero.mp h).symm)
    · exact Or.inr (Or.inr (sub_eq_zero.mp h).symm)
  · exact Or.inr (Or.inl (sub_eq_zero.mp h).symm)

omit [Finite K] in
theorem eq_or_eq_add_one_of_sq_add_self_add_one {x y : K}
    (hx : x * x + x + 1 = 0) (hy : y * y + y + 1 = 0) : y = x ∨ y = x + 1 := by
  have hsum : x * x + y * y + x + y = 0 := by
    have h2 : (x * x + x + 1) + (y * y + y + 1) = 0 := by rw [hx, hy, add_zero]
    have h3 : x * x + y * y + x + y + (1 + 1) = 0 := by rw [← h2]; abel
    simpa using h3
  have hxy : (x + y) * (x + y + 1) = 0 := by
    calc (x + y) * (x + y + 1) = (x + y) * (x + y) + (x + y) := by ring
      _ = (x * x + y * y) + (x + y) := by rw [CharTwo.add_mul_self]
      _ = 0 := by rw [← hsum]; abel
  rcases mul_eq_zero.mp hxy with h | h
  · left
    have h' : x + y = x + x := by rw [h, CharTwo.add_self_eq_zero]
    exact add_left_cancel h'
  · right
    have h1 : x + y = 1 := by
      have h2 := eq_neg_of_add_eq_zero_left h
      rwa [CharTwo.neg_eq] at h2
    have hxx : x + (x + 1) = 1 := by
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    have h' : x + y = x + (x + 1) := by rw [h1, hxx]
    exact add_left_cancel h'

theorem ringEquiv_eq_one_of_generator (hK : 8 ≤ Nat.card K) (σ : K ≃+* K) (g : Kˣ)
    (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g)
    (hσ : σ (g : K) = (g : K) ∨ σ (g : K) = ((g : K)⁻¹)) : σ = 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hgenu : Units.map σ.toRingHom.toMonoidHom g = g ∨
      Units.map σ.toRingHom.toMonoidHom g = g⁻¹ := by
    rcases hσ with h | h
    · exact Or.inl (Units.ext (by simpa using h))
    · exact Or.inr (Units.ext (by simpa using h))
  rcases hgenu with hgen | hgen
  · ext x
    by_cases hx : x = 0
    · rw [hx, map_zero, map_zero]
    · let u : Kˣ := Units.mk0 x hx
      have hu : u ∈ Subgroup.zpowers g := hg u
      rw [Subgroup.mem_zpowers_iff] at hu
      obtain ⟨n, hn⟩ := hu
      have hσu : Units.map σ.toRingHom.toMonoidHom u = u := by
        rw [← hn, map_zpow, hgen]
      have := congrArg Units.val hσu
      simpa [u, Units.coe_map] using this
  · exfalso
    have hinv : ∀ x : K, x ≠ 0 → σ x = x⁻¹ := by
      intro x hx0
      let u : Kˣ := Units.mk0 x hx0
      have hu : u ∈ Subgroup.zpowers g := hg u
      rw [Subgroup.mem_zpowers_iff] at hu
      obtain ⟨n, hn⟩ := hu
      have hσu : Units.map σ.toRingHom.toMonoidHom u = u⁻¹ := by
        rw [← hn, map_zpow, hgen, _root_.inv_zpow]
      have := congrArg Units.val hσu
      simpa [u, Units.coe_map] using this
    have hquad : ∀ x : K, x ≠ 0 → x ≠ 1 → x * x + x + 1 = 0 := by
      intro x hx0 hx1
      have hx1' : x + 1 ≠ 0 := by
        intro h
        rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
        exact hx1 h
      have h1 : x⁻¹ + 1 = (x + 1)⁻¹ := by
        calc x⁻¹ + 1 = σ x + σ 1 := by rw [hinv x hx0, map_one]
          _ = σ (x + 1) := (map_add σ x 1).symm
          _ = (x + 1)⁻¹ := hinv (x + 1) hx1'
      have e : x⁻¹ + 1 = x⁻¹ * (x + 1) := by
        rw [mul_add, mul_one, inv_mul_cancel₀ hx0]
        abel
      have h5 : x + 1 = (x + 1)⁻¹ * x := by
        calc x + 1 = (x⁻¹ + 1)⁻¹ := by rw [h1, inv_inv]
          _ = (x⁻¹ * (x + 1))⁻¹ := by rw [e]
          _ = (x + 1)⁻¹ * x := by rw [_root_.mul_inv_rev, inv_inv]
      have h6 : (x + 1) * (x + 1) = x := by
        have h := congrArg (fun y => y * (x + 1)) h5
        rw [mul_assoc, mul_comm x (x + 1), ← mul_assoc, inv_mul_cancel₀ hx1', one_mul] at h
        exact h
      have h7 : x * x + 1 = x := by
        have h := h6
        rw [CharTwo.add_mul_self] at h
        simpa using h
      calc x * x + x + 1 = (x * x + 1) + x := by abel
        _ = x + x := by rw [h7]
        _ = 0 := CharTwo.add_self_eq_zero x
    have hS : 2 < (Finset.univ.filter fun x : K => x ≠ 0 ∧ x ≠ 1).card := by
      have hcard : (Finset.univ.filter fun x : K => x ≠ 0 ∧ x ≠ 1).card =
          Nat.card K - 2 := by
        have hS_eq : (Finset.univ.filter fun x : K => x ≠ 0 ∧ x ≠ 1) =
            (Finset.univ.erase (0 : K)).erase 1 := by
          ext x
          simp [and_comm]
        rw [hS_eq, Finset.card_erase_of_mem (by simp), Finset.card_erase_of_mem (by simp),
          Finset.card_univ, Nat.card_eq_fintype_card]
        have hK' : 8 ≤ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
        omega
      rw [hcard]
      omega
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hS
    have ha' : a ≠ 0 ∧ a ≠ 1 := by simpa using ha
    have hb' : b ≠ 0 ∧ b ≠ 1 := by simpa using hb
    have hc' : c ≠ 0 ∧ c ≠ 1 := by simpa using hc
    have hqa : a * a + a + 1 = 0 := hquad a ha'.1 ha'.2
    have hqb : b * b + b + 1 = 0 := hquad b hb'.1 hb'.2
    have hqc : c * c + c + 1 = 0 := hquad c hc'.1 hc'.2
    rcases eq_or_eq_add_one_of_sq_add_self_add_one hqa hqb with hba | hba
    · exact hab hba.symm
    rcases eq_or_eq_add_one_of_sq_add_self_add_one hqa hqc with hca | hca
    · exact hac hca.symm
    · exact hbc (hba.trans hca.symm)

omit [Finite K] in
theorem exists_conjAut_of_proj_conj (α : MulAut (StatedSp 2 K))
    (h : ∃ y : StatedProj (StatedSp 2 K),
      (projEquiv K).symm.trans (α.trans (projEquiv K)) = MulAut.conj y) :
    ∃ Y : StatedSp 2 K, α = MulAut.conj Y := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨Y, hY⟩ := (projEquiv K).surjective y
  refine ⟨Y, ?_⟩
  apply MulEquiv.ext
  intro x
  calc α x = (projEquiv K).symm
        ((projEquiv K).symm.trans (α.trans (projEquiv K)) (projEquiv K x)) := by
        simp [MulEquiv.trans_apply]
    _ = (projEquiv K).symm (y * projEquiv K x * y⁻¹) := by rw [hy, MulAut.conj_apply]
    _ = Y * x * Y⁻¹ := by rw [← hY]; simp
    _ = MulAut.conj Y x := by rw [MulAut.conj_apply]

theorem tauAut_pow_eq_zero_of_fix_torus (hK : 8 ≤ Nat.card K)
    (y : StatedProj (StatedSp 2 K)) (σ : K ≃+* K) {ε : ℕ} (hε : ε ≤ 1)
    (h : ∀ t : Fin 2 → Kˣ,
      (MulAut.conj y * (fieldAut 2 K σ * (tauAut : MulAut (StatedProj (StatedSp 2 K))) ^ ε))
        (sp4T K t) = sp4T K t) :
    ε = 0 := by
  rcases Nat.eq_zero_or_pos ε with h0 | hpos
  · exact h0
  · exfalso
    have hε1 : ε = 1 := by omega
    have hs : ∃ s : Kˣ, s ≠ 1 := by
      have h1 : 1 < Nat.card Kˣ := by rw [Nat.card_units]; omega
      haveI : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.mp h1
      exact exists_ne 1
    obtain ⟨s, hs⟩ := hs
    have hkey : y * sp4T K ![(Units.map σ.toRingHom.toMonoidHom s) ^ 2, 1] * y⁻¹ =
        sp4T K ![s, s] := by
      have h := h ![s, s]
      rw [hε1, pow_one, conj_mul_fieldAut_tauAut_sp4T_diag] at h
      exact h
    obtain ⟨Y, hY⟩ := (projEquiv K).surjective y
    have hgrp := lift_torus_eq hY hkey
    have hdet := det_torusHom_sub_scalar_eq_of_conj hgrp 1
    have hzero : ((((torusHom ![(Units.map σ.toRingHom.toMonoidHom s) ^ 2, 1] :
        StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) - (1 : K) • 1).det = 0 := by
      rw [det_torusHom_one_sub_scalar]
      simp
    have hne : ((((torusHom ![s, s] : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) - (1 : K) • 1).det ≠ 0 := by
      rw [det_torusHom_diag_sub_scalar]
      have hs1 : (s : K) - 1 ≠ 0 :=
        sub_ne_zero.mpr (fun h' => hs (Units.ext h'))
      have hsi : ((s : K)⁻¹) - 1 ≠ 0 :=
        sub_ne_zero.mpr (fun h' => hs (Units.ext (inv_eq_one.mp h')))
      simpa only [mul_assoc] using mul_ne_zero (mul_ne_zero hs1 hs1) (mul_ne_zero hsi hsi)
    exact hne (hdet.trans hzero)

theorem exists_conjAut_proj_of_fix_torus_sp4 (hK : 8 ≤ Nat.card K)
    (α : MulAut (StatedSp 2 K)) (hα : ∀ d ∈ torus 2 K, α d = d) :
    ∃ y : StatedProj (StatedSp 2 K),
      (projEquiv K).symm.trans (α.trans (projEquiv K)) = MulAut.conj y := by
  let α' : MulAut (StatedProj (StatedSp 2 K)) :=
    (projEquiv K).symm.trans (α.trans (projEquiv K))
  have hα'apply : ∀ x : StatedSp 2 K, α' (projEquiv K x) = projEquiv K (α x) := by
    intro x
    simp [α', MulEquiv.trans_apply]
  have hα'T : ∀ t : Fin 2 → Kˣ, α' (sp4T K t) = sp4T K t := by
    intro t
    have h1 : sp4T K t = projEquiv K (torusHom t) := rfl
    rw [h1, hα'apply, hα (torusHom t) (torusHom_mem_torus t)]
  obtain ⟨y, σ, ε, hε, hαeq⟩ := exists_conj_mul_std_sp4 α'
  have hfix : ∀ t : Fin 2 → Kˣ,
      (MulAut.conj y * (fieldAut 2 K σ * (tauAut : MulAut (StatedProj (StatedSp 2 K))) ^ ε))
        (sp4T K t) = sp4T K t := by
    intro t
    rw [← hαeq]
    exact hα'T t
  have hε0 : ε = 0 := tauAut_pow_eq_zero_of_fix_torus hK y σ hε hfix
  have hα'0 : α' = MulAut.conj y * fieldAut 2 K σ := by
    rw [hαeq, hε0, pow_zero, mul_one]
  have hσ1 : σ = 1 := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
    have hkeyg : y * sp4T K ![Units.map σ.toRingHom.toMonoidHom g, 1] * y⁻¹ =
        sp4T K ![g, 1] := by
      have h := hα'T ![g, 1]
      rw [hα'0] at h
      rw [MulAut.mul_apply, MulAut.conj_apply, sp4T_fieldAut_one] at h
      exact h
    obtain ⟨Yg, hYg⟩ := (projEquiv K).surjective y
    have hgrpg := lift_torus_eq hYg hkeyg
    have h3 := fieldAut_apply_eq_self_or_one_or_inv hgrpg
    have hσg : σ (g : K) = (g : K) ∨ σ (g : K) = ((g : K)⁻¹) := by
      rcases h3 with h | h | h
      · exact Or.inl h
      · left
        have hg1 : g = 1 := Units.ext (σ.injective (by rw [h]; exact (map_one σ).symm))
        rw [hg1]
        simp
      · exact Or.inr h
    exact ringEquiv_eq_one_of_generator hK σ g hg hσg
  have hα'final : α' = MulAut.conj y := by
    rw [hα'0, hσ1, map_one, mul_one]
  exact ⟨y, hα'final⟩

theorem mem_range_conj_of_fix_torus_sp4 {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 8 ≤ Nat.card K) (α : MulAut (StatedSp 2 K)) (hα : ∀ d ∈ torus 2 K, α d = d) :
    α ∈ (MulAut.conj : StatedSp 2 K →* MulAut (StatedSp 2 K)).range := by
  obtain ⟨Y, hY⟩ := exists_conjAut_of_proj_conj α
    (exists_conjAut_proj_of_fix_torus_sp4 hK α hα)
  exact ⟨Y, hY.symm⟩

end CFSG.RankThree.PartTwo.KFacts

end
