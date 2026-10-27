module

public import CFSG.OddTranspositions.PartThree.Eleven.Five.Refl
import CFSG.OddTranspositions.PartThree.Eleven.FiveMinus.Spinor
import CFSG.OddTranspositions.PartThree.Eleven.FiveMinus.ReflConj
import CFSG.OddTranspositions.PartThree.Eleven.FiveMinus.Derived
import CFSG.ClassicalGroups.Orthogonal.FiveSquareModel

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix
open scoped commutatorElement
open CFSG.ClassicalGroups.Orthogonal

private def bb : Fin 5 → Fin 5 → ZMod 5 :=
  ![![0, 0, 1, 1, 0], ![0, 1, 0, -1, 0], ![0, 1, -1, 0, 0],
    ![1, 0, 0, -1, 0], ![0, 1, 1, 1, 1]]

private lemma Qbb (i : Fin 5) : fiveForm 4 true (bb i) (bb i) = 2 := by
  fin_cases i <;> decide

private lemma Qbb01 : fiveForm 4 true (bb 0 + bb 1) (bb 0 + bb 1) = 2 := by decide

private lemma Qbb02 : fiveForm 4 true (bb 0 + bb 2) (bb 0 + bb 2) = 2 := by decide

private lemma Qbb03 : fiveForm 4 true (bb 0 + bb 3) (bb 0 + bb 3) = 2 := by decide

private lemma Qbb34 : fiveForm 4 true (bb 3 + bb 4) (bb 3 + bb 4) = 2 := by decide

private lemma fiveForm_smul_left_five (c : ZMod 5) (x y : Fin 5 → ZMod 5) :
    fiveForm 4 true (c • x) y = c * fiveForm 4 true x y := by
  simp only [fiveForm, Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    mul_sub, mul_assoc]
  ring

private lemma fiveForm_smul_right_five (c : ZMod 5) (x y : Fin 5 → ZMod 5) :
    fiveForm 4 true x (c • y) = c * fiveForm 4 true x y := by
  rw [fiveForm_comm, fiveForm_smul_left_five, fiveForm_comm]

private def Bmat : Matrix (Fin 5) (Fin 5) (ZMod 5) := fun i j => bb j i

private def Binv : Matrix (Fin 5) (Fin 5) (ZMod 5) :=
  !![3, 3, 3, 3, 1; 2, 3, 3, 2, 2; 3, 3, 2, 3, 2; 1, 0, 0, 0, 0; 0, 0, 0, 0, 1]

private lemma Bmat_mul_Binv : Bmat * Binv = 1 := by decide

private lemma eq_smul_of_fiveReflOf_eq {x y : Fin 5 → ZMod 5}
    (hx : fiveForm 4 true x x ≠ 0) (hy : fiveForm 4 true y y ≠ 0)
    (h : fiveReflOf 4 true x = fiveReflOf 4 true y) :
    ∃ c : ZMod 5, x = c • y := by
  have h2 : (2 : ZMod 5) ≠ 0 := by decide
  have hxx : 2 * fiveForm 4 true x x * (fiveForm 4 true x x)⁻¹ = 2 := by
    rw [mul_assoc, mul_inv_cancel₀ hx, mul_one]
  have h1 : (fiveReflOf 4 true x : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x = -x := by
    rw [fiveReflOf_mulVec, hxx, two_smul]
    abel
  have h2' : (fiveReflOf 4 true y : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x =
      x - (2 * fiveForm 4 true x y * (fiveForm 4 true y y)⁻¹) • y :=
    fiveReflOf_mulVec 4 true y x
  have heq : -x = x - (2 * fiveForm 4 true x y * (fiveForm 4 true y y)⁻¹) • y := by
    rw [← h1, h, h2']
  have hcy : (2 * fiveForm 4 true x y * (fiveForm 4 true y y)⁻¹) • y = x + x := by
    have hh := heq
    rw [eq_sub_iff_add_eq] at hh
    have hh' : (2 * fiveForm 4 true x y * (fiveForm 4 true y y)⁻¹) • y - x = x := by
      rw [sub_eq_add_neg, add_comm]
      exact hh
    exact sub_eq_iff_eq_add.mp hh'
  have htwo : x + x = (2 : ZMod 5) • x := by rw [two_smul]
  refine ⟨(2 : ZMod 5)⁻¹ * (2 * fiveForm 4 true x y * (fiveForm 4 true y y)⁻¹), ?_⟩
  rw [← smul_smul, hcy, htwo, smul_smul, inv_mul_cancel₀ h2, one_smul]

private lemma eq_of_smul_add_eq {v w : Fin 5 → ZMod 5} {a b d : ZMod 5}
    (h : a • v + b • w = d • (v + w)) (k1 k2 : Fin 5)
    (h1v : v k1 = 1) (h1w : w k1 = 0) (h2v : v k2 = 0) (h2w : w k2 = 1) : b = a := by
  have e1 := congrFun h k1
  have e2 := congrFun h k2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1v, h1w, h2v, h2w, mul_one, mul_zero,
    add_zero, zero_add, zero_mul, one_mul] at e1 e2
  exact e2.trans e1.symm

private lemma eq_smul_bb0_bb1 {a b d : ZMod 5}
    (h : a • bb 0 + b • bb 1 = d • (bb 0 + bb 1)) : b = a :=
  eq_of_smul_add_eq h 2 1 (by decide) (by decide) (by decide) (by decide)

private lemma eq_smul_bb0_bb2 {a b d : ZMod 5}
    (h : a • bb 0 + b • bb 2 = d • (bb 0 + bb 2)) : b = a :=
  eq_of_smul_add_eq h 3 1 (by decide) (by decide) (by decide) (by decide)

private lemma eq_smul_bb0_bb3 {a b d : ZMod 5}
    (h : a • bb 0 + b • bb 3 = d • (bb 0 + bb 3)) : b = a :=
  eq_of_smul_add_eq h 2 0 (by decide) (by decide) (by decide) (by decide)

private lemma eq_smul_bb3_bb4 {a b d : ZMod 5}
    (h : a • bb 3 + b • bb 4 = d • (bb 3 + bb 4)) : b = a :=
  eq_of_smul_add_eq h 0 4 (by decide) (by decide) (by decide) (by decide)

theorem center_fiveReflectionGroup_four_true_false :
    Subgroup.center (fiveReflectionGroup 4 true false) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  have hcomm : ∀ y : fiveReflectionGroup 4 true false, y * g = g * y :=
    fun y => Subgroup.mem_center_iff.mp hg y
  have hscalar : ∀ v : Fin 5 → ZMod 5, fiveForm 4 true v v ≠ 0 →
      ¬ IsSquare (fiveForm 4 true v v) →
      ∃ c : ZMod 5, (g : GL (Fin 5) (ZMod 5)) *ᵥ v = c • v := by
    intro v hv hvns
    have hmem : fiveReflOf 4 true v ∈ fiveReflections 4 true false := by
      refine fiveReflOf_mem hv ?_
      exact ⟨fun h => absurd h hvns, fun h => absurd h (by decide : ¬(false = true))⟩
    have hcommv : fiveReflOf 4 true v * (g : GL (Fin 5) (ZMod 5)) =
        (g : GL (Fin 5) (ZMod 5)) * fiveReflOf 4 true v :=
      congrArg (fun x : fiveReflectionGroup 4 true false =>
        (x : GL (Fin 5) (ZMod 5)))
        (hcomm ⟨fiveReflOf 4 true v, Subgroup.subset_closure hmem⟩)
    have hconj : (g : GL (Fin 5) (ZMod 5)) * fiveReflOf 4 true v *
        (g : GL (Fin 5) (ZMod 5))⁻¹ = fiveReflOf 4 true v := by
      rw [← hcommv]
      group
    have hconj2 : (g : GL (Fin 5) (ZMod 5)) * fiveReflOf 4 true v *
        (g : GL (Fin 5) (ZMod 5))⁻¹ =
        fiveReflOf 4 true ((g : GL (Fin 5) (ZMod 5)) *ᵥ v) :=
      conj_fiveReflOf (fiveForm_mulVec_of_mem g.2) v
    have hEq : fiveReflOf 4 true ((g : GL (Fin 5) (ZMod 5)) *ᵥ v) =
        fiveReflOf 4 true v := by rw [← hconj2, hconj]
    have hgv : fiveForm 4 true ((g : GL (Fin 5) (ZMod 5)) *ᵥ v)
        ((g : GL (Fin 5) (ZMod 5)) *ᵥ v) ≠ 0 := by
      rw [fiveForm_mulVec_of_mem g.2 v v]; exact hv
    exact eq_smul_of_fiveReflOf_eq hgv hv hEq
  have hb : ∀ i : Fin 5, ∃ c : ZMod 5,
      (g : GL (Fin 5) (ZMod 5)) *ᵥ bb i = c • bb i :=
    fun i => hscalar (bb i) (by rw [Qbb i]; decide) (by rw [Qbb i]; decide)
  let lam : ZMod 5 := Classical.choose (hb 0)
  have hlam0 : (g : GL (Fin 5) (ZMod 5)) *ᵥ bb 0 = lam • bb 0 :=
    Classical.choose_spec (hb 0)
  have hsum_rel : ∀ (i j : Fin 5) (ci cj d : ZMod 5),
      (g : GL (Fin 5) (ZMod 5)) *ᵥ bb i = ci • bb i →
      (g : GL (Fin 5) (ZMod 5)) *ᵥ bb j = cj • bb j →
      (g : GL (Fin 5) (ZMod 5)) *ᵥ (bb i + bb j) = d • (bb i + bb j) →
      ci • bb i + cj • bb j = d • (bb i + bb j) := by
    intro i j ci cj d hi hj hd
    calc ci • bb i + cj • bb j
        = (g : GL (Fin 5) (ZMod 5)) *ᵥ bb i +
            (g : GL (Fin 5) (ZMod 5)) *ᵥ bb j := by rw [hi, hj]
      _ = (g : GL (Fin 5) (ZMod 5)) *ᵥ (bb i + bb j) := by rw [Matrix.mulVec_add]
      _ = d • (bb i + bb j) := hd
  obtain ⟨c1, hc1⟩ := hb 1
  obtain ⟨c2, hc2⟩ := hb 2
  obtain ⟨c3, hc3⟩ := hb 3
  obtain ⟨c4, hc4⟩ := hb 4
  have hs01 : fiveForm 4 true (bb 0 + bb 1) (bb 0 + bb 1) ≠ 0 := by rw [Qbb01]; decide
  have hn01 : ¬ IsSquare (fiveForm 4 true (bb 0 + bb 1) (bb 0 + bb 1)) := by
    rw [Qbb01]; decide
  obtain ⟨d1, hd1⟩ := hscalar (bb 0 + bb 1) hs01 hn01
  have hc1_lam : c1 = lam :=
    eq_smul_bb0_bb1 (hsum_rel 0 1 lam c1 d1 hlam0 hc1 hd1)
  have hs02 : fiveForm 4 true (bb 0 + bb 2) (bb 0 + bb 2) ≠ 0 := by rw [Qbb02]; decide
  have hn02 : ¬ IsSquare (fiveForm 4 true (bb 0 + bb 2) (bb 0 + bb 2)) := by
    rw [Qbb02]; decide
  obtain ⟨d2, hd2⟩ := hscalar (bb 0 + bb 2) hs02 hn02
  have hc2_lam : c2 = lam :=
    eq_smul_bb0_bb2 (hsum_rel 0 2 lam c2 d2 hlam0 hc2 hd2)
  have hs03 : fiveForm 4 true (bb 0 + bb 3) (bb 0 + bb 3) ≠ 0 := by rw [Qbb03]; decide
  have hn03 : ¬ IsSquare (fiveForm 4 true (bb 0 + bb 3) (bb 0 + bb 3)) := by
    rw [Qbb03]; decide
  obtain ⟨d3, hd3⟩ := hscalar (bb 0 + bb 3) hs03 hn03
  have hc3_lam : c3 = lam :=
    eq_smul_bb0_bb3 (hsum_rel 0 3 lam c3 d3 hlam0 hc3 hd3)
  have hs34 : fiveForm 4 true (bb 3 + bb 4) (bb 3 + bb 4) ≠ 0 := by rw [Qbb34]; decide
  have hn34 : ¬ IsSquare (fiveForm 4 true (bb 3 + bb 4) (bb 3 + bb 4)) := by
    rw [Qbb34]; decide
  obtain ⟨d4, hd4⟩ := hscalar (bb 3 + bb 4) hs34 hn34
  have hc4_c3 : c4 = c3 := eq_smul_bb3_bb4 (hsum_rel 3 4 c3 c4 d4 hc3 hc4 hd4)
  have hc4_lam : c4 = lam := by rw [hc4_c3, hc3_lam]
  have hb_lam : ∀ i : Fin 5, (g : GL (Fin 5) (ZMod 5)) *ᵥ bb i = lam • bb i := by
    intro i
    fin_cases i
    · exact hlam0
    · rw [hc1_lam] at hc1; exact hc1
    · rw [hc2_lam] at hc2; exact hc2
    · rw [hc3_lam] at hc3; exact hc3
    · rw [hc4_lam] at hc4; exact hc4
  have hmat : ((g : GL (Fin 5) (ZMod 5)) : Matrix (Fin 5) (Fin 5) (ZMod 5)) =
      lam • (1 : Matrix (Fin 5) (Fin 5) (ZMod 5)) := by
    have hmul : ((g : GL (Fin 5) (ZMod 5)) : Matrix (Fin 5) (Fin 5) (ZMod 5)) * Bmat =
        lam • Bmat := by
      ext i j
      rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
      have h := congrFun (hb_lam j) i
      simp only [Pi.smul_apply, smul_eq_mul] at h
      simp only [Bmat]
      exact h
    calc ((g : GL (Fin 5) (ZMod 5)) : Matrix (Fin 5) (Fin 5) (ZMod 5))
        = ((g : GL (Fin 5) (ZMod 5)) : Matrix (Fin 5) (Fin 5) (ZMod 5)) * 1 :=
          (mul_one _).symm
      _ = ((g : GL (Fin 5) (ZMod 5)) : Matrix (Fin 5) (Fin 5) (ZMod 5)) *
            (Bmat * Binv) := by rw [Bmat_mul_Binv]
      _ = (((g : GL (Fin 5) (ZMod 5)) : Matrix (Fin 5) (Fin 5) (ZMod 5)) * Bmat) *
            Binv := (Matrix.mul_assoc _ _ _).symm
      _ = (lam • Bmat) * Binv := by rw [hmul]
      _ = lam • (Bmat * Binv) := by rw [Matrix.smul_mul]
      _ = lam • (1 : Matrix (Fin 5) (Fin 5) (ZMod 5)) := by rw [Bmat_mul_Binv]
  have hlam2 : lam ^ 2 = 1 := by
    have h := fiveForm_mulVec_of_mem g.2 (bb 0) (bb 0)
    rw [hlam0] at h
    rw [fiveForm_smul_left_five, fiveForm_smul_right_five, Qbb 0, ← mul_assoc,
      ← pow_two] at h
    have h2 : (2 : ZMod 5) ≠ 0 := by decide
    have h2inv : (2 : ZMod 5) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
    have hh := congrArg (fun z => z * (2 : ZMod 5)⁻¹) h
    rwa [mul_assoc, h2inv, mul_one] at hh
  have hcases : lam = 1 ∨ lam = -1 := by
    have h : ∀ x : ZMod 5, x ^ 2 = 1 → x = 1 ∨ x = -1 := by decide
    exact h lam hlam2
  rcases hcases with h1 | h1
  · apply Subtype.ext
    apply Units.ext
    rw [hmat, h1, one_smul]
    rfl
  · exfalso
    have hgm : (g : GL (Fin 5) (ZMod 5)) = -1 := by
      apply Units.ext
      rw [hmat, h1]
      decide
    exact neg_one_notMem_fiveReflectionGroup_four_true_false (hgm ▸ g.2)

private def r0G : GL (Fin 5) (ZMod 5) := fiveReflOf 4 true (bb 0)

private lemma r0G_mem : r0G ∈ fiveReflections 4 true false := by
  refine fiveReflOf_mem (by rw [Qbb 0]; decide) ?_
  rw [Qbb 0]
  decide

private def r0 : fiveReflectionGroup 4 true false :=
  ⟨r0G, Subgroup.subset_closure r0G_mem⟩

private lemma r0_sq : r0 * r0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change fiveReflMatrix 4 true (bb 0) * fiveReflMatrix 4 true (bb 0) = 1
  exact fiveReflMatrix_mul_self 4 true (bb 0)

private lemma r0_inv : r0⁻¹ = r0 := mul_eq_one_iff_inv_eq.mp r0_sq

private theorem commutator_sup_zpowers_r0 :
    commutator (fiveReflectionGroup 4 true false) ⊔ Subgroup.zpowers r0 = ⊤ := by
  rw [eq_top_iff]
  intro g _
  let H : Subgroup (GL (Fin 5) (ZMod 5)) :=
    (commutator (fiveReflectionGroup 4 true false) ⊔ Subgroup.zpowers r0).map
      (fiveReflectionGroup 4 true false).subtype
  have hgen : fiveReflections 4 true false ⊆ H := by
    intro r hr
    obtain ⟨h, hh, hconj⟩ :=
      exists_conj_eq_of_mem_fiveReflections_four_true_false (r := r0G) (r' := r) r0G_mem hr
    let r' : fiveReflectionGroup 4 true false := ⟨r, Subgroup.subset_closure hr⟩
    let h' : fiveReflectionGroup 4 true false := ⟨h, hh⟩
    have hconj' : h' * r0 * h'⁻¹ = r' := Subtype.ext hconj
    have hcomm_eq : ⁅h', r0⁆ = r' * r0 := by
      rw [commutatorElement_def, hconj', r0_inv]
    have hr'_eq : r' = (r' * r0) * r0 := by rw [mul_assoc, r0_sq, mul_one]
    have hr'_mem : r' ∈ commutator (fiveReflectionGroup 4 true false) ⊔ Subgroup.zpowers r0 := by
      have h1 : r' * r0 ∈ commutator (fiveReflectionGroup 4 true false) := by
        rw [← hcomm_eq]
        exact Subgroup.commutator_mem_commutator (H₁ := ⊤) (H₂ := ⊤)
          (Subgroup.mem_top h') (Subgroup.mem_top r0)
      rw [hr'_eq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers r0))
    exact Subgroup.mem_map.mpr ⟨r', hr'_mem, rfl⟩
  have hgH : (g : GL (Fin 5) (ZMod 5)) ∈ H := by
    refine Subgroup.closure_induction (p := fun x _ => x ∈ H) hgen H.one_mem ?_ ?_ g.2
    · intro x y _ _ hx hy
      exact H.mul_mem hx hy
    · intro x _ hx
      exact H.inv_mem hx
  rw [Subgroup.mem_map] at hgH
  obtain ⟨x, hx, hxg⟩ := hgH
  have hxg' : x = g := Subtype.ext hxg
  rwa [hxg'] at hx

private lemma mem_zpowers_r0_eq {z : fiveReflectionGroup 4 true false}
    (hz : z ∈ Subgroup.zpowers r0) : z = 1 ∨ z = r0 := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [← hn]
  have h2 : r0 ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact r0_sq
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
  · left
    rw [hk, _root_.zpow_mul, h2, _root_.one_zpow]
  · right
    rw [hk, _root_.zpow_add, _root_.zpow_mul, h2, _root_.one_zpow, zpow_one, one_mul]

private lemma det_eq_one_or_neg_one (b : fiveReflectionGroup 4 true false) :
    Matrix.GeneralLinearGroup.det (b : GL (Fin 5) (ZMod 5)) = 1 ∨
      Matrix.GeneralLinearGroup.det (b : GL (Fin 5) (ZMod 5)) = -1 := by
  have hP : ∀ b ∈ fiveReflectionGroup 4 true false,
      Matrix.GeneralLinearGroup.det (b : GL (Fin 5) (ZMod 5)) = 1 ∨
        Matrix.GeneralLinearGroup.det (b : GL (Fin 5) (ZMod 5)) = -1 := by
    intro b hb
    refine Subgroup.closure_induction (p := fun b _ =>
      Matrix.GeneralLinearGroup.det (b : GL (Fin 5) (ZMod 5)) = 1 ∨
        Matrix.GeneralLinearGroup.det (b : GL (Fin 5) (ZMod 5)) = -1) ?_ ?_ ?_ ?_ hb
    · intro r hr
      obtain ⟨x, hx, hπ, rfl⟩ := exists_eq_fiveReflOf hr
      right
      exact det_fiveReflOf hx
    · left
      simp
    · intro x y _ _ hx hy
      rw [map_mul]
      rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy] <;> decide
    · intro x _ hx
      rw [map_inv]
      rcases hx with hx | hx <;> rw [hx] <;> decide
  exact hP b b.2

theorem mem_commutator_fiveReflectionGroup_four_true_false_iff
    (g : fiveReflectionGroup 4 true false) :
    g ∈ commutator (fiveReflectionGroup 4 true false) ↔
      Matrix.GeneralLinearGroup.det (g : GL (Fin 5) (ZMod 5)) = 1 := by
  let detHom : fiveReflectionGroup 4 true false →* (ZMod 5)ˣ :=
    Matrix.GeneralLinearGroup.det.comp (fiveReflectionGroup 4 true false).subtype
  constructor
  · intro hg
    exact MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker detHom hg)
  · intro hg
    have hg_sup : g ∈ commutator (fiveReflectionGroup 4 true false) ⊔
        Subgroup.zpowers r0 := by
      rw [commutator_sup_zpowers_r0]
      exact Subgroup.mem_top g
    rw [Subgroup.mem_sup_of_normal_left] at hg_sup
    obtain ⟨n, hn, z, hz, hnz⟩ := hg_sup
    rcases mem_zpowers_r0_eq hz with hz1 | hzr0
    · rw [hz1, mul_one] at hnz
      rwa [← hnz]
    · exfalso
      have hn_det : detHom n = 1 :=
        MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker detHom hn)
      have hr0_det : detHom r0 = -1 := by
        change Matrix.GeneralLinearGroup.det (fiveReflOf 4 true (bb 0)) = -1
        exact det_fiveReflOf (by rw [Qbb 0]; decide)
      have hg_det : detHom g = -1 := by
        rw [← hnz, hzr0, map_mul, hn_det, hr0_det, one_mul]
      have hg' : Matrix.GeneralLinearGroup.det (g : GL (Fin 5) (ZMod 5)) = -1 := hg_det
      rw [hg'] at hg
      exact (by decide : ¬((-1 : (ZMod 5)ˣ) = 1)) hg

theorem index_commutator_fiveReflectionGroup_four_true_false :
    (commutator (fiveReflectionGroup 4 true false)).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨r0, fun b => ?_⟩
  rw [mem_commutator_fiveReflectionGroup_four_true_false_iff (b * r0),
    mem_commutator_fiveReflectionGroup_four_true_false_iff b]
  have hr0 : Matrix.GeneralLinearGroup.det (r0 : GL (Fin 5) (ZMod 5)) = -1 := by
    change Matrix.GeneralLinearGroup.det (fiveReflOf 4 true (bb 0)) = -1
    exact det_fiveReflOf (by rw [Qbb 0]; decide)
  rw [show ((b * r0 : fiveReflectionGroup 4 true false) : GL (Fin 5) (ZMod 5)) =
      (b : GL (Fin 5) (ZMod 5)) * (r0 : GL (Fin 5) (ZMod 5)) from rfl, map_mul, hr0]
  rcases det_eq_one_or_neg_one b with hb | hb
  · rw [hb, one_mul]
    decide
  · rw [hb]
    decide

private lemma center_derived_eq_bot :
    Subgroup.center FiveSquareFrameGeneration.derived = ⊥ := by
  haveI : IsSimpleGroup FiveSquareFrameGeneration.derived :=
    FiveSquareFrameGeneration.derived_isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.center FiveSquareFrameGeneration.derived) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := FiveSquareModel.exists_noncommuting_derived
    have ha : a ∈ Subgroup.center FiveSquareFrameGeneration.derived := by
      rw [h]
      exact Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.mp ha) b).symm

private lemma center_commutator_eq_bot :
    Subgroup.center (commutator (fiveReflectionGroup 4 true false)) = ⊥ := by
  obtain ⟨e⟩ := nonempty_commutator_fiveReflectionGroup_four_true_false_mulEquiv
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hze : e z ∈ Subgroup.center FiveSquareFrameGeneration.derived := by
    rw [← Subgroup.map_center_eq e]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hz
  rw [center_derived_eq_bot] at hze
  exact e.injective (by rw [Subgroup.mem_bot.mp hze, map_one])

private lemma centralizer_inf_commutator_eq_bot :
    Subgroup.centralizer (commutator (fiveReflectionGroup 4 true false) :
      Set (fiveReflectionGroup 4 true false)) ⊓
      commutator (fiveReflectionGroup 4 true false) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro c hc
  rw [Subgroup.mem_inf] at hc
  obtain ⟨hcC, hcN⟩ := hc
  have hcenter : (⟨c, hcN⟩ : commutator (fiveReflectionGroup 4 true false)) ∈
      Subgroup.center (commutator (fiveReflectionGroup 4 true false)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hcC (y : fiveReflectionGroup 4 true false) y.2
  rw [center_commutator_eq_bot] at hcenter
  exact Subtype.ext_iff.mp (Subgroup.mem_bot.mp hcenter)

theorem centralizer_commutator_fiveReflectionGroup_four_true_false :
    Subgroup.centralizer (commutator (fiveReflectionGroup 4 true false) :
      Set (fiveReflectionGroup 4 true false)) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro c hcC
  have hcenter : c ∈ Subgroup.center (fiveReflectionGroup 4 true false) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hcomm : ⁅c, g⁆ = 1 := by
      have hCnormal : (Subgroup.centralizer
          (commutator (fiveReflectionGroup 4 true false) :
            Set (fiveReflectionGroup 4 true false))).Normal := inferInstance
      have hconj : g * c * g⁻¹ ∈ Subgroup.centralizer
          (commutator (fiveReflectionGroup 4 true false) :
            Set (fiveReflectionGroup 4 true false)) :=
        hCnormal.conj_mem c hcC g
      have hcomm_eq : ⁅c, g⁆ = c * (g * c * g⁻¹)⁻¹ := by
        rw [commutatorElement_def]
        group
      have hmemC : ⁅c, g⁆ ∈ Subgroup.centralizer
          (commutator (fiveReflectionGroup 4 true false) :
            Set (fiveReflectionGroup 4 true false)) := by
        rw [hcomm_eq]
        exact mul_mem hcC (inv_mem hconj)
      have hmemN : ⁅c, g⁆ ∈ commutator (fiveReflectionGroup 4 true false) :=
        Subgroup.commutator_mem_commutator (H₁ := ⊤) (H₂ := ⊤)
          (Subgroup.mem_top c) (Subgroup.mem_top g)
      have hinf : ⁅c, g⁆ ∈ Subgroup.centralizer
          (commutator (fiveReflectionGroup 4 true false) :
            Set (fiveReflectionGroup 4 true false)) ⊓
          commutator (fiveReflectionGroup 4 true false) :=
        Subgroup.mem_inf.mpr ⟨hmemC, hmemN⟩
      rw [centralizer_inf_commutator_eq_bot] at hinf
      exact Subgroup.mem_bot.mp hinf
    exact (commutatorElement_eq_one_iff_commute.mp hcomm).eq.symm
  rw [center_fiveReflectionGroup_four_true_false] at hcenter
  exact Subgroup.mem_bot.mp hcenter

end CFSG.OddTranspositions.PartThree
