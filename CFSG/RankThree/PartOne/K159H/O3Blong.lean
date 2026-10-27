module

public import CFSG.RankThree.PartOne.K159H.O3Phi
public import CFSG.RankThree.PartOne.K159H.O3Group
import CFSG.RankThree.PartOne.KFCL.L4Block

public noncomputable section

namespace CFSG.RankThree.PartOne.K159H

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal.Spin
  CFSG.RankThree.OrthogonalInvolutions Module
open scoped MatrixGroups

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ}

theorem sl2_isSimpleGroup [CharP K 2] (h4 : 4 ≤ Nat.card K) : IsSimpleGroup SL(2, K) :=
  CFSG.RankThree.PartOne.KFCL.L4.sl2_isSimpleGroup h4

theorem sl2_isPerfect [CharP K 2] (h4 : 4 ≤ Nat.card K) : Group.IsPerfect SL(2, K) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have hcard : 4 ≤ Fintype.card K := by rw [← Nat.card_eq_fintype_card]; exact h4
  obtain ⟨a, ha⟩ : ∃ a : K, a ≠ 0 ∧ a ≠ 1 := by
    by_contra hno
    push Not at hno
    have : (Finset.univ : Finset K) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · simp [hx]
      · simp [hno x hx]
    have := Finset.card_le_card this
    rw [Finset.card_univ] at this
    have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
    omega
  refine ⟨Matrix.SL2.commutator_eq_top ha.1 fun hsq => ha.2 ?_⟩
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h5 : (a - 1) ^ 2 = 0 := by linear_combination hsq + (1 - a) * h2
  exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h5)

variable (qA : QuadraticForm K A) (a b : Fin r ⊕ Fin r)

@[expose] def Blong : Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :=
  Subgroup.closure ({g | ∃ t : K, g = rEl qA t a b} ∪ {g | ∃ t : K, g = rEl qA t b a})

variable {qA a b}

theorem rEl_mem_Blong_left (t : K) : rEl qA t a b ∈ Blong qA a b :=
  Subgroup.subset_closure (Or.inl ⟨t, rfl⟩)

theorem rEl_mem_Blong_right (t : K) : rEl qA t b a ∈ Blong qA a b :=
  Subgroup.subset_closure (Or.inr ⟨t, rfl⟩)

theorem Blong_comm : Blong qA a b = Blong qA b a := by
  unfold Blong
  rw [Set.union_comm]

theorem Blong_swap [CharP K 2] (hab : coordIdx a ≠ coordIdx b) : Blong qA a b = Blong qA b.swap a.swap := by
  unfold Blong
  congr 1
  ext g
  have h1 := rEl_swap qA hab
  have h2 := rEl_swap qA hab.symm
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨t, rfl⟩ | ⟨t, rfl⟩)
    · exact Or.inl ⟨t, h1 t⟩
    · exact Or.inr ⟨t, h2 t⟩
  · rintro (⟨t, rfl⟩ | ⟨t, rfl⟩)
    · exact Or.inl ⟨t, (h1 t).symm⟩
    · exact Or.inr ⟨t, (h2 t).symm⟩

section Hom

variable [CharP K 2]

omit [CharP K 2] in
theorem coe_upperSL (t : K) :
    (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) t).1 = !![1, t; 0, 1] := by
  rw [Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

omit [CharP K 2] in
theorem coe_lowerSL (t : K) :
    (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) t).1 = !![1, 0; t, 1] := by
  rw [Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem PhiH_upperSL (hab : coordIdx a ≠ coordIdx b) (t : K) :
    PhiH (A := A) hab (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) t) =
      rEl qA t a b := by
  refine LinearEquiv.ext fun v => ?_
  rw [PhiH_apply, coe_upperSL]
  have := congrArg (fun f : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A) => f v)
    (rEl_eq_phi_upper qA hab t)
  exact this.symm

theorem PhiH_lowerSL (hab : coordIdx a ≠ coordIdx b) (t : K) :
    PhiH (A := A) hab (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) t) =
      rEl qA t b a := by
  refine LinearEquiv.ext fun v => ?_
  rw [PhiH_apply, coe_lowerSL]
  have := congrArg (fun f : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A) => f v)
    (rEl_eq_phi_lower qA hab t)
  exact this.symm

theorem PhiH_mem_Blong (hab : coordIdx a ≠ coordIdx b) (g : SL(2, K)) :
    PhiH (A := A) hab g ∈ Blong qA a b := by
  have hgen := Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field (ι := Fin 2) (K := K)
  have hg : g ∈ Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct (Fin 2) K → SL(2, K))) := by
    rw [hgen]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨t, rfl⟩ := hx
    obtain ⟨i, j, hij, c⟩ := t
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · rw [Matrix.TransvectionStruct.toSpecialLinearGroup_def]
      simp only
      rw [PhiH_upperSL hab]
      exact rEl_mem_Blong_left c
    · rw [Matrix.TransvectionStruct.toSpecialLinearGroup_def]
      simp only
      rw [PhiH_lowerSL hab]
      exact rEl_mem_Blong_right c
    · exact absurd rfl hij
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

theorem PhiH_range (hab : coordIdx a ≠ coordIdx b) :
    (PhiH (K := K) (A := A) hab).range = Blong qA a b := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact PhiH_mem_Blong hab g
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩)
    · exact ⟨_, PhiH_upperSL hab t⟩
    · exact ⟨_, PhiH_lowerSL hab t⟩

theorem isSimpleGroup_Blong (hab : coordIdx a ≠ coordIdx b) (h4 : 4 ≤ Nat.card K) :
    IsSimpleGroup ↥(Blong qA a b) := by
  have e : SL(2, K) ≃* ↥(Blong qA a b) :=
    (MonoidHom.ofInjective (PhiH_injective (K := K) (A := A) hab)).trans
      (MulEquiv.subgroupCongr (PhiH_range hab))
  have := sl2_isSimpleGroup (K := K) h4
  exact e.symm.isSimpleGroup

theorem Blong_perfect (hab : coordIdx a ≠ coordIdx b) (h4 : 4 ≤ Nat.card K) :
    ⁅Blong qA a b, Blong qA a b⁆ = Blong qA a b := by
  have hp := sl2_isPerfect (K := K) h4
  have h1 := Subgroup.map_commutator (⊤ : Subgroup SL(2, K)) ⊤ (PhiH (K := K) (A := A) hab)
  have hp' : ⁅(⊤ : Subgroup SL(2, K)), ⊤⁆ = ⊤ := hp.commutator_eq_top
  rw [hp', ← MonoidHom.range_eq_map, PhiH_range hab] at h1
  exact h1.symm


omit [CharP K 2] in
theorem phi_hypVec_other (hab : coordIdx a ≠ coordIdx b) (g : Matrix (Fin 2) (Fin 2) K) {c : Fin r ⊕ Fin r}
    (hca : c ≠ a) (hcb : c ≠ b) (hca' : c ≠ a.swap) (hcb' : c ≠ b.swap) :
    phi (A := A) a b g (hypVec K A c) = hypVec K A c := by
  have h1 : a ≠ b := ne_of_coordIdx' hab
  have h1' : b ≠ a := h1.symm
  have h2' : a ≠ a.swap := (swap_ne_self'' a).symm
  have h2'' : a.swap ≠ a := swap_ne_self'' a
  have h3 : a ≠ b.swap := ne_swap_of_coordIdx' hab
  have h3' : b.swap ≠ a := h3.symm
  have h4 : b ≠ a.swap := ne_swap_of_coordIdx' (Ne.symm hab)
  have h4' : a.swap ≠ b := h4.symm
  have h5' : b ≠ b.swap := (swap_ne_self'' b).symm
  have h5 : b.swap ≠ b := swap_ne_self'' b
  have h6 : a.swap ≠ b.swap := fun e => h1 (by simpa using congrArg Sum.swap e)
  have h6' : b.swap ≠ a.swap := h6.symm
  refine Prod.ext (funext fun c' => ?_) rfl
  simp only [phi_fst, phiFun, hypVec_fst]
  have e1 := hca.symm
  have e2 := hcb.symm
  have e3 := hca'.symm
  have e4 := hcb'.symm
  by_cases ha : c' = a
  · rw [ha]; simp [e1, e2]
  by_cases hb : c' = b
  · rw [hb]; simp [e1, e2, h1']
  by_cases ha' : c' = a.swap
  · rw [ha']; simp [e3, e4, h2'', h4']
  by_cases hb' : c' = b.swap
  · rw [hb']; simp [e3, e4, h3', h5, h6']
  simp [ha, hb, ha', hb']

theorem torH_mem_Blong_iff (hab : coordIdx a ≠ coordIdx b) (d : Fin r → Kˣ) :
    torH K A r d ∈ Blong qA a b ↔
      (∀ c, c ≠ a → c ≠ b → c ≠ a.swap → c ≠ b.swap → wt d c = 1) ∧ wt d a * wt d b = 1 := by
  have h1 : a ≠ b := ne_of_coordIdx' hab
  have h1' : b ≠ a := h1.symm
  have h2' : a ≠ a.swap := (swap_ne_self'' a).symm
  have h2'' : a.swap ≠ a := swap_ne_self'' a
  have h3 : a ≠ b.swap := ne_swap_of_coordIdx' hab
  have h3' : b.swap ≠ a := h3.symm
  have h4 : b ≠ a.swap := ne_swap_of_coordIdx' (Ne.symm hab)
  have h4' : a.swap ≠ b := h4.symm
  have h5' : b ≠ b.swap := (swap_ne_self'' b).symm
  have h5 : b.swap ≠ b := swap_ne_self'' b
  have h6 : a.swap ≠ b.swap := fun e => h1 (by simpa using congrArg Sum.swap e)
  have h6' : b.swap ≠ a.swap := h6.symm
  rw [← PhiH_range hab]
  constructor
  · rintro ⟨g, hg⟩
    have hv : ∀ v, phi a b g.1 v = torH K A r d v := fun v => by
      have h := LinearEquiv.congr_fun hg v
      exact h
    refine ⟨fun c hca hcb hca' hcb' => ?_, ?_⟩
    · have := congrFun (congrArg Prod.fst (hv (hypVec K A c))) c
      rw [phi_hypVec_other hab g.1 hca hcb hca' hcb', torH_hypVec] at this
      simp only [hypVec_fst, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, ite_true, mul_one] at this
      exact Units.ext this.symm
    · have e00 := congrFun (congrArg Prod.fst (hv (hypVec K A a))) a
      have e10 := congrFun (congrArg Prod.fst (hv (hypVec K A a))) b
      have e01 := congrFun (congrArg Prod.fst (hv (hypVec K A b))) a
      have e11 := congrFun (congrArg Prod.fst (hv (hypVec K A b))) b
      simp [phi_fst, phiFun, torH_hypVec, hypVec_fst, h1, h1'] at e00 e10 e01 e11
      have hdet := g.2
      rw [Matrix.det_fin_two, e01, e10] at hdet
      apply Units.ext
      push_cast
      rw [← e00, ← e11]
      simpa using hdet
  · rintro ⟨hc, hw⟩
    have hdet : Matrix.det !![(wt d a : K), 0; 0, (wt d b : K)] = 1 := by
      rw [Matrix.det_fin_two_of]
      have := congrArg (fun u : Kˣ => (u : K)) hw
      simp only [Units.val_mul, Units.val_one] at this
      linear_combination this
    refine ⟨⟨!![(wt d a : K), 0; 0, (wt d b : K)], hdet⟩, ?_⟩
    refine LinearEquiv.ext fun v => Prod.ext (funext fun c => ?_) rfl
    have hwb : (wt d b : K) = ((wt d a)⁻¹ : Kˣ) := by
      rw [Units.val_inv_eq_inv_val]
      exact eq_inv_of_mul_eq_one_right (by simpa using congrArg (fun u : Kˣ => (u : K)) hw)
    have hwa : (wt d a : K) = ((wt d b)⁻¹ : Kˣ) := by
      rw [Units.val_inv_eq_inv_val]
      exact eq_inv_of_mul_eq_one_left (by simpa using congrArg (fun u : Kˣ => (u : K)) hw)
    show (phi a b _ v).1 c = (torH K A r d v).1 c
    rw [phi_fst, torH_fst]
    simp only [phiFun]
    by_cases ca : c = a
    · subst ca; simp
    by_cases cb : c = b
    · subst cb; simp [h1']
    by_cases cas : c = a.swap
    · subst cas; simp [h2'', h4', wt_swap, hwb]
    by_cases cbs : c = b.swap
    · subst cbs; simp [h3', h5, h6', wt_swap, hwa]
    simp [ca, cb, cas, cbs, hc c ca cb cas cbs]

omit [CharP K 2] in
theorem Blong_comm_torH {d : Fin r → Kˣ} (h : wt d a = wt d b) {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hg : g ∈ Blong qA a b) : g * torH K A r d = torH K A r d * g := by
  have hle : Blong qA a b ≤ Subgroup.centralizer {torH K A r d} := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    · have h1 := torH_conj_rEl (qA := qA) d t a b
      have h2 : (wt d b.swap : K) * wt d a = 1 := by rw [wt_swap, ← h]; simp
      rw [h2, mul_one, mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    · have h1 := torH_conj_rEl (qA := qA) d t b a
      have h2 : (wt d a.swap : K) * wt d b = 1 := by rw [wt_swap, h]; simp
      rw [h2, mul_one, mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)

end Hom

end CFSG.RankThree.PartOne.K159H
