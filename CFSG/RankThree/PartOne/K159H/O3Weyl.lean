module

public import CFSG.RankThree.PartOne.K159H.O3Rot
public import CFSG.RankThree.PartOne.K159H.O3Phi

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.RankThree.PartOne.K159H

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal.Spin
  CFSG.RankThree.OrthogonalInvolutions Module
open scoped MatrixGroups

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ}

@[expose] def dPerm (π : Equiv.Perm (Fin r ⊕ Fin r)) (d : Fin r → Kˣ) : Fin r → Kˣ := fun k => wt d (π (Sum.inl k))

theorem wt_dPerm_inl (π : Equiv.Perm (Fin r ⊕ Fin r)) (d : Fin r → Kˣ) (k : Fin r) :
    wt (dPerm π d) (Sum.inl k) = wt d (π (Sum.inl k)) := rfl

theorem wt_dPerm {π : Equiv.Perm (Fin r ⊕ Fin r)} (hπ : ∀ c, π c.swap = (π c).swap) (d : Fin r → Kˣ)
    (c : Fin r ⊕ Fin r) : wt (dPerm π d) c = wt d (π c) := by
  rcases c with k | k
  · rfl
  · have : (Sum.inr k : Fin r ⊕ Fin r) = (Sum.inl k).swap := rfl
    rw [this, wt_swap, wt_dPerm_inl, hπ, wt_swap]

theorem conj_torH_mono {n : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)} (hn : n * n = 1)
    (π : Equiv.Perm (Fin r ⊕ Fin r)) (hπ : ∀ c, π c.swap = (π c).swap) (lam : Fin r ⊕ Fin r → K)
    (hfr : ∀ c, n (hypVec K A c) = lam c • hypVec K A (π c))
    (htail : ∀ a : A, (n ((0 : Fin r ⊕ Fin r → K), a)).1 = 0) (d : Fin r → Kˣ) :
    n * torH K A r d * n = torH K A r (dPerm π d) := by
  have hnn : ∀ v, n (n v) = v := fun v => by
    have := LinearEquiv.congr_fun hn v
    exact this
  have hππ : ∀ c, π (π c) = c ∧ lam c * lam (π c) = 1 := by
    intro c
    have h := hnn (hypVec K A c)
    rw [hfr c, map_smul, hfr (π c), smul_smul] at h
    have h2 := congrFun (congrArg Prod.fst h) c
    simp only [Prod.smul_fst, Pi.smul_apply, hypVec_fst, smul_eq_mul] at h2
    have hc : π (π c) = c := by
      by_contra hne
      rw [ite_eq_right (Ne.symm hne)] at h2
      simp at h2
    rw [hc] at h2
    exact ⟨hc, by simpa using h2⟩
  refine ext_frame_tail (fun c => ?_) (fun a => ?_)
  · have e1 : (n * torH K A r d * n) (hypVec K A c) = n (torH K A r d (n (hypVec K A c))) := rfl
    rw [e1, hfr c, map_smul, torH_hypVec, map_smul, map_smul, hfr (π c), (hππ c).1, torH_hypVec,
      wt_dPerm hπ, smul_smul, smul_smul]
    congr 1
    have := (hππ c).2
    linear_combination (↑(wt d (π c)) : K) * this
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, torH_snd_zero]
    have h1 : torH K A r d (n ((0 : Fin r ⊕ Fin r → K), a)) = n ((0 : Fin r ⊕ Fin r → K), a) :=
      torH_eq_of_fst_zero d (htail a)
    rw [h1, hnn]


section LongWeyl

variable [CharP K 2] {a b : Fin r ⊕ Fin r}

@[expose] def wSL (K : Type) [Field K] [CharP K 2] : SL(2, K) :=
  ⟨!![0, 1; 1, 0], by
    rw [Matrix.det_fin_two_of]
    have : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination (-1 : K) * this⟩

theorem wSL_mul_self : wSL K * wSL K = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wSL, Matrix.mul_apply, Fin.sum_univ_two]

@[expose] def nW (hab : coordIdx a ≠ coordIdx b) : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A) :=
  PhiH hab (wSL K)

@[expose] def πab (a b : Fin r ⊕ Fin r) : Equiv.Perm (Fin r ⊕ Fin r) :=
  Equiv.swap a b * Equiv.swap a.swap b.swap

theorem nW_mul_self (hab : coordIdx a ≠ coordIdx b) : nW (K := K) (A := A) hab * nW hab = 1 := by
  unfold nW
  rw [← map_mul, wSL_mul_self, map_one]

theorem πab_a (hab : coordIdx a ≠ coordIdx b) : πab a b a = b := by
  have h2 : a ≠ a.swap := (swap_ne_self'' a).symm
  have h3 : a ≠ b.swap := ne_swap_of_coordIdx' hab
  simp [πab, Equiv.swap_apply_of_ne_of_ne h2 h3]

theorem πab_b (hab : coordIdx a ≠ coordIdx b) : πab a b b = a := by
  have h4 : b ≠ a.swap := ne_swap_of_coordIdx' (Ne.symm hab)
  have h5 : b ≠ b.swap := (swap_ne_self'' b).symm
  simp [πab, Equiv.swap_apply_of_ne_of_ne h4 h5]

theorem πab_a' (hab : coordIdx a ≠ coordIdx b) : πab a b a.swap = b.swap := by
  simp [πab, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne (ne_swap_of_coordIdx' hab).symm (swap_ne_self'' b)]

theorem πab_b' (hab : coordIdx a ≠ coordIdx b) : πab a b b.swap = a.swap := by
  simp [πab, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne (swap_ne_self'' a) (ne_swap_of_coordIdx' (Ne.symm hab)).symm]

theorem πab_other {c : Fin r ⊕ Fin r} (hca : c ≠ a) (hcb : c ≠ b)
    (hca' : c ≠ a.swap) (hcb' : c ≠ b.swap) : πab a b c = c := by
  simp [πab, Equiv.swap_apply_of_ne_of_ne hca' hcb', Equiv.swap_apply_of_ne_of_ne hca hcb]


theorem πab_swap (hab : coordIdx a ≠ coordIdx b) (c : Fin r ⊕ Fin r) : πab a b c.swap = (πab a b c).swap := by
  by_cases ha : c = a
  · subst ha
    rw [πab_a' hab, πab_a hab]
  by_cases hb : c = b
  · subst hb
    rw [πab_b' hab, πab_b hab]
  by_cases ha' : c = a.swap
  · rw [ha', Sum.swap_swap, πab_a hab, πab_a' hab, Sum.swap_swap]
  by_cases hb' : c = b.swap
  · rw [hb', Sum.swap_swap, πab_b hab, πab_b' hab, Sum.swap_swap]
  rw [πab_other ha hb ha' hb']
  refine πab_other ?_ ?_ ?_ ?_ <;> intro h
  · exact ha' (by simpa using congrArg Sum.swap h)
  · exact hb' (by simpa using congrArg Sum.swap h)
  · exact ha (by simpa using congrArg Sum.swap h)
  · exact hb (by simpa using congrArg Sum.swap h)

theorem πab_invol (hab : coordIdx a ≠ coordIdx b) (c : Fin r ⊕ Fin r) : πab a b (πab a b c) = c := by
  by_cases ha : c = a
  · subst ha
    rw [πab_a hab, πab_b hab]
  by_cases hb : c = b
  · subst hb
    rw [πab_b hab, πab_a hab]
  by_cases ha' : c = a.swap
  · rw [ha', πab_a' hab, πab_b' hab]
  by_cases hb' : c = b.swap
  · rw [hb', πab_b' hab, πab_a' hab]
  rw [πab_other ha hb ha' hb', πab_other ha hb ha' hb']

theorem phiFun_wSL (hab : coordIdx a ≠ coordIdx b) (x : Fin r ⊕ Fin r → K) :
    phiFun a b (wSL K).1 x = fun c' => x (πab a b c') := by
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
  funext c'
  simp only [phiFun]
  by_cases ha : c' = a
  · rw [ha, πab_a hab]; simp [wSL, *]
  by_cases hb : c' = b
  · rw [hb, πab_b hab]; simp [wSL, *]
  by_cases ha' : c' = a.swap
  · rw [ha', πab_a' hab]; simp [wSL, *]
  by_cases hb' : c' = b.swap
  · rw [hb', πab_b' hab]; simp [wSL, *]
  rw [πab_other ha hb ha' hb']
  simp [ha, hb, ha', hb']

theorem nW_apply (hab : coordIdx a ≠ coordIdx b) (v : (Fin r ⊕ Fin r → K) × A) :
    nW hab v = ((fun c' => v.1 (πab a b c')), v.2) := by
  unfold nW
  rw [PhiH_apply]
  refine Prod.ext ?_ rfl
  rw [phi_fst, phiFun_wSL hab]

theorem nW_hypVec (hab : coordIdx a ≠ coordIdx b) (c : Fin r ⊕ Fin r) :
    nW (K := K) (A := A) hab (hypVec K A c) = hypVec K A (πab a b c) := by
  rw [nW_apply hab]
  refine Prod.ext (funext fun c' => ?_) rfl
  simp only [hypVec_fst]
  have : (πab a b c' = c) ↔ (c' = πab a b c) := by
    constructor
    · intro h
      rw [← h, πab_invol hab]
    · intro h
      rw [h, πab_invol hab]
  by_cases h : c' = πab a b c
  · simp [h, πab_invol hab]
  · have : ¬ πab a b c' = c := fun h' => h (by rw [← h', πab_invol hab])
    simp [h, this]

theorem nW_tail (hab : coordIdx a ≠ coordIdx b) (z : A) :
    (nW (K := K) hab ((0 : Fin r ⊕ Fin r → K), z)).1 = 0 := by
  rw [nW_apply hab]
  rfl

theorem conj_nW (hab : coordIdx a ≠ coordIdx b) (d : Fin r → Kˣ) :
    nW (A := A) hab * torH K A r d * nW hab = torH K A r (dPerm (πab a b) d) :=
  conj_torH_mono (nW_mul_self hab) (πab a b) (πab_swap hab) (fun _ => 1)
    (fun c => by rw [nW_hypVec, one_smul]) (fun z => nW_tail hab z) d

end LongWeyl


section ShortWeyl

variable [CharP K 2] (qA : QuadraticForm K A)

@[expose] def mW (k : Fin r) (a₀ : A) : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A) :=
  shortWeyl (hypPairT r qA k) ((0 : Fin r ⊕ Fin r → K), a₀)

variable {qA}

omit [CharP K 2] in
theorem mW_data (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0) :
    quadTail r qA ((0 : Fin r ⊕ Fin r → K), a₀) ≠ 0 := by
  rw [quadTail_tail]
  exact fun h => ha₀ (hani a₀ h)

theorem mW_inl (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0) (k : Fin r) :
    mW qA k a₀ (hypVec K A (Sum.inl k)) = (qA a₀)⁻¹ • hypVec K A (Sum.inr k) := by
  have := shortWeyl_e (hypPairT r qA k) (tail_mem_perp_hypPairT k a₀) (mW_data hani ha₀)
  rw [quadTail_tail, CharTwo.neg_eq] at this
  exact this

theorem mW_inr (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0) (k : Fin r) :
    mW qA k a₀ (hypVec K A (Sum.inr k)) = qA a₀ • hypVec K A (Sum.inl k) := by
  have := shortWeyl_f (hypPairT r qA k) (tail_mem_perp_hypPairT k a₀) (mW_data hani ha₀)
  rw [quadTail_tail, CharTwo.neg_eq] at this
  exact this

theorem mW_other (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0) {k : Fin r} {c : Fin r ⊕ Fin r}
    (hc : coordIdx c ≠ k) : mW qA k a₀ (hypVec K A c) = hypVec K A c := by
  have hperp : hypVec K A c ∈ (hypPairT r qA k).perp := by
    refine HypPair.mem_perp.2 ⟨?_, ?_⟩
    · rw [hypPairT_e, polar_hypVec_hypVec, ite_eq_right]
      intro h
      apply hc
      have := congrArg coordIdx h
      simpa using this
    · rw [hypPairT_f, polar_hypVec_hypVec, ite_eq_right]
      intro h
      apply hc
      have := congrArg coordIdx h
      simpa using this
  have := shortWeyl_perp (hypPairT r qA k) (tail_mem_perp_hypPairT k a₀) (mW_data hani ha₀) hperp
  change shortWeyl (hypPairT r qA k) ((0 : Fin r ⊕ Fin r → K), a₀) (hypVec K A c) = _
  rw [this, polar_hypVec_tail]
  simp

theorem mW_tail (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0) (k : Fin r) (z : A) :
    (mW qA k a₀ ((0 : Fin r ⊕ Fin r → K), z)).1 = 0 := by
  have := shortWeyl_perp (hypPairT r qA k) (tail_mem_perp_hypPairT k a₀) (mW_data hani ha₀)
    (tail_mem_perp_hypPairT k z)
  change (shortWeyl (hypPairT r qA k) ((0 : Fin r ⊕ Fin r → K), a₀) ((0 : Fin r ⊕ Fin r → K), z)).1 = 0
  rw [this]
  simp

theorem mW_mul_self (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0) (k : Fin r) :
    mW qA k a₀ * mW qA k a₀ = 1 :=
  shortWeyl_mul_self (hypPairT r qA k) (tail_mem_perp_hypPairT k a₀) (mW_data hani ha₀)

theorem swap_inl_inr_swap (k : Fin r) (c : Fin r ⊕ Fin r) :
    Equiv.swap (Sum.inl k) (Sum.inr k) c.swap = (Equiv.swap (Sum.inl k) (Sum.inr k) c).swap := by
  rcases c with m | m
  · by_cases hm : m = k
    · subst hm; simp
    · have h1 : (Sum.inl m : Fin r ⊕ Fin r) ≠ Sum.inl k := fun h => hm (Sum.inl_injective h)
      have h2 : (Sum.inl m : Fin r ⊕ Fin r) ≠ Sum.inr k := Sum.inl_ne_inr
      have h3 : (Sum.inr m : Fin r ⊕ Fin r) ≠ Sum.inl k := Sum.inr_ne_inl
      have h4 : (Sum.inr m : Fin r ⊕ Fin r) ≠ Sum.inr k := fun h => hm (Sum.inr_injective h)
      simp [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne h3 h4]
  · by_cases hm : m = k
    · subst hm; simp
    · have h1 : (Sum.inl m : Fin r ⊕ Fin r) ≠ Sum.inl k := fun h => hm (Sum.inl_injective h)
      have h2 : (Sum.inl m : Fin r ⊕ Fin r) ≠ Sum.inr k := Sum.inl_ne_inr
      have h3 : (Sum.inr m : Fin r ⊕ Fin r) ≠ Sum.inl k := Sum.inr_ne_inl
      have h4 : (Sum.inr m : Fin r ⊕ Fin r) ≠ Sum.inr k := fun h => hm (Sum.inr_injective h)
      simp [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne h3 h4]

theorem conj_mW (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0) (k : Fin r) (d : Fin r → Kˣ) :
    mW qA k a₀ * torH K A r d * mW qA k a₀ =
      torH K A r (dPerm (Equiv.swap (Sum.inl k) (Sum.inr k)) d) := by
  classical
  refine conj_torH_mono (mW_mul_self hani ha₀ k) (Equiv.swap (Sum.inl k) (Sum.inr k)) (swap_inl_inr_swap k)
    (fun c => if c = Sum.inl k then (qA a₀)⁻¹ else if c = Sum.inr k then qA a₀ else 1) (fun c => ?_)
    (fun z => mW_tail hani ha₀ k z) d
  by_cases h1 : c = Sum.inl k
  · subst h1
    simp [mW_inl hani ha₀]
  by_cases h2 : c = Sum.inr k
  · subst h2
    simp [mW_inr hani ha₀]
  · have hc : coordIdx c ≠ k := by
      intro h
      rcases c with m | m
      · exact h1 (by simp at h; rw [h])
      · exact h2 (by simp at h; rw [h])
    simp [h1, h2, mW_other hani ha₀ hc, Equiv.swap_apply_of_ne_of_ne h1 h2]

end ShortWeyl

end CFSG.RankThree.PartOne.K159H
