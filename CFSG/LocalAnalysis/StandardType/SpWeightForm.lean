module

public import CFSG.LocalAnalysis.StandardType.SpWeightDiag
public import CFSG.LocalAnalysis.StandardType.SpBlockMatrices
public import CFSG.LocalAnalysis.StandardType.SpWeightCounting

public section

namespace CFSG.StandardType

namespace SpFixed

open Matrix
open CFSG.Open (StatedSp)
open scoped Classical

variable {F : Type} [Field F] {n : ℕ} {Ω : Type} [Field Ω] [Algebra F Ω]
  {D : Subgroup (StatedSp n F)} [Fintype D]

namespace WeightBasis

variable (W : WeightBasis F n Ω D)

@[expose] noncomputable def Pm : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Ω :=
  (W.P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Ω)

@[expose] noncomputable def Pinv : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Ω :=
  ((W.P⁻¹ : GL (Fin n ⊕ Fin n) Ω) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Ω)

theorem Pinv_mul_Pm : W.Pinv * W.Pm = 1 := by
  unfold Pinv Pm
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem Pm_mul_Pinv : W.Pm * W.Pinv = 1 := by
  unfold Pinv Pm
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

@[expose] def wt (α : Fin n ⊕ Fin n) : D → Ω := fun a => W.w a α

@[expose] noncomputable def fiber (k : D → Ω) : Finset (Fin n ⊕ Fin n) :=
  Finset.univ.filter fun α => W.wt α = k

@[expose] noncomputable def conjHom : StatedSp n F →* Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Ω where
  toFun g := W.Pinv * matOver F n Ω g * W.Pm
  map_one' := by
    rw [map_one, Matrix.mul_one, W.Pinv_mul_Pm]
  map_mul' g h := by
    rw [map_mul]
    calc W.Pinv * (matOver F n Ω g * matOver F n Ω h) * W.Pm
        = W.Pinv * matOver F n Ω g * 1 * matOver F n Ω h * W.Pm := by
          simp only [Matrix.mul_assoc, Matrix.mul_one]
      _ = W.Pinv * matOver F n Ω g * (W.Pm * W.Pinv) * matOver F n Ω h * W.Pm := by
          rw [W.Pm_mul_Pinv]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem conjHom_apply (g : StatedSp n F) : W.conjHom g = W.Pinv * matOver F n Ω g * W.Pm :=
  rfl

theorem conjHom_diag (a : D) : W.conjHom (a : StatedSp n F) = diagonal (W.w a) :=
  W.conj_eq a

theorem w_mul (a b : D) (α : Fin n ⊕ Fin n) : W.w (a * b) α = W.w a α * W.w b α := by
  have hfun : (fun α : Fin n ⊕ Fin n => W.w (a * b) α) = fun α => W.w a α * W.w b α := by
    apply Matrix.diagonal_injective
    simp only [← W.conjHom_diag (a * b), Subgroup.coe_mul, map_mul, W.conjHom_diag a,
      W.conjHom_diag b, Matrix.diagonal_mul_diagonal]
  exact congr_fun hfun α

theorem w_one (α : Fin n ⊕ Fin n) : W.w 1 α = 1 := by
  have hfun : (fun α : Fin n ⊕ Fin n => W.w (1 : D) α) = fun _ => (1 : Ω) := by
    apply Matrix.diagonal_injective
    simp only [← W.conjHom_diag (1 : D), Subgroup.coe_one, map_one, Matrix.diagonal_one]
  exact congr_fun hfun α

theorem w_pow_three (hexp : ∀ a ∈ D, a ^ 3 = 1) (a : D) (α : Fin n ⊕ Fin n) : W.w a α ^ 3 = 1 := by
  have h : (W.conjHom (a : StatedSp n F)) ^ 3 = 1 := by
    rw [← map_pow, hexp a a.2, map_one]
  have h' : (diagonal (W.w a)) ^ 3 = 1 := by
    rwa [W.conjHom_diag a] at h
  rw [Matrix.diagonal_pow, ← Matrix.diagonal_one] at h'
  exact congr_fun (Matrix.diagonal_injective h') α

theorem eq_one_of_forall_w_eq_one {a : D} (h : ∀ α, W.w a α = 1) : a = 1 := by
  have hdiag : diagonal (W.w a) = 1 := by
    ext α β
    rw [Matrix.diagonal_apply]
    by_cases hab : α = β
    · subst hab; simp [h]
    · simp [hab]
  have h1 : W.Pinv * matOver F n Ω (a : StatedSp n F) * W.Pm = 1 := by
    rw [← W.conjHom_apply (a : StatedSp n F), W.conjHom_diag a, hdiag]
  have h2 : matOver F n Ω (a : StatedSp n F) = 1 := by
    calc matOver F n Ω (a : StatedSp n F)
        = W.Pm * W.Pinv * matOver F n Ω (a : StatedSp n F) * (W.Pm * W.Pinv) := by
          rw [W.Pm_mul_Pinv]; simp
      _ = W.Pm * (W.Pinv * matOver F n Ω (a : StatedSp n F) * W.Pm) * W.Pinv := by
          noncomm_ring
      _ = 1 := by rw [h1]; simp [W.Pm_mul_Pinv]
  apply Subtype.ext
  have h2' : matOver F n Ω (a : StatedSp n F) = matOver F n Ω (1 : StatedSp n F) := by
    rw [h2, map_one]
  exact matOver_injective h2'

theorem splits_conjHom_fiber {g : StatedSp n F}
    (hg : g ∈ Subgroup.centralizer (D : Set (StatedSp n F))) (k : D → Ω) :
    SpBlocks.Splits (W.fiber k) (W.conjHom g) := by
  apply SpBlocks.splits_fiber_of_forall W.wt
  intro α β h
  exact SpBlocks.entries_eq_of_commute_diagonal (fun a α => W.w a α) (fun a => by
    have hcomm : (a : StatedSp n F) * g = g * (a : StatedSp n F) :=
      (Subgroup.mem_centralizer_iff.1 hg) (a : StatedSp n F) a.2
    have hconj : W.conjHom ((a : StatedSp n F) * g) = W.conjHom (g * (a : StatedSp n F)) := by
      rw [hcomm]
    simp only [map_mul] at hconj
    rw [W.conjHom_diag a] at hconj
    exact hconj.symm) h

@[expose] noncomputable def gramConj : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Ω :=
  W.Pmᵀ * (gram F n).map (algebraMap F Ω) * W.Pm

theorem gram_mul_neg_self : gram F n * (-gram F n) = 1 := by
  have hneg : -gram F n = Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) F) (-1) 1 0 := by
    unfold gram
    rw [Matrix.fromBlocks_neg]
    simp
  rw [hneg]
  unfold gram
  rw [fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul,
    zero_add, add_zero, neg_zero, neg_neg]
  rw [Matrix.fromBlocks_one]

theorem neg_gram_mul_self : (-gram F n) * gram F n = 1 := by
  rw [Matrix.neg_mul, ← Matrix.mul_neg, gram_mul_neg_self]

theorem isUnit_gramConj : IsUnit W.gramConj := by
  have hP : IsUnit W.Pm := ⟨⟨W.Pm, W.Pinv, W.Pm_mul_Pinv, W.Pinv_mul_Pm⟩, rfl⟩
  have hPt : IsUnit W.Pmᵀ := (Matrix.isUnit_transpose (A := W.Pm)).2 hP
  have hgram : IsUnit ((gram F n).map (algebraMap F Ω)) := by
    refine ⟨⟨(gram F n).map (algebraMap F Ω), -((gram F n).map (algebraMap F Ω)), ?_, ?_⟩, rfl⟩
    · rw [← Matrix.map_neg (algebraMap F Ω) (fun a => map_neg (algebraMap F Ω) a),
        ← Matrix.map_mul, gram_mul_neg_self]
      exact Matrix.map_one (algebraMap F Ω) (map_zero _) (map_one _)
    · rw [← Matrix.map_neg (algebraMap F Ω) (fun a => map_neg (algebraMap F Ω) a),
        ← Matrix.map_mul, neg_gram_mul_self]
      exact Matrix.map_one (algebraMap F Ω) (map_zero _) (map_one _)
  rw [gramConj]
  exact (hPt.mul hgram).mul hP

theorem conjHom_transpose_mul_gramConj_mul (g : StatedSp n F) :
    (W.conjHom g)ᵀ * W.gramConj * W.conjHom g = W.gramConj := by
  have hA : (matOver F n Ω g)ᵀ * (gram F n).map (algebraMap F Ω) * matOver F n Ω g =
      (gram F n).map (algebraMap F Ω) := by
    have h := congrArg (fun M => M.map (algebraMap F Ω)) (matHom_transpose_mul_gram_mul g)
    simpa only [Matrix.map_mul, Matrix.transpose_map, matOver_apply] using h
  have hPt : W.Pinvᵀ * W.Pmᵀ = 1 := by
    rw [← Matrix.transpose_mul, W.Pm_mul_Pinv, Matrix.transpose_one]
  have htrans : (W.Pinv * matOver F n Ω g * W.Pm)ᵀ =
      W.Pmᵀ * (matOver F n Ω g)ᵀ * W.Pinvᵀ := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  change (W.Pinv * matOver F n Ω g * W.Pm)ᵀ *
      (W.Pmᵀ * (gram F n).map (algebraMap F Ω) * W.Pm) *
      (W.Pinv * matOver F n Ω g * W.Pm) =
        W.Pmᵀ * (gram F n).map (algebraMap F Ω) * W.Pm
  rw [htrans]
  calc
    W.Pmᵀ * (matOver F n Ω g)ᵀ * W.Pinvᵀ *
        (W.Pmᵀ * (gram F n).map (algebraMap F Ω) * W.Pm) *
        (W.Pinv * matOver F n Ω g * W.Pm)
        = W.Pmᵀ * (matOver F n Ω g)ᵀ * (W.Pinvᵀ * W.Pmᵀ) *
            (gram F n).map (algebraMap F Ω) * (W.Pm * W.Pinv) * matOver F n Ω g * W.Pm := by
          noncomm_ring
    _ = W.Pmᵀ * (matOver F n Ω g)ᵀ * (gram F n).map (algebraMap F Ω) * matOver F n Ω g * W.Pm := by
          rw [hPt, W.Pm_mul_Pinv]; simp
    _ = W.Pmᵀ * ((matOver F n Ω g)ᵀ * (gram F n).map (algebraMap F Ω) * matOver F n Ω g) *
        W.Pm := by
          noncomm_ring
    _ = W.Pmᵀ * (gram F n).map (algebraMap F Ω) * W.Pm := by rw [hA]

theorem gramConj_entry {α β : Fin n ⊕ Fin n} (h : W.gramConj α β ≠ 0) (a : D) :
    W.w a α * W.w a β = 1 := by
  have hmat := W.conjHom_transpose_mul_gramConj_mul (a : StatedSp n F)
  rw [W.conjHom_diag a] at hmat
  have hentry := congr_fun (congr_fun hmat α) β
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal] at hentry
  have hentry' : W.w a α * W.w a β * W.gramConj α β = 1 * W.gramConj α β := by
    rw [one_mul]
    calc W.w a α * W.w a β * W.gramConj α β
        = (W.w a α * W.gramConj α β) * W.w a β := by ring
      _ = W.gramConj α β := hentry
  exact mul_right_cancel₀ h hentry'

theorem wt_eq_inv_of_gramConj_entry {α β : Fin n ⊕ Fin n} (h : W.gramConj α β ≠ 0) :
    W.wt β = (W.wt α)⁻¹ := by
  funext a
  exact eq_inv_of_mul_eq_one_right (W.gramConj_entry h a)

theorem card_fiber_le (hcard : Fintype.card D = 9) (hexp : ∀ a ∈ D, a ^ 3 = 1) (k : D → Ω)
    (hk : ∃ a, k a ≠ 1) : (W.fiber k).card ≤ n - 1 := by
  by_cases hfib : W.fiber k = ∅
  · rw [hfib]; simp
  · obtain ⟨α₀, hα₀⟩ := (Finset.nonempty_iff_ne_empty).2 hfib
    have hk_eq : W.wt α₀ = k := (Finset.mem_filter.mp hα₀).2
    have hk_ne : k ≠ k⁻¹ := by
      intro hkk
      obtain ⟨a, ha⟩ := hk
      have h3 : k a ^ 3 = 1 := by
        rw [← hk_eq]; exact W.w_pow_three hexp a α₀
      have hka0 : k a ≠ 0 := by
        intro h0
        rw [h0] at h3
        norm_num at h3
      have hka : k a = (k a)⁻¹ := congr_fun hkk a
      have h2 : k a ^ 2 = 1 := by
        have hsq : k a * k a = 1 := by
          nth_rewrite 1 [hka]
          exact inv_mul_cancel₀ hka0
        rwa [pow_two]
      have h3' : k a ^ 2 * k a = 1 := by
        rw [pow_succ] at h3; exact h3
      rw [h2, one_mul] at h3'
      exact ha h3'
    have hcount := SpCount.card_fiber_add_card_fiber_le (wt := W.wt) (inv := fun f : D → Ω => f⁻¹)
      (hinv := inv_inv) (M := W.gramConj) W.isUnit_gramConj
      (fun α β h => W.wt_eq_inv_of_gramConj_entry h) hk_ne
    have hcardι : Fintype.card (Fin n ⊕ Fin n) = 2 * n := by
      rw [Fintype.card_sum, Fintype.card_fin]; ring
    have hle_n : (W.fiber k).card ≤ n := by
      change (Finset.univ.filter fun α => W.wt α = k).card ≤ n
      have h := hcount.1
      rw [hcardι] at h
      omega
    rcases Nat.eq_or_lt_of_le hle_n with h_eq | h_lt
    · exfalso
      have h_eq' : (Finset.univ.filter fun α => W.wt α = k).card = n := h_eq
      have hforall : ∀ α, W.wt α = k ∨ W.wt α = k⁻¹ := by
        apply hcount.2
        rw [h_eq', hcardι]
      have hk_one : k 1 = 1 := by
        rw [← hk_eq]; exact W.w_one α₀
      have hk_mul : ∀ a b : D, k (a * b) = k a * k b := by
        intro a b
        rw [← hk_eq]; exact W.w_mul a b α₀
      have hcube : ∀ a : D, k a ^ 3 = 1 := by
        intro a
        rw [← hk_eq]; exact W.w_pow_three hexp a α₀
      have hb0 : ∀ a : D, k a ≠ 0 := by
        intro a h0
        have := hcube a
        rw [h0] at this
        norm_num at this
      have hbinv : ∀ b : D, k b⁻¹ = (k b)⁻¹ := by
        intro b
        have h := hk_mul b b⁻¹
        rw [mul_inv_cancel, hk_one] at h
        exact eq_inv_of_mul_eq_one_right h.symm
      have hinj : Function.Injective k := by
        intro a b hab
        have h1 : k (a * b⁻¹) = 1 := by
          rw [hk_mul, hbinv b, hab, mul_inv_cancel₀ (hb0 b)]
        have hw : ∀ α, W.w (a * b⁻¹) α = 1 := by
          intro α
          rcases hforall α with hh | hh
          · have hh' := congr_fun hh (a * b⁻¹)
            rw [h1] at hh'
            simpa [WeightBasis.wt] using hh'
          · have hh' : W.wt α (a * b⁻¹) = (k (a * b⁻¹))⁻¹ := by
              rw [hh]; rfl
            rw [h1, inv_one] at hh'
            simpa [WeightBasis.wt] using hh'
        have h1' := W.eq_one_of_forall_w_eq_one hw
        have hmul : a * b⁻¹ * b = a := by rw [mul_assoc, inv_mul_cancel, mul_one]
        rw [← hmul, h1', one_mul]
      have hle3 := SpCount.card_le_three_of_injective_cube k hinj hcube
      omega
    · omega

theorem conj_fixedNorm [CharP Ω 2] (hodd : Odd (Fintype.card D)) :
    W.Pinv * (fixedNorm D).map (algebraMap F Ω) * W.Pm =
      diagonal fun α => if W.wt α = 1 then 1 else 0 := by
  have hper : ∀ α : Fin n ⊕ Fin n,
      (∑ a : D, W.w a α) = if W.wt α = 1 then 1 else 0 := by
    intro α
    by_cases hα : W.wt α = 1
    · rw [if_pos hα]
      have hw : ∀ a : D, W.w a α = 1 := fun a => congr_fun hα a
      rw [Finset.sum_congr rfl (fun a _ => hw a), Finset.sum_const, Finset.card_univ,
        ← Nat.cast_smul_eq_nsmul Ω,
        natCast_eq_one_of_odd_of_two_eq_zero hodd (CharP.cast_eq_zero Ω 2), one_smul]
    · rw [if_neg hα]
      obtain ⟨b, hb⟩ : ∃ b : D, W.w b α ≠ 1 := by
        by_contra h
        push Not at h
        exact hα (funext fun a => h a)
      have hS : (∑ a : D, W.w a α) = W.w b α * ∑ a : D, W.w a α := by
        rw [Finset.mul_sum]
        trans ∑ a : D, W.w (b * a) α
        · exact (Fintype.sum_equiv (Equiv.mulLeft b) (fun a => W.w (b * a) α)
            (fun a => W.w a α) (fun _ => rfl)).symm
        · exact Finset.sum_congr rfl (fun a _ => W.w_mul b a α)
      have h2 : (1 - W.w b α) * (∑ a : D, W.w a α) = 0 := by
        rw [sub_mul, one_mul, ← hS, sub_self]
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd (sub_eq_zero.mp h).symm hb
      · exact h
  have hmap : (fixedNorm D).map (algebraMap F Ω) =
      ∑ a : D, matOver F n Ω (a : StatedSp n F) := by
    change (RingHom.mapMatrix (algebraMap F Ω)) (fixedNorm D) = _
    rw [fixedNorm, map_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rfl
  rw [hmap]
  trans ∑ a : D, diagonal (W.w a)
  · rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← W.conjHom_apply (a : StatedSp n F), W.conjHom_diag a]
  · rw [show (∑ a : D, diagonal (W.w a)) = diagonal (fun α => ∑ a : D, W.w a α) from by
      ext i j
      simp only [Matrix.sum_apply, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]]
    congr 1
    funext α
    exact hper α

theorem vec_eq_zero_of_fixedNorm [CharP Ω 2] (hodd : Odd (Fintype.card D))
    {v : Fin n ⊕ Fin n → F} (hv : fixedNorm D *ᵥ v = 0) {α : Fin n ⊕ Fin n} (hα : W.wt α = 1) :
    (W.Pinv *ᵥ fun i => algebraMap F Ω (v i)) α = 0 := by
  have hN' : (fixedNorm D).map (algebraMap F Ω) *ᵥ (fun i => algebraMap F Ω (v i)) = 0 := by
    funext i
    have h := RingHom.map_mulVec (algebraMap F Ω) (fixedNorm D) v i
    rw [show (fixedNorm D *ᵥ v) i = 0 from congr_fun hv i, map_zero] at h
    simpa [Function.comp_def] using h.symm
  have hL : (W.Pinv * (fixedNorm D).map (algebraMap F Ω) * W.Pm) *ᵥ
      (W.Pinv *ᵥ fun i => algebraMap F Ω (v i)) = 0 := by
    have hy : W.Pm *ᵥ (W.Pinv *ᵥ fun i => algebraMap F Ω (v i)) =
        (fun i => algebraMap F Ω (v i)) := by
      rw [Matrix.mulVec_mulVec (fun i => algebraMap F Ω (v i)) W.Pm W.Pinv,
        W.Pm_mul_Pinv, Matrix.one_mulVec]
    rw [← Matrix.mulVec_mulVec (W.Pinv *ᵥ fun i => algebraMap F Ω (v i))
          (W.Pinv * (fixedNorm D).map (algebraMap F Ω)) W.Pm,
      hy,
      ← Matrix.mulVec_mulVec (fun i => algebraMap F Ω (v i)) W.Pinv
        ((fixedNorm D).map (algebraMap F Ω)),
      hN', Matrix.mulVec_zero]
  have := congr_fun hL α
  rw [W.conj_fixedNorm hodd, Matrix.mulVec_diagonal, hα] at this
  simpa using this

variable (σ : Ω ≃+* Ω)

@[expose] noncomputable def twist : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Ω :=
  W.Pinv * W.Pm.map σ

theorem isUnit_twist : IsUnit (W.twist σ) := by
  have hPinv : IsUnit W.Pinv := ⟨⟨W.Pinv, W.Pm, W.Pinv_mul_Pm, W.Pm_mul_Pinv⟩, rfl⟩
  have hPm : IsUnit (W.Pm.map σ) := by
    refine ⟨⟨W.Pm.map σ, W.Pinv.map σ, ?_, ?_⟩, rfl⟩
    · rw [← Matrix.map_mul, W.Pm_mul_Pinv]
      exact Matrix.map_one σ (map_zero σ) (map_one σ)
    · rw [← Matrix.map_mul, W.Pinv_mul_Pm]
      exact Matrix.map_one σ (map_zero σ) (map_one σ)
  rw [twist]
  exact hPinv.mul hPm

theorem twist_entry (hσF : ∀ x : F, σ (algebraMap F Ω x) = algebraMap F Ω x)
    (hσw : ∀ (a : D) (α : Fin n ⊕ Fin n), σ (W.w a α) = (W.w a α)⁻¹)
    {α β : Fin n ⊕ Fin n} (h : W.twist σ α β ≠ 0) : W.wt α = (W.wt β)⁻¹ := by
  funext a
  have hA : (matOver F n Ω (a : StatedSp n F)).map σ = matOver F n Ω (a : StatedSp n F) := by
    rw [matOver_apply]
    ext i j
    simp only [Matrix.map_apply, matHom_apply]
    exact hσF _
  have hPmPinv : (W.Pm.map σ) * (W.Pinv.map σ) = 1 := by
    rw [← Matrix.map_mul, W.Pm_mul_Pinv]
    exact Matrix.map_one σ (map_zero σ) (map_one σ)
  have h1 : (W.Pinv.map σ) * matOver F n Ω (a : StatedSp n F) * (W.Pm.map σ) =
      diagonal (fun γ => σ (W.w a γ)) := by
    have h := congrArg (fun M => M.map σ) (W.conjHom_diag a)
    rw [W.conjHom_apply a] at h
    simp only [Matrix.map_mul, hA, Matrix.diagonal_map (map_zero σ)] at h
    exact h
  have h2 : matOver F n Ω (a : StatedSp n F) * (W.Pm.map σ) =
      (W.Pm.map σ) * diagonal (fun γ => σ (W.w a γ)) := by
    have h' := congrArg (fun M => (W.Pm.map σ) * M) h1
    rw [show (W.Pm.map σ) * ((W.Pinv.map σ) * matOver F n Ω ↑a * (W.Pm.map σ)) =
        ((W.Pm.map σ) * (W.Pinv.map σ)) * matOver F n Ω ↑a * (W.Pm.map σ) from by
          noncomm_ring] at h'
    rw [hPmPinv, Matrix.one_mul] at h'
    exact h'
  have h3 : W.Pinv * matOver F n Ω (a : StatedSp n F) = diagonal (W.w a) * W.Pinv := by
    calc W.Pinv * matOver F n Ω (a : StatedSp n F)
        = (W.Pinv * matOver F n Ω (a : StatedSp n F)) * 1 := (Matrix.mul_one _).symm
      _ = (W.Pinv * matOver F n Ω (a : StatedSp n F)) * (W.Pm * W.Pinv) := by
          rw [W.Pm_mul_Pinv]
      _ = ((W.Pinv * matOver F n Ω (a : StatedSp n F)) * W.Pm) * W.Pinv := by
          noncomm_ring
      _ = (W.Pinv * matOver F n Ω (a : StatedSp n F) * W.Pm) * W.Pinv := rfl
      _ = W.conjHom (a : StatedSp n F) * W.Pinv := by rw [← W.conjHom_apply (a : StatedSp n F)]
      _ = diagonal (W.w a) * W.Pinv := by rw [W.conjHom_diag a]
  have hT : W.twist σ * diagonal (fun γ => σ (W.w a γ)) =
      diagonal (W.w a) * W.twist σ := by
    rw [twist]
    calc (W.Pinv * W.Pm.map σ) * diagonal (fun γ => σ (W.w a γ))
        = W.Pinv * ((W.Pm.map σ) * diagonal (fun γ => σ (W.w a γ))) := by
          rw [Matrix.mul_assoc]
      _ = W.Pinv * (matOver F n Ω (a : StatedSp n F) * (W.Pm.map σ)) := by rw [← h2]
      _ = (W.Pinv * matOver F n Ω (a : StatedSp n F)) * (W.Pm.map σ) := by
          rw [Matrix.mul_assoc]
      _ = (diagonal (W.w a) * W.Pinv) * (W.Pm.map σ) := by rw [h3]
      _ = diagonal (W.w a) * (W.Pinv * W.Pm.map σ) := by rw [Matrix.mul_assoc]
  have hentry := congr_fun (congr_fun hT α) β
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
  have hc : σ (W.w a β) = W.w a α := by
    rw [mul_comm (W.w a α)] at hentry
    exact mul_left_cancel₀ h hentry
  rw [hσw a β] at hc
  exact hc.symm

@[expose] noncomputable def form : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Ω :=
  W.gramConj * W.twist σ

theorem isUnit_form : IsUnit (W.form σ) := by
  exact W.isUnit_gramConj.mul (W.isUnit_twist σ)

theorem splits_form_fiber (hσF : ∀ x : F, σ (algebraMap F Ω x) = algebraMap F Ω x)
    (hσw : ∀ (a : D) (α : Fin n ⊕ Fin n), σ (W.w a α) = (W.w a α)⁻¹) (k : D → Ω) :
    SpBlocks.Splits (W.fiber k) (W.form σ) := by
  apply SpBlocks.splits_fiber_of_forall W.wt
  intro α β h
  have hmul : (W.gramConj * W.twist σ) α β ≠ 0 := h
  rw [Matrix.mul_apply] at hmul
  obtain ⟨γ, _, hγ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hmul
  rw [mul_ne_zero_iff] at hγ
  have h1 := W.wt_eq_inv_of_gramConj_entry hγ.1
  have h2 := W.twist_entry σ hσF hσw hγ.2
  exact inv_injective (h1.symm.trans h2)

theorem form_invariant (hσF : ∀ x : F, σ (algebraMap F Ω x) = algebraMap F Ω x) (g : StatedSp n F) :
    (W.conjHom g)ᵀ * W.form σ * (W.conjHom g).map σ = W.form σ := by
  have hA : (matOver F n Ω g).map σ = matOver F n Ω g := by
    rw [matOver_apply]
    ext i j
    simp only [Matrix.map_apply, matHom_apply]
    exact hσF _
  have hPmPinv : (W.Pm.map σ) * (W.Pinv.map σ) = 1 := by
    rw [← Matrix.map_mul, W.Pm_mul_Pinv]
    exact Matrix.map_one σ (map_zero σ) (map_one σ)
  have hQmap : (W.conjHom g).map σ =
      (W.Pinv.map σ) * matOver F n Ω g * (W.Pm.map σ) := by
    rw [W.conjHom_apply g]
    simp only [Matrix.map_mul, hA]
  have hQ : W.conjHom g * W.twist σ = W.twist σ * (W.conjHom g).map σ := by
    rw [hQmap, W.conjHom_apply g, twist]
    calc (W.Pinv * matOver F n Ω g * W.Pm) * (W.Pinv * W.Pm.map σ)
        = W.Pinv * matOver F n Ω g * (W.Pm * W.Pinv) * (W.Pm.map σ) := by noncomm_ring
      _ = W.Pinv * matOver F n Ω g * (W.Pm.map σ) := by rw [W.Pm_mul_Pinv]; simp
      _ = W.Pinv * ((W.Pm.map σ) * (W.Pinv.map σ)) * matOver F n Ω g * (W.Pm.map σ) := by
            rw [hPmPinv]; simp
      _ = W.Pinv * (W.Pm.map σ) * ((W.Pinv.map σ) * matOver F n Ω g * (W.Pm.map σ)) := by
            noncomm_ring
  have hgen : (W.conjHom g)ᵀ * (W.gramConj * W.twist σ) * (W.conjHom g).map σ =
      W.gramConj * W.twist σ := by
    calc (W.conjHom g)ᵀ * (W.gramConj * W.twist σ) * (W.conjHom g).map σ
        = (W.conjHom g)ᵀ * W.gramConj * (W.twist σ * (W.conjHom g).map σ) := by
          noncomm_ring
      _ = (W.conjHom g)ᵀ * W.gramConj * (W.conjHom g * W.twist σ) := by rw [← hQ]
      _ = ((W.conjHom g)ᵀ * W.gramConj * W.conjHom g) * W.twist σ := by noncomm_ring
      _ = W.gramConj * W.twist σ := by rw [W.conjHom_transpose_mul_gramConj_mul g]
  exact hgen

end WeightBasis

end SpFixed

end CFSG.StandardType
