module

public import CFSG.Quasithin.Vol2.Ch4Sec3SL3

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix

theorem exists_normal_elemAbelian_of_planeStab {F : Type} [Field F] [Fintype F] {n : ℕ}
    (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (W : Submodule F (Fin 3 → F)) (hW : Module.finrank F W = 2)
    (Y : Subgroup ↥(StatedSL 3 F)) (hY : Y ≠ ⊥) (hYperf : ⁅Y, Y⁆ = Y)
    (hstab : ∀ y ∈ Y, ∀ w ∈ W,
      (((y : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W)
    (hnorm : ∀ g : ↥(StatedSL 3 F),
      (∀ w ∈ W, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W) →
        g ∈ Subgroup.normalizer (Y : Set ↥(StatedSL 3 F))) :
    ∃ N : Subgroup ↥(StatedSL 3 F), N ≠ ⊥ ∧ N ≤ Y ∧ (∀ y ∈ N, y * y = 1) ∧
      ∀ y ∈ Y, ∀ x ∈ N, y * x * y⁻¹ ∈ N := by
  classical
  set e := specialLinearGroupEquivStatedSL 3 F with he
  let mat : ↥(StatedSL 3 F) → Matrix (Fin 3) (Fin 3) F := fun g => ((g : GL (Fin 3) F) : _)
  have hmat_mul : ∀ g h : ↥(StatedSL 3 F), mat (g * h) = mat g * mat h := fun g h => rfl
  have hmat_e : ∀ γ : SpecialLinearGroup (Fin 3) F, mat (e γ) = γ :=
    fun γ => specialLinearGroupEquivStatedSL_coe 3 F γ
  have h2 : (2 : F) = 0 := by
    have h := FiniteField.cast_card_eq_zero F
    rw [hF, Nat.cast_pow] at h
    exact pow_eq_zero_iff (by omega) |>.mp h
  have hWtop : W < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => ?_
    have h3 := congrArg (fun S : Submodule F (Fin 3 → F) => Module.finrank F S) h
    simp only [finrank_top, Module.finrank_fin_fun, hW] at h3
    omega
  obtain ⟨f, hf0, hWf⟩ := Submodule.exists_le_ker_of_lt_top W hWtop
  have hrange : LinearMap.range f = ⊤ := by
    obtain ⟨u₀, hu₀⟩ : ∃ u₀, f u₀ ≠ 0 := by
      by_contra h
      push Not at h
      exact hf0 (LinearMap.ext h)
    refine LinearMap.range_eq_top.mpr fun a => ⟨(a / f u₀) • u₀, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ a hu₀]
  have hker : LinearMap.ker f = W := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq hWf
    have h3 := LinearMap.finrank_range_add_finrank_ker f
    rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h3
    rw [hW]
    omega
  have hmemW : ∀ u, u ∈ W ↔ f u = 0 := fun u => by rw [← hker, LinearMap.mem_ker]
  set fv : Fin 3 → F := fun i => f (fun j => if i = j then 1 else 0) with hfvdef
  have hfv : ∀ u, fv ⬝ᵥ u = f u := by
    intro u
    conv_rhs => rw [pi_eq_sum_univ u]
    simp only [map_sum, map_smul, smul_eq_mul, dotProduct, hfvdef]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hfv0 : fv ≠ 0 := by
    intro h
    apply hf0
    refine LinearMap.ext fun u => ?_
    rw [← hfv, h, zero_dotProduct, LinearMap.zero_apply]
  have hfinv : ∀ y ∈ Y, ∀ u, f ((mat y).mulVec u) = f u := by
    obtain ⟨u₀, hu₀⟩ : ∃ u₀, f u₀ ≠ 0 := by
      by_contra h
      push Not at h
      exact hf0 (LinearMap.ext h)
    have hchi : ∀ g : ↥(StatedSL 3 F), (∀ w ∈ W, (mat g).mulVec w ∈ W) →
        ∀ u, f ((mat g).mulVec u) = (f ((mat g).mulVec u₀) / f u₀) * f u := by
      intro g hg u
      have hd : u - (f u / f u₀) • u₀ ∈ W := by
        rw [hmemW, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hu₀, sub_self]
      have h3 := (hmemW _).mp (hg _ hd)
      rw [mulVec_sub, mulVec_smul, map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h3
      rw [h3]
      field_simp
    let S : Subgroup ↥(StatedSL 3 F) :=
      { carrier := {g | ∀ u, f ((mat g).mulVec u) = f u}
        one_mem' := fun u => by simp [mat]
        mul_mem' := fun {a b} ha hb u => by
          show f ((mat a * mat b).mulVec u) = f u
          rw [← mulVec_mulVec, ha, hb]
        inv_mem' := fun {a} ha u => by
          have h3 := ha ((mat a⁻¹).mulVec u)
          rw [mulVec_mulVec, ← hmat_mul, mul_inv_cancel] at h3
          simpa [mat] using h3.symm }
    have hYS : Y ≤ S := by
      rw [← hYperf, Subgroup.commutator_le]
      intro a ha b hb u
      have hYW : ∀ y ∈ Y, ∀ w ∈ W, (mat y).mulVec w ∈ W := hstab
      set χ : ↥(StatedSL 3 F) → F := fun g => f ((mat g).mulVec u₀) / f u₀ with hχ
      have hc : ∀ y ∈ Y, ∀ u, f ((mat y).mulVec u) = χ y * f u :=
        fun y hy => hchi y (hYW y hy)
      have hinv : ∀ y ∈ Y, χ y * χ y⁻¹ = 1 := by
        intro y hy
        have h3 := hc y hy ((mat y⁻¹).mulVec u₀)
        rw [mulVec_mulVec, ← hmat_mul, mul_inv_cancel, hc y⁻¹ (Y.inv_mem hy)] at h3
        have h4 : f ((mat 1).mulVec u₀) = f u₀ := by simp [mat]
        rw [h4] at h3
        have h5 : f u₀ * 1 = f u₀ * (χ y * χ y⁻¹) :=
          calc f u₀ * 1 = f u₀ := mul_one _
            _ = χ y * (χ y⁻¹ * f u₀) := h3
            _ = f u₀ * (χ y * χ y⁻¹) := by ring
        exact (mul_left_cancel₀ hu₀ h5).symm
      show f ((mat (a * b * a⁻¹ * b⁻¹)).mulVec u) = f u
      rw [hmat_mul, hmat_mul, hmat_mul, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
        hc a ha, hc b hb, hc a⁻¹ (Y.inv_mem ha), hc b⁻¹ (Y.inv_mem hb)]
      have h3 := hinv a ha
      have h4 := hinv b hb
      calc χ a * (χ b * (χ a⁻¹ * (χ b⁻¹ * f u))) = (χ a * χ a⁻¹) * (χ b * χ b⁻¹) * f u := by
            ring
        _ = f u := by rw [h3, h4, one_mul, one_mul]
    exact fun y hy => hYS hy
  have hfvinv : ∀ y ∈ Y, fv ᵥ* mat y = fv := by
    intro y hy
    funext i
    have h3 := hfinv y hy (fun j => if i = j then 1 else 0)
    rw [← hfv, ← hfv, dotProduct_mulVec] at h3
    have h5 : ∀ w : Fin 3 → F, w ⬝ᵥ (fun j => if i = j then (1 : F) else 0) = w i := by
      intro w
      simp [dotProduct]
    rw [h5, h5] at h3
    exact h3
  have houter : ∀ (w u : Fin 3 → F) (a : F),
      (1 + vecMulVec w (a • fv)).mulVec u = u + (a * f u) • w := by
    intro w u a
    rw [add_mulVec, one_mulVec, vecMulVec_mulVec, smul_dotProduct, hfv, smul_eq_mul,
      op_smul_eq_smul]
  have hdet : ∀ (w : Fin 3 → F) (a : F), w ∈ W → (1 + vecMulVec w (a • fv)).det = 1 := by
    intro w a hw
    have h3 : vecMulVec w (a • fv) =
        replicateCol Unit w * replicateRow Unit (a • fv) := by
      ext i j
      simp [vecMulVec_apply, mul_apply]
    rw [h3, det_one_add_replicateCol_mul_replicateRow (ι := Unit), smul_dotProduct, hfv,
      (hmemW w).mp hw, smul_zero, add_zero]
  have hmat_one : mat 1 = 1 := by simp [mat]
  have hmat_inj : ∀ g h : ↥(StatedSL 3 F), mat g = mat h → g = h :=
    fun g h hgh => Subtype.ext (Units.ext hgh)
  have hdetu : ∀ u ∈ W, (1 + vecMulVec u fv).det = 1 := fun u hu => by
    have h := hdet u 1 hu
    rwa [one_smul] at h
  have hact : ∀ u w : Fin 3 → F, (1 + vecMulVec u fv).mulVec w = w + f w • u := by
    intro u w
    have h := houter u w 1
    rwa [one_smul, one_mul] at h
  have hτex : ∀ u ∈ W, ∃ τ : ↥(StatedSL 3 F), mat τ = 1 + vecMulVec u fv :=
    fun u hu => ⟨e (⟨1 + vecMulVec u fv, hdetu u hu⟩ : SpecialLinearGroup (Fin 3) F), hmat_e _⟩
  have haa0 : ∀ a : Fin 3 → F, a + a = 0 := fun a => by
    rw [← two_smul F, h2, zero_smul]
  have hMM : ∀ a b : Fin 3 → F, b ∈ W →
      (1 + vecMulVec a fv) * (1 + vecMulVec b fv) = 1 + vecMulVec (a + b) fv := by
    intro a b hb
    have hb0 : fv ⬝ᵥ b = 0 := by rw [hfv]; exact (hmemW b).mp hb
    rw [add_mul, one_mul, mul_add, mul_one, vecMulVec_mul_vecMulVec, hb0, zero_smul,
      vecMulVec_zero, add_zero, add_vecMulVec]
    abel
  have hMM1 : ∀ a ∈ W, (1 + vecMulVec a fv) * (1 + vecMulVec a fv) = 1 := fun a ha => by
    rw [hMM a a ha, haa0 a, zero_vecMulVec, add_zero]
  have hconj : ∀ y ∈ Y, ∀ g : ↥(StatedSL 3 F), ∀ u : Fin 3 → F,
      mat g = 1 + vecMulVec u fv → mat (y * g * y⁻¹) = 1 + vecMulVec (mat y *ᵥ u) fv := by
    intro y hy g u hg
    have hyy : mat y * mat y⁻¹ = 1 := by rw [← hmat_mul, mul_inv_cancel, hmat_one]
    have hyinv : fv ᵥ* mat y⁻¹ = fv := hfvinv y⁻¹ (Y.inv_mem hy)
    rw [hmat_mul, hmat_mul, hg, mul_add, mul_one, add_mul, mul_vecMulVec, vecMulVec_mul, hyinv,
      hyy]
  let N : Subgroup ↥(StatedSL 3 F) :=
    { carrier := {x | x ∈ Y ∧ ∃ u ∈ W, mat x = 1 + vecMulVec u fv}
      one_mem' := ⟨Y.one_mem, 0, W.zero_mem, by rw [hmat_one, zero_vecMulVec, add_zero]⟩
      mul_mem' := fun {a b} ha hb => by
        obtain ⟨ha, u, hu, hau⟩ := ha
        obtain ⟨hb, v, hv, hbv⟩ := hb
        exact ⟨Y.mul_mem ha hb, u + v, W.add_mem hu hv,
          by rw [hmat_mul, hau, hbv, hMM u v hv]⟩
      inv_mem' := fun {a} ha => by
        obtain ⟨ha, u, hu, hau⟩ := ha
        have haa : a * a = 1 := hmat_inj _ _ (by rw [hmat_mul, hau, hmat_one, hMM1 u hu])
        rw [inv_eq_of_mul_eq_one_right haa]
        exact ⟨ha, u, hu, hau⟩ }
  have hNY : N ≤ Y := fun x hx => by
    obtain ⟨h, _⟩ := hx
    exact h
  have hsq : ∀ x ∈ N, x * x = 1 := by
    intro x hx
    obtain ⟨_, u, hu, hxu⟩ := hx
    exact hmat_inj _ _ (by rw [hmat_mul, hxu, hmat_one, hMM1 u hu])
  have hNconj : ∀ y ∈ Y, ∀ x ∈ N, y * x * y⁻¹ ∈ N := by
    intro y hy x hx
    obtain ⟨hxY, u, hu, hxu⟩ := hx
    exact ⟨Y.mul_mem (Y.mul_mem hy hxY) (Y.inv_mem hy), mat y *ᵥ u, hstab y hy u hu,
      hconj y hy x u hxu⟩
  have hclaim : ∃ y₀ ∈ Y, ∃ u₀ ∈ W, mat y₀ *ᵥ u₀ ≠ u₀ := by
    by_contra hcon
    push Not at hcon
    have hYG : ⁅Y.map (StatedSL 3 F).subtype, Y.map (StatedSL 3 F).subtype⁆ =
        Y.map (StatedSL 3 F).subtype := by
      rw [← Subgroup.map_commutator, hYperf]
    have hstabG : ∀ g ∈ Y.map (StatedSL 3 F).subtype, ∀ w ∈ W,
        (g : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W := by
      intro g hg w hw
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
      exact hstab y hy w hw
    have hform : ∀ y ∈ Y, ∃ a ∈ W, mat y = 1 + vecMulVec a fv := by
      intro y hy
      obtain ⟨v₁, hv₁⟩ := LinearMap.range_eq_top.mp hrange (1 : F)
      obtain ⟨a, ha⟩ : ∃ a, a = mat y *ᵥ v₁ - v₁ := ⟨_, rfl⟩
      have haW : a ∈ W := by
        rw [ha]
        exact mulVec_sub_mem_of_perfect W hW _ hYG hstabG
          (Subgroup.mem_map_of_mem (StatedSL 3 F).subtype hy) v₁
      have hmatv : ∀ v, mat y *ᵥ v = v + (fv ⬝ᵥ v) • a := by
        intro v
        have hw : v - (fv ⬝ᵥ v) • v₁ ∈ W := by
          rw [hmemW, map_sub, map_smul, smul_eq_mul, hv₁, mul_one, sub_eq_zero, hfv]
        have hfix : mat y *ᵥ (v - (fv ⬝ᵥ v) • v₁) = v - (fv ⬝ᵥ v) • v₁ := hcon y hy _ hw
        have hmy1 : mat y *ᵥ v₁ = a + v₁ := by rw [ha, sub_add_cancel]
        conv_lhs => rw [← sub_add_cancel v ((fv ⬝ᵥ v) • v₁)]
        rw [mulVec_add, mulVec_smul, hfix, hmy1, smul_add]
        abel
      refine ⟨a, haW, Matrix.ext_of_mulVec_single fun i => ?_⟩
      rw [hmatv, add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul]
    have hcomm : ∀ y ∈ Y, ∀ y' ∈ Y, y * y' = y' * y := by
      intro y hy y' hy'
      obtain ⟨a, ha, hya⟩ := hform y hy
      obtain ⟨b, hb, hyb⟩ := hform y' hy'
      apply hmat_inj
      rw [hmat_mul, hmat_mul, hya, hyb, hMM a b hb, hMM b a ha, add_comm a b]
    have hYbot : ⁅Y, Y⁆ ≤ ⊥ := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm a ha b hb
    rw [hYperf] at hYbot
    exact hY (le_bot_iff.mp hYbot)
  obtain ⟨y₀, hy₀, u₀, hu₀, hcl⟩ := hclaim
  obtain ⟨τ₀, hτ₀⟩ := hτex u₀ hu₀
  have hτ₀sq : τ₀ * τ₀ = 1 := hmat_inj _ _ (by rw [hmat_mul, hτ₀, hmat_one, hMM1 u₀ hu₀])
  have hτ₀inv : τ₀⁻¹ = τ₀ := inv_eq_of_mul_eq_one_right hτ₀sq
  have hτ₀W : ∀ w ∈ W, (mat τ₀).mulVec w ∈ W := by
    intro w hw
    rw [hτ₀, hact u₀ w, (hmemW w).mp hw, zero_smul, add_zero]
    exact hw
  have hτ₀N : τ₀ ∈ Subgroup.normalizer (Y : Set ↥(StatedSL 3 F)) := hnorm τ₀ hτ₀W
  have hcY : y₀ * τ₀ * y₀⁻¹ * τ₀ ∈ Y := by
    have h1 : τ₀ * y₀⁻¹ * τ₀⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp hτ₀N y₀⁻¹).mp (Y.inv_mem hy₀)
    rw [hτ₀inv] at h1
    have h3 : y₀ * τ₀ * y₀⁻¹ * τ₀ = y₀ * (τ₀ * y₀⁻¹ * τ₀) := by simp only [mul_assoc]
    rw [h3]
    exact Y.mul_mem hy₀ h1
  have hcmat : mat (y₀ * τ₀ * y₀⁻¹ * τ₀) = 1 + vecMulVec (mat y₀ *ᵥ u₀ + u₀) fv := by
    rw [hmat_mul, hconj y₀ hy₀ τ₀ u₀ hτ₀, hτ₀, hMM (mat y₀ *ᵥ u₀) u₀ hu₀]
  have hc1 : y₀ * τ₀ * y₀⁻¹ * τ₀ ≠ 1 := by
    intro h
    have h3 : vecMulVec (mat y₀ *ᵥ u₀ + u₀) fv = 0 := by
      have h4 := congrArg mat h
      rw [hcmat, hmat_one] at h4
      exact add_left_cancel (h4.trans (add_zero 1).symm)
    rcases vecMulVec_eq_zero.mp h3 with h5 | h5
    · apply hcl
      rw [eq_neg_of_add_eq_zero_left h5, neg_eq_of_add_eq_zero_left (haa0 u₀)]
    · exact hfv0 h5
  have hcN : y₀ * τ₀ * y₀⁻¹ * τ₀ ∈ N :=
    ⟨hcY, mat y₀ *ᵥ u₀ + u₀, W.add_mem (hstab y₀ hy₀ u₀ hu₀) hu₀, hcmat⟩
  refine ⟨N, ?_, hNY, hsq, hNconj⟩
  exact (Subgroup.nontrivial_iff_ne_bot N).mp
    ((Subgroup.nontrivial_iff_exists_ne_one N).mpr ⟨_, hcN, hc1⟩)

end CFSG.Quasithin.H13.Ch4.CentK
