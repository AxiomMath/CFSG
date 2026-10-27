module

public import CFSG.Quasithin.MS93.ASIrr

public section

namespace CFSG.Quasithin.MS93.S32

open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped Matrix

variable {F : Type} [Field F]

@[expose] def dg (γ : GL (Fin 3) F) (w : (Fin 3 → F) × (Fin 3 → F)) :
    (Fin 3 → F) × (Fin 3 → F) :=
  ((γ : Matrix (Fin 3) (Fin 3) F) *ᵥ w.1, (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ w.2)

@[simp] theorem dg_fst (γ : GL (Fin 3) F) (w : (Fin 3 → F) × (Fin 3 → F)) :
    (dg γ w).1 = (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ w.1 :=
  rfl

@[simp] theorem dg_snd (γ : GL (Fin 3) F) (w : (Fin 3 → F) × (Fin 3 → F)) :
    (dg γ w).2 = (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ w.2 :=
  rfl

theorem dg_add (γ : GL (Fin 3) F) (w w' : (Fin 3 → F) × (Fin 3 → F)) :
    dg γ (w + w') = dg γ w + dg γ w' := by
  simp [dg, Matrix.mulVec_add]

theorem dg_smul (γ : GL (Fin 3) F) (c : F) (w : (Fin 3 → F) × (Fin 3 → F)) :
    dg γ (c • w) = c • dg γ w := by
  simp [dg, Matrix.mulVec_smul]

theorem mem_statedSL3_of_det {γ : GL (Fin 3) F} (h : (γ : Matrix (Fin 3) (Fin 3) F).det = 1) :
    γ ∈ StatedSL 3 F :=
  CFSG.Open.StatedAPI.mem_statedSL_of_det h

theorem exists_transvection_sl3 {i j : Fin 3} (hij : i ≠ j) (t : F) :
    ∃ γ ∈ StatedSL 3 F, ∀ v : Fin 3 → F,
      (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v + Pi.single i (t * v j) := by
  have hdet : (Matrix.transvection i j t).det = 1 := Matrix.det_transvection_of_ne i j hij t
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (by rw [hdet]; exact one_ne_zero), ?_, ?_⟩
  · apply mem_statedSL3_of_det
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hdet]
  · intro v
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.transvection, Matrix.add_mulVec,
      Matrix.one_mulVec, Matrix.single_mulVec]
    rfl

theorem eq_smul_of_commute_sl3 (φ : (Fin 3 → F) →+ (Fin 3 → F))
    (hφ : ∀ γ ∈ StatedSL 3 F, ∀ v,
      φ ((γ : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ φ v) :
    ∃ c : F, ∀ v, φ v = c • v := by
  classical
  have key : ∀ i j : Fin 3, i ≠ j → ∀ (t : F) (v : Fin 3 → F),
      φ (Pi.single i (t * v j)) = Pi.single i (t * φ v j) := by
    intro i j hij t v
    obtain ⟨γ, hγ, hγv⟩ := exists_transvection_sl3 hij t
    have h := hφ γ hγ v
    rw [hγv, hγv, map_add] at h
    exact add_left_cancel h
  set c := φ (Pi.single 0 1) 0 with hc
  have h0 : φ (Pi.single 0 1) = c • Pi.single 0 1 := by
    have hj : ∀ j : Fin 3, j ≠ 0 → φ (Pi.single 0 1) j = 0 := by
      intro j hj
      have h := key 0 j (Ne.symm hj) 1 (Pi.single 0 1)
      rw [Pi.single_eq_of_ne hj, mul_zero, Pi.single_zero, map_zero, one_mul] at h
      have h' := congrFun h 0
      simpa using h'.symm
    ext k
    fin_cases k
    · simp [hc]
    · simp [hj 1 (by decide)]
    · simp [hj 2 (by decide)]
  have hi : ∀ i : Fin 3, i ≠ 0 → ∀ t, φ (Pi.single i t) = c • Pi.single i t := by
    intro i hi t
    have h := key i 0 hi t (Pi.single 0 1)
    rw [Pi.single_eq_same, mul_one, h0] at h
    rw [h]
    ext k
    by_cases hk : k = i
    · subst hk
      simp [mul_comm]
    · simp [hk]
  have hall : ∀ i t, φ (Pi.single i t) = c • Pi.single i t := by
    intro i t
    by_cases hi0 : i = 0
    · subst hi0
      have h := key 0 1 (by decide) t (Pi.single 1 1)
      rw [Pi.single_eq_same, mul_one, hi 1 (by decide) 1] at h
      rw [h]
      ext k
      by_cases hk : k = 0
      · subst hk
        simp [mul_comm]
      · simp [hk]
    · exact hi i hi0 t
  refine ⟨c, fun v => ?_⟩
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  simp_rw [hall]
  rw [← Finset.smul_sum, Finset.univ_sum_single]

theorem addSubgroup_eq_bot_or_top_of_sl3 (S : AddSubgroup (Fin 3 → F))
    (hS : ∀ γ ∈ StatedSL 3 F, ∀ v ∈ S, (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  by_cases h : ∃ v ∈ S, v ≠ 0
  · right
    obtain ⟨v, hv, hv0⟩ := h
    rw [eq_top_iff]
    intro w _
    by_cases hw : w = 0
    · rw [hw]
      exact S.zero_mem
    · obtain ⟨γ, hγ⟩ := statedSL3_transitive v w hv0 hw
      rw [← hγ]
      exact hS γ γ.2 v hv
  · left
    rw [eq_bot_iff]
    intro v hv
    rw [AddSubgroup.mem_bot]
    by_contra hv0
    exact h ⟨v, hv, hv0⟩

theorem addSubgroup_cases_dg (U : AddSubgroup ((Fin 3 → F) × (Fin 3 → F)))
    (hU : ∀ γ ∈ StatedSL 3 F, ∀ w ∈ U, dg γ w ∈ U) :
    U = ⊥ ∨ U = ⊤ ∨ (∀ w, w ∈ U ↔ w.1 = 0) ∨ ∃ d : F, ∀ w, w ∈ U ↔ w.2 = d • w.1 := by
  classical
  let K : AddSubgroup (Fin 3 → F) := U.comap (AddMonoidHom.inr (Fin 3 → F) (Fin 3 → F))
  let Pr : AddSubgroup (Fin 3 → F) := U.map (AddMonoidHom.fst (Fin 3 → F) (Fin 3 → F))
  have hK : ∀ v, v ∈ K ↔ ((0 : Fin 3 → F), v) ∈ U := fun v => Iff.rfl
  have hP : ∀ v, v ∈ Pr ↔ ∃ w ∈ U, w.1 = v := fun v => by simp [Pr]
  have hKinv : ∀ γ ∈ StatedSL 3 F, ∀ v ∈ K, (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ K := by
    intro γ hγ v hv
    have h := hU γ hγ _ ((hK v).mp hv)
    rw [hK]
    simpa [dg] using h
  have hPinv : ∀ γ ∈ StatedSL 3 F, ∀ v ∈ Pr, (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ Pr := by
    intro γ hγ v hv
    obtain ⟨w, hw, rfl⟩ := (hP v).mp hv
    exact (hP _).mpr ⟨dg γ w, hU γ hγ w hw, rfl⟩
  rcases addSubgroup_eq_bot_or_top_of_sl3 K hKinv with hK0 | hK1 <;>
    rcases addSubgroup_eq_bot_or_top_of_sl3 Pr hPinv with hP0 | hP1
  ·
    left
    rw [eq_bot_iff]
    intro w hw
    have h1 : w.1 = 0 := by
      have : w.1 ∈ Pr := (hP _).mpr ⟨w, hw, rfl⟩
      rwa [hP0, AddSubgroup.mem_bot] at this
    have h2 : w.2 = 0 := by
      have : w.2 ∈ K := by
        rw [hK, ← h1]
        exact hw
      rwa [hK0, AddSubgroup.mem_bot] at this
    rw [AddSubgroup.mem_bot]
    exact Prod.ext h1 h2
  ·
    right; right; right
    have hex : ∀ v : Fin 3 → F, ∃ x, (v, x) ∈ U := by
      intro v
      obtain ⟨w, hw, hwv⟩ := (hP v).mp (hP1 ▸ AddSubgroup.mem_top v)
      exact ⟨w.2, by rw [← hwv]; exact hw⟩
    have huniq : ∀ v x y, (v, x) ∈ U → (v, y) ∈ U → x = y := by
      intro v x y hx hy
      have h : ((0 : Fin 3 → F), x - y) ∈ U := by
        have := U.sub_mem hx hy
        simpa using this
      have : x - y ∈ K := (hK _).mpr h
      rw [hK0, AddSubgroup.mem_bot, sub_eq_zero] at this
      exact this
    choose g hg using hex
    let φ : (Fin 3 → F) →+ (Fin 3 → F) := AddMonoidHom.mk' g (fun a b => by
      refine huniq (a + b) _ _ (hg (a + b)) ?_
      have := U.add_mem (hg a) (hg b)
      simpa using this)
    have hφ : ∀ γ ∈ StatedSL 3 F, ∀ v,
        φ ((γ : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ φ v := by
      intro γ hγ v
      refine huniq _ _ _ (hg _) ?_
      exact hU γ hγ _ (hg v)
    obtain ⟨d, hd⟩ := eq_smul_of_commute_sl3 φ hφ
    refine ⟨d, fun w => ⟨fun hw => ?_, fun hw => ?_⟩⟩
    · rw [← hd w.1]
      exact huniq w.1 _ _ hw (hg w.1)
    · have h : w = (w.1, g w.1) := by
        refine Prod.ext rfl ?_
        rw [hw]
        exact (hd w.1).symm
      rw [h]
      exact hg w.1
  ·
    right; right; left
    intro w
    refine ⟨fun hw => ?_, fun hw => ?_⟩
    · have : w.1 ∈ Pr := (hP _).mpr ⟨w, hw, rfl⟩
      rwa [hP0, AddSubgroup.mem_bot] at this
    · have h : w = (0, w.2) := Prod.ext hw rfl
      rw [h, ← hK, hK1]
      exact AddSubgroup.mem_top _
  ·
    right; left
    rw [eq_top_iff]
    intro w _
    obtain ⟨w', hw', hw'1⟩ := (hP w.1).mp (hP1 ▸ AddSubgroup.mem_top w.1)
    have h0 : ((0 : Fin 3 → F), w.2 - w'.2) ∈ U := by
      rw [← hK, hK1]
      exact AddSubgroup.mem_top _
    have h : w = w' + (0, w.2 - w'.2) := by
      refine Prod.ext ?_ ?_
      · simp [hw'1]
      · simp
    rw [h]
    exact U.add_mem hw' h0

@[expose] def blockSmul (a b c d : F) (w : (Fin 3 → F) × (Fin 3 → F)) :
    (Fin 3 → F) × (Fin 3 → F) :=
  (a • w.1 + b • w.2, c • w.1 + d • w.2)

theorem blockSmul_add (a b c d : F) (w w' : (Fin 3 → F) × (Fin 3 → F)) :
    blockSmul a b c d (w + w') = blockSmul a b c d w + blockSmul a b c d w' := by
  simp only [blockSmul, Prod.fst_add, Prod.snd_add, smul_add, Prod.mk_add_mk]
  congr 1 <;> abel

theorem blockSmul_smul (a b c d e : F) (w : (Fin 3 → F) × (Fin 3 → F)) :
    blockSmul a b c d (e • w) = e • blockSmul a b c d w := by
  ext <;> simp [blockSmul, smul_smul, mul_comm]

theorem blockSmul_dg (a b c d : F) (γ : GL (Fin 3) F) (w : (Fin 3 → F) × (Fin 3 → F)) :
    blockSmul a b c d (dg γ w) = dg γ (blockSmul a b c d w) := by
  simp [blockSmul, dg, Matrix.mulVec_add, Matrix.mulVec_smul]

theorem exists_blockSmul_of_commute
    (D : ((Fin 3 → F) × (Fin 3 → F)) →+ ((Fin 3 → F) × (Fin 3 → F)))
    (hD : ∀ γ ∈ StatedSL 3 F, ∀ w, D (dg γ w) = dg γ (D w)) :
    ∃ a b c d : F, ∀ w, D w = blockSmul a b c d w := by
  have hl : ∀ (γ : GL (Fin 3) F) v, dg γ (v, 0) = ((γ : Matrix (Fin 3) (Fin 3) F) *ᵥ v, 0) := by
    intro γ v
    simp [dg]
  have hr : ∀ (γ : GL (Fin 3) F) v, dg γ (0, v) = (0, (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
    intro γ v
    simp [dg]
  obtain ⟨a, ha⟩ := eq_smul_of_commute_sl3
    (AddMonoidHom.mk' (fun v => (D (v, 0)).1) (fun x y => by
      rw [← Prod.fst_add, ← map_add, Prod.mk_add_mk, add_zero])) (by
      intro γ hγ v
      change (D (_, 0)).1 = _ *ᵥ (D (v, 0)).1
      rw [← hl, hD γ hγ, dg_fst])
  obtain ⟨b, hb⟩ := eq_smul_of_commute_sl3
    (AddMonoidHom.mk' (fun v => (D (0, v)).1) (fun x y => by
      rw [← Prod.fst_add, ← map_add, Prod.mk_add_mk, add_zero])) (by
      intro γ hγ v
      change (D (0, _)).1 = _ *ᵥ (D (0, v)).1
      rw [← hr, hD γ hγ, dg_fst])
  obtain ⟨c, hc⟩ := eq_smul_of_commute_sl3
    (AddMonoidHom.mk' (fun v => (D (v, 0)).2) (fun x y => by
      rw [← Prod.snd_add, ← map_add, Prod.mk_add_mk, add_zero])) (by
      intro γ hγ v
      change (D (_, 0)).2 = _ *ᵥ (D (v, 0)).2
      rw [← hl, hD γ hγ, dg_snd])
  obtain ⟨d, hd⟩ := eq_smul_of_commute_sl3
    (AddMonoidHom.mk' (fun v => (D (0, v)).2) (fun x y => by
      rw [← Prod.snd_add, ← map_add, Prod.mk_add_mk, add_zero])) (by
      intro γ hγ v
      change (D (0, _)).2 = _ *ᵥ (D (0, v)).2
      rw [← hr, hD γ hγ, dg_snd])
  refine ⟨a, b, c, d, fun w => ?_⟩
  have hw : D w = D (w.1, 0) + D (0, w.2) := by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  rw [hw]
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_add]
    exact congrArg₂ (· + ·) (ha w.1) (hb w.2)
  · rw [Prod.snd_add]
    exact congrArg₂ (· + ·) (hc w.1) (hd w.2)

theorem exists_smul_fun_of_normalizes
    (τ : ((Fin 3 → F) × (Fin 3 → F)) ≃+ ((Fin 3 → F) × (Fin 3 → F)))
    (hτ : ∀ γ ∈ StatedSL 3 F, ∃ γ' ∈ StatedSL 3 F, ∀ w, τ (dg γ (τ.symm w)) = dg γ' w)
    (hτ' : ∀ γ ∈ StatedSL 3 F, ∃ γ' ∈ StatedSL 3 F, ∀ w, τ.symm (dg γ (τ w)) = dg γ' w) :
    ∃ σ : F → F, ∀ (c : F) w, τ (c • w) = σ c • τ w := by
  have hconj : ∀ a b c d : F, ∃ a' b' c' d' : F, ∀ w,
      τ.symm (blockSmul a b c d (τ w)) = blockSmul a' b' c' d' w := by
    intro a b c d
    refine exists_blockSmul_of_commute
      (AddMonoidHom.mk' (fun w => τ.symm (blockSmul a b c d (τ w))) (fun x y => by
        rw [map_add, blockSmul_add, map_add])) ?_
    intro γ hγ w
    obtain ⟨γ', -, h⟩ := hτ γ hγ
    have h1 : τ (dg γ w) = dg γ' (τ w) := by simpa using h (τ w)
    have h2 : τ.symm (dg γ' (blockSmul a b c d (τ w))) =
        dg γ (τ.symm (blockSmul a b c d (τ w))) := by
      rw [← h, AddEquiv.symm_apply_apply]
    change τ.symm (blockSmul a b c d (τ (dg γ w))) = dg γ (τ.symm (blockSmul a b c d (τ w)))
    rw [h1, blockSmul_dg, h2]
  have hscal : ∀ c : F, ∃ s : F, ∀ x, τ (c • τ.symm x) = s • x := by
    intro c
    let Dc : ((Fin 3 → F) × (Fin 3 → F)) →+ ((Fin 3 → F) × (Fin 3 → F)) :=
      AddMonoidHom.mk' (fun x => τ (c • τ.symm x)) (fun x y => by
        rw [map_add, smul_add, map_add])
    have hDc : ∀ γ ∈ StatedSL 3 F, ∀ x, Dc (dg γ x) = dg γ (Dc x) := by
      intro γ hγ x
      obtain ⟨γ', -, h⟩ := hτ' γ hγ
      have h1 : τ.symm (dg γ x) = dg γ' (τ.symm x) := by simpa using h (τ.symm x)
      have h2 : τ (dg γ' (c • τ.symm x)) = dg γ (τ (c • τ.symm x)) := by
        rw [← h, AddEquiv.apply_symm_apply]
      change τ (c • τ.symm (dg γ x)) = dg γ (τ (c • τ.symm x))
      rw [h1, ← dg_smul, h2]
    obtain ⟨a, b, c', d, hD⟩ := exists_blockSmul_of_commute Dc hDc
    have hcomm : ∀ (α β γ δ : F) x, blockSmul α β γ δ (Dc x) = Dc (blockSmul α β γ δ x) := by
      intro α β γ δ x
      obtain ⟨α', β', γ', δ', hE⟩ := hconj α β γ δ
      change blockSmul α β γ δ (τ (c • τ.symm x)) = τ (c • τ.symm (blockSmul α β γ δ x))
      have e1 : blockSmul α β γ δ (τ (c • τ.symm x)) =
          τ (blockSmul α' β' γ' δ' (c • τ.symm x)) := by
        rw [← hE, AddEquiv.apply_symm_apply]
      have e2 : τ.symm (blockSmul α β γ δ x) = blockSmul α' β' γ' δ' (τ.symm x) := by
        rw [← hE, AddEquiv.apply_symm_apply]
      rw [e1, blockSmul_smul, e2]
    have hb : ∀ v : Fin 3 → F, b • v = 0 := by
      intro v
      have h := hcomm 1 0 0 0 (0, v)
      rw [hD, hD] at h
      have h' := congrArg Prod.fst h
      simpa [blockSmul] using h'
    have hc' : ∀ v : Fin 3 → F, c' • v = 0 := by
      intro v
      have h := hcomm 1 0 0 0 (v, 0)
      rw [hD, hD] at h
      have h' := congrArg Prod.snd h
      simpa [blockSmul] using h'.symm
    have hda : ∀ v : Fin 3 → F, d • v = a • v := by
      intro v
      have h := hcomm 0 1 0 0 (0, v)
      rw [hD, hD] at h
      have h' := congrArg Prod.fst h
      simpa [blockSmul, hc'] using h'
    refine ⟨a, fun x => ?_⟩
    change Dc x = a • x
    rw [hD]
    refine Prod.ext ?_ ?_
    · simp [blockSmul, hb]
    · simp [blockSmul, hc', hda]
  choose σ hσ using hscal
  refine ⟨σ, fun c w => ?_⟩
  have h := hσ c (τ w)
  rwa [AddEquiv.symm_apply_apply] at h

theorem exists_ringEquiv_of_normalizes
    (τ : ((Fin 3 → F) × (Fin 3 → F)) ≃+ ((Fin 3 → F) × (Fin 3 → F)))
    (hτ : ∀ γ ∈ StatedSL 3 F, ∃ γ' ∈ StatedSL 3 F, ∀ w, τ (dg γ (τ.symm w)) = dg γ' w)
    (hτ' : ∀ γ ∈ StatedSL 3 F, ∃ γ' ∈ StatedSL 3 F, ∀ w, τ.symm (dg γ (τ w)) = dg γ' w) :
    ∃ σ : F ≃+* F, ∀ (c : F) w, τ (c • w) = σ c • τ w := by
  obtain ⟨σ, hσ⟩ := exists_smul_fun_of_normalizes τ hτ hτ'
  obtain ⟨σ', hσ'⟩ := exists_smul_fun_of_normalizes τ.symm hτ' hτ
  set x₀ : (Fin 3 → F) × (Fin 3 → F) := (fun _ => 1, 0) with hx₀
  have huniq : ∀ a b : F, a • x₀ = b • x₀ → a = b := by
    intro a b h
    have h' := congrArg (fun w : (Fin 3 → F) × (Fin 3 → F) => w.1 0) h
    simpa [hx₀] using h'
  have hσx : ∀ c, σ c • x₀ = τ (c • τ.symm x₀) := by
    intro c
    rw [hσ, AddEquiv.apply_symm_apply]
  have hadd : ∀ a b, σ (a + b) = σ a + σ b := by
    intro a b
    apply huniq
    rw [hσx, add_smul, map_add, ← hσx, ← hσx, add_smul]
  have hmul : ∀ a b, σ (a * b) = σ a * σ b := by
    intro a b
    apply huniq
    rw [hσx, mul_smul, hσ, ← hσx, mul_smul]
  have hone : σ 1 = 1 := by
    apply huniq
    rw [hσx, one_smul, AddEquiv.apply_symm_apply, one_smul]
  have hzero : σ 0 = 0 := by
    apply huniq
    rw [hσx, zero_smul, map_zero, zero_smul]
  have hinv : ∀ c, σ (σ' c) = c := by
    intro c
    apply huniq
    have h := hσ' c x₀
    rw [hσx, ← h, AddEquiv.apply_symm_apply]
  let σr : F →+* F :=
    { toFun := σ
      map_one' := hone
      map_mul' := hmul
      map_zero' := hzero
      map_add' := hadd }
  refine ⟨RingEquiv.ofBijective σr ⟨σr.injective, fun c => ⟨σ' c, hinv c⟩⟩, fun c w => ?_⟩
  exact hσ c w

theorem exists_hom_ringAut_of_semilinear {W : Type} [AddCommGroup W] [Module F W] [Nontrivial W]
    {P : Type} [Group P] (act : P → W →+ W)
    (hmul : ∀ (s t : P) (w : W), act (s * t) w = act s (act t w))
    (hinj : ∀ t, Function.Injective (act t))
    (hsemi : ∀ t, ∃ σ : F ≃+* F, ∀ (c : F) (w : W), act t (c • w) = σ c • act t w) :
    ∃ σ : P →* RingAut F, ∀ (t : P) (c : F) (w : W), act t (c • w) = σ t c • act t w := by
  choose σ hσ using hsemi
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : W)
  have hne : ∀ t, act t w₀ ≠ 0 := fun t h => hw₀ (hinj t (by rw [h, map_zero]))
  refine ⟨MonoidHom.mk' σ (fun s t => ?_), hσ⟩
  apply RingEquiv.ext
  intro c
  apply smul_left_injective F (hne (s * t))
  change σ (s * t) c • act (s * t) w₀ = σ s (σ t c) • act (s * t) w₀
  rw [← hσ, hmul, hmul, hσ, hσ]

theorem exists_fixed_not_mem {W : Type} [AddCommGroup W] [Module F W]
    {P : Type} [Group P] [Finite P] (act : P → W →+ W)
    (hmul : ∀ (s t : P) (w : W), act (s * t) w = act s (act t w)) (σ : P →* RingAut F)
    (hsemi : ∀ (t : P) (c : F) (w : W), act t (c • w) = σ t c • act t w)
    (V : Submodule F W) (hV : ∀ t, ∀ v ∈ V, act t v ∈ V)
    (hker : ∀ t, σ t = 1 → ∀ v ∈ V, act t v = v)
    (S : Submodule F W) (hVS : ¬ V ≤ S) :
    ∃ v ∈ V, (∀ t, act t v = v) ∧ v ∉ S := by
  classical
  obtain ⟨v₀, hv₀V, hv₀S⟩ : ∃ v ∈ V, v ∉ S := by
    by_contra h
    exact hVS fun v hv => by_contra fun hvS => h ⟨v, hv, hvS⟩
  by_contra hcon'
  have hcon : ∀ v ∈ V, (∀ t, act t v = v) → v ∈ S := fun v hv hfix =>
    by_contra fun hvS => hcon' ⟨v, hv, hfix, hvS⟩
  have : Finite ↥σ.range := Finite.of_surjective _ σ.rangeRestrict_surjective
  have : Fintype ↥σ.range := Fintype.ofFinite _
  have hsec : ∀ g : ↥σ.range, ∃ t : P, σ t = g := fun g => g.2
  choose s hs using hsec
  set Tr : W → W := fun v => ∑ g : ↥σ.range, act (s g) v with hTr
  have hTrV : ∀ v ∈ V, Tr v ∈ V := fun v hv => V.sum_mem (fun g _ => hV _ v hv)
  have hTrfix : ∀ v ∈ V, ∀ u : P, act u (Tr v) = Tr v := by
    intro v hv u
    simp only [hTr, map_sum]
    have key : ∀ g : ↥σ.range,
        act u (act (s g) v) = act (s (⟨σ u, u, rfl⟩ * g)) v := by
      intro g
      rw [← hmul]
      set t' := s (⟨σ u, u, rfl⟩ * g) with ht'
      have hk : σ (t'⁻¹ * (u * s g)) = 1 := by
        rw [map_mul, map_inv, map_mul, ht', hs, hs, Subgroup.coe_mul]
        group
      have h : u * s g = t' * (t'⁻¹ * (u * s g)) := by group
      rw [h, hmul, hker _ hk v hv]
    rw [Finset.sum_congr rfl (fun g _ => key g)]
    exact Fintype.sum_equiv (Equiv.mulLeft _) _ _ (fun g => rfl)
  obtain ⟨f, hf0, hfS⟩ := Submodule.exists_le_ker_of_notMem hv₀S
  have hrel : ∀ c : F, ∑ g : ↥σ.range, f (act (s g) v₀) * (g : RingAut F) c = 0 := by
    intro c
    have hmem : Tr (c • v₀) ∈ S :=
      hcon _ (hTrV _ (V.smul_mem c hv₀V)) (hTrfix _ (V.smul_mem c hv₀V))
    have h0 : f (Tr (c • v₀)) = 0 := hfS hmem
    rw [← h0]
    simp only [hTr, map_sum, hsemi, map_smul, smul_eq_mul, hs]
    exact Finset.sum_congr rfl fun g _ => mul_comm _ _
  have hli : LinearIndependent F (fun g : ↥σ.range => ((g : RingAut F) : F → F)) := by
    have h := linearIndependent_monoidHom F F
    have hinj : Function.Injective
        (fun g : ↥σ.range => ((g : RingAut F) : F ≃+* F).toMonoidHom) := by
      intro g g' hgg'
      apply Subtype.ext
      apply RingEquiv.ext
      intro x
      exact DFunLike.congr_fun hgg' x
    exact h.comp _ hinj
  rw [Fintype.linearIndependent_iff] at hli
  have hcoef := hli (fun g => f (act (s g) v₀)) (by
    funext c
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact hrel c) 1
  have h1 : act (s 1) v₀ = v₀ := hker _ (by rw [hs]; rfl) v₀ hv₀V
  rw [h1] at hcoef
  exact hf0 hcoef

theorem exists_sl3_of_embed [CharP F 2]
    (τ : ((Fin 3 → F) × (Fin 3 → F)) ≃+ ((Fin 3 → F) × (Fin 3 → F)))
    (hlin : ∀ (c : F) w, τ (c • w) = c • τ w) {e : ℕ} (hτe : ∀ w, (⇑τ)^[2 ^ e] w = w)
    (ι : (Fin 3 → F) → (Fin 3 → F) × (Fin 3 → F)) (hιinj : Function.Injective ι)
    (hιadd : ∀ x y, ι (x + y) = ι x + ι y) (hιsmul : ∀ (c : F) x, ι (c • x) = c • ι x)
    (hιdg : ∀ (γ : GL (Fin 3) F) x, ι ((γ : Matrix (Fin 3) (Fin 3) F) *ᵥ x) = dg γ (ι x))
    (hτι : ∀ x, ∃ y, τ (ι x) = ι y) :
    ∃ γ ∈ StatedSL 3 F, γ ^ (2 ^ e) = 1 ∧ ∀ x, τ (ι x) = dg γ (ι x) := by
  choose A hA using hτι
  have hAadd : ∀ x y, A (x + y) = A x + A y := by
    intro x y
    apply hιinj
    rw [← hA, hιadd, map_add, hA, hA, hιadd]
  have hAsmul : ∀ (c : F) x, A (c • x) = c • A x := by
    intro c x
    apply hιinj
    rw [← hA, hιsmul, hlin, hA, hιsmul]
  let Al : (Fin 3 → F) →ₗ[F] (Fin 3 → F) :=
    { toFun := A
      map_add' := hAadd
      map_smul' := hAsmul }
  set M : Matrix (Fin 3) (Fin 3) F := LinearMap.toMatrix' Al
  have hMv : ∀ x, M *ᵥ x = A x := fun x => LinearMap.toMatrix'_mulVec Al x
  have hiter : ∀ (k : ℕ) x, (⇑τ)^[k] (ι x) = ι (A^[k] x) := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply, hA, ih, Function.iterate_succ_apply]
  have hAe : ∀ x, A^[2 ^ e] x = x := by
    intro x
    apply hιinj
    rw [← hiter, hτe]
  have hpow : ∀ (k : ℕ) x, (M ^ k) *ᵥ x = A^[k] x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, ← Matrix.mulVec_mulVec, hMv, ih, Function.iterate_succ_apply]
  have hMe : M ^ (2 ^ e) = 1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hpow, hAe, Matrix.one_mulVec]
  have hdet : M.det = 1 := by
    have h1 : M.det ^ (2 ^ e) = 1 := by
      rw [← Matrix.det_pow, hMe, Matrix.det_one]
    have h2 : (M.det - 1) ^ (2 ^ e) = 0 := by
      rw [sub_pow_char_pow, h1, one_pow, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero e two_ne_zero) |>.mp h2)
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero), ?_, ?_, ?_⟩
  · apply mem_statedSL3_of_det
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hdet]
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hMe]
    rfl
  · intro x
    rw [← hιdg, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hMv, hA]

theorem exists_sl3_of_linear [CharP F 2]
    (τ : ((Fin 3 → F) × (Fin 3 → F)) ≃+ ((Fin 3 → F) × (Fin 3 → F)))
    (hlin : ∀ (c : F) w, τ (c • w) = c • τ w) {e : ℕ} (hτe : ∀ w, (⇑τ)^[2 ^ e] w = w)
    (U : AddSubgroup ((Fin 3 → F) × (Fin 3 → F))) (hτU : ∀ w ∈ U, τ w ∈ U)
    (hUform : (∀ w, w ∈ U ↔ w.1 = 0) ∨ ∃ d : F, ∀ w, w ∈ U ↔ w.2 = d • w.1) :
    ∃ γ ∈ StatedSL 3 F, γ ^ (2 ^ e) = 1 ∧ ∀ w ∈ U, τ w = dg γ w := by
  rcases hUform with hU | ⟨d, hU⟩
  · obtain ⟨γ, hγ, hγe, hγτ⟩ := exists_sl3_of_embed τ hlin hτe (fun x => (0, x))
      (fun x y h => congrArg Prod.snd h) (fun x y => by simp) (fun c x => by simp)
      (fun γ x => by simp [dg]) (fun x => by
        have h := (hU _).mp (hτU _ ((hU (0, x)).mpr rfl))
        exact ⟨(τ (0, x)).2, Prod.ext h rfl⟩)
    refine ⟨γ, hγ, hγe, fun w hw => ?_⟩
    have h : w = (0, w.2) := Prod.ext ((hU w).mp hw) rfl
    rw [h]
    exact hγτ w.2
  · obtain ⟨γ, hγ, hγe, hγτ⟩ := exists_sl3_of_embed τ hlin hτe (fun x => (x, d • x))
      (fun x y h => congrArg Prod.fst h) (fun x y => by simp [smul_add])
      (fun c x => by simp [smul_comm c d]) (fun γ x => by simp [dg, Matrix.mulVec_smul])
      (fun x => by
        have h := (hU _).mp (hτU _ ((hU (x, d • x)).mpr rfl))
        exact ⟨(τ (x, d • x)).1, Prod.ext rfl h⟩)
    refine ⟨γ, hγ, hγe, fun w hw => ?_⟩
    have h : w = (w.1, d • w.1) := Prod.ext rfl ((hU w).mp hw)
    rw [h]
    exact hγτ w.1

end CFSG.Quasithin.MS93.S32
