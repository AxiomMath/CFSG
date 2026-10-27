module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFactsH
import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFactsJ

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

@[expose] noncomputable def spUFixRootU (hF : Nat.card F = (2 ^ n) ^ 2) (m : ℕ)
    (e : Fin m → F) : Subgroup (StatedProj (StatedSU m (2 ^ n) F)) :=
  Subgroup.closure {x | ∃ s : F, s + unitaryInvolution F 2 n s = 0 ∧ x = kFactsSuProjTv hF m e s}

private theorem spUFixRootU_map_conj (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ}
    (t : ↥(SUid (unitaryInvolution F 2 n) m)) {e : Fin m → F}
    (he : herm (unitaryInvolution F 2 n) e e = 0) :
    (spUFixRootU hF m e).map (MulAut.conj (kFactsSuProj hF m t)).toMonoidHom =
      spUFixRootU hF m (t • e) := by
  rw [spUFixRootU, MonoidHom.map_closure, spUFixRootU]
  congr 1
  ext y
  constructor
  · rintro ⟨z, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨s, hs, ?_⟩
    change MulAut.conj (kFactsSuProj hF m t) (kFactsSuProjTv hF m e s) =
      kFactsSuProjTv hF m (t • e) s
    rw [MulAut.conj_apply, kFacts_suProj_conj_suProjTv hF t he hs]
  · rintro ⟨s, hs, rfl⟩
    refine ⟨kFactsSuProjTv hF m e s, ⟨s, hs, rfl⟩, ?_⟩
    change MulAut.conj (kFactsSuProj hF m t) (kFactsSuProjTv hF m e s) =
      kFactsSuProjTv hF m (t • e) s
    rw [MulAut.conj_apply, kFacts_suProj_conj_suProjTv hF t he hs]

theorem mem_spUFixRootU (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ} {e : Fin m → F}
    (he : herm (unitaryInvolution F 2 n) e e = 0) {x : StatedProj (StatedSU m (2 ^ n) F)} :
    x ∈ spUFixRootU hF m e ↔
      ∃ s : F, s + unitaryInvolution F 2 n s = 0 ∧ x = kFactsSuProjTv hF m e s := by
  have hσ := isUnitaryInvolution_unitaryInvolution hF
  have key : ∀ x : StatedProj (StatedSU m (2 ^ n) F), x ∈ spUFixRootU hF m e →
      ∃ s : F, s + unitaryInvolution F 2 n s = 0 ∧ x = kFactsSuProjTv hF m e s := by
    intro x hx
    refine Subgroup.closure_induction
      (p := fun x _ => ∃ s : F, s + unitaryInvolution F 2 n s = 0 ∧
        x = kFactsSuProjTv hF m e s) ?_ ?_ ?_ ?_ hx
    · rintro x ⟨s, hs, rfl⟩
      exact ⟨s, hs, rfl⟩
    · exact ⟨0, by simp, by
        unfold kFactsSuProjTv
        rw [kFacts_suTv_zero_param hF he, map_one]⟩
    · rintro x y hx hy ⟨s, hs, rfl⟩ ⟨s', hs', rfl⟩
      refine ⟨s + s', ?_, ?_⟩
      · rw [map_add]
        linear_combination hs + hs'
      · unfold kFactsSuProjTv
        rw [← map_mul, suTv_mul_suTv hσ he hs hs']
    · rintro x hx ⟨s, hs, rfl⟩
      refine ⟨s, hs, ?_⟩
      have hsq : kFactsSuProjTv hF m e s * kFactsSuProjTv hF m e s = 1 := by
        unfold kFactsSuProjTv
        rw [← map_mul, suTv_mul_suTv hσ he hs hs, CharTwo.add_self_eq_zero s,
          kFacts_suTv_zero_param hF he, map_one]
      exact inv_eq_of_mul_eq_one_left hsq
  constructor
  · exact key x
  · rintro ⟨s, hs, rfl⟩
    exact Subgroup.subset_closure ⟨s, hs, rfl⟩

theorem spUFixRootU_smul (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ} {c : F} (hc : c ≠ 0)
    {e : Fin m → F} (he : herm (unitaryInvolution F 2 n) e e = 0) :
    spUFixRootU hF m (c • e) = spUFixRootU hF m e := by
  set σ := unitaryInvolution F 2 n with hσdef
  have hN0 : σ c * c ≠ 0 := mul_ne_zero ((map_ne_zero_iff σ σ.injective).mpr hc) hc
  have hNfix : σ (σ c * c) = σ c * c := by rw [map_mul, hσdef, unitaryInvolution_involutive hF,
    mul_comm]
  apply le_antisymm
  · rw [spUFixRootU, Subgroup.closure_le]
    rintro y ⟨s, hs, rfl⟩
    refine Subgroup.subset_closure ⟨σ c * c * s, ?_, kFacts_suProjTv_smul_vec hF he hs c⟩
    rw [map_mul, hNfix]
    have h : σ c * c * s + σ c * c * σ s = σ c * c * (s + σ s) := by ring
    rw [h, hs, mul_zero]
  · rw [spUFixRootU, Subgroup.closure_le]
    rintro y ⟨t, ht, rfl⟩
    have htz : (σ c * c)⁻¹ * t + σ ((σ c * c)⁻¹ * t) = 0 := by
      rw [map_mul, map_inv₀, hNfix]
      have h : (σ c * c)⁻¹ * t + (σ c * c)⁻¹ * σ t = (σ c * c)⁻¹ * (t + σ t) := by ring
      rw [h, ht, mul_zero]
    refine Subgroup.subset_closure ⟨(σ c * c)⁻¹ * t, htz, ?_⟩
    rw [kFacts_suProjTv_smul_vec hF he htz c]
    congr 1
    rw [← mul_assoc, mul_inv_cancel₀ hN0, one_mul]

theorem exists_smul_of_spUFixRootU_eq (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ}
    {e w : Fin m → F} (he0 : e ≠ 0) (hw0 : w ≠ 0) (he : herm (unitaryInvolution F 2 n) e e = 0)
    (hw : herm (unitaryInvolution F 2 n) w w = 0) (h : spUFixRootU hF m e = spUFixRootU hF m w) :
    ∃ c : F, w = c • e := by
  have hσ := isUnitaryInvolution_unitaryInvolution hF
  by_contra hcon
  have hne' : ∀ c : F, w ≠ c • e := fun c hc => hcon ⟨c, hc⟩
  have h1 : (1 : F) + unitaryInvolution F 2 n 1 = 0 := by
    rw [map_one]; exact CharTwo.add_self_eq_zero 1
  have hmem : kFactsSuProjTv hF m w 1 ∈ spUFixRootU hF m e := by
    rw [h]
    exact Subgroup.subset_closure ⟨1, h1, rfl⟩
  obtain ⟨s, hs, heq⟩ := (mem_spUFixRootU hF he).mp hmem
  unfold kFactsSuProjTv at heq
  obtain ⟨u, hu⟩ := (kFacts_suProj_eq_iff hF (suTv hσ w 1) (suTv hσ e s)).mp heq
  have hact : ∀ v : Fin m → F, suTv hσ e s • v = (u : F) • (suTv hσ w 1 • v) := by
    intro v
    rw [smul_def, smul_def, hu, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact Matrix.mulVec_smul _ _ _
  have hW : suTv hσ w 1 • e = e + herm (unitaryInvolution F 2 n) w e • w := by
    rw [suTv_smul hσ hw h1, one_mul]
  have hE : suTv hσ e s • e = e := by
    rw [suTv_smul hσ he hs, he, mul_zero, zero_smul, add_zero]
  have hu1 : (u : F) = 1 := by
    by_contra hu_ne
    have h1u : (1 : F) - (u : F) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu_ne)
    have hKey : (1 - (u : F)) • e =
        ((u : F) * herm (unitaryInvolution F 2 n) w e) • w := by
      have h2 := hact e
      rw [hE, hW, smul_add, smul_smul] at h2
      rw [sub_smul, one_smul]
      nth_rewrite 1 [h2]
      module
    set d : F := (1 - (u : F))⁻¹ * ((u : F) * herm (unitaryInvolution F 2 n) w e) with hd
    have he_dw : e = d • w := by
      have hcong := congrArg (fun z : Fin m → F => (1 - (u : F))⁻¹ • z) hKey
      rw [smul_smul, inv_mul_cancel₀ h1u, one_smul, smul_smul, ← hd] at hcong
      exact hcong
    have hd0 : d ≠ 0 := by
      intro hdzero
      exact he0 (by rw [he_dw, hdzero, zero_smul])
    exact hne' d⁻¹ (by rw [he_dw, smul_smul, inv_mul_cancel₀ hd0, one_smul])
  obtain ⟨x, hx⟩ := exists_herm_eq_one (unitaryInvolution F 2 n) hw0
  have hfin : x + (s * herm (unitaryInvolution F 2 n) e x) • e = x + w := by
    have h2 := hact x
    rw [hu1, one_smul, suTv_smul hσ he hs, suTv_smul hσ hw h1, hx] at h2
    simpa using h2
  exact hne' (s * herm (unitaryInvolution F 2 n) e x) (add_left_cancel hfin).symm

theorem mul_self_of_mem_spUFixRootU (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ} {e : Fin m → F}
    (he : herm (unitaryInvolution F 2 n) e e = 0) {x : StatedProj (StatedSU m (2 ^ n) F)}
    (hx : x ∈ spUFixRootU hF m e) : x * x = 1 := by
  have hσ := isUnitaryInvolution_unitaryInvolution hF
  obtain ⟨s, hs, rfl⟩ := (mem_spUFixRootU hF he).mp hx
  unfold kFactsSuProjTv
  rw [← map_mul, suTv_mul_suTv hσ he hs hs, CharTwo.add_self_eq_zero s,
    kFacts_suTv_zero_param hF he, map_one]

theorem commute_of_mem_spUFixRootU (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ} {e w : Fin m → F}
    (he : herm (unitaryInvolution F 2 n) e e = 0) (hw : herm (unitaryInvolution F 2 n) w w = 0)
    (hew : herm (unitaryInvolution F 2 n) e w = 0) {x y : StatedProj (StatedSU m (2 ^ n) F)}
    (hx : x ∈ spUFixRootU hF m e) (hy : y ∈ spUFixRootU hF m w) : x * y = y * x := by
  obtain ⟨s, hs, rfl⟩ := (mem_spUFixRootU hF he).mp hx
  obtain ⟨t, ht, rfl⟩ := (mem_spUFixRootU hF hw).mp hy
  exact kFacts_suProjTv_comm_of_herm_eq_zero hF he hw hew hs ht

theorem exists_linearMap_map_conj_spUFixRootU (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ}
    (x : StatedProj (StatedSU m (2 ^ n) F)) :
    ∃ M : (Fin m → F) →ₗ[F] (Fin m → F), Function.Injective M ∧
      (∀ v w, herm (unitaryInvolution F 2 n) (M v) (M w) = herm (unitaryInvolution F 2 n) v w) ∧
      (∀ e, herm (unitaryInvolution F 2 n) e e = 0 →
        (spUFixRootU hF m e).map (MulAut.conj x).toMonoidHom = spUFixRootU hF m (M e)) ∧
      (x * x = 1 → ∃ c : F, ∀ v, M (M v) = c • v) := by
  obtain ⟨t, rfl⟩ := kFacts_suProj_surjective hF m x
  refine ⟨Matrix.mulVecLin (((t : GL (Fin m) F)) : Matrix (Fin m) (Fin m) F), ?_, ?_, ?_, ?_⟩
  · intro v w hvw
    have h2 : t • v = t • w := by
      simpa only [Matrix.mulVecLin_apply, smul_def] using hvw
    calc v = t⁻¹ • (t • v) := (inv_smul_smul t v).symm
      _ = t⁻¹ • (t • w) := by rw [h2]
      _ = w := inv_smul_smul t w
  · intro v w
    simpa only [Matrix.mulVecLin_apply, smul_def] using
      herm_smul_smul (unitaryInvolution F 2 n) t v w
  · intro e he
    show (spUFixRootU hF m e).map (MulAut.conj (kFactsSuProj hF m t)).toMonoidHom =
      spUFixRootU hF m (Matrix.mulVecLin (((t : GL (Fin m) F)) : Matrix (Fin m) (Fin m) F) e)
    rw [show Matrix.mulVecLin (((t : GL (Fin m) F)) : Matrix (Fin m) (Fin m) F) e = t • e from
      (smul_def (unitaryInvolution F 2 n) t e).symm]
    exact spUFixRootU_map_conj hF t he
  · intro hxx
    have hproj : kFactsSuProj hF m (t * t) = kFactsSuProj hF m 1 := by
      rw [map_mul, hxx, map_one]
    obtain ⟨u, hu⟩ :=
      (kFacts_suProj_eq_iff hF (1 : ↥(SUid (unitaryInvolution F 2 n) m)) (t * t)).mp
        hproj.symm
    refine ⟨(u : F), ?_⟩
    intro v
    have hmat : (((t : GL (Fin m) F)) : Matrix (Fin m) (Fin m) F) *
        (((t : GL (Fin m) F)) : Matrix (Fin m) (Fin m) F) =
        (((t * t : ↥(SUid (unitaryInvolution F 2 n) m)) : GL (Fin m) F) :
          Matrix (Fin m) (Fin m) F) := rfl
    have hMM : Matrix.mulVecLin (((t : GL (Fin m) F)) : Matrix (Fin m) (Fin m) F)
        (Matrix.mulVecLin (((t : GL (Fin m) F)) : Matrix (Fin m) (Fin m) F) v) =
        (t * t) • v := by
      rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hmat, smul_def]
    rw [hMM, smul_def, hu]
    rw [show (((1 : ↥(SUid (unitaryInvolution F 2 n) m)) : GL (Fin m) F) :
      Matrix (Fin m) (Fin m) F) = 1 from rfl]
    rw [Matrix.one_mul, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem exists_spUFixRootU_eq_map (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ} (hm : 3 ≤ m)
    {a v : Fin m → F} (ha0 : a ≠ 0) (hv0 : v ≠ 0) (ha : herm (unitaryInvolution F 2 n) a a = 0)
    (hv : herm (unitaryInvolution F 2 n) v v = 0) :
    ∃ x : StatedProj (StatedSU m (2 ^ n) F),
      spUFixRootU hF m v = (spUFixRootU hF m a).map (MulAut.conj x).toMonoidHom := by
  obtain ⟨t, _, hta⟩ := exists_mem_T_smul_eq_of_iso
    (isUnitaryInvolution_unitaryInvolution hF) hm ha0 ha hv0 hv
  refine ⟨kFactsSuProj hF m t, ?_⟩
  rw [← hta]
  exact (spUFixRootU_map_conj hF t ha).symm

theorem spUFix_exists_herm_eq_zero_not_smul (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ}
    (hm : 4 ≤ m) {a : Fin m → F} (ha0 : a ≠ 0) (ha : herm (unitaryInvolution F 2 n) a a = 0) :
    ∃ v : Fin m → F, herm (unitaryInvolution F 2 n) v v = 0 ∧
      herm (unitaryInvolution F 2 n) a v = 0 ∧ ∀ c : F, v ≠ c • a := by
  have hσ := isUnitaryInvolution_unitaryInvolution hF
  have hm3 : 3 ≤ m := by omega
  set i0 : Fin m := ⟨0, by omega⟩ with hi0
  set i1 : Fin m := ⟨1, by omega⟩ with hi1
  set i2 : Fin m := ⟨2, by omega⟩ with hi2
  set i3 : Fin m := ⟨3, by omega⟩ with hi3
  have h01 : i0 ≠ i1 := by
    intro hh
    have hv := congrArg Fin.val hh
    rw [hi0, hi1] at hv
    simp only [Fin.val_mk] at hv
    omega
  have h02 : i0 ≠ i2 := by
    intro hh
    have hv := congrArg Fin.val hh
    rw [hi0, hi2] at hv
    simp only [Fin.val_mk] at hv
    omega
  have h03 : i0 ≠ i3 := by
    intro hh
    have hv := congrArg Fin.val hh
    rw [hi0, hi3] at hv
    simp only [Fin.val_mk] at hv
    omega
  have h12 : i1 ≠ i2 := by
    intro hh
    have hv := congrArg Fin.val hh
    rw [hi1, hi2] at hv
    simp only [Fin.val_mk] at hv
    omega
  have h13 : i1 ≠ i3 := by
    intro hh
    have hv := congrArg Fin.val hh
    rw [hi1, hi3] at hv
    simp only [Fin.val_mk] at hv
    omega
  have h23 : i2 ≠ i3 := by
    intro hh
    have hv := congrArg Fin.val hh
    rw [hi2, hi3] at hv
    simp only [Fin.val_mk] at hv
    omega
  set a₀ : Fin m → F := Pi.single i0 1 + Pi.single i1 1 with ha₀def
  set v₀ : Fin m → F := Pi.single i2 1 + Pi.single i3 1 with hv₀def
  have ha₀ : herm (unitaryInvolution F 2 n) a₀ a₀ = 0 := by
    rw [ha₀def, herm_single_add_single h01 1, map_one, one_mul]
    exact CharTwo.add_self_eq_zero 1
  have hv₀ : herm (unitaryInvolution F 2 n) v₀ v₀ = 0 := by
    rw [hv₀def, herm_single_add_single h23 1, map_one, one_mul]
    exact CharTwo.add_self_eq_zero 1
  have ha₀i2 : a₀ i2 = 0 := by
    rw [ha₀def]
    simp [Pi.single_eq_of_ne' h02, Pi.single_eq_of_ne' h12]
  have ha₀i3 : a₀ i3 = 0 := by
    rw [ha₀def]
    simp [Pi.single_eq_of_ne' h03, Pi.single_eq_of_ne' h13]
  have ha₀v₀ : herm (unitaryInvolution F 2 n) a₀ v₀ = 0 := by
    rw [hv₀def, herm_add_right, herm_single_right, herm_single_right]
    simp [ha₀i2, ha₀i3]
  have ha₀0 : a₀ ≠ 0 := by
    intro hh
    have h1 : a₀ i0 = 1 := by
      rw [ha₀def]
      simp [Pi.single_eq_of_ne' (Ne.symm h01)]
    rw [hh] at h1
    simpa using h1
  obtain ⟨t, _, hta⟩ := exists_mem_T_smul_eq_of_iso hσ hm3 ha₀0 ha₀ ha0 ha
  refine ⟨t • v₀, ?_, ?_, ?_⟩
  · rw [herm_smul_smul (unitaryInvolution F 2 n) t v₀ v₀, hv₀]
  · rw [← hta, herm_smul_smul (unitaryInvolution F 2 n) t a₀ v₀, ha₀v₀]
  · intro c hc
    have hv : v₀ = c • a₀ := by
      have hh := congrArg (fun z : Fin m → F => t⁻¹ • z) hc
      rw [inv_smul_smul, smul_comm, ← hta, inv_smul_smul] at hh
      exact hh
    have h1 : v₀ i2 = 1 := by
      rw [hv₀def]
      simp [Pi.single_eq_of_ne' (Ne.symm h23)]
    have h2 : (c • a₀) i2 = 0 := by
      rw [Pi.smul_apply, ha₀i2, smul_zero]
    have hv1 : (c • a₀) i2 = 1 := by rw [← hv, h1]
    rw [h2] at hv1
    exact one_ne_zero hv1.symm

end CFSG.LocalAnalysis.WeakClosure81

end
