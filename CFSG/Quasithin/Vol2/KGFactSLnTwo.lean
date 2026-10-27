module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration

public section

namespace CFSG.Quasithin.SLnTwo

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBGraphForm

variable {n : ℕ}

theorem zmod_two_cases (r : ZMod 2) : r = 0 ∨ r = 1 := by
  revert r
  decide

theorem mulVec_transvection {i j : Fin n} (hij : i ≠ j) (v : Fin n → ZMod 2) :
    ((SpecialLinearGroup.transvection hij (1 : ZMod 2) : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v = v + Pi.single i (v j) := by
  rw [SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.one_mulVec]
  congr 1
  ext k
  by_cases hk : k = i
  · subst hk
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
  · simp [Matrix.mulVec, dotProduct, Ne.symm hk, hk]

theorem transvection_mem_unitriangular {i j : Fin n} (hij : i < j) :
    SpecialLinearGroup.transvection (ne_of_lt hij) (1 : ZMod 2) ∈ unitriangular n (ZMod 2) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hab),
      Matrix.single_apply]
    have : ¬ (i = a ∧ j = b) := by
      rintro ⟨rfl, rfl⟩
      exact absurd (lt_trans hab hij) (lt_irrefl _)
    simp [this]
  · rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply_eq,
      Matrix.single_apply]
    have : ¬ (i = a ∧ j = a) := by
      rintro ⟨rfl, h⟩
      exact absurd h (ne_of_gt hij)
    simp [this]

theorem fix_unitriangular {v : Fin n → ZMod 2}
    (hv : ∀ u ∈ unitriangular n (ZMod 2), (u : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v = v)
    (j : Fin n) (hj : (j : ℕ) ≠ 0) : v j = 0 := by
  have hi : (⟨0, by omega⟩ : Fin n) < j := by
    rw [Fin.lt_def]
    simp only
    omega
  have h := congrFun (hv _ (transvection_mem_unitriangular hi)) ⟨0, by omega⟩
  rw [mulVec_transvection] at h
  simpa using h

theorem eq_single_of_fix_unitriangular (hn : 1 ≤ n) {v : Fin n → ZMod 2}
    (hv : ∀ u ∈ unitriangular n (ZMod 2), (u : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v = v)
    (hv0 : v ≠ 0) : v = Pi.single ⟨0, by omega⟩ 1 := by
  have h0 : v ⟨0, by omega⟩ = 1 := by
    rcases zmod_two_cases (v ⟨0, by omega⟩) with h | h
    · exfalso
      apply hv0
      ext j
      by_cases hj : (j : ℕ) = 0
      · have : j = ⟨0, by omega⟩ := Fin.ext hj
        rw [this, h]
        rfl
      · exact fix_unitriangular hv j hj
    · exact h
  ext j
  by_cases hj : (j : ℕ) = 0
  · have : j = ⟨0, by omega⟩ := Fin.ext hj
    rw [this, h0]
    simp
  · rw [fix_unitriangular hv j hj, Pi.single_eq_of_ne (fun h => hj (by rw [h]))]

theorem eq_of_fixed_sylow (hn : 1 ≤ n) (S : Sylow 2 (SpecialLinearGroup (Fin n) (ZMod 2)))
    {v w : Fin n → ZMod 2}
    (hv : ∀ s ∈ (S : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))),
      (s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v = v)
    (hw : ∀ s ∈ (S : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))),
      (s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w = w)
    (hv0 : v ≠ 0) (hw0 : w ≠ 0) : v = w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₀, hT₀⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 hn
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin n) (ZMod 2)) T₀ S
  have hmem : ∀ u ∈ unitriangular n (ZMod 2), g * u * g⁻¹ ∈
      (S : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))) := by
    intro u hu
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨u, hT₀ ▸ hu, rfl⟩
  have hinv : ((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have key : ∀ x : Fin n → ZMod 2, (∀ s ∈ (S : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))),
      (s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = x) → x ≠ 0 →
      ((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x =
        Pi.single ⟨0, by omega⟩ 1 := by
    intro x hx hx0
    refine eq_single_of_fix_unitriangular hn (fun u hu => ?_) fun h0 => hx0 ?_
    · have h1 := hx _ (hmem u hu)
      have e : ((g * u * g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) :
          Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
            ((u : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
              (((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
                x)) := by
        simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rw [e] at h1
      have h2 := congrArg (((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ ·) h1
      simp only [Matrix.mulVec_mulVec] at h2
      rw [← Matrix.mul_assoc, hinv, Matrix.one_mul] at h2
      rw [Matrix.mulVec_mulVec]
      exact h2
    · have := congrArg ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ ·) h0
      simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at this
      exact this
  have e1 := key v hv hv0
  have e2 := key w hw hw0
  have := congrArg ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ ·) (e1.trans e2.symm)
  simp only [Matrix.mulVec_mulVec] at this
  rwa [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_mulVec, Matrix.one_mulVec] at this

theorem eq_zero_or_one_of_commute {B : Matrix (Fin n) (Fin n) (ZMod 2)}
    (h : ∀ g : SpecialLinearGroup (Fin n) (ZMod 2),
      B * (g : Matrix (Fin n) (Fin n) (ZMod 2)) = (g : Matrix (Fin n) (Fin n) (ZMod 2)) * B) :
    B = 0 ∨ B = 1 := by
  obtain ⟨r, hr⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct fun t =>
    (h ⟨t.toMatrix, t.det⟩).symm
  rcases zmod_two_cases r with rfl | rfl
  · left
    rw [← hr]
    simp
  · right
    rw [← hr]
    simp

theorem scalars_eq_bot : scalars n (ZMod 2) = ⊥ := by
  rw [eq_bot_iff]
  rintro A ⟨c, -, hA⟩
  have hc : (c : ZMod 2) = 1 := by
    rcases zmod_two_cases (c : ZMod 2) with h | h
    · exact absurd h c.ne_zero
    · exact h
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [hA, hc]
  simp

theorem center_eq_bot : Subgroup.center (SpecialLinearGroup (Fin n) (ZMod 2)) = ⊥ := by
  rw [← scalars_eq_center, scalars_eq_bot]

theorem transvection_mul_self {i j : Fin n} (hij : i ≠ j) :
    SpecialLinearGroup.transvection hij (1 : ZMod 2) *
      SpecialLinearGroup.transvection hij (1 : ZMod 2) = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.coe_one]
  rw [add_mul, mul_add, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.single_mul_single_of_ne 1 i j i hij.symm 1, add_zero, add_assoc]
  have h2 : Matrix.single i j (1 : ZMod 2) + Matrix.single i j 1 = 0 := by
    ext a b
    rw [Matrix.add_apply, CharTwo.add_self_eq_zero, Matrix.zero_apply]
  rw [h2, add_zero]

theorem col_zero_of_graph {A : Matrix (Fin n) (Fin n) (ZMod 2)} {i j : Fin n}
    (h : A * (1 + Matrix.single i j 1) = (1 + Matrix.single j i 1) * A) {k : Fin n}
    (hk : k ≠ j) : A k i = 0 := by
  have e := congrFun (congrFun h k) j
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.add_apply,
    Matrix.add_apply, Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ hk,
    mul_one, add_zero] at e
  simpa using e

theorem graph_ne_conj (hn : 3 ≤ n) (A : GL (Fin n) (ZMod 2)) :
    ∃ g : SpecialLinearGroup (Fin n) (ZMod 2),
      slGraphAut n (ZMod 2) g ≠ slConjugation n (ZMod 2) A g := by
  by_contra hcon
  have h : ∀ g, slGraphAut n (ZMod 2) g = slConjugation n (ZMod 2) A g := fun g => by
    by_contra hg
    exact hcon ⟨g, hg⟩
  set i₀ : Fin n := ⟨0, by omega⟩
  have key : ∀ j : Fin n, (hj : i₀ ≠ j) → ∀ k : Fin n, k ≠ j →
      (A : Matrix (Fin n) (Fin n) (ZMod 2)) k i₀ = 0 := by
    intro j hj k hk
    set t := SpecialLinearGroup.transvection hj (1 : ZMod 2)
    have ht : t⁻¹ = t := inv_eq_of_mul_eq_one_right (transvection_mul_self hj)
    have h1 := congrArg (fun g : SpecialLinearGroup (Fin n) (ZMod 2) =>
      (g : Matrix (Fin n) (Fin n) (ZMod 2))) (h t)
    simp only [slGraphAut_matrix, coe_slConjugation, ht] at h1
    rw [SpecialLinearGroup.transvection_coe, Matrix.transpose_add, Matrix.transpose_one,
      Matrix.transpose_single] at h1
    have h2 : (A : Matrix (Fin n) (Fin n) (ZMod 2)) * (1 + Matrix.single i₀ j 1) =
        (1 + Matrix.single j i₀ 1) * (A : Matrix (Fin n) (Fin n) (ZMod 2)) := by
      rw [h1, Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    exact col_zero_of_graph h2 hk
  apply Matrix.GeneralLinearGroup.det_ne_zero A
  refine Matrix.det_eq_zero_of_column_eq_zero i₀ fun k => ?_
  by_cases hk : (k : ℕ) = 1
  · exact key ⟨2, by omega⟩ (fun h => by simp [i₀, Fin.ext_iff] at h) k
      (fun h => by rw [h] at hk; simp at hk)
  · exact key ⟨1, by omega⟩ (fun h => by simp [i₀, Fin.ext_iff] at h) k
      (fun h => hk (by rw [h]))

theorem ringEquiv_eq_one (φ : ZMod 2 ≃+* ZMod 2) : φ = 1 :=
  RingEquiv.toRingHom_injective (Subsingleton.elim _ _)

theorem exists_conj_graph (hn : 3 ≤ n) (σ : MulAut (SpecialLinearGroup (Fin n) (ZMod 2))) :
    ∃ (A : GL (Fin n) (ZMod 2)) (ε : ℕ), ε ≤ 1 ∧
      σ = slConjugation n (ZMod 2) A * slGraphAut n (ZMod 2) ^ ε := by
  obtain ⟨A, φ, ε, hε, hσ⟩ :=
    (automorphism_generation (K := ZMod 2) (n := n) hn).2 (descendAut n (ZMod 2) σ)
  refine ⟨A, ε, hε, ?_⟩
  have hd : descendAut n (ZMod 2) (slConjugation n (ZMod 2) A * slGraphAut n (ZMod 2) ^ ε) =
      descendAut n (ZMod 2) σ := by
    rw [hσ, ringEquiv_eq_one φ, map_one, mul_one, map_mul, map_pow]
    rfl
  apply MulEquiv.ext
  intro g
  have e := congrArg (fun τ : MulAut (projectiveSL n (ZMod 2)) => τ (proj n (ZMod 2) g)) hd
  simp only [descendAut_proj] at e
  rw [proj_eq_proj_iff, scalars_eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at e
  exact e.symm

theorem exists_col (w v r : Fin n → ZMod 2) (hrw : r ⬝ᵥ w = 1) (hrv : r ⬝ᵥ v = 1) :
    ∃ h : SpecialLinearGroup (Fin n) (ZMod 2),
      (h : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w = v := by
  have hdet := det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) (v - w) r
  rw [dotProduct_sub, hrv, hrw, sub_self, add_zero] at hdet
  refine ⟨⟨_, hdet⟩, ?_⟩
  show (1 + replicateCol (Fin 1) (v - w) * replicateRow (Fin 1) r) *ᵥ w = v
  rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
  have e1 : replicateRow (Fin 1) r *ᵥ w = fun _ => (1 : ZMod 2) := by
    ext j
    simpa [Matrix.mulVec, replicateRow] using hrw
  rw [e1]
  ext i
  have e2 : (replicateCol (Fin 1) (v - w) *ᵥ fun _ => (1 : ZMod 2)) i = v i - w i := by
    simp [Matrix.mulVec, dotProduct, replicateCol]
  rw [Pi.add_apply, e2]
  ring

theorem exists_row (a b u : Fin n → ZMod 2) (hau : a ⬝ᵥ u = 1) (hbu : b ⬝ᵥ u = 1) :
    ∃ h : SpecialLinearGroup (Fin n) (ZMod 2), a ᵥ* (h : Matrix (Fin n) (Fin n) (ZMod 2)) = b ∧
      ∀ x, (b - a) ⬝ᵥ x = 0 → (h : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = x := by
  have hdet := det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) u (b - a)
  rw [sub_dotProduct, hbu, hau, sub_self, add_zero] at hdet
  refine ⟨⟨_, hdet⟩, ?_, fun x hx => ?_⟩
  · show a ᵥ* (1 + replicateCol (Fin 1) u * replicateRow (Fin 1) (b - a)) = b
    rw [Matrix.vecMul_add, Matrix.vecMul_one, ← Matrix.vecMul_vecMul]
    have e1 : a ᵥ* replicateCol (Fin 1) u = fun _ => (1 : ZMod 2) := by
      ext j
      simpa [Matrix.vecMul, replicateCol, dotProduct_comm] using hau
    rw [e1]
    ext i
    have e2 : ((fun _ => (1 : ZMod 2)) ᵥ* replicateRow (Fin 1) (b - a)) i = b i - a i := by
      simp [Matrix.vecMul, dotProduct, replicateRow]
    rw [Pi.add_apply, e2]
    ring
  · show (1 + replicateCol (Fin 1) u * replicateRow (Fin 1) (b - a)) *ᵥ x = x
    rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    have e1 : replicateRow (Fin 1) (b - a) *ᵥ x = 0 := by
      ext j
      exact hx
    rw [e1, Matrix.mulVec_zero, add_zero]

theorem single_dotProduct_eq (i : Fin n) (v : Fin n → ZMod 2) :
    (Pi.single i 1 : Fin n → ZMod 2) ⬝ᵥ v = v i := by
  simp

theorem exists_eq_one_of_ne_zero {v : Fin n → ZMod 2} (hv : v ≠ 0) : ∃ k, v k = 1 := by
  by_contra h
  apply hv
  ext k
  rcases zmod_two_cases (v k) with h0 | h1
  · exact h0
  · exact absurd ⟨k, h1⟩ h

theorem coe_inv_mul (g : SpecialLinearGroup (Fin n) (ZMod 2)) :
    ((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem coe_mul_inv (g : SpecialLinearGroup (Fin n) (ZMod 2)) :
    (g : Matrix (Fin n) (Fin n) (ZMod 2)) *
      ((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem exists_mulVec_eq (hn : 1 ≤ n) {v : Fin n → ZMod 2} (hv : v ≠ 0) :
    ∃ g : SpecialLinearGroup (Fin n) (ZMod 2),
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Pi.single ⟨0, by omega⟩ 1 = v := by
  set i₀ : Fin n := ⟨0, by omega⟩
  by_cases h0 : v i₀ = 1
  · exact exists_col _ v (Pi.single i₀ 1) (by simp) (by rw [single_dotProduct_eq, h0])
  · obtain ⟨k, hk⟩ := exists_eq_one_of_ne_zero hv
    have hki : k ≠ i₀ := fun h => h0 (h ▸ hk)
    set w : Fin n → ZMod 2 := Pi.single i₀ 1 + Pi.single k 1
    obtain ⟨g₁, hg₁⟩ := exists_col (Pi.single i₀ 1) w (Pi.single i₀ 1) (by simp)
      (by simp [w, hki])
    obtain ⟨g₂, hg₂⟩ := exists_col w v (Pi.single k 1)
      (by simp [w, hki.symm]) (by rw [single_dotProduct_eq, hk])
    refine ⟨g₂ * g₁, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hg₁, hg₂]

theorem exists_nonincident (hn : 1 ≤ n) {x f : Fin n → ZMod 2} (hx : x ≠ 0)
    (hfx : f ⬝ᵥ x = 1) :
    ∃ g : SpecialLinearGroup (Fin n) (ZMod 2),
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Pi.single ⟨0, by omega⟩ 1 = x ∧
        f ᵥ* (g : Matrix (Fin n) (Fin n) (ZMod 2)) = Pi.single ⟨0, by omega⟩ 1 := by
  set i₀ : Fin n := ⟨0, by omega⟩
  obtain ⟨g₁, hg₁⟩ := exists_mulVec_eq hn hx
  have hf' : (f ᵥ* (g₁ : Matrix (Fin n) (Fin n) (ZMod 2))) ⬝ᵥ Pi.single i₀ 1 = 1 := by
    rw [← Matrix.dotProduct_mulVec, hg₁, hfx]
  obtain ⟨h, hh, hfix⟩ := exists_row (f ᵥ* (g₁ : Matrix (Fin n) (Fin n) (ZMod 2)))
    (Pi.single i₀ 1) (Pi.single i₀ 1) hf' (by simp)
  have he : (h : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Pi.single i₀ 1 = Pi.single i₀ 1 :=
    hfix _ (by rw [sub_dotProduct, hf']; simp)
  refine ⟨g₁ * h, ?_, ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, he, hg₁]
  · rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.vecMul_vecMul, hh]

theorem exists_incident (hn : 2 ≤ n) {x f : Fin n → ZMod 2} (hx : x ≠ 0) (hf : f ≠ 0)
    (hfx : f ⬝ᵥ x = 0) :
    ∃ g : SpecialLinearGroup (Fin n) (ZMod 2),
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Pi.single ⟨0, by omega⟩ 1 = x ∧
        f ᵥ* (g : Matrix (Fin n) (Fin n) (ZMod 2)) = Pi.single ⟨n - 1, by omega⟩ 1 := by
  set i₀ : Fin n := ⟨0, by omega⟩
  set i₁ : Fin n := ⟨n - 1, by omega⟩
  have hi : i₁ ≠ i₀ := fun h => by
    have := congrArg Fin.val h
    simp [i₀, i₁] at this
    omega
  obtain ⟨g₁, hg₁⟩ := exists_mulVec_eq (by omega) hx
  set f' := f ᵥ* (g₁ : Matrix (Fin n) (Fin n) (ZMod 2)) with hf'def
  have hf'0 : f' ⬝ᵥ Pi.single i₀ 1 = 0 := by
    rw [hf'def, ← Matrix.dotProduct_mulVec, hg₁, hfx]
  have hf'ne : f' ≠ 0 := by
    intro h0
    apply hf
    have := congrArg (· ᵥ* ((g₁⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2))) h0
    simp only [hf'def, Matrix.vecMul_vecMul, Matrix.zero_vecMul, coe_mul_inv,
      Matrix.vecMul_one] at this
    exact this
  obtain ⟨k, hk⟩ := exists_eq_one_of_ne_zero hf'ne
  have hk0 : k ≠ i₀ := by
    intro h
    rw [h] at hk
    rw [dotProduct_comm, single_dotProduct_eq, hk] at hf'0
    exact one_ne_zero hf'0
  obtain ⟨hA, hhA, hfixA⟩ := exists_row f' (Pi.single k 1) (Pi.single k 1)
    (by rw [dotProduct_comm, single_dotProduct_eq, hk]) (by simp)
  have heA : (hA : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Pi.single i₀ 1 = Pi.single i₀ 1 :=
    hfixA _ (by rw [sub_dotProduct, hf'0, single_dotProduct_eq, Pi.single_eq_of_ne hk0]; simp)
  obtain ⟨hB, hhB, heB⟩ : ∃ hB : SpecialLinearGroup (Fin n) (ZMod 2),
      (Pi.single k 1 : Fin n → ZMod 2) ᵥ* (hB : Matrix (Fin n) (Fin n) (ZMod 2)) =
        Pi.single i₁ 1 ∧
      (hB : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Pi.single i₀ 1 = Pi.single i₀ 1 := by
    by_cases hk1 : k = i₁
    · refine ⟨1, ?_, ?_⟩
      · rw [Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one, hk1]
      · rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    · obtain ⟨hB, hhB, hfixB⟩ := exists_row (Pi.single k 1) (Pi.single i₁ 1)
        (Pi.single k 1 + Pi.single i₁ 1)
        (by simp [Ne.symm hk1])
        (by simp [hk1])
      refine ⟨hB, hhB, hfixB _ ?_⟩
      rw [sub_dotProduct, single_dotProduct_eq, single_dotProduct_eq,
        Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hk0]
      simp
  refine ⟨g₁ * hA * hB, ?_, ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, heB, heA, hg₁]
  · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, ← hf'def, hhA, hhB]

@[expose] noncomputable def slEquivGL (n : ℕ) :
    SpecialLinearGroup (Fin n) (ZMod 2) ≃* GL (Fin n) (ZMod 2) :=
  MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
    ⟨Matrix.SpecialLinearGroup.toGL_injective, fun g => by
      have hdet : (g : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 := by
        rcases zmod_two_cases (g : Matrix (Fin n) (Fin n) (ZMod 2)).det with h | h
        · exact absurd h (Matrix.GeneralLinearGroup.det_ne_zero g)
        · exact h
      exact ⟨⟨g, hdet⟩, Units.ext rfl⟩⟩

theorem coe_slEquivGL (g : SpecialLinearGroup (Fin n) (ZMod 2)) :
    ((slEquivGL n g : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) := rfl

theorem eq_one_of_forall_commute_GL {z : GL (Fin n) (ZMod 2)} (h : ∀ g, z * g = g * z) : z = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Units.ext (Subsingleton.elim _ _)
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rcases eq_zero_or_one_of_commute (B := (z : Matrix (Fin n) (Fin n) (ZMod 2))) (fun g => by
    have := congrArg Units.val (h (Matrix.SpecialLinearGroup.toGL g))
    simpa using this) with h0 | h1
  · exfalso
    have := Matrix.GeneralLinearGroup.det_ne_zero z
    rw [h0, Matrix.det_zero] at this
    exact this rfl
  · exact Units.ext h1

theorem eq_one_of_forall_commute_SL {z : SpecialLinearGroup (Fin n) (ZMod 2)}
    (h : ∀ g, z * g = g * z) : z = 1 := by
  have hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin n) (ZMod 2)) :=
    Subgroup.mem_center_iff.2 fun g => (h g).symm
  rw [center_eq_bot, Subgroup.mem_bot] at hz
  exact hz

theorem exists_conj_or_conj_graph_GL (hn : 3 ≤ n) (α : MulAut (GL (Fin n) (ZMod 2))) :
    ∃ c : GL (Fin n) (ZMod 2), (∀ g, α g = c * g * c⁻¹) ∨
      ∀ g, α g = c * glGraphAut n (ZMod 2) g * c⁻¹ := by
  set e := slEquivGL n
  obtain ⟨A, ε, hε, hα⟩ := exists_conj_graph hn (MulAut.congr e.symm α)
  have key : ∀ s : SpecialLinearGroup (Fin n) (ZMod 2),
      α (e s) = e ((slConjugation n (ZMod 2) A * slGraphAut n (ZMod 2) ^ ε) s) := by
    intro s
    rw [← hα]
    simp [MulAut.congr_apply]
  refine ⟨A, ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · left
    intro g
    obtain ⟨s, rfl⟩ := e.surjective g
    rw [key, pow_zero, mul_one]
    exact toGL_slConjugation n (ZMod 2) A s
  · right
    intro g
    obtain ⟨s, rfl⟩ := e.surjective g
    rw [key, pow_one, MulAut.mul_apply]
    show Matrix.SpecialLinearGroup.toGL (slConjugation n (ZMod 2) A (slGraphAut n (ZMod 2) s)) =
      A * glGraphAut n (ZMod 2) (Matrix.SpecialLinearGroup.toGL s) * A⁻¹
    rw [toGL_slConjugation, toGL_slGraphAut]

end CFSG.Quasithin.SLnTwo
