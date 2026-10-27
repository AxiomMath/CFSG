module

public import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlockPair
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionNonsplitRestSUWit

public section

namespace CFSG.StandardType

namespace SUTB

open Matrix Module CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups

section Index

variable {n d : ℕ}

theorem ggPairPerm_of_lt {c : Fin n} (hc : (c : ℕ) < d) :
    SURep.ggPairPerm n d c = Fin.rev c := by
  rw [SURep.ggPairPerm_apply, SURep.ggPairInv, ite_eq_left (Or.inl hc)]

theorem ggPairPerm_of_ge {c : Fin n} (hc : n - d ≤ (c : ℕ)) :
    SURep.ggPairPerm n d c = Fin.rev c := by
  rw [SURep.ggPairPerm_apply, SURep.ggPairInv, ite_eq_left (Or.inr (by rw [Fin.val_rev]; omega))]

theorem ggPairPerm_of_mem {c : Fin n} (hc : c ∈ SUNS.midSet n d) :
    SURep.ggPairPerm n d c = c := by
  rw [SUNS.mem_midSet] at hc
  rw [SURep.ggPairPerm_apply, SURep.ggPairInv, ite_eq_right (by rw [Fin.val_rev]; omega)]

theorem ggPairPerm_mem_iff (c : Fin n) :
    SURep.ggPairPerm n d c ∈ SUNS.midSet n d ↔ c ∈ SUNS.midSet n d := by
  by_cases hc : c ∈ SUNS.midSet n d
  · rw [ggPairPerm_of_mem hc]
  · have hc' := hc
    rw [SUNS.mem_midSet] at hc'
    rcases Nat.lt_or_ge (c : ℕ) d with h1 | h1
    · rw [ggPairPerm_of_lt h1, SUNS.mem_midSet, Fin.val_rev]
      simp only [hc, iff_false]
      omega
    · have h2 : n - d ≤ (c : ℕ) := by omega
      rw [ggPairPerm_of_ge h2, SUNS.mem_midSet, Fin.val_rev]
      simp only [hc, iff_false]
      omega

theorem ggPairPerm_involutive (c : Fin n) : SURep.ggPairPerm n d (SURep.ggPairPerm n d c) = c :=
  SURep.ggPairInv_involutive n d c

end Index

section Frame

variable {K : Type} [Field K] {σ : K →+* K} {V : Type} [AddCommGroup V] [Module K V]
  {n d : ℕ}

@[expose] noncomputable def frameVec (e : Fin d → V) (θ : V →ₗ[K] V) (m : Fin (n - 2 * d) → V)
    (c : Fin n) : V :=
  if hc : (c : ℕ) < d then e ⟨c, hc⟩
  else if hc' : n - d ≤ (c : ℕ) then θ (e ⟨n - 1 - c, by have := c.isLt; omega⟩)
  else m ⟨c - d, by omega⟩

variable (e : Fin d → V) (θ : V →ₗ[K] V) (m : Fin (n - 2 * d) → V)

theorem frameVec_of_lt {c : Fin n} (hc : (c : ℕ) < d) : frameVec e θ m c = e ⟨c, hc⟩ := by
  rw [frameVec, dite_eq_left hc]

theorem frameVec_of_ge {c : Fin n} (hc : n - d ≤ (c : ℕ)) (hcd : d ≤ (c : ℕ)) :
    frameVec e θ m c = θ (e ⟨n - 1 - c, by have := c.isLt; omega⟩) := by
  rw [frameVec, dite_eq_right (by omega), dite_eq_left hc]

theorem frameVec_of_mem {c : Fin n} (hc : c ∈ SUNS.midSet n d) :
    frameVec e θ m c = m ⟨c - d, by rw [SUNS.mem_midSet] at hc; omega⟩ := by
  rw [SUNS.mem_midSet] at hc
  rw [frameVec, dite_eq_right (by omega), dite_eq_right (by omega)]

theorem frameVec_pair_of_lt (hdn : 2 * d ≤ n) {c : Fin n} (hc : (c : ℕ) < d) :
    frameVec e θ m (SURep.ggPairPerm n d c) = θ (frameVec e θ m c) := by
  rw [ggPairPerm_of_lt hc, frameVec_of_ge e θ m (by rw [Fin.val_rev]; omega)
    (by rw [Fin.val_rev]; omega), frameVec_of_lt e θ m hc]
  congr 2
  ext
  simp only [Fin.val_rev]
  omega

theorem frameVec_pair_of_ge (hdn : 2 * d ≤ n) {c : Fin n} (hc : n - d ≤ (c : ℕ)) :
    frameVec e θ m c = θ (frameVec e θ m (SURep.ggPairPerm n d c)) := by
  have hrc : ((Fin.rev c : Fin n) : ℕ) < d := by rw [Fin.val_rev]; have := c.isLt; omega
  rw [ggPairPerm_of_ge hc, frameVec_of_lt e θ m hrc, frameVec_of_ge e θ m hc (by omega)]
  congr 2
  ext
  simp only [Fin.val_rev]
  omega

variable {B : V →ₛₗ[σ] V →ₗ[K] K} {U₁ U₂ M : Submodule K V}

theorem frameVec_orthonormal (hdn : 2 * d ≤ n) (he : ∀ i, e i ∈ U₁)
    (heo : ∀ i j, B (e i) (e j) = if i = j then 1 else 0)
    (hθB : ∀ u ∈ U₁, ∀ v ∈ U₁, B (θ u) (θ v) = B u v) (hθU : ∀ u ∈ U₁, θ u ∈ U₂)
    (hm : ∀ i, m i ∈ M) (hmo : ∀ i j, B (m i) (m j) = if i = j then 1 else 0)
    (h12 : ∀ u ∈ U₁, ∀ w ∈ U₂, B u w = 0 ∧ B w u = 0)
    (h1M : ∀ u ∈ U₁, ∀ z ∈ M, B u z = 0 ∧ B z u = 0)
    (h2M : ∀ u ∈ U₂, ∀ z ∈ M, B u z = 0 ∧ B z u = 0) (i j : Fin n) :
    B (frameVec e θ m i) (frameVec e θ m j) = if i = j then 1 else 0 := by
  have hcase : ∀ c : Fin n, (c : ℕ) < d ∨ (n - d ≤ (c : ℕ) ∧ d ≤ (c : ℕ)) ∨
      (d ≤ (c : ℕ) ∧ (c : ℕ) < n - d) := by
    intro c
    omega
  have hne : ∀ {a b : Fin n}, (a : ℕ) ≠ b → a ≠ b := fun h hab => h (congrArg Fin.val hab)
  have hmid : ∀ {c : Fin n}, d ≤ (c : ℕ) ∧ (c : ℕ) < n - d → c ∈ SUNS.midSet n d :=
    fun hc => SUNS.mem_midSet.mpr hc
  rcases hcase i with hi | ⟨hi, hi'⟩ | hi <;> rcases hcase j with hj | ⟨hj, hj'⟩ | hj
  · rw [frameVec_of_lt e θ m hi, frameVec_of_lt e θ m hj, heo]
    simp only [Fin.ext_iff]
  · rw [frameVec_of_lt e θ m hi, frameVec_of_ge e θ m hj hj', (h12 _ (he _) _ (hθU _ (he _))).1,
      ite_eq_right (hne (by omega))]
  · rw [frameVec_of_lt e θ m hi, frameVec_of_mem e θ m (hmid hj), (h1M _ (he _) _ (hm _)).1,
      ite_eq_right (hne (by omega))]
  · rw [frameVec_of_ge e θ m hi hi', frameVec_of_lt e θ m hj, (h12 _ (he _) _ (hθU _ (he _))).2,
      ite_eq_right (hne (by omega))]
  · rw [frameVec_of_ge e θ m hi hi', frameVec_of_ge e θ m hj hj', hθB _ (he _) _ (he _), heo]
    simp only [Fin.ext_iff]
    have := i.isLt
    have := j.isLt
    by_cases hij : (i : ℕ) = j
    · rw [ite_eq_left (by omega), ite_eq_left hij]
    · rw [ite_eq_right (by omega), ite_eq_right hij]
  · rw [frameVec_of_ge e θ m hi hi', frameVec_of_mem e θ m (hmid hj),
      (h2M _ (hθU _ (he _)) _ (hm _)).1, ite_eq_right (hne (by omega))]
  · rw [frameVec_of_mem e θ m (hmid hi), frameVec_of_lt e θ m hj, (h1M _ (he _) _ (hm _)).2,
      ite_eq_right (hne (by omega))]
  · rw [frameVec_of_mem e θ m (hmid hi), frameVec_of_ge e θ m hj hj',
      (h2M _ (hθU _ (he _)) _ (hm _)).2, ite_eq_right (hne (by omega))]
  · rw [frameVec_of_mem e θ m (hmid hi), frameVec_of_mem e θ m (hmid hj), hmo]
    simp only [Fin.ext_iff]
    by_cases hij : (i : ℕ) = j
    · rw [ite_eq_left (by omega), ite_eq_left hij]
    · rw [ite_eq_right (by omega), ite_eq_right hij]

omit [AddCommGroup V] [Module K V] in
theorem linearIndependent_of_orthonormal {V : Type} [AddCommGroup V] [Module K V]
    {B : V →ₛₗ[σ] V →ₗ[K] K} {ι : Type} [Fintype ι] [DecidableEq ι] {b : ι → V}
    (hb : ∀ i j, B (b i) (b j) = if i = j then 1 else 0) : LinearIndependent K b := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have := congrArg (B (b j)) hc
  simpa [map_sum, hb] using this

end Frame

section Matrix

variable {f n : ℕ} {K : Type} [Field K]

@[expose] def colMat (b : Fin n → Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun r c => b c r

theorem colMat_mulVec (b : Fin n → Fin n → K) (v : Fin n → K) :
    colMat b *ᵥ v = ∑ c, v c • b c := by
  ext r
  simp only [colMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, mul_comm]

theorem colMat_mulVec_single (b : Fin n → Fin n → K) (c : Fin n) :
    colMat b *ᵥ Pi.single c 1 = b c := by
  rw [colMat_mulVec, Finset.sum_eq_single c (fun c' _ hc' => by
    rw [Pi.single_eq_of_ne hc', zero_smul]) (by simp), Pi.single_eq_same, one_smul]

variable (h : UnitaryFieldData 2 f K)

theorem conjTr_colMat_mul_apply (b : Fin n → Fin n → K) (M : Matrix (Fin n) (Fin n) K)
    (i j : Fin n) :
    (((colMat b).map h.bar)ᵀ * M * colMat b) i j = stdHermForm h n (b i) (M *ᵥ b j) := by
  rw [stdHermForm_apply, Matrix.mul_assoc, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [colMat, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply,
    Matrix.mulVec, dotProduct]

theorem conjTr_colMat_mul_self {b : Fin n → Fin n → K}
    (hb : ∀ i j, stdHermForm h n (b i) (b j) = if i = j then 1 else 0) :
    ((colMat b).map h.bar)ᵀ * colMat b = 1 := by
  ext i j
  have := conjTr_colMat_mul_apply h b 1 i j
  rw [Matrix.mul_one, Matrix.one_mulVec, hb] at this
  rw [this, Matrix.one_apply]

theorem conj_mem_unitarySU {Q : GL (Fin n) K}
    (hQ : ((Q : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (Q : Matrix (Fin n) (Fin n) K) = 1)
    {c : GL (Fin n) K} (hc : c ∈ unitarySU 2 f K n) : Q⁻¹ * c * Q ∈ unitarySU 2 f K n := by
  have hQi : ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((Q : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ := by
    have h1 : ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Q = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (Q * (((Q : Matrix (Fin n) (Fin n) K).map
          h.bar)ᵀ)) := by rw [mul_eq_one_comm.mp hQ, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  obtain ⟨hdet, hu⟩ := (mem_unitarySU_iff h).mp hc
  rw [mem_unitarySU_iff h, Units.val_mul, Units.val_mul, hQi]
  refine ⟨?_, ?_⟩
  · rw [det_mul, det_mul, hdet, mul_one, ← det_mul, hQ, det_one]
  · rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
    have hbb : (((Q : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ.map h.bar)ᵀ =
        (Q : Matrix (Fin n) (Fin n) K) := by
      ext i j
      simp [UnitaryFieldData.bar_bar]
    rw [hbb]
    calc ((Q : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
          ((((c : Matrix (Fin n) (Fin n) K)).map h.bar)ᵀ * Q) *
          ((((Q : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * c) * Q) =
        ((Q : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * ((((c : Matrix (Fin n) (Fin n) K)).map
          h.bar)ᵀ * (Q * ((Q : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ) * c) * Q := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [mul_eq_one_comm.mp hQ, Matrix.mul_one, hu, Matrix.mul_one, hQ]

end Matrix

section Core

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {p : ℕ}
  {A : Subgroup ↥(unitarySU 2 f K n)}

theorem exists_twoBlock_frame (hA : MaxElemAb p A) (hcard : p ^ 4 ≤ Nat.card A) :
    ∃ (Q : GL (Fin n) K) (d : ℕ) (x a₁ a₂ : ↥(unitarySU 2 f K n)),
      ((Q : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (Q : Matrix (Fin n) (Fin n) K) = 1 ∧
      x ∈ A ∧ a₁ ∈ A ∧ a₂ ∈ A ∧ 2 ≤ d ∧ 4 * d ≤ n ∧
      ((Q⁻¹ * (x : GL (Fin n) K) * Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((CFSG.RankThree.Classical.permGL (SURep.ggPairPerm n d) : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K) =
        ((CFSG.RankThree.Classical.permGL (SURep.ggPairPerm n d) : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K) *
          ((Q⁻¹ * (x : GL (Fin n) K) * Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∧
      TableBUE.IsBlockOn (SUNS.midSet n d)ᶜ
        ((Q⁻¹ * (x : GL (Fin n) K) * Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∧
      (∀ v : Fin n → K, ((Q⁻¹ * (x : GL (Fin n) K) * Q : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) *ᵥ v = v → ∀ k ∉ SUNS.midSet n d, v k = 0) ∧
      (∀ v : Fin n → K, v ᵥ* ((Q⁻¹ * (x : GL (Fin n) K) * Q : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) = v → ∀ k ∉ SUNS.midSet n d, v k = 0) ∧
      ∀ c ∈ A, TableBUE.IsBlockOn (SUNS.midSet n d)ᶜ
          ((Q⁻¹ * (c : GL (Fin n) K) * Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →
        ∃ i j : ℕ, c = a₁ ^ i * a₂ ^ j := by
  classical
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  set B := stdHermForm h n with hBdef
  have hBs : B.IsSymm := stdHermForm_isSymm h n
  obtain ⟨x, a₁, a₂, U₁, U₂, θ, hxA, ha₁, ha₂, hnd₁, hnd₂, h12, hd2, h4, hinv₁, hinv₂, hxM, hR₁,
    hR₂, hθU, hθB, hθx, hθs, hgen⟩ := exists_twoCopy h hA hcard
  set d := finrank K U₁ with hd
  have hsep : ∀ {U : Submodule K (Fin n → K)}, NondegOn B U →
      (B.domRestrict₁₂ U U).SeparatingLeft := by
    intro U hU u hu
    refine Subtype.ext (hU u u.2 fun w hw => ?_)
    rw [← hBs.eq (u : Fin n → K) w]
    rw [show B u w = 0 from hu ⟨w, hw⟩, map_zero]
  obtain ⟨e, he⟩ := h.exists_orthonormal_basis (hBs.domRestrict U₁) (hsep hnd₁)
  have he' : ∀ i j, B (e i : Fin n → K) (e j) = if i = j then 1 else 0 := fun i j => he i j
  have h21 : ∀ u ∈ U₂, ∀ v ∈ U₁, B u v = 0 ∧ B v u = 0 := fun u hu v hv =>
    ⟨(h12 v hv u hu).2, (h12 v hv u hu).1⟩
  have hW : NondegOn B (U₁ ⊔ U₂) := nondegOn_sup hnd₁ hnd₂ h21
  set M := (U₁ ⊔ U₂).orthogonalBilin B with hM
  have hcompl : IsCompl (U₁ ⊔ U₂) M := CFSG.RankThree.PartOne.OddIso.isCompl_orthogonalBilin_of_sep hW
  have hMnd : NondegOn B M := by
    intro z hz hn
    refine stdHermForm_separatingLeft h n z fun v => ?_
    obtain ⟨w, hw, z', hz', rfl⟩ := exists_add_orth hW v
    rw [map_add, ← hBs.eq w z, ← hBs.eq z' z, (Submodule.mem_orthogonalBilin.mp hz) w hw,
      hn z' hz', map_zero, add_zero]
  obtain ⟨m₀, hm₀⟩ := h.exists_orthonormal_basis (hBs.domRestrict M) (hsep hMnd)
  have hli₂ : LinearIndependent K (fun i => (⟨θ (e i), hθU _ (e i).2⟩ : U₂)) := by
    refine LinearIndependent.of_comp U₂.subtype ?_
    exact linearIndependent_of_orthonormal (B := B) fun i j => by
      change B (θ (e i)) (θ (e j)) = _
      rw [hθB _ (e i).2 _ (e j).2, he']
  have hdim₂ : finrank K U₂ = d := by
    refine le_antisymm ?_ ?_
    · have hle : U₂ ≤ U₁.map θ := fun w hw => by
        obtain ⟨u, hu, rfl⟩ := hθs w hw
        exact ⟨u, hu, rfl⟩
      exact (Submodule.finrank_mono hle).trans (Submodule.finrank_map_le θ U₁)
    · have := hli₂.fintype_card_le_finrank
      rwa [Fintype.card_fin] at this
  have hinf : U₁ ⊓ U₂ = ⊥ := (Submodule.eq_bot_iff _).mpr fun v hv =>
    hnd₁ v hv.1 fun m hm => (h12 m hm v hv.2).1
  have hdimW : finrank K ↥(U₁ ⊔ U₂) = 2 * d := by
    have := Submodule.finrank_sup_add_finrank_inf_eq U₁ U₂
    rw [hinf, finrank_bot, add_zero, hdim₂] at this
    omega
  have hdimM : finrank K M = n - 2 * d := by
    have := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [Module.finrank_fin_fun, hdimW] at this
    omega
  set e' : Fin d → (Fin n → K) := fun i => (e i : Fin n → K) with he'def
  set m' : Fin (n - 2 * d) → (Fin n → K) := fun i => (m₀ (Fin.cast hdimM.symm i) : Fin n → K)
    with hm'def
  set b := frameVec e' θ m' with hb
  have h2d : 2 * d ≤ n := by omega
  have h1M : ∀ u ∈ U₁, ∀ z ∈ M, B u z = 0 ∧ B z u = 0 := fun u hu z hz =>
    ⟨(Submodule.mem_orthogonalBilin.mp hz) u (Submodule.mem_sup_left hu), by
      rw [← hBs.eq, (Submodule.mem_orthogonalBilin.mp hz) u (Submodule.mem_sup_left hu),
        map_zero]⟩
  have h2M : ∀ u ∈ U₂, ∀ z ∈ M, B u z = 0 ∧ B z u = 0 := fun u hu z hz =>
    ⟨(Submodule.mem_orthogonalBilin.mp hz) u (Submodule.mem_sup_right hu), by
      rw [← hBs.eq, (Submodule.mem_orthogonalBilin.mp hz) u (Submodule.mem_sup_right hu),
        map_zero]⟩
  have hbo : ∀ i j, B (b i) (b j) = if i = j then 1 else 0 :=
    frameVec_orthonormal e' θ m' h2d (fun i => (e i).2) he' hθB hθU
      (fun i => (m₀ _).2) (fun i j => by
        have := hm₀ (Fin.cast hdimM.symm i) (Fin.cast hdimM.symm j)
        simp only [LinearMap.domRestrict₁₂_apply, Fin.cast_inj] at this
        exact this) h12 h1M h2M
  have hbU₁ : ∀ c : Fin n, (c : ℕ) < d → b c ∈ U₁ := fun c hc => by
    rw [hb, frameVec_of_lt e' θ m' hc]
    exact (e _).2
  have hbU₂ : ∀ c : Fin n, n - d ≤ (c : ℕ) → b c ∈ U₂ := fun c hc => by
    rw [hb, frameVec_of_ge e' θ m' hc (by omega)]
    exact hθU _ (e _).2
  have hbM : ∀ c ∈ SUNS.midSet n d, b c ∈ M := fun c hc => by
    rw [hb, frameVec_of_mem e' θ m' hc]
    exact (m₀ _).2
  have hcase : ∀ c : Fin n, (c : ℕ) < d ∨ n - d ≤ (c : ℕ) ∨ c ∈ SUNS.midSet n d := by
    intro c
    rw [SUNS.mem_midSet]
    omega
  have hout : ∀ c : Fin n, c ∉ SUNS.midSet n d → (c : ℕ) < d ∨ n - d ≤ (c : ℕ) := by
    intro c hc
    rcases hcase c with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact absurd h1 hc
  have hxb : ∀ k ∈ SUNS.midSet n d, lin x (b k) = b k := fun k hk => hxM _ (hbM k hk)
  set Qm := colMat b with hQm
  have hQQ : (Qm.map h.bar)ᵀ * Qm = 1 := conjTr_colMat_mul_self h hbo
  set Q : GL (Fin n) K := ⟨Qm, (Qm.map h.bar)ᵀ, mul_eq_one_comm.mp hQQ, hQQ⟩ with hQdef
  have hQiv : ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (Qm.map h.bar)ᵀ := rfl
  have hN : ∀ (c : ↥(unitarySU 2 f K n)) (i j : Fin n),
      ((Q⁻¹ * (c : GL (Fin n) K) * Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j =
        B (b i) (lin c (b j)) := by
    intro c i j
    rw [Units.val_mul, Units.val_mul, hQiv, lin_apply]
    exact conjTr_colMat_mul_apply h b _ i j
  have hcQ : ∀ (c : ↥(unitarySU 2 f K n)) (v : Fin n → K), mx c *ᵥ (Qm *ᵥ v) =
      Qm *ᵥ (((Q⁻¹ * (c : GL (Fin n) K) * Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) := by
    intro c v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul, hQiv]
    change _ = (Qm * ((Qm.map h.bar)ᵀ * mx c * Qm)) *ᵥ v
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_eq_one_comm.mp hQQ, Matrix.one_mul]
  have hcoord : ∀ (v : Fin n → K) (k : Fin n), B (b k) (Qm *ᵥ v) = v k := by
    intro v k
    rw [colMat_mulVec, map_sum]
    simp only [map_smul, hbo, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
  have hexp : ∀ v : Fin n → K, Qm *ᵥ (fun k => B (b k) v) = v := by
    intro v
    have h1 : (fun k => B (b k) v) = (Qm.map h.bar)ᵀ *ᵥ v := by
      funext k
      rw [stdHermForm_apply]
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply, hQm, colMat,
        Matrix.of_apply]
    rw [h1, Matrix.mulVec_mulVec, mul_eq_one_comm.mp hQQ, Matrix.one_mulVec]
  have hpi : ∀ i j : Fin n, B (b i) (lin x (b (SURep.ggPairPerm n d j))) =
      B (b (SURep.ggPairPerm n d i)) (lin x (b j)) := by
    intro i j
    have hθb : ∀ c : Fin n, (c : ℕ) < d → b (SURep.ggPairPerm n d c) = θ (b c) :=
      fun c hc => frameVec_pair_of_lt e' θ m' h2d hc
    have hθb' : ∀ c : Fin n, n - d ≤ (c : ℕ) → b c = θ (b (SURep.ggPairPerm n d c)) :=
      fun c hc => frameVec_pair_of_ge e' θ m' h2d hc
    have hπlt : ∀ c : Fin n, n - d ≤ (c : ℕ) → ((SURep.ggPairPerm n d c : Fin n) : ℕ) < d :=
      fun c hc => by rw [ggPairPerm_of_ge hc, Fin.val_rev]; have := c.isLt; omega
    have hπge : ∀ c : Fin n, (c : ℕ) < d → n - d ≤ ((SURep.ggPairPerm n d c : Fin n) : ℕ) :=
      fun c hc => by rw [ggPairPerm_of_lt hc, Fin.val_rev]; omega
    by_cases hj : j ∈ SUNS.midSet n d
    · rw [ggPairPerm_of_mem hj, hxb j hj, hbo, hbo]
      by_cases hij : i = j
      · subst hij
        rw [ite_eq_left rfl, ggPairPerm_of_mem hj, ite_eq_left rfl]
      · rw [ite_eq_right hij, ite_eq_right]
        intro h1
        apply hij
        have := congrArg (SURep.ggPairPerm n d) h1
        rwa [ggPairPerm_involutive, ggPairPerm_of_mem hj] at this
    by_cases hi : i ∈ SUNS.midSet n d
    · have hiso : ∀ w, B (b i) (lin x w) = B (b i) w := fun w => by
        rw [← isometry_lin h x (b i) w, hxb i hi]
      rw [ggPairPerm_of_mem hi, hiso, hiso, hbo, hbo, ite_eq_right, ite_eq_right] <;>
      intro h1
      all_goals first
        | exact hj (h1 ▸ hi)
        | (rw [h1, ggPairPerm_mem_iff] at hi; exact hj hi)
    rcases hout i hi with hi' | hi' <;> rcases hout j hj with hj' | hj'
    · rw [hθb j hj', ← hθx _ (hbU₁ j hj'), hθb i hi',
        (h12 _ (hbU₁ i hi') _ (hθU _ (hinv₁ _ (hbU₁ j hj')))).1,
        (h12 _ (hinv₁ _ (hbU₁ j hj')) _ (hθU _ (hbU₁ i hi'))).2]
    · rw [hθb i hi', hθb' j hj', ← hθx _ (hbU₁ _ (hπlt j hj')),
        hθB _ (hbU₁ i hi') _ (hinv₁ _ (hbU₁ _ (hπlt j hj')))]
    · rw [hθb j hj', ← hθx _ (hbU₁ j hj'), hθb' i hi',
        hθB _ (hbU₁ _ (hπlt i hi')) _ (hinv₁ _ (hbU₁ j hj'))]
    · rw [hθb' i hi', hθb' j hj', ← hθx _ (hbU₁ _ (hπlt j hj')),
        (h12 _ (hinv₁ _ (hbU₁ _ (hπlt j hj'))) _ (hθU _ (hbU₁ _ (hπlt i hi')))).2,
        (h12 _ (hbU₁ _ (hπlt i hi')) _ (hθU _ (hinv₁ _ (hbU₁ _ (hπlt j hj'))))).1]
  have hQQ' : ((Q : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (Q : Matrix (Fin n) (Fin n) K) = 1 :=
    hQQ
  have hfix : ∀ v : Fin n → K, ((Q⁻¹ * (x : GL (Fin n) K) * Q : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) *ᵥ v = v → ∀ k ∉ SUNS.midSet n d, v k = 0 := by
    intro v hv k hk
    have hxv : lin x (Qm *ᵥ v) = Qm *ᵥ v := by rw [lin_apply, hcQ, hv]
    have hker : Qm *ᵥ v ∈ (rng x).orthogonalBilin B := by
      rw [rng_orth_eq_ker (h := h) hA hxA, LinearMap.mem_ker, LinearMap.sub_apply,
        Module.End.one_apply, hxv, sub_self]
    have hbk : b k ∈ rng x := by
      rcases hout k hk with h1 | h1
      · exact hR₁ (hbU₁ k h1)
      · exact hR₂ (hbU₂ k h1)
    rw [← hcoord v k]
    exact (Submodule.mem_orthogonalBilin.mp hker) _ hbk
  refine ⟨Q, d, x, a₁, a₂, hQQ', hxA, ha₁, ha₂, hd2, h4, ?_, ?_, hfix, ?_, ?_⟩
  ·
    ext i j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [TableBUE.permGL_apply, SURep.ggPairPerm_inv]
    have e1 : ∀ (F : Fin n → K), ∑ k, F k * (if SURep.ggPairPerm n d k = j then (1 : K) else 0) =
        F (SURep.ggPairPerm n d j) := by
      intro F
      rw [Finset.sum_eq_single (SURep.ggPairPerm n d j)]
      · rw [ggPairPerm_involutive, ite_eq_left rfl, mul_one]
      · intro k _ hk
        rw [ite_eq_right (fun h1 => hk (by rw [← h1, ggPairPerm_involutive])), mul_zero]
      · simp
    have e2 : ∀ (F : Fin n → K), ∑ k, (if SURep.ggPairPerm n d i = k then (1 : K) else 0) * F k =
        F (SURep.ggPairPerm n d i) := by
      intro F
      simp
    rw [e1 (fun k => ((Q⁻¹ * (x : GL (Fin n) K) * Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i k),
      e2 (fun k => ((Q⁻¹ * (x : GL (Fin n) K) * Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) k j),
      hN, hN]
    exact hpi i j
  ·
    intro i j hij
    rw [hN, Matrix.one_apply, ← hbo]
    rcases hij with hi | hj
    · have hi' : i ∈ SUNS.midSet n d := by simpa using hi
      rw [← isometry_lin h x (b i) (b j), hxb i hi']
    · have hj' : j ∈ SUNS.midSet n d := by simpa using hj
      rw [hxb j hj']
  ·
    intro v hv k hk
    have hNU := conj_mem_unitarySU h hQQ' x.2
    obtain ⟨-, hNN⟩ := (mem_unitarySU_iff h).mp hNU
    set N := ((Q⁻¹ * (x : GL (Fin n) K) * Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hNdef
    have hNN' : N * (N.map h.bar)ᵀ = 1 := mul_eq_one_comm.mp hNN
    set w : Fin n → K := fun k => h.bar (v k) with hw
    have hw1 : (N.map h.bar)ᵀ *ᵥ w = w := by
      funext j
      have := congrFun hv j
      simp only [Matrix.vecMul, dotProduct] at this
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply, hw]
      rw [← this, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_mul, mul_comm]
    have hw2 : N *ᵥ w = w := by
      rw [← hw1, Matrix.mulVec_mulVec, hNN', Matrix.one_mulVec, hw1]
    have := hfix w hw2 k hk
    exact (h.bar_eq_zero_iff).mp this
  ·
    intro c hc hcb
    refine hgen c hc fun v hv => ?_
    set u : Fin n → K := fun k => B (b k) v with hu
    have hu0 : ∀ k ∉ SUNS.midSet n d, u k = 0 := by
      intro k hk
      rcases hout k hk with h1 | h1
      · exact (h1M _ (hbU₁ k h1) _ hv).1
      · exact (h2M _ (hbU₂ k h1) _ hv).1
    have hNu : ((Q⁻¹ * (c : GL (Fin n) K) * Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u =
        u := by
      funext i
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single i]
      · by_cases hi : i ∈ SUNS.midSet n d
        · rw [hcb i i (Or.inl (by simpa using hi)), Matrix.one_apply_eq, one_mul]
        · rw [hu0 i hi, mul_zero]
      · intro k _ hki
        by_cases hk : k ∈ SUNS.midSet n d
        · rw [hcb i k (Or.inr (by simpa using hk)), Matrix.one_apply_ne (Ne.symm hki), zero_mul]
        · rw [hu0 k hk, mul_zero]
      · simp
    rw [← hexp v, lin_apply, hcQ, hNu]

end Core

end SUTB

end CFSG.StandardType
