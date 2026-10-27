module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPart

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LinearGroups

variable {K : Type} [Field K] {n N : ℕ}

theorem card_mul_card_le_card_of_inf_eq_bot_of_le {G : Type*} [Group G] {H A B : Subgroup G}
    [Finite H] (hA : A ≤ H) (hB : B ≤ H) (hAB : A ⊓ B = ⊥) :
    Nat.card A * Nat.card B ≤ Nat.card H := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun p : A × B => (⟨p.1.1 * p.2.1, H.mul_mem (hA p.1.2) (hB p.2.2)⟩ : H)) ?_
  rintro ⟨a, b⟩ ⟨a', b'⟩ hab
  have h1 : (a : G) * b = a' * b' := congrArg Subtype.val hab
  have hmem : (a' : G)⁻¹ * a ∈ A ⊓ B := by
    refine ⟨A.mul_mem (A.inv_mem a'.2) a.2, ?_⟩
    have h2 : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h1, mul_inv_cancel_right]
    rw [h2]
    exact B.mul_mem b'.2 (B.inv_mem b.2)
  rw [hAB, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  have hb : (b : G) = b' := by
    rw [← hmem] at h1
    exact mul_left_cancel h1
  exact Prod.ext (Subtype.ext hmem.symm) (Subtype.ext hb)

theorem conj_mem_pairRadical {p f : ℕ} {W L : Submodule K (Fin N → K)}
    {g x : unitarySU p f K N}
    (hgW : ∀ v ∈ W, ((g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v ∈ W)
    (hgW' : ∀ v ∈ W,
      (((g⁻¹ : unitarySU p f K N) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v ∈ W)
    (hgL : ∀ v ∈ L, ((g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v ∈ L)
    (hgL' : ∀ v ∈ L,
      (((g⁻¹ : unitarySU p f K N) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v ∈ L)
    (hx : x ∈ pairRadical p f W L) : g * x * g⁻¹ ∈ pairRadical p f W L := by
  obtain ⟨h1, h2, h3⟩ := hx
  set G := ((g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)
  set G' := (((g⁻¹ : unitarySU p f K N) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)
  set X := ((x : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)
  have hinv : ∀ v, G *ᵥ (G' *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, show G * G' = (((g * g⁻¹ : unitarySU p f K N) : GL (Fin N) K) :
      Matrix (Fin N) (Fin N) K) by simp only [Subgroup.coe_mul, Units.val_mul, G, G'],
      mul_inv_cancel, OneMemClass.coe_one, Units.val_one, one_mulVec]
  have hexp : ∀ v, (((g * x * g⁻¹ : unitarySU p f K N) : GL (Fin N) K) :
      Matrix (Fin N) (Fin N) K) *ᵥ v = G *ᵥ (X *ᵥ (G' *ᵥ v)) := fun v => by
    simp only [Subgroup.coe_mul, Units.val_mul, mulVec_mulVec, G, X, G', mul_assoc]
  refine ⟨fun v hv => ?_, fun v hv => ?_, fun v => ?_⟩
  · rw [hexp, h1 _ (hgW' v hv), hinv]
  · rw [hexp]
    have := hgW _ (h2 _ (hgL' v hv))
    rwa [mulVec_sub, hinv] at this
  · rw [hexp]
    have := hgL _ (h3 (G' *ᵥ v))
    rwa [mulVec_sub, hinv] at this

@[expose] def pairDiagBlock (A : Matrix (Fin n) (Fin n) K) :
    Matrix (HypIndex n 0) (HypIndex n 0) K :=
  fromBlocks A 0 0 (fromBlocks 1 0 0 A)

theorem pairDiagBlock_one : pairDiagBlock (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [pairDiagBlock, fromBlocks_one, fromBlocks_one]

theorem pairDiagBlock_mul (A B : Matrix (Fin n) (Fin n) K) :
    pairDiagBlock (A * B) = pairDiagBlock A * pairDiagBlock B := by
  simp [pairDiagBlock, fromBlocks_multiply]

theorem det_pairDiagBlock (A : Matrix (Fin n) (Fin n) K) :
    (pairDiagBlock A).det = A.det * A.det := by
  rw [pairDiagBlock, det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁, det_one, one_mul]

variable (w : Module.Basis (HypIndex n 0) K (Fin N → K))

@[expose] noncomputable def pairDiagMat (A : Matrix (Fin n) (Fin n) K) : Matrix (Fin N) (Fin N) K :=
  LinearMap.toMatrix' (Matrix.toLin w w (pairDiagBlock A))

theorem pairDiagMat_mulVec (A : Matrix (Fin n) (Fin n) K) (v : Fin N → K) :
    pairDiagMat w A *ᵥ v = Matrix.toLin w w (pairDiagBlock A) v :=
  LinearMap.toMatrix'_mulVec _ v

theorem pairDiagMat_mulVec_inl (A : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    pairDiagMat w A *ᵥ w (.inl i) = ∑ j, A j i • w (.inl j) := by
  rw [pairDiagMat_mulVec, Matrix.toLin_self]
  simp [pairDiagBlock, Fintype.sum_sum_type]

theorem pairDiagMat_mulVec_inr_inr (A : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    pairDiagMat w A *ᵥ w (.inr (.inr i)) = ∑ j, A j i • w (.inr (.inr j)) := by
  rw [pairDiagMat_mulVec, Matrix.toLin_self]
  simp [pairDiagBlock, Fintype.sum_sum_type]

@[expose] noncomputable def pairDiagMatHom :
    Matrix (Fin n) (Fin n) K →* Matrix (Fin N) (Fin N) K where
  toFun := pairDiagMat w
  map_one' := by rw [pairDiagMat, pairDiagBlock_one, Matrix.toLin_one, LinearMap.toMatrix'_id]
  map_mul' A B := by
    simp only [pairDiagMat, pairDiagBlock_mul, Matrix.toLin_mul w w w, LinearMap.toMatrix'_comp]

theorem pairDiagMatHom_apply (A : Matrix (Fin n) (Fin n) K) :
    pairDiagMatHom w A = pairDiagMat w A :=
  rfl

theorem det_pairDiagMat (A : Matrix (Fin n) (Fin n) K) : (pairDiagMat w A).det = A.det * A.det := by
  rw [pairDiagMat, LinearMap.det_toMatrix', LinearMap.det_toLin, det_pairDiagBlock]

theorem pairDiagMat_mulVec_mem_aSpanTop (A : Matrix (Fin n) (Fin n) K) {v : Fin N → K}
    (hv : v ∈ aSpanTop K ⇑w) : pairDiagMat w A *ᵥ v ∈ aSpanTop K ⇑w := by
  have hle : aSpanTop K ⇑w ≤ (aSpanTop K ⇑w).comap (pairDiagMat w A).mulVecLin :=
    Submodule.span_le.mpr (by
      rintro _ ⟨i, rfl⟩
      change pairDiagMat w A *ᵥ w (.inl i) ∈ aSpanTop K ⇑w
      rw [pairDiagMat_mulVec_inl]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (inl_mem_aSpanTop _ j))
  exact hle hv

theorem zSpan_eq_bot {V : Type*} [AddCommGroup V] [Module K V] {r : ℕ} (v : HypIndex r 0 → V) :
    zSpan K v = ⊥ := by
  rw [zSpan, Submodule.span_eq_bot]
  rintro _ ⟨l, rfl⟩
  exact l.elim0

section SU

variable {p f : ℕ} (h : UnitaryFieldData p f K) {w}
  (hw : ∀ x y, stdHermForm h N (w x) (w y) = hypGram n 0 K x y)

include hw in
theorem pairDiagMat_isometry {A : Matrix (Fin n) (Fin n) K} (hA : (A.map h.bar)ᵀ * A = 1)
    (x y : Fin N → K) :
    stdHermForm h N (pairDiagMat w A *ᵥ x) (pairDiagMat w A *ᵥ y) = stdHermForm h N x y := by
  have hAij : ∀ i j, ∑ l, A l j * h.bar (A l i) = if i = j then 1 else 0 := fun i j => by
    have := congrFun (congrFun hA i) j
    simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply,
      Matrix.map_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have key := LinearMap.ext_basis w w
    (B := ((stdHermForm h N).comp (Matrix.toLin w w (pairDiagBlock A))).compl₂
      (Matrix.toLin w w (pairDiagBlock A))) (B' := stdHermForm h N) fun x y => by
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply]
    rw [← pairDiagMat_mulVec, ← pairDiagMat_mulVec, hw]
    rcases x with i | l | i <;> rcases y with j | t | j
    · simp [pairDiagMat_mulVec_inl, map_sum, hw]
    · exact t.elim0
    · simp [pairDiagMat_mulVec_inl, pairDiagMat_mulVec_inr_inr, map_sum, hw, hAij]
    · exact l.elim0
    · exact l.elim0
    · exact l.elim0
    · simp [pairDiagMat_mulVec_inl, pairDiagMat_mulVec_inr_inr, map_sum, hw, hAij]
    · exact t.elim0
    · simp [pairDiagMat_mulVec_inr_inr, map_sum, hw]
  have := LinearMap.congr_fun₂ key x y
  simp only [LinearMap.compl₂_apply, LinearMap.comp_apply] at this
  rw [pairDiagMat_mulVec, pairDiagMat_mulVec]
  exact this

include hw in
theorem pairDiagMat_mem_unitarySU (A : unitarySU p f K n) :
    Units.map (pairDiagMatHom w) (A : GL (Fin n) K) ∈ unitarySU p f K N := by
  obtain ⟨hdet, hA⟩ := (mem_unitarySU_iff h).mp A.2
  refine (mem_unitarySU_iff_isometry h).mpr ⟨?_, fun x y => ?_⟩
  · rw [Units.coe_map, pairDiagMatHom_apply, det_pairDiagMat, hdet, one_mul]
  · rw [Units.coe_map, pairDiagMatHom_apply]
    exact pairDiagMat_isometry h hw hA x y

@[expose] noncomputable def pairDiagSU : unitarySU p f K n →* unitarySU p f K N :=
  ((Units.map (pairDiagMatHom w)).comp (unitarySU p f K n).subtype).codRestrict _
    fun A => pairDiagMat_mem_unitarySU h hw A

theorem coe_pairDiagSU (A : unitarySU p f K n) :
    (((pairDiagSU h hw A : unitarySU p f K N) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
      pairDiagMat w ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  rfl

theorem pairDiagSU_injective : Function.Injective (pairDiagSU h hw) := by
  intro A A' hAA'
  have h1 : pairDiagMat w ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      pairDiagMat w ((A' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [← coe_pairDiagSU h hw, ← coe_pairDiagSU h hw, hAA']
  have h2 : pairDiagBlock ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      pairDiagBlock ((A' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    (Matrix.toLin w w).injective (LinearMap.toMatrix'.injective h1)
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  have := congrFun (congrFun h2 (.inl i)) (.inl j)
  simpa [pairDiagBlock] using this

theorem pairDiagSU_mem_centralizer {s : unitarySU p f K N}
    (hs1 : ∀ i, ((s : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ w (.inl i) = w (.inl i))
    (hs2 : ∀ i, ((s : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ w (.inr (.inr i)) =
      w (.inr (.inr i)) + w (.inl i)) (A : unitarySU p f K n) :
    pairDiagSU h hw A ∈ centralizer {s} := by
  rw [mem_centralizer_singleton_iff]
  refine Subtype.ext (Units.ext ?_)
  simp only [Subgroup.coe_mul, Units.val_mul, coe_pairDiagSU]
  refine Matrix.toLin'.injective (w.ext fun x => ?_)
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, LinearMap.comp_apply, LinearMap.comp_apply,
    Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_apply]
  rcases x with i | l | i
  · rw [hs1, pairDiagMat_mulVec_inl, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hs1]
  · exact l.elim0
  · rw [hs2, mulVec_add, pairDiagMat_mulVec_inl, pairDiagMat_mulVec_inr_inr, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hs2, smul_add, Finset.sum_add_distrib]

include hw in
theorem eq_one_of_pairDiagMat_fix {A : unitarySU p f K n}
    (hfix : ∀ i, pairDiagMat w ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w (.inl i) =
      w (.inl i)) : A = 1 := by
  refine Subtype.ext (Units.ext (Matrix.ext fun l i => ?_))
  have := congrArg (stdHermForm h N (w (.inr (.inr l)))) (hfix i)
  rw [pairDiagMat_mulVec_inl] at this
  simpa [map_sum, hw, Matrix.one_apply] using this

include hw in
theorem pairDiagSU_mem_normalizer (A : unitarySU p f K n) :
    pairDiagSU h hw A ∈ normalizer (pairRadical p f (aSpanTop K ⇑w) (aSpanTop K ⇑w ⊔ zSpan K ⇑w) :
      Set (unitarySU p f K N)) := by
  rw [zSpan_eq_bot, sup_bot_eq]
  have hpres : ∀ B : unitarySU p f K n, ∀ v ∈ aSpanTop K ⇑w,
      (((pairDiagSU h hw B : unitarySU p f K N) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v ∈
        aSpanTop K ⇑w :=
    fun B v hv => pairDiagMat_mulVec_mem_aSpanTop w _ hv
  have hpres' : ∀ B : unitarySU p f K n, ∀ v ∈ aSpanTop K ⇑w,
      ((((pairDiagSU h hw B)⁻¹ : unitarySU p f K N) : GL (Fin N) K) :
        Matrix (Fin N) (Fin N) K) *ᵥ v ∈ aSpanTop K ⇑w :=
    fun B v hv => by
      rw [← map_inv]
      exact hpres _ v hv
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_pairRadical (hpres A) (hpres' A) (hpres A) (hpres' A) hx,
    fun hx => ?_⟩
  have := conj_mem_pairRadical (g := (pairDiagSU h hw A)⁻¹) (hpres' A)
    (by rw [inv_inv]; exact hpres A) (hpres' A) (by rw [inv_inv]; exact hpres A) hx
  simpa [mul_assoc] using this

end SU

section Maximal

variable {f : ℕ} (h : UnitaryFieldData 2 f K) {w}
  (hw : ∀ x y, stdHermForm h N (w x) (w y) = hypGram n 0 K x y)

include hw in
theorem exists_isPGroup_le_centralizer_of_adapted (hn : 3 ≤ n) {s : unitarySU 2 f K N}
    (hs1 : ∀ i, ((s : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ w (.inl i) = w (.inl i))
    (hs2 : ∀ i, ((s : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ w (.inr (.inr i)) =
      w (.inr (.inr i)) + w (.inl i)) :
    ∃ Q : Subgroup (unitarySU 2 f K N), IsPGroup 2 Q ∧ Q ≤ centralizer {s} ∧
      2 ^ (f * (n ^ 2 + 2)) ≤ Nat.card Q := by
  have : CharP K 2 := h.charP
  have := h.finite
  set S := ((s : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) with hS
  obtain ⟨Rn, hRn2, -, hRncard⟩ :=
    exists_isPGroup_le_centralizer_of_mul_self h (1 : unitarySU 2 f K n) (mul_one 1)
  set R := pairRadical 2 f (aSpanTop K ⇑w) (aSpanTop K ⇑w ⊔ zSpan K ⇑w) with hR
  set T := Rn.map (pairDiagSU h hw) with hT
  have hsW : ∀ v, S *ᵥ v - v ∈ aSpanTop K ⇑w := by
    have hle : (⊤ : Submodule K (Fin N → K)) ≤
        (aSpanTop K ⇑w).comap (S.mulVecLin - LinearMap.id) := by
      rw [← w.span_eq, Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      rcases x with i | l | i
      · change S *ᵥ w (.inl i) - w (.inl i) ∈ aSpanTop K ⇑w
        rw [hs1, sub_self]
        exact zero_mem _
      · exact l.elim0
      · change S *ᵥ w (.inr (.inr i)) - w (.inr (.inr i)) ∈ aSpanTop K ⇑w
        rw [hs2, add_sub_cancel_left]
        exact inl_mem_aSpanTop _ i
    exact fun v => hle Submodule.mem_top
  have hsL : ∀ v ∈ aSpanTop K ⇑w ⊔ zSpan K ⇑w, S *ᵥ v = v := by
    rw [zSpan_eq_bot, sup_bot_eq]
    intro v hv
    have hle : aSpanTop K ⇑w ≤ LinearMap.ker (S.mulVecLin - LinearMap.id) :=
      Submodule.span_le.mpr (by
        rintro _ ⟨i, rfl⟩
        change S *ᵥ w (.inl i) - w (.inl i) = 0
        rw [hs1, sub_self])
    have := LinearMap.mem_ker.mp (hle hv)
    rwa [LinearMap.sub_apply, Matrix.mulVecLin_apply, LinearMap.id_apply, sub_eq_zero] at this
  have hRC : R ≤ centralizer {s} := fun g hg => mem_centralizer_of_mem_pairRadical hsW hsL hg
  have hTC : T ≤ centralizer {s} := by
    rintro _ ⟨A, -, rfl⟩
    exact pairDiagSU_mem_centralizer h hw hs1 hs2 A
  have hTN : T ≤ normalizer (R : Set (unitarySU 2 f K N)) := by
    rintro _ ⟨A, -, rfl⟩
    exact pairDiagSU_mem_normalizer h hw A
  have hTR : T ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨⟨A, -, rfl⟩, hg⟩
    have hA : A = 1 := eq_one_of_pairDiagMat_fix h hw fun i =>
      (mem_pairRadical.mp hg).1 _ (inl_mem_aSpanTop _ i)
    rw [hA, map_one]
    exact one_mem _
  refine ⟨T ⊔ R, (hRn2.map _).to_sup_of_normal_right' (isPGroup_pairRadical 2 f _ _) hTN,
    sup_le hTC hRC, ?_⟩
  have hcard := card_mul_card_le_card_of_inf_eq_bot_of_le (le_sup_left : T ≤ T ⊔ R)
    le_sup_right hTR
  have hTcard : Nat.card T = Nat.card Rn :=
    Subgroup.card_map_of_injective (pairDiagSU_injective h hw)
  have hRcard := card_pairRadical_ge h w hw
  have hexp : f * (n ^ 2 + 2) ≤
      f * (n / 2 * (n / 2 + 2 * (n % 2))) + f * (n * (n + 2 * 0)) := by
    have h3 := Nat.mul_le_mul (show 1 ≤ n / 2 by omega) (show 2 ≤ n / 2 + 2 * (n % 2) by omega)
    rw [← mul_add]
    exact Nat.mul_le_mul_left _ (by nlinarith)
  calc 2 ^ (f * (n ^ 2 + 2))
      ≤ 2 ^ (f * (n / 2 * (n / 2 + 2 * (n % 2))) + f * (n * (n + 2 * 0))) :=
        Nat.pow_le_pow_right two_pos hexp
    _ = 2 ^ (f * (n / 2 * (n / 2 + 2 * (n % 2)))) * 2 ^ (f * (n * (n + 2 * 0))) :=
        pow_add _ _ _
    _ ≤ Nat.card T * Nat.card R := Nat.mul_le_mul (hTcard ▸ hRncard) hRcard
    _ ≤ Nat.card (T ⊔ R : Subgroup (unitarySU 2 f K N)) := hcard


end Maximal

end CFSG.SeitzReduction.UnitaryPilot
