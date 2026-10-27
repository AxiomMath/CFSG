module

public import CFSG.CharacterTheory.Wreathed.OddLinearThreeCentralizerCore

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix

variable {K : Type*} [Field K]

@[expose] def negDiag3 (K : Type*) [Field K] : GL (Fin 3) K :=
  ⟨diagonal ![-1, -1, 1], diagonal ![-1, -1, 1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem coe_negDiag3 : ((negDiag3 K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    diagonal ![-1, -1, 1] :=
  rfl

theorem exists_conj_negDiag3 (h2 : (2 : K) ≠ 0) {t : GL (Fin 3) K} (ht2 : t * t = 1)
    (ht1 : t ≠ 1) (hdet : (t : Matrix (Fin 3) (Fin 3) K).det = 1) :
    ∃ P : GL (Fin 3) K, P⁻¹ * t * P = negDiag3 K := by
  classical
  open CFSG.Wreathed.OddLinearThreeCentralizerCore in
  set a : Module.End K (Fin 3 → K) := Matrix.toLin' (t : Matrix (Fin 3) (Fin 3) K) with ha
  have htt : (t : Matrix (Fin 3) (Fin 3) K) * (t : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, ht2, Units.val_one]
  have hinv : Function.Involutive a := by
    intro v
    rw [ha, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, htt,
      Matrix.one_mulVec]
  have hdeta : LinearMap.det a = 1 := by
    rw [ha, LinearMap.det_toLin', hdet]
  have hne : a ≠ LinearMap.id := by
    intro h
    apply ht1
    apply Units.ext
    rw [Units.val_one, ← Matrix.toLin'_one] at *
    exact Matrix.toLin'.injective (by rw [← ha, h])
  obtain ⟨hm, hp⟩ := CFSG.Wreathed.OddLinearThreeCentralizerCore.involution_finrank_three
    h2 a hinv (by simp) hdeta hne
  have hc := CFSG.Wreathed.OddLinearThreeCentralizerCore.involution_spaces_isCompl h2 a hinv
  let bm := Module.finBasisOfFinrankEq K
    (CFSG.Wreathed.OddLinearThreeCentralizerCore.minusSpace a) hm
  let bp := Module.finBasisOfFinrankEq K
    (CFSG.Wreathed.OddLinearThreeCentralizerCore.plusSpace a) hp
  let b₀ := (bm.prod bp).map (Submodule.prodEquivOfIsCompl _ _ hc)
  let d₀ : Fin 2 ⊕ Fin 1 → K := Sum.elim (fun _ => -1) (fun _ => 1)
  have hb₀ : ∀ i, a (b₀ i) = d₀ i • b₀ i := by
    rintro (i | i)
    · have hmem : b₀ (Sum.inl i) ∈ CFSG.Wreathed.OddLinearThreeCentralizerCore.minusSpace a := by
        simp [b₀, Module.Basis.map_apply, Module.Basis.prod_apply]
      exact Module.End.mem_eigenspace_iff.mp hmem
    · have hmem : b₀ (Sum.inr i) ∈ CFSG.Wreathed.OddLinearThreeCentralizerCore.plusSpace a := by
        simp [b₀, Module.Basis.map_apply, Module.Basis.prod_apply]
      exact Module.End.mem_eigenspace_iff.mp hmem
  let b := b₀.reindex finSumFinEquiv
  have hd : ∀ j : Fin 3, d₀ (finSumFinEquiv.symm j) = ![-1, -1, 1] j := by
    intro j
    fin_cases j <;> rfl
  have hb : ∀ j : Fin 3, (t : Matrix (Fin 3) (Fin 3) K) *ᵥ b j =
      (![-1, -1, 1] : Fin 3 → K) j • b j := by
    intro j
    have h := hb₀ (finSumFinEquiv.symm j)
    rw [hd j] at h
    rw [Module.Basis.reindex_apply]
    rwa [ha, Matrix.toLin'_apply] at h
  set U : Matrix (Fin 3) (Fin 3) K := (Pi.basisFun K (Fin 3)).toMatrix b with hU
  have hUij : ∀ i j, U i j = b j i := fun i j => by
    rw [hU, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
  have hUdet : IsUnit U.det := by
    have h := (Pi.basisFun K (Fin 3)).isUnit_det b
    rwa [Module.Basis.det_apply] at h
  have htU : (t : Matrix (Fin 3) (Fin 3) K) * U = U * diagonal ![-1, -1, 1] := by
    ext i j
    rw [mul_diagonal, hUij, Matrix.mul_apply]
    have h := congrFun (hb j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    simp only [hUij]
    rw [h, mul_comm]
  let P : GL (Fin 3) K := Matrix.GeneralLinearGroup.mk'' U hUdet
  refine ⟨P, ?_⟩
  have htP : t * P = P * negDiag3 K := by
    apply Units.ext
    simpa [P, coe_negDiag3] using htU
  rw [mul_assoc, htP, ← mul_assoc, inv_mul_cancel, one_mul]

theorem block_eq_zero_of_commute_negDiag (h2 : (2 : K) ≠ 0) {g : Matrix (Fin 3) (Fin 3) K}
    (hg : g * diagonal ![-1, -1, 1] = diagonal ![-1, -1, 1] * g) :
    g 0 2 = 0 ∧ g 1 2 = 0 ∧ g 2 0 = 0 ∧ g 2 1 = 0 := by
  have h := fun i j => congrFun (congrFun hg i) j
  simp only [mul_diagonal, diagonal_mul] at h
  have h02 := h 0 2
  have h12 := h 1 2
  have h20 := h 2 0
  have h21 := h 2 1
  simp at h02 h12 h20 h21
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : (2 : K) * g 0 2 = 0 := by linear_combination h02
    exact (mul_eq_zero.mp this).resolve_left h2
  · have : (2 : K) * g 1 2 = 0 := by linear_combination h12
    exact (mul_eq_zero.mp this).resolve_left h2
  · have : (2 : K) * g 2 0 = 0 := by linear_combination -h20
    exact (mul_eq_zero.mp this).resolve_left h2
  · have : (2 : K) * g 2 1 = 0 := by linear_combination -h21
    exact (mul_eq_zero.mp this).resolve_left h2

@[expose] def ulBlock (g : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 2) (Fin 2) K :=
  !![g 0 0, g 0 1; g 1 0, g 1 1]

theorem ulBlock_mul {g h : Matrix (Fin 3) (Fin 3) K} (hg : g 0 2 = 0 ∧ g 1 2 = 0) :
    ulBlock (g * h) = ulBlock g * ulBlock h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ulBlock, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, hg.1, hg.2]

theorem ulBlock_one : ulBlock (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ulBlock]

@[expose] noncomputable def negDiagBlockHom (h2 : (2 : K) ≠ 0) (X : Subgroup (GL (Fin 3) K))
    (hX : ∀ x ∈ X, x * negDiag3 K = negDiag3 K * x) : X →* GL (Fin 2) K where
  toFun x :=
    ⟨ulBlock (x : GL (Fin 3) K), ulBlock ((x⁻¹ : X) : GL (Fin 3) K), by
      have hb := block_eq_zero_of_commute_negDiag h2
        (congrArg Units.val (hX _ x.2) : _)
      rw [← ulBlock_mul ⟨hb.1, hb.2.1⟩, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel,
        Subgroup.coe_one, Units.val_one, ulBlock_one], by
      have hb := block_eq_zero_of_commute_negDiag h2
        (congrArg Units.val (hX _ (x⁻¹ : X).2) : _)
      rw [← ulBlock_mul ⟨hb.1, hb.2.1⟩, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel,
        Subgroup.coe_one, Units.val_one, ulBlock_one]⟩
  map_one' := by
    apply Units.ext
    simp [ulBlock_one]
  map_mul' x y := by
    apply Units.ext
    have hb := block_eq_zero_of_commute_negDiag h2 (congrArg Units.val (hX _ x.2) : _)
    simp only [Subgroup.coe_mul, Units.val_mul]
    exact ulBlock_mul ⟨hb.1, hb.2.1⟩

theorem coe_negDiagBlockHom (h2 : (2 : K) ≠ 0) (X : Subgroup (GL (Fin 3) K))
    (hX : ∀ x ∈ X, x * negDiag3 K = negDiag3 K * x) (x : X) :
    ((negDiagBlockHom h2 X hX x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ulBlock ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
  rfl

theorem negDiagBlockHom_injective (h2 : (2 : K) ≠ 0) (X : Subgroup (GL (Fin 3) K))
    (hX : ∀ x ∈ X, x * negDiag3 K = negDiag3 K * x)
    (hdet : ∀ x ∈ X, (x : Matrix (Fin 3) (Fin 3) K).det = 1) :
    Function.Injective (negDiagBlockHom h2 X hX) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hb := block_eq_zero_of_commute_negDiag h2 (congrArg Units.val (hX _ x.2) : _)
  have hm := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) hx
  simp only [coe_negDiagBlockHom, Units.val_one] at hm
  have e := fun i j => congrFun (congrFun hm i) j
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp [ulBlock] at e00 e01 e10 e11
  have hd := hdet _ x.2
  rw [Matrix.det_fin_three, e00, e01, e10, e11, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2] at hd
  have h22 : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    linear_combination hd
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e00, e01, e10, e11, h22, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2]

theorem exists_injective_gl2_of_commute (h2 : (2 : K) ≠ 0) {t : GL (Fin 3) K}
    (ht2 : t * t = 1) (ht1 : t ≠ 1) (htdet : (t : Matrix (Fin 3) (Fin 3) K).det = 1)
    (X : Subgroup (GL (Fin 3) K)) (hX : ∀ x ∈ X, x * t = t * x)
    (hdet : ∀ x ∈ X, (x : Matrix (Fin 3) (Fin 3) K).det = 1) :
    ∃ ρ : X →* GL (Fin 2) K, Function.Injective ρ ∧ ∀ x : X, (x : GL (Fin 3) K) = t → ρ x = -1 := by
  obtain ⟨P, hP⟩ := exists_conj_negDiag3 h2 ht2 ht1 htdet
  let c : GL (Fin 3) K ≃* GL (Fin 3) K := MulAut.conj P⁻¹
  let Y : Subgroup (GL (Fin 3) K) := X.map c.toMonoidHom
  have hcY : ∀ x : GL (Fin 3) K, c x = P⁻¹ * x * P := fun x => by
    simp [c]
  have hY : ∀ y ∈ Y, y * negDiag3 K = negDiag3 K * y := by
    rintro _ ⟨x, hx, rfl⟩
    change c x * negDiag3 K = negDiag3 K * c x
    rw [← hP, hcY]
    have := hX x hx
    calc P⁻¹ * x * P * (P⁻¹ * t * P) = P⁻¹ * (x * t) * P := by group
      _ = P⁻¹ * (t * x) * P := by rw [this]
      _ = P⁻¹ * t * P * (P⁻¹ * x * P) := by group
  have hYdet : ∀ y ∈ Y, (y : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    change ((c x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1
    rw [hcY, Units.val_mul, Units.val_mul, det_mul, det_mul, hdet x hx, mul_one,
      ← det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one]
  let e : X ≃* Y := X.equivMapOfInjective c.toMonoidHom c.injective
  refine ⟨(negDiagBlockHom h2 Y hY).comp e.toMonoidHom,
    (negDiagBlockHom_injective h2 Y hY hYdet).comp e.injective, ?_⟩
  intro x hxt
  apply Units.ext
  have hex : ((e x : Y) : GL (Fin 3) K) = negDiag3 K := by
    change c (x : GL (Fin 3) K) = negDiag3 K
    rw [hxt, hcY, hP]
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    coe_negDiagBlockHom, hex, coe_negDiag3, Units.val_neg, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ulBlock]

theorem fin_two_eq_of_commute_involution (h2 : (2 : K) ≠ 0)
    {s x : Matrix (Fin 2) (Fin 2) K}
    (hs : s * s = 1) (hs1 : s ≠ 1) (hsn : s ≠ -1) (hx : x * x = 1) (hxs : x * s = s * x) :
    x = 1 ∨ x = -1 ∨ x = s ∨ x = -s := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : K, s = !![a, b; c, d] := ⟨_, _, _, _, s.eta_fin_two⟩
  obtain ⟨x₁, x₂, x₃, x₄, rfl⟩ : ∃ x₁ x₂ x₃ x₄ : K, x = !![x₁, x₂; x₃, x₄] :=
    ⟨_, _, _, _, x.eta_fin_two⟩
  have hn : ∀ p q r t : K, -!![p, q; r, t] = !![-p, -q; -r, -t] := by
    intro p q r t
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  simp only [Matrix.mul_fin_two, Matrix.one_fin_two, hn] at hs hx hxs hs1 hsn ⊢
  rw [← Matrix.ext_iff] at hs hx
  simp [Fin.forall_fin_two] at hs hx hxs hs1 hsn ⊢
  obtain ⟨⟨s00, s01⟩, s10, s11⟩ := hs
  obtain ⟨⟨x00, x01⟩, x10, x11⟩ := hx
  obtain ⟨⟨c00, c01⟩, c10, -⟩ := hxs
  have hsq : ∀ y : K, y * y = 1 → y = 1 ∨ y = -1 := fun y hy => mul_self_eq_one_iff.mp hy
  have had : a + d = 0 := by
    by_contra hne
    have hb : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination s01
      exact (mul_eq_zero.mp this).resolve_right hne
    have hc : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination s10
      exact (mul_eq_zero.mp this).resolve_right hne
    subst hb hc
    rcases hsq a (by linear_combination s00) with ha | ha <;>
      rcases hsq d (by linear_combination s11) with hd | hd
    · exact hs1 ha rfl rfl hd
    · exact hne (by rw [ha, hd]; ring)
    · exact hne (by rw [ha, hd]; ring)
    · exact hsn ha rfl rfl hd
  have hd : d = -a := by linear_combination had
  subst hd
  by_cases hx14 : x₁ + x₄ = 0
  · have hx4 : x₄ = -x₁ := by linear_combination hx14
    subst hx4
    have e1 : b * x₁ = a * x₂ := by
      have : (2 : K) * (b * x₁ - a * x₂) = 0 := by linear_combination c01
      linear_combination (mul_eq_zero.mp this).resolve_left h2
    have e2 : c * x₁ = a * x₃ := by
      have : (2 : K) * (c * x₁ - a * x₃) = 0 := by linear_combination -c10
      linear_combination (mul_eq_zero.mp this).resolve_left h2
    have e3 : c * x₂ = b * x₃ := by linear_combination c00
    obtain ⟨l, hl1, hl2, hl3⟩ : ∃ l : K, x₁ = l * a ∧ x₂ = l * b ∧ x₃ = l * c := by
      by_cases ha0 : a = 0
      · subst ha0
        have hbc : b * c = 1 := by linear_combination s00
        have hb0 : b ≠ 0 := left_ne_zero_of_mul_eq_one hbc
        refine ⟨x₂ / b, ?_, by field_simp, ?_⟩
        · simp only [mul_zero]
          simpa [hb0] using e1
        · field_simp
          linear_combination -e3
      · refine ⟨x₁ / a, by field_simp, ?_, ?_⟩
        · field_simp
          linear_combination -e1
        · field_simp
          linear_combination -e2
    subst hl1 hl2 hl3
    have hl : l * l = 1 := by linear_combination x00 - l * l * s00
    rcases hsq l hl with h | h
    · subst h
      right; right; left
      refine ⟨⟨by ring, by ring⟩, by ring, by ring⟩
    · subst h
      right; right; right
      refine ⟨⟨by ring, by ring⟩, by ring, by ring⟩
  · have hx2 : x₂ = 0 := by
      have : x₂ * (x₁ + x₄) = 0 := by linear_combination x01
      exact (mul_eq_zero.mp this).resolve_right hx14
    have hx3 : x₃ = 0 := by
      have : x₃ * (x₁ + x₄) = 0 := by linear_combination x10
      exact (mul_eq_zero.mp this).resolve_right hx14
    subst hx2 hx3
    rcases hsq x₁ (by linear_combination x00) with h1 | h1 <;>
      rcases hsq x₄ (by linear_combination x11) with h4 | h4
    · left; exact ⟨⟨h1, rfl⟩, rfl, h4⟩
    · exact absurd (by rw [h1, h4]; ring) hx14
    · exact absurd (by rw [h1, h4]; ring) hx14
    · right; left; exact ⟨⟨h1, rfl⟩, rfl, h4⟩

theorem card_le_four_of_sq_eq_one_gl2 (h2 : (2 : K) ≠ 0) (F : Subgroup (GL (Fin 2) K))
    (hsq : ∀ x ∈ F, x * x = 1) : Nat.card F ≤ 4 := by
  classical
  have hcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := by
    intro x hx y hy
    have h1 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right (hsq _ (F.mul_mem hx hy))
    rw [_root_.mul_inv_rev, inv_eq_of_mul_eq_one_right (hsq y hy),
      inv_eq_of_mul_eq_one_right (hsq x hx)] at h1
    exact h1.symm
  have hval : ∀ x ∈ F, (x : Matrix (Fin 2) (Fin 2) K) * (x : Matrix (Fin 2) (Fin 2) K) = 1 :=
    fun x hx => by rw [← Units.val_mul, hsq x hx, Units.val_one]
  have hfin : ∀ T : Finset (GL (Fin 2) K), T.card ≤ 4 → (∀ x ∈ F, x ∈ T) → Nat.card F ≤ 4 := by
    intro T hT hsub
    calc Nat.card F = Nat.card (F : Set (GL (Fin 2) K)) := rfl
      _ ≤ Nat.card ((T : Set (GL (Fin 2) K))) :=
          Nat.card_mono (Set.toFinite _) fun x hx => hsub x hx
      _ ≤ 4 := by rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]; exact hT
  by_cases hall : ∀ x ∈ F, x = 1 ∨ x = -1
  · refine hfin {1, -1} ((Finset.card_le_two).trans (by norm_num)) fun x hx => ?_
    rcases hall x hx with h | h <;> simp [h]
  push Not at hall
  obtain ⟨s, hs, hs1, hsn⟩ := hall
  refine hfin {1, -1, s, -s} Finset.card_le_four fun x hx => ?_
  have hs1' : (s : Matrix (Fin 2) (Fin 2) K) ≠ 1 := fun h => hs1 (Units.ext h)
  have hsn' : (s : Matrix (Fin 2) (Fin 2) K) ≠ -1 := fun h => hsn (Units.ext (by simpa using h))
  have hxs : (x : Matrix (Fin 2) (Fin 2) K) * (s : Matrix (Fin 2) (Fin 2) K) =
      (s : Matrix (Fin 2) (Fin 2) K) * (x : Matrix (Fin 2) (Fin 2) K) := by
    rw [← Units.val_mul, hcomm x hx s hs, Units.val_mul]
  rcases fin_two_eq_of_commute_involution h2 (hval s hs) hs1' hsn' (hval x hx) hxs with
    h | h | h | h
  · have : x = 1 := Units.ext h
    simp [this]
  · have : x = -1 := Units.ext (by simpa using h)
    simp [this]
  · have : x = s := Units.ext h
    simp [this]
  · have : x = -s := Units.ext (by simpa using h)
    simp [this]

theorem card_le_four_of_sq_eq_one_sl3 (h2 : (2 : K) ≠ 0) (E : Subgroup (GL (Fin 3) K))
    (hsq : ∀ x ∈ E, x * x = 1) (hdet : ∀ x ∈ E, (x : Matrix (Fin 3) (Fin 3) K).det = 1) :
    Nat.card E ≤ 4 := by
  classical
  by_cases hE : ∀ x ∈ E, x = 1
  · have : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr hE
    rw [this, Subgroup.card_bot]
    norm_num
  push Not at hE
  obtain ⟨t, ht, ht1⟩ := hE
  have hcomm : ∀ x ∈ E, x * t = t * x := by
    intro x hx
    have h1 : (x * t)⁻¹ = x * t := inv_eq_of_mul_eq_one_right (hsq _ (E.mul_mem hx ht))
    rw [_root_.mul_inv_rev, inv_eq_of_mul_eq_one_right (hsq t ht),
      inv_eq_of_mul_eq_one_right (hsq x hx)] at h1
    exact h1.symm
  obtain ⟨ρ, hρ, -⟩ := exists_injective_gl2_of_commute h2 (hsq t ht) ht1 (hdet t ht) E hcomm hdet
  have hF := card_le_four_of_sq_eq_one_gl2 h2 ρ.range (by
    rintro _ ⟨x, rfl⟩
    rw [← map_mul, show x * x = 1 from Subtype.ext (hsq x x.2), map_one])
  calc Nat.card E = Nat.card ρ.range :=
        Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv
    _ ≤ 4 := hF

end CFSG.RankThree.SubgroupLists
