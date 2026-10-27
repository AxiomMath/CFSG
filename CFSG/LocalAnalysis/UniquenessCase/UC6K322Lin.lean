module

public import CFSG.RankThree.SubgroupLists.CliffordPrime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6.K322Lin

open Matrix Polynomial CFSG.RepresentationTheory

variable {F : Type*} [Field F] {n : ℕ}

theorem mulVec_eq_zero_of_commute {H : Subgroup (GL (Fin n) F)} {M : Matrix (Fin n) (Fin n) F}
    (hM : ∀ x ∈ H, (x : Matrix (Fin n) (Fin n) F) * M = M * x) {x : GL (Fin n) F} (hx : x ∈ H)
    {w : Fin n → F} (hw : M *ᵥ w = 0) : M *ᵥ ((x : Matrix (Fin n) (Fin n) F) *ᵥ w) = 0 := by
  rw [Matrix.mulVec_mulVec, ← hM x hx, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]

theorem eq_zero_or_injective_of_commute {H : Subgroup (GL (Fin n) F)}
    (hirr : IsIrreducibleMatrixRep H.subtype) {M : Matrix (Fin n) (Fin n) F}
    (hM : ∀ x ∈ H, (x : Matrix (Fin n) (Fin n) F) * M = M * x) :
    M = 0 ∨ ∀ w : Fin n → F, M *ᵥ w = 0 → w = 0 := by
  rcases hirr (LinearMap.ker (Matrix.toLin' M)) (fun g w hw => by
      rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hw ⊢
      exact mulVec_eq_zero_of_commute hM g.2 hw) with h | h
  · right
    intro w hw
    have : w ∈ LinearMap.ker (Matrix.toLin' M) := by
      rw [LinearMap.mem_ker, Matrix.toLin'_apply]
      exact hw
    rw [h] at this
    exact (Submodule.mem_bot F).1 this
  · left
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun w => ?_
    have : w ∈ LinearMap.ker (Matrix.toLin' M) := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker] at this
    rw [this, map_zero, LinearMap.zero_apply]

theorem mulVec_inv_mem_of_isInvariant {h : GL (Fin n) F} {W : Submodule F (Fin n → F)}
    (hW : ∀ w ∈ W, (h : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W) {w : Fin n → F} (hw : w ∈ W) :
    ((h⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W := by
  let f : W →ₗ[F] W := (Matrix.toLin' (h : Matrix (Fin n) (Fin n) F)).restrict
    (fun v hv => by rw [Matrix.toLin'_apply]; exact hW v hv)
  have hf : Function.Injective f := by
    intro a b hab
    have h1 := congrArg Subtype.val hab
    simp only [f, LinearMap.restrict_coe_apply, Matrix.toLin'_apply] at h1
    apply Subtype.ext
    have h2 := congrArg (fun v => ((h⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v) h1
    simpa [Matrix.mulVec_mulVec] using h2
  obtain ⟨w', hw'⟩ := (LinearMap.injective_iff_surjective.1 hf) ⟨w, hw⟩
  have h1 := congrArg Subtype.val hw'
  simp only [f, LinearMap.restrict_coe_apply, Matrix.toLin'_apply] at h1
  rw [← h1, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec]
  exact w'.2

theorem isInvariant_zpowers_of_isInvariant {h : GL (Fin n) F} {W : Submodule F (Fin n → F)}
    (hW : ∀ w ∈ W, (h : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W) :
    ∀ y ∈ Subgroup.zpowers h, ∀ w ∈ W, (y : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W := by
  intro y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  induction k using Int.induction_on with
  | zero => intro w hw; simpa using hw
  | succ k ih =>
    intro w hw
    rw [zpow_add_one, Units.val_mul, ← Matrix.mulVec_mulVec]
    exact ih (Subgroup.zpow_mem_zpowers h k) _ (hW w hw)
  | pred k ih =>
    intro w hw
    rw [zpow_sub_one, Units.val_mul, ← Matrix.mulVec_mulVec]
    exact ih (Subgroup.zpow_mem_zpowers h _) _ (mulVec_inv_mem_of_isInvariant hW hw)

theorem eq_bot_or_eq_top_of_isInvariant {h : GL (Fin n) F}
    (hirr : IsIrreducibleMatrixRep (Subgroup.zpowers h).subtype) {W : Submodule F (Fin n → F)}
    (hW : ∀ w ∈ W, (h : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W) : W = ⊥ ∨ W = ⊤ :=
  hirr W fun g w hw => isInvariant_zpowers_of_isInvariant hW g g.2 w hw

theorem eq_zero_or_injective_of_commute_gen {h : GL (Fin n) F}
    (hirr : IsIrreducibleMatrixRep (Subgroup.zpowers h).subtype) {M : Matrix (Fin n) (Fin n) F}
    (hM : (h : Matrix (Fin n) (Fin n) F) * M = M * h) :
    M = 0 ∨ ∀ w : Fin n → F, M *ᵥ w = 0 → w = 0 := by
  rcases eq_bot_or_eq_top_of_isInvariant hirr (W := LinearMap.ker (Matrix.toLin' M))
      (fun w hw => by
        rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hw ⊢
        rw [Matrix.mulVec_mulVec, ← hM, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero])
    with h | h
  · right
    intro w hw
    have : w ∈ LinearMap.ker (Matrix.toLin' M) := by
      rw [LinearMap.mem_ker, Matrix.toLin'_apply]
      exact hw
    rw [h] at this
    exact (Submodule.mem_bot F).1 this
  · left
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun w => ?_
    have : w ∈ LinearMap.ker (Matrix.toLin' M) := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker] at this
    rw [this, map_zero, LinearMap.zero_apply]

theorem charpoly_eq_three (M : Matrix (Fin 3) (Fin 3) F) :
    M.charpoly = X ^ 3 + C (M.charpoly.coeff 2) * X ^ 2 + C (M.charpoly.coeff 1) * X +
      C (M.charpoly.coeff 0) := by
  have h := (Matrix.charpoly_monic M).as_sum
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h
  conv_lhs => rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, mul_one, zero_add]
  ring

theorem false_of_cyclic_involution {h t : GL (Fin 3) F}
    (hirr : IsIrreducibleMatrixRep (Subgroup.zpowers h).subtype) (ht2 : t * t = 1) {m : ℕ}
    (hth : t * h * t⁻¹ = h ^ m)
    (hfix : Module.finrank F
      (LinearMap.ker (Matrix.toLin' ((t : Matrix (Fin 3) (Fin 3) F) - 1))) = 1) : False := by
  classical
  set H : Matrix (Fin 3) (Fin 3) F := (h : Matrix (Fin 3) (Fin 3) F) with hHdef
  set T : Matrix (Fin 3) (Fin 3) F := (t : Matrix (Fin 3) (Fin 3) F) with hTdef
  set Ti : Matrix (Fin 3) (Fin 3) F := ((t⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
    with hTidef
  have hTiT : Ti * T = 1 := by rw [hTdef, hTidef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hval : ∀ g : GL (Fin 3) F, ∀ k : ℕ,
      ((g ^ k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F) ^ k :=
    fun g k => Units.val_pow_eq_pow_val g k
  have hconj : T * H * Ti = H ^ m := by
    have := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hth
    simpa only [Units.val_mul, hval] using this
  have h1 : t * h ^ m * t⁻¹ = h := by
    calc t * h ^ m * t⁻¹ = t * (t * h * t⁻¹) * t⁻¹ := by rw [hth]
      _ = (t * t) * h * (t * t)⁻¹ := by group
      _ = h := by rw [ht2]; group
  have hconj' : T * H ^ m * Ti = H := by
    have := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) h1
    simpa only [Units.val_mul, hval] using this
  have hcommHm : H * H ^ m = H ^ m * H := (Commute.self_pow H m).eq
  set K : Submodule F (Fin 3 → F) := LinearMap.ker (Matrix.toLin' (T - 1)) with hKdef
  have hmemK : ∀ z, z ∈ K ↔ T *ᵥ z = z := fun z => by
    rw [hKdef, LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
      sub_eq_zero]
  have hKinv : ∀ M : Matrix (Fin 3) (Fin 3) F, T * M = M * T → ∀ z ∈ K, M *ᵥ z ∈ K := by
    intro M hM z hz
    rw [hmemK] at hz ⊢
    rw [Matrix.mulVec_mulVec, hM, ← Matrix.mulVec_mulVec, hz]
  have hK3 : K ≠ ⊥ ∧ K ≠ ⊤ := by
    constructor
    · intro hb
      rw [hb, finrank_bot] at hfix
      exact zero_ne_one hfix
    · intro ht
      rw [ht, finrank_top, Module.finrank_fin_fun] at hfix
      norm_num at hfix
  by_cases hc : H ^ m = H
  ·
    have hTH : T * H = H * T := by
      calc T * H = T * H * Ti * T := by rw [mul_assoc (T * H), hTiT, mul_one]
        _ = H * T := by rw [hconj, hc]
    rcases eq_bot_or_eq_top_of_isInvariant hirr (hKinv H hTH) with hb | ht
    · exact hK3.1 hb
    · exact hK3.2 ht
  set χ := H.charpoly with hχdef
  set c₀ := χ.coeff 0
  set c₁ := χ.coeff 1
  set c₂ := χ.coeff 2
  have hχ3 : χ = X ^ 3 + C c₂ * X ^ 2 + C c₁ * X + C c₀ := charpoly_eq_three H
  have hχH : aeval H χ = 0 := Matrix.aeval_self_charpoly H
  have hχHm : aeval (H ^ m) χ = 0 := by
    have hcp : (H ^ m).charpoly = χ := by
      rw [← hconj, hTidef, Matrix.coe_units_inv]
      exact Matrix.charpoly_units_conj t H
    rw [← hcp]
    exact Matrix.aeval_self_charpoly _
  have hpcomm : ∀ q₁ q₂ : F[X], aeval H q₁ * aeval H q₂ = aeval H q₂ * aeval H q₁ :=
    fun q₁ q₂ => by rw [← map_mul, mul_comm, map_mul]
  have hcommH : ∀ q : F[X], H * aeval H q = aeval H q * H := fun q => by
    have := hpcomm X q
    rwa [aeval_X] at this
  have hinj : ∀ q : F[X], aeval H q = 0 ∨ ∀ w, aeval H q *ᵥ w = 0 → w = 0 := fun q =>
    eq_zero_or_injective_of_commute_gen hirr (hcommH q)
  have hHm : aeval H (X ^ m : F[X]) = H ^ m := by rw [map_pow, aeval_X]
  set Qp : F[X] := X ^ 2 + X * X ^ m + (X ^ m) ^ 2 + C c₂ * (X + X ^ m) + C c₁ with hQp
  have hdiff : χ - χ.comp (X ^ m) = (X - X ^ m) * Qp := by
    rw [hχ3]
    simp only [add_comp, mul_comp, pow_comp, X_comp, C_comp]
    ring
  have hQ : aeval H Qp = 0 := by
    have h2 := congrArg (aeval H) hdiff
    rw [map_sub, hχH, aeval_comp, hHm, hχHm, sub_zero, map_mul, map_sub, aeval_X, hHm] at h2
    rcases hinj (X - X ^ m) with h0 | hi
    · exfalso
      rw [map_sub, aeval_X, hHm, sub_eq_zero] at h0
      exact hc h0.symm
    · apply Matrix.toLin'.injective
      refine LinearMap.ext fun w => ?_
      rw [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply]
      apply hi
      rw [map_sub, aeval_X, hHm, Matrix.mulVec_mulVec, ← h2, Matrix.zero_mulVec]
  set Rp : F[X] := -C c₂ - X - X ^ m with hRp
  have hroot : χ.comp Rp = Qp * (Rp - X) + χ := by
    rw [hχ3]
    simp only [add_comp, mul_comp, pow_comp, X_comp, C_comp]
    ring
  set r : Matrix (Fin 3) (Fin 3) F := aeval H Rp with hrdef
  have hχr : aeval r χ = 0 := by
    have h2 := congrArg (aeval H) hroot
    rwa [aeval_comp, map_add, map_mul, hQ, zero_mul, zero_add, hχH] at h2
  have hr : r = algebraMap F _ (-c₂) - H - H ^ m := by
    rw [hrdef, hRp, map_sub, map_sub, map_neg, aeval_C, aeval_X, map_pow, aeval_X, map_neg]
  have hTr : T * r = r * T := by
    have hTTi : T * Ti = 1 := by
      rw [hTdef, hTidef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h3 : T * r * Ti = r := by
      rw [hr, Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, hconj, hconj',
        Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hTTi]
      abel
    calc T * r = T * r * Ti * T := by rw [mul_assoc (T * r), hTiT, mul_one]
      _ = r * T := by rw [h3]
  obtain ⟨z₀, hz₀K, hz₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK3.1
  have hrz : r *ᵥ z₀ ∈ K := hKinv r hTr z₀ hz₀K
  have hspan := (finrank_eq_one_iff_of_nonzero' (⟨z₀, hz₀K⟩ : K)
    (fun h0 => hz₀ (congrArg Subtype.val h0))).1 hfix
  obtain ⟨c, hcz⟩ := hspan ⟨r *ᵥ z₀, hrz⟩
  have hcz' : r *ᵥ z₀ = c • z₀ := by
    have := congrArg Subtype.val hcz
    simpa using this.symm
  have hrc : r = algebraMap F _ c := by
    rcases hinj (Rp - C c) with h0 | hi
    · rw [map_sub, aeval_C, ← hrdef, sub_eq_zero] at h0
      exact h0
    · exfalso
      apply hz₀
      apply hi
      rw [map_sub, aeval_C, ← hrdef, Matrix.sub_mulVec, hcz', Algebra.algebraMap_eq_smul_one,
        Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
  have hχc : χ.eval c = 0 := by
    rw [hrc, aeval_algebraMap_apply_eq_algebraMap_eval] at hχr
    exact (algebraMap F (Matrix (Fin 3) (Fin 3) F)).injective (by rw [hχr, map_zero])
  rw [hχdef, Matrix.eval_charpoly] at hχc
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hχc
  have hsc : Matrix.scalar (Fin 3) c *ᵥ v = c • v := by
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have hHv : H *ᵥ v = c • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero, hsc] at hv
    exact hv.symm
  rcases eq_bot_or_eq_top_of_isInvariant hirr (W := F ∙ v) (fun w hw => by
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
      rw [Matrix.mulVec_smul, hHv, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)) with hb | ht
  · exact hv0 ((Submodule.span_singleton_eq_bot).1 hb)
  · have h1 := finrank_span_singleton (K := F) hv0
    rw [ht, finrank_top, Module.finrank_fin_fun] at h1
    norm_num at h1

open CFSG.RankThree.SubgroupLists (translate)

theorem mulVec_mem_translate_iff {g : GL (Fin n) F} {W : Submodule F (Fin n → F)}
    {v : Fin n → F} : (g : Matrix (Fin n) (Fin n) F) *ᵥ v ∈ translate g W ↔ v ∈ W := by
  constructor
  · intro h
    obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.1 h
    rw [Matrix.toLin'_apply] at hwv
    have : w = v := by
      have h2 := congrArg (fun u => ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ u) hwv
      simpa [Matrix.mulVec_mulVec] using h2
    exact this ▸ hw
  · intro hv
    exact Submodule.mem_map.2 ⟨v, hv, by rw [Matrix.toLin'_apply]⟩

theorem injective_of_isInternal {ι : Type*} [DecidableEq ι] {L : ι → Submodule F (Fin n → F)}
    (hL : DirectSum.IsInternal L) (hL1 : ∀ i, Module.finrank F (L i) = 1) :
    Function.Injective L := by
  intro i j hij
  by_contra hne
  have hd : Disjoint (L i) (L j) := hL.submodule_iSupIndep.pairwiseDisjoint hne
  rw [hij, disjoint_self] at hd
  have := hL1 j
  rw [hd, finrank_bot] at this
  exact zero_ne_one this

theorem iterate_two_of_iterate_four : ∀ σ : Fin 3 → Fin 3, Function.Injective σ →
    (∀ i, σ (σ (σ (σ i))) = i) → ∀ i, σ (σ i) = i := by decide

theorem eq_line_of_monomial {G : Subgroup (GL (Fin 3) F)} (h2 : (2 : F) ≠ 0)
    {L : Fin 3 → Submodule F (Fin 3 → F)} (hL : DirectSum.IsInternal L)
    (hL1 : ∀ i, Module.finrank F (L i) = 1) (hperm : ∀ g ∈ G, ∀ i, ∃ j, translate g (L i) = L j)
    {x : GL (Fin 3) F} (hxG : x ∈ G) (hx4 : x ^ 4 = 1) {Z : Submodule F (Fin 3 → F)}
    (hZ : Module.finrank F Z = 1)
    (hfix : {v | ((x ^ 2 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v} =
      (Z : Set (Fin 3 → F))) : ∃ i, Z = L i := by
  classical
  have htop := hL.submodule_iSup_eq_top
  have hinjL : Function.Injective L := injective_of_isInternal hL hL1
  choose σ hσ using hperm x hxG
  have hσinj : Function.Injective σ := by
    intro i j hij
    apply hinjL
    rw [← CFSG.RankThree.SubgroupLists.translate_inv_translate x (L i), hσ i, hij, ← hσ j,
      CFSG.RankThree.SubgroupLists.translate_inv_translate]
  have hiter : ∀ k : ℕ, ∀ i, translate (x ^ k) (L i) = L (σ^[k] i) := by
    intro k
    induction k with
    | zero => intro i; simp [CFSG.RankThree.SubgroupLists.translate_one]
    | succ k ih =>
      intro i
      rw [pow_succ', CFSG.RankThree.SubgroupLists.translate_mul, ih, hσ,
        Function.iterate_succ_apply']
  have hσ4 : ∀ i, σ (σ (σ (σ i))) = i := by
    intro i
    apply hinjL
    have := hiter 4 i
    rw [hx4, CFSG.RankThree.SubgroupLists.translate_one] at this
    simpa using this.symm
  have hσ2 := iterate_two_of_iterate_four σ hσinj hσ4
  have hx2L : ∀ i, translate (x ^ 2) (L i) = L i := by
    intro i
    rw [hiter 2 i]
    simp [hσ2 i]
  set y : Matrix (Fin 3) (Fin 3) F := ((x ^ 2 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hy
  have hyy : ∀ v, y *ᵥ (y *ᵥ v) = v := by
    intro v
    rw [hy, Matrix.mulVec_mulVec, ← Units.val_mul, ← pow_add, show 2 + 2 = 4 by norm_num, hx4,
      Units.val_one, Matrix.one_mulVec]
  have hsign : ∀ i, ∀ v ∈ L i, y *ᵥ v = v ∨ ∀ w ∈ L i, y *ᵥ w = -w := by
    intro i v hv
    have hyL : ∀ w ∈ L i, y *ᵥ w ∈ L i := fun w hw => by
      have := (mulVec_mem_translate_iff (g := x ^ 2) (W := L i)).2 hw
      rwa [hx2L i] at this
    by_cases hv0 : v = 0
    · left; rw [hv0, Matrix.mulVec_zero]
    have hspan := (finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : L i)
      (fun h0 => hv0 (congrArg Subtype.val h0))).1 (hL1 i)
    obtain ⟨ε, hε⟩ := hspan ⟨y *ᵥ v, hyL v hv⟩
    have hε' : y *ᵥ v = ε • v := by
      have := congrArg Subtype.val hε
      simpa using this.symm
    have hεε : ε * ε = 1 := by
      have h1 := hyy v
      rw [hε', Matrix.mulVec_smul, hε', smul_smul] at h1
      have h3 : (ε * ε - 1) • v = 0 := by rw [sub_smul, h1, one_smul, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right hv0)
    have hε1 : ε = 1 ∨ ε = -1 := by
      have : (ε - 1) * (ε + 1) = 0 := by ring_nf; rw [sq, hεε]; ring
      rcases mul_eq_zero.1 this with h | h
      · left; exact sub_eq_zero.1 h
      · right; exact eq_neg_of_add_eq_zero_left h
    rcases hε1 with rfl | rfl
    · left; rw [hε', one_smul]
    · right
      intro w hw
      obtain ⟨a, ha⟩ := hspan ⟨w, hw⟩
      have ha' : w = a • v := by
        have := congrArg Subtype.val ha
        simpa using this.symm
      rw [ha', Matrix.mulVec_smul, hε', neg_one_smul, smul_neg]
  by_cases hex : ∃ i, ∃ v ∈ L i, v ≠ 0 ∧ y *ᵥ v = v
  · obtain ⟨i, v, hv, hv0, hyv⟩ := hex
    refine ⟨i, (Submodule.eq_of_le_of_finrank_eq ?_ (by rw [hZ, hL1 i])).symm⟩
    intro w hw
    have hspan := (finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : L i)
      (fun h0 => hv0 (congrArg Subtype.val h0))).1 (hL1 i)
    obtain ⟨a, ha⟩ := hspan ⟨w, hw⟩
    have ha' : w = a • v := by
      have := congrArg Subtype.val ha
      simpa using this.symm
    have : w ∈ (Z : Set (Fin 3 → F)) := by
      rw [← hfix]
      show y *ᵥ w = w
      rw [ha', Matrix.mulVec_smul, hyv]
    exact this
  · exfalso
    push Not at hex
    have hneg : ∀ i, ∀ w ∈ L i, y *ᵥ w = -w := by
      intro i w hw
      by_cases hw0 : w = 0
      · rw [hw0, Matrix.mulVec_zero, neg_zero]
      rcases hsign i w hw with h | h
      · exact absurd h (hex i w hw hw0)
      · exact h w hw
    have hall : ∀ v, y *ᵥ v = -v := by
      intro v
      have hv : v ∈ ⨆ i, L i := htop ▸ Submodule.mem_top
      induction hv using Submodule.iSup_induction' with
      | mem i w hw => exact hneg i w hw
      | zero => rw [Matrix.mulVec_zero, neg_zero]
      | add a b _ _ ha hb => rw [Matrix.mulVec_add, ha, hb, neg_add]
    have hZne : Z ≠ ⊥ := fun hb => by
      rw [hb, finrank_bot] at hZ
      exact zero_ne_one hZ
    obtain ⟨z, hzZ, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZne
    have hz : y *ᵥ z = z := by
      have : z ∈ (Z : Set (Fin 3 → F)) := hzZ
      rw [← hfix] at this
      exact this
    rw [hall z] at hz
    have h2z : (2 : F) • z = 0 := by
      rw [two_smul]
      calc z + z = -z + z := by rw [hz]
        _ = 0 := neg_add_cancel z
    exact hz0 ((smul_eq_zero.1 h2z).resolve_left h2)

end CFSG.LocalAnalysis.UniquenessCase.UC6.K322Lin
