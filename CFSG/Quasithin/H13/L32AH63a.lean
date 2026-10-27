module

public import CFSG.Quasithin.H13.L32AOddAvg
public import CFSG.Quasithin.H13.VolIH5

public section

namespace CFSG.Quasithin.H6

open scoped MatrixGroups

@[expose] def zsm {M : Type} [Zero M] (c : ZMod 2) (x : M) : M := if c = 0 then 0 else x

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem zsm_add {M : Type} [AddGroup M] (h2 : ∀ m : M, m + m = 0) (a b : ZMod 2) (x : M) :
    zsm (a + b) x = zsm a x + zsm b x := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · simp [zsm]
  · simp [zsm]
  · simp [zsm]
  · show (if (1 + 1 : ZMod 2) = 0 then 0 else x) =
      (if (1 : ZMod 2) = 0 then 0 else x) + (if (1 : ZMod 2) = 0 then 0 else x)
    rw [ite_eq_left (by decide : (1 + 1 : ZMod 2) = 0),
      ite_eq_right (by decide : ¬ (1 : ZMod 2) = 0)]
    exact (h2 x).symm

theorem map_zsm {M N : Type} [AddGroup M] [AddGroup N] (f : M →+ N) (c : ZMod 2) (x : M) :
    f (zsm c x) = zsm c (f x) := by
  unfold zsm
  split_ifs <;> simp

theorem zsm_end {M : Type} [AddGroup M] (φ : AddMonoid.End M) (c : ZMod 2) (x : M) :
    φ (zsm c x) = zsm c (φ x) := by
  unfold zsm
  split_ifs
  · exact φ.map_zero
  · rfl

theorem zsm_zero {M : Type} [Zero M] (c : ZMod 2) : zsm c (0 : M) = 0 := by
  unfold zsm
  split_ifs <;> rfl

@[expose] def belMat : Fin 8 → Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  ![!![1, 0, 0; 0, 1, 0; 0, 0, 1], !![1, 1, 0; 0, 1, 0; 0, 0, 1], !![1, 0, 1; 0, 1, 0; 0, 0, 1],
    !![1, 1, 1; 0, 1, 0; 0, 0, 1], !![1, 0, 0; 0, 1, 1; 0, 0, 1], !![1, 1, 0; 0, 1, 1; 0, 0, 1],
    !![1, 0, 1; 0, 1, 1; 0, 0, 1], !![1, 1, 1; 0, 1, 1; 0, 0, 1]]

@[expose] def bel (i : Fin 8) : Γ := ⟨belMat i, by revert i; decide⟩

theorem bel_mem : ∀ i : Fin 8, bel i ∈ borel := by decide

theorem exists_bel : ∀ t : Γ, t ∈ borel → ∃ i, bel i = t := by decide +kernel

theorem bel_injective : Function.Injective bel := by
  intro i j h
  revert i j
  decide

@[expose] noncomputable def belEquiv : Fin 8 ≃ ↥borel :=
  Equiv.ofBijective (fun i => ⟨bel i, bel_mem i⟩)
    ⟨fun i j h => bel_injective (congrArg Subtype.val h),
      fun t => by
        obtain ⟨i, hi⟩ := exists_bel t t.2
        exact ⟨i, Subtype.ext hi⟩⟩

theorem card_borel : Nat.card ↥borel = 8 := by
  rw [← Nat.card_congr belEquiv, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_gamma : Nat.card Γ = 168 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem index_borel : borel.index = 21 := by
  have h := borel.index_mul_card
  rw [card_borel, card_gamma] at h
  omega

theorem st_add_self : ∀ x : St, x + x = 0 := by decide +kernel

@[expose] def stE13 : St := ⟨!![0, 0, 1; 0, 0, 0; 0, 0, 0], by decide⟩

@[expose] def stE31 : St := ⟨!![0, 0, 0; 0, 0, 0; 1, 0, 0], by decide⟩

@[expose] def stLam (A : St) : ZMod 2 :=
  A.1 0 1 + A.1 0 2 + A.1 1 0 + A.1 1 2 + A.1 2 0 + A.1 2 1

@[expose] def stLamHom : St →+ ZMod 2 :=
  AddMonoidHom.mk' stLam fun x y => by
    simp only [stLam, AddSubgroup.coe_add, Matrix.add_apply]
    ring

theorem stLamHom_apply (x : St) : stLamHom x = stLam x := rfl

@[expose] def freeTerm (x : St) (i : Fin 8) : St := zsm (stLam ((bel i)⁻¹ • x)) (bel i • stE31)

theorem st_free_aux : ∀ x : St, x = freeTerm x 0 + freeTerm x 1 + freeTerm x 2 + freeTerm x 3 +
    freeTerm x 4 + freeTerm x 5 + freeTerm x 6 + freeTerm x 7 := by
  decide +kernel

theorem belEquiv_apply (i : Fin 8) : ((belEquiv i : ↥borel) : Γ) = bel i := rfl

theorem st_free (x : St) :
    x = ∑ t : ↥borel, zsm (stLam ((t : Γ)⁻¹ • x)) ((t : Γ) • stE31) := by
  have h := Fintype.sum_equiv belEquiv (fun i => freeTerm x i)
    (fun t : ↥borel => zsm (stLam ((t : Γ)⁻¹ • x)) ((t : Γ) • stE31))
    (fun i => by rw [belEquiv_apply]; rfl)
  rw [← h, Fin.sum_univ_eight]
  exact st_free_aux x

theorem st_projective_aux {M : Type} [AddCommGroup M] [Finite M] (ρ : Γ →* AddMonoid.End M)
    (h2 : ∀ m : M, m + m = 0) (f : M →+ St) (hf : Function.Surjective f)
    (hfe : ∀ (g : Γ) (m : M), f (ρ g m) = ρSt g (f m)) :
    ∃ s : St →+ M, (∀ x, f (s x) = x) ∧ ∀ (g : Γ) (x : St), s (ρSt g x) = ρ g (s x) := by
  obtain ⟨m', hm'⟩ := hf stE31
  have hρmul : ∀ (a b : Γ) (m : M), ρ (a * b) m = ρ a (ρ b m) := fun a b m => by
    rw [map_mul]; rfl
  let s₀ : St →+ M :=
    { toFun := fun x => ∑ t : ↥borel, zsm (stLam ((t : Γ)⁻¹ • x)) (ρ t m')
      map_zero' := by
        refine Finset.sum_eq_zero fun t _ => ?_
        rw [smul_zero]
        show zsm (stLam 0) _ = 0
        rw [show stLam (0 : St) = 0 from rfl]
        rfl
      map_add' := fun x y => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [smul_add, ← stLamHom_apply, map_add, stLamHom_apply, stLamHom_apply]
        exact zsm_add h2 _ _ _ }
  have hs₀ : ∀ x, s₀ x = ∑ t : ↥borel, zsm (stLam ((t : Γ)⁻¹ • x)) (ρ t m') := fun x => rfl
  refine OddAvg.exists_equivariant_section_of_odd_index ρ ρSt borel
    (by rw [index_borel]; decide) st_add_self f hfe s₀ (fun x => ?_) (fun u hu x => ?_)
  · show f (s₀ x) = x
    rw [hs₀, map_sum]
    conv_rhs => rw [st_free x]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_zsm, hfe, hm']
    rfl
  · show s₀ (u • x) = ρ u (s₀ x)
    rw [hs₀, hs₀, map_sum]
    rw [← Fintype.sum_equiv (Equiv.mulLeft (⟨u, hu⟩ : ↥borel)) _ _ fun t => rfl]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Equiv.coe_mulLeft, Subgroup.coe_mul]
    rw [zsm_end, ← hρmul, mul_inv_rev, mul_smul, inv_smul_smul]

theorem smul_zsm (g : Γ) (c : ZMod 2) (x : St) : g • zsm c x = zsm c (g • x) := by
  unfold zsm
  split_ifs <;> simp

theorem zsmul_mem_pair {M : Type} [AddCommGroup M] (h2 : ∀ m : M, m + m = 0) (k : ℤ) (m : M) :
    k • m = 0 ∨ k • m = m := by
  obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [mul_zsmul, two_zsmul, h2]
  · right
    rw [add_zsmul, one_zsmul, mul_zsmul, two_zsmul, h2, zero_add]

theorem exists_hom_extend {M : Type} [AddCommGroup M] [Finite M] (h2 : ∀ m : M, m + m = 0)
    (W : AddSubgroup M) (φ : W →+ ZMod 2) : ∃ ψ : M →+ ZMod 2, ∀ w : W, ψ w = φ w := by
  classical
  induction W using WellFoundedGT.induction with
  | _ W ih =>
    by_cases hW : W = ⊤
    · subst hW
      exact ⟨φ.comp (AddSubgroup.topEquiv.symm : M ≃+ ↥(⊤ : AddSubgroup M)).toAddMonoidHom,
        fun w => rfl⟩
    obtain ⟨m, hmW⟩ : ∃ m, m ∉ W := by
      by_contra h
      push Not at h
      exact hW (eq_top_iff.mpr fun x _ => h x)
    set W' := W ⊔ AddSubgroup.zmultiples m with hW'
    have hlt : W < W' := lt_of_le_of_ne le_sup_left fun e =>
      hmW (e ▸ AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples m))
    have hcase : ∀ x ∈ W', x ∈ W ∨ x + m ∈ W := by
      intro x hx
      obtain ⟨w, hw, z, hz, rfl⟩ := AddSubgroup.mem_sup.mp hx
      obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hz
      rcases zsmul_mem_pair h2 k m with h | h <;> rw [h]
      · exact Or.inl (by simpa using hw)
      · exact Or.inr (by rw [add_assoc, h2, add_zero]; exact hw)
    have hWW' : W ≤ W' := le_sup_left
    let φ' : W' →+ ZMod 2 :=
      { toFun := fun x => if hx : (x : M) ∈ W then φ ⟨x, hx⟩ else
          φ ⟨x + m, (hcase x x.2).resolve_left hx⟩
        map_zero' := by
          simp only [AddSubgroup.coe_zero, zero_mem, dite_true]
          exact φ.map_zero
        map_add' := fun x y => by
          have hx2 := hcase x x.2
          have hy2 := hcase y y.2
          by_cases hx : (x : M) ∈ W <;> by_cases hy : (y : M) ∈ W
          · have hxy : ((x + y : W') : M) ∈ W := add_mem hx hy
            rw [dite_eq_left hxy, dite_eq_left hx, dite_eq_left hy, ← map_add]
            rfl
          · have hxy : ((x + y : W') : M) ∉ W := fun h => hy (by
              have := sub_mem h hx
              simpa using this)
            rw [dite_eq_right hxy, dite_eq_left hx, dite_eq_right hy, ← map_add]
            congr 1
            apply Subtype.ext
            simp only [AddSubgroup.coe_add]
            abel
          · have hxy : ((x + y : W') : M) ∉ W := fun h => hx (by
              have := sub_mem h hy
              simpa using this)
            rw [dite_eq_right hxy, dite_eq_right hx, dite_eq_left hy, ← map_add]
            congr 1
            apply Subtype.ext
            simp only [AddSubgroup.coe_add]
            abel
          · have hxy : ((x + y : W') : M) ∈ W := by
              have := add_mem (hx2.resolve_left hx) (hy2.resolve_left hy)
              rwa [show (x : M) + m + ((y : M) + m) = (x : M) + y + (m + m) by abel, h2,
                add_zero] at this
            rw [dite_eq_left hxy, dite_eq_right hx, dite_eq_right hy, ← map_add]
            congr 1
            apply Subtype.ext
            simp only [AddSubgroup.coe_add]
            rw [show (x : M) + m + ((y : M) + m) = (x : M) + y + (m + m) by abel, h2, add_zero] }
    obtain ⟨ψ, hψ⟩ := ih W' hlt φ'
    refine ⟨ψ, fun w => ?_⟩
    have h1 : ψ (w : M) = φ' ⟨w, hWW' w.2⟩ := hψ ⟨w, hWW' w.2⟩
    rw [h1]
    show (if hx : (w : M) ∈ W then φ ⟨w, hx⟩ else _) = φ w
    rw [dite_eq_left w.2]

theorem exists_functional {M : Type} [AddCommGroup M] [Finite M] (h2 : ∀ m : M, m + m = 0)
    (f : St →+ M) (hf : Function.Injective f) : ∃ μ : M →+ ZMod 2, ∀ x, μ (f x) = stLam x := by
  let e := AddMonoidHom.ofInjective hf
  obtain ⟨ψ, hψ⟩ := exists_hom_extend h2 f.range (stLamHom.comp e.symm.toAddMonoidHom)
  refine ⟨ψ, fun x => ?_⟩
  have h1 := hψ (e x)
  rw [show ((e x : ↥f.range) : M) = f x from rfl] at h1
  rw [h1]
  show stLamHom (e.symm (e x)) = stLam x
  rw [AddEquiv.symm_apply_apply, stLamHom_apply]

theorem st_injective_aux {M : Type} [AddCommGroup M] [Finite M] (ρ : Γ →* AddMonoid.End M)
    (h2 : ∀ m : M, m + m = 0) (f : St →+ M) (hf : Function.Injective f)
    (hfe : ∀ (g : Γ) (x : St), f (ρSt g x) = ρ g (f x)) :
    ∃ p : M →+ St, (∀ x, p (f x) = x) ∧ ∀ (g : Γ) (m : M), p (ρ g m) = ρSt g (p m) := by
  obtain ⟨μ, hμ⟩ := exists_functional h2 f hf
  have hρmul : ∀ (a b : Γ) (m : M), ρ (a * b) m = ρ a (ρ b m) := fun a b m => by
    rw [map_mul]; rfl
  let p₀ : M →+ St :=
    { toFun := fun m => ∑ t : ↥borel, zsm (μ (ρ (t : Γ)⁻¹ m)) ((t : Γ) • stE31)
      map_zero' := by
        refine Finset.sum_eq_zero fun t _ => ?_
        rw [map_zero, map_zero]
        rfl
      map_add' := fun x y => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [map_add, map_add]
        exact zsm_add st_add_self _ _ _ }
  have hp₀ : ∀ m, p₀ m = ∑ t : ↥borel, zsm (μ (ρ (t : Γ)⁻¹ m)) ((t : Γ) • stE31) :=
    fun m => rfl
  refine OddAvg.exists_equivariant_retraction_of_odd_index ρ ρSt borel
    (by rw [index_borel]; decide) st_add_self f hfe p₀ (fun x => ?_) (fun u hu m => ?_)
  · show p₀ (f x) = x
    rw [hp₀]
    conv_rhs => rw [st_free x]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← hfe, hμ]
    rfl
  · show p₀ (ρ u m) = ρSt u (p₀ m)
    rw [hp₀, hp₀]
    show _ = u • ∑ t : ↥borel, zsm (μ (ρ (t : Γ)⁻¹ m)) ((t : Γ) • stE31)
    rw [Finset.smul_sum]
    rw [← Fintype.sum_equiv (Equiv.mulLeft (⟨u, hu⟩ : ↥borel)) _ _ fun t => rfl]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Equiv.coe_mulLeft, Subgroup.coe_mul]
    rw [smul_zsm, mul_inv_rev, hρmul, ← hρmul u⁻¹ u, inv_mul_cancel, map_one, mul_smul]
    rfl

theorem st_projective {M : Type} [AddGroup M] [Finite M] (ρ : Γ →* AddMonoid.End M)
    (h2 : ∀ m : M, m + m = 0) (f : M →+ St) (hf : Function.Surjective f)
    (hfe : ∀ (g : Γ) (m : M), f (ρ g m) = ρSt g (f m)) :
    ∃ s : St →+ M, (∀ x, f (s x) = x) ∧ ∀ (g : Γ) (x : St), s (ρSt g x) = ρ g (s x) := by
  let _ : AddCommGroup M := addCommGroupOfAddSelf h2
  exact st_projective_aux ρ h2 f hf hfe

theorem st_injective {M : Type} [AddGroup M] [Finite M] (ρ : Γ →* AddMonoid.End M)
    (h2 : ∀ m : M, m + m = 0) (f : St →+ M) (hf : Function.Injective f)
    (hfe : ∀ (g : Γ) (x : St), f (ρSt g x) = ρ g (f x)) :
    ∃ p : M →+ St, (∀ x, p (f x) = x) ∧ ∀ (g : Γ) (m : M), p (ρ g m) = ρSt g (p m) := by
  let _ : AddCommGroup M := addCommGroupOfAddSelf h2
  exact st_injective_aux ρ h2 f hf hfe

@[expose] def stForm : St →+ St →+ ZMod 2 where
  toFun x :=
    { toFun := fun y => (x.1 * y.1).trace
      map_zero' := by simp
      map_add' := fun y y' => by simp [Matrix.mul_add, Matrix.trace_add] }
  map_zero' := by
    ext y
    simp
  map_add' := fun x x' => by
    ext y
    simp [Matrix.add_mul, Matrix.trace_add]

theorem stForm_apply (x y : St) : stForm x y = (x.1 * y.1).trace := rfl

@[expose] def stBasisMat (i : Fin 8) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  ![!![0, 1, 0; 0, 0, 0; 0, 0, 0], !![0, 0, 1; 0, 0, 0; 0, 0, 0], !![0, 0, 0; 1, 0, 0; 0, 0, 0],
    !![0, 0, 0; 0, 0, 1; 0, 0, 0], !![0, 0, 0; 0, 0, 0; 1, 0, 0], !![0, 0, 0; 0, 0, 0; 0, 1, 0],
    !![1, 0, 0; 0, 1, 0; 0, 0, 0], !![0, 0, 0; 0, 1, 0; 0, 0, 1]] i

theorem stForm_nondeg_aux : ∀ x : St, (∀ i : Fin 8, (x.1 * stBasisMat i).trace = 0) → x = 0 := by
  decide +kernel

theorem stForm_nondeg (x : St) (hx : ∀ y : St, stForm x y = 0) : x = 0 :=
  stForm_nondeg_aux x fun i => by
    have := hx ⟨stBasisMat i, by revert i; decide⟩
    rwa [stForm_apply] at this

theorem stForm_conj (g : Γ) (x y : St) : stForm (ρSt g x) (ρSt g y) = stForm x y := by
  rw [stForm_apply, stForm_apply]
  show ((g • x : St).1 * (g • y : St).1).trace = (x.1 * y.1).trace
  rw [coe_smul_st, coe_smul_st]
  set a : Matrix (Fin 3) (Fin 3) (ZMod 2) := (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) with ha
  set b : Matrix (Fin 3) (Fin 3) (ZMod 2) := ((g⁻¹ : Γ) : Matrix (Fin 3) (Fin 3) (ZMod 2))
    with hb
  have h1 : b * a = 1 := by
    rw [ha, hb, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have e : a * x.1 * b * (a * y.1 * b) = a * (x.1 * y.1) * b := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc b, h1, Matrix.one_mul]
  rw [e, ha, hb, trace_conj]

theorem stE13_ne : stE13 ≠ 0 := by decide

theorem stE13_fix_bel : ∀ i : Fin 8, bel i • stE13 = stE13 := by decide +kernel

theorem st_fix_bel_eq : ∀ m : St, m ≠ 0 → (∀ i : Fin 8, bel i • m = m) → m = stE13 := by
  decide +kernel

theorem st_stab_E13 : ∀ g : Γ, g • stE13 = stE13 → g ∈ borel := by decide +kernel

theorem st_fix_borel : ∃ m : St, m ≠ 0 ∧ (∀ t ∈ borel, ρSt t m = m) ∧
    ∀ m' : St, m' ≠ 0 → (∀ t ∈ borel, ρSt t m' = m') → m' = m := by
  refine ⟨stE13, stE13_ne, fun t ht => ?_, fun m' hm' hfix =>
    st_fix_bel_eq m' hm' fun i => hfix _ (bel_mem i)⟩
  obtain ⟨i, rfl⟩ := exists_bel t ht
  exact stE13_fix_bel i

theorem st_stabilizer (m : St) (hm : m ≠ 0) (hfix : ∀ t ∈ borel, ρSt t m = m) (g : Γ)
    (hg : ρSt g m = m) : g ∈ borel := by
  have e := st_fix_bel_eq m hm fun i => hfix _ (bel_mem i)
  subst e
  exact st_stab_E13 g hg

@[expose] def llA : Γ := ⟨!![0, 1, 0; 1, 1, 0; 0, 0, 1], by decide⟩

@[expose] def llB : Γ := ⟨!![0, 1, 0; 1, 1, 1; 0, 0, 1], by decide⟩

@[expose] def lpA : Γ := ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 1], by decide⟩

@[expose] def lpB : Γ := ⟨!![1, 0, 1; 0, 0, 1; 0, 1, 1], by decide⟩

theorem llA_mem : llA ∈ Ll := by decide
theorem llB_mem : llB ∈ Ll := by decide
theorem lpA_mem : lpA ∈ Lp := by decide
theorem lpB_mem : lpB ∈ Lp := by decide

@[expose] def llW1 (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![0, 0, 0; 0, 0, 0; A 2 0 + A 2 1 + A 0 0 + A 1 1, A 0 1 + A 1 0 + A 2 0 + A 1 1, 0]

@[expose] def llW2 (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![0, 0, A 1 2 + A 1 1; A 0 1, A 0 1 + A 0 0, A 0 1 + A 0 2 + A 1 2 + A 1 1;
    A 0 0 + A 1 1, A 0 1 + A 1 0 + A 1 1, A 0 1 + A 0 0]

@[expose] def lpW1 (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![0, 0, 0; A 1 2 + A 2 0 + A 2 1 + A 0 0 + A 2 2, 0, 0; A 1 0 + A 2 0 + A 0 0, 0, 0]

@[expose] def lpW2 (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![A 0 2 + A 2 2, 0, 0; A 1 2 + A 2 1 + A 0 0 + A 2 2, A 0 2 + A 0 1 + A 0 0, A 0 2 + A 1 2;
    A 0 0, A 0 2, A 0 1 + A 0 0 + A 2 2]

theorem st_comm_Ll_aux : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.trace = 0 →
    (llW1 A).trace = 0 ∧ (llW2 A).trace = 0 ∧
      A = ((llA : Matrix (Fin 3) (Fin 3) (ZMod 2)) * llW1 A *
          ((llA⁻¹ : Γ) : Matrix (Fin 3) (Fin 3) (ZMod 2)) - llW1 A) +
        ((llB : Matrix (Fin 3) (Fin 3) (ZMod 2)) * llW2 A *
          ((llB⁻¹ : Γ) : Matrix (Fin 3) (Fin 3) (ZMod 2)) - llW2 A) := by
  decide +kernel

theorem st_comm_Lp_aux : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.trace = 0 →
    (lpW1 A).trace = 0 ∧ (lpW2 A).trace = 0 ∧
      A = ((lpA : Matrix (Fin 3) (Fin 3) (ZMod 2)) * lpW1 A *
          ((lpA⁻¹ : Γ) : Matrix (Fin 3) (Fin 3) (ZMod 2)) - lpW1 A) +
        ((lpB : Matrix (Fin 3) (Fin 3) (ZMod 2)) * lpW2 A *
          ((lpB⁻¹ : Γ) : Matrix (Fin 3) (Fin 3) (ZMod 2)) - lpW2 A) := by
  decide +kernel

theorem st_comm_Ll :
    AddSubgroup.closure {y : St | ∃ g ∈ Ll, ∃ m : St, y = ρSt g m - m} = ⊤ := by
  refine eq_top_iff.mpr fun A _ => ?_
  obtain ⟨hB, hC, e⟩ := st_comm_Ll_aux A.1 (mem_stSub.mp A.2)
  have e' : A = (llA • (⟨_, hB⟩ : St) - ⟨_, hB⟩) + (llB • (⟨_, hC⟩ : St) - ⟨_, hC⟩) :=
    Subtype.ext e
  rw [e']
  exact add_mem (AddSubgroup.subset_closure ⟨llA, llA_mem, _, rfl⟩)
    (AddSubgroup.subset_closure ⟨llB, llB_mem, _, rfl⟩)

theorem st_comm_Lp :
    AddSubgroup.closure {y : St | ∃ g ∈ Lp, ∃ m : St, y = ρSt g m - m} = ⊤ := by
  refine eq_top_iff.mpr fun A _ => ?_
  obtain ⟨hB, hC, e⟩ := st_comm_Lp_aux A.1 (mem_stSub.mp A.2)
  have e' : A = (lpA • (⟨_, hB⟩ : St) - ⟨_, hB⟩) + (lpB • (⟨_, hC⟩ : St) - ⟨_, hC⟩) :=
    Subtype.ext e
  rw [e']
  exact add_mem (AddSubgroup.subset_closure ⟨lpA, lpA_mem, _, rfl⟩)
    (AddSubgroup.subset_closure ⟨lpB, lpB_mem, _, rfl⟩)

end CFSG.Quasithin.H6
