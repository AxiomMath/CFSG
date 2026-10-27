module

public import CFSG.RankThree.PartOne.KF1514B.AbsThompson
public import CFSG.RankThree.PartOne.KF1514B.Thompson
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailSubspaceCount

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.KF1514B

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin QuadraticMap Matrix

section Chain

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem symm_mem_of_forall (e : V ≃ₗ[K] V) (W : Submodule K V) (h : ∀ w ∈ W, e w ∈ W) :
    ∀ w ∈ W, e.symm w ∈ W := by
  have hle : W.map (e : V →ₗ[K] V) ≤ W := Submodule.map_le_iff_le_comap.2 fun w hw => h w hw
  have heq : W.map (e : V →ₗ[K] V) = W :=
    Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq e W)
  intro w hw
  rw [← heq] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  simpa using hu

theorem map_eq_of_forall (e : V ≃ₗ[K] V) (W : Submodule K V) (h : ∀ w ∈ W, e w ∈ W) :
    W.map (e : V →ₗ[K] V) = W :=
  Submodule.eq_of_le_of_finrank_eq (Submodule.map_le_iff_le_comap.2 fun w hw => h w hw)
    (LinearEquiv.finrank_map_eq e W)

variable (W₁ W₂ W₃ : Submodule K V) (h12 : W₁ ≤ W₂) (h23 : W₂ ≤ W₃)

def chainGroup : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | (∀ w ∈ W₁, g w = w) ∧ (∀ w ∈ W₂, g w - w ∈ W₁) ∧ (∀ w ∈ W₃, g w - w ∈ W₂)}
  one_mem' := ⟨fun _ _ => rfl, fun w _ => by simp, fun w _ => by simp⟩
  mul_mem' := by
    rintro g h ⟨ga, gb, gc⟩ ⟨ha, hb, hc⟩
    have gp2 : ∀ w ∈ W₂, g w ∈ W₂ := fun w hw => by
      have := W₂.add_mem hw (h12 (gb w hw))
      simpa using this
    refine ⟨fun w hw => ?_, fun w hw => ?_, fun w hw => ?_⟩
    · rw [LinearEquiv.mul_apply, ha w hw, ga w hw]
    · have e1 := hb w hw
      have e2 := ga _ e1
      rw [map_sub] at e2
      have : (g * h) w - w = (h w - w) + (g w - w) := by
        rw [LinearEquiv.mul_apply]
        have : g (h w) = h w - w + g w := by
          have e3 : g (h w) - g w = h w - w := e2
          rw [← e3]; abel
        rw [this]; abel
      rw [this]
      exact W₁.add_mem e1 (gb w hw)
    · have e1 := hc w hw
      have e2 : g (h w - w) ∈ W₂ := gp2 _ e1
      rw [map_sub] at e2
      have : (g * h) w - w = (g (h w) - g w) + (g w - w) := by
        rw [LinearEquiv.mul_apply]; abel
      rw [this]
      exact W₂.add_mem e2 (gc w hw)
  inv_mem' := by
    rintro g ⟨ga, gb, gc⟩
    have gp2 : ∀ w ∈ W₂, g w ∈ W₂ := fun w hw => by
      have := W₂.add_mem hw (h12 (gb w hw))
      simpa using this
    have gp3 : ∀ w ∈ W₃, g w ∈ W₃ := fun w hw => by
      have := W₃.add_mem hw (h23 (gc w hw))
      simpa using this
    have gs2 := symm_mem_of_forall g W₂ gp2
    have gs3 := symm_mem_of_forall g W₃ gp3
    refine ⟨fun w hw => ?_, fun w hw => ?_, fun w hw => ?_⟩
    · have h1 := ga w hw
      show g.symm w = w
      calc g.symm w = g.symm (g w) := by rw [h1]
        _ = w := LinearEquiv.symm_apply_apply g w
    · have hu := gs2 w hw
      have := gb _ hu
      have e : g (g.symm w) = w := LinearEquiv.apply_symm_apply g w
      rw [e] at this
      have h3 := W₁.neg_mem this
      have : g⁻¹ w - w = -(w - g.symm w) := by
        show g.symm w - w = -(w - g.symm w)
        abel
      rw [this]
      exact h3
    · have hu := gs3 w hw
      have := gc _ hu
      have e : g (g.symm w) = w := LinearEquiv.apply_symm_apply g w
      rw [e] at this
      have h3 := W₂.neg_mem this
      have : g⁻¹ w - w = -(w - g.symm w) := by
        show g.symm w - w = -(w - g.symm w)
        abel
      rw [this]
      exact h3

variable {W₁ W₂ W₃ h12 h23}

theorem mem_chainGroup {g : V ≃ₗ[K] V} :
    g ∈ chainGroup W₁ W₂ W₃ h12 h23 ↔
      (∀ w ∈ W₁, g w = w) ∧ (∀ w ∈ W₂, g w - w ∈ W₁) ∧ (∀ w ∈ W₃, g w - w ∈ W₂) := Iff.rfl

theorem conj_mem_chainGroup {g n : V ≃ₗ[K] V} (hg : g ∈ chainGroup W₁ W₂ W₃ h12 h23)
    (n1 : ∀ w ∈ W₁, n w ∈ W₁) (n2 : ∀ w ∈ W₂, n w ∈ W₂) (n3 : ∀ w ∈ W₃, n w ∈ W₃) :
    n * g * n⁻¹ ∈ chainGroup W₁ W₂ W₃ h12 h23 := by
  obtain ⟨ga, gb, gc⟩ := hg
  have s1 := symm_mem_of_forall n W₁ n1
  have s2 := symm_mem_of_forall n W₂ n2
  have s3 := symm_mem_of_forall n W₃ n3
  have key : ∀ w, (n * g * n⁻¹) w = n (g (n.symm w)) := fun w => rfl
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · rw [key, ga _ (s1 w hw)]
    exact LinearEquiv.apply_symm_apply n w
  · rw [key]
    have := n1 _ (gb _ (s2 w hw))
    rw [map_sub, LinearEquiv.apply_symm_apply] at this
    exact this
  · rw [key]
    have := n2 _ (gc _ (s3 w hw))
    rw [map_sub, LinearEquiv.apply_symm_apply] at this
    exact this

end Chain

section Specific

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c]

@[expose] def Wy (K : Type) [Field K] : Submodule K (Vt K) where
  carrier := {v | ∀ i, v.1 (Sum.inr i) = 0}
  add_mem' := fun {a b} ha hb i => by simp [ha i, hb i]
  zero_mem' := fun i => rfl
  smul_mem' := fun t v hv i => by simp [hv i]

noncomputable abbrev W1 (K : Type) [Field K] : Submodule K (Vt K) :=
  tailFlag K (Fin 2 → K) 3 1

noncomputable abbrev W2 (K : Type) [Field K] : Submodule K (Vt K) :=
  tailFlag K (Fin 2 → K) 3 3

noncomputable abbrev G0 (b c : K) : Subgroup (Vt K ≃ₗ[K] Vt K) :=
  orthElementaryGroup (quadTail 3 (minusTailForm K b c))

theorem mem_W2 {v : Vt K} : v ∈ W2 K ↔ (∀ j, v.1 (Sum.inr j) = 0) ∧ v.2 = 0 :=
  mem_tailFlag_top_iff

theorem mem_W1 {v : Vt K} : v ∈ W1 K ↔ (∀ j, v.1 (Sum.inr j) = 0) ∧
    (∀ j : Fin 3, 1 ≤ (j : ℕ) → v.1 (Sum.inl j) = 0) ∧ v.2 = 0 := by
  rw [mem_tailFlag_iff, mem_flag]
  tauto

theorem W1_le_W2 : W1 K ≤ W2 K := fun _ hv => by
  obtain ⟨h1, -, h3⟩ := (mem_W1 (K := K)).1 hv
  exact mem_W2.2 ⟨h1, h3⟩

theorem W2_le_Wy : W2 K ≤ Wy K := fun _ hv => (mem_W2 (K := K)).1 hv |>.1

theorem hypVec_inl_mem_W2 (i : Fin 3) : hypVec K (Fin 2 → K) (Sum.inl i) ∈ W2 K :=
  mem_W2.2 ⟨fun j => by simp [hypVec], rfl⟩

theorem mem_Wy_iff_polar (b c : K) {v : Vt K} :
    v ∈ Wy K ↔ ∀ u ∈ W2 K, polar (quadTail 3 (minusTailForm K b c)) v u = 0 := by
  constructor
  · intro hv u hu
    obtain ⟨hu1, hu2⟩ := (mem_W2 (K := K)).1 hu
    rw [polar_quadTail, hu2, polar_zero_right, add_zero, polar_quadPlus]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hu1 i]
    have : v.1 (Sum.inr i) = 0 := hv i
    rw [this]
    ring
  · intro h i
    have := h _ (hypVec_inl_mem_W2 i)
    rw [polar_hypVec] at this
    exact this

theorem polar_map_of_mem_orth {Q : QuadraticForm K (Vt K)} {n : Vt K ≃ₗ[K] Vt K}
    (hn : n ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (v w : Vt K) :
    polar Q (n v) (n w) = polar Q v w := by
  have h := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hn
  simp only [QuadraticMap.polar, ← map_add, h]

variable (b c) in
@[expose] noncomputable def P13 : Subgroup (Vt K ≃ₗ[K] Vt K) where
  carrier := {n | n ∈ G0 b c ∧ (∀ w ∈ W1 K, n w ∈ W1 K) ∧ (∀ w ∈ W2 K, n w ∈ W2 K)}
  one_mem' := ⟨one_mem _, fun _ h => h, fun _ h => h⟩
  mul_mem' := by
    rintro n m ⟨hn, n1, n2⟩ ⟨hm, m1, m2⟩
    exact ⟨mul_mem hn hm, fun w hw => by rw [LinearEquiv.mul_apply]; exact n1 _ (m1 w hw),
      fun w hw => by rw [LinearEquiv.mul_apply]; exact n2 _ (m2 w hw)⟩
  inv_mem' := by
    rintro n ⟨hn, n1, n2⟩
    exact ⟨inv_mem hn, symm_mem_of_forall n _ n1, symm_mem_of_forall n _ n2⟩

variable (b c) in
@[expose] noncomputable def Rgeom : Subgroup (Vt K ≃ₗ[K] Vt K) :=
  G0 b c ⊓ chainGroup (W1 K) (W2 K) (Wy K) W1_le_W2 W2_le_Wy

theorem mem_Rgeom {g : Vt K ≃ₗ[K] Vt K} :
    g ∈ Rgeom b c ↔ g ∈ G0 b c ∧ (∀ w ∈ W1 K, g w = w) ∧ (∀ w ∈ W2 K, g w - w ∈ W1 K) ∧
      (∀ w ∈ Wy K, g w - w ∈ W2 K) := by
  rw [Rgeom, Subgroup.mem_inf, mem_chainGroup]

theorem P13_preserves_Wy {n : Vt K ≃ₗ[K] Vt K} (hn : n ∈ P13 b c) : ∀ w ∈ Wy K, n w ∈ Wy K := by
  obtain ⟨hnG, n1, n2⟩ := hn
  have hnO := orthElementaryGroup_le _ hnG
  intro w hw
  rw [mem_Wy_iff_polar b c] at hw ⊢
  intro u hu
  have hu' := symm_mem_of_forall n _ n2 u hu
  have := polar_map_of_mem_orth hnO w (n.symm u)
  rw [LinearEquiv.apply_symm_apply] at this
  rw [this]
  exact hw _ hu'

theorem P13_le_normalizer_Rgeom : P13 b c ≤ Subgroup.normalizer (Rgeom b c : Set (Vt K ≃ₗ[K] Vt K)) := by
  have key : ∀ n ∈ P13 b c, ∀ g ∈ Rgeom b c, n * g * n⁻¹ ∈ Rgeom b c := by
    intro n hn g hg
    obtain ⟨hgG, hgC⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨hnG, n1, n2⟩ := hn
    exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hnG hgG) (inv_mem hnG),
      conj_mem_chainGroup hgC n1 n2 (P13_preserves_Wy ⟨hnG, n1, n2⟩)⟩
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key n hn g, fun hg => ?_⟩
  have := key n⁻¹ (inv_mem hn) _ hg
  simpa [mul_assoc] using this

theorem U0_apply_of_inr_zero (g : ↥(U0 b c)) (v : Vt K) (hy : ∀ i, v.1 (Sum.inr i) = 0) :
    (∀ i, ((g : Vt K ≃ₗ[K] Vt K) v).1 (Sum.inr i) = 0) ∧ ((g : Vt K ≃ₗ[K] Vt K) v).2 = v.2 ∧
      ∀ i : Fin 3, ((g : Vt K ≃ₗ[K] Vt K) v).1 (Sum.inl i) =
        ∑ j, (Dm g : Matrix (Fin 3) (Fin 3) K) i j *
          (v.1 (Sum.inl j) - polar (minusTailForm K b c) (Lp g j) v.2) := by
  have e := (par_spec g).eq
  have hy' : v.1 ∘ Sum.inr = 0 := funext hy
  have hu1 : ∀ i, (uLin (minusTailForm K b c) (Lp g) (Cp g) v).1 (Sum.inl i) =
      v.1 (Sum.inl i) - polar (minusTailForm K b c) (Lp g i) v.2 := by
    intro i
    rw [uLin_apply_inl, hy', mulVec_zero]
    simp
  have hu2 : (uLin (minusTailForm K b c) (Lp g) (Cp g) v).2 = v.2 := by
    rw [uLin_apply_snd]
    simp [hy]
  have hu3 : (uLin (minusTailForm K b c) (Lp g) (Cp g) v).1 ∘ Sum.inr = 0 :=
    funext fun i => (uLin_apply_inr _ _ v i).trans (hy i)
  rw [e, LinearEquiv.mul_apply, uMap_apply, dMap_apply]
  refine ⟨fun i => ?_, ?_, fun i => ?_⟩
  · simp only [Sum.elim_inr, hu3, mulVec_zero, Pi.zero_apply]
  · simp only [hu2]
    rfl
  · simp only [Sum.elim_inl, mulVec, dotProduct, Function.comp_apply, hu1]

theorem mem_Rgeom_of_db_zero (g : ↥(U0 b c)) (hg : db g = 0) :
    (g : Vt K ≃ₗ[K] Vt K) ∈ Rgeom b c := by
  have hD1 : (Dm g : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := Dm_lower g (show (0 : Fin 3) < 1 by decide)
  have hD2 : (Dm g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := Dm_lower g (show (0 : Fin 3) < 2 by decide)
  have hD3 : (Dm g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := Dm_lower g (show (1 : Fin 3) < 2 by decide)
  have hd0 := Dm_diag g 0
  have hd1 := Dm_diag g 1
  have hd2 := Dm_diag g 2
  have hD12 : (Dm g : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := hg
  refine mem_Rgeom.2 ⟨tailUnipotent_le g.2, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨h1, h2, h3⟩ := mem_W1.1 hw
    obtain ⟨hy1, hy2, hy3⟩ := U0_apply_of_inr_zero g w h1
    have h21 := h2 1 (by decide)
    have h22 := h2 2 (by decide)
    refine Prod.ext (funext fun c' => ?_) (by rw [hy2])
    rcases c' with i | i
    · show ((g : Vt K ≃ₗ[K] Vt K) w).1 (Sum.inl i) = w.1 (Sum.inl i)
      rw [hy3 i, h3]
      fin_cases i <;> simp [Fin.sum_univ_three, h21, h22, hD1, hD2, hd0, hd1, hd2]
    · exact (hy1 i).trans (h1 i).symm
  · intro w hw
    obtain ⟨h1, h3⟩ := mem_W2.1 hw
    obtain ⟨hy1, hy2, hy3⟩ := U0_apply_of_inr_zero g w h1
    refine mem_W1.2 ⟨fun i => ?_, fun j hj => ?_, ?_⟩
    · show ((g : Vt K ≃ₗ[K] Vt K) w).1 (Sum.inr i) - w.1 (Sum.inr i) = 0
      rw [hy1 i, h1 i, sub_zero]
    · show ((g : Vt K ≃ₗ[K] Vt K) w).1 (Sum.inl j) - w.1 (Sum.inl j) = 0
      rw [hy3 j, h3]
      fin_cases j
      · exact absurd hj (by decide)
      · simp [Fin.sum_univ_three, hD1, hD12, hd1]
      · simp [Fin.sum_univ_three, hD2, hD3, hd2]
    · show ((g : Vt K ≃ₗ[K] Vt K) w).2 - w.2 = 0
      rw [hy2, sub_self]
  · intro w hw
    obtain ⟨hy1, hy2, hy3⟩ := U0_apply_of_inr_zero g w hw
    refine mem_W2.2 ⟨fun i => ?_, ?_⟩
    · show ((g : Vt K ≃ₗ[K] Vt K) w).1 (Sum.inr i) - w.1 (Sum.inr i) = 0
      rw [hy1 i, hw i, sub_zero]
    · show ((g : Vt K ≃ₗ[K] Vt K) w).2 - w.2 = 0
      rw [hy2, sub_self]

theorem tailFlag_one_le {i : ℕ} (hi : 1 ≤ i) : W1 K ≤ tailFlag K (Fin 2 → K) 3 i := fun v hv => by
  obtain ⟨h1, h2, h3⟩ := (mem_W1 (K := K)).1 hv
  rw [mem_tailFlag_iff, mem_flag]
  exact ⟨⟨h1, fun j hj => h2 j (le_trans hi hj)⟩, h3⟩

theorem tailFlag_le_three {i : ℕ} : tailFlag K (Fin 2 → K) 3 i ≤ W2 K := fun v hv => by
  rw [mem_tailFlag_iff, mem_flag] at hv
  exact mem_W2.2 ⟨hv.1.1, hv.2⟩

theorem Rgeom_le_U0 : Rgeom b c ≤ U0 b c := by
  intro g hg
  obtain ⟨hgG, ha, hb', hc'⟩ := mem_Rgeom.1 hg
  have hani := anisotropic_minusTailForm (AnisoPair.hirr (b := b) (c := c))
  show g ∈ tailUnipotent 3 (minusTailForm K b c)
  rw [mem_tailUnipotent_iff_ker hani]
  have hflag : g ∈ tailFlagStab 3 (minusTailForm K b c) := by
    rw [mem_tailFlagStab]
    refine ⟨orthElementaryGroup_le _ hgG, fun i hi1 _ => ?_⟩
    refine map_eq_of_forall g _ fun w hw => ?_
    have hw3 : w ∈ W2 K := tailFlag_le_three hw
    have h1 := tailFlag_one_le (K := K) hi1 (hb' w hw3)
    have := Submodule.add_mem _ hw h1
    simpa using this
  refine ⟨hflag, ?_⟩
  rw [stabDiagHom_apply]
  change stabDiag g = 1
  refine Prod.ext (funext fun i => ?_) (LinearMap.ext fun a => ?_)
  · have hmem : hypVec K (Fin 2 → K) (Sum.inl i) ∈ W2 K := hypVec_inl_mem_W2 i
    change (g (hypVec K (Fin 2 → K) (Sum.inl i))).1 (Sum.inl i) = 1
    by_cases hi : (i : ℕ) = 0
    · have hmem1 : hypVec K (Fin 2 → K) (Sum.inl i) ∈ W1 K := by
        refine mem_W1.2 ⟨fun j => by simp [hypVec], fun j hj => ?_, rfl⟩
        have : j ≠ i := fun h => by subst h; omega
        simp [hypVec, this.symm]
      rw [ha _ hmem1]
      simp [hypVec]
    · have h1 := (mem_W1 (K := K)).1 (hb' _ hmem)
      have := h1.2.1 i (by omega)
      have e : (g (hypVec K (Fin 2 → K) (Sum.inl i)) - hypVec K (Fin 2 → K) (Sum.inl i)).1 (Sum.inl i) =
          (g (hypVec K (Fin 2 → K) (Sum.inl i))).1 (Sum.inl i) - 1 := by
        simp [hypVec]
      rw [e] at this
      exact sub_eq_zero.1 this
  · change (g ((0 : Fin 3 ⊕ Fin 3 → K), a)).2 = a
    have hmem : ((0 : Fin 3 ⊕ Fin 3 → K), a) ∈ Wy K := fun i => rfl
    have h2 := (mem_W2 (K := K)).1 (hc' _ hmem)
    have : (g ((0 : Fin 3 ⊕ Fin 3 → K), a) - ((0 : Fin 3 ⊕ Fin 3 → K), a)).2 =
        (g ((0 : Fin 3 ⊕ Fin 3 → K), a)).2 - a := rfl
    rw [this] at h2
    exact sub_eq_zero.1 h2.2

theorem P13_le_normalizer_pushingUpS :
    P13 b c ≤ Subgroup.normalizer (pushingUpS (U0 b c) : Set (Vt K ≃ₗ[K] Vt K)) := by
  have hfam : ∀ A ∈ elemThompsonFamily ↥(U0 b c) 2, A.map (U0 b c).subtype ≤ Rgeom b c := by
    rintro A hA _ ⟨a, ha, rfl⟩
    exact mem_Rgeom_of_db_zero a (db_eq_zero_of_mem_family hA a ha)
  have hS : pushingUpS (U0 b c) ≤ Rgeom b c := by
    intro s hs
    have hsT : s ∈ U0 b c := hs.1
    have hsC : s ∈ Subgroup.centralizer
        (((elemThompsonCenterTorsion ↥(U0 b c) 2).map (U0 b c).subtype : Subgroup _) :
          Set (Vt K ≃ₗ[K] Vt K)) := hs.2
    have hcent : (⟨s, hsT⟩ : ↥(U0 b c)) ∈ Subgroup.centralizer
        (elemThompsonCenterTorsion ↥(U0 b c) 2 : Set ↥(U0 b c)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hsC _ ⟨z, hz, rfl⟩).symm.symm
    exact mem_Rgeom_of_db_zero ⟨s, hsT⟩ (db_eq_zero_of_mem_centralizer_E hcent)
  exact P13_le_normalizer_Rgeom.trans
    (normalizer_le_normalizer_pushingUpS Rgeom_le_U0 hfam hS)

end Specific

end CFSG.RankThree.PartOne.KF1514B
