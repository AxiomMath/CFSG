module

public import CFSG.Quasithin.Background.G9StmtsModels

public section

namespace CFSG.Quasithin.SzN31

open CFSG.Quasithin.G11

abbrev M0 : Type := (ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)

@[expose] def q0 (x : M0) : ZMod 2 := (if x.1 = 0 then 0 else 1) + (if x.2 = 0 then 0 else 1)

@[expose] def B0 (x y : M0) : ZMod 2 :=
  x.1.1 * y.1.2 + x.1.2 * y.1.1 + x.2.1 * y.2.2 + x.2.2 * y.2.1

theorem q0_add : ∀ x y : M0, q0 (x + y) = q0 x + q0 y + B0 x y := by
  unfold q0 B0
  decide

theorem B0_eq : ∀ x y : M0, B0 x y = q0 (x + y) + q0 x + q0 y := by
  unfold q0 B0
  decide

theorem q0_smul : ∀ (c : ZMod 2) (x : M0), q0 (c • x) = c * c * q0 x := by
  unfold q0
  decide

theorem q0_eq_one_iff : ∀ x : M0, q0 x = 1 ↔ x ≠ 0 ∧ (x.1 = 0 ∨ x.2 = 0) := by
  unfold q0
  decide

theorem q0_eq_zero_or_one : ∀ x : M0, q0 x = 0 ∨ q0 x = 1 := by
  unfold q0
  decide

theorem q0_diag : ∀ w : ZMod 2 × ZMod 2, q0 (w, w) = 0 := by
  unfold q0
  decide

theorem B0_add_left : ∀ x x' y : M0, B0 (x + x') y = B0 x y + B0 x' y := by
  unfold B0
  decide

theorem B0_add_right : ∀ x y y' : M0, B0 x (y + y') = B0 x y + B0 x y' := by
  unfold B0
  decide

theorem B0_smul_left : ∀ (c : ZMod 2) (x y : M0), B0 (c • x) y = c • B0 x y := by
  unfold B0
  decide

theorem B0_smul_right : ∀ (c : ZMod 2) (x y : M0), B0 x (c • y) = c • B0 x y := by
  unfold B0
  decide

theorem B0_nondeg : ∀ x : M0, (∀ y : M0, B0 x y = 0) → x = 0 := by
  unfold B0
  decide

@[expose] def B0f : LinearMap.BilinForm (ZMod 2) M0 :=
  LinearMap.mk₂ (ZMod 2) B0 B0_add_left B0_smul_left B0_add_right B0_smul_right

theorem isPlusQuadForm_comp {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (Ψ : V ≃ₗ[ZMod 2] M0) : IsPlusQuadForm (fun v => q0 (Ψ v)) := by
  refine ⟨B0f.compl₁₂ Ψ.toLinearMap Ψ.toLinearMap, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have h0 : Ψ v = 0 := by
      refine B0_nondeg _ fun y => ?_
      have := hv (Ψ.symm y)
      simpa [B0f, LinearMap.mk₂_apply] using this
    simpa using h0
  · intro v w
    simp only [map_add, LinearMap.compl₁₂_apply, B0f, LinearMap.mk₂_apply]
    exact q0_add _ _
  · intro c v
    simp only [map_smul]
    exact q0_smul c _
  · let S₀ : Submodule (ZMod 2) M0 :=
      LinearMap.range (LinearMap.prod (LinearMap.id : (ZMod 2 × ZMod 2) →ₗ[ZMod 2] _) LinearMap.id)
    have hS₀ : Module.finrank (ZMod 2) S₀ = 2 := by
      have hinj : Function.Injective
          (LinearMap.prod (LinearMap.id : (ZMod 2 × ZMod 2) →ₗ[ZMod 2] _) LinearMap.id) := by
        intro a b h
        exact congrArg Prod.fst h
      rw [LinearMap.finrank_range_of_inj hinj]
      simp [Module.finrank_prod]
    refine ⟨S₀.map Ψ.symm.toLinearMap, ?_, ?_⟩
    · rw [LinearEquiv.finrank_map_eq, hS₀, LinearEquiv.finrank_eq Ψ]
      simp [Module.finrank_prod]
    · intro s hs
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hs
      obtain ⟨w, rfl⟩ := hx
      simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      exact q0_diag w

@[expose] def e1 : M0 := ((1, 0), (0, 0))

@[expose] def e2 : M0 := ((0, 1), (0, 0))

@[expose] def e3 : M0 := ((0, 0), (1, 0))

@[expose] def e4 : M0 := ((0, 0), (0, 1))

theorem M0_eq_span :
    ∀ x : M0, x = x.1.1 • e1 + x.1.2 • e2 + x.2.1 • e3 + x.2.2 • e4 := by
  unfold e1 e2 e3 e4
  decide

@[expose] def F12 : Finset (M0 × M0) :=
  Finset.univ.filter fun p => q0 p.1 = 1 ∧ q0 p.2 = 1 ∧ q0 (p.1 + p.2) = 1 ∧ p.1 ≠ p.2

@[expose] def Fall : Finset ((M0 × M0) × (M0 × M0)) :=
  (F12 ×ˢ F12).filter fun t =>
    B0 t.1.1 t.2.1 = 0 ∧ B0 t.1.1 t.2.2 = 0 ∧ B0 t.1.2 t.2.1 = 0 ∧ B0 t.1.2 t.2.2 = 0

theorem Fall_card : Fall.card = 72 := by
  unfold Fall F12 q0 B0
  decide

theorem isometry_tuple_mem (T : M0 ≃ₗ[ZMod 2] M0) (hT : ∀ x, q0 (T x) = q0 x) :
    ((T e1, T e2), (T e3, T e4)) ∈ Fall := by
  have hB : ∀ x y, B0 (T x) (T y) = B0 x y := by
    intro x y
    rw [B0_eq, B0_eq, ← map_add, hT, hT, hT]
  have q1 : q0 e1 = 1 := by unfold q0 e1; decide
  have q2 : q0 e2 = 1 := by unfold q0 e2; decide
  have q3 : q0 e3 = 1 := by unfold q0 e3; decide
  have q4 : q0 e4 = 1 := by unfold q0 e4; decide
  have q12 : q0 (e1 + e2) = 1 := by unfold q0 e1 e2; decide
  have q34 : q0 (e3 + e4) = 1 := by unfold q0 e3 e4; decide
  have n12 : e1 ≠ e2 := by unfold e1 e2; decide
  have n34 : e3 ≠ e4 := by unfold e3 e4; decide
  have b13 : B0 e1 e3 = 0 := by unfold B0 e1 e3; decide
  have b14 : B0 e1 e4 = 0 := by unfold B0 e1 e4; decide
  have b23 : B0 e2 e3 = 0 := by unfold B0 e2 e3; decide
  have b24 : B0 e2 e4 = 0 := by unfold B0 e2 e4; decide
  simp only [Fall, F12, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
  refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩, ?_, ?_, ?_, ?_⟩
  · rw [hT, q1]
  · rw [hT, q2]
  · rw [← map_add, hT, q12]
  · exact fun h => n12 (T.injective h)
  · rw [hT, q3]
  · rw [hT, q4]
  · rw [← map_add, hT, q34]
  · exact fun h => n34 (T.injective h)
  · rw [hB, b13]
  · rw [hB, b14]
  · rw [hB, b23]
  · rw [hB, b24]

theorem equiv_eq_of_tuple (T T' : M0 ≃ₗ[ZMod 2] M0) (h1 : T e1 = T' e1) (h2 : T e2 = T' e2)
    (h3 : T e3 = T' e3) (h4 : T e4 = T' e4) : T = T' := by
  refine LinearEquiv.ext fun x => ?_
  rw [M0_eq_span x]
  simp only [map_add, map_smul, h1, h2, h3, h4]

theorem card_orthogonal_le {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (Ψ : V ≃ₗ[ZMod 2] M0) : Nat.card (orthogonalSubgroupOf (fun v => q0 (Ψ v))) ≤ 72 := by
  let conj : (V ≃ₗ[ZMod 2] V) → (M0 ≃ₗ[ZMod 2] M0) := fun g => Ψ.symm.trans (g.trans Ψ)
  have hconj : ∀ g x, conj g x = Ψ (g (Ψ.symm x)) := fun g x => rfl
  have hmem : ∀ g : orthogonalSubgroupOf (fun v => q0 (Ψ v)),
      ((conj g.1 e1, conj g.1 e2), (conj g.1 e3, conj g.1 e4)) ∈ Fall := by
    intro g
    apply isometry_tuple_mem
    intro x
    have hg : ∀ v, q0 (Ψ (g.1 v)) = q0 (Ψ v) := g.2
    rw [hconj, hg, LinearEquiv.apply_symm_apply]
  let Φ : orthogonalSubgroupOf (fun v => q0 (Ψ v)) → ↥Fall := fun g => ⟨_, hmem g⟩
  have hinj : Function.Injective Φ := by
    intro g g' h
    have h' : ((conj g.1 e1, conj g.1 e2), (conj g.1 e3, conj g.1 e4)) =
        ((conj g'.1 e1, conj g'.1 e2), (conj g'.1 e3, conj g'.1 e4)) := congrArg Subtype.val h
    simp only [Prod.mk.injEq] at h'
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h'
    have hT := equiv_eq_of_tuple _ _ h1 h2 h3 h4
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    have h5 := DFunLike.congr_fun hT (Ψ v)
    rw [hconj, hconj, LinearEquiv.symm_apply_apply] at h5
    exact Ψ.injective h5
  calc Nat.card (orthogonalSubgroupOf (fun v => q0 (Ψ v))) ≤ Nat.card ↥Fall :=
        Nat.card_le_card_of_injective Φ hinj
    _ = 72 := by rw [Nat.card_eq_fintype_card, Fintype.card_coe, Fall_card]

end CFSG.Quasithin.SzN31
