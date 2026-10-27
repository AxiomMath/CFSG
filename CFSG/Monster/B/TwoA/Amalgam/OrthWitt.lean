module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailFlagTransitivity
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelCoordinates
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherIncidenceGraph
public import CFSG.Monster.B.TwoA.Sp8.QuadForm
public import CFSG.Monster.B.TwoA.Sp8.GenActionHomBase

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open QuadraticMap Module CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.Monster.B.TwoA.Sp8

section Transport

variable {K V₁ V₂ : Type*} [Field K] [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂]
  [Module K V₂] {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}

theorem singular_map_iff (e : Q₁.IsometryEquiv Q₂) {X : Submodule K V₁} :
    (∀ y ∈ X.map (e.toLinearEquiv : V₁ →ₗ[K] V₂), Q₂ y = 0) ↔ ∀ x ∈ X, Q₁ x = 0 := by
  constructor
  · intro h x hx
    rw [← e.map_app]
    exact h _ ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    exact (e.map_app x).trans (h x hx)

theorem map_mem_singularSubspaces_iff (e : Q₁.IsometryEquiv Q₂) {k : ℕ} {X : Submodule K V₁} :
    X.map (e.toLinearEquiv : V₁ →ₗ[K] V₂) ∈ singularSubspaces Q₂ k ↔
      X ∈ singularSubspaces Q₁ k := by
  rw [mem_singularSubspaces, mem_singularSubspaces, LinearEquiv.finrank_map_eq, singular_map_iff]

theorem monotone_map_iff (e : V₁ ≃ₗ[K] V₂) {k : ℕ} {W : Fin k → Submodule K V₁} :
    Monotone (fun i => (W i).map (e : V₁ →ₗ[K] V₂)) ↔ Monotone W :=
  ⟨fun h _ _ hij => (Submodule.map_le_map_iff_of_injective e.injective _ _).1 (h hij),
    fun h _ _ hij => Submodule.map_mono (h hij)⟩

theorem map_mem_singularFlags_iff (e : Q₁.IsometryEquiv Q₂) {k : ℕ}
    {W : Fin k → Submodule K V₁} :
    (fun i => (W i).map (e.toLinearEquiv : V₁ →ₗ[K] V₂)) ∈ singularFlags Q₂ k ↔
      W ∈ singularFlags Q₁ k := by
  simp only [mem_singularFlags, LinearEquiv.finrank_map_eq, singular_map_iff, monotone_map_iff]

theorem map_symm_map (e : V₁ ≃ₗ[K] V₂) (X : Submodule K V₂) :
    (X.map (e.symm : V₂ →ₗ[K] V₁)).map (e : V₁ →ₗ[K] V₂) = X := by
  rw [← Submodule.map_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
    LinearEquiv.refl_toLinearMap, Submodule.map_id]

@[expose] def conjIso (e : Q₁.IsometryEquiv Q₂) (g : V₁ ≃ₗ[K] V₁) : V₂ ≃ₗ[K] V₂ :=
  e.toLinearEquiv.symm.trans (g.trans e.toLinearEquiv)

theorem conjIso_mem (e : Q₁.IsometryEquiv Q₂) {g : V₁ ≃ₗ[K] V₁}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q₁) :
    conjIso e g ∈ TauCeti.QuadraticMap.orthogonalGroup Q₂ := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro x
  change Q₂ (e.toLinearEquiv (g (e.toLinearEquiv.symm x))) = Q₂ x
  rw [show Q₂ (e.toLinearEquiv (g (e.toLinearEquiv.symm x))) = Q₁ (g (e.toLinearEquiv.symm x))
    from e.map_app _, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg]
  conv_rhs => rw [← e.toLinearEquiv.apply_symm_apply x]
  exact (e.map_app _).symm

theorem map_conjIso (e : Q₁.IsometryEquiv Q₂) (g : V₁ ≃ₗ[K] V₁) (X : Submodule K V₂) :
    X.map (conjIso e g : V₂ →ₗ[K] V₂) =
      ((X.map (e.toLinearEquiv.symm : V₂ →ₗ[K] V₁)).map (g : V₁ →ₗ[K] V₁)).map
        (e.toLinearEquiv : V₁ →ₗ[K] V₂) := by
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  rfl

theorem exists_orth_map_flag_eq (e : Q₁.IsometryEquiv Q₂) {k : ℕ}
    (h : ∀ W ∈ singularFlags Q₁ k, ∀ W' ∈ singularFlags Q₁ k,
      ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q₁, ∀ i, (W i).map (g : V₁ →ₗ[K] V₁) = W' i)
    {W W' : Fin k → Submodule K V₂} (hW : W ∈ singularFlags Q₂ k)
    (hW' : W' ∈ singularFlags Q₂ k) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q₂, ∀ i, (W i).map (g : V₂ →ₗ[K] V₂) = W' i := by
  have hb : (fun i => (W i).map (e.symm.toLinearEquiv : V₂ →ₗ[K] V₁)) ∈ singularFlags Q₁ k :=
    (map_mem_singularFlags_iff e.symm).2 hW
  have hb' : (fun i => (W' i).map (e.symm.toLinearEquiv : V₂ →ₗ[K] V₁)) ∈ singularFlags Q₁ k :=
    (map_mem_singularFlags_iff e.symm).2 hW'
  obtain ⟨g, hg, hgW⟩ := h _ hb _ hb'
  refine ⟨conjIso e g, conjIso_mem e hg, fun i => ?_⟩
  rw [map_conjIso]
  exact (congrArg (Submodule.map (e.toLinearEquiv : V₁ →ₗ[K] V₂)) (hgW i)).trans
    (map_symm_map e.toLinearEquiv (W' i))

theorem natCard_singularSubspaces_congr (e : Q₁.IsometryEquiv Q₂) (k : ℕ) :
    Nat.card (singularSubspaces Q₁ k) = Nat.card (singularSubspaces Q₂ k) :=
  Nat.card_congr ((Submodule.orderIsoMapComap e.toLinearEquiv).toEquiv.subtypeEquiv
    fun _ => (map_mem_singularSubspaces_iff e).symm)

end Transport

section Through

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_flag_through {U X : Submodule K V} (hUX : U ≤ X) {j k : ℕ}
    (hU : finrank K U = j) (hX : finrank K X = k) (hj : 0 < j) (hjk : j ≤ k) :
    ∃ G : Fin k → Submodule K V, (∀ i, finrank K (G i) = i + 1) ∧ Monotone G ∧
      (∀ i, G i ≤ X) ∧ G ⟨j - 1, by omega⟩ = U ∧ G ⟨k - 1, by omega⟩ = X := by
  obtain ⟨C₁, hC₁m, hC₁b, hC₁d⟩ := LinearFlag.exists_chain_between j ⊥ U bot_le
    (by rw [finrank_bot, hU, zero_add])
  obtain ⟨C₂, hC₂m, hC₂b, hC₂d⟩ := LinearFlag.exists_chain_between (k - j) U X hUX
    (by rw [hU, hX]; omega)
  set G : Fin k → Submodule K V := fun i =>
    if (i : ℕ) + 1 ≤ j then C₁ ((i : ℕ) + 1) else C₂ ((i : ℕ) + 1 - j) with hGdef
  have hG1 : ∀ i : Fin k, (i : ℕ) + 1 ≤ j → G i = C₁ ((i : ℕ) + 1) := fun i h => ite_eq_left h
  have hG2 : ∀ i : Fin k, ¬(i : ℕ) + 1 ≤ j → G i = C₂ ((i : ℕ) + 1 - j) := fun i h =>
    ite_eq_right h
  have hGX : ∀ i, G i ≤ X := fun i => by
    by_cases h : (i : ℕ) + 1 ≤ j
    · rw [hG1 i h]
      exact (hC₁b _).2.trans hUX
    · rw [hG2 i h]
      exact (hC₂b _).2
  refine ⟨G, fun i => ?_, fun i i' hii' => ?_, hGX, ?_, ?_⟩
  · have hi := i.isLt
    by_cases h : (i : ℕ) + 1 ≤ j
    · rw [hG1 i h, hC₁d _ h, finrank_bot, zero_add]
    · rw [hG2 i h, hC₂d _ (by omega), hU]
      omega
  · have hle : (i : ℕ) ≤ i' := hii'
    by_cases h : (i : ℕ) + 1 ≤ j
    · rw [hG1 i h]
      by_cases h' : (i' : ℕ) + 1 ≤ j
      · rw [hG1 i' h']
        exact hC₁m (by omega)
      · rw [hG2 i' h']
        exact (hC₁b _).2.trans (hC₂b _).1
    · rw [hG2 i h, hG2 i' (by omega)]
      exact hC₂m (by omega)
  · rw [hG1 _ (by simp only; omega)]
    refine Submodule.eq_of_le_of_finrank_eq (hC₁b _).2 ?_
    rw [show j - 1 + 1 = j by omega, hC₁d _ le_rfl, finrank_bot, zero_add, hU]
  · refine Submodule.eq_of_le_of_finrank_eq (hGX _) ?_
    by_cases h : k - 1 + 1 ≤ j
    · rw [hG1 _ h, show k - 1 + 1 = j by omega, hC₁d _ le_rfl, finrank_bot, zero_add, hX]
      omega
    · rw [hG2 _ h, hC₂d _ (by simp only; omega), hU, hX]
      simp only
      omega

end Through

abbrev qTail2 : QuadraticForm (ZMod 2) (Fin 2 → ZMod 2) := minusTailForm (ZMod 2) 1 1

theorem sq_add_one_mul_add_one_ne_zero : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by
  decide

theorem anisotropic_qTail2 : qTail2.Anisotropic :=
  anisotropic_minusTailForm sq_add_one_mul_add_one_ne_zero

theorem nondegenerate_qTail2 : (polarBilin qTail2).Nondegenerate :=
  nondegenerate_minusTailForm sq_add_one_mul_add_one_ne_zero

theorem exists_ne_zero_fin_two : ∃ a : Fin 2 → ZMod 2, a ≠ 0 :=
  ⟨Pi.single 0 1, fun h => by simpa using congrFun h 0⟩

@[expose] def qTailIso : (quadTail (4 - 1) qTail2).IsometryEquiv qForm :=
  (minusTailIsometry 4 (ZMod 2) 1 1).trans isometryEquivQuadMinus.symm

theorem qForm_flag_transitive {k : ℕ} (hk : k ≤ 3) {W W' : Fin k → Submodule (ZMod 2) V8}
    (hW : W ∈ singularFlags qForm k) (hW' : W' ∈ singularFlags qForm k) :
    ∃ M ∈ TauCeti.QuadraticMap.orthogonalGroup qForm,
      ∀ i, (W i).map (M : V8 →ₗ[ZMod 2] V8) = W' i :=
  exists_orth_map_flag_eq qTailIso (fun _ hU _ hU' => by
    obtain ⟨g, hg, hgU⟩ := (orthogonal_geometry_tail_singular_flag_transitivity (r := 4 - 1)
      anisotropic_qTail2 exists_ne_zero_fin_two).1 k (by omega) _ hU _ hU'
    exact ⟨g, orthElementaryGroup_le _ hg, hgU⟩) hW hW'

theorem qForm_subspace_transitive {k : ℕ} (hk : k ≤ 3) {X X' : Submodule (ZMod 2) V8}
    (hX : X ∈ singularSubspaces qForm k) (hX' : X' ∈ singularSubspaces qForm k) :
    ∃ M ∈ TauCeti.QuadraticMap.orthogonalGroup qForm, X.map (M : V8 →ₗ[ZMod 2] V8) = X' := by
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · refine ⟨1, one_mem _, ?_⟩
    rw [Submodule.finrank_eq_zero.1 hX.1, Submodule.finrank_eq_zero.1 hX'.1, Submodule.map_bot]
  · obtain ⟨W, hW, hWX⟩ := exists_mem_singularFlags_eq hX hpos
    obtain ⟨W', hW', hWX'⟩ := exists_mem_singularFlags_eq hX' hpos
    obtain ⟨M, hM, hMW⟩ := qForm_flag_transitive hk hW hW'
    exact ⟨M, hM, by rw [← hWX, ← hWX', hMW]⟩

theorem qForm_pair_transitive {j k : ℕ} (hj : 0 < j) (hjk : j ≤ k) (hk : k ≤ 3)
    {U X U' X' : Submodule (ZMod 2) V8} (hUX : U ≤ X) (hUX' : U' ≤ X')
    (hU : finrank (ZMod 2) U = j) (hU' : finrank (ZMod 2) U' = j)
    (hX : X ∈ singularSubspaces qForm k) (hX' : X' ∈ singularSubspaces qForm k) :
    ∃ M ∈ TauCeti.QuadraticMap.orthogonalGroup qForm,
      U.map (M : V8 →ₗ[ZMod 2] V8) = U' ∧ X.map (M : V8 →ₗ[ZMod 2] V8) = X' := by
  obtain ⟨G, hGd, hGm, hGX, hGU, hGX'⟩ := exists_flag_through hUX hU hX.1 hj hjk
  obtain ⟨G', hGd', hGm', hGX₂, hGU', hGX₂'⟩ := exists_flag_through hUX' hU' hX'.1 hj hjk
  obtain ⟨M, hM, hMG⟩ := qForm_flag_transitive hk
    ⟨hGd, hGm, fun i x hx => hX.2 x (hGX i hx)⟩ ⟨hGd', hGm', fun i x hx => hX'.2 x (hGX₂ i hx)⟩
  exact ⟨M, hM, by rw [← hGU, ← hGU', hMG], by rw [← hGX', ← hGX₂', hMG]⟩

theorem finrank_le_three_of_singular {X : Submodule (ZMod 2) V8} (hX : ∀ x ∈ X, qForm x = 0) :
    finrank (ZMod 2) X ≤ 3 := by
  have h := finrank_le_of_totSing_tail (r := 4 - 1) anisotropic_qTail2
    ((singular_map_iff qTailIso.symm).2 hX)
  rw [LinearEquiv.finrank_map_eq] at h
  omega

theorem natCard_singularSubspaces_qForm_eq {k : ℕ} (hk : k ≤ 3) :
    (Nat.card (singularSubspaces qForm k) : ℚ) =
      (∏ j ∈ Finset.range k, (((2 : ℚ) ^ (3 - j) - 1) * ((2 : ℚ) ^ (3 + 2 - j - 1) + 1))) /
        ∏ i ∈ Finset.Icc 1 k, ((2 : ℚ) ^ i - 1) := by
  rw [← natCard_singularSubspaces_congr qTailIso,
    card_singularSubspaces_tail (r := 4 - 1) anisotropic_qTail2 nondegenerate_qTail2 (by omega),
    Nat.card_zmod,
    Module.finrank_fin_fun]
  norm_num

theorem natCard_singularSubspaces_qForm :
    Nat.card (singularSubspaces qForm 1) = 119 ∧ Nat.card (singularSubspaces qForm 2) = 1071 ∧
      Nat.card (singularSubspaces qForm 3) = 765 := by
  have h1 := natCard_singularSubspaces_qForm_eq (k := 1) (by norm_num)
  have h2 := natCard_singularSubspaces_qForm_eq (k := 2) (by norm_num)
  have h3 := natCard_singularSubspaces_qForm_eq (k := 3) (by norm_num)
  rw [show Finset.Icc 1 1 = {1} from rfl] at h1
  rw [show Finset.Icc 1 2 = {1, 2} from rfl] at h2
  rw [show Finset.Icc 1 3 = {1, 2, 3} from rfl] at h3
  norm_num [Finset.prod_range_succ] at h1 h2 h3
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩

end CFSG.Monster.B.TwoA.Amalgam
