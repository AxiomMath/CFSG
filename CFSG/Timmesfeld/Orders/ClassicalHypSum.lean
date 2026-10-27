module

public import CFSG.Timmesfeld.Orders.ClassicalTransitive
public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.Timmesfeld.ClassicalOrders

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]

variable (K) in
@[expose] noncomputable def hypPlane : QuadraticForm K (K × K) :=
  QuadraticMap.linMulLin (LinearMap.fst K K K) (LinearMap.snd K K K)

theorem hypPlane_apply (p : K × K) : hypPlane K p = p.1 * p.2 := rfl

@[expose] noncomputable def hypSum (Q' : QuadraticForm K W) : QuadraticForm K ((K × K) × W) :=
  (hypPlane K).prod Q'

theorem hypSum_apply (Q' : QuadraticForm K W) (p : (K × K) × W) :
    hypSum Q' p = p.1.1 * p.1.2 + Q' p.2 := rfl

theorem polar_hypSum (Q' : QuadraticForm K W) (p p' : (K × K) × W) :
    polar (hypSum Q') p p' = p.1.1 * p'.1.2 + p'.1.1 * p.1.2 + polar Q' p.2 p'.2 := by
  rw [hypSum, polar_prod]
  congr 1
  simp only [polar, hypPlane_apply, Prod.fst_add, Prod.snd_add]
  ring

theorem nondegenerate_polarBilin_hypSum {Q' : QuadraticForm K W}
    (hQ' : (polarBilin Q').Nondegenerate) : (polarBilin (hypSum Q')).Nondegenerate := by
  refine CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun p hp => ?_
  have h1 := hp ((0, 1), 0)
  have h2 := hp ((1, 0), 0)
  rw [polar_hypSum] at h1 h2
  simp only [mul_one, zero_mul, add_zero, polar_zero_right, mul_zero, one_mul, zero_add] at h1 h2
  have h3 : p.2 = 0 := eq_zero_of_polar_eq_zero hQ' fun w => by
    have := hp ((0, 0), w)
    rw [polar_hypSum] at this
    simpa using this
  ext <;> simp [h1, h2, h3]

@[expose] noncomputable def hypPair (Q' : QuadraticForm K W) : HypPair (hypSum Q') where
  e := ((1, 0), 0)
  f := ((0, 1), 0)
  Q_e := by simp [hypSum_apply]
  Q_f := by simp [hypSum_apply]
  polar_ef := by simp [polar_hypSum]

theorem hypPair_e (Q' : QuadraticForm K W) : (hypPair Q').e = ((1, 0), 0) := rfl

theorem hypPair_f (Q' : QuadraticForm K W) : (hypPair Q').f = ((0, 1), 0) := rfl

@[expose] noncomputable def hypExt (h : W ≃ₗ[K] W) : ((K × K) × W) ≃ₗ[K] ((K × K) × W) :=
  (LinearEquiv.refl K (K × K)).prodCongr h

theorem hypExt_apply (h : W ≃ₗ[K] W) (p : (K × K) × W) : hypExt h p = (p.1, h p.2) := rfl

theorem hypExt_mem {Q' : QuadraticForm K W} {h : W ≃ₗ[K] W}
    (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q') :
    hypExt h ∈ TauCeti.QuadraticMap.orthogonalGroup (hypSum Q') :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun p => by
    simp only [hypExt_apply, hypSum_apply, map_of_mem hh]

variable {Q' : QuadraticForm K W} {g : ((K × K) × W) ≃ₗ[K] ((K × K) × W)}

theorem apply_inr_fst_eq_of_fix (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (hypSum Q'))
    (he : g ((1, 0), 0) = ((1, 0), 0)) (hf : g ((0, 1), 0) = ((0, 1), 0)) (w : W) :
    (g ((0, 0), w)).1 = (0, 0) := by
  have h1 := polar_map_of_mem hg ((1, 0), 0) ((0, 0), w)
  have h2 := polar_map_of_mem hg ((0, 1), 0) ((0, 0), w)
  rw [he, polar_hypSum, polar_hypSum] at h1
  rw [hf, polar_hypSum, polar_hypSum] at h2
  simp only [one_mul, mul_zero, add_zero, polar_zero_left, zero_mul, mul_one, zero_add] at h1 h2
  exact Prod.ext h2 h1

theorem apply_eq_of_fix (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (hypSum Q'))
    (he : g ((1, 0), 0) = ((1, 0), 0)) (hf : g ((0, 1), 0) = ((0, 1), 0))
    (p : (K × K) × W) : g p = (p.1, (g ((0, 0), p.2)).2) := by
  have hp : p = p.1.1 • ((1, 0), 0) + p.1.2 • ((0, 1), 0) + ((0, 0), p.2) := by
    ext <;> simp
  have h0 := apply_inr_fst_eq_of_fix hg he hf p.2
  have h01 : (g ((0, 0), p.2)).1.1 = 0 := congrArg Prod.fst h0
  have h02 : (g ((0, 0), p.2)).1.2 = 0 := congrArg Prod.snd h0
  conv_lhs => rw [hp]
  rw [map_add, map_add, map_smul, map_smul, he, hf]
  ext <;> simp [h01, h02]

theorem exists_hypExt_of_fix
    {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    {Q' : QuadraticForm K W}
    {g : ((K × K) × W) ≃ₗ[K] ((K × K) × W)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (hypSum Q'))
    (he : g ((1, 0), 0) = ((1, 0), 0))
    (hf : g ((0, 1), 0) = ((0, 1), 0)) :
    ∃ h : W ≃ₗ[K] W, h ∈ TauCeti.QuadraticMap.orthogonalGroup Q' ∧ g = hypExt h := by
  have hg' : g⁻¹ ∈ TauCeti.QuadraticMap.orthogonalGroup (hypSum Q') := inv_mem hg
  have he' : g⁻¹ ((1, 0), 0) = ((1, 0), 0) := by
    conv_lhs => rw [← he]
    exact LinearEquiv.inv_apply_apply' g _
  have hf' : g⁻¹ ((0, 1), 0) = ((0, 1), 0) := by
    conv_lhs => rw [← hf]
    exact LinearEquiv.inv_apply_apply' g _
  let hl : W →ₗ[K] W :=
    LinearMap.snd K (K × K) W ∘ₗ g.toLinearMap ∘ₗ LinearMap.inr K (K × K) W
  let hl' : W →ₗ[K] W :=
    LinearMap.snd K (K × K) W ∘ₗ (g⁻¹).toLinearMap ∘ₗ LinearMap.inr K (K × K) W
  have hl_apply : ∀ w, hl w = (g ((0, 0), w)).2 := fun w => rfl
  have hl'_apply : ∀ w, hl' w = (g⁻¹ ((0, 0), w)).2 := fun w => rfl
  have hg_apply : ∀ w, g ((0, 0), w) = ((0, 0), hl w) := fun w => by
    rw [apply_eq_of_fix hg he hf ((0, 0), w), hl_apply]
  have hg_inv_apply : ∀ w, g⁻¹ ((0, 0), w) = ((0, 0), hl' w) := fun w => by
    rw [apply_eq_of_fix hg' he' hf' ((0, 0), w), hl'_apply]
  have h₁ : hl ∘ₗ hl' = LinearMap.id := LinearMap.ext fun w => by
    rw [LinearMap.comp_apply, LinearMap.id_apply, hl_apply, ← hg_inv_apply,
      LinearEquiv.apply_inv_apply']
  have h₂ : hl' ∘ₗ hl = LinearMap.id := LinearMap.ext fun w => by
    rw [LinearMap.comp_apply, LinearMap.id_apply, hl'_apply, ← hg_apply,
      LinearEquiv.inv_apply_apply']
  let h : W ≃ₗ[K] W := LinearEquiv.ofLinearMap hl hl' h₁ h₂
  have hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q' :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun w => by
      show Q' (hl w) = Q' w
      have := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg ((0, 0), w)
      rw [hg_apply, hypSum_apply, hypSum_apply] at this
      simpa using this
  refine ⟨h, hh, ?_⟩
  apply LinearEquiv.ext
  intro p
  rw [apply_eq_of_fix hg he hf p, hypExt_apply]
  rfl

theorem card_stabilizer_hypPair (Q' : QuadraticForm K W) :
    Nat.card (MulAction.stabilizer (TauCeti.QuadraticMap.orthogonalGroup (hypSum Q'))
      ((hypPair Q').e, (hypPair Q').f)) = Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q') := by
  set O := TauCeti.QuadraticMap.orthogonalGroup (hypSum Q')
  have hmem : ∀ h : TauCeti.QuadraticMap.orthogonalGroup Q',
      (⟨hypExt (h : W ≃ₗ[K] W), hypExt_mem h.2⟩ : O) ∈
        MulAction.stabilizer O ((hypPair Q').e, (hypPair Q').f) := by
    intro h
    rw [MulAction.mem_stabilizer_iff]
    change (hypExt (h : W ≃ₗ[K] W) ((1, 0), 0), hypExt (h : W ≃ₗ[K] W) ((0, 1), 0)) =
      (((1, 0), 0), ((0, 1), 0))
    simp [hypExt_apply]
  have hfix : ∀ g : MulAction.stabilizer O ((hypPair Q').e, (hypPair Q').f),
      ((g : O) : ((K × K) × W) ≃ₗ[K] ((K × K) × W)) ((1, 0), 0) = ((1, 0), 0) ∧
        ((g : O) : ((K × K) × W) ≃ₗ[K] ((K × K) × W)) ((0, 1), 0) = ((0, 1), 0) := by
    intro g
    have hg := g.2
    rw [MulAction.mem_stabilizer_iff, Prod.ext_iff] at hg
    exact hg
  refine (Nat.card_congr (Equiv.ofBijective (fun h : TauCeti.QuadraticMap.orthogonalGroup Q' =>
    (⟨⟨hypExt (h : W ≃ₗ[K] W),
    hypExt_mem h.2⟩, hmem h⟩ : MulAction.stabilizer O ((hypPair Q').e, (hypPair Q').f)))
    ⟨fun h h' hhh => ?_, fun g => ?_⟩)).symm
  · apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    have := congrArg (fun x : MulAction.stabilizer O ((hypPair Q').e, (hypPair Q').f) =>
      (((x : O) : ((K × K) × W) ≃ₗ[K] ((K × K) × W)) ((0, 0), w)).2) hhh
    simpa [hypExt_apply] using this
  · obtain ⟨he, hf⟩ := hfix g
    set g₀ : ((K × K) × W) ≃ₗ[K] ((K × K) × W) :=
      ((g : O) : ((K × K) × W) ≃ₗ[K] ((K × K) × W))
    have hgO : g₀ ∈ O := (g : O).2
    obtain ⟨h, hh, hg_eq⟩ := exists_hypExt_of_fix (K := K) (W := W) (Q' := Q') hgO he hf
    refine ⟨⟨h, hh⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro p
    change hypExt h p = g₀ p
    rw [← hg_eq]

open scoped Classical in
theorem card_mul_add_eq_zero [Finite K] (c : K) :
    Nat.card {p : K × K // p.1 * p.2 + c = 0} =
      Nat.card K - 1 + if c = 0 then Nat.card K else 0 := by
  classical
  have := Fintype.ofFinite K
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun a b : K => a * b + c = 0),
    Nat.card_sigma]
  have hterm : ∀ a : K, Nat.card {b : K // a * b + c = 0} =
      if a = 0 then (if c = 0 then Nat.card K else 0) else 1 := by
    intro a
    split_ifs with ha hc
    · subst ha
      subst hc
      simp only [zero_mul, add_zero]
      exact Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)
    · subst ha
      simp only [zero_mul, zero_add, hc, Nat.card_of_isEmpty]
    · rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨-c / a, by field_simp; ring⟩⟩⟩
      have hx := x.2
      have hy := y.2
      have : a * (x : K) = a * y := by linear_combination hx - hy
      exact mul_left_cancel₀ ha this
  rw [Fintype.sum_congr _ _ hterm, Fintype.sum_eq_add_sum_compl 0, ite_eq_left rfl,
    Finset.sum_congr rfl fun a ha => ite_eq_right fun h =>
      Finset.mem_compl.mp ha (Finset.mem_singleton.mpr h),
    Finset.sum_const, smul_eq_mul, mul_one, Finset.card_compl, Finset.card_singleton,
    ← Nat.card_eq_fintype_card, add_comm]

theorem card_singular_hypSum [Finite K] [Finite W] (Q' : QuadraticForm K W) :
    Nat.card {p : (K × K) × W // hypSum Q' p = 0} =
      Nat.card K * Nat.card {w : W // Q' w = 0} + (Nat.card K - 1) * Nat.card W := by
  classical
  have := Fintype.ofFinite K
  have := Fintype.ofFinite W
  let e : {p : (K × K) × W // hypSum Q' p = 0} ≃
      Σ w : W, {ab : K × K // ab.1 * ab.2 + Q' w = 0} :=
    { toFun := fun p => ⟨p.1.2, p.1.1, p.2⟩
      invFun := fun x => ⟨(x.2.1, x.1), x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  simp_rw [card_mul_add_eq_zero]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite, Finset.sum_const,
    Finset.sum_const_zero, add_zero, Finset.card_univ, smul_eq_mul, smul_eq_mul,
    ← Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := {w : W // Q' w = 0}),
    Fintype.card_subtype]
  ring

theorem card_partners_hypPair_e (Q' : QuadraticForm K W) :
    Nat.card {y : (K × K) × W // hypSum Q' y = 0 ∧ polar (hypSum Q') ((1, 0), 0) y = 1} =
      Nat.card W := by
  have key : ∀ y : (K × K) × W, (hypSum Q' y = 0 ∧ polar (hypSum Q') ((1, 0), 0) y = 1) ↔
      y.1.2 = 1 ∧ y.1.1 = -Q' y.2 := by
    intro y
    rw [hypSum_apply, polar_hypSum]
    simp only [one_mul, mul_zero, add_zero, polar_zero_left]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h2, ?_⟩
      rw [h2, mul_one] at h1
      linear_combination h1
    · rintro ⟨h1, h2⟩
      rw [h1, h2]
      exact ⟨by ring, rfl⟩
  refine Nat.card_congr
    { toFun := fun y => y.1.2
      invFun := fun w => ⟨((-Q' w, 1), w), (key _).mpr ⟨rfl, rfl⟩⟩
      left_inv := fun y => ?_
      right_inv := fun w => rfl }
  obtain ⟨h1, h2⟩ := (key y.1).mp y.2
  apply Subtype.ext
  ext
  · exact h2.symm
  · exact h1.symm
  · rfl

theorem card_partners (hQ' : (polarBilin Q').Nondegenerate) (h2 : (2 : K) = 0)
    {x : (K × K) × W} (hx : hypSum Q' x = 0) (hx0 : x ≠ 0) :
    Nat.card {y : (K × K) × W // hypSum Q' y = 0 ∧ polar (hypSum Q') x y = 1} =
      Nat.card W := by
  obtain ⟨g, hg, hgx⟩ := exists_mem_orthogonalGroup_apply_eq
    (nondegenerate_polarBilin_hypSum hQ') h2 (hypPair Q').Q_e hx (hypPair Q').e_ne_zero hx0
  rw [← card_partners_hypPair_e Q']
  refine (Nat.card_congr (Equiv.subtypeEquiv g.toEquiv fun y => ?_)).symm
  change _ ↔ hypSum Q' (g y) = 0 ∧ polar (hypSum Q') x (g y) = 1
  rw [map_of_mem hg, ← hgx, polar_map_of_mem hg]
  rfl

variable [Finite K]

theorem card_hypPairs [Finite W] (hQ' : (polarBilin Q').Nondegenerate) (h2 : (2 : K) = 0) :
    Nat.card {p : ((K × K) × W) × ((K × K) × W) // hypSum Q' p.1 = 0 ∧ hypSum Q' p.2 = 0 ∧
      polar (hypSum Q') p.1 p.2 = 1} =
      (Nat.card {v : (K × K) × W // hypSum Q' v = 0} - 1) * Nat.card W := by
  classical
  have := Fintype.ofFinite K
  have := Fintype.ofFinite W
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun x y : (K × K) × W =>
    hypSum Q' x = 0 ∧ hypSum Q' y = 0 ∧ polar (hypSum Q') x y = 1), Nat.card_sigma]
  have hterm : ∀ x : (K × K) × W, Nat.card {y // hypSum Q' x = 0 ∧ hypSum Q' y = 0 ∧
      polar (hypSum Q') x y = 1} = if hypSum Q' x = 0 ∧ x ≠ 0 then Nat.card W else 0 := by
    intro x
    split_ifs with hx
    · rw [← card_partners hQ' h2 hx.1 hx.2]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp [hx.1])
    · have : IsEmpty {y // hypSum Q' x = 0 ∧ hypSum Q' y = 0 ∧ polar (hypSum Q') x y = 1} := by
        refine ⟨fun y => hx ⟨y.2.1, fun h0 => ?_⟩⟩
        have h' := y.2.2.2
        subst h0
        rw [polar_zero_left] at h'
        exact zero_ne_one h'
      exact Nat.card_of_isEmpty
  rw [Fintype.sum_congr _ _ hterm, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero,
    add_zero, smul_eq_mul]
  congr 1
  rw [Nat.card_eq_fintype_card (α := {v : (K × K) × W // hypSum Q' v = 0}),
    Fintype.card_subtype]
  have hsplit : Finset.univ.filter (fun x : (K × K) × W => hypSum Q' x = 0) =
      insert 0 (Finset.univ.filter fun x : (K × K) × W => hypSum Q' x = 0 ∧ x ≠ 0) := by
    ext x
    by_cases hx : x = 0 <;> simp [hx]
  rw [hsplit, Finset.card_insert_of_notMem (by simp), Nat.add_sub_cancel]

theorem card_orthogonalGroup_hypSum [Finite W] (hQ' : (polarBilin Q').Nondegenerate)
    (h2 : (2 : K) = 0) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (hypSum Q')) =
      (Nat.card {v : (K × K) × W // hypSum Q' v = 0} - 1) * Nat.card W *
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q') := by
  set O := TauCeti.QuadraticMap.orthogonalGroup (hypSum Q')
  have horbit : MulAction.orbit O ((hypPair Q').e, (hypPair Q').f) =
      {p | hypSum Q' p.1 = 0 ∧ hypSum Q' p.2 = 0 ∧ polar (hypSum Q') p.1 p.2 = 1} := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨g, hg⟩
      rw [← hg]
      set g' : ((K × K) × W) ≃ₗ[K] ((K × K) × W) := ((g : O) : ((K × K) × W) ≃ₗ[K] ((K × K) × W))
      change hypSum Q' (g' (hypPair Q').e) = 0 ∧ hypSum Q' (g' (hypPair Q').f) = 0 ∧
        polar (hypSum Q') (g' (hypPair Q').e) (g' (hypPair Q').f) = 1
      rw [map_of_mem g.2, map_of_mem g.2, polar_map_of_mem g.2]
      exact ⟨(hypPair Q').Q_e, (hypPair Q').Q_f, (hypPair Q').polar_ef⟩
    · rintro ⟨hx, hy, hxy⟩
      obtain ⟨g, hg, hge, hgf⟩ := exists_mem_orthogonalGroup_apply_pair
        (nondegenerate_polarBilin_hypSum hQ') h2 (hypPair Q') ⟨x, y, hx, hy, hxy⟩
      exact ⟨⟨g, hg⟩, Prod.ext hge hgf⟩
  have hcard := (MulAction.stabilizer O ((hypPair Q').e, (hypPair Q').f)).card_mul_index
  rw [MulAction.index_stabilizer, horbit, ← Nat.card_coe_set_eq, card_stabilizer_hypPair] at hcard
  rw [← hcard, mul_comm]
  congr 1
  exact card_hypPairs hQ' h2

end CFSG.Timmesfeld.ClassicalOrders
