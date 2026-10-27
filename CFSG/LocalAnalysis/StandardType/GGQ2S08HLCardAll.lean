module

public import CFSG.LocalAnalysis.StandardType.GGHLDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma ggQ2s08y_conj_gen {p : ℕ} [Fact p.Prime] {E : Type*} [Group E] {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] {Λ : Type*} (ι : Additive E ≃+ V) (φ : Λ → MulAut E)
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hsimple : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    {g : V ≃ₗ[ZMod p] V} (hg : g ∈ ggDiagramSet h α) :
    ∃ π : Λ ≃ Λ, ∀ i, g * ggLin (p := p) ι (φ i) * g⁻¹ =
      ggLin (p := p) ι (φ (π i)) := by
  obtain ⟨π, hπ⟩ := hg
  refine ⟨π, fun i => ?_⟩
  ext v
  simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv]
  rw [hsimple i (g.symm v), hsimple (π i) v]
  rw [map_sub, map_smul, LinearEquiv.apply_symm_apply, (hπ i).1]
  have hscalar : α i (g.symm v) = α (π i) v := by
    rw [← (hπ i).2 (g.symm v), LinearEquiv.apply_symm_apply]
  rw [hscalar]

private def ggQ2s08y_diagramSubgroup {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] {Λ : Type*} (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V) :
    Subgroup (V ≃ₗ[ZMod p] V) where
  carrier := ggDiagramSet h α
  one_mem' := by
    refine ⟨Equiv.refl Λ, fun i => ⟨?_, ?_⟩⟩
    · simp
    · intro v; simp
  mul_mem' := by
    rintro g g' ⟨π, hπ⟩ ⟨π', hπ'⟩
    refine ⟨π * π', fun i => ⟨?_, ?_⟩⟩
    · rw [LinearEquiv.mul_apply, (hπ' i).1, (hπ (π' i)).1, Equiv.Perm.mul_apply]
    · intro v
      rw [LinearEquiv.mul_apply, Equiv.Perm.mul_apply, (hπ (π' i)).2 (g' v), (hπ' i).2 v]
  inv_mem' := by
    rintro g ⟨π, hπ⟩
    refine ⟨π.symm, fun i => ⟨?_, ?_⟩⟩
    · have h1 : g (h (π.symm i)) = h i := by
        rw [(hπ (π.symm i)).1, Equiv.apply_symm_apply]
      rw [← h1, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    · intro v
      have h1 : α i (g (g⁻¹ v)) = α (π.symm i) (g⁻¹ v) := by
        rw [← (hπ (π.symm i)).2 (g⁻¹ v), Equiv.apply_symm_apply]
      rw [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] at h1
      exact h1.symm

private lemma ggQ2s08y_conj_mem {p : ℕ} [Fact p.Prime] {E : Type*} [Group E] {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] {Λ : Type*} (ι : Additive E ≃+ V) (φ : Λ → MulAut E)
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hsimple : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    {g : V ≃ₗ[ZMod p] V} (hg : g ∈ ggDiagramSet h α) :
    ∀ w ∈ Subgroup.closure (Set.range fun i => ggLin (p := p) ι (φ i)),
      g * w * g⁻¹ ∈ Subgroup.closure (Set.range fun i => ggLin (p := p) ι (φ i)) := by
  let W : Subgroup (V ≃ₗ[ZMod p] V) :=
    Subgroup.closure (Set.range fun i => ggLin (p := p) ι (φ i))
  change ∀ w ∈ W, g * w * g⁻¹ ∈ W
  obtain ⟨π, hπ⟩ := ggQ2s08y_conj_gen ι φ h α hsimple hg
  intro w hw
  refine Subgroup.closure_induction (p := fun y _ => g * y * g⁻¹ ∈ W) ?_ ?_ ?_ ?_ hw
  · intro y hy
    obtain ⟨i, rfl⟩ := hy
    rw [hπ i]
    exact Subgroup.subset_closure ⟨π i, rfl⟩
  · simp
  · intro y z _ _ hy hz
    have h : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
    rw [h]
    exact W.mul_mem hy hz
  · intro y _ hy
    have h : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
    rw [h]
    exact W.inv_mem hy

private lemma ggQ2s08y_diagram_mem_normalizer {p : ℕ} [Fact p.Prime] {E : Type*} [Group E]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] {Λ : Type*} (ι : Additive E ≃+ V)
    (φ : Λ → MulAut E) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hsimple : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    {g : V ≃ₗ[ZMod p] V} (hg : g ∈ ggDiagramSet h α) :
    g ∈ Subgroup.normalizer
      (Subgroup.closure (Set.range fun i => ggLin (p := p) ι (φ i)) :
        Set (V ≃ₗ[ZMod p] V)) := by
  refine Subgroup.mem_normalizer_iff.mpr (fun w => ⟨fun hw => ?_, fun hw => ?_⟩)
  · exact ggQ2s08y_conj_mem ι φ h α hsimple hg w hw
  · have hginv : g⁻¹ ∈ ggDiagramSet h α := (ggQ2s08y_diagramSubgroup h α).inv_mem hg
    have hmem := ggQ2s08y_conj_mem ι φ h α hsimple hginv (g * w * g⁻¹) hw
    rwa [show g⁻¹ * (g * w * g⁻¹) * (g⁻¹)⁻¹ = w from by group] at hmem

private lemma ggQ2s08y_neg_central {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] (w : V ≃ₗ[ZMod p] V) :
    LinearEquiv.neg (ZMod p) * w = w * LinearEquiv.neg (ZMod p) := by
  ext v
  simp only [LinearEquiv.mul_apply, LinearEquiv.neg_apply, map_neg]

private lemma ggQ2s08y_neg_conj {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] (w : V ≃ₗ[ZMod p] V) :
    LinearEquiv.neg (ZMod p) * w * (LinearEquiv.neg (ZMod p))⁻¹ = w := by
  rw [ggQ2s08y_neg_central w, mul_assoc, mul_inv_cancel, mul_one]

private lemma ggQ2s08y_card_neg_le {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] :
    Nat.card ↥(Subgroup.closure ({LinearEquiv.neg (ZMod p)} : Set (V ≃ₗ[ZMod p] V))) ≤ 2 := by
  rw [← Subgroup.zpowers_eq_closure (LinearEquiv.neg (ZMod p)), Nat.card_zpowers]
  have h2 : (LinearEquiv.neg (ZMod p) : V ≃ₗ[ZMod p] V) ^ 2 = 1 := by
    ext v
    simp [pow_two, LinearEquiv.mul_apply, LinearEquiv.neg_apply]
  exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.mpr h2)

private lemma ggQ2s08y_card_le_card_of_le {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (h : H ≤ K) : Nat.card ↥H ≤ Nat.card ↥K :=
  Nat.card_le_card_of_injective (fun x : ↥H => (⟨x.1, h x.2⟩ : ↥K))
    (fun x y hxy => Subtype.ext (congrArg (fun z : ↥K => (z : G)) hxy))

private lemma ggQ2s08y_card_sup_le_mul {G : Type*} [Group G] [Finite G] (W K : Subgroup G)
    (h : K ≤ Subgroup.normalizer (W : Set G)) :
    Nat.card ↥(W ⊔ K) ≤ Nat.card ↥W * Nat.card ↥K := by
  let S : Set G := {x | ∃ w ∈ W, ∃ k ∈ K, w * k = x}
  have hmul : ∀ {x y : G}, x ∈ S → y ∈ S → x * y ∈ S := by
    rintro x y ⟨w₁, hw₁, k₁, hk₁, rfl⟩ ⟨w₂, hw₂, k₂, hk₂, rfl⟩
    have hw : k₁ * w₂ * k₁⁻¹ ∈ W :=
      (Subgroup.le_normalizer_iff.mp h) k₁ hk₁ w₂ hw₂
    exact ⟨w₁ * (k₁ * w₂ * k₁⁻¹), W.mul_mem hw₁ hw, k₁ * k₂, K.mul_mem hk₁ hk₂, by group⟩
  have hinv : ∀ {x : G}, x ∈ S → x⁻¹ ∈ S := by
    rintro x ⟨w, hw, k, hk, rfl⟩
    have hw' : k⁻¹ * w⁻¹ * k ∈ W := by
      have hmem := (Subgroup.le_normalizer_iff.mp h) k⁻¹ (K.inv_mem hk) w⁻¹ (W.inv_mem hw)
      simpa only [inv_inv] using hmem
    exact ⟨k⁻¹ * w⁻¹ * k, hw', k⁻¹, K.inv_mem hk, by group⟩
  have hmem : ∀ x ∈ W ⊔ K, x ∈ S := by
    intro x hx
    rw [Subgroup.sup_eq_closure] at hx
    refine Subgroup.closure_induction (p := fun y _ => y ∈ S) ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases hy with hyW | hyK
      · exact ⟨y, hyW, 1, K.one_mem, by simp⟩
      · exact ⟨1, W.one_mem, y, hyK, by simp⟩
    · exact ⟨1, W.one_mem, 1, K.one_mem, by simp⟩
    · intro y z _ _ hy hz
      exact hmul hy hz
    · intro y _ hy
      exact hinv hy
  have hcard : Nat.card ↥(W ⊔ K) ≤ Nat.card (↥W × ↥K) := by
    refine Nat.card_le_card_of_surjective
      (fun p : ↥W × ↥K => (⟨p.1 * p.2, ?_⟩ : ↥(W ⊔ K))) ?_
    · exact (W ⊔ K).mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)
    · rintro ⟨x, hx⟩
      obtain ⟨w, hw, k, hk, hwk⟩ := hmem x hx
      exact ⟨(⟨w, hw⟩, ⟨k, hk⟩), Subtype.ext hwk⟩
  simpa only [Nat.card_prod] using hcard

private theorem ggQ2s08y_card_diagramSubgroup_le {p : ℕ} [Fact p.Prime] {E : Type*} [Group E]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] {Λ : Type*} [Fintype Λ]
    (ι : Additive E ≃+ V) (φ : Λ → MulAut E) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hdisj : Submodule.span (ZMod p) (Set.range h) = ⊤ ∨ ∀ v, (∀ i, α i v = 0) → v = 0) :
    Nat.card ↥(ggQ2s08y_diagramSubgroup h α) ≤
      Nat.card {π : Λ ≃ Λ // ∀ i j, α (π i) (h (π j)) = α i (h j)} := by
  classical
  have hex : ∀ g : ↥(ggQ2s08y_diagramSubgroup h α),
      ∃ π : Λ ≃ Λ, ∀ i, g.1 (h i) = h (π i) ∧ ∀ v, α (π i) (g.1 v) = α i v :=
    fun g => g.2
  let Φ : ↥(ggQ2s08y_diagramSubgroup h α) →
      {π : Λ ≃ Λ // ∀ i j, α (π i) (h (π j)) = α i (h j)} :=
    fun g => ⟨Classical.choose (hex g), fun i j => by
      have hg1 : g.1 (h j) = h (Classical.choose (hex g) j) :=
        (Classical.choose_spec (hex g) j).1
      have hg2 := (Classical.choose_spec (hex g) i).2
      rw [← hg1]
      exact hg2 (h j)⟩
  refine Nat.card_le_card_of_injective Φ (fun x y hxy => ?_)
  have hπ : Classical.choose (hex x) = Classical.choose (hex y) := by
    have h := congrArg Subtype.val hxy
    exact h
  apply Subtype.ext
  rcases hdisj with hspan | hsep
  · apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext_on hspan
    intro v hv
    obtain ⟨i, rfl⟩ := hv
    change x.1 (h i) = y.1 (h i)
    have hx1 : x.1 (h i) = h (Classical.choose (hex x) i) := (Classical.choose_spec (hex x) i).1
    have hy1 : y.1 (h i) = h (Classical.choose (hex y) i) := (Classical.choose_spec (hex y) i).1
    rw [hx1, hy1, hπ]
  ·
    apply LinearEquiv.ext
    intro v
    have key : ∀ (g : ↥(ggQ2s08y_diagramSubgroup h α)) (j : Λ),
        α j (g.1 v) = α ((Classical.choose (hex g)).symm j) v := by
      intro g j
      have := (Classical.choose_spec (hex g) ((Classical.choose (hex g)).symm j)).2 v
      rwa [Equiv.apply_symm_apply] at this
    have hsub : ∀ j, α j (x.1 v - y.1 v) = 0 := by
      intro j
      rw [map_sub, key x j, key y j, hπ]
      exact sub_self _
    exact sub_eq_zero.mp (hsep _ hsub)

theorem ggQ2s08_hL_card_le_all {p : ℕ} [Fact p.Prime] {E : Type*} [Group E] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] {Λ : Type*} [Fintype Λ] (ι : Additive E ≃+ V)
    (φ : Λ → MulAut E) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hdisj : Submodule.span (ZMod p) (Set.range h) = ⊤ ∨ ∀ v, (∀ i, α i v = 0) → v = 0)
    (hsimple : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) :
    Nat.card ↥(ggHL ι φ h α) ≤
      2 * Nat.card {π : Λ ≃ Λ // ∀ i j, α (π i) (h (π j)) = α i (h j)} *
        Nat.card ↥(Subgroup.closure (Set.range fun i => ggLin (p := p) ι (φ i))) := by
  classical
  haveI : Finite (V ≃ₗ[ZMod p] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod p] V => (e : V → V))
      (fun e f h => LinearEquiv.ext (fun v => congrFun h v))
  let s : Λ → (V ≃ₗ[ZMod p] V) := fun i => ggLin (p := p) ι (φ i)
  let W : Subgroup (V ≃ₗ[ZMod p] V) := Subgroup.closure (Set.range s)
  let K : Subgroup (V ≃ₗ[ZMod p] V) :=
    Subgroup.closure (({LinearEquiv.neg (ZMod p)} : Set (V ≃ₗ[ZMod p] V)) ∪ ggDiagramSet h α)
  let GΓ : Subgroup (V ≃ₗ[ZMod p] V) := ggQ2s08y_diagramSubgroup h α
  let Neg : Subgroup (V ≃ₗ[ZMod p] V) :=
    Subgroup.closure ({LinearEquiv.neg (ZMod p)} : Set (V ≃ₗ[ZMod p] V))
  have hggHL : ggHL ι φ h α =
      Subgroup.closure (Set.range s ∪
        ({LinearEquiv.neg (ZMod p)} ∪ ggDiagramSet h α)) := by
    unfold ggHL
    rw [Set.union_assoc]
  have hHL : ggHL ι φ h α = W ⊔ K := by
    rw [hggHL, Subgroup.closure_union]
  have hK_norm : K ≤ Subgroup.normalizer (W : Set (V ≃ₗ[ZMod p] V)) := by
    refine (Subgroup.closure_le (Subgroup.normalizer (W : Set (V ≃ₗ[ZMod p] V)))).mpr
      (fun x hx => ?_)
    rcases hx with hx | hx
    · simp only [Set.mem_singleton_iff] at hx
      rcases hx with rfl
      exact Subgroup.mem_normalizer_iff.mpr (fun w => by
        rw [show LinearEquiv.neg (ZMod p) * w * (LinearEquiv.neg (ZMod p))⁻¹ = w from
          ggQ2s08y_neg_conj w])
    · exact ggQ2s08y_diagram_mem_normalizer ι φ h α hsimple hx
  have hK_le_sup : K ≤ GΓ ⊔ Neg := by
    refine (Subgroup.closure_le (GΓ ⊔ Neg)).mpr (fun x hx => ?_)
    rcases hx with hx | hx
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure hx)
    · exact Subgroup.mem_sup_left hx
  have hNeg_norm : Neg ≤ Subgroup.normalizer (GΓ : Set (V ≃ₗ[ZMod p] V)) := by
    refine (Subgroup.closure_le (Subgroup.normalizer (GΓ : Set (V ≃ₗ[ZMod p] V)))).mpr
      (fun x hx => ?_)
    simp only [Set.mem_singleton_iff] at hx
    rcases hx with rfl
    exact Subgroup.mem_normalizer_iff.mpr (fun g => by
      rw [show LinearEquiv.neg (ZMod p) * g * (LinearEquiv.neg (ZMod p))⁻¹ = g from
        ggQ2s08y_neg_conj g])
  have hGΓ_card : Nat.card ↥GΓ ≤
      Nat.card {π : Λ ≃ Λ // ∀ i j, α (π i) (h (π j)) = α i (h j)} :=
    ggQ2s08y_card_diagramSubgroup_le ι φ h α hdisj
  have hNeg_card : Nat.card ↥Neg ≤ 2 := ggQ2s08y_card_neg_le (p := p) (V := V)
  calc
    Nat.card ↥(ggHL ι φ h α) = Nat.card ↥(W ⊔ K) := by rw [hHL]
    _ ≤ Nat.card ↥W * Nat.card ↥K := ggQ2s08y_card_sup_le_mul W K hK_norm
    _ ≤ Nat.card ↥W * Nat.card ↥(GΓ ⊔ Neg) :=
          Nat.mul_le_mul_left _ (ggQ2s08y_card_le_card_of_le hK_le_sup)
    _ ≤ Nat.card ↥W * (Nat.card ↥GΓ * Nat.card ↥Neg) :=
          Nat.mul_le_mul_left _ (ggQ2s08y_card_sup_le_mul GΓ Neg hNeg_norm)
    _ ≤ Nat.card ↥W *
        (Nat.card {π : Λ ≃ Λ // ∀ i j, α (π i) (h (π j)) = α i (h j)} * 2) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hGΓ_card hNeg_card)
    _ = 2 * Nat.card {π : Λ ≃ Λ // ∀ i j, α (π i) (h (π j)) = α i (h j)} *
        Nat.card ↥W := by ac_rfl

end CFSG.StandardType

end
