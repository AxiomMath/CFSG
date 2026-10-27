module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.GroupAction.SubMulAction

public noncomputable section

namespace CFSG.Sporadic.Schreier

variable {G V : Type*} [Group G] [MulAction G V] {N : ℕ} {ι : Type*}
  {s : ι → G} {vs : Fin N → V} {σ : ι → Equiv.Perm (Fin N)}

theorem smul_mem_range (hs : Subgroup.closure (Set.range s) = ⊤)
    (hσ : ∀ k i, s k • vs i = vs (σ k i)) (g : G) : ∀ i, g • vs i ∈ Set.range vs := by
  have hg : g ∈ Subgroup.closure (Set.range s) := by rw [hs]; trivial
  refine Subgroup.closure_induction'' (p := fun g _ => ∀ i, g • vs i ∈ Set.range vs)
    ?_ ?_ ?_ ?_ hg
  · rintro _ ⟨k, rfl⟩ i
    exact ⟨σ k i, (hσ k i).symm⟩
  · rintro _ ⟨k, rfl⟩ i
    refine ⟨(σ k).symm i, ?_⟩
    rw [eq_inv_smul_iff, hσ, Equiv.apply_symm_apply]
  · intro i
    exact ⟨i, (one_smul G (vs i)).symm⟩
  · intro x y _ _ hx hy i
    obtain ⟨j, hj⟩ := hy i
    obtain ⟨l, hl⟩ := hx j
    exact ⟨l, by rw [mul_smul, ← hj, hl]⟩

@[expose] def familySub (h : ∀ g : G, ∀ i, g • vs i ∈ Set.range vs) : SubMulAction G V where
  carrier := Set.range vs
  smul_mem' g := by
    rintro _ ⟨i, rfl⟩
    exact h g i

@[expose] def familyEquiv (hinj : Function.Injective vs)
    (h : ∀ g : G, ∀ i, g • vs i ∈ Set.range vs) : Fin N ≃ familySub h :=
  Equiv.ofBijective (fun i => ⟨vs i, i, rfl⟩)
    ⟨fun _ _ hij => hinj (congrArg Subtype.val hij), by rintro ⟨_, i, rfl⟩; exact ⟨i, rfl⟩⟩

theorem vs_familyEquiv_symm (hinj : Function.Injective vs)
    (h : ∀ g : G, ∀ i, g • vs i ∈ Set.range vs) (y : familySub h) :
    vs ((familyEquiv hinj h).symm y) = y := by
  conv_rhs => rw [← (familyEquiv hinj h).apply_symm_apply y]
  rfl

@[expose] def familyPerm (hinj : Function.Injective vs)
    (h : ∀ g : G, ∀ i, g • vs i ∈ Set.range vs) : G →* Equiv.Perm (Fin N) :=
  ((familyEquiv hinj h).symm.permCongrHom).toMonoidHom.comp (MulAction.toPermHom G (familySub h))

variable (hinj : Function.Injective vs) (h : ∀ g : G, ∀ i, g • vs i ∈ Set.range vs)
include hinj

theorem familyPerm_apply (g : G) (i : Fin N) : vs (familyPerm hinj h g i) = g • vs i := by
  change vs ((familyEquiv hinj h).symm (g • (familyEquiv hinj h) i)) = _
  rw [vs_familyEquiv_symm hinj h]
  rfl

theorem familyPerm_gen (hσ : ∀ k i, s k • vs i = vs (σ k i)) (k : ι) :
    familyPerm hinj h (s k) = σ k :=
  Equiv.ext fun i => hinj (by rw [familyPerm_apply hinj h, hσ])

theorem familyPerm_range (hs : Subgroup.closure (Set.range s) = ⊤)
    (hσ : ∀ k i, s k • vs i = vs (σ k i)) :
    (familyPerm hinj h).range = Subgroup.closure (Set.range σ) := by
  rw [MonoidHom.range_eq_map, ← hs, MonoidHom.map_closure, ← Set.range_comp]
  congr 2
  funext k
  exact familyPerm_gen hinj h hσ k

theorem familyPerm_injective (hfix : ∀ g : G, (∀ i, g • vs i = vs i) → g = 1) :
    Function.Injective (familyPerm hinj h) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  refine hfix g fun i => ?_
  rw [← familyPerm_apply hinj h, hg]
  rfl

@[expose] def familyPermEquiv (hs : Subgroup.closure (Set.range s) = ⊤)
    (hσ : ∀ k i, s k • vs i = vs (σ k i)) (hfix : ∀ g : G, (∀ i, g • vs i = vs i) → g = 1) :
    G ≃* Subgroup.closure (Set.range σ) :=
  (MonoidHom.ofInjective (familyPerm_injective hinj h hfix)).trans
    (MulEquiv.subgroupCongr (familyPerm_range hinj h hs hσ))

theorem familyPermEquiv_apply (hs : Subgroup.closure (Set.range s) = ⊤)
    (hσ : ∀ k i, s k • vs i = vs (σ k i)) (hfix : ∀ g : G, (∀ i, g • vs i = vs i) → g = 1)
    (g : G) : (familyPermEquiv hinj h hs hσ hfix g : Equiv.Perm (Fin N)) = familyPerm hinj h g :=
  rfl

end CFSG.Sporadic.Schreier
