module

public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix

variable {G : Type} [Group G]

section Coord

variable {V : Subgroup G} {ι : Type} {F : Type} [Field F]
  (β : ↥V →* Multiplicative (Fin 1 → ι → F))

@[expose] def IsCoordAct (g : G) (f : (ι → F) → (ι → F)) : Prop :=
  ∀ u v : ↥V, (v : G) = g * u * g⁻¹ →
    Multiplicative.toAdd (β v) 0 = f (Multiplicative.toAdd (β u) 0)

variable {β}

theorem exists_coord_eq (hβ : Function.Surjective β) (x : ι → F) :
    ∃ u : ↥V, Multiplicative.toAdd (β u) 0 = x := by
  obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd fun _ => x)
  exact ⟨u, by rw [hu]; rfl⟩

theorem conj_mem_of_mem_normalizer {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G)) (u : ↥V) :
    g * (u : G) * g⁻¹ ∈ V :=
  (Subgroup.mem_normalizer_iff.1 hg u).1 u.2

theorem IsCoordAct.congr {g : G} {f f' : (ι → F) → (ι → F)} (hf : IsCoordAct β g f)
    (hff' : ∀ x, f x = f' x) : IsCoordAct β g f' := fun u v huv => by
  rw [hf u v huv, hff']

theorem IsCoordAct.unique (hβ : Function.Surjective β) {g : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) {f f' : (ι → F) → (ι → F)}
    (hf : IsCoordAct β g f) (hf' : IsCoordAct β g f') : f = f' := by
  funext x
  obtain ⟨u, rfl⟩ := exists_coord_eq hβ x
  have hv := conj_mem_of_mem_normalizer hg u
  rw [← hf u ⟨_, hv⟩ rfl, ← hf' u ⟨_, hv⟩ rfl]

theorem IsCoordAct.matrix_eq [Fintype ι] [DecidableEq ι] (hβ : Function.Surjective β) {g : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) {A B : Matrix ι ι F}
    (hA : IsCoordAct β g A.mulVec) (hB : IsCoordAct β g B.mulVec) : A = B := by
  have h := IsCoordAct.unique hβ hg hA hB
  ext i j
  have := congrFun (congrFun h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

theorem isCoordAct_one : IsCoordAct β 1 id := by
  intro u v huv
  have : v = u := Subtype.ext (by rw [huv]; group)
  rw [this]
  rfl

theorem isCoordAct_one_mulVec [Fintype ι] [DecidableEq ι] :
    IsCoordAct β 1 (1 : Matrix ι ι F).mulVec :=
  (isCoordAct_one (β := β)).congr fun x => (Matrix.one_mulVec x).symm

theorem IsCoordAct.mul {g h : G} (hh : h ∈ Subgroup.normalizer (V : Set G))
    {f f' : (ι → F) → (ι → F)} (hf : IsCoordAct β g f) (hf' : IsCoordAct β h f') :
    IsCoordAct β (g * h) (f ∘ f') := by
  intro u v huv
  have hw := conj_mem_of_mem_normalizer hh u
  rw [hf ⟨_, hw⟩ v (by rw [huv]; simp only [_root_.mul_inv_rev]; group), hf' u ⟨_, hw⟩ rfl]
  rfl

theorem IsCoordAct.inv [Fintype ι] [DecidableEq ι] {g : G} {A : GL ι F}
    (hA : IsCoordAct β g (A : Matrix ι ι F).mulVec) :
    IsCoordAct β g⁻¹ ((A⁻¹ : GL ι F) : Matrix ι ι F).mulVec := by
  intro u v huv
  have huv' : (u : G) = g * v * g⁻¹ := by rw [huv]; group
  rw [hA v u huv', Matrix.mulVec_mulVec]
  simp

end Coord

section Extension

variable {V Z : Subgroup G} {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
  {β : ↥V →* Multiplicative (Fin 1 → ι → F)} {Γ : Subgroup (GL ι F)}

@[expose] def coordGroup (β : ↥V →* Multiplicative (Fin 1 → ι → F)) (Γ : Subgroup (GL ι F))
    (M : Subgroup G) (hMV : M ≤ Subgroup.normalizer (V : Set G)) : Subgroup G where
  carrier := {g | g ∈ M ∧ ∃ γ : ↥Γ, IsCoordAct β g ((γ : GL ι F) : Matrix ι ι F).mulVec}
  one_mem' := ⟨M.one_mem, 1, by simpa using (isCoordAct_one_mulVec (β := β))⟩
  mul_mem' := by
    rintro g h ⟨hg, γ, hγ⟩ ⟨hh, γ', hγ'⟩
    refine ⟨M.mul_mem hg hh, γ * γ', ?_⟩
    have := hγ.mul (hMV hh) hγ'
    convert this using 1
    funext x
    simp [Matrix.mulVec_mulVec]
  inv_mem' := by
    rintro g ⟨hg, γ, hγ⟩
    exact ⟨M.inv_mem hg, γ⁻¹, by simpa using hγ.inv⟩

theorem exists_natural_of_coordAct {A M T : Subgroup G} (hM : M = A ⊔ T) {α : ↥A →* ↥Γ}
    (hα : Function.Surjective α) (hAV : A ≤ Subgroup.normalizer (V : Set G)) (hZV : Z ≤ V)
    (hβ : Function.Surjective β) (hβker : β.ker = Z.subgroupOf V)
    (hβα : ∀ (a : ↥A) (u v : ↥V), (v : G) = a * u * a⁻¹ → ∀ i : Fin 1,
      Multiplicative.toAdd (β v) i =
        (moduleAct false (α a : GL ι F)).mulVec (Multiplicative.toAdd (β u) i))
    (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hT : ∀ t ∈ T, ∃ γ : ↥Γ, IsCoordAct β t ((γ : GL ι F) : Matrix ι ι F).mulVec) :
    ∃ α' : ↥M →* ↥Γ, Function.Surjective α' ∧ IsSumOfNaturalModulesVia M V Z α' false 1 := by
  have hMV : M ≤ Subgroup.normalizer (V : Set G) := hM ▸ sup_le hAV hTV
  have hA' : ∀ a : ↥A, IsCoordAct β a ((α a : GL ι F) : Matrix ι ι F).mulVec := by
    intro a u v huv
    simpa [moduleAct] using hβα a u v huv 0
  have hAM : A ≤ M := hM ▸ (le_sup_left : A ≤ A ⊔ T)
  have hTM : T ≤ M := hM ▸ (le_sup_right : T ≤ A ⊔ T)
  have hle : M ≤ coordGroup β Γ M hMV :=
    hM.le.trans (sup_le (fun a ha => ⟨hAM ha, α ⟨a, ha⟩, hA' ⟨a, ha⟩⟩)
      (fun t ht => ⟨hTM ht, hT t ht⟩))
  have hS : ∀ m : ↥M, ∃ γ : ↥Γ, IsCoordAct β m ((γ : GL ι F) : Matrix ι ι F).mulVec :=
    fun m => (hle m.2).2
  choose φ hφ using hS
  have huniq : ∀ (m : ↥M) (γ : ↥Γ), IsCoordAct β m ((γ : GL ι F) : Matrix ι ι F).mulVec →
      φ m = γ := by
    intro m γ hγ
    have h := IsCoordAct.matrix_eq hβ (hMV m.2) (hφ m) hγ
    exact Subtype.ext (Units.ext h)
  let α' : ↥M →* ↥Γ :=
    { toFun := φ
      map_one' := huniq 1 1 (by simpa using (isCoordAct_one_mulVec (β := β)))
      map_mul' := fun m m' => by
        refine huniq (m * m') (φ m * φ m') ?_
        have := (hφ m).mul (hMV m'.2) (hφ m')
        convert this using 1
        funext x
        simp [Matrix.mulVec_mulVec] }
  refine ⟨α', fun γ => ?_, hMV, hZV, β, hβ, hβker, ?_⟩
  · obtain ⟨a, rfl⟩ := hα γ
    exact ⟨⟨a, hAM a.2⟩, huniq ⟨a, hAM a.2⟩ (α a) (hA' a)⟩
  · intro m u v huv i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    have := hφ m u v huv
    simp only [moduleAct, Bool.false_eq_true, ite_false]
    exact this

end Extension

end CFSG.Quasithin.MS93
