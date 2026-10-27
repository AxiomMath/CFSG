module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClPoint

public section

namespace CFSG.RankThree.GF2n.Stroth80.Classify

private theorem elationFull_mono {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {F : LinearMap.BilinForm K V} {D D' : Set (V ≃ₗ[K] V)} {e : V} (hDD : D ⊆ D')
    (h : ElationFull F D e) : ElationFull F D' e := by
  intro φ hφ
  obtain ⟨g, hg, hgφ⟩ := h φ hφ
  exact ⟨g, hDD hg, hgφ⟩

theorem opp_dichotomy (hX : TheoremXStatement)
    {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (F : LinearMap.BilinForm K V) (hnd : F.Nondegenerate) (halt : F.IsAlt) (h4 : 4 ≤ Nat.card K)
    (hdim : 4 ≤ Module.finrank K V)
    (e₁ e₂ : V) (h12 : F e₁ e₂ ≠ 0)
    (A₁ A₂ : Subgroup (V ≃ₗ[K] V))
    (hA₁ : A₁ ≤ pointRadSubgroup F e₁) (hA₂ : A₂ ≤ pointRadSubgroup F e₂)
    (hf₁ : ElationFull F (A₁ : Set _) e₁) (hf₂ : ElationFull F (A₂ : Set _) e₂) :
    A₁ ⊔ A₂ = sympSubgroup F ∨
      ∃ Qf : QuadraticForm K V, Qf.polarBilin = F ∧
        A₁ ⊔ A₂ = ⁅orthSubgroup Qf, orthSubgroup Qf⁆ := by
  have he₁ : e₁ ≠ 0 := fun h => h12 (by simp [h])
  have he₂ : e₂ ≠ 0 := fun h => h12 (by simp [h])
  have hH : A₁ ⊔ A₂ ≤ sympSubgroup F :=
    sup_le (hA₁.trans (pointRadSubgroup_le_symp e₁)) (hA₂.trans (pointRadSubgroup_le_symp e₂))
  obtain ⟨P, hPmem⟩ : ∃ P : Set V,
      ∀ v, v ∈ P ↔ ∃ g ∈ A₁ ⊔ A₂, v = g e₁ ∨ v = g e₂ :=
    ⟨{v | ∃ g ∈ A₁ ⊔ A₂, v = g e₁ ∨ v = g e₂}, fun _ => Iff.rfl⟩
  have hgP₂ : ∀ g ∈ A₁ ⊔ A₂, g e₂ ∈ P := fun g hg => (hPmem _).mpr ⟨g, hg, Or.inr rfl⟩
  have he₁P : e₁ ∈ P := (hPmem e₁).mpr ⟨1, (A₁ ⊔ A₂).one_mem, Or.inl (by simp)⟩
  have he₂P : e₂ ∈ P := (hPmem e₂).mpr ⟨1, (A₁ ⊔ A₂).one_mem, Or.inr (by simp)⟩
  have hP0 : ∀ v ∈ P, v ≠ 0 := by
    intro v hv
    obtain ⟨g, -, rfl | rfl⟩ := (hPmem v).mp hv
    · exact fun h => he₁ (g.injective (h.trans (map_zero g).symm))
    · exact fun h => he₂ (g.injective (h.trans (map_zero g).symm))
  have hsub₁ : (A₁ : Set (V ≃ₗ[K] V)) ⊆
      ((A₁ ⊔ A₂ : Subgroup (V ≃ₗ[K] V)) : Set (V ≃ₗ[K] V)) ∩ pointRad F e₁ :=
    fun g (hg : g ∈ A₁) => ⟨Subgroup.mem_sup_left hg, hA₁ hg⟩
  have hsub₂ : (A₂ : Set (V ≃ₗ[K] V)) ⊆
      ((A₁ ⊔ A₂ : Subgroup (V ≃ₗ[K] V)) : Set (V ≃ₗ[K] V)) ∩ pointRad F e₂ :=
    fun g (hg : g ∈ A₂) => ⟨Subgroup.mem_sup_right hg, hA₂ hg⟩
  have hfull₁ := elationFull_mono hsub₁ hf₁
  have hfull₂ := elationFull_mono hsub₂ hf₂
  have hfull : ∀ v ∈ P, ElationFull F
      (((A₁ ⊔ A₂ : Subgroup (V ≃ₗ[K] V)) : Set (V ≃ₗ[K] V)) ∩ pointRad F v) v := by
    intro v hv
    obtain ⟨g, hg, rfl | rfl⟩ := (hPmem v).mp hv
    · exact elationFull_conj hH hfull₁ hg
    · exact elationFull_conj hH hfull₂ hg
  obtain ⟨f, hdef⟩ : ∃ f : V, f = (F e₁ e₂)⁻¹ • e₂ := ⟨_, rfl⟩
  have hF1 : F e₁ f = 1 := by
    rw [hdef, map_smul, smul_eq_mul, inv_mul_cancel₀ h12]
  have hF1' : F f e₁ = 1 := (form_comm halt f e₁).trans hF1
  have hfU : f ∈ Submodule.span K P := by
    rw [hdef]
    exact Submodule.smul_mem _ _ (Submodule.subset_span he₂P)
  have hgf : ∀ g : V ≃ₗ[K] V, g f = (F e₁ e₂)⁻¹ • g e₂ := by
    intro g
    rw [hdef, map_smul]
  have hspan : Submodule.span K P = ⊤ := by
    have hω : ∀ ω : V, F ω e₁ = 0 → ω ∈ Submodule.span K P := by
      intro ω hω0
      have hD : (A₁ : Set (V ≃ₗ[K] V)) ⊆ pointRad F e₁ := fun g (hg : g ∈ A₁) => hA₁ hg
      obtain ⟨g, hgA, c, hgc⟩ := ElationFull.om hnd halt hF1 hD hf₁ hω0
      have hgA' : g ∈ A₁ := hgA
      have hgU : g f ∈ Submodule.span K P := by
        rw [hgf g]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (hgP₂ g (Subgroup.mem_sup_left hgA')))
      have hωeq : ω = (g f - f) - c • e₁ := by
        rw [hgc]
        abel
      rw [hωeq]
      exact Submodule.sub_mem _ (Submodule.sub_mem _ hgU hfU)
        (Submodule.smul_mem _ _ (Submodule.subset_span he₁P))
    rw [eq_top_iff]
    intro v _
    have hperp : F (v - F v e₁ • f) e₁ = 0 := by
      simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, hF1', smul_eq_mul,
        mul_one, sub_self]
    have h1 := Submodule.add_mem _ (hω _ hperp) (Submodule.smul_mem _ (F v e₁) hfU)
    rwa [sub_add_cancel] at h1
  have hgen : A₁ ⊔ A₂ = Subgroup.closure
      (⋃ e ∈ P, ((A₁ ⊔ A₂ : Subgroup (V ≃ₗ[K] V)) : Set (V ≃ₗ[K] V)) ∩ pointRad F e) := by
    refine le_antisymm (sup_le ?_ ?_) ?_
    · intro g hg
      exact Subgroup.subset_closure (Set.mem_iUnion₂.mpr
        ⟨e₁, he₁P, ⟨Subgroup.mem_sup_left hg, hA₁ hg⟩⟩)
    · intro g hg
      exact Subgroup.subset_closure (Set.mem_iUnion₂.mpr
        ⟨e₂, he₂P, ⟨Subgroup.mem_sup_right hg, hA₂ hg⟩⟩)
    · refine (Subgroup.closure_le _).mpr ?_
      intro g hg
      obtain ⟨e, -, hgH, -⟩ := Set.mem_iUnion₂.mp hg
      exact hgH
  exact hX K V F h4 hnd halt hdim (A₁ ⊔ A₂) hH P hP0 hspan hfull hgen

end CFSG.RankThree.GF2n.Stroth80.Classify
