module

public import CFSG.Sporadic.Recognition.ThMultiplierConfig

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.Sporadic.Recognition.ThMultiplier

open CFSG.GroupTheory.GLnTwoSplitting CFSG.LocalAnalysis.DempwolffFive Matrix

namespace Config

variable {Γ : Type*} [Group Γ] (X : Config Γ)

theorem a_conj_mem (k : Fin 3) (j : Fin 5) : X.a k * X.v j * (X.a k)⁻¹ ∈ X.Vsub := by
  rw [X.a_conj]
  exact X.iota_mem_Vsub _

theorem a_mem_Hsub (k : Fin 3) : X.a k ∈ X.Hsub :=
  X.mem_normalizer_of_conj (X.a_conj_mem k)

@[expose] def aH (k : Fin 3) : X.Hsub := ⟨X.a k, X.a_mem_Hsub k⟩

theorem actV_eq_mulVec (g : X.Hsub) (M : Matrix (Fin 5) (Fin 5) (ZMod 2))
    (h : ∀ j, (g : Γ) * X.v j * (g : Γ)⁻¹ = X.iota (fun i => M i j)) (e : Fin 5 → ZMod 2) :
    X.actV g e = M *ᵥ e := by
  have key : ((X.actV g : (Fin 5 → ZMod 2) ≃ₗ[ZMod 2] (Fin 5 → ZMod 2)) :
      (Fin 5 → ZMod 2) →ₗ[ZMod 2] (Fin 5 → ZMod 2)) = Matrix.toLin' M := by
    refine (Pi.basisFun (ZMod 2) (Fin 5)).ext fun j => ?_
    rw [Pi.basisFun_apply]
    apply X.iotaH_injective
    have h1 := X.actV_spec g (Pi.single j 1)
    have h2 : X.iotaH (Pi.single j 1) = ⟨X.v j, X.Vsub_le_Hsub (X.v_mem_Vsub j)⟩ :=
      Subtype.ext (X.iota_single j)
    rw [h2] at h1
    have h3 : X.iotaH (X.actV g (Pi.single j 1)) = X.iotaH (M *ᵥ Pi.single j 1) := by
      rw [← h1]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [h j, Matrix.mulVec_single_one]
      rfl
    simpa [Matrix.toLin'_apply] using h3
  exact DFunLike.congr_fun key e

theorem actV_aH (k : Fin 3) (e : Fin 5 → ZMod 2) :
    X.actV (X.aH k) e = ((X.atom k : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ e :=
  X.actV_eq_mulVec (X.aH k) _ (X.a_conj k) e

theorem ρV_atom (k : Fin 3) : ρV (X.atom k) = X.actV (X.aH k) := LinearEquiv.ext fun e => by
  rw [ρV_apply, X.actV_aH k]

@[expose] def letter (l : Fin 3 × Bool) : GL (Fin 5) (ZMod 2) :=
  if l.2 then (X.atom l.1)⁻¹ else X.atom l.1

theorem evalWord_mem (w : List (Fin 3 × Bool)) :
    (w.map X.letter).prod ∈ Subgroup.closure (Set.range X.atom) := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
  unfold letter
  split_ifs
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨l.1, rfl⟩)
  · exact Subgroup.subset_closure ⟨l.1, rfl⟩

theorem xg_mem_closure_atom (s : Sym) : xg s ∈ Subgroup.closure (Set.range X.atom) := by
  obtain ⟨i, j, c⟩ := s
  by_cases hij : i = j
  · subst hij
    have : xg (i, i, c) = 1 := Units.ext (by simp [xg, symMat])
    rw [this]
    exact Subgroup.one_mem _
  · fin_cases c
    · have : xg (i, j, 0) = 1 := Units.ext (by simp [xg, symMat, hij])
      change xg (i, j, 0) ∈ _
      rw [this]
      exact Subgroup.one_mem _
    · change xg (i, j, 1) ∈ _
      rw [X.word_spec i j hij]
      exact X.evalWord_mem _

theorem toMatrix'_mul_symm' (f : V ≃ₗ[ZMod 2] V) :
    LinearMap.toMatrix' (f : V →ₗ[ZMod 2] V) * LinearMap.toMatrix' (f.symm : V →ₗ[ZMod 2] V) =
      1 := by
  rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
  congr 1
  exact LinearMap.ext fun v => f.apply_symm_apply v

theorem toMatrix'_symm_mul' (f : V ≃ₗ[ZMod 2] V) :
    LinearMap.toMatrix' (f.symm : V →ₗ[ZMod 2] V) * LinearMap.toMatrix' (f : V →ₗ[ZMod 2] V) =
      1 := by
  rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
  congr 1
  exact LinearMap.ext fun v => f.symm_apply_apply v

theorem ρV_surjective' : Function.Surjective ρV := by
  intro f
  refine ⟨⟨LinearMap.toMatrix' (f : V →ₗ[ZMod 2] V), LinearMap.toMatrix' (f.symm : V →ₗ[ZMod 2] V),
    toMatrix'_mul_symm' f, toMatrix'_symm_mul' f⟩, LinearEquiv.ext fun v => ?_⟩
  rw [ρV_apply]
  exact LinearMap.toMatrix'_mulVec (f : V →ₗ[ZMod 2] V) v

theorem actV_surjective : Function.Surjective X.actV := by
  intro T
  obtain ⟨g, rfl⟩ := ρV_surjective' T
  have hg : g ∈ Subgroup.closure (Set.range X.atom) := by
    have h1 : g ∈ Subgroup.closure (Set.range xg) := by
      rw [closure_range_xg]
      exact Subgroup.mem_top g
    exact (Subgroup.closure_le _ |>.2 (by
      rintro _ ⟨s, rfl⟩
      exact X.xg_mem_closure_atom s)) h1
  have hS : Subgroup.closure (Set.range X.atom) ≤ (X.actV.range).comap ρV := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨X.aH k, (X.ρV_atom k).symm⟩
  exact hS hg

end Config

end CFSG.Sporadic.Recognition.ThMultiplier
