module

public import CFSG.Quasithin.Background.SmithCurtisMain

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis

section Generic

variable {G : Type*} [Group G] [Finite G] {B : Type*} {M : CoxeterMatrix B} {W : Type*}
  [Group W] {cs : CoxeterSystem M W} {p : ℕ} {D : CurtisDatum G cs p}
  {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {ρ : Representation k G V}

theorem isCurtisType_comp {y : V} {χ : G → k} {μ : B → k} (ht : D.IsCurtisType ρ y χ μ)
    (γ : G ≃* G) (π : B → B) (hU : ∀ u ∈ D.U, γ u ∈ D.U) (hH : ∀ h ∈ D.H, γ h ∈ D.H)
    (hX : ∀ s x, x ∈ D.X s ↔ γ x ∈ D.X (π s)) (hn : ∀ s, γ (D.n s) = D.n (π s)) :
    D.IsCurtisType (ρ.comp γ.toMonoidHom) y (χ ∘ γ) (μ ∘ π) := by
  obtain ⟨hy, hy0, hχ, hμ⟩ := ht
  refine ⟨?_, hy0, fun h hh => hχ (γ h) (hH h hh), fun s => ?_⟩
  · rw [D.mem_fixU]
    exact fun u hu => (D.mem_fixU (ρ := ρ) (v := y)).mp hy (γ u) (hU u hu)
  · let e : D.X s ≃ D.X (π s) :=
      { toFun := fun x => ⟨γ (x : G), (hX s (x : G)).mp x.2⟩
        invFun := fun z => ⟨γ.symm (z : G),
          (hX s (γ.symm (z : G))).mpr (by rw [γ.apply_symm_apply]; exact z.2)⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun z => Subtype.ext (by simp) }
    have hfin_s : Fintype (D.X s) := Fintype.ofFinite (D.X s)
    have hfin_π : Fintype (D.X (π s)) := Fintype.ofFinite (D.X (π s))
    show D.heckeT (ρ.comp γ.toMonoidHom) s y = μ (π s) • y
    rw [D.heckeT_apply (ρ.comp γ.toMonoidHom) s y, ← hμ (π s), D.heckeT_apply ρ (π s) y]
    refine Fintype.sum_equiv e _ _ (fun x => ?_)
    show ρ (γ ((x : G) * D.n s)) y = ρ ((e x : G) * D.n (π s)) y
    rw [map_mul, hn]
    rfl

theorem isSimpleRep_comp_mulEquiv (hρ : IsSimpleRep ρ) (γ : G ≃* G) :
    IsSimpleRep (ρ.comp γ.toMonoidHom) :=
  ⟨hρ.1, fun W hW => hρ.2 W fun g w hw => by simpa using hW (γ.symm g) w hw⟩

end Generic

end CFSG.LocalAnalysis.WeakClosure81
