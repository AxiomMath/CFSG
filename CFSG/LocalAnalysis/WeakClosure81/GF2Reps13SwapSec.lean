module

public import CFSG.Quasithin.Background.D2Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W]

abbrev SecT (U₂ U₁ : Subgroup W) : Type := ↥U₂ ⧸ U₁.subgroupOf U₂

@[expose] def secStabAll (U₂ U₁ : Subgroup W) : Subgroup (MulAut W) := stabSub U₂ ⊓ stabSub U₁

theorem map_resAut_subgroupOf (U₂ U₁ : Subgroup W) (g : ↥(secStabAll U₂ U₁)) :
    (U₁.subgroupOf U₂).map (resAut U₂ ⟨g.1, g.2.1⟩).toMonoidHom = U₁.subgroupOf U₂ := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact (g.2.2 (y : W)).2 hy
  · intro hx
    refine ⟨(resAut U₂ ⟨g.1, g.2.1⟩).symm x, ?_, by simp⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have h := (g.2.2 (((resAut U₂ ⟨g.1, g.2.1⟩).symm x : ↥U₂) : W)).1
    refine h ?_
    have : (g.1 (((resAut U₂ ⟨g.1, g.2.1⟩).symm x : ↥U₂) : W)) = (x : W) := by
      have := congrArg (fun z : ↥U₂ => (z : W))
        ((resAut U₂ ⟨g.1, g.2.1⟩).apply_symm_apply x)
      simpa [resAut] using this
    rw [this]
    exact hx

@[expose] noncomputable def secAut (U₂ U₁ : Subgroup W) :
    ↥(secStabAll U₂ U₁) →* MulAut (SecT U₂ U₁) where
  toFun g := QuotientGroup.congr (U₁.subgroupOf U₂) (U₁.subgroupOf U₂)
    (resAut U₂ ⟨g.1, g.2.1⟩) (map_resAut_subgroupOf U₂ U₁ g)
  map_one' := by
    apply MulEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H w => rfl
  map_mul' g h := by
    apply MulEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H w => rfl

theorem secAut_mk (U₂ U₁ : Subgroup W) (g : ↥(secStabAll U₂ U₁)) (u : ↥U₂) :
    secAut U₂ U₁ g (QuotientGroup.mk u) = QuotientGroup.mk (resAut U₂ ⟨g.1, g.2.1⟩ u) := rfl

@[expose] noncomputable def secImg (X : Subgroup (MulAut W)) (U₂ U₁ : Subgroup W) :
    Subgroup (MulAut (SecT U₂ U₁)) :=
  (X.subgroupOf (secStabAll U₂ U₁)).map (secAut U₂ U₁)

theorem mem_secImg {X : Subgroup (MulAut W)} {U₂ U₁ : Subgroup W} {φ : MulAut (SecT U₂ U₁)} :
    φ ∈ secImg X U₂ U₁ ↔ ∃ g : ↥(secStabAll U₂ U₁), (g : MulAut W) ∈ X ∧ secAut U₂ U₁ g = φ := by
  simp [secImg, Subgroup.mem_map, Subgroup.mem_subgroupOf]

@[expose] noncomputable def secCost (t : MulAut W) (U₂ U₁ : Subgroup W) : ℕ :=
  rk ↥(commSub U₂ (Subgroup.zpowers t) ⊔ U₁) - rk ↥U₁

end CFSG.LocalAnalysis.WeakClosure81
