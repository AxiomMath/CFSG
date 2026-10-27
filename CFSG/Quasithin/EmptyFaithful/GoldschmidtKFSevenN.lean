module

public import CFSG.Quasithin.EmptyFaithful.SBd18Out

public section

namespace CFSG.Quasithin.SBd19F

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem fixedSub_conj {G : Type*} [Group G] (φ α : MulAut G) :
    SBd18.fixedSub (φ * α * φ⁻¹) = (SBd18.fixedSub α).map φ.toMonoidHom := by
  ext x
  rw [SBd18.mem_fixedSub]
  constructor
  · intro h
    refine ⟨φ⁻¹ x, ?_, ?_⟩
    · show φ⁻¹ x ∈ SBd18.fixedSub α
      rw [SBd18.mem_fixedSub]
      have h1 : φ (α (φ⁻¹ x)) = x := h
      calc α (φ⁻¹ x) = φ⁻¹ (φ (α (φ⁻¹ x))) := by simp
        _ = φ⁻¹ x := by rw [h1]
    · simp
  · rintro ⟨y, hy, rfl⟩
    have h1 : α y = y := SBd18.mem_fixedSub.mp hy
    change φ (α (φ⁻¹ (φ y))) = φ y
    simp [h1]

theorem not_isSolvable_fixedSub_conj {G : Type*} [Group G] (φ α : MulAut G)
    (h : ¬ Group.IsSolvable ↥(SBd18.fixedSub α)) :
    ¬ Group.IsSolvable ↥(SBd18.fixedSub (φ * α * φ⁻¹)) := by
  intro hs
  apply h
  have hs' : Group.IsSolvable ↥((SBd18.fixedSub α).map φ.toMonoidHom) := by
    rw [← fixedSub_conj]
    exact hs
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.equivMapOfInjective (SBd18.fixedSub α) φ.toMonoidHom φ.injective).toMonoidHom)
    (Subgroup.equivMapOfInjective (SBd18.fixedSub α) φ.toMonoidHom φ.injective).injective

theorem not_isSolvable_fixedSub_of_hom {K : Type} [Field K] [Finite K] (hK : 4 ≤ Nat.card K)
    (Φ : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 3) K)
    {α : MulAut (projectiveSL 3 K)} (hfix : ∀ h, α (proj 3 K (Φ h)) = proj 3 K (Φ h))
    (hnt : ∃ h, proj 3 K (Φ h) ≠ 1) :
    ¬ Group.IsSolvable ↥(SBd18.fixedSub α) := by
  intro hsolv
  let f : SpecialLinearGroup (Fin 2) K →* projectiveSL 3 K := (proj 3 K).comp Φ
  have : Group.IsPerfect (SpecialLinearGroup (Fin 2) K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
  have : Group.IsPerfect ↥f.range := Group.IsPerfect.ofSurjective f.rangeRestrict_surjective
  have hnt' : Nontrivial ↥f.range := by
    obtain ⟨h, hh⟩ := hnt
    exact ⟨⟨⟨f h, h, rfl⟩, 1, fun e => hh (congrArg Subtype.val e)⟩⟩
  have hle : f.range ≤ SBd18.fixedSub α := by
    rintro _ ⟨h, rfl⟩
    exact SBd18.mem_fixedSub.mpr (hfix h)
  have : Group.IsSolvable ↥f.range :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  exact Group.IsPerfect.not_isSolvable ↥f.range this

end CFSG.Quasithin.SBd19F
