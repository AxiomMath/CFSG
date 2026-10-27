module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFSevenMain
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFJRed
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldFourCover
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem fixedSub_autTransfer {G H : Type} [Group G] [Group H] (e : G ≃* H) (φ : MulAut G) :
    SBd18.fixedSub (autTransfer e φ) = (SBd18.fixedSub φ).map e.toMonoidHom := by
  ext y
  rw [SBd18.mem_fixedSub]
  constructor
  · intro h
    refine ⟨e.symm y, ?_, by simp⟩
    show e.symm y ∈ SBd18.fixedSub φ
    rw [SBd18.mem_fixedSub]
    have h1 : e (φ (e.symm y)) = y := h
    calc φ (e.symm y) = e.symm (e (φ (e.symm y))) := by simp
      _ = e.symm y := by rw [h1]
  · rintro ⟨x, hx, rfl⟩
    have h1 : φ x = x := SBd18.mem_fixedSub.mp hx
    change e (φ (e.symm (e x))) = e x
    simp [h1]

theorem not_isSolvable_fixedSub_of_autTransfer {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (φ : MulAut G) (h : ¬ Group.IsSolvable ↥(SBd18.fixedSub (autTransfer e φ))) :
    ¬ Group.IsSolvable ↥(SBd18.fixedSub φ) := by
  intro hs
  apply h
  rw [fixedSub_autTransfer]
  exact Group.isSolvable_of_surjective
    (f := (Subgroup.equivMapOfInjective (SBd18.fixedSub φ) e.toMonoidHom e.injective).toMonoidHom)
    (Subgroup.equivMapOfInjective (SBd18.fixedSub φ) e.toMonoidHom e.injective).surjective

theorem nonsolv_of_isPSL_three_seven {L₂ : Type} [Group L₂] [Finite L₂]
    (h : IsPSL 3 7 1 (L₂ ⧸ Subgroup.center L₂)) (u : MulAut L₂) (hu : u * u = 1) :
    ¬ Group.IsSolvable ↥(SBd18.fixedSub u) := by
  have hLie : CFSG.Blueprint.LieModel (L₂ ⧸ Subgroup.center L₂) .PSL 3 7 1 :=
    Or.inl ⟨by decide, h⟩
  obtain ⟨k, _, _, hcard, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hLie
  have hk : Nat.card k = 7 := by rw [hcard]; norm_num
  have : Finite (L₂ ⧸ Subgroup.center L₂) := inferInstance
  have hfin : Finite k := Nat.finite_of_card_ne_zero (by omega)
  apply not_isSolvable_fixedSub_of_quotient
  apply not_isSolvable_fixedSub_of_autTransfer e
  apply not_isSolvable_fixedSub_of_sq hk
  rw [← map_mul, ← map_mul, hu, map_one, map_one]

end CFSG.Quasithin.SBd19F
