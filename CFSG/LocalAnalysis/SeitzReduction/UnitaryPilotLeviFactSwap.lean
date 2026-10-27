module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotLeviFactPiece
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotLeviFactSU

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono le_perfectCore_of_perfect
  perfectCore_perfect)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.LinearPilot (fixAll mem_fixAll fixAll_comp_of_surjective
  centralizerPerfectCore_eq_map_of_le)

section Prod

variable {S S' : Type*} [Group S] [Group S']

theorem prodCongr_apply_eq (α β : MulAut S) (x : S × S) :
    (α.prodCongr β) x = (α x.1, β x.2) :=
  rfl

theorem fixAll_prodCongr {ι : Type*} (α : ι → MulAut S) :
    fixAll (fun j => (α j).prodCongr (α j)) = (fixAll α).prod (fixAll α) := by
  ext x
  simp only [mem_fixAll, mem_prod, prodCongr_apply_eq, Prod.ext_iff, forall_and]

theorem perfectCore_prod [Finite S] [Finite S'] (A : Subgroup S) (B : Subgroup S') :
    perfectCore (A.prod B) = (perfectCore A).prod (perfectCore B) := by
  apply le_antisymm
  · rw [le_prod_iff]
    constructor
    · rw [CFSG.Quasithin.map_perfectCore]
      refine perfectCore_mono ?_
      rw [map_le_iff_le_comap]
      exact fun x hx => (mem_prod.1 hx).1
    · rw [CFSG.Quasithin.map_perfectCore]
      refine perfectCore_mono ?_
      rw [map_le_iff_le_comap]
      exact fun x hx => (mem_prod.1 hx).2
  · refine le_perfectCore_of_perfect (prod_mono (perfectCore_le A) (perfectCore_le B)) ?_
    rw [commutator_prod_prod, perfectCore_perfect, perfectCore_perfect]

end Prod

section Swap

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {n : ℕ} (e : L ≃* unitaryPSU h n)

@[expose] def TorusEquivariantProd (N I : Finset (Fin n))
    (Ψ : unitaryBlock h N × unitaryBlock h N →* G) : Prop :=
  ∀ c : unitaryTorusParam h (∅ : Finset (Fin n)), c.1 ∈ unitaryTorusParam h I →
    ∀ x : unitaryBlock h N × unitaryBlock h N,
      Ψ (conjTorusSU h N c x.1, conjTorusSU h N c x.2) =
        ((e.symm (unitaryProj h n (torusDiagSU h c)) : L) : G) * Ψ x *
          ((e.symm (unitaryProj h n (torusDiagSU h c)) : L) : G)⁻¹

theorem pieceCore_eq_map_of_conjTorusSU_prod {N I : Finset (Fin n)} (hIN : I ⊆ N)
    (hI2 : 2 ≤ I.card) (hIc : 2 ≤ Iᶜ.card)
    (hperf : ⁅unitaryBlock h I, unitaryBlock h I⁆ = unitaryBlock h I)
    {X : Subgroup G} (hXI : X ≤ modelToG e (unitaryBlockTorus h I))
    (Ψ : unitaryBlock h N × unitaryBlock h N →* G)
    (hker : Ψ.ker ≤ center (unitaryBlock h N × unitaryBlock h N))
    (hrange : Ψ.range = centralizerPerfectCore X) (hΨ : TorusEquivariantProd e N I Ψ) :
    pieceCore e I = (((unitaryBlock h I).subgroupOf (unitaryBlock h N)).prod
      ((unitaryBlock h I).subgroupOf (unitaryBlock h N))).map Ψ := by
  have := h.finite
  set T := modelToG e (unitaryBlockTorus h I)
  let φ : T → unitaryBlockTorus h I := fun d =>
    ⟨e ⟨(d : G), modelToG_le e _ d.2⟩, apply_mem_unitaryBlockTorus_of_mem_modelToG e d.2⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    refine ⟨⟨((e.symm y : L) : G), symm_mem_modelToG e hy⟩, Subtype.ext ?_⟩
    simp [φ]
  set β : unitaryBlockTorus h I → MulAut (unitaryBlock h N) :=
    fun d => conjTorusSU h N (unitaryBlockTorusLift h d) with hβ
  have hα : ∀ (d : T) (x : unitaryBlock h N × unitaryBlock h N),
      Ψ (((β (φ d)).prodCongr (β (φ d))) x) = (d : G) * Ψ x * (d : G)⁻¹ := by
    intro d x
    rw [prodCongr_apply_eq]
    change Ψ (conjTorusSU h N (unitaryBlockTorusLift h (φ d)) x.1,
      conjTorusSU h N (unitaryBlockTorusLift h (φ d)) x.2) = _
    rw [hΨ _ (unitaryBlockTorusLift_mem h (φ d)) x,
      unitaryProj_torusDiagSU_unitaryBlockTorusLift]
    have hd : ((e.symm ((φ d : unitaryBlockTorus h I) : unitaryPSU h n) : L) : G) = (d : G) := by
      simp [φ]
    rw [hd]
  rw [pieceCore_def, centralizerPerfectCore_eq_map_of_le Ψ hker hXI hrange
    (fun d => (β (φ d)).prodCongr (β (φ d))) hα]
  congr 1
  rw [show (fixAll fun d : T => (β (φ d)).prodCongr (β (φ d))) =
      fixAll (fun d : unitaryBlockTorus h I => (β d).prodCongr (β d)) from
    fixAll_comp_of_surjective (fun d : unitaryBlockTorus h I => (β d).prodCongr (β d)) hφ,
    fixAll_prodCongr, perfectCore_prod, hβ,
    perfectCore_fixAll_conjTorusSU_unitaryBlockTorusLift h hIN hI2 hIc hperf]

theorem pieceCore_eq_map_of_neighbourCore_prod {a b : Fin n} (hab : a ≠ b)
    {I : Finset (Fin n)} (hI : I ⊆ {a, b}ᶜ) (hI2 : 2 ≤ I.card)
    (hperf : ⁅unitaryBlock h I, unitaryBlock h I⁆ = unitaryBlock h I)
    (Ψ : unitaryBlock h ({a, b}ᶜ : Finset (Fin n)) × unitaryBlock h ({a, b}ᶜ : Finset (Fin n)) →* G)
    (hker : Ψ.ker ≤ center (unitaryBlock h ({a, b}ᶜ : Finset (Fin n)) ×
      unitaryBlock h ({a, b}ᶜ : Finset (Fin n))))
    (hrange : Ψ.range = neighbourCore e hab) (hΨ : TorusEquivariantProd e {a, b}ᶜ I Ψ) :
    pieceCore e I = (((unitaryBlock h I).subgroupOf (unitaryBlock h {a, b}ᶜ)).prod
      ((unitaryBlock h I).subgroupOf (unitaryBlock h {a, b}ᶜ))).map Ψ :=
  pieceCore_eq_map_of_conjTorusSU_prod e hI hI2 (two_le_card_compl_of_subset_compl_pair hab hI)
    hperf (modelToG_unitaryRootTorus_le e hab hI) Ψ hker hrange hΨ

theorem map_prod_eq_map_prod_of_conjTorusSU {N N' I : Finset (Fin n)} (hIN : I ⊆ N)
    (hIN' : I ⊆ N') (hI2 : 2 ≤ I.card) (hIc : 2 ≤ Iᶜ.card)
    (hperf : ⁅unitaryBlock h I, unitaryBlock h I⁆ = unitaryBlock h I) {X X' : Subgroup G}
    (hXI : X ≤ modelToG e (unitaryBlockTorus h I)) (hXI' : X' ≤ modelToG e (unitaryBlockTorus h I))
    (Ψ : unitaryBlock h N × unitaryBlock h N →* G)
    (hker : Ψ.ker ≤ center (unitaryBlock h N × unitaryBlock h N))
    (hrange : Ψ.range = centralizerPerfectCore X) (hΨ : TorusEquivariantProd e N I Ψ)
    (Ψ' : unitaryBlock h N' × unitaryBlock h N' →* G)
    (hker' : Ψ'.ker ≤ center (unitaryBlock h N' × unitaryBlock h N'))
    (hrange' : Ψ'.range = centralizerPerfectCore X') (hΨ' : TorusEquivariantProd e N' I Ψ') :
    (((unitaryBlock h I).subgroupOf (unitaryBlock h N)).prod
        ((unitaryBlock h I).subgroupOf (unitaryBlock h N))).map Ψ =
      (((unitaryBlock h I).subgroupOf (unitaryBlock h N')).prod
        ((unitaryBlock h I).subgroupOf (unitaryBlock h N'))).map Ψ' := by
  rw [← pieceCore_eq_map_of_conjTorusSU_prod e hIN hI2 hIc hperf hXI Ψ hker hrange hΨ,
    ← pieceCore_eq_map_of_conjTorusSU_prod e hIN' hI2 hIc hperf hXI' Ψ' hker' hrange' hΨ']

end Swap

end CFSG.SeitzReduction.UnitaryPilot
