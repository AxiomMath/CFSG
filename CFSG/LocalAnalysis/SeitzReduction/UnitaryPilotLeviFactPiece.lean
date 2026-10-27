module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotLeviFact
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCores

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear blockSpecialLinear_mono fixAll
  fixAll_comp_of_surjective centralizerPerfectCore_eq_map_of_le)

section General

variable {G : Type*} [Group G] {L : Subgroup G} {p f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData p f K} {n : ℕ}

theorem apply_mem_unitaryBlockTorus_of_mem_modelToG (e : L ≃* unitaryPSU h n)
    {I : Finset (Fin n)} {d : G} (hd : d ∈ modelToG e (unitaryBlockTorus h I)) :
    e ⟨d, modelToG_le e _ hd⟩ ∈ unitaryBlockTorus h I :=
  (coe_mem_modelToG_iff e (y := ⟨d, modelToG_le e _ hd⟩)).1 hd

theorem pieceCore_eq_map_of_conjTorus_of_sep [Finite G] (e : L ≃* unitaryPSU h n)
    {N I : Finset (Fin n)} (hIN : I ⊆ N)
    (hsep : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → (i ∉ I ∨ j ∉ I) →
      ∃ c ∈ unitaryTorusParam h I, c i ≠ c j)
    (hperf : ⁅blockSpecialLinear (K := K) I, blockSpecialLinear (K := K) I⁆ =
      blockSpecialLinear I)
    {X : Subgroup G} (hXI : X ≤ modelToG e (unitaryBlockTorus h I))
    (Φ : blockSpecialLinear (K := K) N →* G)
    (hker : Φ.ker ≤ center (blockSpecialLinear (K := K) N))
    (hrange : Φ.range = centralizerPerfectCore X)
    (hΦ : ∀ c : unitaryTorusParam h (∅ : Finset (Fin n)), c.1 ∈ unitaryTorusParam h I →
      ∀ x : blockSpecialLinear (K := K) N,
        Φ (conjTorus h N c x) = ((e.symm (unitaryProj h n (torusDiagSU h c)) : L) : G) * Φ x *
          ((e.symm (unitaryProj h n (torusDiagSU h c)) : L) : G)⁻¹) :
    pieceCore e I = ((blockSpecialLinear (K := K) I).subgroupOf (blockSpecialLinear N)).map Φ := by
  have := h.finite
  set T := modelToG e (unitaryBlockTorus h I)
  let φ : T → unitaryBlockTorus h I := fun d =>
    ⟨e ⟨(d : G), modelToG_le e _ d.2⟩, apply_mem_unitaryBlockTorus_of_mem_modelToG e d.2⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    refine ⟨⟨((e.symm y : L) : G), symm_mem_modelToG e hy⟩, Subtype.ext ?_⟩
    simp [φ]
  have hα : ∀ (d : T) (x : blockSpecialLinear (K := K) N),
      Φ (conjTorus h N (unitaryBlockTorusLift h (φ d)) x) = (d : G) * Φ x * (d : G)⁻¹ := by
    intro d x
    rw [hΦ _ (unitaryBlockTorusLift_mem h (φ d)) x,
      unitaryProj_torusDiagSU_unitaryBlockTorusLift]
    have hd : ((e.symm ((φ d : unitaryBlockTorus h I) : unitaryPSU h n) : L) : G) = (d : G) := by
      simp [φ]
    rw [hd]
  rw [pieceCore_def, centralizerPerfectCore_eq_map_of_le Φ hker hXI hrange
    (fun d => conjTorus h N (unitaryBlockTorusLift h (φ d))) hα]
  congr 1
  rw [show (fixAll fun d : T => conjTorus h N (unitaryBlockTorusLift h (φ d))) =
      fixAll (fun d : unitaryBlockTorus h I => conjTorus h N (unitaryBlockTorusLift h d)) from
    fixAll_comp_of_surjective
      (fun d : unitaryBlockTorus h I => conjTorus h N (unitaryBlockTorusLift h d)) hφ]
  refine perfectCore_fixAll_conjTorus h hIN _ (unitaryBlockTorusLift_mem h)
    (fun i hi j hj hij hIJ => ?_) hperf
  obtain ⟨c, hc, hcij⟩ := hsep i hi j hj hij hIJ
  exact exists_unitaryBlockTorusLift_ne h hc hcij

theorem pieceCore_eq_range_of_conjTorus [Finite G] (e : L ≃* unitaryPSU h n)
    {N : Finset (Fin n)}
    (hperf : ⁅blockSpecialLinear (K := K) N, blockSpecialLinear (K := K) N⁆ =
      blockSpecialLinear N)
    {X : Subgroup G} (hXN : X ≤ modelToG e (unitaryBlockTorus h N))
    (Φ : blockSpecialLinear (K := K) N →* G)
    (hker : Φ.ker ≤ center (blockSpecialLinear (K := K) N))
    (hrange : Φ.range = centralizerPerfectCore X)
    (hΦ : ∀ c : unitaryTorusParam h (∅ : Finset (Fin n)), c.1 ∈ unitaryTorusParam h N →
      ∀ x : blockSpecialLinear (K := K) N,
        Φ (conjTorus h N c x) = ((e.symm (unitaryProj h n (torusDiagSU h c)) : L) : G) * Φ x *
          ((e.symm (unitaryProj h n (torusDiagSU h c)) : L) : G)⁻¹) :
    pieceCore e N = Φ.range := by
  rw [pieceCore_eq_map_of_conjTorus_of_sep e subset_rfl
    (fun _ hi _ hj _ hIJ => absurd hIJ (by simp [hi, hj])) hperf hXN Φ hker hrange hΦ,
    subgroupOf_self, ← MonoidHom.range_eq_map]

end General

section Even

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {n : ℕ} (e : L ≃* unitaryPSU h n)

@[expose] def TorusEquivariant (N I : Finset (Fin n)) (Φ : blockSpecialLinear (K := K) N →* G) :
    Prop :=
  ∀ c : unitaryTorusParam h (∅ : Finset (Fin n)), c.1 ∈ unitaryTorusParam h I →
    ∀ x : blockSpecialLinear (K := K) N,
      Φ (conjTorus h N c x) = ((e.symm (unitaryProj h n (torusDiagSU h c)) : L) : G) * Φ x *
        ((e.symm (unitaryProj h n (torusDiagSU h c)) : L) : G)⁻¹

omit [Finite G] in
theorem TorusEquivariant.mono {N I I' : Finset (Fin n)} (hII' : I ⊆ I')
    {Φ : blockSpecialLinear (K := K) N →* G} (hΦ : TorusEquivariant e N I Φ) :
    TorusEquivariant e N I' Φ :=
  fun c hc x => hΦ c (unitaryTorusParam_anti h hII' hc) x

theorem pieceCore_eq_map_of_conjTorus {N I : Finset (Fin n)} (hIN : I ⊆ N) (hI2 : 2 ≤ I.card)
    (hIc : 2 ≤ Iᶜ.card) {X : Subgroup G} (hXI : X ≤ modelToG e (unitaryBlockTorus h I))
    (Φ : blockSpecialLinear (K := K) N →* G)
    (hker : Φ.ker ≤ center (blockSpecialLinear (K := K) N))
    (hrange : Φ.range = centralizerPerfectCore X) (hΦ : TorusEquivariant e N I Φ) :
    pieceCore e I = ((blockSpecialLinear (K := K) I).subgroupOf (blockSpecialLinear N)).map Φ :=
  pieceCore_eq_map_of_conjTorus_of_sep e hIN
    (fun _ _ _ _ hij hIJ => exists_mem_unitaryTorusParam_ne h hIc hij hIJ)
    (commutator_blockSpecialLinear_eq_of_unitaryFieldData h hI2) hXI Φ hker hrange hΦ

theorem pieceCore_eq_map_of_neighbourCore {a b : Fin n} (hab : a ≠ b) {I : Finset (Fin n)}
    (hI : I ⊆ {a, b}ᶜ) (hI2 : 2 ≤ I.card)
    (Φ : blockSpecialLinear (K := K) ({a, b}ᶜ : Finset (Fin n)) →* G)
    (hker : Φ.ker ≤ center (blockSpecialLinear (K := K) ({a, b}ᶜ : Finset (Fin n))))
    (hrange : Φ.range = neighbourCore e hab) (hΦ : TorusEquivariant e {a, b}ᶜ I Φ) :
    pieceCore e I = ((blockSpecialLinear (K := K) I).subgroupOf
      (blockSpecialLinear ({a, b}ᶜ : Finset (Fin n)))).map Φ :=
  pieceCore_eq_map_of_conjTorus e hI hI2 (two_le_card_compl_of_subset_compl_pair hab hI)
    (modelToG_unitaryRootTorus_le e hab hI) Φ hker hrange hΦ

theorem map_eq_map_of_conjTorus {N N' I : Finset (Fin n)} (hIN : I ⊆ N) (hIN' : I ⊆ N')
    (hI2 : 2 ≤ I.card) (hIc : 2 ≤ Iᶜ.card) {X X' : Subgroup G}
    (hXI : X ≤ modelToG e (unitaryBlockTorus h I)) (hXI' : X' ≤ modelToG e (unitaryBlockTorus h I))
    (Φ : blockSpecialLinear (K := K) N →* G)
    (hker : Φ.ker ≤ center (blockSpecialLinear (K := K) N))
    (hrange : Φ.range = centralizerPerfectCore X) (hΦ : TorusEquivariant e N I Φ)
    (Φ' : blockSpecialLinear (K := K) N' →* G)
    (hker' : Φ'.ker ≤ center (blockSpecialLinear (K := K) N'))
    (hrange' : Φ'.range = centralizerPerfectCore X') (hΦ' : TorusEquivariant e N' I Φ') :
    ((blockSpecialLinear (K := K) I).subgroupOf (blockSpecialLinear N)).map Φ =
      ((blockSpecialLinear (K := K) I).subgroupOf (blockSpecialLinear N')).map Φ' := by
  rw [← pieceCore_eq_map_of_conjTorus e hIN hI2 hIc hXI Φ hker hrange hΦ,
    ← pieceCore_eq_map_of_conjTorus e hIN' hI2 hIc hXI' Φ' hker' hrange' hΦ']

theorem nonempty_mulEquiv_pieceCore_of_conjTorus {N I : Finset (Fin n)} (hIN : I ⊆ N)
    (hne : I ≠ N) (hI2 : 2 ≤ I.card) (hIc : 2 ≤ Iᶜ.card) {X : Subgroup G}
    (hXI : X ≤ modelToG e (unitaryBlockTorus h I))
    (Φ : blockSpecialLinear (K := K) N →* G)
    (hker : Φ.ker ≤ center (blockSpecialLinear (K := K) N))
    (hrange : Φ.range = centralizerPerfectCore X) (hΦ : TorusEquivariant e N I Φ) :
    Nonempty (Matrix.SpecialLinearGroup (Fin I.card) K ≃* pieceCore e I) := by
  set H := (blockSpecialLinear (K := K) I).subgroupOf (blockSpecialLinear (K := K) N)
  have hinj := LinearPilot.injective_comp_subtype_of_ker_le_center hIN hne Φ hker
  have hrangeH : (Φ.comp H.subtype).range = pieceCore e I := by
    rw [MonoidHom.range_comp, range_subtype,
      pieceCore_eq_map_of_conjTorus e hIN hI2 hIc hXI Φ hker hrange hΦ]
  have e₁ : H ≃* pieceCore e I :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrangeH)
  have e₂ : blockSpecialLinear (K := K) I ≃* H :=
    (Subgroup.subgroupOfEquivOfLe (blockSpecialLinear_mono hIN)).symm
  have e₃ : Matrix.SpecialLinearGroup (Fin I.card) K ≃* blockSpecialLinear (K := K) I :=
    (LinearPilot.reindexSpecialLinear I.equivFin).symm.trans
      ((MonoidHom.ofInjective (LinearPilot.blockEmbed_injective I)).trans
        (MulEquiv.subgroupCongr (LinearPilot.range_blockEmbed I)))
  exact ⟨e₃.trans (e₂.trans e₁)⟩

theorem pieceCore_le_centralizer_pieceCore_of_disjoint {N I J : Finset (Fin n)} (hIN : I ⊆ N)
    (hJN : J ⊆ N) (hIJ : Disjoint I J) (hI2 : 2 ≤ I.card) (hJ2 : 2 ≤ J.card)
    (hIc : 2 ≤ Iᶜ.card) (hJc : 2 ≤ Jᶜ.card) {X : Subgroup G}
    (hXI : X ≤ modelToG e (unitaryBlockTorus h I)) (hXJ : X ≤ modelToG e (unitaryBlockTorus h J))
    (Φ : blockSpecialLinear (K := K) N →* G)
    (hker : Φ.ker ≤ center (blockSpecialLinear (K := K) N))
    (hrange : Φ.range = centralizerPerfectCore X) (hΦI : TorusEquivariant e N I Φ)
    (hΦJ : TorusEquivariant e N J Φ) :
    pieceCore e I ≤ centralizer (pieceCore e J : Set G) := by
  rw [pieceCore_eq_map_of_conjTorus e hIN hI2 hIc hXI Φ hker hrange hΦI,
    pieceCore_eq_map_of_conjTorus e hJN hJ2 hJc hXJ Φ hker hrange hΦJ]
  exact LinearPilot.map_subgroupOf_le_centralizer_of_disjoint hIJ Φ

end Even

end CFSG.SeitzReduction.UnitaryPilot
