module

public import CFSG.Monster.B.TwoA.Fischer.AmbientRootComplete
public import CFSG.Monster.B.TwoA.Fischer.AdjointIntertwiner

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent AddSubgroupClass.instZModModule

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Fischer CFSG.Monster.B.TwoA CFSG.Monster.B.Classical.Mog22
  CFSG.Sporadic.SmallF2
open CFSG.Monster.B.E6.FixedE6 CFSG.Monster.B.E6.FixedE6Root CFSG.Monster.B.E6.StdF4
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open scoped Matrix IsMulCommutative

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

@[expose] def qRootOrbit
    (Q : Subgroup S) (ρQ : Q →* GStar) (x : rootClass) : Set rootClass :=
  {x' | ∃ q : Q, (SemidirectProduct.inl (x' : stdGroup) : GStar) =
    (ρQ q)⁻¹ * SemidirectProduct.inl (x : stdGroup) * ρQ q}

theorem qRootOrbit_eq
    (Q : Subgroup S) (ρQ : Q →* GStar) (x : rootClass) :
    qRootOrbit Q ρQ x = {x' : rootClass | rootVecOf (x' : stdGroup) ∈
      {u' | ∃ q : Q, u' = actStar (ρQ q) (rootVecOf (x : stdGroup))}} := by
  refine Set.ext fun x' : rootClass => ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨q, hq⟩ := h
    have h := rootVecOf_conj_star (ρQ q)⁻¹ x.2 (by rw [hq, inv_inv])
    exact ⟨q⁻¹, by rw [h.2, map_inv ρQ]⟩
  · obtain ⟨q, hq⟩ := h
    obtain ⟨hx'', e⟩ := rootVecOf_conj_star (ρQ q) x.2 (conj_inl (ρQ q) x).symm
    have e2 := bijOn_rootVecOf.injOn x'.2 hx'' (hq.trans e.symm)
    refine ⟨q⁻¹, ?_⟩
    rw [e2, ← conj_inl, map_inv ρQ, inv_inv]

namespace IsFischerSlice

theorem root_classes_of_choices
    (hS : IsFischerSlice act lab Y) {C : Set V}
    (hC : IsSliceMaxClique lab Y C) [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]
    {x : V} (hx : x ∈ hexadFiber lab Y C ∅) {η : C ≃ X₀}
    {θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
      CFSG.Blueprint.NativeSporadic.M22}
    (hη : ∀ T : Finset C, Subtype.val '' (T : Set C) ∈ cliqueBlocks lab C ↔
      T.image (fun z => (η z : Fin 24)) ∈ ℬ₀)
    (hθ : ∀ (f : setStab act lab Y C) (z : C),
      (η (setStabPerm act lab Y C f z) : Fin 24) = psiHom (θ f) (η z))
    {φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀}
    (hφ : ∀ z : C, φ (Additive.ofMul (cliqueGen z)) = K₀.mkQ (e (η z)))
    {α : setStab act lab Y C →* F₀}
    (hα : ∀ (r : Subgroup.closure (lab '' C)) (f k : setStab act lab Y C),
      (f : S) = r * k → act (k : S) x = x → α f = wF (φ (Additive.ofMul r)) * kF (θ k))
    {Φ : Y ≃ CFSG.Monster.B.Fischer.Y} (hΦ : IsCliqueIntertwiner act lab Y C x η φ α Φ)
    {ρ : sliceGroup lab Y →* stdGroup} (hρ : Function.Injective ρ)
    (hroot : ∀ y : Y, ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ ∈ rootClass)
    (Q : Subgroup S) (hHQ : sliceGroup lab Y ≤ Q) (hQY : ∀ q ∈ Q, ∀ y ∈ Y, act q y ∈ Y)
    (ρQ : Q →* GStar)
    (hρQ : ∀ (h : S) (hh : h ∈ sliceGroup lab Y),
      ρQ ⟨h, hHQ hh⟩ = SemidirectProduct.inl (ρ ⟨h, hh⟩)) :
    ∃ r : Fin 4 → rootClass,
      (∀ x : rootClass, ∃! k, x ∈ qRootOrbit Q ρQ (r k)) ∧
      qRootOrbit Q ρQ (r 0) =
        {x : rootClass | ∃ y : Y, ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ = (x : stdGroup)} ∧
      (∀ k, (qRootOrbit Q ρQ (r k)).ncard = (![3510, 142155, 694980, 3127410] : Fin 4 → ℕ) k) ∧
      ∀ k, ∀ x ∈ qRootOrbit Q ρQ (r k),
        {x' : rootClass | x' ∈ {x : rootClass |
            ∃ y : Y, ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ = (x : stdGroup)} ∧
          x' ≠ x ∧ Commute (x' : stdGroup) x}.ncard = (![693, 22, 126, 22] : Fin 4 → ℕ) k := by
  have H := FullIntertwinerHyp.mk hS hC hx hη hθ hφ hα
  obtain ⟨ψ, hψ, -, hxT, -⟩ := hS.canonical_permutation_identification hC hx hη hθ hφ hα hΦ
  obtain ⟨-, -, -, -, Ψ, -, hΨ, -⟩ :=
    hS.exact_fixed_E6_adjoint_intertwiner ρ hρ hroot Φ ψ hψ hx.1 (H.phi_base hΦ) hxT
  obtain ⟨y₀, hy₀⟩ := hS.nonempty_of_isSliceMaxClique hC
  obtain ⟨s, hs, -⟩ := H.existsUnique_fourGens hΦ
  obtain ⟨qC, hqC, hqCz⟩ := H.cliqueFixedVec_mem_rootVecSet hΦ hρ hroot hΨ
  obtain ⟨hpart, hsize, -, -, hcount, hQorb⟩ :=
    hS.complete_ambient_root_orbits_core hC hx hη hθ hφ hα hΦ hρ hroot hΨ
      (y₀ := ⟨y₀, hC.1.1 hy₀⟩) hy₀ hs hqC hqCz Q hHQ hQY ρQ hρQ
  set reps := orbitReps ρ Φ Ψ s qC ⟨y₀, hC.1.1 hy₀⟩ with hreps_def
  have hreps_mem : ∀ k : Fin 4, reps k ∈ rootVecSet := by
    intro k
    fin_cases k
    · exact psi_mem_rootVecSet hroot hΨ _
    · exact H.cliqueFixedVec_mem_rootVecSet hΦ hρ hroot hΨ
    · exact H.seedRootVec_mem hΦ hρ hroot hΨ s qC
    · exact H.cliqueFixedVec_add_mem_rootVecSet hΦ hρ hroot hΨ hy₀
  have hex : ∀ k : Fin 4, ∃ x : rootClass, rootVecOf (x : stdGroup) = reps k := fun k => by
    obtain ⟨x, hx, e⟩ := hreps_mem k
    exact ⟨⟨x, hx⟩, e⟩
  choose r hr using hex
  have hrv : Function.Injective fun x : rootClass => rootVecOf (x : stdGroup) :=
    fun a b e => Subtype.ext (bijOn_rootVecOf.injOn a.2 b.2 e)
  have hmem : ∀ (k : Fin 4) (x' : rootClass),
      x' ∈ qRootOrbit Q ρQ (r k) ↔ rootVecOf (x' : stdGroup) ∈ hOrbit ρ (reps k) := by
    intro k x'
    rw [qRootOrbit_eq, hr k, ← hQorb k]
    rfl
  have hlabels : ∀ x' : rootClass, (∃ y : Y, ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ = (x' : stdGroup)) ↔
      rootVecOf (x' : stdGroup) ∈ Set.range fun y : Y => Ψ (ncommVec lab Y y) := by
    intro x'
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      change Ψ (ncommVec lab Y y) = _
      rw [hΨ, ← hy]
      rfl
    · rintro ⟨y, hy⟩
      change Ψ (ncommVec lab Y y) = _ at hy
      rw [hΨ] at hy
      exact ⟨y, bijOn_rootVecOf.injOn (hroot y) x'.2 hy⟩
  refine ⟨r, fun x' => ?_, ?_, fun k => ?_, fun k x' hx' => ?_⟩
  · obtain ⟨k, hk, huniq⟩ := hpart _ ⟨x', x'.2, rfl⟩
    exact ⟨k, (hmem k x').2 hk, fun k' hk' => huniq k' ((hmem k' x').1 hk')⟩
  · ext x'
    rw [hmem, Set.mem_ofPred_eq, hlabels]
    change rootVecOf (x' : stdGroup) ∈ hOrbit ρ (Ψ (ncommVec lab Y ⟨y₀, hC.1.1 hy₀⟩)) ↔ _
    rw [H.hOrbit_psi hroot hΨ]
  · have e : qRootOrbit Q ρQ (r k) =
        (fun x : rootClass => rootVecOf (x : stdGroup)) ⁻¹' hOrbit ρ (reps k) :=
      Set.ext fun x' => hmem k x'
    rw [e, Set.ncard_preimage_of_injective_subset_range hrv, hsize k]
    intro u hu
    obtain ⟨x, hx, rfl⟩ := hOrbit_subset_rootVecSet (hreps_mem k) hu
    exact ⟨⟨x, hx⟩, rfl⟩
  · have hc := hcount k _ ((hmem k x').1 hx') x' x'.2 rfl
    rw [← hc]
    have e : {x'' : rootClass | x'' ∈ {x : rootClass |
          ∃ y : Y, ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ = (x : stdGroup)} ∧
          x'' ≠ x' ∧ Commute (x'' : stdGroup) x'} =
        (fun y : Y => (⟨ρ ⟨lab y, lab_mem_sliceGroup y.2⟩, hroot y⟩ : rootClass)) ''
          {y : Y | ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ ≠ x' ∧
            Commute (x' : stdGroup) (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩)} := by
      ext x''
      constructor
      · rintro ⟨⟨y, hy⟩, hne, hc⟩
        refine ⟨y, ⟨fun e => hne (Subtype.ext (hy.symm.trans e)), ?_⟩, Subtype.ext hy⟩
        rw [hy]
        exact hc.symm
      · rintro ⟨y, ⟨hne, hc⟩, rfl⟩
        exact ⟨⟨y, rfl⟩, fun e => hne (congrArg Subtype.val e), hc.symm⟩
    rw [e, Set.ncard_image_of_injective]
    intro a b e
    have e' := congrArg Subtype.val e
    exact Subtype.ext (hS.injOn a.2 b.2 (congrArg Subtype.val (hρ e')))

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
