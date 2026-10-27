module

public import CFSG.Monster.B.TwoA.Fischer.CanonicalIdentT
public import CFSG.Monster.B.TwoA.Fischer.SliceSimple

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Fischer CFSG.Monster.B.TwoA CFSG.Monster.B.Classical.Mog22
open scoped IsMulCommutative

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

namespace FullIntertwinerHyp

variable {C : Set V} [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] {x : V}
  {η : C ≃ X₀}
  {θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
    CFSG.Blueprint.NativeSporadic.M22}
  {φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀} {α : setStab act lab Y C →* F₀}
  (H : FullIntertwinerHyp act lab Y C x η θ φ α)

@[expose] def conjHom (Φ : Y ≃ CFSG.Monster.B.Fischer.Y) :
    sliceGroup lab Y →* Equiv.Perm CFSG.Monster.B.Fischer.Y :=
  Φ.permCongrHom.toMonoidHom.comp (slicePerm act lab Y H.slice.mapsTo)

theorem conjHom_apply (Φ : Y ≃ CFSG.Monster.B.Fischer.Y) (h : sliceGroup lab Y) (v : Y) :
    H.conjHom Φ h (Φ v) = Φ (slicePerm act lab Y H.slice.mapsTo h v) := by
  simp only [conjHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Equiv.permCongrHom_coe,
    Equiv.permCongr_apply, Equiv.symm_apply_apply]

theorem conjHom_injective (Φ : Y ≃ CFSG.Monster.B.Fischer.Y) :
    Function.Injective (H.conjHom Φ) :=
  Φ.permCongrHom.injective.comp H.slice.slicePerm_injective

include H in
theorem alpha_surjective : Function.Surjective α := by
  rintro ⟨a, g⟩
  set r : Subgroup.closure (lab '' C) := Additive.toMul (φ.symm (Multiplicative.toAdd a)) with hr
  refine ⟨⟨r * H.fixLift g, (setStab act lab Y C).mul_mem (H.mem_setStab r) (H.fixLift g).2⟩, ?_⟩
  rw [H.alpha r _ (H.fixLift g) rfl (H.fixLift_fix g), H.theta_fixLift, wF_mul_kF, hr,
    ofMul_toMul, LinearEquiv.apply_symm_apply, ofAdd_toAdd]

variable {Φ : Y ≃ CFSG.Monster.B.Fischer.Y} (hΦ : IsCliqueIntertwiner act lab Y C x η φ α Φ)
include H hΦ

theorem conjHom_setStab (f : setStab act lab Y C) :
    H.conjHom Φ ⟨f, f.2.1⟩ = MulAction.toPerm (α f) := by
  refine Equiv.ext fun y => ?_
  obtain ⟨v, rfl⟩ := Φ.surjective y
  rw [H.conjHom_apply, MulAction.toPerm_apply]
  exact hΦ.equivariant f v _ rfl

theorem conjHom_lab :
    H.conjHom Φ ⟨lab x, lab_mem_sliceGroup H.mem.1⟩ = tPerm := by
  rw [← H.permCongr_labPerm hΦ]
  rfl

theorem sliceGroup_eq_closure :
    sliceGroup lab Y = Subgroup.closure ((setStab act lab Y C : Set S) ∪ {lab x}) := by
  classical
  set H' := Subgroup.closure ((setStab act lab Y C : Set S) ∪ {lab x}) with hH'
  have hF : ∀ f ∈ setStab act lab Y C, f ∈ H' := fun f hf =>
    Subgroup.subset_closure (Or.inl hf)
  have ht : lab x ∈ H' := Subgroup.subset_closure (Or.inr rfl)
  refine le_antisymm ?_ ((Subgroup.closure_le _).2 ?_)
  · obtain ⟨u, hu⟩ := H.slice.nonempty_of_isSliceMaxClique H.clique
    have hlu : lab u ∈ setStab act lab Y C :=
      ptStab_le_setStab C (H.slice.closure_le_ptStab H.clique.1.1 H.clique.1.2
        (Subgroup.subset_closure ⟨u, hu, rfl⟩))
    have hx' : act (lab u * lab x) u = x := by
      rw [map_mul, Equiv.Perm.mul_apply, H.slice.act_lab_eq_act_lab H.clique H.mem hu,
        ← Equiv.Perm.mul_apply, ← map_mul, H.slice.lab_mul_self (H.clique.1.1 hu), map_one,
        Equiv.Perm.one_apply]
    have hh₁ : lab u * lab x ∈ H' := H'.mul_mem (hF _ hlu) ht
    have htrans : ∀ y ∈ Y, ∃ h ∈ H', act h u = y := by
      intro y hy
      obtain ⟨T₀, hT₀⟩ := H.exists_T₀
      have hB := H.block_mem hT₀
      obtain ⟨y₀, hy₀⟩ : (hexadFiber lab Y C (Subtype.val '' (T₀ : Set C))).Nonempty :=
        Set.nonempty_of_ncard_ne_zero (by
          rw [(H.slice.hexadFiber_of_mem_cliqueBlocks H.clique hB).1]; norm_num)
      rcases H.regions hT₀ hy₀ hy with ⟨z, rfl⟩ | ⟨r, rfl⟩ | ⟨f, rfl⟩
      · obtain ⟨f, hf, hfz⟩ := H.slice.exists_setStab H.clique hu z.2
        exact ⟨f, hF f hf, hfz⟩
      · refine ⟨r * (lab u * lab x), H'.mul_mem (hF _ (H.mem_setStab r)) hh₁, ?_⟩
        rw [map_mul, Equiv.Perm.mul_apply, hx']
      ·
        obtain ⟨r₃, -, hr₃⟩ := H.exists_layer_three hΦ w7.2
        have hv₃ : act (r₃ : S) x ∈ Y := (H.act_mem_omega r₃).1
        have hΦv : Φ (H.labPerm ⟨act (r₃ : S) x, hv₃⟩) =
            Sum.inr (Sum.inr (sigmaEquiv w7 : Z)) := by
          rw [← H.permCongr_phi, show Φ ⟨act (r₃ : S) x, hv₃⟩ = _ from H.phi_omega hΦ r₃, hr₃]
          exact H.permCongr_L3 hΦ w7
        have hvC : (H.labPerm ⟨act (r₃ : S) x, hv₃⟩ : V) ∉ C := by
          have h1 := H.symm_inr_inr_not_mem_clique hΦ (sigmaEquiv w7 : Z)
          rwa [← hΦv, Equiv.symm_apply_apply] at h1
        have hvΩ : (H.labPerm ⟨act (r₃ : S) x, hv₃⟩ : V) ∉ hexadFiber lab Y C ∅ := by
          have h1 := H.symm_inr_inr_not_mem_omega hΦ (sigmaEquiv w7 : Z)
          rwa [← hΦv, Equiv.symm_apply_apply] at h1
        rcases H.slice.inter_neighborSet_eq_empty_or_mem H.clique hvC with h0 | hB'
        · exact absurd ⟨(H.labPerm ⟨act (r₃ : S) x, hv₃⟩).2, hvC, h0⟩ hvΩ
        have hfy := H.act_mem_image_fiber hy₀ f
        have hB'' : act (f : S) '' (Subtype.val '' (T₀ : Set C)) ∈ cliqueBlocks lab C :=
          image_mem_cliqueBlocks H.slice.lab_act (fun z hz => (f.2.2 z).2 hz)
            (setStabPerm act lab Y C f) (fun _ => rfl) hB
        obtain ⟨g, hg, hgv⟩ := H.exists_act_eq_of_mem_hexadFiber hB' hB''
          ⟨(H.labPerm ⟨act (r₃ : S) x, hv₃⟩).2, hvC, rfl⟩ hfy
        refine ⟨g * (lab x * (r₃ * (lab u * lab x))),
          H'.mul_mem (hF g hg) (H'.mul_mem ht (H'.mul_mem (hF _ (H.mem_setStab r₃)) hh₁)), ?_⟩
        have hx'' : act (lab u) (act (lab x) u) = x := by
          rw [← Equiv.Perm.mul_apply, ← map_mul]
          exact hx'
        have e : act (g * (lab x * ((r₃ : S) * (lab u * lab x)))) u =
            act g (act (lab x) (act (r₃ : S) x)) := by
          simp only [map_mul, Equiv.Perm.mul_apply, hx'']
        rw [e]
        exact hgv
    refine (Subgroup.closure_le H').2 ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨h, hh, rfl⟩ := htrans y hy
    rw [H.slice.lab_act]
    exact H'.mul_mem (H'.mul_mem hh (hF _ hlu)) (H'.inv_mem hh)
  · rintro s (hs | rfl)
    · exact hs.1
    · exact lab_mem_sliceGroup H.mem.1

theorem range_conjHom :
    (H.conjHom Φ).range = CFSG.Monster.B.Fischer.J := by
  apply le_antisymm
  · rintro _ ⟨h, rfl⟩
    have hh : (h : S) ∈ Subgroup.closure ((setStab act lab Y C : Set S) ∪ {lab x}) :=
      H.sliceGroup_eq_closure hΦ ▸ h.2
    suffices key : ∀ (s : S) (hs : s ∈ Subgroup.closure ((setStab act lab Y C : Set S) ∪ {lab x})),
        ∀ hs' : s ∈ sliceGroup lab Y, H.conjHom Φ ⟨s, hs'⟩ ∈ CFSG.Monster.B.Fischer.J from
      key h hh h.2
    intro s hs
    induction hs using Subgroup.closure_induction with
    | mem s hs =>
      intro hs'
      rcases hs with hs | rfl
      · rw [show (⟨s, hs'⟩ : sliceGroup lab Y) = ⟨(⟨s, hs⟩ : setStab act lab Y C), hs.1⟩ from rfl,
          H.conjHom_setStab hΦ]
        exact Subgroup.subset_closure (Or.inl ⟨α ⟨s, hs⟩, rfl⟩)
      · rw [H.conjHom_lab hΦ]
        exact Subgroup.subset_closure (Or.inr rfl)
    | one =>
      intro hs'
      rw [show (⟨1, hs'⟩ : sliceGroup lab Y) = 1 from rfl, map_one]
      exact Subgroup.one_mem _
    | mul s s' hs hs₂ ihs ihs' =>
      intro hss'
      have h1 : s ∈ sliceGroup lab Y := H.sliceGroup_eq_closure hΦ ▸ hs
      have h2 : s' ∈ sliceGroup lab Y := H.sliceGroup_eq_closure hΦ ▸ hs₂
      rw [show (⟨s * s', hss'⟩ : sliceGroup lab Y) = ⟨s, h1⟩ * ⟨s', h2⟩ from rfl, map_mul]
      exact Subgroup.mul_mem _ (ihs h1) (ihs' h2)
    | inv s hs ihs =>
      intro hs'
      have h1 : s ∈ sliceGroup lab Y := H.sliceGroup_eq_closure hΦ ▸ hs
      rw [show (⟨s⁻¹, hs'⟩ : sliceGroup lab Y) = (⟨s, h1⟩)⁻¹ from rfl, map_inv]
      exact Subgroup.inv_mem _ (ihs h1)
  · rw [CFSG.Monster.B.Fischer.J, Subgroup.closure_le]
    rintro _ (⟨g, rfl⟩ | rfl)
    · obtain ⟨f, rfl⟩ := H.alpha_surjective g
      exact ⟨⟨f, f.2.1⟩, H.conjHom_setStab hΦ f⟩
    · exact ⟨_, H.conjHom_lab hΦ⟩

theorem canonical_identification :
    ∃ ψ : sliceGroup lab Y ≃* CFSG.Monster.B.Fischer.J,
      (∀ (h : sliceGroup lab Y) (v w : Y), (w : V) = act (h : S) v →
        (ψ h : Equiv.Perm CFSG.Monster.B.Fischer.Y) (Φ v) = Φ w) ∧
      (∀ f : setStab act lab Y C,
        (ψ ⟨f, f.2.1⟩ : Equiv.Perm CFSG.Monster.B.Fischer.Y) = MulAction.toPerm (α f)) ∧
      (ψ ⟨lab x, lab_mem_sliceGroup H.mem.1⟩ : Equiv.Perm CFSG.Monster.B.Fischer.Y) = tPerm ∧
      sliceGroup lab Y = Subgroup.closure ((setStab act lab Y C : Set S) ∪ {lab x}) ∧
      Nat.card CFSG.Monster.B.Fischer.J = 64561751654400 ∧
      IsSimpleGroup CFSG.Monster.B.Fischer.J ∧ ¬IsMulCommutative CFSG.Monster.B.Fischer.J := by
  set ψ : sliceGroup lab Y ≃* CFSG.Monster.B.Fischer.J :=
    (MonoidHom.ofInjective (H.conjHom_injective Φ)).trans
      (MulEquiv.subgroupCongr (H.range_conjHom hΦ)) with hψ
  have hψh : ∀ h, (ψ h : Equiv.Perm CFSG.Monster.B.Fischer.Y) = H.conjHom Φ h := fun h => rfl
  obtain ⟨hsimple, hnc, hcard, -⟩ := H.slice.simple
  refine ⟨ψ, fun h v w hw => ?_, fun f => ?_, ?_, H.sliceGroup_eq_closure hΦ, ?_, ?_, ?_⟩
  · rw [hψh, H.conjHom_apply]
    congr 1
    exact Subtype.ext hw.symm
  · rw [hψh, H.conjHom_setStab hΦ]
  · rw [hψh, H.conjHom_lab hΦ]
  · rw [← Nat.card_congr ψ.toEquiv, hcard]
  · exact (MulEquiv.isSimpleGroup_congr ψ).1 hsimple
  · intro hJ
    apply hnc
    refine ⟨⟨fun a b => ψ.injective ?_⟩⟩
    rw [map_mul, map_mul]
    exact hJ.is_comm.comm _ _

end FullIntertwinerHyp

namespace IsFischerSlice

theorem canonical_permutation_identification
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
    {Φ : Y ≃ CFSG.Monster.B.Fischer.Y} (hΦ : IsCliqueIntertwiner act lab Y C x η φ α Φ) :
    ∃ ψ : sliceGroup lab Y ≃* CFSG.Monster.B.Fischer.J,
      (∀ (h : sliceGroup lab Y) (v w : Y), (w : V) = act (h : S) v →
        (ψ h : Equiv.Perm CFSG.Monster.B.Fischer.Y) (Φ v) = Φ w) ∧
      (∀ f : setStab act lab Y C,
        (ψ ⟨f, f.2.1⟩ : Equiv.Perm CFSG.Monster.B.Fischer.Y) = MulAction.toPerm (α f)) ∧
      (ψ ⟨lab x, lab_mem_sliceGroup hx.1⟩ : Equiv.Perm CFSG.Monster.B.Fischer.Y) = tPerm ∧
      sliceGroup lab Y = Subgroup.closure ((setStab act lab Y C : Set S) ∪ {lab x}) ∧
      Nat.card CFSG.Monster.B.Fischer.J = 64561751654400 ∧
      IsSimpleGroup CFSG.Monster.B.Fischer.J ∧ ¬IsMulCommutative CFSG.Monster.B.Fischer.J :=
  (FullIntertwinerHyp.mk hS hC hx hη hθ hφ hα).canonical_identification hΦ

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
