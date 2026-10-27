module

public import CFSG.Monster.B.TwoA.Fischer.CliqueModuleIso
public import CFSG.Monster.B.TwoA.Fischer.CliqueModuleIrred

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Fischer CFSG.Monster.B.TwoA CFSG.Monster.B.Classical.Mog22
open scoped IsMulCommutative commutatorElement

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

@[expose] def labSubspace {C : Set V} [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]
    (N : Subgroup S) : Submodule (ZMod 2) (Additive (Subgroup.closure (lab '' C))) where
  carrier := {x | ((Additive.toMul x : Subgroup.closure (lab '' C)) : S) ∈ N}
  add_mem' {x y} hx hy := N.mul_mem hx hy
  zero_mem' := N.one_mem
  smul_mem' c x hx := by
    rcases zmod2_cases c with rfl | rfl
    · rw [zero_smul]
      exact N.one_mem
    · rw [one_smul]
      exact hx

theorem mem_labSubspace {C : Set V} [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]
    {N : Subgroup S} {x : Additive (Subgroup.closure (lab '' C))} :
    x ∈ labSubspace N ↔ ((Additive.toMul x : Subgroup.closure (lab '' C)) : S) ∈ N := Iff.rfl

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y)
include hS

theorem conj_mem_closure_of_mem {C : Set V} {f : S} (hf : f ∈ setStab act lab Y C) {r : S}
    (hr : r ∈ Subgroup.closure (lab '' C)) : f * r * f⁻¹ ∈ Subgroup.closure (lab '' C) :=
  conj_mem_closure hS.lab_act (fun x hx => (hf.2 x).2 hx) r hr

section Main

variable {C : Set V} (hC : IsSliceMaxClique lab Y C)
include hC

theorem exists_conj_ne : ∃ f ∈ setStab act lab Y C, ∃ r ∈ Subgroup.closure (lab '' C),
    f * r * f⁻¹ ≠ r := by
  by_contra h
  push Not at h
  have hbot : (setStabPerm act lab Y C).range = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨f, rfl⟩
    refine (Subgroup.mem_bot).2 (Equiv.ext fun z => Subtype.ext ?_)
    have hz := h f f.2 (lab z) (Subgroup.subset_closure ⟨z, z.2, rfl⟩)
    rw [← hS.lab_act] at hz
    exact hS.injOn (hS.mapsTo f f.2.1 z (hC.1.1 z.2)) (hC.1.1 z.2) hz
  have hcard := (hS.maximal_clique_stabilizer_kernel.2.2 C hC).2.1
  rw [hbot, Subgroup.card_bot] at hcard
  exact absurd hcard (by norm_num)

section Module

variable [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] [Finite C] {η : C ≃ X₀}
  {θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
    CFSG.Blueprint.NativeSporadic.M22}
  (hθ : ∀ (f : setStab act lab Y C) (z : C),
    (η (setStabPerm act lab Y C f z) : Fin 24) = psiHom (θ f) (η z))
  {φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀}
  (hφ : ∀ z : C, φ (Additive.ofMul (cliqueGen z)) = K₀.mkQ (e (η z)))
include hθ hφ

theorem rhoW_faithful
    (g : CFSG.Blueprint.NativeSporadic.M22) (hg : ∀ w : W₀, rhoW g w = w) :
    g = 1 := by
  obtain ⟨x, rfl⟩ := θ.surjective g
  obtain ⟨f, rfl⟩ := QuotientGroup.mk_surjective x
  have hfix : ∀ z ∈ C, act (f : S) z = z := fun z hz => by
    have h := hS.map_conj_eq_rhoW hθ hφ f (cliqueGen ⟨z, hz⟩)
      (hS.conj_mem_closure_of_mem f.2 (cliqueGen (lab := lab) ⟨z, hz⟩).2)
    rw [hg] at h
    have h' : (f : S) * lab z * (f : S)⁻¹ = lab z :=
      congrArg Subtype.val (Additive.ofMul.injective (φ.injective h))
    rw [← hS.lab_act] at h'
    exact hS.injOn (hS.mapsTo f f.2.1 z (hC.1.1 hz)) (hC.1.1 hz) h'
  have hf : (f : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C)) =
      1 := (QuotientGroup.eq_one_iff f).2 (Subgroup.mem_subgroupOf.2 ⟨f.2.1, hfix⟩)
  rw [hf, map_one]

omit hC in
theorem eq_bot_or_eq_closure
    (hirr : ∀ U : Submodule (ZMod 2) W₀, (∀ g, U ≤ U.comap (rhoW g)) → U = ⊥ ∨ U = ⊤)
    (N : Subgroup S) (hNR : N ≤ Subgroup.closure (lab '' C))
    (hN : ∀ f ∈ setStab act lab Y C, ∀ n ∈ N, f * n * f⁻¹ ∈ N) :
    N = ⊥ ∨ N = Subgroup.closure (lab '' C) := by
  let U : Submodule (ZMod 2) W₀ := (labSubspace N).map φ.toLinearMap
  have hinv : ∀ g, U ≤ U.comap (rhoW g) := by
    intro g
    obtain ⟨x, rfl⟩ := θ.surjective g
    obtain ⟨f, rfl⟩ := QuotientGroup.mk_surjective x
    rintro _ ⟨y, hy, rfl⟩
    have hy' := hS.conj_mem_closure_of_mem f.2 (Additive.toMul y).2
    have h := hS.map_conj_eq_rhoW hθ hφ f (Additive.toMul y) hy'
    rw [ofMul_toMul] at h
    rw [Submodule.mem_comap, LinearEquiv.coe_coe, ← h]
    exact ⟨Additive.ofMul ⟨_, hy'⟩, hN f f.2 _ hy, rfl⟩
  rcases hirr U hinv with h | h
  · refine Or.inl ((Subgroup.eq_bot_iff_forall N).2 fun n hn => ?_)
    have hmem : φ (Additive.ofMul ⟨n, hNR hn⟩) ∈ U := ⟨_, hn, rfl⟩
    rw [h, Submodule.mem_bot, LinearEquiv.map_eq_zero_iff] at hmem
    have h0 := congrArg (fun x : Additive (Subgroup.closure (lab '' C)) =>
      ((Additive.toMul x : Subgroup.closure (lab '' C)) : S)) hmem
    exact h0
  · refine Or.inr (le_antisymm hNR fun r hr => ?_)
    obtain ⟨y, hy, hyr⟩ : φ (Additive.ofMul ⟨r, hr⟩) ∈ U := by
      rw [h]
      exact Submodule.mem_top
    rw [LinearEquiv.coe_coe, φ.injective.eq_iff] at hyr
    rw [SetLike.mem_coe, mem_labSubspace, hyr] at hy
    exact hy

end Module

section Group

variable (hcl : ptStab act lab Y C = Subgroup.closure (lab '' C))
  (hirrR : ∀ N : Subgroup S, N ≤ Subgroup.closure (lab '' C) →
    (∀ f ∈ setStab act lab Y C, ∀ n ∈ N, f * n * f⁻¹ ∈ N) →
    N = ⊥ ∨ N = Subgroup.closure (lab '' C))
include hcl hirrR

theorem closure_le_commutator :
    Subgroup.closure (lab '' C) ≤ ⁅setStab act lab Y C, setStab act lab Y C⁆ := by
  have hFF : ∀ k ∈ setStab act lab Y C, ∀ n ∈ ⁅setStab act lab Y C, setStab act lab Y C⁆,
      k * n * k⁻¹ ∈ ⁅setStab act lab Y C, setStab act lab Y C⁆ := by
    intro k hk n hn
    rw [← Subgroup.map_subtype_commutator] at hn ⊢
    obtain ⟨n', hn', rfl⟩ := hn
    exact ⟨⟨k, hk⟩ * n' * ⟨k, hk⟩⁻¹, Subgroup.Normal.conj_mem inferInstance n' hn' ⟨k, hk⟩, rfl⟩
  rcases hirrR _ inf_le_left (fun k hk n hn => Subgroup.mem_inf.2
      ⟨hS.conj_mem_closure_of_mem hk (Subgroup.mem_inf.1 hn).1,
        hFF k hk n (Subgroup.mem_inf.1 hn).2⟩) with h | h
  · exfalso
    obtain ⟨f, hf, r, hr, hne⟩ := hS.exists_conj_ne hC
    have hmem : ⁅f, r⁆ ∈ Subgroup.closure (lab '' C) ⊓
        ⁅setStab act lab Y C, setStab act lab Y C⁆ :=
      Subgroup.mem_inf.2 ⟨mul_mem (hS.conj_mem_closure_of_mem hf hr) (inv_mem hr),
        Subgroup.commutator_mem_commutator hf (ptStab_le_setStab C (hcl ▸ hr))⟩
    rw [h, Subgroup.mem_bot, commutatorElement_def, mul_inv_eq_one] at hmem
    exact hne hmem
  · exact inf_eq_left.1 h

theorem commutator_setStab
    (θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
      CFSG.Blueprint.NativeSporadic.M22) :
    _root_.commutator (setStab act lab Y C) = ⊤ := by
  set Rq := (ptStab act lab Y C).subgroupOf (setStab act lab Y C)
  have hRq : Rq ≤ _root_.commutator (setStab act lab Y C) := fun x hx => by
    have hx' : (x : S) ∈ (_root_.commutator (setStab act lab Y C)).map
        (setStab act lab Y C).subtype := by
      rw [Subgroup.map_subtype_commutator]
      exact hS.closure_le_commutator hC hcl hirrR (hcl ▸ Subgroup.mem_subgroupOf.1 hx)
    obtain ⟨y, hy, hyx⟩ := hx'
    rwa [Subtype.ext hyx] at hy
  have hq : (_root_.commutator (setStab act lab Y C ⧸ Rq)) = ⊤ := by
    have h := Subgroup.map_commutator ⊤ ⊤ θ.symm.toMonoidHom
    rw [← commutator_def, commutator_M22,
      Subgroup.map_top_of_surjective _ θ.symm.surjective, ← commutator_def] at h
    exact h.symm
  have hmap : (_root_.commutator (setStab act lab Y C)).map (QuotientGroup.mk' Rq) = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Rq), ← commutator_def, hq]
  have h := Subgroup.comap_map_eq (QuotientGroup.mk' Rq) (_root_.commutator (setStab act lab Y C))
  rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk', sup_eq_left.2 hRq] at h
  exact h.symm

theorem center_setStab
    (θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
      CFSG.Blueprint.NativeSporadic.M22) :
    Subgroup.center (setStab act lab Y C) = ⊥ := by
  have hZ : ∀ z ∈ Subgroup.center (setStab act lab Y C),
      (z : S) ∈ Subgroup.closure (lab '' C) := by
    intro z hz
    have h1 : θ (z : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf
        (setStab act lab Y C)) ∈ Subgroup.center CFSG.Blueprint.NativeSporadic.M22 := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨x, rfl⟩ := θ.surjective g
      obtain ⟨f, rfl⟩ := QuotientGroup.mk_surjective x
      rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        Subgroup.mem_center_iff.1 hz f]
    rw [center_M22, Subgroup.mem_bot, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf, hcl] at h1
    exact h1
  rcases hirrR (Subgroup.closure (lab '' C) ⊓ Subgroup.centralizer (setStab act lab Y C))
      inf_le_left (fun k hk n hn => by
        rw [Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hn).2 k hk, mul_inv_cancel_right]
        exact hn) with h | h
  · refine eq_bot_iff.2 fun z hz => (Subgroup.mem_bot).2 (Subtype.ext ?_)
    have hmem : (z : S) ∈ Subgroup.closure (lab '' C) ⊓
        Subgroup.centralizer (setStab act lab Y C) :=
      Subgroup.mem_inf.2 ⟨hZ z hz, Subgroup.mem_centralizer_iff.2 fun f hf =>
        congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨f, hf⟩)⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact hmem
  · exfalso
    obtain ⟨f, hf, r, hr, hne⟩ := hS.exists_conj_ne hC
    have hr' : r ∈ Subgroup.centralizer (setStab act lab Y C) := inf_eq_left.1 h hr
    rw [Subgroup.mem_centralizer_iff.1 hr' f hf, mul_inv_cancel_right] at hne
    exact hne rfl

end Group

end Main

theorem clique_exact_binary_M22_module
    {C : Set V} (hC : IsSliceMaxClique lab Y C)
    [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] (η : C ≃ X₀)
    (θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
      CFSG.Blueprint.NativeSporadic.M22)
    (hη : ∀ T : Finset C, Subtype.val '' (T : Set C) ∈ cliqueBlocks lab C ↔
      T.image (fun z => (η z : Fin 24)) ∈ ℬ₀)
    (hθ : ∀ (f : setStab act lab Y C) (z : C),
      (η (setStabPerm act lab Y C f z) : Fin 24) = psiHom (θ f) (η z)) :
    ptStab act lab Y C = Subgroup.closure (lab '' C) ∧
    (∃! φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀,
      ∀ z : C, φ (Additive.ofMul (cliqueGen z)) = K₀.mkQ (e (η z))) ∧
    (∀ φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀,
      (∀ z : C, φ (Additive.ofMul (cliqueGen z)) = K₀.mkQ (e (η z))) →
      ∀ (f : setStab act lab Y C) (r : Subgroup.closure (lab '' C))
        (h : (f : S) * r * (f : S)⁻¹ ∈ Subgroup.closure (lab '' C)),
        φ (Additive.ofMul ⟨(f : S) * r * (f : S)⁻¹, h⟩) = rhoW (θ f) (φ (Additive.ofMul r))) ∧
    Module.finrank (ZMod 2) W₀ = 10 ∧
    (∀ g : CFSG.Blueprint.NativeSporadic.M22, (∀ w : W₀, rhoW g w = w) → g = 1) ∧
    (∀ U : Submodule (ZMod 2) W₀, (∀ g, U ≤ U.comap (rhoW g)) → U = ⊥ ∨ U = ⊤) ∧
    (∀ N : Subgroup S, N ≤ Subgroup.closure (lab '' C) →
      (∀ f ∈ setStab act lab Y C, ∀ n ∈ N, f * n * f⁻¹ ∈ N) →
      N = ⊥ ∨ N = Subgroup.closure (lab '' C)) ∧
    _root_.commutator (setStab act lab Y C) = ⊤ ∧ Subgroup.center (setStab act lab Y C) = ⊥ := by
  have : Finite C := (hS.finite.subset hC.1.1).to_subtype
  have hcl := (hS.maximal_clique_stabilizer_kernel.2.2 C hC).2.2.1
  have hK := hS.map_cliqueCode_eq_K₀ hC η θ hη hθ
  have hφ := cliqueModuleEquiv_gen hK
  have hfaith := hS.rhoW_faithful hC hθ hφ
  have hirr : ∀ U : Submodule (ZMod 2) W₀, (∀ g, U ≤ U.comap (rhoW g)) → U = ⊥ ∨ U = ⊤ :=
    eq_bot_or_eq_top_of_faithful rhoW finrank_W₀ fun g hg => hfaith g fun w => by rw [hg]; rfl
  have hirrR := hS.eq_bot_or_eq_closure hθ hφ hirr
  exact ⟨hcl, ⟨_, hφ, fun ψ hψ => LinearEquiv.toLinearMap_injective
      (eq_cliqueModuleEquiv hK (ψ := ψ.toLinearMap) hψ)⟩,
    fun ψ hψ f r h => hS.map_conj_eq_rhoW hθ hψ f r h, finrank_W₀, hfaith, hirr, hirrR,
    hS.commutator_setStab hC hcl hirrR θ, hS.center_setStab hC hcl hirrR θ⟩

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
