module

public import CFSG.Monster.B.TwoA.Base.Flags

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open Module

open scoped IsMulCommutative

section Conj

variable {G : Type*} [Group G]

@[expose] def conjSub (g : G) (H : Subgroup G) : Subgroup G := H.map (MulAut.conj g).toMonoidHom

theorem mem_conjSub {g x : G} {H : Subgroup G} : x ∈ conjSub g H ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    change g⁻¹ * (g * h * g⁻¹) * g ∈ H
    rw [show g⁻¹ * (g * h * g⁻¹) * g = h by group]
    exact hh
  · intro hx
    refine ⟨g⁻¹ * x * g, hx, ?_⟩
    change g * (g⁻¹ * x * g) * g⁻¹ = x
    group

theorem conj_mem_conjSub {g h : G} {H : Subgroup G} (hh : h ∈ H) : g * h * g⁻¹ ∈ conjSub g H :=
  ⟨h, hh, rfl⟩

theorem conjSub_one (H : Subgroup G) : conjSub 1 H = H := by
  ext x
  rw [mem_conjSub, inv_one, one_mul, mul_one]

theorem conjSub_mul (g h : G) (H : Subgroup G) :
    conjSub (g * h) H = conjSub g (conjSub h H) := by
  ext x
  rw [mem_conjSub, mem_conjSub, mem_conjSub,
    show (g * h)⁻¹ * x * (g * h) = h⁻¹ * (g⁻¹ * x * g) * h by group]

theorem conjSub_mono {g : G} {H H' : Subgroup G} (h : H ≤ H') : conjSub g H ≤ conjSub g H' :=
  Subgroup.map_mono h

theorem conjSub_inv_conjSub (g : G) (H : Subgroup G) : conjSub g⁻¹ (conjSub g H) = H := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

theorem conjSub_conjSub_inv (g : G) (H : Subgroup G) : conjSub g (conjSub g⁻¹ H) = H := by
  rw [← conjSub_mul, mul_inv_cancel, conjSub_one]

theorem conjSub_le_conjSub_iff {g : G} {H H' : Subgroup G} :
    conjSub g H ≤ conjSub g H' ↔ H ≤ H' := by
  refine ⟨fun h => ?_, conjSub_mono⟩
  have h1 := conjSub_mono (g := g⁻¹) h
  rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at h1

theorem natCard_conjSub (g : G) (H : Subgroup G) : Nat.card (conjSub g H) = Nat.card H :=
  (Nat.card_congr (H.equivMapOfInjective _ (MulAut.conj g).injective).toEquiv).symm

theorem conjSub_eq_self_iff {g : G} {H : Subgroup G} :
    conjSub g H = H ↔ g ∈ Subgroup.normalizer (H : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← h]
      exact conj_mem_conjSub hx
    · intro hx
      rw [← h, mem_conjSub, show g⁻¹ * (g * x * g⁻¹) * g = x by group] at hx
      exact hx
  · intro hg
    ext x
    rw [mem_conjSub]
    have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg)) x
    rw [inv_inv] at h1
    exact h1.symm

@[expose, instance_reducible] def conjSubAction : MulAction G (Subgroup G) where
  smul := conjSub
  one_smul := conjSub_one
  mul_smul := conjSub_mul

theorem ncard_conjSub_orbit (K H : Subgroup G) :
    {F : Subgroup G | ∃ k ∈ K, F = conjSub k H}.ncard =
      ((Subgroup.normalizer (H : Set G)).subgroupOf K).index := by
  let _ : MulAction G (Subgroup G) := conjSubAction
  let _ : MulAction K (Subgroup G) := MulAction.compHom _ K.subtype
  have hstab : MulAction.stabilizer K H = (Subgroup.normalizer (H : Set G)).subgroupOf K := by
    ext k
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    exact conjSub_eq_self_iff
  have horb : MulAction.orbit K H = {F : Subgroup G | ∃ k ∈ K, F = conjSub k H} := by
    ext F
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  rw [← hstab, MulAction.index_stabilizer, horb]

end Conj

theorem exists_conj_of_natCard_eq {G : Type*} [Group G] [Finite G] {E F F' : Subgroup G}
    [CFSG.IsElementaryAbelian 2 E] (hsurj : Function.Surjective (conjE E)) (hF : F ≤ E)
    (hF' : F' ≤ E) (hc : Nat.card F = Nat.card F') :
    ∃ k ∈ Subgroup.normalizer (E : Set G), ∀ f ∈ F, k * f * k⁻¹ ∈ F' := by
  have hr : finrank (ZMod 2) (subOf E F) = finrank (ZMod 2) (subOf E F') := by
    have h1 := FiniteField.pow_finrank_eq_natCard 2 (subOf E F)
    have h2 := FiniteField.pow_finrank_eq_natCard 2 (subOf E F')
    rw [natCard_subOf E hF] at h1
    rw [natCard_subOf E hF', ← hc, ← h1] at h2
    exact (Nat.pow_right_injective le_rfl h2).symm
  obtain ⟨e, he⟩ := exists_linearEquiv_map_eq hr
  obtain ⟨k, hk⟩ := linConj_surjective E hsurj e
  refine ⟨k, k.2, fun f hf => ?_⟩
  have h1 : (linConj E k : Additive E →ₗ[ZMod 2] Additive E) (Additive.ofMul ⟨f, hF hf⟩) ∈
      subOf E F' := by
    rw [← he, hk]
    exact ⟨_, hf, rfl⟩
  exact h1

theorem exists_normalizer_conjSub_eq {G : Type*} [Group G] [Finite G] {E F : Subgroup G}
    [CFSG.IsElementaryAbelian 2 E] (hsurj : Function.Surjective (conjE E)) (hFE : F ≤ E) {g : G}
    (hF : F ≤ conjSub g E) :
    ∃ h ∈ Subgroup.normalizer (F : Set G), conjSub g E = conjSub h E := by
  have hF0 : conjSub g⁻¹ F ≤ E := by
    have h1 := conjSub_mono (g := g⁻¹) hF
    rwa [conjSub_inv_conjSub] at h1
  obtain ⟨k, hk, hkF⟩ := exists_conj_of_natCard_eq hsurj hF0 hFE (natCard_conjSub _ _)
  refine ⟨g * k⁻¹, ?_, ?_⟩
  · rw [← Subgroup.inv_mem_iff]
    refine Subgroup.mem_normalizer_fintype fun f hf => ?_
    have h1 : g⁻¹ * f * g ∈ conjSub g⁻¹ F := by
      rw [mem_conjSub, inv_inv, show g * (g⁻¹ * f * g) * g⁻¹ = f by group]
      exact hf
    rw [show (g * k⁻¹)⁻¹ * f * (g * k⁻¹)⁻¹⁻¹ = k * (g⁻¹ * f * g) * k⁻¹ by group]
    exact hkF _ h1
  · rw [conjSub_mul, conjSub_eq_self_iff.2 (Subgroup.inv_mem _ hk)]

section Parabolic

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_linearEquiv_fix_map_eq {W T T' : Submodule K V} (hT : W ≤ T) (hT' : W ≤ T')
    (h : finrank K T = finrank K T') :
    ∃ e : V ≃ₗ[K] V, W.map (e : V →ₗ[K] V) = W ∧ T.map (e : V →ₗ[K] V) = T' := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
  have hsup : ∀ {S : Submodule K V}, W ≤ S → W ⊔ C ⊓ S = S := fun hS => by
    rw [← sup_inf_assoc_of_le C hS, hC.sup_eq_top, top_inf_eq]
  have hdim : ∀ {S : Submodule K V}, W ≤ S → finrank K ↥(C ⊓ S) + finrank K W = finrank K S := by
    intro S hS
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq W (C ⊓ S)
    have h2 : W ⊓ (C ⊓ S) = ⊥ := eq_bot_iff.2 fun x hx =>
      hC.disjoint.le_bot ⟨hx.1, hx.2.1⟩
    rw [hsup hS, h2, finrank_bot] at h1
    omega
  let S₁ : Submodule K C := (C ⊓ T).comap C.subtype
  let S₂ : Submodule K C := (C ⊓ T').comap C.subtype
  have hS : finrank K S₁ = finrank K S₂ := by
    rw [(Submodule.comapSubtypeEquivOfLe (inf_le_left : C ⊓ T ≤ C)).finrank_eq,
      (Submodule.comapSubtypeEquivOfLe (inf_le_left : C ⊓ T' ≤ C)).finrank_eq]
    have h1 := hdim hT
    have h2 := hdim hT'
    omega
  obtain ⟨f, hf⟩ := exists_linearEquiv_map_eq hS
  let e : V ≃ₗ[K] V := (Submodule.prodEquivOfIsCompl W C hC).symm.trans
    (((LinearEquiv.refl K W).prodCongr f).trans (Submodule.prodEquivOfIsCompl W C hC))
  have heW : ∀ x : W, e x = x := by
    intro x
    change Submodule.prodEquivOfIsCompl W C hC
      (((LinearEquiv.refl K W).prodCongr f) ((Submodule.prodEquivOfIsCompl W C hC).symm x)) = _
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left, LinearEquiv.prodCongr_apply,
      Submodule.coe_prodEquivOfIsCompl', map_zero, Submodule.coe_zero, add_zero]
    rfl
  have heC : ∀ x : C, e x = f x := by
    intro x
    change Submodule.prodEquivOfIsCompl W C hC
      (((LinearEquiv.refl K W).prodCongr f) ((Submodule.prodEquivOfIsCompl W C hC).symm x)) = _
    rw [Submodule.prodEquivOfIsCompl_symm_apply_right, LinearEquiv.prodCongr_apply,
      Submodule.coe_prodEquivOfIsCompl', map_zero, Submodule.coe_zero, zero_add]
  have hW : W.map (e : V →ₗ[K] V) = W := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change e (⟨x, hx⟩ : W) ∈ W
      rw [heW]
      exact hx
    · intro x hx
      exact ⟨x, hx, heW ⟨x, hx⟩⟩
  have hCT : (C ⊓ T).map (e : V →ₗ[K] V) = C ⊓ T' := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have h1 : f ⟨x, hx.1⟩ ∈ S₂ := by
        rw [← hf]
        exact ⟨⟨x, hx.1⟩, hx, rfl⟩
      change e (⟨x, hx.1⟩ : C) ∈ C ⊓ T'
      rw [heC]
      exact h1
    · intro y hy
      have h1 : (⟨y, hy.1⟩ : C) ∈ S₁.map (f : C →ₗ[K] C) := by
        rw [hf]
        exact hy
      obtain ⟨s, hs, hsy⟩ := h1
      refine ⟨s, hs, ?_⟩
      change e s = y
      rw [heC]
      exact congrArg Subtype.val hsy
  refine ⟨e, hW, ?_⟩
  rw [← hsup hT, Submodule.map_sup, hW, hCT, hsup hT']

end Parabolic

end CFSG.Monster.B.TwoA
