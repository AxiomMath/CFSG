module

public import CFSG.Open.Defs
import CFSG.Quasithin.Background.F918V5GComp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup

private theorem s16k_exists_mulEquiv_sup_prod {X : Type*} [Group X] {V₁ V₂ : Subgroup X}
    (hs : IsSimpleGroup V₁) (hp : ⁅V₁, V₁⁆ = V₁) (hcomm : ⁅V₁, V₂⁆ = ⊥) :
    Nonempty (↥(V₁ ⊔ V₂) ≃* V₁ × V₂) := by
  have hc : ∀ a ∈ V₁, ∀ b ∈ V₂, Commute a b := fun a ha b hb => by
    have := Subgroup.commutator_mem_commutator ha hb
    rw [hcomm, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  have hbot : V₁ ⊓ V₂ = ⊥ := by
    have hN : ((V₁ ⊓ V₂).subgroupOf V₁).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hn2 : (n : X) ∈ V₂ := (Subgroup.mem_subgroupOf.mp hn).2
      have hcg : Commute (g : X) n := (hc g g.2 n hn2).symm.symm
      rw [Subgroup.mem_subgroupOf]
      have : (g : X) * n * (g : X)⁻¹ = n := by
        rw [hcg.eq, mul_assoc, mul_inv_cancel, mul_one]
      change (g : X) * (n : X) * (g : X)⁻¹ ∈ V₁ ⊓ V₂
      rw [this]
      exact Subgroup.mem_subgroupOf.mp hn
    rcases hs.eq_bot_or_eq_top_of_normal ((V₁ ⊓ V₂).subgroupOf V₁) with h | h
    · rw [eq_bot_iff]
      intro x hx
      have hx1 : x ∈ V₁ := hx.1
      have : (⟨x, hx1⟩ : V₁) ∈ (V₁ ⊓ V₂).subgroupOf V₁ := hx
      rw [h, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val this
    · exfalso
      have hle : V₁ ≤ V₂ := fun x hx => by
        have : (⟨x, hx⟩ : V₁) ∈ (V₁ ⊓ V₂).subgroupOf V₁ := by rw [h]; trivial
        exact (Subgroup.mem_subgroupOf.mp this).2
      have h1 : ⁅V₁, V₁⁆ ≤ ⊥ := hcomm ▸ Subgroup.commutator_mono le_rfl hle
      rw [hp] at h1
      obtain ⟨a, b, hab⟩ := hs.exists_pair_ne
      have ha : (a : X) = 1 := Subgroup.mem_bot.mp (h1 a.2)
      have hb : (b : X) = 1 := Subgroup.mem_bot.mp (h1 b.2)
      exact hab (Subtype.ext (ha.trans hb.symm))
  let θ : V₁ × V₂ →* X := V₁.subtype.noncommCoprod V₂.subtype fun a b => hc a a.2 b b.2
  have hθ : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    have h1 : (a : X) * b = 1 := hab
    have hb : (b : X) = (a : X)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    have hmem : (a : X) ∈ V₁ ⊓ V₂ := ⟨a.2, by
      have : (a : X)⁻¹ ∈ V₂ := hb ▸ b.2
      simpa using V₂.inv_mem this⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have ha1 : a = 1 := Subtype.ext hmem
    have hb1 : b = 1 := Subtype.ext (by rw [hb, hmem, inv_one]; rfl)
    rw [ha1, hb1]
    rfl
  have hrange : θ.range = V₁ ⊔ V₂ := by
    have := MonoidHom.noncommCoprod_range V₁.subtype V₂.subtype fun a b => hc a a.2 b b.2
    rwa [Subgroup.range_subtype, Subgroup.range_subtype] at this
  exact ⟨((MonoidHom.ofInjective hθ).trans (MulEquiv.subgroupCongr hrange)).symm⟩

theorem s16k_components_conj {A : Type} [Group A] [Finite A] {M K : Subgroup A} {g : A}
    (hK : IsComponentOf K M) (hg : g ∈ M)
    (hne : K ≠ K.map (MulAut.conj g).toMonoidHom) (hs : IsSimpleGroup ↥K) :
    IsComponentOf (K.map (MulAut.conj g).toMonoidHom) M ∧
      (∀ x ∈ K, ∀ y ∈ K.map (MulAut.conj g).toMonoidHom, x * y = y * x) ∧
      Nonempty (↥(K ⊔ K.map (MulAut.conj g).toMonoidHom) ≃*
        ↥K × ↥(K.map (MulAut.conj g).toMonoidHom)) := by
  have hK' : IsComponentOf (K.map (MulAut.conj g).toMonoidHom) M :=
    CFSG.Quasithin.F918V5G.isComponentOf_map_conj hK hg
  have hcomm : ∀ x ∈ K, ∀ y ∈ K.map (MulAut.conj g).toMonoidHom, x * y = y * x :=
    (CFSG.Quasithin.F918V5G.isComponentOf_eq_or_commute hK hK').resolve_left hne
  have hp : ⁅K, K⁆ = K :=
    Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hK.2.2.1)
  have hcomm0 : ⁅K, K.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcomm x hx y hy).symm
  exact ⟨hK', hcomm, s16k_exists_mulEquiv_sup_prod hs hp hcomm0⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
