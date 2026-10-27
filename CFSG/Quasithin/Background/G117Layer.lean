module

public import CFSG.Quasithin.Background.G118Hyp

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace G11

namespace G117

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem exists_mul_ne_of_isQuasisimple {X : Type*} [Group X] (h : CFSG.Open.IsQuasisimple X) :
    ∃ a b : X, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  obtain ⟨a, b, hab⟩ := h.2.exists_pair_ne
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [QuotientGroup.eq, Subgroup.mem_center_iff]
  intro g
  exact hcomm g (a⁻¹ * b)

theorem isComponentOf_subgroupOf_map_conj {Γ L : Subgroup (GLV V)} (hL : IsComponentOf L Γ)
    {γ : GLV V} (hγ : γ ∈ Γ) :
    IsComponentOf ((L.map (MulAut.conj γ).toMonoidHom).subgroupOf Γ) ⊤ :=
  (isComponentOf_iff_subgroupOf.1 (isComponentOf_map_conj hL hγ)).2

variable [Finite V]

theorem layer_map_eq_normalClosure {Γ L : Subgroup (GLV V)} (hL : IsComponentOf L Γ)
    (hab : ∀ a ∈ Γ, (∀ h ∈ normalClosure Γ L, a * h = h * a) → ∀ b ∈ Γ,
      (∀ h ∈ normalClosure Γ L, b * h = h * b) → a * b = b * a) :
    (genFittingLayer ↥Γ).map Γ.subtype = normalClosure Γ L := by
  have hLΓ : L ≤ Γ := hL.1
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, genFittingLayer]
    refine sSup_le fun K hK => ?_
    by_cases hconj : ∃ γ ∈ Γ, K = (L.map (MulAut.conj γ).toMonoidHom).subgroupOf Γ
    · obtain ⟨γ, hγ, rfl⟩ := hconj
      intro x hx
      exact map_conj_le_normalClosure hγ hx
    · exfalso
      push Not at hconj
      have hK' : CFSG.GorensteinWalter.IsComponentOf K ⊤ :=
        (CFSG.Adapters.isComponentOf_top_iff K).1 hK
      have hKcent : ∀ x ∈ K, ∀ h ∈ normalClosure Γ L,
          (x : GLV V) * h = h * (x : GLV V) := by
        intro x hx
        have hle : normalClosure Γ L ≤ Subgroup.centralizer ({(x : GLV V)} : Set (GLV V)) := by
          rw [normalClosure, Subgroup.closure_le]
          rintro _ ⟨γ, hγ, l, hl, rfl⟩ z hz
          rw [Set.mem_singleton_iff] at hz
          rw [hz]
          have hA : CFSG.GorensteinWalter.IsComponentOf
              ((L.map (MulAut.conj γ).toMonoidHom).subgroupOf Γ) ⊤ :=
            (CFSG.Adapters.isComponentOf_top_iff _).1 (isComponentOf_subgroupOf_map_conj hL hγ)
          have hcomm := CFSG.GorensteinWalter.component_commute_of_ne hK' hA (hconj γ hγ)
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
          have hmem : (⟨γ * l * γ⁻¹, Γ.mul_mem (Γ.mul_mem hγ (hLΓ hl)) (Γ.inv_mem hγ)⟩ : ↥Γ) ∈
              (L.map (MulAut.conj γ).toMonoidHom).subgroupOf Γ :=
            mem_map_conj_of_mem hl
          have := Subgroup.mem_centralizer_iff.1 (hcomm hx) _ hmem
          exact (congrArg Subtype.val this).symm
        intro h hh
        exact Subgroup.mem_centralizer_iff.1 (hle hh) (x : GLV V) rfl
      obtain ⟨a, b, hne⟩ := exists_mul_ne_of_isQuasisimple hK.2.2
      apply hne
      apply Subtype.ext
      apply Subtype.ext
      exact hab a.1 a.1.2 (hKcent a a.2) b.1 b.1.2 (hKcent b b.2)
  · rw [normalClosure, Subgroup.closure_le]
    rintro _ ⟨γ, hγ, l, hl, rfl⟩
    have hcomp := isComponentOf_subgroupOf_map_conj hL hγ
    have hle : (L.map (MulAut.conj γ).toMonoidHom).subgroupOf Γ ≤ genFittingLayer ↥Γ :=
      le_sSup hcomp
    have hmem : (⟨γ * l * γ⁻¹, Γ.mul_mem (Γ.mul_mem hγ (hLΓ hl)) (Γ.inv_mem hγ)⟩ : ↥Γ) ∈
        (L.map (MulAut.conj γ).toMonoidHom).subgroupOf Γ :=
      mem_map_conj_of_mem hl
    exact ⟨_, hle hmem, rfl⟩

theorem fstar_map_eq_normalClosure {Γ L : Subgroup (GLV V)} (hL : IsComponentOf L Γ)
    (hC : ∀ c ∈ Γ, (∀ h ∈ normalClosure Γ L, c * h = h * c) → c = 1) :
    (genFittingFStar ↥Γ).map Γ.subtype = normalClosure Γ L := by
  have hlayer := layer_map_eq_normalClosure hL (fun a ha hac b _ _ => by
    rw [hC a ha hac]
    simp)
  have hE : genFittingLayer ↥Γ = CFSG.GorensteinWalter.componentLayerOf (⊤ : Subgroup ↥Γ) :=
    (CFSG.Adapters.componentLayerOf_top_eq_componentClassification _).symm
  have hFS : genFittingFStar ↥Γ =
      CFSG.fittingSubgroupOf (⊤ : Subgroup ↥Γ) ⊔ genFittingLayer ↥Γ := by
    rw [CFSG.Adapters.genFittingFStar_eq, hE]
    rfl
  rw [hFS, Subgroup.map_sup, hlayer]
  refine sup_eq_right.2 ?_
  rintro _ ⟨f, hf, rfl⟩
  have hFE := CFSG.GorensteinWalter.layer_centralizes_fitting (⊤ : Subgroup ↥Γ)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hFE
  have h1 : (f : GLV V) = 1 := by
    refine hC f f.2 fun h hh => ?_
    rw [← hlayer] at hh
    obtain ⟨e, he, rfl⟩ := hh
    rw [← hE] at hFE
    have := Subgroup.mem_centralizer_iff.1 (hFE he) f hf
    exact congrArg Subtype.val this
  show (f : GLV V) ∈ normalClosure Γ L
  rw [h1]
  exact Subgroup.one_mem _

@[expose] noncomputable def fstarEquiv {Γ L : Subgroup (GLV V)}
    (hF : (genFittingFStar ↥Γ).map Γ.subtype = normalClosure Γ L) :
    ↥(genFittingFStar ↥Γ) ≃* ↥(normalClosure Γ L) :=
  (Subgroup.equivMapOfInjective _ Γ.subtype Γ.subtype_injective).trans
    (MulEquiv.subgroupCongr hF)

end G117

end G11

end CFSG.Quasithin
