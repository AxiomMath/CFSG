module

public import CFSG.Quasithin.Background.G10Comp
public import CFSG.Adapters.GeneralizedFitting

public section

namespace CFSG.Quasithin

namespace G11

theorem genFittingFStar_eq_sup_of_components {G : Type} [Group G] [Finite G] {A B : Subgroup G}
    (hA : CFSG.Open.IsComponentOf A ⊤) (hB : CFSG.Open.IsComponentOf B ⊤)
    (hC : ∀ g : G, (∀ a ∈ A, g * a = a * g) → (∀ b ∈ B, g * b = b * g) → g = 1) :
    CFSG.Open.genFittingFStar G = A ⊔ B := by
  have hA' : CFSG.GorensteinWalter.IsComponentOf A ⊤ :=
    (CFSG.Adapters.isComponentOf_top_iff A).1 hA
  have hB' : CFSG.GorensteinWalter.IsComponentOf B ⊤ :=
    (CFSG.Adapters.isComponentOf_top_iff B).1 hB
  rw [CFSG.Adapters.genFittingFStar_eq G]
  unfold CFSG.GorensteinWalter.generalizedFittingSubgroupOf
  have hAE : A ≤ CFSG.GorensteinWalter.componentLayerOf (⊤ : Subgroup G) := le_sSup hA'
  have hBE : B ≤ CFSG.GorensteinWalter.componentLayerOf (⊤ : Subgroup G) := le_sSup hB'
  apply le_antisymm
  · refine sup_le ?_ ?_
    · have hFE := CFSG.GorensteinWalter.layer_centralizes_fitting (⊤ : Subgroup G)
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hFE
      intro f hf
      have hf1 : f = 1 := hC f
        (fun a ha => (Subgroup.mem_centralizer_iff.1 (hFE (hAE ha)) f hf))
        (fun b hb => (Subgroup.mem_centralizer_iff.1 (hFE (hBE hb)) f hf))
      rw [hf1]
      exact Subgroup.one_mem _
    · refine sSup_le fun K hK => ?_
      by_cases hKA : K = A
      · rw [hKA]
        exact le_sup_left
      by_cases hKB : K = B
      · rw [hKB]
        exact le_sup_right
      have hcA := CFSG.GorensteinWalter.component_commute_of_ne hK hA' hKA
      have hcB := CFSG.GorensteinWalter.component_commute_of_ne hK hB' hKB
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcA hcB
      intro k hk
      have hk1 : k = 1 := hC k
        (fun a ha => (Subgroup.mem_centralizer_iff.1 (hcA hk) a ha).symm)
        (fun b hb => (Subgroup.mem_centralizer_iff.1 (hcB hk) b hb).symm)
      rw [hk1]
      exact Subgroup.one_mem _
  · exact sup_le (hAE.trans le_sup_right) (hBE.trans le_sup_right)

theorem open_isComponentOf_top_map_conj {G : Type} [Group G] {A : Subgroup G}
    (hA : CFSG.Open.IsComponentOf A ⊤) (g : G) :
    CFSG.Open.IsComponentOf (A.map (MulAut.conj g).toMonoidHom) ⊤ := by
  refine ⟨le_top, ?_, Comp.quasisimple_map_conj hA.2.2 g⟩
  have h1 : A.IsSubnormal := (CFSG.Adapters.isSubnormal_top_iff A).1 hA.2.1
  exact (CFSG.Adapters.isSubnormal_top_iff _).2
    (h1.map (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem fstar_map_eq_of_components {Γ L : Subgroup (GLV V)} {x : GLV V} (hxΓ : x ∈ Γ)
    (hL : CFSG.Open.IsComponentOf L Γ)
    (hC : ∀ c : GLV V, c ∈ Γ → (∀ l ∈ L, c * l = l * c) →
      (∀ b ∈ L.map (MulAut.conj x).toMonoidHom, c * b = b * c) → c = 1) :
    (CFSG.Open.genFittingFStar ↥Γ).map Γ.subtype = L ⊔ L.map (MulAut.conj x).toMonoidHom := by
  have hLΓ : L ≤ Γ := hL.1
  set A : Subgroup ↥Γ := L.subgroupOf Γ with hAdef
  set x' : ↥Γ := ⟨x, hxΓ⟩ with hx'
  set B : Subgroup ↥Γ := A.map (MulAut.conj x').toMonoidHom with hBdef
  have hA : CFSG.Open.IsComponentOf A ⊤ := (isComponentOf_iff_subgroupOf.1 hL).2
  have hB : CFSG.Open.IsComponentOf B ⊤ := open_isComponentOf_top_map_conj hA x'
  have hAmap : A.map Γ.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLΓ
  have hBmap : B.map Γ.subtype = L.map (MulAut.conj x).toMonoidHom := by
    rw [hBdef, Subgroup.map_map, ← hAmap, Subgroup.map_map]
    rfl
  have hC' : ∀ g : ↥Γ, (∀ a ∈ A, g * a = a * g) → (∀ b ∈ B, g * b = b * g) → g = 1 := by
    intro g hgA hgB
    apply Subtype.ext
    show (g : GLV V) = 1
    refine hC g g.2 ?_ ?_
    · intro l hl
      have := hgA ⟨l, hLΓ hl⟩ (by simpa [hAdef, Subgroup.mem_subgroupOf] using hl)
      exact congrArg Subtype.val this
    · intro b hb
      rw [← hBmap] at hb
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
      exact congrArg Subtype.val (hgB b' hb')
  rw [genFittingFStar_eq_sup_of_components hA hB hC', Subgroup.map_sup, hAmap, hBmap]

end G11

end CFSG.Quasithin
