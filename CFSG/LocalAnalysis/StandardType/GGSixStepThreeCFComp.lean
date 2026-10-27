module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionBridge

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Components

variable {G : Type} [Group G]

theorem ggIsComponentOf_conj {K X : Subgroup G} (hK : IsComponentOf K X) {x : G} (hx : x ∈ X) :
    IsComponentOf (K.map (MulAut.conj x).toMonoidHom) X := by
  have hker : ¬ K ≤ (MulAut.conj x).toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr (MulAut.conj x).injective, le_bot_iff]
    exact ggComponent_ne_bot hK
  have h := ggIsComponentOf_map (MulAut.conj x).toMonoidHom hK hker
  have hX : X.map (MulAut.conj x).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hx)
  rwa [hX] at h

theorem ggLayer_le (X : Subgroup G) : LargeEvenLayer X ≤ X :=
  sSup_le fun _ hK => hK.1

theorem ggLe_layer {K X : Subgroup G} (hK : IsComponentOf K X) : K ≤ LargeEvenLayer X :=
  le_sSup hK

theorem ggLayer_normal (X : Subgroup G) : ((LargeEvenLayer X).subgroupOf X).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (ggLayer_le X)]
  intro h k hh hk
  have hmap : (LargeEvenLayer X).map (MulAut.conj k).toMonoidHom ≤ LargeEvenLayer X := by
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact ggLe_layer (ggIsComponentOf_conj hK hk)
  exact hmap ⟨h, hh, by simp [MulAut.conj_apply]⟩

theorem ggMem_centralizer_sSup {S : Set (Subgroup G)} {c : G}
    (hc : ∀ L ∈ S, ∀ l ∈ L, c * l = l * c) :
    c ∈ Subgroup.centralizer ((sSup S : Subgroup G) : Set G) := by
  have hle : sSup S ≤ Subgroup.centralizer (({c} : Set G)) := by
    refine sSup_le fun L hL l hl => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hc L hL l hl).symm
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

variable [Finite G]

theorem ggSSup_components_normal_layer {X : Subgroup G} {S : Set (Subgroup G)}
    (hS : ∀ L ∈ S, IsComponentOf L X) :
    ((sSup S : Subgroup G).subgroupOf (LargeEvenLayer X)).Normal := by
  have hSle : sSup S ≤ LargeEvenLayer X := sSup_le fun L hL => ggLe_layer (hS L hL)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hSle]
  refine sSup_le fun C hC => ?_
  by_cases hmem : ∃ L ∈ S, C ≤ L
  · obtain ⟨L, hL, hCL⟩ := hmem
    exact (hCL.trans (le_sSup hL)).trans Subgroup.le_normalizer
  · push Not at hmem
    intro c hc
    have hcomm : ∀ L ∈ S, ∀ l ∈ L, c * l = l * c := by
      intro L hL l hl
      have hLX := hS L hL
      have hsn : (L.subgroupOf X).IsSubnormal := (ggAssemblyIsSubnormal_iff hLX.1).mp hLX.2.1
      rcases ggComponent_le_or_commute hC hsn with hle | hco
      · exact absurd hle (hmem L hL)
      · exact hco c hc l ⟨hLX.1 hl, hl⟩
    exact Subgroup.centralizer_le_normalizer _ (ggMem_centralizer_sSup hcomm)

theorem ggIsSubnormal_sSup_components {X : Subgroup G} {S : Set (Subgroup G)}
    (hS : ∀ L ∈ S, IsComponentOf L X) : IsSubnormal (sSup S) X :=
  IsSubnormal.step (sSup_le fun L hL => ggLe_layer (hS L hL)) (ggSSup_components_normal_layer hS)
    (IsSubnormal.step (ggLayer_le X) (ggLayer_normal X) (IsSubnormal.refl X))

theorem ggIsSubnormal_sup_components {X L₂ L₃ : Subgroup G} (h₂ : IsComponentOf L₂ X)
    (h₃ : IsComponentOf L₃ X) : IsSubnormal (L₂ ⊔ L₃) X := by
  have h := ggIsSubnormal_sSup_components (S := {L₂, L₃}) (X := X) (by
    rintro L (rfl | rfl)
    · exact h₂
    · exact h₃)
  rwa [sSup_pair] at h

end Components

end CFSG.StandardType
