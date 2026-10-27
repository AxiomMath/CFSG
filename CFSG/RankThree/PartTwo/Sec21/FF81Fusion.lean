module

import CFSG.GF2Type.Aschbacher1976Full.HSBurnside
import CFSG.LocalAnalysis.StandardType.GGSixFusion
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

variable {G : Type} [Group G] [Finite G]

theorem isElemAb_conjBy {p k : ℕ} {B : Subgroup G} (hB : IsElemAb p k B) (g : G) :
    IsElemAb p k (conjBy g B) :=
  ⟨CFSG.IsElementaryAbelian.subgroup_map hB.1 _,
    (Subgroup.card_map_of_injective (MulAut.conj g).injective).trans hB.2⟩

theorem controlsFusionIn_of_unique {p k : ℕ} [Fact p.Prime] {B : Subgroup G}
    (hB : IsElemAb p k B) (P : Sylow p (Nor B))
    (hU : ∀ A : Subgroup G, A ≤ (P : Subgroup (Nor B)).map (Nor B).subtype → IsElemAb p k A →
      A = B) :
    ControlsFusionIn B := by
  set P' := (P : Subgroup (Nor B)).map (Nor B).subtype with hP'
  have hBp : IsPGroup p B := IsPGroup.of_card hB.2
  have hBP : B ≤ P' := by
    have : (B.comap (Nor B).subtype).Normal := Subgroup.normal_in_normalizer
    have hle := (hBp.comap_of_injective (Nor B).subtype Subtype.coe_injective).le_sylow_of_normal P
    intro x hx
    exact ⟨⟨x, Subgroup.le_normalizer hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hconj : ∀ g ∈ Subgroup.normalizer (P' : Set G), conjBy g B = B := by
    intro g hg
    refine hU _ ?_ (isElemAb_conjBy hB g)
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg x).mp (hBP hx)
  have hNP : Subgroup.normalizer (P' : Set G) ≤ Nor B := fun g hg =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hconj g hg)
  obtain ⟨Q, hQ0⟩ := CFSG.StandardType.exists_sylow_eq_map_of_normalizer_le P hNP
  have hQ : (Q : Subgroup G) = P' := hQ0
  have hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hB.1.toIsMulCommutative.is_comm.comm (⟨a, ha⟩ : B) ⟨b, hb⟩)
  have hweak : ∀ g : G, CFSG.conjugate B g ≤ (Q : Subgroup G) → CFSG.conjugate B g = B :=
    fun g hg => hU _ (by rw [← hQ]; exact hg) (isElemAb_conjBy hB g⁻¹)
  intro x hx y hy g hgy
  obtain ⟨n, hn, hnx⟩ := CFSG.GF2Type.Aschbacher1976Full.HS.burnside_fusion Q B (by rw [hQ]; exact hBP) hab
    hweak hx (hgy ▸ hy)
  exact ⟨n, hn, hnx.trans hgy⟩

end CFSG.RankThree.PartTwo.Sec21.FF81
