module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.Row9Core
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.Row9Split
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.Row9Model
import CFSG.LieType.HighestRoot.CentTrialityThree

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace Stellmacher.CD.L3YC

variable {G : Type} [Group G] [Finite G]

theorem false_row9 {H S L L₁ : Subgroup G} (hS : IsSylowTwoOf S H) (hLH : L ≤ H) (hLL₁ : L ≤ L₁)
    (hN : (L₁.subgroupOf H).Normal)
    (hsplit : ∀ s ∈ S, ∃ p ∈ S ⊓ L, ∃ c ∈ S,
      (∀ x ∈ L, ∃ m ∈ pCoreOf 2 L, c * x * c⁻¹ = x * m) ∧ s = p * c)
    (s : Bool) (h9 : IsSL2 7 ↥(modO2Image H L))
    (h : IsPSLEps3 s 7 1 ↥(modO2Image H L₁) ∨ IsSLEps3 s 7 ↥(modO2Image H L₁)) : False := by
  obtain ⟨e⟩ := h9
  have hqs : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)) :=
    CFSG.LieType.HighestRoot.isQuasisimple_SL2_of_four_le (by rw [Nat.card_zmod]; norm_num)
  have hq : CFSG.IsQuasisimple ↥(modO2Image H L) :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).2 hqs
  have hn : ¬ IsPGroup 2 (↥(modO2Image H L) ⧸ Subgroup.center ↥(modO2Image H L)) := by
    intro hp
    have hsol : Group.IsSolvable (↥(modO2Image H L) ⧸ Subgroup.center ↥(modO2Image H L)) :=
      by have := IsPGroup.isNilpotent hp; infer_instance
    have hs : IsSimpleGroup (↥(modO2Image H L) ⧸ Subgroup.center ↥(modO2Image H L)) := hq.2.1
    obtain ⟨a, b, hab⟩ := hq.2.2
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsol a b)
  have hSb : IsSylowTwoOf ((S.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hS)
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) (QuotientGroup.mk'_surjective _)
  have hN1 : (modO2Image H L₁).Normal :=
    Subgroup.Normal.map hN _ (QuotientGroup.mk'_surjective _)
  have hLL : modO2Image H L ≤ modO2Image H L₁ := Subgroup.map_mono fun _ hx => hLL₁ hx
  have hsplitb := split_bar_quasi hS.1 hLH hsplit hq hn
  obtain ⟨k, o, m, hk, ho, hkm, hC⟩ := Row9.row9_model s h
  refine false_row9_core hSb hN1 hLL hsplitb ⟨e⟩ hk ho hkm ?_
  intro z g hz hg hz2 hz1 hord hzc Q hQ hQp
  refine hC z g hz2 hz1 hord (hzc g hg ▸ rfl) Q (fun q hq' => ?_) hQp
  have hqc := Subgroup.mem_centralizer_iff.mp (hQ hq')
  exact ⟨(hqc z hz).symm, (hqc g hg).symm⟩

end Stellmacher.CD.L3YC

end CFSG.Quasithin
