module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteOrder
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionLang

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.RootSystem
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.CentralCover CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc TableBExcTwo TableBExcTwoFusion
  TableBExcTwoTB

theorem tmStruct_card_torusPow_of_E7_E8
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hτ : τ = .E7 ∨ τ = .E8) (hK : Nat.card K = 2) :
    Nat.card (torusPow τ (FiniteField.Extension K 2 2) 3) = 3 ^ τ.rank := by
  have h3 : 3 ∣ Nat.card (FiniteField.Extension K 2 2) - 1 :=
    TableBExcTwoFusion.three_dvd_natCard_ext_sub_one hK
  rcases hτ with rfl | rfl
  · exact card_torusPow_E7 (K := FiniteField.Extension K 2 2) Nat.prime_three h3
  · exact card_torusPow_E8 (K := FiniteField.Extension K 2 2) Nat.prime_three h3

theorem tmStruct_conj_mem_torusPow
    {τ : Tag} {L : Type} [Field L] [Finite L] [CharP L 2]
    {m : adjointGroup τ L}
    (hm : (m : ModGL τ L) ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)))
    {x : adjointGroup τ L} (hx : x ∈ torusPow τ L 3) : m * x * m⁻¹ ∈ torusPow τ L 3 := by
  rw [mem_torusPow] at hx ⊢
  refine ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp hm (x : ModGL τ L)).mp hx.1
  · refine Subtype.ext ?_
    have hx3 : (x : ModGL τ L) ^ 3 = 1 := by
      have := congrArg (fun z : adjointGroup τ L => (z : ModGL τ L)) hx.2
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using this
    have h1 : ((MulAut.conj (m : ModGL τ L)) (x : ModGL τ L)) ^ 3 = 1 := by
      rw [← map_pow, hx3, map_one]
    rwa [MulAut.conj_apply] at h1

theorem tmStruct_canonicalRep_mem_normalizer_torusPow
    {τ : Tag} {L : Type} [Field L] [Finite L] [CharP L 2] (w : WeylGroup τ) :
    (⟨canonicalRep (coxeterSystem τ) L w,
      CFSG.LieType.Chevalley.canonicalRep_mem_adjointGroup (cs := coxeterSystem τ) (K := L) w⟩ :
        adjointGroup τ L) ∈
      Subgroup.normalizer ((torusPow τ L 3 : Subgroup (adjointGroup τ L)) :
        Set (adjointGroup τ L)) := by
  set n : adjointGroup τ L :=
    ⟨canonicalRep (coxeterSystem τ) L w,
      CFSG.LieType.Chevalley.canonicalRep_mem_adjointGroup (cs := coxeterSystem τ) (K := L) w⟩ with hn
  have hnN : (n : ModGL τ L) ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) :=
    CFSG.LieType.Chevalley.canonicalRep_mem_normalizer (R := L) w
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact tmStruct_conj_mem_torusPow (m := n) hnN hx
  · intro hx
    have hx' := tmStruct_conj_mem_torusPow (m := n⁻¹) (inv_mem hnN) hx
    have hx'' : x ∈ torusPow τ L 3 := by
      rw [show x = n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ by group]
      exact hx'
    exact hx''

theorem tmStruct_congr_symm {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (f : MulAut G) :
    MulAut.congr e.symm (MulAut.congr e f) = f := by
  ext x
  simp only [MulAut.congr_apply, MulEquiv.symm_trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_symm, MulEquiv.symm_apply_apply]

end CFSG.StandardType.FrameRoute

end
