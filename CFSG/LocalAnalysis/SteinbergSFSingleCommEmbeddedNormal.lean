module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommEmbeddedDefs
public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixFElementary
public import CFSG.LocalAnalysis.SteinbergSFSingleCommRootStandardClosure

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section Steps

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type} [Field K]
  [CharP K 2] [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

theorem sixEmb_e3_aux_key {H : Type} [Group H] (a b v : H) (ha : a * a = 1) (hb : b * b = 1) :
    (MulAut.conj b⁻¹).toMonoidHom ((MulAut.conj (b * a * b)⁻¹).toMonoidHom v) =
      a⁻¹ * (MulAut.conj b⁻¹).toMonoidHom v * a := by
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev, inv_inv, hb', ha']
  calc _ = (b * b) * (a * (b * v * b) * a) * (b * b) := by group
    _ = a * (b * v * b) * a := by rw [hb]; simp

theorem sixEmb_e3_aux_w_mem (hS : SCSetting L K n φ t i) :
    w φ i ∈ normalizer (Mhat φ t i i : Set G) :=
  (SixF.weylProductConclusion_both hS.fc i hS.ne_bot hS.eq_bot).1.2.2.2.2.2.2.2.2.2.2

theorem sixEmb_e3_aux_embVw_le_Mhat :
    embVw φ t i ≤ Mhat φ t i i.swap :=
  le_trans (Subgroup.map_mono (f := (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom)
    (inf_le_left : Vtor φ t i i ≤ Mc φ t i)) le_sup_right

theorem sixEmb_e3_aux_Mhat_le_S (k : Axis) : Mhat φ t i k ≤ S φ t i := by
  cases k
  · exact le_sup_left
  · exact le_sup_right

theorem sixEmb_e3_aux_S_le_Tplus (hH : SixHConclusion φ t i) : S φ t i ≤ Tplus φ t i := by
  rw [← hH.sup_t]
  exact le_sup_left

theorem sixEmb_e3_aux_embVw_le_Tplus (hH : SixHConclusion φ t i) : embVw φ t i ≤ Tplus φ t i :=
  le_trans (le_trans (sixEmb_e3_aux_embVw_le_Mhat (φ := φ) (t := t) (i := i))
    (sixEmb_e3_aux_Mhat_le_S (φ := φ) (t := t) (i := i) i.swap))
    (sixEmb_e3_aux_S_le_Tplus hH)

theorem sixEmb_e3_aux_Tplus_le (hH : SixHConclusion φ t i) :
    Tplus φ t i ≤ normalizer (Mhat φ t i i : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (hH.normal_Mhat i).1).1 (hH.normal_Mhat i).2.1

theorem sixEmb_e3
    (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i) (hgen : EmbGenConcl φ t i) :
    Ytilde φ i ≤ normalizer (Mhat φ t i i : Set G) := by
  have hE : embVw φ t i ≤ normalizer (Mhat φ t i i : Set G) :=
    le_trans (sixEmb_e3_aux_embVw_le_Tplus hH) (sixEmb_e3_aux_Tplus_le hH)
  have ha : w φ i ∈ normalizer (Mhat φ t i i : Set G) := sixEmb_e3_aux_w_mem hS
  have hgen' : Ytor φ i =
      Vtor φ t i i ⊔ (Vtor φ t i i).map (MulAut.conj (embTau φ i)⁻¹).toMonoidHom := hgen
  show (Ytor φ i).map (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom ≤
    normalizer (Mhat φ t i i : Set G)
  rw [hgen', Subgroup.map_sup]
  refine sup_le hE ?_
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy
  have hv' : (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom v ∈ normalizer (Mhat φ t i i : Set G) :=
    hE (Subgroup.mem_map_of_mem (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom hv)
  have key : (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom
      ((MulAut.conj (embTau φ i)⁻¹).toMonoidHom v) =
      (w φ i)⁻¹ * (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom v * w φ i :=
    sixEmb_e3_aux_key (w φ i) (w φ i.swap) v (FullCenterWeyl.w_mul_self (φ := φ) i)
      (FullCenterWeyl.w_mul_self (φ := φ) i.swap)
  rw [key]
  exact (normalizer (Mhat φ t i i : Set G)).mul_mem
    ((normalizer (Mhat φ t i i : Set G)).mul_mem
      ((normalizer (Mhat φ t i i : Set G)).inv_mem ha) hv') ha

theorem sixEmb_e4
    (hS : SCSetting L K n φ t i) : embVw φ t i ≤ Ytilde φ i := by
  show (Vtor φ t i i).map (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom ≤
    (Ytor φ i).map (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom
  exact Subgroup.map_mono (RootStandard.V_le_Y hS.fc i hS.ne_bot hS.eq_bot i)

end Steps

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
