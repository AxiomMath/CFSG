module

public import CFSG.Quasithin.Vol2.Ch10SecE9ZP
public import CFSG.Quasithin.Vol2.Ch10SecB48Main
public import CFSG.Quasithin.Vol2.Ch10SecE9ZE
public import CFSG.Quasithin.Vol2.Ch10SecE9ZI
public import CFSG.Quasithin.Vol2.Ch10SecE9ZM
public import CFSG.Quasithin.Vol2.Ch10SecE9ZO

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13 CFSG.Quasithin.B5 E9
open scoped commutatorElement

theorem e9PtFix_of (h56 : AsB56) (h3228 : TmpL6_3_2_2_eight)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) : E9PtFix := by
  intro G _ _ T L I hyp h3 hJ P hP hTP hpt
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  set Z := ZQ T L I
  set hZ := isElemAbelian_ZQ T L I
  have hN := le_normalizer_ZQ h37 h38 hyp
  have PD := pairData_ZQ h3228 h37 h38 hyp h3 hJ ht htn
  set L₁ := autI hZ L
  set L₂ := autI hZ (CFSG.conjugate L t)
  set S := autI hZ (T1 T L)
  set X := autI hZ (oTwoUpper P)
  have hT2 : IsPGroup 2 ↥T := hyp.fsu.sylow.1
  have hT1N : T1 T L ≤ Subgroup.normalizer (Z : Set G) := (inf_le_left.trans le_sup_right).trans hN
  have hLN : L ≤ Subgroup.normalizer (Z : Set G) :=
    ((SecA.le_fsuL0 T L).trans le_sup_left).trans hN
  have hLtN : CFSG.conjugate L t ≤ Subgroup.normalizer (Z : Set G) :=
    ((SecA.conjugate_le_fsuL0 ht).trans le_sup_left).trans hN
  have hL0N : fsuL0 T L ≤ Subgroup.normalizer (Z : Set G) := le_sup_left.trans hN
  have hJ12 : L₁ ⊔ L₂ = autI hZ (fsuL0 T L) := by
    rw [SecA.fsuL0_eq_sup h37 h38 hyp ht htn, autI_sup hZ hLN hLtN]
  have hXL0 : oTwoUpper P ≤ fsuL0 T L := (Subgroup.closure_le _).mpr fun x ⟨hxP, hodd⟩ =>
    mem_of_odd_of_le_sup hT2 (sup_le Subgroup.le_normalizer (SecA.le_fsuM T L)) (hP.1.le hxP) hodd
  have hT1L0 : T1 T L ≤ Subgroup.normalizer (fsuL0 T L : Set G) :=
    inf_le_left.trans (SecA.le_fsuM T L)
  have hS2 : IsPGroup 2 ↥S :=
    ((hT2.to_le inf_le_left).comap_of_injective _ (Subgroup.subtype_injective _)).map _
  have hSn : ∀ {K : Subgroup G}, T1 T L ≤ Subgroup.normalizer (K : Set G) →
      ∀ s ∈ S, s ∈ Subgroup.normalizer (autI hZ K : Set (MulAut (IntMod Z hZ))) := by
    intro K hK s hs
    obtain ⟨g, hg, rfl⟩ := (mem_autI hZ).mp hs
    exact convI_mem_normalizer_autI hZ (hK hg)
  have hLtn : T1 T L ≤ Subgroup.normalizer (CFSG.conjugate L t : Set G) := fun s hs =>
    mem_normalizer_conjugate h37 h38 hyp ht htn hs
  have hSn₁ := hSn (K := L) inf_le_right
  have hSn₂ := hSn hLtn
  have hXJ : X ≤ L₁ ⊔ L₂ := hJ12 ▸ autI_mono hZ hXL0
  have htM : t ∈ fsuM T L := SecA.le_fsuM T L ht
  have hV₂eq : CFSG.conjugate (fsuUL T L I) t = ⁅fsuVM T L I, CFSG.conjugate L t⁆ :=
    SecA.conjugate_commutator_fsuVM htM
  have hVZ : fsuVM T L I ≤ Z := fsuVM_le_ZQ hyp
  have hV₁Z : fsuUL T L I ≤ Z := (SecA.fsuUL_le_fsuVM T L I).trans hVZ
  have hV₂Z : CFSG.conjugate (fsuUL T L I) t ≤ Z := (SecA.conjugate_fsuUL_le htM).trans hVZ
  have hU₁ : (fsuUL T L I).comap (valZ hZ) ≤ commV L₁ := fun u hu =>
    mk_mem_commV_autI hZ hVZ hLN (show u.val ∈ ⁅fsuVM T L I, L⁆ from hu) (IntMod.val_mem u)
  have hU₂ : (CFSG.conjugate (fsuUL T L I) t).comap (valZ hZ) ≤ commV L₂ := fun u hu => by
    have hu' : u.val ∈ CFSG.conjugate (fsuUL T L I) t := hu
    rw [hV₂eq] at hu'
    exact mk_mem_commV_autI hZ hVZ hLtN hu' (IntMod.val_mem u)
  have hSU : ∀ {U : Subgroup G}, T1 T L ≤ Subgroup.normalizer (U : Set G) →
      ∀ s ∈ S, ∀ u ∈ U.comap (valZ hZ), s u ∈ U.comap (valZ hZ) := by
    intro U hU s hs u hu
    obtain ⟨g, hg, rfl⟩ := (mem_autI hZ).mp hs
    show (convI hZ g u).val ∈ U
    rw [convI_apply_val]
    exact (Subgroup.mem_normalizer_iff.mp (hU hg) _).mp hu
  have hT1V : T1 T L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    inf_le_left.trans (SecA.le_normalizer_fsuVM T L I)
  have hSU₁ := hSU (U := fsuUL T L I) (SecA.le_normalizer_commutator hT1V inf_le_right)
  have hSU₂ := hSU (U := CFSG.conjugate (fsuUL T L I) t)
    (hV₂eq ▸ SecA.le_normalizer_commutator hT1V hLtn)
  have htC : t ∈ Subgroup.normalizer (Subgroup.centralizer (fsuL0 T L : Set G) : Set G) :=
    SecA.le_normalizer_centralizer (V := fsuL0 T L) (SecA.le_fsuM T L) ht
  have htO : t ∈ Subgroup.normalizer (oTwoUpper P : Set G) := le_normalizer_oTwoUpper P (hTP ht)
  have htT : t⁻¹ ∈ Subgroup.normalizer (T1 T L : Set G) := T1_normal h37 h38 hyp (T.inv_mem ht)
  have hU₁8 : Nat.card ↥((fsuUL T L I).comap (valZ hZ) ⊔ fixV (L₁ ⊔ L₂)) =
      8 * Nat.card ↥(fixV (L₁ ⊔ L₂)) := by
    rw [hJ12]
    exact card_sup_fixV_autI hZ hL0N hV₁Z (card_fsuUL_eq h3)
  have hU₂8 : Nat.card ↥((CFSG.conjugate (fsuUL T L I) t).comap (valZ hZ) ⊔ fixV (L₁ ⊔ L₂)) =
      8 * Nat.card ↥(fixV (L₁ ⊔ L₂)) := by
    rw [hJ12]
    exact card_sup_fixV_autI hZ hL0N hV₂Z (card_conjugate_eq htC (card_fsuUL_eq h3))
  have hpt₁ : fixSec S ((fsuUL T L I).comap (valZ hZ) ⊔ fixV (L₁ ⊔ L₂)) (fixV (L₁ ⊔ L₂)) ≤
      fixSec X ((fsuUL T L I).comap (valZ hZ) ⊔ fixV (L₁ ⊔ L₂)) (fixV (L₁ ⊔ L₂)) := by
    rw [hJ12]
    exact fixSec_le_of_cond hZ hL0N hT1N hT1L0 hXL0 hpt
  have hpt₂ : fixSec S ((CFSG.conjugate (fsuUL T L I) t).comap (valZ hZ) ⊔ fixV (L₁ ⊔ L₂))
      (fixV (L₁ ⊔ L₂)) ≤ fixSec X ((CFSG.conjugate (fsuUL T L I) t).comap (valZ hZ) ⊔
        fixV (L₁ ⊔ L₂)) (fixV (L₁ ⊔ L₂)) := by
    rw [hJ12]
    exact fixSec_le_of_cond hZ hL0N hT1N hT1L0 hXL0 (ptCond_conjugate hpt htC htO htT)
  obtain ⟨g₁, hg₁L, hg₁S, hg₁4⟩ := exists_order_four h3228 h37 h38 hyp h3
  have hnS : convI hZ ⟨t⁻¹, hN (Subgroup.mem_sup_right (T.inv_mem ht))⟩ ∈
      Subgroup.normalizer (S : Set (MulAut (IntMod Z hZ))) := convI_mem_normalizer_autI hZ htT
  have hconj : ∀ a : MulAut (IntMod Z hZ), orderOf (a * g₁ * a⁻¹) = 4 := fun a => by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hg₁4]
  have hfix := pair_fixSec h56 asB4_8Three_holds (fun v => IntMod.sq_eq_one v) PD hS2 hSn₁ hSn₂
    hXJ hU₁ hU₂ hU₁8 hU₂8 hSU₁ hSU₂ hpt₁ hpt₂ hg₁L hg₁S hg₁4 (PD.swap₁ g₁ hg₁L)
    ((Subgroup.mem_normalizer_iff.mp hnS g₁).mp hg₁S) (hconj _)
  refine (Subgroup.closure_le _).mpr fun x ⟨hxP, hodd⟩ => ?_
  have hxO : x ∈ oTwoUpper P := Subgroup.subset_closure ⟨hxP, hodd⟩
  have hxL0 := hXL0 hxO
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro w hw
  have hW : quasithinOmegaOneCenter (T1 T L) ≤
      T1 T L ⊓ Subgroup.centralizer (T1 T L : Set G) := (Subgroup.closure_le _).mpr fun z hz => hz.1
  have hwc := hW hw
  obtain ⟨w', hw'⟩ : ∃ w' : IntMod Z hZ, w'.val = w :=
    ⟨IntMod.mk hZ ⟨w, omegaOne_T1_le_ZQ h37 h38 hyp hw⟩, rfl⟩
  have hw'S : w' ∈ fixSec S ⊤ (fixV (L₁ ⊔ L₂)) := by
    refine ⟨Subgroup.mem_top w', fun s hs => ?_⟩
    obtain ⟨g, hg, rfl⟩ := (mem_autI hZ).mp hs
    have e : convI hZ g w' = w' := by
      refine IntMod.val_injective ?_
      rw [convI_apply_val, hw', Subgroup.mem_centralizer_iff.mp hwc.2 _ hg, mul_inv_cancel_right]
    rw [e, mul_inv_cancel]
    exact Subgroup.one_mem _
  have h0 := (hfix hw'S).2 _ (convI_mem_autI hZ hxO (hL0N hxL0))
  have hcZ := IntMod.val_mem (convI hZ ⟨x, hL0N hxL0⟩ w' * w'⁻¹)
  rw [hJ12, mem_fixV_autI_iff hZ hL0N] at h0
  rw [IntMod.val_mul, IntMod.val_inv, convI_apply_val, hw'] at h0 hcZ
  have hc : x * w * x⁻¹ * w⁻¹ ∈ Subgroup.centralizer (fsuL0 T L : Set G) := h0
  exact (commute_of_commutator hodd (Subgroup.mem_centralizer_iff.mp hc x hxL0)
    (hZ.2 _ hcZ)).symm

end CFSG.Quasithin.Vol2.Ch10.SecB
