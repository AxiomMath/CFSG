module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24D4Cat
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Layer
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24Grp

public section

namespace CFSG.Sporadic.Fi24I301

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LocalAnalysis.GLTheoremB

section Conj

variable {G : Type} [Group G]

private theorem glaPLayer_gLBConj_aux (p : ℕ) (g : G) (X : Subgroup G) :
    GLAPLayer p (GLBConj g X) = GLBConj g (GLAPLayer p X) := by
  refine gLBConj_eq_of_forall_ge (F := GLAPLayer p) (fun g X => ?_) g X
  unfold GLBConj
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun L hL => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (glaPComponent_gLBConj hL g)

variable [Finite G]

private theorem isTypeWithCenter_of_pQuot_equiv_aux {p : ℕ} {X Y : Subgroup G}
    (e : PQuot p X ≃* PQuot p Y) {Q : TauCeti.CFSGIndex → Prop} {z : ℕ}
    (h : IsTypeWithCenter p X Q z) : IsTypeWithCenter p Y Q z := by
  obtain ⟨⟨i, hi, ⟨f⟩⟩, hz⟩ := h
  exact ⟨⟨i, hi, ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).symm.trans f⟩⟩,
    (Nat.card_congr (Subgroup.centerCongr e).symm.toEquiv).trans hz⟩

theorem isTypeWithCenter_glaPLayer_centralizer_of_isConj {p : ℕ}
    {Q : TauCeti.CFSGIndex → Prop} {z : ℕ} {x y : G} (hxy : IsConj x y)
    (h : IsTypeWithCenter p (GLAPLayer p (Subgroup.centralizer ({x} : Set G))) Q z) :
    IsTypeWithCenter p (GLAPLayer p (Subgroup.centralizer ({y} : Set G))) Q z := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hxy
  have hC : Subgroup.centralizer ({c * x * c⁻¹} : Set G) =
      GLBConj c⁻¹ (Subgroup.centralizer ({x} : Set G)) := by
    rw [← centralizer_singleton_gLBConj, inv_inv]
  rw [hC, glaPLayer_gLBConj_aux]
  exact isTypeWithCenter_of_pQuot_equiv_aux (conjQuotEquiv p c⁻¹ _) h

end Conj

section PIndex

variable {G : Type} [Group G] [Finite G]

theorem glaPLayer_eq_of_isSimple_index_sq {p : ℕ} (hp : p.Prime) {C L : Subgroup G} (hLC : L ≤ C)
    (hs : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hpL : p ∣ Nat.card ↥L)
    (hk : Nat.card ↥C = Nat.card ↥L * p ^ 2) (hfac : (p ^ 2).factorial < Nat.card ↥C) :
    GLAPLayer p C = L := by
  haveI : Fact p.Prime := ⟨hp⟩
  let E : Subgroup ↥C := L.subgroupOf C
  have eL : ↥E ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLC
  haveI : IsSimpleGroup ↥E := eL.isSimpleGroup_congr.2 hs
  have hpos : 0 < Nat.card ↥L := Nat.card_pos
  have hidx : E.index = p ^ 2 := by
    have h1 : E.index * Nat.card ↥E = Nat.card ↥C := Subgroup.index_mul_card E
    rw [Nat.card_congr eL.toEquiv, hk] at h1
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h1, mul_comm])
  haveI hEn : E.Normal := CFSG.HardMathSupport.Dickson.I271.normal_of_isSimple_of_index E hidx
    (pow_ne_zero 2 hp.ne_zero) hfac
  have hSn : ∀ g ∈ C, ∀ s ∈ L, g * s * g⁻¹ ∈ L := fun g hg s hs =>
    Subgroup.mem_subgroupOf.1 (hEn.conj_mem ⟨s, hLC hs⟩ (Subgroup.mem_subgroupOf.2 hs) ⟨g, hg⟩)
  have hq : Nat.card (↥C ⧸ E) = p ^ 2 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  have hab := IsPGroup.commutative_of_card_eq_prime_sq hq
  have hc : ⁅C, C⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    have h1 : (QuotientGroup.mk ((⟨a, ha⟩ : ↥C) * ⟨b, hb⟩ * (⟨a, ha⟩ : ↥C)⁻¹ *
        (⟨b, hb⟩ : ↥C)⁻¹) : ↥C ⧸ E) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv, hab (QuotientGroup.mk ⟨a, ha⟩) (QuotientGroup.mk ⟨b, hb⟩)]
      group
    exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)
  exact H301.glaPLayer_eq_of_isSimple_normal_commutator_le hp hLC hSn hs hnab hpL hc

end PIndex

section Fi24

open CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Dickson.I271.TabFi24
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three (fi24Rep3)
open CFSG.Sporadic.Fi24 (J)


theorem glaPLayer_cent0 : GLAPLayer 3 cent0 = fiN := by
  obtain ⟨hcard, hsimple, hnab, -⟩ := fiN_facts
  refine glaPLayer_eq_of_isSimple_index_sq Nat.prime_three
    (fiN_le_lvl_two.trans lvl_two_le_cent0) hsimple hnab ?_ ?_ ?_
  · rw [hcard]
    norm_num
  · rw [card_cent0, hcard]
    norm_num
  · rw [card_cent0]
    decide

theorem isTypeWithCenter_layer_s0 : IsTypeWithCenter 3 (GLAPLayer 3 cent0) (isD4of 3) 1 := by
  obtain ⟨hcard, hsimple, hnab, -⟩ := fiN_facts
  rw [glaPLayer_cent0]
  exact H301.isTypeWithCenter_of_isSimple Nat.prime_three hsimple hnab (by rw [hcard]; norm_num)
    catalogIs_fiN

theorem isTypeWithCenter_layer_rep0 :
    IsTypeWithCenter 3 (GLAPLayer 3 (Subgroup.centralizer ({fi24Rep3 0} : Set J))) (isD4of 3)
      1 := by
  have hconj : IsConj s0 (fi24Rep3 0) := isConj_rep0_s0.symm
  exact isTypeWithCenter_glaPLayer_centralizer_of_isConj hconj isTypeWithCenter_layer_s0

end Fi24

end CFSG.Sporadic.Fi24I301
