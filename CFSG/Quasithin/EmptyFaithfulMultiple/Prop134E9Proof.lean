module

public import CFSG.Quasithin.Vol2.Ch1Sec3E9Main
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Setup

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native CFSG.Quasithin.P134

theorem prop134E9He_of (h36 : A36CoreForSQTKCat) (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (hC : TheoremCSimple) (hF : Facts134E9He) : Prop134E9He := by
  intro G _ _ H S X P hsqtk _ hS hXH hX h9 hPX hP3 hP9
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hyp : SQTKHypCat (↥H ⧸ CFSG.pCore 2 ↥H) := SQTKHypCat.quotient_pCore ↥H hsqtk
  have hPH : P ≤ H := hPX.trans hXH
  have hexp := exp_of_setup hX h9 hPX hP3 hP9
  have hPO : P ⊓ pCoreOf 2 H = ⊥ := inf_pCoreOf_eq_bot hexp
  have hirr := irr_modO2Image hPH (inf_le_left.trans hS.1) inf_le_right
    (irr_of_setup hS hXH hX h9 hPX hP3 hP9)
  have hNT : modO2Image H (S ⊓ Subgroup.normalizer (P : Set G)) ≤ modO2Image H S :=
    modO2Image_mono inf_le_left
  have hNP : modO2Image H (S ⊓ Subgroup.normalizer (P : Set G)) ≤
      Subgroup.normalizer (modO2Image H P : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    modO2Image_le_normalizer inf_le_right
  have hXK : ∀ K : Subgroup G, H ≤ Subgroup.normalizer (K : Set G) → P ≤ K → X ≤ K := by
    intro K hHK hPK
    rw [cl_of_setup hX h9 hPX hP3 hP9]
    exact conjClosure_le fun h hh z hz =>
      (Subgroup.mem_normalizer_iff.mp (hHK (hXH hh)) z).mp (hPK hz)
  have hPpull : ∀ K : Subgroup G, pCoreOf 2 H ≤ Subgroup.normalizer (K : Set G) →
      modO2Image H P ≤ modO2Image H K → P ≤ K := fun K hOK hPK a ha =>
    mem_of_mem_modO2Image hOK (hPH ha) (hexp a ha) (hPK (mk_mem_modO2Image ha (hPH ha)))
  rcases quotient_main hyp (h36 _ hyp) (h37 _ hyp) (h38 _ hyp) hC hF
      (card_bar hXH hX h9 hPX hP3 hP9) (exp_bar hX h9 hPX hP3 hP9) (sylow_bar hS) hNT hNP hirr
      (mul_bar hS hXH hX h9 hPX hP3 hP9) (sup_bar hS hXH hX h9 hPX hP3 hP9)
      (oX_bar hXH hX h9 hPX hP3 hP9) (comm_bar hS hXH hX h9 hPX hP3 hP9) with
    hn | ⟨Lb, hLbc, hLb, hLbn, hPLb, hout⟩ | ⟨Lb, hLbc, hLb, nb, hnbN, hnbL, hinf, hPK, h3, htype⟩
  ·
    exact Or.inl (le_normalizer_of_normal hS hXH hX h9 hPX hP3 hP9 hn)
  ·
    right
    obtain ⟨L, hL, rfl⟩ := exists_cComp_modO2Image_eq hLbc
    obtain ⟨e⟩ := modO2_mulEquiv hL
    have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hLb.1
    have hLH : L ≤ H := le_of_mem_cComp hL
    have hLnH : (L.subgroupOf H).Normal :=
      normal_of_normal_map_of_mem_cComp (CFSG.pCore 2 ↥H) (isSolvable_pCore_two_group ↥H)
        (subgroupOf_mem_cComp hL) hLbn
    have hHL : H ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mp hLnH
    have hSL : S ≤ Subgroup.normalizer (L : Set G) := hS.1.trans hHL
    have hPL : P ≤ L := hPpull L (pCoreOf_le_normalizer_of_mem_cComp hL) hPLb
    have hcl : conjClosure L S = L := by
      refine le_antisymm (conjClosure_le fun g hg l hl => ?_) (le_conjClosure L S)
      exact (Subgroup.mem_normalizer_iff.mp (hSL hg) l).mp hl
    refine ⟨L, hL, hq, hcl.symm ▸ hXK L hHL hPL, ?_⟩
    rcases hout with h2 | ⟨m, hm, hsp, hcyc⟩ | he' | h4 | h5 | hHe
    · exact Or.inr (Or.inl ⟨hSL, Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h2)⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hSL,
        ⟨m, hm, CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hsp⟩,
        autCyclic_of_bar hS hXH hX h9 hPX hP3 hP9 hcyc⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hSL, Or.inl (he'.map fun e' => e.trans e')⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hSL, Or.inr (Or.inl
        (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h4))⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hSL, Or.inr (Or.inr
        (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h5))⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hHL, hHe.map fun e' => e.trans e'⟩)))
  ·
    right
    obtain ⟨L, hL, rfl⟩ := exists_cComp_modO2Image_eq hLbc
    obtain ⟨e⟩ := modO2_mulEquiv hL
    have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hLb.1
    obtain ⟨t', ht', rfl⟩ := hnbN
    set t : G := (t' : G) with ht
    have htSN : t ∈ S ⊓ Subgroup.normalizer (P : Set G) := ht'
    have htH : t ∈ H := t'.2
    set Lt := L.map (MulAut.conj t).toMonoidHom with hLt
    have hLtc : Lt ∈ cComp H := map_conj_mem_cComp hL htH
    have hLtb : modO2Image H Lt = (modO2Image H L).map (MulAut.conj (π t')).toMonoidHom :=
      modO2Image_conj t'
    have htL : t ∉ Subgroup.normalizer (L : Set G) := by
      intro h
      apply hnbL
      rw [← A38.map_conj_eq_iff, ← hLtb, hLt, A38.map_conj_eq_iff.mpr h]
    set A := P ⊓ L with hA
    have hAH : A ≤ H := inf_le_left.trans hPH
    have hAb : modO2Image H A = modO2Image H P ⊓ modO2Image H L := by
      refine le_antisymm (le_inf (modO2Image_mono inf_le_left) (modO2Image_mono inf_le_right))
        fun x hx => ?_
      obtain ⟨⟨a, haH⟩, haP, rfl⟩ := hx.1
      have haL : a ∈ L :=
        mem_of_mem_modO2Image (pCoreOf_le_normalizer_of_mem_cComp hL) haH (hexp a haP) hx.2
      exact mk_mem_modO2Image (Y := A) (show a ∈ P ⊓ L from ⟨haP, haL⟩) haH
    have hA3 : Nat.card A = 3 := by
      rw [← card_modO2Image hAH (eq_bot_iff.mpr ((inf_le_inf_right _ inf_le_left).trans
        hPO.le)), hAb]
      exact h3
    set A' := conjByElt t A with hA'
    have hA'P : A' ≤ P := by
      rintro _ ⟨a, ha, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp htSN.2 a).mp ha.1
    have hA'3 : Nat.card A' = 3 := by
      rw [hA', conjByElt, Subgroup.card_map_of_injective (MulAut.conj t).injective, hA3]
    have hAA' : A ⊓ A' = ⊥ := by
      refine eq_bot_iff.mpr fun x hx => ?_
      have hxP : x ∈ P := hx.1.1
      have hxH : x ∈ H := hPH hxP
      have hxLt : x ∈ Lt := Subgroup.map_mono (inf_le_right : A ≤ L) hx.2
      have h1 : π ⟨x, hxH⟩ ∈
          modO2Image H L ⊓ (modO2Image H L).map (MulAut.conj (π t')).toMonoidHom :=
        ⟨mk_mem_modO2Image hx.1.2 hxH, hLtb ▸ mk_mem_modO2Image hxLt hxH⟩
      rw [hinf, Subgroup.mem_bot] at h1
      have h2 : π ⟨x, hxH⟩ = π ⟨1, H.one_mem⟩ := by
        rw [h1]
        exact (map_one π).symm
      rw [eq_of_mk_eq hPO hxP P.one_mem hxH H.one_mem h2]
      exact Subgroup.one_mem _
    have hAne : A ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hA3
      omega
    have hPAA : P = A ⊔ A' := by
      symm
      by_contra hne
      have hle : A ⊔ A' ≤ P := sup_le inf_le_left hA'P
      have hne1 : A ⊔ A' ≠ ⊥ := fun h => hAne (eq_bot_iff.mpr (h ▸ le_sup_left))
      have hc := card_eq_three_of_lt hP9 hle hne1 hne
      have h1 : A = A ⊔ A' := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hc, hA3])
      have h2 : A' = A ⊔ A' := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hc, hA'3])
      have h3' : A ⊓ A' = A := by rw [h1, ← h2, inf_idem]
      exact hAne (h3'.symm.trans hAA')
    have hOLt : pCoreOf 2 H ≤ Subgroup.normalizer ((L ⊔ Lt : Subgroup G) : Set G) :=
      fun o ho => Subgroup.inf_normalizer_le_normalizer_sup L Lt
        ⟨pCoreOf_le_normalizer_of_mem_cComp hL ho, pCoreOf_le_normalizer_of_mem_cComp hLtc ho⟩
    have hPLLt : P ≤ L ⊔ Lt := by
      refine hPpull _ hOLt (hPK.trans ?_)
      rw [← hLtb]
      exact sup_le (modO2Image_mono le_sup_left) (modO2Image_mono le_sup_right)
    have hLLtS : L ⊔ Lt ≤ conjClosure L S := by
      refine sup_le (le_conjClosure L S) ?_
      rintro _ ⟨l, hl, rfl⟩
      exact mem_conjClosure htSN.1 hl
    have hHcl : H ≤ Subgroup.normalizer (conjClosure L S : Set G) :=
      normal_conjClosure_of_subgroup hS hL (h37 _ hyp) (h38 _ hyp)
    refine ⟨L, hL, hq, hXK _ hHcl (hPLLt.trans hLLtS), Or.inl ⟨⟨t, htSN, htL, hPAA, hAA'⟩, ?_⟩⟩
    rcases htype with ⟨m, hm, hmod⟩ | ⟨q, hqp, hq2, hmod⟩
    · exact Or.inl ⟨m, hm, CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hmod⟩
    · exact Or.inr ⟨q, hqp, hq2, CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hmod⟩

end CFSG.Quasithin.EmptyFaithfulMultiple
