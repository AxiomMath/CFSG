module

public import CFSG.RankThree.PartTwo.Sec20.OneBasics
public import CFSG.RankThree.PartTwo.KFacts.L34Automizer
public import CFSG.RankThree.PartTwo.Sec20.OneFrontierCleanStatements

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def quotientRestrictEquiv {L B : Subgroup G} (hBL : B ≤ L)
    (hinj : Function.Injective
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (B.subgroupOf L).subtype)) :
    B ≃* ((B.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) :=
  (Subgroup.subgroupOfEquivOfLe hBL).symm.trans
    ((MonoidHom.ofInjective hinj).trans
      (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype])))

omit [Finite G] in
theorem quotientRestrictEquiv_apply {L B : Subgroup G} (hBL : B ≤ L)
    (hinj : Function.Injective
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (B.subgroupOf L).subtype)) (w : B) :
    ((quotientRestrictEquiv hBL hinj w : _) : ↥L ⧸ CFSG.pCore 2 ↥L) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨w, hBL w.2⟩ :=
  rfl

section Q8


theorem injective_mk_of_hyp201One (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1)
    {A M L N : Subgroup G} {c : G} (h : Hyp201One G A M L N c) :
    Function.Injective ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp
      ((A ⊓ L).subgroupOf L).subtype) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB3 : IsPGroup 3 ((A ⊓ L).subgroupOf L) :=
    (isSylowOf_three_inf_of_hyp201One h1812 h184 h).isPGroup.comap_subtype
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hx
  have h1 : (x : ↥L) ∈ (A ⊓ L).subgroupOf L ⊓ CFSG.pCore 2 ↥L := ⟨x.2, hx⟩
  have hbot : (A ⊓ L).subgroupOf L ⊓ CFSG.pCore 2 ↥L = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ (card_inf_eq_one_of_isPGroup hB3 CFSG.pCore_isPGroup)
  rw [hbot, Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.mpr (Subtype.ext h1)

theorem map_autIn_le_of_hyp201One (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1)
    {A M L N : Subgroup G} {c : G} (h : Hyp201One G A M L N c) :
    (Sec4.autIn ⊤ (((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)))).map
        (MulAut.congr (quotientRestrictEquiv inf_le_right
          (injective_mk_of_hyp201One h1812 h184 h)).symm).toMonoidHom ≤
      Sec4.autIn M (A ⊓ L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBL : A ⊓ L ≤ L := inf_le_right
  have hAM : A ≤ M := le_of_hyp201 h.1
  have hNB := normalizer_inf_le_of_hyp201One h (card_inf_of_hyp201One h1812 h184 h)
  have hB3 : IsPGroup 3 (A ⊓ L : Subgroup G) :=
    (isSylowOf_three_inf_of_hyp201One h1812 h184 h).isPGroup
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  set β := quotientRestrictEquiv hBL (injective_mk_of_hyp201One h1812 h184 h) with hβ
  rintro _ ⟨τ, hτ, rfl⟩
  obtain ⟨z, hzN, -, rfl⟩ := Sec4.mem_autIn_iff.mp hτ
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) z
  obtain ⟨y, hy, m, hm, rfl⟩ := exists_mul_of_mk_mem_normalizer hBL hB3 hzN
  obtain ⟨b, hb, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
  have hbB : ((b : ↥L) : G) ∈ A ⊓ L := Subgroup.mem_subgroupOf.mp hb
  have hnN : ((b : G) * (m : G)) ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) :=
    mul_mem (Subgroup.le_normalizer hbB) hm
  refine Sec4.mem_autIn_iff.mpr ⟨(b : G) * m, hnN, M.mul_mem (hAM hbB.1) (hNB hm), ?_⟩
  have ho1 : π o = 1 := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ho
  apply MulEquiv.ext
  intro w
  apply β.injective
  rw [MulEquiv.coe_toMonoidHom, MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply,
    MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [Sec4.normalizerMonoidHom_apply_coe, quotientRestrictEquiv_apply,
    quotientRestrictEquiv_apply]
  have hval : (⟨((A ⊓ L).normalizerMonoidHom ⟨(b : G) * m, hnN⟩ w : G),
      hBL ((A ⊓ L).normalizerMonoidHom ⟨(b : G) * m, hnN⟩ w).2⟩ : ↥L) =
      b * m * ⟨w, hBL w.2⟩ * (b * m)⁻¹ := by
    apply Subtype.ext
    rw [Sec4.normalizerMonoidHom_apply_coe]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hval, map_mul, map_mul, map_mul, map_mul, map_mul, map_inv, map_mul, ho1, mul_one]

theorem hasSection_autIn_of_hyp201One (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1)
    {A M L N : Subgroup G} {c : G} (h : Hyp201One G A M L N c) :
    Sec4.HasSection (Sec4.autIn M (A ⊓ L)) (QuaternionGroup 2) := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  set Bb := ((A ⊓ L).subgroupOf L).map π with hBb
  obtain ⟨e⟩ := nonempty_quotient_of_hyp201One h184 h
  set e' := e.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)) with he'
  have hBb' : Nat.card (Bb.map e'.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (f := e'.toMonoidHom) e'.injective,
      card_map_inf_of_hyp201One h1812 h184 h]
  obtain ⟨q⟩ := KFacts.L34.nonempty_automizer_of_card_eq_nine
    KFacts.L34.card_galoisField_two_two hBb'
  let qB : Sec4.autIn ⊤ Bb ≃* QuaternionGroup 2 :=
    (KFacts.L34.automizerEquivAutIn Bb).symm.trans
      ((CFSG.RankThree.Asc83Table.automizerCongr e' Bb).trans q)
  set κ := MulAut.congr (quotientRestrictEquiv inf_le_right
    (injective_mk_of_hyp201One h1812 h184 h)).symm with hκ
  have hle := map_autIn_le_of_hyp201One h1812 h184 h
  let f : Sec4.autIn ⊤ Bb →* Sec4.autIn M (A ⊓ L) :=
    (κ.toMonoidHom.comp (Sec4.autIn ⊤ Bb).subtype).codRestrict (Sec4.autIn M (A ⊓ L))
      fun x => hle ⟨x, x.2, rfl⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 := congrArg Subtype.val hxy
    exact Subtype.ext (κ.injective h1)
  refine KFacts.L34.hasSection_of_injective ?_ f hf
  exact KFacts.L34.hasSection_congr_right (KFacts.L34.hasSection_quotient ⊥)
    (QuotientGroup.quotientBot.trans qB)

theorem item203One2_of_items (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1) :
    Item203One2 :=
  fun _ _ _ _ _ _ _ _ h => hasSection_autIn_of_hyp201One h1812 h184 h

end Q8

end CFSG.RankThree.PartTwo.Sec20
