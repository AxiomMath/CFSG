module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Nine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3NineH
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3NineA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G]

theorem s1611e3_nine_pRank_two_le {D : Data G} (h : S1611e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h9 : Case168_9 D V₀ V hV L) :
    CFSG.Open.pRank 2 (Mbar D.M V₀ V hV) ≤ 4 := by
  classical
  obtain ⟨g, hg⟩ := s1611e3_nine_two D h.h1217 hV hc (s1611e3_nine_v1Sub h9) h9
  refine CFSG.SectionRank.pRank_le (p := 2) (by norm_num) ?_
  intro E hEM hEab
  have hEab2 : IsElemAbelian2 E :=
    ⟨fun a ha b hb => by
      simpa [Subgroup.coe_mul] using
        congrArg Subtype.val (hEab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩), hEab.2⟩
  have hcard4 : ∀ E' : Subgroup (MulAut (Vtil V₀ V hV)), E' ≤ Mbar D.M V₀ V hV →
      IsElemAbelian2 E' →
      E' ≤ Subgroup.normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) →
      E' ≤ Subgroup.normalizer (((lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom :
        Subgroup (MulAut (Vtil V₀ V hV))) : Set (MulAut (Vtil V₀ V hV))) →
      (∀ x ∈ E', ∀ a ∈ lBar V₀ V hV L, x * a = a * x) → Nat.card ↥E' ≤ 4 :=
    fun E' hE'M hE'ab hE'NL hE'NB hcent =>
      s1611e3_nine_card_le_four_of_acttriv h hc h9 hg hE'M hE'ab hE'NL hE'NB hcent
  have hfaith : ∀ x ∈ Mbar D.M V₀ V hV, x * x = 1 →
      (∀ a ∈ lBar V₀ V hV L, x * a = a * x) →
      (∀ a ∈ (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom, x * a = a * x) → x = 1 :=
    fun x hxM hx2 hxL hxL' =>
      s1611e3_nine_faith_of_comm h hc h9 hg hxM hx2 hxL hxL'
        (s1611e3_nine_center_comm h hc h9 hxM hx2 hxL)
  have h16 := s1611e3_nine_abs_card_le_sixteen hg h9.2.1 hcard4 hfaith hEM hEab2
  calc Nat.card ↥E ≤ 16 := h16
    _ = 2 ^ 4 := by norm_num

theorem s1611e3_nine_five_le_rkIdx {D : Data G} (h : S1611e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h9 : Case168_9 D V₀ V hV L)
    {E : Subgroup (MulAut (Vtil V₀ V hV))} (hE : E ≤ Mbar D.M V₀ V hV) (hab : IsElemAbelian2 E)
    (h3 : 3 ≤ rk ↥E) : 5 ≤ rkIdx (fixV E) := by
  classical
  obtain ⟨g, hg⟩ := s1611e3_nine_two D h.h1217 hV hc (s1611e3_nine_v1Sub h9) h9
  have hW : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have h9' := h9
  obtain ⟨-, hL3, hs15, hsum, -⟩ := h9
  have h9rk : rk ↥(commSub ⊤ (lBar V₀ V hV L)) = 9 :=
    s16c167_rk_natSum3 (s16c167_natSum3_of_sumOfNat hsum)
  by_cases hcase : ∃ t ∈ E, (lBar V₀ V hV L).map (MulAut.conj t).toMonoidHom =
      (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom
  · obtain ⟨t, htE, htL⟩ := hcase
    exact s1611e3_nine_abs_five_le_rkIdx_of_swap hg h9rk hE hab htE htL
  · have hstab : ∀ x ∈ E, x ∈ Subgroup.normalizer
        (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
      intro x hxE
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      rcases hg.conj x (hE hxE) with hh | hh
      · exact hh
      · exact absurd hh fun hhh => hcase ⟨x, hxE, hhh⟩
    have hL : IsPSL 3 2 1 ↥(lBar V₀ V hV L) := s16c167_isPSL_of_isL3 hL3
    obtain ⟨hind, hsup⟩ :=
      s16t_case9_directSum D h.h1217 hV hc.setting.hyp151 (s1611e3_nine_v1Sub h9') hc.ne_bot
    have hrk0 : rk ↥(wTil V₀ V hV L) = 9 :=
      s16c167_rk_natSum3 (s16c167_natSum3_of_sumOfNat hsum)
    have hrktop : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 18 :=
      s16t_case9_rk_top D h.h1217 hV hc.setting.hyp151 (s1611e3_nine_v1Sub h9') hc.ne_bot
        hs15 hsum
    have hn2 : (conjSubs (Mbar D.M V₀ V hV) (wTil V₀ V hV L)).ncard = 2 :=
      s16n9b_case9_conjSubs_ncard hV hind hsup hrk0 hrktop
    have hcls : Set.ncard {Y : Subgroup (MulAut (Vtil V₀ V hV)) |
        ∃ φ ∈ Mbar D.M V₀ V hV,
          Y = (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom} = 2 := by
      unfold s15 at hs15
      exact hs15
    have hsum' : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) (lBar V₀ V hV L)
        (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)) ⊥ 3 := hsum
    have habs := s16c167_cfg9_abstract hW hL hsum' hcls hn2 hind hsup
    have hcard4 : ∀ E' : Subgroup (MulAut (Vtil V₀ V hV)), E' ≤ Mbar D.M V₀ V hV →
        IsElemAbelian2 E' →
        E' ≤ Subgroup.normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) →
        E' ≤ Subgroup.normalizer (((lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom :
          Subgroup (MulAut (Vtil V₀ V hV))) : Set (MulAut (Vtil V₀ V hV))) →
        (∀ x ∈ E', ∀ a ∈ lBar V₀ V hV L, x * a = a * x) → Nat.card ↥E' ≤ 4 :=
      fun E' hE'M hE'ab hE'NL hE'NB hcent =>
        s1611e3_nine_card_le_four_of_acttriv h hc h9' hg hE'M hE'ab hE'NL hE'NB hcent
    have hcard4sym : ∀ E' : Subgroup (MulAut (Vtil V₀ V hV)), E' ≤ Mbar D.M V₀ V hV →
        IsElemAbelian2 E' →
        E' ≤ Subgroup.normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) →
        (∀ x ∈ E', ∀ a ∈ (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom,
          x * a = a * x) → Nat.card ↥E' ≤ 4 :=
      fun E' hE'M hE'ab hE'NL hcent =>
        s1611e3_nine_card_le_four_of_acttriv_sym h hc h9' hg hE'M hE'ab hE'NL hcent
    have hloc0 : ∀ t ∈ Mbar D.M V₀ V hV, t * t = 1 →
        (commSub ⊤ (lBar V₀ V hV L)).map t.toMonoidHom = commSub ⊤ (lBar V₀ V hV L) →
        commSub ⊤ (lBar V₀ V hV L) ≤ fixV (Subgroup.zpowers t) ∨
          3 ≤ E3.mQuot (commSub ⊤ (lBar V₀ V hV L))
                (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (Subgroup.zpowers t)) :=
      fun t htX ht2 hstab0 =>
        habs.2.2.1 t htX ht2 (commSub ⊤ (lBar V₀ V hV L))
          ⟨1, (Mbar D.M V₀ V hV).one_mem, by ext y; simp⟩ hstab0
    have hloc1 : ∀ t ∈ Mbar D.M V₀ V hV, t * t = 1 →
        ((commSub ⊤ (lBar V₀ V hV L)).map g.toMonoidHom).map t.toMonoidHom =
          (commSub ⊤ (lBar V₀ V hV L)).map g.toMonoidHom →
        (commSub ⊤ (lBar V₀ V hV L)).map g.toMonoidHom ≤ fixV (Subgroup.zpowers t) ∨
          3 ≤ E3.mQuot ((commSub ⊤ (lBar V₀ V hV L)).map g.toMonoidHom)
                (((commSub ⊤ (lBar V₀ V hV L)).map g.toMonoidHom) ⊓
                  fixV (Subgroup.zpowers t)) :=
      fun t htX ht2 hstab1 =>
        habs.2.2.1 t htX ht2 ((commSub ⊤ (lBar V₀ V hV L)).map g.toMonoidHom)
          ⟨g, hg.mem, rfl⟩ hstab1
    exact s1611e3_nine_abs_five_le_rkIdx_of_stab hg hW hcard4 hcard4sym hloc0 hloc1
      hE hab hstab h3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
