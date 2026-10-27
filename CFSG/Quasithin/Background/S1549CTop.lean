module

public import CFSG.Quasithin.Background.S1549CIn
public import CFSG.Quasithin.Background.S1549CN3
public import CFSG.Quasithin.Background.S1549CM
public import CFSG.Quasithin.Background.S1549CD2
public import CFSG.Quasithin.Background.S1549CB
public import CFSG.Quasithin.Background.S1549CC
public import CFSG.Quasithin.Background.S1549COff
public import CFSG.Quasithin.Background.S1549CSup

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
  CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

namespace S1549C

theorem stage15349Core_of_named_inputs (h11 : StageLemma14111) (h113 : StageLemma14113)
    (i1 : Input49I) (i2 : Input49K) (i3 : Input49E) (i4 : Input49L) (i5 : Input49S)
    (i6 : Input49L3) (i7 : Input49Ln) (i8 : Input49A6) : Stage15349Core := by
  intro G _ _ T Mc M V₁ V₂ t c r45 r46 r47 hF
  have h := c.hyp
  by_cases h1 : Case157One T Mc M
  · exact threePrime_of_case_one h113 h h1
  · exfalso
    have h2 : Case157Two T Mc M := (h.lemma_15_3_7_cases h113).resolve_left h1
    let cx : Ctx49 G T Mc M V₁ V₂ t :=
      ⟨c, r45, r46, r47, h2, fun H hH hY => hF H hH (fun _ => hY)⟩
    obtain ⟨H, hH, hmin⟩ := exists_minimal_adm h11 h
    have hbB := claim_b h11 h113 h hH
    have hc := claim_c h113 cx hH
    have hd := claim_d h11 h113 cx hH hc
    have hdMc := claim_d h11 h113 cx (adm_mc h11 h) (claim_c h113 cx (adm_mc h11 h))
    have h98 := claim_e h11 h113 cx hH hdMc
    have hbase : InspBase cx H := ⟨hH, hmin, hbB, hc, hd, h98⟩
    obtain ⟨γ, γ', g, s, hpos, hle⟩ := exists_good_setup h113 cx hH h98 hc
    obtain ⟨c0, hc0H, B, od⟩ := exists_offData h11 h113 cx hbase s hpos hle
    obtain ⟨⟨L, hL⟩, hall⟩ := i1 G T Mc M V₁ V₂ t cx H hbase _ B od
    have hLY := hall L hL
    have hLH : L ≤ H := (le_of_mem_cComp hL).trans (preStar_le _ _)
    have hHL := eq_sup_of_minimal h11 h113 h hH hmin hbB hLH (ne_bot_of_mem_cComp hL)
      (perfect_of_mem_cComp hL) hLY
    have hm := claim_m h11 h113 cx hH hc
    have lctx : LCtx hbase od L := ⟨hL, hLY, hHL⟩
    obtain ⟨A, hA1, hA2⟩ := claim_n h11 h113 cx hbase s hpos hle hc0H od hL hHL hm
    have hk := i2 G T Mc M V₁ V₂ t cx H hbase _ B od L lctx
    have hE := i3 G T Mc M V₁ V₂ t cx H hbase _ B od L lctx hk
    have hl := i4 G T Mc M V₁ V₂ t cx H hbase _ B od L lctx hk hE
    have ec : EndCtx hbase od L := ⟨lctx, hk, hl⟩
    rcases hl.lie with ⟨n, hn3, hn5, hiso⟩ | hA6 | hhat | hA7 | hG2
    · have hn : n = 3 ∨ n = 4 ∨ n = 5 := by omega
      rcases hn with rfl | rfl | rfl
      · exact i6 G T Mc M V₁ V₂ t cx H hbase _ B od L ec hiso ⟨A, hA1, hA2⟩
      · exact i7 G T Mc M V₁ V₂ t cx H hbase _ B od L ec 4 (Or.inl rfl) hiso
      · exact i7 G T Mc M V₁ V₂ t cx H hbase _ B od L ec 5 (Or.inr rfl) hiso
    · exact i8 G T Mc M V₁ V₂ t cx H hbase _ B od L ec hA6 ⟨A, hA1, hA2⟩
    · exact i5 G T Mc M V₁ V₂ t cx H hbase _ B od L ec (Or.inl hhat) ⟨A, hA1⟩
    · exact i5 G T Mc M V₁ V₂ t cx H hbase _ B od L ec (Or.inr (Or.inl hA7)) ⟨A, hA1⟩
    · exact i5 G T Mc M V₁ V₂ t cx H hbase _ B od L ec (Or.inr (Or.inr hG2)) ⟨A, hA1⟩

end S1549C

end CFSG.Quasithin
