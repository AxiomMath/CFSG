module

public import CFSG.RankThree.GF2n.Stroth80.Sec103
public import CFSG.RankThree.GF2n.Stroth80.Sec103AAdm
public import CFSG.RankThree.GF2n.Stroth80.Sec103BPoint
public import CFSG.RankThree.GF2n.Stroth80.Sec103BRoot
public import CFSG.RankThree.GF2n.Stroth80.Sec103BRoute
public import CFSG.RankThree.GF2n.Stroth80.Sec10Seven

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def Stroth103CaseB2Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G)
    (Y : Subgroup G), Sec10Hyp hc n → Good101 M Q Z B t → Sit M Q Z Y t → ¬ CaseA Q Z t →
      SLMNat hc t 2 → Q ⊓ QB Y ≤ Vt M (LB M Q B) B Z t

theorem stroth_10_3_caseB2 (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    (hA : Stroth103CaseAStatement) (hE2 : Stroth107M2Statement) :
    Stroth103CaseB2Statement := by
  intro G _ _ M Q Z B hc n t Y H ht hs hB h2
  by_contra hbad
  obtain ⟨α, hα, hαV⟩ := SetLike.not_le_iff_exists.mp hbad
  have hAB := ht.inf_QB_le_QB_of_not_caseA h34 hspread H hs hB h2
  obtain ⟨c, hcQ, hcα, hcB, hcW⟩ :=
    ht.exists_mem_centralizer_not_mem_Wt H hα.1 hαV
  have hαc : α ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G) :=
    ⟨hα, Subgroup.mem_centralizer_singleton_iff.mpr hcα.symm⟩
  have hA' := ht.caseA_conj h34 hspread H hs hAB hcQ hcB hcW hαc hαV
  obtain ⟨a, ha, haB, u, hu, huB, y, hy, hyt, hconj⟩ :=
    ht.exists_conj_eq_mul_ne h34 hspread H hs h2 hAB hcQ hcB hcW hA' hαc hαV
  obtain ⟨hw, hws, hw2, hwA⟩ :=
    ht.caseA_of_conj_eq_mul h34 hspread H hs h2 hcQ hcB hcW ha haB huB hy hyt hconj
  exact hE2 G M Q Z B hc n _ H
    (Good101.good103_of_le_Vt h34 hspread H hw hws (hA G M Q Z B hc n _ _ H hw hws hwA)) hw2

theorem stroth103M2Statement_of_caseB2 (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) (hB2 : Stroth103CaseB2Statement) :
    Stroth103M2Statement := by
  intro G _ _ M Q Z B hc n s H hs hs2 hno
  obtain ⟨Y, hY⟩ := hs.exists_sit hc
  have h103 : Q ⊓ QB Y ≤ Vt M (LB M Q B) B Z s → False := fun hle =>
    hno 1 Q.one_mem (by rw [mul_one]; exact Good101.good103_of_le_Vt h34 hspread H hs hY hle)
  by_cases hcA : CaseA Q Z s
  · exact ⟨s, Y, hs, hY, hcA, h103⟩
  · exact (h103 (hB2 G M Q Z B hc n s Y H hs hY hcA hs2)).elim

theorem stroth_10_3a_of_caseB2 (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    (hA : Stroth103CaseAStatement) (hE2 : Stroth107M2Statement) : Stroth103aStatement :=
  stroth_10_3a_of_cases hA
    (stroth103M2Statement_of_caseB2 h34 hspread (stroth_10_3_caseB2 h34 hspread hA hE2))

end CFSG.RankThree.GF2n.Stroth80
