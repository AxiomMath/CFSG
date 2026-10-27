module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42CLay
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma43Setup
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec4Defs
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.GF2Type.Smith1979.CaseIIExclL52

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G] [Finite G]

namespace Setup14

variable {b : G} {J B : Subgroup G} (S : Setup14 5 b J B)
include S

theorem solvable_C0 (hX : Odd (Nat.card (Opp 3 (Cen b)))) :
    Group.IsSolvable ↥(Cen b ⊓ CenS J) := by
  set Z : Subgroup G := Cen b ⊓ CenS J with hZ
  set X : Subgroup G := Opp 3 (Cen b) with hXdef
  have hXZ : X ≤ Z := S.X_le_C0 hX
  set X' : Subgroup ↥Z := X.subgroupOf Z with hX'
  have hnorm : X'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hX', Subgroup.mem_subgroupOf] at hn ⊢
    exact L14.Opp_conj_mem g.2.1 hn
  have hsolv : Group.IsSolvable ↥X' := by
    have hodd : Odd (Nat.card ↥X') := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXZ).toEquiv]
      exact hX
    exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hquot : ∀ q q' : ↥Z ⧸ X', q * q' = q' * q := by
    have hgen : ∀ q : ↥Z ⧸ X', ∃ i : ℤ, q = ((QuotientGroup.mk (⟨b, S.b_mem_C0⟩ : ↥Z) :
        ↥Z ⧸ X')) ^ i := by
      intro q
      obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨i, x, hx, hzx⟩ := S.C0_decomp (z : G) z.2
      refine ⟨i, ?_⟩
      have hxZ : x ∈ Z := hXZ hx
      have h1 : z = (⟨b, S.b_mem_C0⟩ : ↥Z) ^ i * (⟨x, hxZ⟩ : ↥Z) := by
        ext; simpa using hzx
      have h2 : ((⟨x, hxZ⟩ : ↥Z) : ↥Z ⧸ X') = 1 := by
        rw [QuotientGroup.eq_one_iff]
        exact (Subgroup.mem_subgroupOf.mpr hx)
      rw [h1, QuotientGroup.mk_mul, h2, mul_one, QuotientGroup.mk_zpow]
    intro q q'
    obtain ⟨i, rfl⟩ := hgen q
    obtain ⟨j, rfl⟩ := hgen q'
    exact (Commute.zpow_zpow_self _ i j).eq
  haveI : Group.IsSolvable (↥Z ⧸ X') := isSolvable_of_comm hquot
  exact solvable_of_ker_le_range X'.subtype (QuotientGroup.mk' X')
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

end Setup14

theorem lay_eq_lay_J_inf {b : G} {J B : Subgroup G} {b₁ b₂ : G}
    (h4 : FF79Sec4 b J B b₁ b₂) (hJ5 : FF79_JL5) (h41 : FF79_4_1) {Y : Subgroup G}
    (hY : Y ≤ Cen b) : Lay Y = Lay (J ⊓ Y) := by
  obtain ⟨e⟩ := CFSG.GF2Type.Smith1979.Case2.nonempty_mulEquiv_gl_of_psl_two
    (hJ5 G b J h4.hyp)
  have S := setup_of_sec4 h4 e
  exact lay_eq_lay_inf_of_normal S.J_le_cen S.hJn hY
    (perfect_le_of_cen_solvable S.J_le_cen S.hJn e (S.solvable_C0 (h41 G b J B b₁ b₂ h4)))

end CFSG.RankThree.PartTwo.Sec21.FF79
