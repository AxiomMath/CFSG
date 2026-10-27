module

public import CFSG.RankThree.GF2n.Smith81.TiFusion
public import CFSG.RankThree.GF2n.Smith81.LinStmt
public import CFSG.RankThree.GF2n.Smith81.Sec2Defs

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G] [Finite G] {M Q Z : Subgroup G}

theorem conjClassSet_inter_cosetSet_eq_of_inZClass {z x : G} (hz : z ∈ Z) (hz1 : z ≠ 1)
    (hxc : IsConj z x) (h4 : ∀ z' ∈ Z, InZClass Z (x * z') → z' = 1) :
    conjClassSet z ∩ cosetSet x Z = {x} := by
  ext y
  refine ⟨fun ⟨hyc, hyx⟩ => ?_, fun hy => ?_⟩
  · obtain ⟨z', hz', rfl⟩ := hyx
    obtain ⟨c, hc⟩ := isConj_iff.mp hyc
    have : z' = 1 := h4 z' hz' ⟨c, z, hz, hz1, hc.symm⟩
    simp [this]
  · rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨hxc, 1, Z.one_mem, mul_one y⟩

theorem exists_linSetup_of_typeE6 (h22 : Lin22Statement) {M Q Z B : Subgroup G} {n : ℕ}
    (hc : Ctx M Q Z B) (hn : TypeE6 M Q Z B n) :
    ∃ V₁ V₂ : Subgroup G, LinSetup M Q Z B n V₁ V₂ ∧ 2 ≤ n := by
  rcases hn with ⟨hnTI, hE6⟩ | ⟨rfl, hD2, hno⟩
  · obtain ⟨V₁, V₂, hS⟩ := hE6.exists_linSetup
    exact ⟨V₁, V₂, hS, CaseE6.two_le hc hnTI hE6⟩
  · obtain ⟨V₁, V₂, hS⟩ := h22 G M Q Z B hc hD2 hno
    exact ⟨V₁, V₂, hS, le_rfl⟩

theorem isRootInvolutionSet_of_lin213Prop (H : StrothHyp M Q Z) {z : G} (hz : z ∈ Z)
    (hz1 : z ≠ 1) (h : Lin213Prop M Z) :
    Timmesfeld.IsRootInvolutionSet (conjClassSet z ∩ (M : Set G)) := by
  have hcl : ∀ {d : G}, IsConj z d → InZClass Z d := fun {d} hd => by
    obtain ⟨c, hc⟩ := isConj_iff.mp hd
    exact ⟨c, z, hz, hz1, hc.symm⟩
  have hcl' : ∀ {d : G}, InZClass Z d → IsConj z d := fun {d} hd => by
    obtain ⟨g, u, hu, hu1, e⟩ := hd
    obtain ⟨m, -, hm⟩ := Z_isConj H hz hz1 hu hu1
    exact isConj_iff.mpr ⟨g * m, by rw [e, ← hm]; group⟩
  refine ⟨fun d hdD => ?_, fun d hdD e heD => ?_, fun d hdD e heD ho => ?_⟩
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq]; exact mul_self_eq_one_of_isConj_Z H hz hdD.1)
      (ne_one_of_isConj_Z hz1 hdD.1)
  · exact (h d e hdD.2 heD.2 (hcl hdD.1) (hcl heD.1)).1
  · exact ⟨hcl' ((h d e hdD.2 heD.2 (hcl hdD.1) (hcl heD.1)).2 ho),
      pow_mem (M.mul_mem hdD.2 heD.2) 2⟩

end CFSG.RankThree.GF2n.Smith81
