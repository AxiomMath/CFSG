module

public import CFSG.RankThree.GF2n.Stroth80.Sec310Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec310M1

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem card_eq_of_sectionAct {R V Z : Subgroup G} {K : Type} [Field K] [Finite K]
    {ι : Type} [Fintype ι] [DecidableEq ι] {φ : ↥R →* GL ι K} (hZV : Z ≤ V)
    (hsec : SectionAct K R V Z φ (fun g => (g : Matrix ι ι K))) :
    Nat.card V = Nat.card Z * Nat.card K ^ Fintype.card ι := by
  obtain ⟨-, hnorm, ψ, -⟩ := hsec
  haveI := hnorm
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf V)
  have h2 : Nat.card (↥V ⧸ Z.subgroupOf V) = Nat.card K ^ Fintype.card ι := by
    rw [Nat.card_congr ψ.toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ι → K) ≃ _), Nat.card_fun,
      Nat.card_eq_fintype_card (α := ι)]
  have h3 : Nat.card (Z.subgroupOf V) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv
  rw [h1, h2, h3, mul_comm]

theorem sympRep_two_of_not_le_QB (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hnot : ¬ Vt M (LB M Q B) B Z t ≤ QB B) (hrep : SympRep 1 hc t) :
    SympRep 2 hc t := by
  obtain ⟨K, _, _, hK, m, hm, φ, hr, hk, hsec⟩ := hrep
  refine ⟨K, inferInstance, inferInstance, hK, m, ?_, φ, hr, hk, hsec⟩
  by_contra hlt
  have hm1 : m = 1 := by omega
  subst hm1
  apply hnot
  have hcardV := card_eq_of_sectionAct (sec39_Z_le_Vt (M := M) (L := LB M Q B) (B := B) (t := t))
    hsec
  have hV3 : Nat.card (Vt M (LB M Q B) B Z t) = Nat.card Z ^ 3 := by
    rw [hcardV, hK]
    simp only [Fintype.card_sum, Fintype.card_fin]
    ring
  exact (hc.Vt_le_inf_QB_of_card_eq h34 hs hV3).trans inf_le_right

theorem stroth310SympBranch_of_steps (h34 : Stroth34Statement)
    (hForm : Stroth310SympFormStatement) (hCl : Stroth310ClassifyStatement) :
    Stroth310SympBranchStatement := by
  intro G _ _ M Q Z B hc n t hs hR hV
  exact hCl G M Q Z B hc n t hs hR hV
    (sympRep_two_of_not_le_QB h34 hc hs hV (hForm G M Q Z B hc n t hs hR hV))

theorem stroth310_of_branches (hSL : Stroth310SLBranchStatement)
    (hSp : Stroth310SympBranchStatement) : Stroth310Statement := by
  intro G _ _ M Q Z B hc n hw hn hno hgen t ht htQ
  have hs : Sec5Hyp hc n t := ⟨hw, hn, hno, hgen, ht, htQ⟩
  by_cases hR : Rt M (LB M Q B) t = LB M Q B
  · exact Or.inl hR
  · right
    by_cases hV : Vt M (LB M Q B) B Z t ≤ QB B
    · obtain ⟨K, _, _, hK, m, hm, hrep⟩ := hSL G M Q Z B hc n t hs hR hV
      exact ⟨K, inferInstance, inferInstance, hK, Or.inl ⟨m, hm, hrep⟩⟩
    · rcases hSp G M Q Z B hc n t hs hR hV with
        ⟨K, _, _, hK, m, hm, hrep⟩ | ⟨K, _, _, hK, hO⟩ | ⟨K, _, _, hK, hrep⟩
      · exact ⟨K, inferInstance, inferInstance, hK, Or.inr (Or.inl ⟨m, by omega, hrep⟩)⟩
      · rcases hO with ⟨m, hm, hrep⟩ | ⟨m, b, c, hm, hirr, hrep⟩
        · exact ⟨K, inferInstance, inferInstance, hK,
            Or.inr (Or.inr (Or.inl ⟨m, by omega, hrep⟩))⟩
        · exact ⟨K, inferInstance, inferInstance, hK,
            Or.inr (Or.inr (Or.inr ⟨m, b, c, hm, hirr, hrep⟩))⟩
      · exact ⟨K, inferInstance, inferInstance, hK,
          Or.inr (Or.inr (Or.inl ⟨2, le_rfl, hrep⟩))⟩

theorem stroth310_of_steps (h34 : Stroth34Statement) (hSL : Stroth310SLBranchStatement)
    (hForm : Stroth310SympFormStatement) (hCl : Stroth310ClassifyStatement) :
    Stroth310Statement :=
  stroth310_of_branches hSL (stroth310SympBranch_of_steps h34 hForm hCl)

end CFSG.RankThree.GF2n.Stroth80
