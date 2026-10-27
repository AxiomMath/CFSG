module

public import CFSG.RankThree.PartTwo.Sec12.Item125DiagSU
import CFSG.RankThree.PartTwo.Sec12.Item128StepsProofCaseA

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Item125BarThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec12StdBar G A c L →
    (Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22) →
    ∀ E : Subgroup G, Late.IsE27 E → E ≤ lcBar c L → c ∈ E →
      Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 3 →
      Nat.card (E ⊓ L : Subgroup G) = 3 →
      Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)

open Item128StepsProof in
theorem item125BarThree_of_item45
    (h45 : Sec4.Item4_5) (hKT : KS125TypeCInvol) : Item125BarThree := by
  intro G _ _ A c L h hty E hE hEL hcE hB3 hEL3
  have hL := h.mem_thetaComponentsAt
  have hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3 := by
    rcases hty with hSL | hA6 | hA7 | hM22
    · exact card_center_eq_three_of_isSLThreePi hSL
    · exact hA6.1
    · exact hA7.1
    · exact hM22.1
  have hcases : (∀ x : L ⧸ aschbacherSolvableCore 3 L,
      x ^ 3 ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) → x ^ 3 = 1) ∨
      ∃ q : ℕ, Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) q ∧
        (q % 9 = 1 ∨ q % 9 = 8) := by
    rcases hty with ⟨q, hq⟩ | hTC
    · by_cases h9 : q % 9 = 1 ∨ q % 9 = 8
      · exact Or.inr ⟨q, hq, h9⟩
      · exact Or.inl fun x hx => pow_three_eq_one_of_not_modNine hq h9 hx
    · refine Or.inl fun x hx => KFacts.pow_three_eq_one_of_isTripleCover hTC x ⟨2, ?_⟩
      have h3 : (⟨x ^ 3, hx⟩ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) ^ 3 = 1 := by
        have h0 := pow_card_eq_one' (x := (⟨x ^ 3, hx⟩ :
          Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)))
        rwa [hZ] at h0
      have h4 := congrArg Subtype.val h3
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at h4
      rw [← pow_mul] at h4
      exact h4
  by_cases hexp : ∀ e ∈ E, ∃ l ∈ L, ∃ z ∈ Sec4.thetaQuotCentralizer L,
      e = l * z ∧ l ^ 3 = 1 ∧ l * z = z * l
  · exact Item125DiagSU.item125Diag_of_item45 h45 G A c L h hty E hE hEL hcE hB3 hEL3 hexp
  · push Not at hexp
    obtain ⟨e, heE, hne⟩ := hexp
    obtain ⟨l₀, hl₀, z₀, hz₀, hlz⟩ := exists_mul_of_mem_lcBar hL (hEL heE)
    have hx3 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨l₀, hl₀⟩ ^ 3 ≠ 1 := by
      intro h3
      obtain ⟨l, hl, z, hz, hlz', hl3, hlzc⟩ :=
        exists_decomp_of_mk_pow hL (hEL heE) (hE.1.2 e heE) hl₀ hz₀ hlz h3
      exact hne l hl z hz hlz' hl3 hlzc
    rcases hcases with hcube | ⟨q, hq, -⟩
    · exact absurd (mk_pow_three_eq_one_of_cube hL hcube (hEL heE) (hE.1.2 e heE) l₀ hl₀ hz₀
        hlz) hx3
    · exact (false_of_card_inf_L_eq_three_of_pow_ne hKT h.partTwoF_eq hL h.mem_L h.ne_one
        ⟨q, hq⟩ hE hEL hcE hB3 hEL3 heE hl₀ hz₀ hlz hx3).elim

theorem item125BarThree_of_item45'
    (h45 : Sec4.Item4_5) : Item125BarThree :=
  item125BarThree_of_item45 h45 Item125DiagSU.ks125TypeCInvol_closed

end CFSG.RankThree.PartTwo.Sec12
