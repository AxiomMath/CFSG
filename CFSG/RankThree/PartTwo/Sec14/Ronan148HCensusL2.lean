module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148HCensusInnerThree
public import CFSG.RankThree.PartTwo.Sec14.Ronan148HCensusOrd
public import CFSG.Models.PGLSimple
public import CFSG.RankThree.PartTwo.Sec13.Item13Res5ProofCenter
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3InvolveModels
public import CFSG.Milestones.ASVolI.A3OddFacts

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

section Row

set_option linter.unusedSectionVars false


variable {X : Type} [Group X] [Finite X] {P L Q : Subgroup X}

theorem OLCfg.false_of_orderOf_nine (hcfg : OLCfg P L Q) (hZL : Subgroup.center L = ⊥) (x : L)
    (hx : orderOf x = 9) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 ((Subgroup.zpowers x).map L.subtype) := by
    apply IsPGroup.map
    apply IsPGroup.of_card (n := 2)
    rw [Nat.card_zpowers, hx]
    norm_num
  obtain ⟨h3, -⟩ := commutator_mem_center_of_isPGroup hcfg.triple hp
  have hx3 : (x : X) ^ 3 ∈ Subgroup.center X := h3 _ ⟨x, Subgroup.mem_zpowers x, rfl⟩
  have hxL : x ^ 3 ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, SubgroupClass.coe_pow]
    exact (Subgroup.mem_center_iff.mp hx3) g
  rw [hZL, Subgroup.mem_bot] at hxL
  have := orderOf_dvd_of_pow_eq_one hxL
  rw [hx] at this
  norm_num at this

theorem OLCfg.false_of_nonabelian_three (hcfg : OLCfg P L Q) (hZL : Subgroup.center L = ⊥)
    {a b : L} (hT : IsPGroup 3 (Subgroup.closure ({a, b} : Set L))) (hab : a * b ≠ b * a) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 ((Subgroup.closure ({a, b} : Set L)).map L.subtype) := hT.map _
  obtain ⟨-, hc⟩ := commutator_mem_center_of_isPGroup hcfg.triple hp
  have hc' := hc _ ⟨a, Subgroup.subset_closure (Or.inl rfl), rfl⟩ _
    ⟨b, Subgroup.subset_closure (Or.inr rfl), rfl⟩
  have hL : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_center_iff.mp hc') g
  rw [hZL, Subgroup.mem_bot] at hL
  apply hab
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [hL, one_mul]


theorem innerThree_projSL_two (p : ℕ) [Fact p.Prime] :
    InnerThree (projSL 2 (GaloisField p 1)) := by
  have hp : p.Prime := Fact.out
  refine InnerThree.of_mulEquiv (Sec4.projSLEquivPSLn 2 (GaloisField p 1)) fun σ hσ => ?_
  have hK : Nat.card (GaloisField p 1) = p ^ 1 := GaloisField.card p 1 one_ne_zero
  have hodd : Odd (orderOf σ) := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hσ) with h | h
    · rw [h]; exact odd_one
    · rw [h]; decide
  exact CFSG.ASVolI.burnsideA315x_psl2_odd_inner hp hK (Or.inl rfl) σ hodd

theorem olRow_one_inner (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (h9 : ¬ 9 ∣ Nat.card (projSL 2 (GaloisField p 1))) :
    OLRow (fun T _ => Nonempty (T ≃* projSL 2 (GaloisField p 1))) := by
  have hK : Nat.card (GaloisField p 1) = p := by rw [GaloisField.card p 1 one_ne_zero, pow_one]
  haveI : IsSimpleGroup (projSL 2 (GaloisField p 1)) :=
    CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (GaloisField p 1) le_rfl
      (Or.inr (by rw [hK]; omega)) (Or.inr (by rw [hK]; omega))
  have : Finite (projSL 2 (GaloisField p 1)) := inferInstance
  exact olRow_of_innerThree _ (innerThree_projSL_two p) fun B V =>
    not_innerCfg_of_not_dvd h9 B V

theorem olRow_one (p e : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e) :
    OLRow (fun T _ => Nonempty (T ≃* projSL 2 (GaloisField p e))) := by
  intro X _ _ P L Q hcfg ⟨φ⟩
  have hp : p.Prime := Fact.out
  have hK : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  have hLN : Nat.card (projSL 2 (GaloisField p e)) ∣ 1382446517760 := by
    rw [← Nat.card_congr φ.toEquiv, ← card_X hcfg.triple]
    exact Subgroup.card_subgroup_dvd_card L
  have hc := Sec11.KSListsProof.card_projSL_two_mul (GaloisField p e)
  rw [hK] at hc
  have hodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
  have hg : Nat.gcd 2 (p ^ e - 1) = 2 := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk, Nat.add_sub_cancel]
    exact Nat.gcd_eq_left (dvd_mul_right 2 k)
  rw [hg] at hc
  have hcontra : p ^ e * ((p ^ e) ^ 2 - 1) ∣ 1382446517760 * 2 := by
    rw [← hc]
    exact Nat.mul_dvd_mul_right hLN 2
  have hq : p ^ e ∣ Nat.card (projSL 2 (GaloisField p e)) := by
    have h' : p ^ e ∣ Nat.card (projSL 2 (GaloisField p e)) * 2 := by
      rw [hc]; exact dvd_mul_right _ _
    exact (coprime_pow_of_dvd hp (dvd_refl 2) (fun h =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))).dvd_of_dvd_mul_right h'
  have hqN := hq.trans hLN
  have hpN : p ∣ 1382446517760 := (dvd_pow_self p (by omega)).trans hqN
  have hqL := hcfg.isQuasisimple
  rcases prime_of_dvd_N hp hpN with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hp2 rfl
  ·
    have he5 := three_pow_dvd_N hqN
    interval_cases e
    · exact Sec13.Res5Proof.false_of_projSL_two_small (Or.inr (by rw [hK]; norm_num)) hqL φ
    · obtain ⟨ψ⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_alternating_six_of_statedProj
        (by rw [hK]; norm_num) (CFSG.PGLModel.projSLEquivStatedProj 2 (GaloisField 3 2))
      exact olRow_alt_six X P L Q hcfg ⟨φ.trans ψ⟩
    all_goals norm_num at hcontra
  ·
    rcases pow_dvd_N hp (by norm_num) hqN with h1 | ⟨h7, -⟩
    · obtain rfl : e = 1 := by omega
      norm_num at hc
      exact olRow_one_inner 5 le_rfl (by omega) X P L Q hcfg ⟨φ⟩
    · norm_num at h7
  ·
    rcases pow_dvd_N hp (by norm_num) hqN with h1 | ⟨-, h3⟩
    · obtain rfl : e = 1 := by omega
      norm_num at hc
      exact olRow_one_inner 7 (by norm_num) (by omega) X P L Q hcfg ⟨φ⟩
    · interval_cases e
      · norm_num at hc
        exact olRow_one_inner 7 (by norm_num) (by omega) X P L Q hcfg ⟨φ⟩
      all_goals norm_num at hcontra
  ·
    rcases pow_dvd_N hp (by norm_num) hqN with h1 | ⟨h7, -⟩
    · obtain rfl : e = 1 := by omega
      norm_num at hc
      exact olRow_one_inner 11 (by norm_num) (by omega) X P L Q hcfg ⟨φ⟩
    · norm_num at h7
  ·
    rcases pow_dvd_N hp (by norm_num) hqN with h1 | ⟨h7, -⟩
    · obtain rfl : e = 1 := by omega
      have hK19 : Nat.card (GaloisField 19 1) = 19 := by rw [hK]; norm_num
      haveI : IsSimpleGroup (projSL 2 (GaloisField 19 1)) :=
        CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (GaloisField 19 1) le_rfl
          (Or.inr (by rw [hK19]; norm_num)) (Or.inr (by rw [hK19]; norm_num))
      have hZL := Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hqL φ
      obtain ⟨g, hg9⟩ := CFSG.AGLEmbedding.exists_orderOf_nine_psl_nineteen hK19
      set ψ := (CFSG.PGLModel.projSLEquivStatedProj 2 (GaloisField 19 1)).symm
      exact hcfg.false_of_orderOf_nine hZL (φ.symm (ψ g))
        (by rw [MulEquiv.orderOf_eq, MulEquiv.orderOf_eq, hg9])
    · norm_num at h7
  ·
    rcases pow_dvd_N hp (by norm_num) hqN with h1 | ⟨h7, -⟩
    · obtain rfl : e = 1 := by omega
      norm_num at hc
      exact olRow_one_inner 31 (by norm_num) (by omega) X P L Q hcfg ⟨φ⟩
    · norm_num at h7

end Row

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
