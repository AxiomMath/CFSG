module

public import CFSG.RankThree.PartTwo.Sec12.Hering129HC9
public import CFSG.RankThree.PartTwo.Sec12.Item128StepsProofCaseA
import CFSG.RankThree.PartTwo.Sec6.Item612Local
public import CFSG.RankThree.PartTwo.Sec12.Hering129Defs
public import CFSG.RankThree.PartTwo.Sec12.Item125DiagSU

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Item128StepsProof Item125BarTC

@[expose] def Item125BarNot9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec12StdBar G A c L →
    ∀ q : ℕ, Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) q → ¬ PiModNine q →
    ∀ E : Subgroup G, Late.IsE27 E → E ≤ lcBar c L → c ∈ E →
      Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)


theorem item125BarNot9_of
    (h45 : Sec4.Item4_5) (hK2 : KFacts.KS12NormalizerMoves)
    (hK9 : KFacts.KS12OrderNine) (hG1 : Gap125NonCentralBar) : Item125BarNot9 := by
  intro G _ _ A c L h q hq h9 E hE hEL hcE
  have hty : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22 :=
    Or.inl ⟨q, hq⟩
  have hL := h.mem_thetaComponentsAt
  have hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3 :=
    card_center_eq_three_of_isSLThreePi ⟨q, hq⟩
  have hperf : commutator (L ⧸ aschbacherSolvableCore 3 L) = ⊤ := by
    have h1 := (isQuasisimple_thetaQuot_of_mem hL).1
    rwa [Group.isPerfect_def] at h1
  have hev := KFacts.two_dvd_card_of_item122_type hty
  have hm3 : ∀ S : Subgroup (L ⧸ aschbacherSolvableCore 3 L), IsMulCommutative S →
      (∀ x ∈ S, x ^ 3 = 1) → Nat.card S ≤ 9 := fun S hS hS3 =>
    card_le_nine_of_isSLThreePi ⟨q, hq⟩ S
      (fun x hx y hy => congrArg Subtype.val (hS.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) hS3
  have hcube : ∀ x : L ⧸ aschbacherSolvableCore 3 L,
      x ^ 3 ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) → x ^ 3 = 1 :=
    fun x hx => pow_three_eq_one_of_not_modNine hq h9 hx
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hcC : c ∈ E ⊓ Sec4.thetaQuotCentralizer L :=
    ⟨hcE, mem_thetaQuotCentralizer_of_central h.mem_L hLc⟩
  have hcEL : c ∈ E ⊓ L := ⟨hcE, h.mem_L⟩
  have hdvd : ∀ S : Subgroup G, S ≤ E → Nat.card S ∣ 3 ^ 3 := fun S hS => by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE.2]
    exact Subgroup.card_dvd_of_le hS
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (hdvd _ inf_le_left)
  interval_cases k
  · rw [pow_zero, Subgroup.card_eq_one] at hk
    exact absurd (hk ▸ hcC) (by simpa using h.ne_one)
  ·
    have hB3 : Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 3 := by rw [hk, pow_one]
    obtain ⟨j, hj3, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (hdvd (E ⊓ L) inf_le_left)
    interval_cases j
    · rw [pow_zero, Subgroup.card_eq_one] at hj
      exact absurd (hj ▸ hcEL) (by simpa using h.ne_one)
    · have hEL3 : Nat.card (E ⊓ L : Subgroup G) = 3 := by rw [hj, pow_one]
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
        exact absurd (mk_pow_three_eq_one_of_cube hL hcube (hEL heE) (hE.1.2 e heE) l₀ hl₀ hz₀
          hlz) hx3
    · have hEL9 : Nat.card (E ⊓ L : Subgroup G) = 9 := by rw [hj]; norm_num
      exact (false_of_card_inf_L_eq_nine_of hm3 hL h.mem_L h.ne_one hZ hE hEL hcE
        (fun e he l hl z hz hlz =>
          mk_pow_three_eq_one_of_cube hL hcube (hEL he) (hE.1.2 e he) l hl hz hlz)
        hB3 hEL9).elim
    · exfalso
      have hEL' : E ⊓ L = E :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hj, hE.2]; norm_num)
      exact false_of_isE27_le_of hm3 hE (hEL' ▸ inf_le_right)
  · exact item125BarC9_of h45 hK2 hK9 hG1 G A c L h hty E hE hEL hcE (by rw [hk]; norm_num)
  · exfalso
    have hEC : E ⊓ Sec4.thetaQuotCentralizer L = E :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk, hE.2]; norm_num)
    exact false_of_E27_le_thetaQuotCentralizer h.partTwoF_eq hperf hZ hev hE.1 hE.2
      (hEC ▸ inf_le_right)

end CFSG.RankThree.PartTwo.Sec12
