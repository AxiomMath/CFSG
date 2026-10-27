module

public import CFSG.RankThree.PartTwo.Sec4.Item426RestSetup
public import CFSG.RankThree.PartTwo.Sec4.Item413Cases
import CFSG.RankThree.PartTwo.Sec4.Item426A6Models
import CFSG.LieType.Simplicity.Suzuki
import CFSG.Sporadic.Mathieu.M11
import CFSG.Sporadic.Mathieu.M12
import CFSG.Sporadic.Mathieu.M22
import CFSG.Sporadic.Mathieu.M23
import CFSG.Sporadic.Mathieu.M24
import CFSG.Sporadic.J1
import CFSG.Sporadic.J2
import CFSG.Sporadic.J3
import CFSG.Sporadic.J4
import CFSG.Sporadic.McL.Simple
import CFSG.Sporadic.HS
import CFSG.Sporadic.He
import CFSG.Sporadic.Ru
public import CFSG.RankThree.PartTwo.Sec4.Item47CasesEven

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item426Rest

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

variable {X : Type} [Group X]

theorem false_of_mulEquiv_quotient_center (hX : IsQuasisimple X)
    (hZ : Subgroup.center X ≠ ⊥) {Y : Type*} [Group Y] (e : X ≃* Y ⧸ Subgroup.center Y) :
    False :=
  hZ (Item426.center_eq_bot_of_mulEquiv_quotient_center hX e)

theorem false_of_mulEquiv_isSimpleGroup (hX : IsQuasisimple X) (hZ : Subgroup.center X ≠ ⊥)
    {Y : Type*} [Group Y] [IsSimpleGroup Y] (e : X ≃* Y) : False :=
  hZ (center_eq_bot_of_mulEquiv_isSimpleGroup hX e)

theorem false_of_projSL (hX : IsQuasisimple X) (hZ : Subgroup.center X ≠ ⊥) {n : ℕ}
    {F : Type} [Field F] (e : X ≃* projSL n F) : False :=
  false_of_mulEquiv_quotient_center hX hZ (e.trans (projSLEquivPSLn n F))

theorem false_of_projSU (hX : IsQuasisimple X) (hZ : Subgroup.center X ≠ ⊥) {n p f : ℕ}
    [Fact p.Prime] (hn : 3 ≤ n) (hf : 1 ≤ f) (e : X ≃* projSU n p f) : False := by
  by_cases hq : (n, p ^ f) = (3, 2)
  · obtain ⟨rfl, hpf⟩ := Prod.mk.inj hq
    have hp2 : p = 2 := by
      have hp := (Fact.out : p.Prime).two_le
      have : p ≤ p ^ f := Nat.le_self_pow (by omega) p
      omega
    subst hp2
    have hf1 : f = 1 := Nat.pow_right_injective le_rfl (hpf.trans (pow_one 2).symm)
    subst hf1
    exact false_of_mulEquiv_projSU_three_two hX e
  · have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
      rw [GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
    have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU
      (GaloisField p (2 * f)) p f hK n hn hq
    exact false_of_mulEquiv_isSimpleGroup hX hZ (e.trans (projSUEquivStatedProj n p f))

theorem false_of_projSp (hX : IsQuasisimple X) (hZ : Subgroup.center X ≠ ⊥) {n : ℕ}
    {F : Type} [Field F] (hn : 1 ≤ n)
    (hF : (Infinite F ∨ 4 ≤ Nat.card F) ∨ (Nat.card F = 3 ∧ 2 ≤ n) ∨
      (Nat.card F = 2 ∧ 3 ≤ n)) (e : X ≃* projSp n F) : False := by
  have := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F n hn hF
  exact false_of_mulEquiv_isSimpleGroup hX hZ (e.trans (projSpEquivStatedProj n F))

theorem false_of_projSp_two (hX : IsQuasisimple X) (hZ : Subgroup.center X ≠ ⊥)
    (hbig : ∃ N, 720 < N ∧ N ∣ Nat.card X) {n : ℕ} (hn : 1 ≤ n)
    (e : X ≃* projSp 2 (GaloisField 2 n)) : False := by
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  · obtain rfl : n = 1 := by omega
    obtain ⟨N, hN, hNd⟩ := hbig
    rw [Nat.card_congr (e.trans (projSpEquivStatedProj 2 _)).toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo, hF] at hNd
    have h720 : (2 ^ 1) ^ 2 ^ 2 * ∏ j ∈ Finset.Icc 1 2, ((2 ^ 1) ^ (2 * j) - 1) = 720 := by
      decide
    rw [h720] at hNd
    have := Nat.le_of_dvd (by norm_num) hNd
    omega
  · refine false_of_projSp hX hZ (by norm_num) (Or.inl (Or.inr ?_)) e
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2

theorem false_of_alternating (_hX : IsQuasisimple X) (hZ : Subgroup.center X ≠ ⊥)
    (hbig : ∃ N, 720 < N ∧ N ∣ Nat.card X) {n : ℕ} (e : X ≃* alternatingGroup (Fin n)) :
    False := by
  rcases Nat.lt_or_ge n 4 with hn | hn
  · obtain ⟨N, hN, hNd⟩ := hbig
    rw [Nat.card_congr e.toEquiv] at hNd
    have h1 : Nat.card (alternatingGroup (Fin n)) ∣ Nat.card (Equiv.Perm (Fin n)) :=
      Subgroup.card_subgroup_dvd_card _
    rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin n)), Fintype.card_perm,
      Fintype.card_fin] at h1
    have h2 := Nat.le_of_dvd (Nat.factorial_pos n) (hNd.trans h1)
    have h3 : n.factorial ≤ 6 := by
      interval_cases n <;> decide
    omega
  · exact hZ (center_eq_bot_of_mulEquiv e
      (alternatingGroup.center_eq_bot (by simpa using hn)))

theorem false_of_chevalleyExceptional (hX : IsQuasisimple X) (hZ : Subgroup.center X ≠ ⊥)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {p f : ℕ} (ht : t = .G2 ∨ t = .trialityD4)
    (hm : Blueprint.ChevalleyExceptionalModel X t p f) : False := by
  rcases ht with rfl | rfl
  · obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := hm
    exact false_of_mulEquiv_quotient_center hX hZ e
  · obtain ⟨-, K, _, _, -, σ, -, ⟨e⟩⟩ := hm
    exact false_of_mulEquiv_quotient_center hX hZ e

theorem false_of_reeTits (hX : IsQuasisimple X) (hZ : Subgroup.center X ≠ ⊥)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {p f : ℕ} (ht : t = .twistedF4 ∨ t = .Tits)
    (hm : Blueprint.ReeTitsModel X t p f) : False := by
  rcases ht with rfl | rfl
  · obtain ⟨-, a, -, K, _, _, -, ⟨e⟩⟩ := hm
    exact false_of_mulEquiv_quotient_center hX hZ e
  · obtain ⟨-, a, -, K, _, _, -, ⟨e⟩⟩ := hm
    exact false_of_mulEquiv_quotient_center hX hZ e

theorem false_of_suzuki (hX : IsQuasisimple X) (hZ : Subgroup.center X ≠ ⊥) {p f : ℕ}
    (hm : Blueprint.SuzukiModel X p f) : False := by
  have := (CFSG.LieType.Simplicity.fam_2b2_simplicity X p f hm).2
  exact false_of_mulEquiv_isSimpleGroup hX hZ (MulEquiv.refl X)

theorem false_of_sporadic46
    (hX : IsQuasisimple X) (hZ : Subgroup.center X ≠ ⊥) {s : TauCeti.SporadicName}
    (hs : s ∈ sporadics46) (e : X ≃* Blueprint.NativeSporadic.Carrier s) : False := by
  simp only [sporadics46, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have := CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
    exact false_of_mulEquiv_isSimpleGroup hX hZ (Y := Blueprint.NativeSporadic.M11) e
  · have := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
    exact false_of_mulEquiv_isSimpleGroup hX hZ (Y := Blueprint.NativeSporadic.M12) e
  · have := CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
    exact false_of_mulEquiv_isSimpleGroup hX hZ (Y := Blueprint.NativeSporadic.M22) e
  · have := CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2
    exact false_of_mulEquiv_isSimpleGroup hX hZ (Y := Blueprint.NativeSporadic.M23) e
  · have := CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
    exact false_of_mulEquiv_isSimpleGroup hX hZ (Y := Blueprint.NativeSporadic.M24) e
  · have := CFSG.Sporadic.J1.fam_j1_simplicity.2.2
    exact false_of_mulEquiv_isSimpleGroup hX hZ (Y := Blueprint.NativeSporadic.J1) e
  · have := CFSG.Sporadic.J2.fam_j2_simplicity.2.2
    exact false_of_mulEquiv_isSimpleGroup hX hZ (Y := Blueprint.NativeSporadic.J2) e
  · have := CFSG.Sporadic.J3.fam_j3_simplicity.2.2
    exact false_of_mulEquiv_isSimpleGroup hX hZ (Y := Blueprint.NativeSporadic.J3) e
  · have := CFSG.Sporadic.J4.fam_j4_simplicity.2.2
    exact false_of_mulEquiv_isSimpleGroup hX hZ (Y := Blueprint.NativeSporadic.J4) e
  · have := CFSG.Sporadic.McL.fam_mcl_simplicity.2.2
    exact false_of_mulEquiv_isSimpleGroup hX hZ (Y := Blueprint.NativeSporadic.McL) e
  · have := CFSG.Sporadic.HS.fam_hs_simplicity.2.2
    exact false_of_mulEquiv_isSimpleGroup hX hZ (Y := Blueprint.NativeSporadic.HS) e
  · have := CFSG.Sporadic.He.fam_he_simplicity.2.2
    exact false_of_mulEquiv_isSimpleGroup hX hZ (Y := Blueprint.NativeSporadic.He) e
  · have := CFSG.Sporadic.Ru.fam_ru_simplicity.2.2
    exact false_of_mulEquiv_isSimpleGroup hX hZ (Y := Blueprint.NativeSporadic.Ru) e

theorem card_secQ_dvd {P : Subgroup X} [Finite X] : Nat.card (secQ P) ∣ Nat.card X := by
  have h1 : Nat.card (secQ P) ∣ Nat.card (P ⧸ aschbacherSolvableCore 3 P) :=
    Dvd.intro _ (card_secQ_mul P)
  have h2 : Nat.card (P ⧸ aschbacherSolvableCore 3 P) ∣ Nat.card P :=
    Subgroup.card_quotient_dvd_card _
  exact h1.trans (h2.trans (Subgroup.card_subgroup_dvd_card P))

end CFSG.RankThree.PartTwo.Sec4.Item426Rest
