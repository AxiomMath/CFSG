module

public import CFSG.RankThree.PartTwo.Sec21.Item21EarlyProofQuasi
public import CFSG.RankThree.PartTwo.Sec4.Census.SporadicTwoCoverM23
import CFSG.Sporadic.J2
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec21.Item22Tools
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherU54
import CFSG.LieType.Simplicity.Classical
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6G2
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Triality
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.Timmesfeld.Orders.Classical
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint

@[expose] def Bar211Quot (Y : Type) [Group Y] : Prop :=
  Nonempty (Y ≃* NativeSporadic.M22) ∨ Nonempty (Y ≃* NativeSporadic.M23) ∨
    Nonempty (Y ≃* NativeSporadic.HS) ∨ Nonempty (Y ≃* NativeSporadic.M24) ∨
    Nonempty (Y ≃* NativeSporadic.He) ∨ Nonempty (Y ≃* NativeSporadic.J2) ∨
    Nonempty (Y ≃* NativeSporadic.Ru) ∨ Nonempty (Y ≃* NativeSporadic.J4) ∨
    Nonempty (Y ≃* NativeSporadic.J3) ∨
    (∃ n : ℕ, 2 ≤ n ∧ Even n ∧ Nonempty (Y ≃* projSL 3 (GaloisField 2 n))) ∨
    (∃ n : ℕ, 2 ≤ n ∧ Even n ∧
      (ChevalleyExceptionalModel Y .G2 2 n ∨ ChevalleyExceptionalModel Y .trialityD4 2 n)) ∨
    (∃ n : ℕ, 2 ≤ n ∧ Even n ∧ Nonempty (Y ≃* projSp 2 (GaloisField 2 n))) ∨
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty (Y ≃* projSU 4 2 n)) ∨ Nonempty (Y ≃* projSU 5 2 2) ∨
    Nonempty (Y ≃* projSL 4 (GaloisField 2 1)) ∨ Nonempty (Y ≃* projSL 5 (GaloisField 2 1)) ∨
    Nonempty (Y ≃* projSp 3 (GaloisField 2 1))

namespace Item21Early2Proof

section Centre

variable {X S : Type*} [Group X] [Group S]

theorem center_eq_bot_of_isSimpleGroup_of_not_prime [IsSimpleGroup S]
    (hS : ¬ (Nat.card S).Prime) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    have : IsMulCommutative S :=
      ⟨⟨fun a b => (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b : b ∈ _) a)⟩⟩
    exact hS (Group.is_simple_iff_prime_card.mp inferInstance)

theorem not_prime_of_four_dvd {m : ℕ} (h : 4 ∣ m) : ¬ m.Prime := by
  intro hp
  have h2 : 2 ∣ m := (show (2 : ℕ) ∣ 4 by norm_num).trans h
  rcases (Nat.dvd_prime hp).mp h2 with h1 | h1
  · norm_num at h1
  · subst h1
    norm_num at h

theorem center_eq_bot_of_mulEquiv (e : X ≃* S) (hS : Subgroup.center S = ⊥) :
    Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hez : e z ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro s
    obtain ⟨x, rfl⟩ := e.surjective s
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
  rw [hS, Subgroup.mem_bot, map_eq_one_iff e e.injective] at hez
  exact (Subgroup.mem_bot).mpr hez

@[expose] noncomputable def quotCenterEquivOfBot (h : Subgroup.center X = ⊥) :
    X ⧸ Subgroup.center X ≃* X :=
  (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot

theorem nonempty_quot_of_mulEquiv (hS : Subgroup.center S = ⊥) (e : X ≃* S) :
    Nonempty (X ⧸ Subgroup.center X ≃* S) :=
  ⟨(quotCenterEquivOfBot (center_eq_bot_of_mulEquiv e hS)).trans e⟩

theorem map_center_eq (e : X ≃* S) :
    (Subgroup.center X).map e.toMonoidHom = Subgroup.center S := by
  ext s
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro t
    obtain ⟨x, rfl⟩ := e.surjective t
    change e x * e z = e z * e x
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
  · intro hs
    refine ⟨e.symm s, ?_, by simp⟩
    change e.symm s ∈ Subgroup.center X
    rw [Subgroup.mem_center_iff]
    intro x
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, Subgroup.mem_center_iff.mp hs (e x)]

@[expose] noncomputable def quotCenterCongr (e : X ≃* S) :
    X ⧸ Subgroup.center X ≃* S ⧸ Subgroup.center S :=
  QuotientGroup.congr (Subgroup.center X) (Subgroup.center S) e (map_center_eq e)

end Centre

theorem center_nativeM22_eq_bot :
    Subgroup.center NativeSporadic.M22 = ⊥ := by
  have : IsSimpleGroup NativeSporadic.M22 := CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  refine center_eq_bot_of_isSimpleGroup_of_not_prime ?_
  rw [CFSG.Sporadic.Mathieu.card_M22]
  norm_num

theorem center_nativeHS_eq_bot :
    Subgroup.center NativeSporadic.HS = ⊥ := by
  have : IsSimpleGroup NativeSporadic.HS := CFSG.Sporadic.HS.isSimpleGroup_HS
  refine center_eq_bot_of_isSimpleGroup_of_not_prime ?_
  rw [CFSG.Sporadic.HS.card_HS]
  norm_num

theorem center_nativeM24_eq_bot :
    Subgroup.center NativeSporadic.M24 = ⊥ := by
  have : IsSimpleGroup NativeSporadic.M24 := CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
  refine center_eq_bot_of_isSimpleGroup_of_not_prime ?_
  rw [CFSG.Sporadic.Mathieu.card_M24]
  norm_num

theorem center_nativeHe_eq_bot :
    Subgroup.center NativeSporadic.He = ⊥ := by
  have : IsSimpleGroup NativeSporadic.He := CFSG.Sporadic.He.isSimpleGroup_He
  refine center_eq_bot_of_isSimpleGroup_of_not_prime ?_
  rw [CFSG.Sporadic.He.card_He]
  norm_num

theorem center_nativeJ2_eq_bot :
    Subgroup.center NativeSporadic.J2 = ⊥ := by
  have : IsSimpleGroup NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  refine center_eq_bot_of_isSimpleGroup_of_not_prime ?_
  rw [KFacts.KS14.card_nativeJ2]
  norm_num

theorem center_nativeRu_eq_bot :
    Subgroup.center NativeSporadic.Ru = ⊥ := by
  have : IsSimpleGroup NativeSporadic.Ru := CFSG.Sporadic.Ru.isSimpleGroup_Ru
  refine center_eq_bot_of_isSimpleGroup_of_not_prime ?_
  rw [CFSG.Sporadic.Ru.card_Ru]
  norm_num

theorem center_nativeJ4_eq_bot :
    Subgroup.center NativeSporadic.J4 = ⊥ := by
  have : IsSimpleGroup NativeSporadic.J4 := CFSG.Sporadic.J4.isSimpleGroup_J4
  refine center_eq_bot_of_isSimpleGroup_of_not_prime ?_
  rw [CFSG.Sporadic.J4.card_J4]
  norm_num

theorem center_nativeJ3_eq_bot :
    Subgroup.center NativeSporadic.J3 = ⊥ := by
  have : IsSimpleGroup NativeSporadic.J3 := CFSG.Sporadic.J3.isSimpleGroup_J3
  refine center_eq_bot_of_isSimpleGroup_of_not_prime ?_
  rw [CFSG.Sporadic.J3.card_J3]
  norm_num

section M23

open Equiv Sec4.Census.SporadicTwoCover

@[expose] def m23C : Perm (Fin 23) := m23α * m23β

theorem m23C_orbit : ∀ i : Fin 23, ∃ k : Fin 23, (m23C ^ (k : ℕ)) 0 = i := by
  decide +kernel

theorem m23C_pow_not_commute :
    ∀ k : Fin 23, (k : ℕ) ≠ 0 → m23C ^ (k : ℕ) * m23α ≠ m23α * m23C ^ (k : ℕ) := by
  decide +kernel

theorem eq_pow_of_commute_m23C {z : Perm (Fin 23)} (hz : z * m23C = m23C * z) :
    ∃ k : Fin 23, z = m23C ^ (k : ℕ) := by
  obtain ⟨m, hm⟩ := m23C_orbit (z 0)
  refine ⟨m, Equiv.ext fun i => ?_⟩
  obtain ⟨k, rfl⟩ := m23C_orbit i
  have hzk : z * m23C ^ (k : ℕ) = m23C ^ (k : ℕ) * z := ((Commute.pow_right hz (k : ℕ))).eq
  have h1 : z ((m23C ^ (k : ℕ)) 0) = (m23C ^ (k : ℕ)) (z 0) := by
    rw [← Perm.mul_apply, hzk, Perm.mul_apply]
  rw [h1, ← hm, ← Perm.mul_apply, ← Perm.mul_apply, ← pow_add, ← pow_add, add_comm]

theorem center_nativeM23_eq_bot : Subgroup.center NativeSporadic.M23 = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hC : (z : Perm (Fin 23)) * m23C = m23C * z := by
    have := Subgroup.mem_center_iff.mp hz ⟨m23C, Subgroup.mul_mem _ m23α_mem m23β_mem⟩
    exact (congrArg Subtype.val this).symm
  have hA : (z : Perm (Fin 23)) * m23α = m23α * z := by
    have := Subgroup.mem_center_iff.mp hz ⟨m23α, m23α_mem⟩
    exact (congrArg Subtype.val this).symm
  obtain ⟨k, hk⟩ := eq_pow_of_commute_m23C hC
  rw [Subgroup.mem_bot]
  by_cases h0 : (k : ℕ) = 0
  · apply Subtype.ext
    rw [hk, h0, pow_zero]
    rfl
  · exact absurd (hk ▸ hA) (m23C_pow_not_commute k h0)

end M23

theorem two_pow_mod_three_of_even {n : ℕ} (hn : Even n) : 2 ^ n % 3 = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

theorem center_projSL_three_eq_bot {n : ℕ} (hn : 0 < n) (he : Even n) :
    Subgroup.center (projSL 3 (GaloisField 2 n)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (Sec13.isPerfect_center_projSL 2 n hn (two_pow_mod_three_of_even he)).2

theorem center_projSp_two_eq_bot {n : ℕ} (hn : 2 ≤ n) :
    Subgroup.center (projSp 2 (GaloisField 2 n)) = ⊥ := by
  have : IsSimpleGroup (projSp 2 (GaloisField 2 n)) := isSimpleGroup_projSp_two hn
  refine center_eq_bot_of_isSimpleGroup_of_not_prime (not_prime_of_four_dvd ?_)
  rw [Sec19.Step1911Proof.card_projSp_two (by omega)]
  refine Dvd.dvd.mul_right ?_ _
  exact (show (4 : ℕ) ∣ 2 ^ 2 by norm_num).trans (Nat.pow_dvd_pow 2 (by omega))

theorem center_projSU_four_eq_bot {n : ℕ} (hn : 1 ≤ n) :
    Subgroup.center (projSU 4 2 n) = ⊥ := by
  have : IsSimpleGroup (projSU 4 2 n) := isSimpleGroup_projSU le_rfl hn
  refine center_eq_bot_of_isSimpleGroup_of_not_prime (not_prime_of_four_dvd ?_)
  rw [Sec19.Step1911Proof.card_projSU_four hn]
  refine Dvd.dvd.mul_right ?_ _
  rw [← pow_mul]
  exact (show (4 : ℕ) ∣ 2 ^ 2 by norm_num).trans (Nat.pow_dvd_pow 2 (by omega))

theorem nonempty_quot_SL3 (n : ℕ) :
    Nonempty (SL3 n ⧸ Subgroup.center (SL3 n) ≃* projSL 3 (GaloisField 2 n)) :=
  ⟨(Sec4.projSLEquivPSLn 3 (GaloisField 2 n)).symm⟩

theorem chevalleyG2_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : Y ≃* X) {p f : ℕ}
    (h : ChevalleyExceptionalModel X .G2 p f) : ChevalleyExceptionalModel Y .G2 p f := by
  obtain ⟨hadm, K, hK1, hK2, hK, ⟨e'⟩⟩ := h
  exact ⟨hadm, K, hK1, hK2, hK, ⟨e.trans e'⟩⟩

theorem chevalleyD4_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : Y ≃* X) {p f : ℕ}
    (h : ChevalleyExceptionalModel X .trialityD4 p f) :
    ChevalleyExceptionalModel Y .trialityD4 p f := by
  obtain ⟨hadm, K, hK1, hK2, hK, σ, hσ, ⟨e'⟩⟩ := h
  exact ⟨hadm, K, hK1, hK2, hK, σ, hσ, ⟨e.trans e'⟩⟩

variable {X : Type} [Group X] [Finite X]

theorem bar211Quot_of_isBar211
    (h : IsBar211 X) : Bar211Quot (X ⧸ Subgroup.center X) := by
  unfold IsBar211 at h
  unfold Bar211Quot
  rcases h with h | h | h | h | h | h | h | h | h |
      ⟨n, hn, he, h | h | hG | hD | h | h⟩ | h | ⟨n, hn, hno, h⟩ | h | h |
      h | h | h
  ·
    exact Or.inl <| h.2
  ·
    obtain ⟨e⟩ := h
    exact Or.inl <| nonempty_quot_of_mulEquiv (S := NativeSporadic.M22) center_nativeM22_eq_bot e
  ·
    obtain ⟨e⟩ := h
    exact Or.inr <| Or.inl <|
      nonempty_quot_of_mulEquiv (S := NativeSporadic.M23) center_nativeM23_eq_bot e
  ·
    obtain ⟨e⟩ := h
    exact Or.inr <| Or.inr <| Or.inl <|
      nonempty_quot_of_mulEquiv (S := NativeSporadic.HS) center_nativeHS_eq_bot e
  ·
    obtain ⟨e⟩ := h
    exact Or.inr <| Or.inr <| Or.inr <| Or.inl <|
      nonempty_quot_of_mulEquiv (S := NativeSporadic.M24) center_nativeM24_eq_bot e
  ·
    obtain ⟨e⟩ := h
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
      nonempty_quot_of_mulEquiv (S := NativeSporadic.He) center_nativeHe_eq_bot e
  ·
    obtain ⟨e⟩ := h
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
      nonempty_quot_of_mulEquiv (S := NativeSporadic.J2) center_nativeJ2_eq_bot e
  ·
    obtain ⟨e⟩ := h
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
      nonempty_quot_of_mulEquiv (S := NativeSporadic.Ru) center_nativeRu_eq_bot e
  ·
    obtain ⟨e⟩ := h
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
      nonempty_quot_of_mulEquiv (S := NativeSporadic.J4) center_nativeJ4_eq_bot e
  ·
    obtain ⟨e⟩ := h
    have hn2 : 2 ≤ n := by obtain ⟨k, rfl⟩ := he; omega
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      Or.inl <| ⟨n, hn2, he, nonempty_quot_of_mulEquiv (center_projSL_three_eq_bot hn he) e⟩
  ·
    obtain ⟨e⟩ := h
    have hn2 : 2 ≤ n := by obtain ⟨k, rfl⟩ := he; omega
    obtain ⟨f⟩ := nonempty_quot_SL3 n
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      Or.inl <| ⟨n, hn2, he, ⟨(quotCenterCongr e).trans f⟩⟩
  ·
    have hn2 : 2 ≤ n := by obtain ⟨k, rfl⟩ := he; omega
    have hZ := (CFSG.QuasithinUnique.Setup.X6.even_G2_model_two_extensions hG).1
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      Or.inr <| Or.inl <|
      ⟨n, hn2, he, Or.inl (chevalleyG2_of_mulEquiv (quotCenterEquivOfBot hZ) hG)⟩
  ·
    have hn2 : 2 ≤ n := by obtain ⟨k, rfl⟩ := he; omega
    have hZ := (CFSG.QuasithinUnique.Setup.X6.even_triality_model_two_extensions hD).1
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      Or.inr <| Or.inl <|
      ⟨n, hn2, he, Or.inr (chevalleyD4_of_mulEquiv (quotCenterEquivOfBot hZ) hD)⟩
  ·
    obtain ⟨e⟩ := h
    have hn2 : 2 ≤ n := by obtain ⟨k, rfl⟩ := he; omega
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      Or.inr <| Or.inr <| Or.inl <|
      ⟨n, hn2, he, nonempty_quot_of_mulEquiv (center_projSp_two_eq_bot hn2) e⟩
  ·
    obtain ⟨e⟩ := h
    have hn2 : 2 ≤ n := by obtain ⟨k, rfl⟩ := he; omega
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      Or.inr <| Or.inr <| Or.inr <| Or.inl <|
      ⟨n, hn2, nonempty_quot_of_mulEquiv (center_projSU_four_eq_bot (by omega)) e⟩
  ·
    obtain ⟨e⟩ := h
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
      nonempty_quot_of_mulEquiv Sec4.Item434SmallTwoOther.U54.center_U54 e
  ·
    obtain ⟨e⟩ := h
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      Or.inr <| Or.inr <| Or.inr <| Or.inl <|
      ⟨n, hn, nonempty_quot_of_mulEquiv (center_projSU_four_eq_bot (by omega)) e⟩
  ·
    obtain ⟨e⟩ := h
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
      nonempty_quot_of_mulEquiv (S := NativeSporadic.J3) center_nativeJ3_eq_bot e
  ·
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
      h.2
  ·
    have : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 4 2 1 h).2
    have hZ : Subgroup.center X = ⊥ := by
      refine center_eq_bot_of_isSimpleGroup_of_not_prime ?_
      rw [(CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl,
        show CFSG.Open.ordA (4 - 1) (2 ^ 1) = 20160 by decide]
      norm_num
    obtain ⟨e⟩ := CFSG.RankThree.PartOne.projSL_of_statedClassicalModel h
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
      ⟨(quotCenterEquivOfBot hZ).trans e⟩
  ·
    have : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 5 2 1 h).2
    have hZ : Subgroup.center X = ⊥ := by
      refine center_eq_bot_of_isSimpleGroup_of_not_prime ?_
      rw [(CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl,
        show CFSG.Open.ordA (5 - 1) (2 ^ 1) = 9999360 by decide]
      norm_num
    obtain ⟨e⟩ := CFSG.RankThree.PartOne.projSL_of_statedClassicalModel h
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
      ⟨(quotCenterEquivOfBot hZ).trans e⟩
  ·
    have : IsSimpleGroup X :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp X 3 2 1 h
    have hZ : Subgroup.center X = ⊥ := by
      refine center_eq_bot_of_isSimpleGroup_of_not_prime ?_
      rw [(CFSG.Timmesfeld.card_statedClassicalModel_two h).2.2.1 rfl,
        show CFSG.Open.ordBC 3 (2 ^ 1) = 2 ^ 9 * 2835 by decide]
      norm_num
    obtain ⟨e⟩ := CFSG.RankThree.PartOne.projSp_of_statedClassicalModel h
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      ⟨(quotCenterEquivOfBot hZ).trans e⟩

end Item21Early2Proof

end CFSG.RankThree.PartTwo.Sec21
