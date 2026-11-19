module

public import CFSG.Open.StatedDefs
public import Mathlib.FieldTheory.Finite.GaloisField
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
import CFSG.Open.StatedAPI
import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Open

private theorem card_statedSp_gf2f_eq (f : ℕ) (hf : 1 ≤ f) (r : ℕ) :
    Nat.card ↥(StatedSp r (GaloisField 2 f)) =
      (2 ^ f) ^ (r ^ 2) * ∏ j ∈ Finset.Icc 1 r, ((2 ^ f) ^ (2 * j) - 1) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
    GaloisField.card 2 f (by omega)]

theorem isSimpleGroup_statedSp_gf2f {m f : ℕ} (hm : 1 ≤ m) (hf : 2 ≤ f) :
    IsSimpleGroup ↥(StatedSp m (GaloisField 2 f)) := by
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hK4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hsimple : IsSimpleGroup (StatedProj (StatedSp m (GaloisField 2 f))) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (GaloisField 2 f) m hm
      (Or.inl (Or.inr hK4))
  have hbij : Function.Bijective (QuotientGroup.mk'
      ((StatedScalars (Fin m ⊕ Fin m) (GaloisField 2 f)).subgroupOf
        (StatedSp m (GaloisField 2 f)))) :=
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by
      rw [QuotientGroup.ker_mk',
        CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]),
      QuotientGroup.mk'_surjective _⟩
  exact (MulEquiv.ofBijective _ hbij).isSimpleGroup

theorem not_isMulCommutative_statedSp_gf2f {m f : ℕ} (hm : 1 ≤ m) (hf : 2 ≤ f) :
    ¬ IsMulCommutative ↥(StatedSp m (GaloisField 2 f)) := by
  intro hcomm
  have hprime := (Group.is_simple_iff_prime_card (α := ↥(StatedSp m (GaloisField 2 f)))).1
    (isSimpleGroup_statedSp_gf2f hm hf)
  have h4 : 4 ∣ Nat.card ↥(StatedSp m (GaloisField 2 f)) := by
    rw [card_statedSp_gf2f_eq f (by omega)]
    refine Dvd.dvd.mul_right ?_ _
    calc 4 = 2 ^ 2 := by norm_num
      _ ∣ 2 ^ f := pow_dvd_pow 2 hf
      _ ∣ (2 ^ f) ^ (m ^ 2) := dvd_pow_self _ (pow_ne_zero 2 (by omega))
  rcases Nat.Prime.eq_one_or_self_of_dvd hprime 4 h4 with h | h
  · omega
  · rw [← h] at hprime
    norm_num at hprime

theorem even_card_statedSp_gf2f {m f : ℕ} (hm : 1 ≤ m) (hf : 1 ≤ f) :
    Even (Nat.card ↥(StatedSp m (GaloisField 2 f))) := by
  rw [card_statedSp_gf2f_eq f hf]
  exact Even.mul_right (Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩,
    pow_ne_zero 2 (by omega)⟩) _

theorem card_statedSp_one_two : Nat.card ↥(StatedSp 1 (GaloisField 2 2)) = 60 := by
  rw [card_statedSp_gf2f_eq 2 (by norm_num)]
  decide

theorem eq_of_card_statedSp_dvd_m12 {m f : ℕ} (hm : 1 ≤ m) (hf : 2 ≤ f)
    (h : Nat.card ↥(StatedSp m (GaloisField 2 f)) ∣ 95040) : m = 1 ∧ f = 2 := by
  have hcard := card_statedSp_gf2f_eq f (by omega) m
  have h2 : 2 ^ (f * m ^ 2) ∣ 95040 := by
    refine dvd_trans ?_ h
    rw [hcard, ← pow_mul]
    exact Dvd.intro _ rfl
  have hle : f * m ^ 2 ≤ 6 := by
    by_contra hlt
    push Not at hlt
    have h128 : 2 ^ 7 ∣ 95040 := dvd_trans (pow_dvd_pow 2 hlt) h2
    norm_num at h128
  have hm1 : m = 1 := by
    by_contra hne
    have hm2 : 2 ≤ m := by omega
    have h4 : 4 ≤ m ^ 2 := by nlinarith
    nlinarith
  subst hm1
  have hf6 : f ≤ 6 := by simpa using hle
  refine ⟨rfl, ?_⟩
  interval_cases f
  · rfl
  all_goals
    exfalso
    rw [hcard] at h
    norm_num [Finset.Icc_self] at h

end CFSG.RankThree.GF2n.Tim79a
