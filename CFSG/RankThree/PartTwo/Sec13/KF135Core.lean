module

public import CFSG.RankThree.PartTwo.Sec13.KF135Defs
public import CFSG.RankThree.PartTwo.Sec13.K135K3Core

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Proof

open CFSG Subgroup Pointwise
open CFSG.RankThree.PartTwo.Sec13.F135Last

variable {S : Type} [Group S] [Finite S]

theorem smul_subgroup_eq_map (φ : MulAut S) (T : Subgroup S) :
    φ • T = T.map φ.toMonoidHom := by
  ext y
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨φ⁻¹ • y, h, by simp⟩
  · rintro ⟨w, hw, rfl⟩
    simpa using hw

namespace KF135Hyp

variable {p : ℕ} {P : Subgroup (MulAut S)} {x u : MulAut S} {V : Subgroup (MulAut S)}

theorem center_eq_bot (h : KF135Hyp S p P x u V) : Subgroup.center S = ⊥ := by
  haveI := h.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h0 | h0
  · exact h0
  · obtain ⟨a, b, hab⟩ := h.nonab
    exact absurd (Subgroup.mem_center_iff.1 (h0 ▸ Subgroup.mem_top b) a) hab

theorem conj_injective (h : KF135Hyp S p P x u V) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hac : a ∈ Subgroup.center S := Subgroup.mem_center_iff.2 fun g => by
    have h1 := congrArg (fun φ : MulAut S => φ g) ha
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc g * a = a * g * a⁻¹ * a := by rw [h1]
      _ = a * g := by group
  rw [h.center_eq_bot, Subgroup.mem_bot] at hac
  exact hac

theorem sq_dvd_card (h : KF135Hyp S p P x u V) (hOut : KFactOutP) (hL : Sec4.Census.List42 S) :
    p ^ 2 ∣ Nat.card S := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hidx := hOut S h.simple h.nonab hL p h.prime h.seven_le P h.exponent
  set A := P ⊓ (MulAut.conj : S →* MulAut S).range with hA
  have h1 : Nat.card A * A.relIndex P = Nat.card P := by
    have e := (A.subgroupOf P).card_mul_index
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ≤ P)).toEquiv] at e
  have hcardA : p ^ 2 ≤ Nat.card A := by
    have hpos : 0 < p := h.prime.pos
    by_contra hlt
    push Not at hlt
    have h2 : Nat.card A * A.relIndex P < p ^ 2 * p :=
      Nat.mul_lt_mul_of_lt_of_le hlt hidx hpos
    rw [h1] at h2
    have h3 : p ^ 2 * p = p ^ 3 := by ring
    have := h.card
    omega
  have hAp : IsPGroup p A := h.pgroup.to_le inf_le_left
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hAp
  have hk2 : 2 ≤ k := (Nat.pow_le_pow_iff_right h.prime.one_lt).1 (hk ▸ hcardA)
  have hdvdA : p ^ 2 ∣ Nat.card A := hk ▸ pow_dvd_pow p hk2
  have hrange : Nat.card (MulAut.conj : S →* MulAut S).range = Nat.card S :=
    (Nat.card_congr (MonoidHom.ofInjective h.conj_injective).toEquiv).symm
  have hAdvd : Nat.card A ∣ Nat.card S := hrange ▸ Subgroup.card_dvd_of_le inf_le_right
  exact hdvdA.trans hAdvd

theorem false_of_not_sq_dvd_card (h : KF135Hyp S p P x u V) (hOut : KFactOutP)
    (hL : Sec4.Census.List42 S) (hn : ¬ p ^ 2 ∣ Nat.card S) : False :=
  hn (h.sq_dvd_card hOut hL)

theorem cube_dvd_card_of_le (h : KF135Hyp S p P x u V)
    (hle : P ≤ (MulAut.conj : S →* MulAut S).range) : p ^ 3 ∣ Nat.card S := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h.pgroup
  have hk3 : 3 ≤ k := (Nat.pow_le_pow_iff_right h.prime.one_lt).1 (hk ▸ h.card)
  have hdvdP : p ^ 3 ∣ Nat.card P := hk ▸ pow_dvd_pow p hk3
  have hrange : Nat.card (MulAut.conj : S →* MulAut S).range = Nat.card S :=
    (Nat.card_congr (MonoidHom.ofInjective h.conj_injective).toEquiv).symm
  exact hdvdP.trans (hrange ▸ Subgroup.card_dvd_of_le hle)

theorem cube_dvd_card_of_not_dvd_outer (h : KF135Hyp S p P x u V)
    (hout : ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S)) :
    p ^ 3 ∣ Nat.card S :=
  h.cube_dvd_card_of_le (inner_of_not_dvd_outer h.prime hout P h.pgroup)

end KF135Hyp

end CFSG.RankThree.PartTwo.Sec13.KF135Proof
