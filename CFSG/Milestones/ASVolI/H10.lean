module

public import Mathlib
public import CFSG.Milestones.ASVolI.H1

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin

theorem mQuot_bot_eq_rk {G : Type*} [Group G] [Finite G] (A : Subgroup G) :
    E3.mQuot A ⊥ = rk ↥A := by
  unfold E3.mQuot rk
  rw [Subgroup.relIndex_bot_left]

theorem mQuot_succ_le_rk {G : Type*} [Group G] [Finite G] (A X : Subgroup G) (hA : IsPGroup 2 ↥A)
    (hXA : X ≤ A) (hX : X ≠ ⊥) : E3.mQuot A X + 1 ≤ rk ↥A := by
  have hXp : IsPGroup 2 ↥X := hA.to_le hXA
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hXp
  have hn1 : n ≠ 0 := by
    rintro rfl
    apply hX
    rw [pow_zero] at hn
    exact Subgroup.eq_bot_of_card_eq X hn
  have h1 : E3.mQuot X ⊥ = n := by
    unfold E3.mQuot
    rw [Subgroup.relIndex_bot_left, hn, padicValNat.prime_pow]
  have h2 := E3.mQuot_add (V := A) (U := ⊥) (U' := X) bot_le hXA
  rw [h1, mQuot_bot_eq_rk] at h2
  omega

end CFSG.ASVolI.ChH

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.ASVolI.ChH

@[expose] def H_10_1 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
  ∀ (M A : Subgroup (MulAut V)), IsA2 M A → xiSub A = E3.gammaCheck (rk ↥A - 1) A

theorem as_H_10_1 : H_10_1 := by
  intro V _ _ hV M A hA
  obtain ⟨hAM, hA1, hAel⟩ := hA
  have : Finite (MulAut V) :=
    Finite.of_injective (fun f : MulAut V => (f : V → V)) (fun f g h => MulEquiv.ext (congrFun h))
  have hp : IsPGroup 2 ↥A := fun g => ⟨1, by
    apply Subtype.ext
    have := hAel.2 g.1 g.2
    simpa using this⟩
  have key2 : 1 ≤ rk ↥A := by
    have := mQuot_succ_le_rk A A hp le_rfl hA1
    rw [E3.mQuot_self] at this
    omega
  apply le_antisymm
  · unfold xiSub E3.gammaCheck
    refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
    have hX : Subgroup.zpowers a ≠ ⊥ := by
      intro h
      apply ha1
      have : a ∈ Subgroup.zpowers a := Subgroup.mem_zpowers a
      rw [h] at this
      exact Subgroup.mem_bot.mp this
    have hle : Subgroup.zpowers a ≤ A := (Subgroup.zpowers_le).2 ha
    have hm := mQuot_succ_le_rk A (Subgroup.zpowers a) hp hle hX
    exact le_iSup_of_le (Subgroup.zpowers a)
      (le_iSup_of_le hle (le_iSup_of_le (by omega) le_rfl))
  · unfold xiSub E3.gammaCheck
    refine iSup_le fun X => iSup_le fun hXA => iSup_le fun hX => ?_
    have hXne : X ≠ ⊥ := by
      rintro rfl
      rw [mQuot_bot_eq_rk] at hX
      omega
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hXne
    have hzp : Subgroup.zpowers (a : MulAut V) ≤ X := (Subgroup.zpowers_le).2 a.2
    have hfix : fixV X ≤ fixV (Subgroup.zpowers (a : MulAut V)) :=
      fun v hv x hx => hv x (hzp hx)
    refine hfix.trans (le_iSup_of_le (a : MulAut V)
      (le_iSup_of_le (hXA a.2) (le_iSup_of_le (fun h => ha1 (Subtype.ext h)) le_rfl)))

end CFSG.ASVolI
