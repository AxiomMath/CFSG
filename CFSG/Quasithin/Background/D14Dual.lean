module

public import CFSG.Quasithin.Background.B4Dual
public import CFSG.Quasithin.Background.A4Aut

public section

namespace CFSG.Quasithin.D14

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Abstract

variable {V : Type*} [CommGroup V] [Finite V]

theorem isFFModule_dualSub_of_card (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hAX : A ≤ X) (hA : A ≠ ⊥) (hel : IsElemAbelian2 A)
    (hcard : Nat.card (commV A) ≤ Nat.card A) : IsFFModule (dualSub X) := by
  refine ⟨dualSub A, Subgroup.map_mono hAX, ?_, ?_, ?_⟩
  · intro hbot
    apply hA
    apply Subgroup.eq_bot_of_card_eq
    rw [← card_dualSub hV A, hbot]
    exact Subgroup.card_bot
  · obtain ⟨hcomm, hsq⟩ := hel
    refine ⟨?_, ?_⟩
    · rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
      have : dualAct V (a * b) = dualAct V (b * a) := by rw [hcomm a ha b hb]
      exact (map_mul (dualAct V) a b).symm.trans (this.trans (map_mul (dualAct V) b a))
    · rintro x ⟨a, ha, rfl⟩
      exact (map_pow (dualAct V) a 2).symm.trans (by rw [hsq a ha, map_one]; rfl)
  · calc Nat.card (DualGrp V) = Nat.card (fixV (dualSub A)) * (fixV (dualSub A)).index :=
          (Subgroup.card_mul_index _).symm
      _ = Nat.card (fixV (dualSub A)) * Nat.card (commV A) := by rw [index_fixV_dualSub hV A]
      _ ≤ Nat.card (fixV (dualSub A)) * Nat.card A := Nat.mul_le_mul_left _ hcard
      _ = Nat.card (dualSub A) * Nat.card (fixV (dualSub A)) := by
          rw [card_dualSub hV A, mul_comm]

theorem isElemAbelian2_and_card_le (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)}
    (hquad : ∀ a ∈ A, ∀ b ∈ A, ∀ v : V, a (b v * v⁻¹) = b v * v⁻¹) (v₀ : V)
    (hcomm : ∀ a ∈ A, ∀ v : V, ∃ a' ∈ A, a v * v⁻¹ = a' v₀ * v₀⁻¹) :
    IsElemAbelian2 A ∧ Nat.card (commV A) ≤ Nat.card A := by
  have hab : ∀ a ∈ A, ∀ b ∈ A, ∀ v : V, (a * b) v = (b v * v⁻¹) * (a v * v⁻¹) * v := by
    intro a ha b hb v
    calc (a * b) v = a ((b v * v⁻¹) * v) := by rw [MulAut.mul_apply, inv_mul_cancel_right]
      _ = (b v * v⁻¹) * a v := by rw [map_mul, hquad a ha b hb v]
      _ = (b v * v⁻¹) * (a v * v⁻¹) * v := by rw [mul_assoc (b v * v⁻¹), inv_mul_cancel_right]
  refine ⟨⟨fun a ha b hb => ?_, fun a ha => ?_⟩, ?_⟩
  · ext v
    rw [hab a ha b hb v, hab b hb a ha v, mul_comm (b v * v⁻¹)]
  · ext v
    rw [pow_two, hab a ha a ha v, ← pow_two, hV, one_mul, MulAut.one_apply]
  · let g : A →* V :=
      { toFun := fun a => (a : MulAut V) v₀ * v₀⁻¹
        map_one' := by simp
        map_mul' := fun a b => by
          show ((a : MulAut V) * b) v₀ * v₀⁻¹ =
            ((a : MulAut V) v₀ * v₀⁻¹) * ((b : MulAut V) v₀ * v₀⁻¹)
          rw [hab a a.2 b b.2 v₀, mul_inv_cancel_right, mul_comm] }
    have hle : commV A ≤ g.range := by
      rw [commV, Subgroup.closure_le]
      rintro _ ⟨a, ha, v, rfl⟩
      obtain ⟨a', ha', h⟩ := hcomm a ha v
      exact ⟨⟨a', ha'⟩, h.symm⟩
    exact (Subgroup.card_le_of_le hle).trans
      (Nat.card_le_card_of_surjective _ g.rangeRestrict_surjective)

end Abstract

section Internal

variable {G : Type*} [Group G] [Finite G]

theorem isDualFFInt_of_commutator {G₁ Q V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hQG₁ : Q ≤ G₁) (hQV : Q ≤ Subgroup.normalizer (V : Set G))
    (hnc : ¬ Q ≤ Subgroup.centralizer (V : Set G))
    (hquad : ∀ q ∈ Q, ∀ q' ∈ Q, ∀ v ∈ V,
      q * (q' * v * q'⁻¹ * v⁻¹) * q⁻¹ = q' * v * q'⁻¹ * v⁻¹)
    {v₀ : G} (hv₀ : v₀ ∈ V)
    (hcomm : ∀ q ∈ Q, ∀ v ∈ V, ∃ q' ∈ Q, q * v * q⁻¹ * v⁻¹ = q' * v₀ * q'⁻¹ * v₀⁻¹) :
    IsDualFFInt G₁ V hV := by
  let _inst : CommGroup ↥V := commGroupOfElemAbelian hV
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (hV.2 v v.2)
  have hmem : ∀ a ∈ autOn Q V, ∃ q : Q, A4.actionOn V Q hQV q = a := fun a ha =>
    (A4.mem_autOn_iff hQV).mp ha
  have hquad' : ∀ a ∈ autOn Q V, ∀ b ∈ autOn Q V, ∀ v : ↥V, a (b v * v⁻¹) = b v * v⁻¹ := by
    intro a ha b hb v
    obtain ⟨q, rfl⟩ := hmem a ha
    obtain ⟨q', rfl⟩ := hmem b hb
    apply Subtype.ext
    show (q : G) * ((q' : G) * v * (q' : G)⁻¹ * (v : G)⁻¹) * (q : G)⁻¹ =
      (q' : G) * v * (q' : G)⁻¹ * (v : G)⁻¹
    exact hquad q q.2 q' q'.2 v v.2
  have hcomm' : ∀ a ∈ autOn Q V, ∀ v : ↥V, ∃ a' ∈ autOn Q V,
      a v * v⁻¹ = a' ⟨v₀, hv₀⟩ * (⟨v₀, hv₀⟩ : ↥V)⁻¹ := by
    intro a ha v
    obtain ⟨q, rfl⟩ := hmem a ha
    obtain ⟨q', hq', h⟩ := hcomm q q.2 v v.2
    refine ⟨A4.actionOn V Q hQV ⟨q', hq'⟩, (A4.mem_autOn_iff hQV).mpr ⟨_, rfl⟩, ?_⟩
    apply Subtype.ext
    show (q : G) * v * (q : G)⁻¹ * (v : G)⁻¹ = q' * v₀ * q'⁻¹ * v₀⁻¹
    exact h
  have hne : autOn Q V ≠ ⊥ := by
    intro hbot
    apply hnc
    intro q hq
    have h1 : A4.actionOn V Q hQV ⟨q, hq⟩ ∈ autOn Q V := (A4.mem_autOn_iff hQV).mpr ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact (A4.actionOn_eq_one_iff hQV ⟨q, hq⟩).mp h1
  obtain ⟨hel, hcard⟩ := isElemAbelian2_and_card_le hV2 hquad' ⟨v₀, hv₀⟩ hcomm'
  exact isFFModule_dualSub_of_card hV2 (A4.autOn_mono hQG₁) hne hel hcard

end Internal

end CFSG.Quasithin.D14
