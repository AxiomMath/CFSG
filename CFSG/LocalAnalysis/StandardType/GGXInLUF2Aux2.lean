module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneDefs

public section

namespace CFSG.StandardType.GGXInL

open CFSG.Assembly

theorem lup8f_f2_commute_of_noTransvection {G : Type} [Group G] {p : ℕ} (hp : p.Prime)
    {Bs : Subgroup G} (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs) {x a : G}
    (hx : x ∈ Bs) (ha : a ∈ Subgroup.normalizer (Bs : Set G)) (hax : a * x = x * a)
    (hdisp : ∀ b ∈ Bs, b * a * b⁻¹ * a⁻¹ ∈ Subgroup.zpowers x) :
    ∀ b ∈ Bs, a * b = b * a := by
  have hzx : ∀ g : G, g * x = x * g → ∀ y ∈ Subgroup.zpowers x, g * y * g⁻¹ = y := by
    intro g hg y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [((show Commute g x from hg).zpow_right k).eq, mul_inv_cancel_right]
  let S : Subgroup G :=
    { carrier := {g | g * x = x * g ∧ ∀ b ∈ Bs, b * g * b⁻¹ * g⁻¹ ∈ Subgroup.zpowers x}
      mul_mem' := by
        rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
        refine ⟨by rw [mul_assoc, hh1, ← mul_assoc, hg1, mul_assoc], fun b hb => ?_⟩
        have e : b * (g * h) * b⁻¹ * (g * h)⁻¹ =
            (b * g * b⁻¹ * g⁻¹) * (g * (b * h * b⁻¹ * h⁻¹) * g⁻¹) := by group
        rw [e, hzx g hg1 _ (hh2 b hb)]
        exact Subgroup.mul_mem _ (hg2 b hb) (hh2 b hb)
      one_mem' := ⟨by rw [one_mul, mul_one], fun b _ => by simp⟩
      inv_mem' := by
        rintro g ⟨hg1, hg2⟩
        have hg1' : g⁻¹ * x = x * g⁻¹ := by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hg1, mul_assoc, mul_inv_cancel, mul_one]
        refine ⟨hg1', fun b hb => ?_⟩
        have e : b * g⁻¹ * b⁻¹ * g⁻¹⁻¹ = g⁻¹ * (b * g * b⁻¹ * g⁻¹)⁻¹ * g⁻¹⁻¹ := by group
        rw [e, hzx g⁻¹ hg1' _ (Subgroup.inv_mem _ (hg2 b hb))]
        exact Subgroup.inv_mem _ (hg2 b hb) }
  have haS : a ∈ S := ⟨hax, hdisp⟩
  have hle : ⁅Bs, Subgroup.zpowers a⁆ ≤ Subgroup.zpowers x := by
    rw [Subgroup.commutator_le]
    intro b hb g hg
    rw [commutatorElement_def]
    exact (Subgroup.zpowers_le.mpr haS hg).2 b hb
  intro b hb
  by_contra hab
  apply CFSG.StandardType.not_ggTransvection_of_noTransvection hp hBs hNT a ha
  have hxp : x ^ p = 1 := hBs.2 x hx
  refine ⟨?_, hle.trans ?_⟩
  · have h1 : Nat.card (⁅Bs, Subgroup.zpowers a⁆ : Subgroup G) ∣ p :=
      (Subgroup.card_dvd_of_le hle).trans
        (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hxp)
    have h2 : Nat.card (⁅Bs, Subgroup.zpowers a⁆ : Subgroup G) ≠ 1 := by
      intro h
      rw [Subgroup.card_eq_one] at h
      have hm := Subgroup.commutator_mem_commutator hb (Subgroup.mem_zpowers a)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
      exact hab hm.symm
    exact ((Nat.dvd_prime hp).mp h1).resolve_left h2
  · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact hax.symm

end CFSG.StandardType.GGXInL

end
