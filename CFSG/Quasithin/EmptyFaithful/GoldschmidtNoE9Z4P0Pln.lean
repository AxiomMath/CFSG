module

import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P0Grp

public section

namespace CFSG.Quasithin

section Defs

variable {V : Type} [CommGroup V]

@[expose] def PlanePair (Tb P P₁ P₂ : Subgroup (MulAut V)) : Prop :=
  P₁ ≤ P ∧ P₂ ≤ P ∧ Nat.card P₁ = 3 ∧ Nat.card P₂ = 3 ∧ P₁ ⊔ P₂ = P ∧
    Disjoint (commV P₁) (commV P₂) ∧ commV P₁ ⊔ commV P₂ = ⊤ ∧ commV P₁ ≤ fixV P₂ ∧
    commV P₂ ≤ fixV P₁ ∧ ∃ σ ∈ Tb, conjBy σ P₁ = P₂

@[expose] def Nonsingular (P : Subgroup (MulAut V)) : Set V :=
  {v | v ≠ 1 ∧ ∃ a ∈ P, a ≠ 1 ∧ a v = v}

end Defs

namespace E9Z4Str

variable {V : Type} [CommGroup V] [Finite V] {X Tb P P₁ P₂ : Subgroup (MulAut V)}

omit [Finite V] in
theorem exists_planePair (h : E9Z4Str X Tb P) : ∃ P₁ P₂, PlanePair Tb P P₁ P₂ := h.planes

omit [Finite V] in
theorem Tb_comm (h : E9Z4Str X Tb P) {a b : MulAut V} (ha : a ∈ Tb) (hb : b ∈ Tb) :
    a * b = b * a := by
  obtain ⟨g, hg⟩ := h.cyclic_Tb.exists_generator
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨a, ha⟩)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨b, hb⟩)
  have hi' : (g : MulAut V) ^ i = a := congrArg Subtype.val hi
  have hj' : (g : MulAut V) ^ j = b := congrArg Subtype.val hj
  rw [← hi', ← hj']
  exact ((Commute.refl (g : MulAut V)).zpow_zpow i j).eq

theorem rk_commV_plane (h : E9Z4Str X Tb P) (hp : PlanePair Tb P P₁ P₂) :
    rk (commV P₁) = 2 ∧ rk (commV P₂) = 2 := by
  obtain ⟨-, -, -, -, -, hdisj, hcsup, -, -, σ, -, hσP⟩ := hp
  have hrkBA : rk (commV P₂) = rk (commV P₁) := by rw [← hσP, rk_commV_conjBy]
  have hinf : commV P₁ ⊓ commV P₂ = ⊥ := disjoint_iff.mp hdisj
  have hsum := rk_sup_add_rk_inf (commV P₁) (commV P₂)
  rw [hcsup, hinf, rk_top, rk_bot, h.rk_four] at hsum
  omega

theorem plane_inf_eq_bot (h : E9Z4Str X Tb P) (hp : PlanePair Tb P P₁ P₂) : P₁ ⊓ P₂ = ⊥ := by
  have hrk := (h.rk_commV_plane hp).1
  obtain ⟨-, -, hc₁, hc₂, -, hdisj, -, -, -, -⟩ := hp
  have hdvd : Nat.card ↥(P₁ ⊓ P₂) ∣ 3 := hc₁ ▸ Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with e | e
  · exact Subgroup.card_eq_one.mp e
  · have h1 : P₁ ⊓ P₂ = P₁ := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [e, hc₁])
    have h2 : P₁ ⊓ P₂ = P₂ := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [e, hc₂])
    have h12 : P₁ = P₂ := h1.symm.trans h2
    rw [← h12] at hdisj
    rw [disjoint_self.mp hdisj, rk_bot] at hrk
    omega

theorem zpowers_le_normalizer_of_le (h : E9Z4Str X Tb P) {t : MulAut V} (ht : t ∈ X)
    (ht2 : orderOf t = 2) {Q : Subgroup (MulAut V)} (hQ : Q ≤ P) :
    Subgroup.zpowers t ≤ Subgroup.normalizer (Q : Set (MulAut V)) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
  have htsq : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
  intro q
  constructor
  · intro hq
    rw [h.inverts_of_involution ht ht2 q (hQ hq)]
    exact Q.inv_mem hq
  · intro hq
    have e : t * (t * q * t⁻¹) * t⁻¹ = q := by
      rw [show t * (t * q * t⁻¹) * t⁻¹ = t ^ 2 * q * (t ^ 2)⁻¹ by rw [pow_two]; group, htsq]
      group
    have := Q.inv_mem hq
    rwa [← h.inverts_of_involution ht ht2 _ (hQ hq), e] at this

theorem card_plane_S3 (h : E9Z4Str X Tb P) {t : MulAut V} (ht : t ∈ Tb) (ht2 : orderOf t = 2)
    {Q : Subgroup (MulAut V)} (hQ : Q ≤ P) (hQ3 : Nat.card Q = 3) :
    Nat.card ↥(Q ⊔ Subgroup.zpowers t) = 6 := by
  have hzt : Subgroup.zpowers t ≤ Tb := Subgroup.zpowers_le.mpr ht
  have hprod := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
    (h.zpowers_le_normalizer_of_le (h.Tb_le_X ht) ht2 hQ)
  have hinf : Subgroup.zpowers t ⊓ Q = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun y hy => ?_
    have : y ∈ P ⊓ Tb := ⟨hQ hy.2, hzt hy.1⟩
    rwa [h.P_inf_Tb, Subgroup.mem_bot] at this
  rw [hinf, Subgroup.card_bot, Nat.card_zpowers, ht2, hQ3, mul_one, sup_comm] at hprod
  omega

end E9Z4Str

end CFSG.Quasithin
