module

public import CFSG.Quasithin.Vol2.Ch8Sec2Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

section L829TA

variable {G : Type} [Group G]

theorem le_normalizer_sup_829 {T A B : Subgroup G} (hA : T ≤ Subgroup.normalizer (A : Set G))
    (hB : T ≤ Subgroup.normalizer (B : Set G)) :
    T ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA ht),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB ht)]

theorem conjSub_le_ch82I_of_mem_sup {V Q : Subgroup G} {h : G}
    (hIQ : ch82I V h ≤ Subgroup.normalizer (Q : Set G))
    (hQV : Q ≤ Subgroup.normalizer (V : Set G)) {g : G} (hg : g ∈ ch82I V h ⊔ Q) :
    B6.conjSub g V ≤ ch82I V h := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hIQ] at hg
  obtain ⟨i, hi, q, hq, rfl⟩ := hg
  rw [B6.conjSub_mul, B6.conjSub_eq_self (hQV hq)]
  intro x hx
  rw [B6.mem_conjSub] at hx
  have h1 : i * (i⁻¹ * x * i) * i⁻¹ ∈ ch82I V h :=
    mul_mem (mul_mem hi ((le_sup_left : V ≤ ch82I V h) hx)) (inv_mem hi)
  simpa [mul_assoc] using h1

theorem le_normalizer_ch82I_of_sup {V Q T : Subgroup G} {h : G} (hh : h ∈ ch82I V h)
    (hIQ : ch82I V h ≤ Subgroup.normalizer (Q : Set G))
    (hQV : Q ≤ Subgroup.normalizer (V : Set G)) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hT : T ≤ Subgroup.normalizer ((ch82I V h ⊔ Q : Subgroup G) : Set G)) :
    T ≤ Subgroup.normalizer (ch82I V h : Set G) := by
  have key : ∀ t ∈ T, B6.conjSub t (ch82I V h) ≤ ch82I V h := by
    intro t ht
    have hconj : B6.conjSub t (ch82I V h) = V ⊔ B6.conjSub (t * h * t⁻¹) V := by
      have e1 : B6.conjSub (t * h) V = B6.conjSub (t * h * t⁻¹) V := by
        have e0 : t * h = t * h * t⁻¹ * t := by group
        conv_lhs => rw [e0]
        rw [B6.conjSub_mul, B6.conjSub_eq_self (hTV ht)]
      rw [ch82I, map_sup, B6.conjSub_eq_self (hTV ht), ← B6.conjSub_mul, e1]
    have hg : t * h * t⁻¹ ∈ ch82I V h ⊔ Q :=
      (Subgroup.mem_normalizer_iff.mp (hT ht) h).mp (Subgroup.mem_sup_left hh)
    rw [hconj]
    exact sup_le le_sup_left (conjSub_le_ch82I_of_mem_sup hIQ hQV hg)
  intro t ht
  exact B6.mem_normalizer_of_conjSub_le (key t ht) (key t⁻¹ (inv_mem ht))

theorem le_normalizer_ch82I_of_le_sup {V Q T Y : Subgroup G} {h : G} (hh : h ∈ ch82I V h)
    (hIQ : ch82I V h ≤ Subgroup.normalizer (Q : Set G))
    (hQV : Q ≤ Subgroup.normalizer (V : Set G)) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hTQ : T ≤ Subgroup.normalizer (Q : Set G)) (hTY : T ≤ Subgroup.normalizer (Y : Set G))
    (hVY : V ≤ Subgroup.normalizer (Y : Set G)) (hhY : h ∈ Y ⊔ T)
    (hYI : Y ≤ ch82I V h ⊔ Q) : T ≤ Subgroup.normalizer (ch82I V h : Set G) := by
  have hVh : B6.conjSub h V ≤ V ⊔ Y := by
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTY] at hhY
    obtain ⟨y, hy, t, ht, rfl⟩ := hhY
    rw [B6.conjSub_mul, B6.conjSub_eq_self (hTV ht)]
    intro x hx
    rw [B6.mem_conjSub] at hx
    have e : x = (y * (y⁻¹ * x * y) * y⁻¹ * (y⁻¹ * x * y)⁻¹) * (y⁻¹ * x * y) := by group
    rw [e]
    refine mul_mem (Subgroup.mem_sup_right ?_) (Subgroup.mem_sup_left hx)
    have h1 : (y⁻¹ * x * y) * y⁻¹ * (y⁻¹ * x * y)⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hVY hx) _).mp (inv_mem hy)
    have e2 : y * (y⁻¹ * x * y) * y⁻¹ * (y⁻¹ * x * y)⁻¹ =
        y * ((y⁻¹ * x * y) * y⁻¹ * (y⁻¹ * x * y)⁻¹) := by group
    rw [e2]
    exact mul_mem hy h1
  have heq : ch82I V h ⊔ Q = V ⊔ Y ⊔ Q := by
    refine le_antisymm (sup_le (sup_le (le_sup_left.trans le_sup_left)
      (hVh.trans le_sup_left)) le_sup_right) (sup_le (sup_le ?_ hYI) le_sup_right)
    exact (le_sup_left : V ≤ ch82I V h).trans le_sup_left
  refine le_normalizer_ch82I_of_sup hh hIQ hQV hTV ?_
  rw [heq]
  exact le_normalizer_sup_829 (le_normalizer_sup_829 hTV hTY) hTQ

end L829TA

end CFSG.Quasithin.H13
