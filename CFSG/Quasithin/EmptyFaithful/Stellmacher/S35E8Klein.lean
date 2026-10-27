module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35E8Goal
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35E8Fin

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.E8

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {δ : Geo H M}

omit [Finite G] in
theorem act_one_apply (w : orth.W) : orth.act (1 : Perm (Fin 5)) w = w := by
  rw [map_one]; rfl

omit [Finite G] in
theorem act_mul_apply' (a b : Perm (Fin 5)) (w : orth.W) :
    orth.act (a * b) w = orth.act a (orth.act b w) := by
  rw [map_mul]; rfl

theorem goal_of_klein (hS : Sit H M S) (hδ : vtype δ = false) (c : Ch.Chart δ)
    {Y Vb : Subgroup G} (hY : Y ≤ stab δ) (hV : Vb ≤ stab δ) {v₀ : G} (hv₀ : v₀ ∈ Vb)
    (ht : th c v₀ = swap 0 1) {s : Perm (Fin 5)} (hs : DS (swap 0 1) s)
    (hVb : ∀ v ∈ Vb, th c v = 1 ∨ th c v = swap 0 1)
    (hYb : ∀ y ∈ Y, th c y = 1 ∨ th c y = swap 0 1 ∨ th c y = s ∨ th c y = swap 0 1 * s) :
    Goal δ Y Vb := by
  have hs' := E8.F4 s hs
  set A : Subgroup G := c.pre (fixW orth (Subgroup.zpowers (swap 0 1))) with hA
  set B : Subgroup G := c.pre (fixW orth (Subgroup.zpowers s)) with hB
  have hAmem : ∀ x, x ∈ A ↔ x ∈ Vn δ ∧ orth.act (swap 0 1) (pg c x) = pg c x := fun x => by
    rw [hA, mem_pre_iff', mem_fixW_zpowers]
  have hBmem : ∀ x, x ∈ B ↔ x ∈ Vn δ ∧ orth.act s (pg c x) = pg c x := fun x => by
    rw [hB, mem_pre_iff', mem_fixW_zpowers]
  refine ⟨A, B, c.pre_le_Vn _, c.pre_le_Vn _, ?_, ?_, ?_, ?_⟩
  · refine le_antisymm (sup_le (c.pre_le_Vn _) (c.pre_le_Vn _)) fun x hx => ?_
    obtain ⟨w1, w2, h1, h2, hw⟩ := E8.F3 s hs' (pg c x)
    obtain ⟨x1, hx1, hpx1⟩ := pg_surj c w1
    obtain ⟨x2, hx2, hpx2⟩ := pg_surj c w2
    have hxA : x1 ∈ A := (hAmem x1).mpr ⟨hx1, by rw [hpx1]; exact h1⟩
    have hxB : x2 ∈ B := (hBmem x2).mpr ⟨hx2, by rw [hpx2]; exact h2⟩
    have hz : x * x2⁻¹ * x1⁻¹ ∈ Zv δ := by
      have hm : x * x2⁻¹ * x1⁻¹ ∈ Vn δ :=
        (Vn δ).mul_mem ((Vn δ).mul_mem hx ((Vn δ).inv_mem hx2)) ((Vn δ).inv_mem hx1)
      refine (pg_eq_one_iff c hm).mp ?_
      rw [pg_mul c ((Vn δ).mul_mem hx ((Vn δ).inv_mem hx2)) ((Vn δ).inv_mem hx1),
        pg_mul c hx ((Vn δ).inv_mem hx2), pg_inv c hx2, pg_inv c hx1, hpx1, hpx2, hw]
      group
    have hzA : x * x2⁻¹ * x1⁻¹ ∈ A := by
      rw [hAmem]
      exact ⟨c.le hz, by rw [(pg_eq_one_iff c (c.le hz)).mpr hz]; exact (map_one _)⟩
    have e : x = ((x * x2⁻¹ * x1⁻¹) * x1) * x2 := by group
    rw [e]
    exact Subgroup.mul_mem_sup (A.mul_mem hzA hxA) hxB
  · rw [Subgroup.commutator_le]
    intro v hv a ha
    rw [commutatorElement_def]
    refine (comm_iff c (hV hv) ((hAmem a).mp ha).1).mpr ?_
    rcases hVb v hv with h | h
    · rw [h, act_one_apply]
    · rw [h]; exact ((hAmem a).mp ha).2
  · refine comm_le_of_cases c hY hV (c.pre_le_Vn _) fun y hy b hb => ?_
    have hbs := ((hBmem b).mp hb).2
    rcases hYb y hy with h | h | h | h
    · left; rw [h, act_one_apply]
    · right; exact ⟨v₀, hv₀, by rw [h, ht]⟩
    · left; rw [h]; exact hbs
    · right
      refine ⟨v₀, hv₀, ?_⟩
      rw [h, ht, act_mul_apply', hbs]
  · intro K hK hKQ hbot
    have : ∃ u ∈ K, u ∉ Qv δ := by
      by_contra hcon
      push Not at hcon
      exact hKQ hcon
    obtain ⟨u, huK, huQ⟩ := this
    have hus : u ∈ stab δ := hV (hK huK)
    have h1 : th c u ≠ 1 := fun h' => huQ ((th_eq_one_iff c hS hδ hus).mp h')
    have h2 : th c u = swap 0 1 := (hVb u (hK huK)).resolve_left h1
    have hall : ∀ w : orth.W, orth.act (swap 0 1) w = w := by
      intro w
      obtain ⟨w1, w2, h1', h2', hw⟩ := E8.F3 s hs' w
      obtain ⟨b, hb, hpb⟩ := pg_surj c w2
      have hbB : b ∈ B := (hBmem b).mpr ⟨hb, by rw [hpb]; exact h2'⟩
      have h3 : ⁅b, u⁆ ∈ (⊥ : Subgroup G) :=
        hbot ▸ Subgroup.commutator_mem_commutator hbB huK
      have h4 := act_fixed_of_comm_eq_one c hus hb (Subgroup.mem_bot.mp h3)
      rw [h2, hpb] at h4
      rw [hw, map_mul, h1', h4]
    exact (by decide : (swap (0 : Fin 5) 1) ≠ 1) (S35.Fin.eq_one_of_act_eq_self hall)

end S35.E8

end F53.Stellmacher

end CFSG.Quasithin
