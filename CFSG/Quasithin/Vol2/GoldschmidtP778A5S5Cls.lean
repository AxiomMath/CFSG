module

public import CFSG.Quasithin.Vol2.GoldschmidtP778A5S5
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Quasithin.E1.ThinA5

open Equiv Equiv.Perm

theorem isSwap_of_odd_involution :
    ∀ x : Perm (Fin 5), x ^ 2 = 1 → Perm.sign x = -1 → ∃ a b : Fin 5, a ≠ b ∧ x = swap a b := by
  decide +kernel

theorem exists_conj_sA_of_odd_involution :
    ∀ x : Perm (Fin 5), x ^ 2 = 1 → Perm.sign x = -1 → ∃ g : Perm (Fin 5), g * x * g⁻¹ = sA := by
  unfold sA; decide +kernel

theorem disjoint_of_comm_swap : ∀ a b c d : Fin 5, a ≠ b → c ≠ d →
    (∀ p : Fin 5, swap a b (swap c d p) = swap c d (swap a b p)) →
    (¬ ∀ p : Fin 5, swap a b p = swap c d p) → a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
  decide +kernel

theorem exists_perm_four : ∀ a b c d : Fin 5, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ∃ g : Perm (Fin 5), g a = 0 ∧ g b = 1 ∧ g c = 2 ∧ g d = 3 := by
  decide +kernel

theorem pair_conj (x y : Perm (Fin 5)) (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hxs : Perm.sign x = -1)
    (hys : Perm.sign y = -1) (hc : x * y = y * x) (hne : x ≠ y) :
    ∃ g : Perm (Fin 5), g * x * g⁻¹ = sA ∧ g * y * g⁻¹ = sB := by
  obtain ⟨a, b, hab, rfl⟩ := isSwap_of_odd_involution x hx hxs
  obtain ⟨c, d, hcd, rfl⟩ := isSwap_of_odd_involution y hy hys
  have hcomm : ∀ p : Fin 5, swap a b (swap c d p) = swap c d (swap a b p) := fun p => by
    simpa using congrArg (fun f : Perm (Fin 5) => f p) hc
  obtain ⟨h1, h2, h3, h4⟩ := disjoint_of_comm_swap a b c d hab hcd hcomm
    fun h => hne (Equiv.ext h)
  obtain ⟨g, hga, hgb, hgc, hgd⟩ := exists_perm_four a b c d hab h1 h2 h3 h4 hcd
  exact ⟨g, by rw [← Equiv.swap_apply_apply, hga, hgb]; rfl,
    by rw [← Equiv.swap_apply_apply, hgc, hgd]; rfl⟩

theorem eq_top_of_alt_le_of_odd {R : Subgroup (Perm (Fin 5))} (hA : alternatingGroup (Fin 5) ≤ R)
    {x : Perm (Fin 5)} (hx : x ∈ R) (hs : Perm.sign x = -1) : R = ⊤ := by
  refine eq_top_iff.mpr fun σ _ => ?_
  rcases Int.units_eq_one_or (Perm.sign σ) with h | h
  · exact hA (Perm.mem_alternatingGroup.mpr h)
  · have h1 : σ * x⁻¹ ∈ alternatingGroup (Fin 5) := by
      rw [Perm.mem_alternatingGroup, map_mul, map_inv, hs, h]; decide
    have := R.mul_mem (hA h1) hx
    simpa using this

@[expose] def g0 : Perm (Fin 5) := swap 0 2 * swap 1 3

theorem g0_conj_vo : ∀ v ∈ volist, g0 * v * g0⁻¹ ∈ volist := by
  unfold g0 volist sA sB; decide +kernel

theorem c1_sup_conj : C1 ⊔ C1.comap (MulAut.conj g0).toMonoidHom = ⊤ := by
  set J := C1 ⊔ C1.comap (MulAut.conj g0).toMonoidHom with hJ
  have hc1 : ∀ x ∈ c1list, x ∈ J := fun x hx => Subgroup.mem_sup_left hx
  have hc2 : ∀ x : Perm (Fin 5), g0 * x * g0⁻¹ ∈ c1list → x ∈ J := fun x hx =>
    Subgroup.mem_sup_right (Subgroup.mem_comap.mpr hx)
  have h23 : swap 2 3 ∈ J := hc1 _ (by unfold c1list r1list sA sB c3; decide +kernel)
  have h24 : swap 2 4 ∈ J := hc1 _ (by unfold c1list r1list sA sB c3; decide +kernel)
  have h34 : swap 3 4 ∈ J := hc1 _ (by unfold c1list r1list sA sB c3; decide +kernel)
  have h01 : swap 0 1 ∈ J := hc1 _ (by unfold c1list r1list sA sB c3; decide +kernel)
  have h04 : swap 0 4 ∈ J := hc2 _ (by unfold g0 c1list r1list sA sB c3; decide +kernel)
  have h14 : swap 1 4 ∈ J := hc2 _ (by unfold g0 c1list r1list sA sB c3; decide +kernel)
  have h02 : swap 0 2 ∈ J := by
    have : (swap (0 : Fin 5) 2 : Perm (Fin 5)) = swap 2 4 * swap 0 4 * swap 2 4 := by decide
    rw [this]; exact J.mul_mem (J.mul_mem h24 h04) h24
  have h03 : swap 0 3 ∈ J := by
    have : (swap (0 : Fin 5) 3 : Perm (Fin 5)) = swap 3 4 * swap 0 4 * swap 3 4 := by decide
    rw [this]; exact J.mul_mem (J.mul_mem h34 h04) h34
  have h12 : swap 1 2 ∈ J := by
    have : (swap (1 : Fin 5) 2 : Perm (Fin 5)) = swap 2 4 * swap 1 4 * swap 2 4 := by decide
    rw [this]; exact J.mul_mem (J.mul_mem h24 h14) h24
  have h13 : swap 1 3 ∈ J := by
    have : (swap (1 : Fin 5) 3 : Perm (Fin 5)) = swap 3 4 * swap 1 4 * swap 3 4 := by decide
    rw [this]; exact J.mul_mem (J.mul_mem h34 h14) h34
  have hs : ∀ a b : Fin 5, a ≠ b → swap a b ∈ J := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp at hab <;>
      first | assumption | rwa [swap_comm]
  refine eq_top_iff.mpr ?_
  rw [← Equiv.Perm.closure_isSwap]
  rw [Subgroup.closure_le]
  rintro σ ⟨a, b, hab, rfl⟩
  exact hs a b hab

theorem card_dvd_twelve_of_comm_odd {V : Subgroup (Perm (Fin 5))} {x : Perm (Fin 5)}
    (hx2 : x ^ 2 = 1) (hxs : Perm.sign x = -1) (hc : ∀ v ∈ V, v * x = x * v) :
    Nat.card ↥V ∣ 12 := by
  obtain ⟨g, hg⟩ := exists_conj_sA_of_odd_involution x hx2 hxs
  have hle : V.map (MulAut.conj g).toMonoidHom ≤ C1 := by
    rintro _ ⟨v, hv, rfl⟩
    show (MulAut.conj g).toMonoidHom v ∈ c1list
    rw [← c1list_iff]
    have h1 := (hc v hv).symm
    calc sA * (g * v * g⁻¹) = (g * x * g⁻¹) * (g * v * g⁻¹) := by rw [hg]
      _ = g * (x * v) * g⁻¹ := by group
      _ = g * (v * x) * g⁻¹ := by rw [h1]
      _ = (g * v * g⁻¹) * (g * x * g⁻¹) := by group
      _ = (g * v * g⁻¹) * sA := by rw [hg]
  have h1 := Subgroup.card_dvd_of_le hle
  rw [card_C1] at h1
  rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective] at h1

theorem cls {V : Subgroup (Perm (Fin 5))} (hV2 : ∀ x ∈ V, x ^ 2 = 1)
    (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hcard : 2 < Nat.card ↥V) :
    (V ≤ alternatingGroup (Fin 5) ∧ Nat.card ↥V = 4) ∨
      ∃ g : Perm (Fin 5), V.map (MulAut.conj g).toMonoidHom = Vo := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup 2 ↥V := fun y => ⟨1, Subtype.ext (by simpa using hV2 y y.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hpg
  by_cases hA : V ≤ alternatingGroup (Fin 5)
  · left
    refine ⟨hA, ?_⟩
    have hA60 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]; rfl
    have h60 : Nat.card ↥V ∣ 60 := hA60 ▸ Subgroup.card_dvd_of_le hA
    exact card_eq_four_of_two_power hk hcard (Or.inl h60)
  · right
    obtain ⟨x, hxV, hxA⟩ := Set.not_subset.mp hA
    have hxs : Perm.sign x = -1 := by
      rcases Int.units_eq_one_or (Perm.sign x) with h | h
      · exact absurd (Perm.mem_alternatingGroup.mpr h) hxA
      · exact h
    have hx2 := hV2 x hxV
    have h12 : Nat.card ↥V ∣ 12 :=
      card_dvd_twelve_of_comm_odd hx2 hxs (fun v hv => hVc v hv x hxV)
    have hc4 : Nat.card ↥V = 4 := card_eq_four_of_two_power hk hcard (Or.inr h12)
    have hy : ∃ y ∈ V, y ≠ 1 ∧ y ≠ x := by
      by_contra hne
      push Not at hne
      have hsub : (V : Set (Perm (Fin 5))) ⊆ {1, x} := by
        intro y hy
        by_cases h1 : y = 1
        · exact Or.inl h1
        · exact Or.inr (hne y hy h1)
      have h2 : (V : Set (Perm (Fin 5))).ncard ≤ ({1, x} : Set (Perm (Fin 5))).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
      have h3 : ({1, x} : Set (Perm (Fin 5))).ncard ≤ 2 := by
        have := Set.ncard_insert_le (1 : Perm (Fin 5)) {x}
        rwa [Set.ncard_singleton] at this
      have h4 : (V : Set (Perm (Fin 5))).ncard = Nat.card ↥V := by
        rw [← Nat.card_coe_set_eq]; rfl
      omega
    obtain ⟨y, hyV, hy1, hyx⟩ := hy
    obtain ⟨y', hy'V, hy's, hy'x⟩ : ∃ y' ∈ V, Perm.sign y' = -1 ∧ x ≠ y' := by
      by_cases hys : Perm.sign y = -1
      · exact ⟨y, hyV, hys, fun h => hyx h.symm⟩
      · have hy_even : Perm.sign y = 1 := (Int.units_eq_one_or _).resolve_right hys
        refine ⟨x * y, V.mul_mem hxV hyV, ?_, ?_⟩
        · rw [map_mul, hxs, hy_even]; decide
        · intro h
          apply hy1
          have : x * y = x * 1 := by rw [mul_one]; exact h.symm
          exact mul_left_cancel this
    obtain ⟨g, hg1, hg2⟩ := pair_conj x y' hx2 (hV2 y' hy'V) hxs hy's (hVc x hxV y' hy'V) hy'x
    refine ⟨g, ?_⟩
    have hle : Vo ≤ V.map (MulAut.conj g).toMonoidHom := by
      intro z hz
      change z ∈ volist at hz
      unfold volist at hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact Subgroup.one_mem _
      · exact ⟨x, hxV, hg1⟩
      · exact ⟨y', hy'V, hg2⟩
      · refine ⟨x * y', V.mul_mem hxV hy'V, ?_⟩
        show g * (x * y') * g⁻¹ = sA * sB
        rw [← hg1, ← hg2]; group
    exact (Subgroup.eq_of_le_of_card_ge hle (by
      rw [card_Vo, Subgroup.card_map_of_injective (MulAut.conj g).injective, hc4])).symm

end CFSG.Quasithin.E1.ThinA5
