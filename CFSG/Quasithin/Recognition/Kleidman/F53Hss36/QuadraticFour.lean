module

public import CFSG.Quasithin.EmptyFaithful.SzF53MTab

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open Equiv CFSG.Quasithin.F53Mod

private theorem fact_sq : ∀ g : Perm (Fin 5), (∀ c : Fin 4 → ZMod 2,
    CFSG.Quasithin.F53Mod.natAct g (CFSG.Quasithin.F53Mod.natAct g c - c) = CFSG.Quasithin.F53Mod.natAct g c - c) → g * g = 1 := by
  decide +kernel

private theorem fact_odd_invol : ∀ σ : Perm (Fin 5), σ * σ = 1 → Perm.sign σ = -1 →
    ∃ i j : Fin 5, i ≠ j ∧ σ = swap i j := by
  decide +kernel

private theorem fact_trans : ∀ i j k l : Fin 5, i ≠ j → k ≠ l → swap i j ≠ swap k l →
    swap i j * swap k l = swap k l * swap i j →
    ∃ c : Fin 4 → ZMod 2, CFSG.Quasithin.F53Mod.natAct (swap k l) (CFSG.Quasithin.F53Mod.natAct (swap i j) c - c) ≠
      CFSG.Quasithin.F53Mod.natAct (swap i j) c - c := by
  decide +kernel

private theorem fact_fix : ∀ x b : Perm (Fin 5), x * x = 1 → b * b = 1 → x * b = b * x →
    Perm.sign x = 1 → Perm.sign b = 1 → x ≠ 1 → b ≠ 1 → x ≠ b →
    ∀ c : Fin 4 → ZMod 2, CFSG.Quasithin.F53Mod.natAct x c = c → CFSG.Quasithin.F53Mod.natAct b c = c := by
  decide +kernel

private theorem toAdd_act (g : Perm (Fin 5)) (w : nat.W) :
    Multiplicative.toAdd (nat.act g w) = CFSG.Quasithin.F53Mod.natAct g (Multiplicative.toAdd w) := rfl

private theorem fixed_iff (g : Perm (Fin 5)) (w : nat.W) :
    nat.act g w = w ↔ CFSG.Quasithin.F53Mod.natAct g (Multiplicative.toAdd w) = Multiplicative.toAdd w := by
  constructor
  · intro h
    have := congrArg Multiplicative.toAdd h
    rwa [toAdd_act] at this
  · intro h
    apply Multiplicative.toAdd.injective
    rw [toAdd_act]
    exact h

private theorem quad_apply {A : Subgroup (Perm (Fin 5))}
    (hq : commW nat A (commW nat A ⊤) = ⊥) {h g : Perm (Fin 5)} (hh : h ∈ A) (hg : g ∈ A)
    (w : nat.W) :
    CFSG.Quasithin.F53Mod.natAct h (CFSG.Quasithin.F53Mod.natAct g (Multiplicative.toAdd w : Fin 4 → ZMod 2) -
        (Multiplicative.toAdd w : Fin 4 → ZMod 2)) =
      CFSG.Quasithin.F53Mod.natAct g (Multiplicative.toAdd w : Fin 4 → ZMod 2) -
        (Multiplicative.toAdd w : Fin 4 → ZMod 2) := by
  have hu : nat.act g w * w⁻¹ ∈ commW nat A ⊤ :=
    Subgroup.subset_closure ⟨g, hg, _, Subgroup.mem_top _, rfl⟩
  have hmem : nat.act h (nat.act g w * w⁻¹) * (nat.act g w * w⁻¹)⁻¹ ∈
      commW nat A (commW nat A ⊤) :=
    Subgroup.subset_closure ⟨h, hh, _, hu, rfl⟩
  rw [hq, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  have e2 : (Multiplicative.toAdd (nat.act g w * w⁻¹) : Fin 4 → ZMod 2) =
      CFSG.Quasithin.F53Mod.natAct g (Multiplicative.toAdd w : Fin 4 → ZMod 2) - (Multiplicative.toAdd w : Fin 4 → ZMod 2) :=
    (show (Multiplicative.toAdd (nat.act g w * w⁻¹) : Fin 4 → ZMod 2) =
        CFSG.Quasithin.F53Mod.natAct g (Multiplicative.toAdd w : Fin 4 → ZMod 2) + -(Multiplicative.toAdd w : Fin 4 → ZMod 2)
      from rfl).trans (sub_eq_add_neg _ _).symm
  have hfix : CFSG.Quasithin.F53Mod.natAct h (Multiplicative.toAdd (nat.act g w * w⁻¹) : Fin 4 → ZMod 2) =
      (Multiplicative.toAdd (nat.act g w * w⁻¹) : Fin 4 → ZMod 2) :=
    congrArg Multiplicative.toAdd hmem
  exact (congrArg (CFSG.Quasithin.F53Mod.natAct h) e2.symm).trans (hfix.trans e2)

private theorem quad_chart {A : Subgroup (Perm (Fin 5))}
    (hq : commW nat A (commW nat A ⊤) = ⊥) {h g : Perm (Fin 5)} (hh : h ∈ A) (hg : g ∈ A)
    (c : Fin 4 → ZMod 2) : CFSG.Quasithin.F53Mod.natAct h (CFSG.Quasithin.F53Mod.natAct g c - c) = CFSG.Quasithin.F53Mod.natAct g c - c :=
  quad_apply hq hh hg (Multiplicative.ofAdd c : nat.W)

private theorem sq_of_mem {A : Subgroup (Perm (Fin 5))}
    (hq : commW nat A (commW nat A ⊤) = ⊥) {g : Perm (Fin 5)} (hg : g ∈ A) : g * g = 1 :=
  fact_sq g fun c => quad_chart hq hg hg c

private theorem comm_of_mem {A : Subgroup (Perm (Fin 5))}
    (hq : commW nat A (commW nat A ⊤) = ⊥) {x y : Perm (Fin 5)} (hx : x ∈ A) (hy : y ∈ A) :
    x * y = y * x := by
  have h1 := mul_eq_one_iff_eq_inv.mp (sq_of_mem hq (Subgroup.mul_mem _ hx hy))
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (sq_of_mem hq hx),
    inv_eq_of_mul_eq_one_right (sq_of_mem hq hy)] at h1
  exact h1

private theorem exists_ne_of_card_four {A : Subgroup (Perm (Fin 5))} (hA : Nat.card A = 4)
    (hq : commW nat A (commW nat A ⊤) = ⊥) {x : Perm (Fin 5)} (hx : x ∈ A) (hx1 : x ≠ 1) :
    ∃ b ∈ A, b ≠ 1 ∧ b ≠ x := by
  by_contra hcon
  push Not at hcon
  have hxsq : x ^ 2 = 1 := by rw [pow_two]; exact sq_of_mem hq hx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub : A ≤ Subgroup.zpowers x := by
    intro b hb
    by_cases h1 : b = 1
    · rw [h1]; exact Subgroup.one_mem _
    · rw [hcon b hb h1]; exact Subgroup.mem_zpowers x
  have h2 := Subgroup.card_le_of_le hsub
  rw [Nat.card_zpowers, orderOf_eq_prime hxsq hx1, hA] at h2
  omega

private theorem le_alt_of_quad {A : Subgroup (Perm (Fin 5))} (hA : Nat.card A = 4)
    (hq : commW nat A (commW nat A ⊤) = ⊥) : A ≤ alternatingGroup (Fin 5) := by
  intro x hx
  rw [Equiv.Perm.mem_alternatingGroup]
  by_contra hodd
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hodd (map_one _)
  have hsx : Perm.sign x = -1 := by
    rcases Int.units_eq_one_or (Perm.sign x) with h | h
    · exact absurd h hodd
    · exact h
  obtain ⟨b, hb, hb1, hbx⟩ := exists_ne_of_card_four hA hq hx hx1
  obtain ⟨y, hy, hyodd, hyx⟩ : ∃ y ∈ A, Perm.sign y = -1 ∧ y ≠ x := by
    rcases Int.units_eq_one_or (Perm.sign b) with hbs | hbs
    · refine ⟨x * b, Subgroup.mul_mem _ hx hb, ?_, ?_⟩
      · rw [map_mul, hsx, hbs, mul_one]
      · intro h
        apply hb1
        exact mul_left_cancel (h.trans (mul_one x).symm)
    · exact ⟨b, hb, hbs, hbx⟩
  obtain ⟨i, j, hij, rfl⟩ := fact_odd_invol x (sq_of_mem hq hx) hsx
  obtain ⟨k, l, hkl, rfl⟩ := fact_odd_invol y (sq_of_mem hq hy) hyodd
  obtain ⟨c, hc⟩ := fact_trans i j k l hij hkl (fun h => hyx h.symm) (comm_of_mem hq hx hy)
  exact hc (quad_chart hq hy hx c)

theorem quadratic_four_nat {A : Subgroup (Perm (Fin 5))} (hA : Nat.card A = 4)
    (hq : commW nat A (commW nat A ⊤) = ⊥) {a : Perm (Fin 5)} (ha : a ∈ A) (ha1 : a ≠ 1) :
    A ≤ alternatingGroup (Fin 5) ∧ fixW nat A = fixW nat (Subgroup.zpowers a) ∧
      (fixW nat A).index = 4 := by
  have hAalt := le_alt_of_quad hA hq
  have hsa : Perm.sign a = 1 := Equiv.Perm.mem_alternatingGroup.mp (hAalt ha)
  have hfix : fixW nat A = fixW nat (Subgroup.zpowers a) := by
    ext w
    rw [mem_fixW_zpowers]
    constructor
    · intro hw
      exact (mem_fixW.mp hw) a ha
    · intro hw
      apply mem_fixW.mpr
      intro b hb
      by_cases hb1 : b = 1
      · subst hb1
        simp
      by_cases hba : b = a
      · rw [hba]; exact hw
      · have hsb : Perm.sign b = 1 := Equiv.Perm.mem_alternatingGroup.mp (hAalt hb)
        rw [fixed_iff] at hw ⊢
        exact fact_fix a b (sq_of_mem hq ha) (sq_of_mem hq hb) (comm_of_mem hq ha hb) hsa hsb
          ha1 hb1 (fun h => hba h.symm) _ hw
  refine ⟨hAalt, hfix, ?_⟩
  rw [hfix]
  have hsq : a ^ 2 = 1 := by rw [pow_two]; exact sq_of_mem hq ha
  have h4 : idx nat a = 4 := by
    rw [idx_nat]
    simp [ha1, hsq]
  exact h4

end CFSG.Quasithin.Kleidman.F53Hss36

end
