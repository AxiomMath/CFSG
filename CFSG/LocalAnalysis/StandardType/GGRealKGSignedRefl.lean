module

public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport

public section

namespace CFSG.StandardType

namespace RealKGSignedRefl

open Multiplicative SpCoord

variable {p k : ℕ}

private noncomputable def dHom (u : MulAut (Fin k → Multiplicative (ZMod p))) :
    (Fin k → Multiplicative (ZMod p)) →* (Fin k → Multiplicative (ZMod p)) where
  toFun f := u f * f⁻¹
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, mul_inv_rev]
    simp [mul_assoc, mul_left_comm, mul_comm]

private theorem dHom_apply (u : MulAut (Fin k → Multiplicative (ZMod p)))
    (f : Fin k → Multiplicative (ZMod p)) : dHom u f = u f * f⁻¹ := rfl

private theorem dHom_ker_card (u : MulAut (Fin k → Multiplicative (ZMod p))) :
    Nat.card (dHom u).ker = Nat.card {f : Fin k → Multiplicative (ZMod p) // u f = f} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun f => ?_)
  rw [MonoidHom.mem_ker, dHom_apply, mul_inv_eq_one, eq_comm]

private theorem dHom_mulSingle_apply {u : MulAut (Fin k → Multiplicative (ZMod p))}
    {π : Equiv.Perm (Fin k)} {ε : Fin k → ZMod p}
    (hπ : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i)) (i j : Fin k) :
    toAdd (dHom u (Pi.mulSingle i (ofAdd 1)) j) =
      (if j = π i then ε i else 0) + (if j = i then -1 else 0) := by
  rw [dHom_apply, toAdd_mul_apply, toAdd_inv_apply, IsSignedPerm.apply_mulSingle hπ i 1,
    toAdd_mulSingle, toAdd_mulSingle]
  by_cases h1 : j = π i <;> by_cases h2 : j = i <;> by_cases h3 : π i = i <;>
    simp [h1, h2, h3]

private theorem dHom_range_card (hp : p.Prime) {u : MulAut (Fin k → Multiplicative (ZMod p))}
    (hcard : Nat.card {f : Fin k → Multiplicative (ZMod p) // u f = f} * p =
      Nat.card (Fin k → Multiplicative (ZMod p))) :
    Nat.card (dHom u).range = p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hV : Nat.card (Fin k → Multiplicative (ZMod p)) =
      Nat.card (dHom u).range * Nat.card (dHom u).ker :=
    (TableB.card_range_mul_card_ker _).symm
  have h2 : Nat.card (dHom u).range * Nat.card (dHom u).ker = p * Nat.card (dHom u).ker := by
    rw [← hV, dHom_ker_card, ← hcard, mul_comm]
  have hKpos : 0 < Nat.card (dHom u).ker := by
    haveI : Nonempty (dHom u).ker := ⟨⟨1, (dHom u).ker.one_mem⟩⟩
    exact Nat.card_pos
  exact Nat.mul_right_cancel hKpos h2

private theorem coord_supp (hp : p.Prime) {x y : Fin k → Multiplicative (ZMod p)} (hy : y ≠ 1)
    (hpow : ∃ c : ℕ, x ^ c = y) : ∀ j, toAdd (y j) = 0 ↔ toAdd (x j) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hc⟩ := hpow
  have h1 : ∀ j, toAdd (y j) = ((c : ℕ) : ZMod p) * toAdd (x j) := fun j => by
    rw [← hc]
    exact toAdd_pow_apply x c j
  have hc0 : ((c : ℕ) : ZMod p) ≠ 0 := by
    intro hc0
    apply hy
    funext j
    apply toAdd.injective
    rw [h1, hc0, zero_mul]
    simp
  intro j
  rw [h1]
  exact ⟨fun h => (mul_eq_zero.mp h).resolve_left hc0, fun ha => by rw [ha, mul_zero]⟩

private theorem mem_supp_self (hp : p.Prime) {u : MulAut (Fin k → Multiplicative (ZMod p))}
    {π : Equiv.Perm (Fin k)} {ε : Fin k → ZMod p}
    (hπ : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i)) (j : Fin k)
    (hj : dHom u (Pi.mulSingle j (ofAdd 1)) ≠ 1) :
    toAdd (dHom u (Pi.mulSingle j (ofAdd 1)) j) ≠ 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  by_cases hpj : π j = j
  · intro h0
    apply hj
    apply eq_of_toAdd_eq
    intro l
    rw [dHom_mulSingle_apply hπ]
    by_cases hl : l = j
    · subst hl
      rw [dHom_mulSingle_apply hπ] at h0
      simpa using h0
    · have h1 : l ≠ π j := by rw [hpj]; exact hl
      simp [hl, h1]
  · rw [dHom_mulSingle_apply hπ]
    have h1 : ¬ (j = π j) := fun h => hpj h.symm
    have hne : ((-1 : ZMod p)) ≠ 0 := coord_sign_ne_zero hp (Or.inr rfl)
    simpa [h1] using hne

private theorem dHom_eq_one_iff (hp : p.Prime) {u : MulAut (Fin k → Multiplicative (ZMod p))}
    {π : Equiv.Perm (Fin k)} {ε : Fin k → ZMod p}
    (hπ : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i))
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (j : Fin k) :
    dHom u (Pi.mulSingle j (ofAdd 1)) = 1 ↔ π j = j ∧ ε j = 1 := by
  constructor
  · intro h
    have huδ : u (Pi.mulSingle j (ofAdd 1)) = Pi.mulSingle j (ofAdd 1) := by
      rw [dHom_apply] at h
      exact mul_inv_eq_one.mp h
    rw [IsSignedPerm.apply_mulSingle hπ j 1] at huδ
    simp only [mul_one] at huδ
    exact mulSingle_ofAdd_eq_iff (coord_sign_ne_zero hp (hε j)) huδ
  · rintro ⟨h1, h2⟩
    apply eq_of_toAdd_eq
    intro l
    rw [dHom_mulSingle_apply hπ]
    by_cases hl : l = j
    · subst hl
      simp [h1, h2]
    · have hl' : l ≠ π j := by rw [h1]; exact hl
      simp [hl, hl']

private theorem toAdd_apply_symm {u : MulAut (Fin k → Multiplicative (ZMod p))}
    {π : Equiv.Perm (Fin k)} {ε : Fin k → ZMod p}
    (hπ : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i)) (f : Fin k → Multiplicative (ZMod p))
    (l : Fin k) : toAdd (u f l) = ε (π.symm l) * toAdd (f (π.symm l)) := by
  have h := hπ f (π.symm l)
  simpa using h

theorem signedRefl_cases (hp : p.Prime) (hp2 : p ≠ 2) {u : MulAut (Fin k → Multiplicative (ZMod p))}
    (hu : IsSignedPerm ⇑u) (hu2 : u * u = 1)
    (hcard : Nat.card {f : Fin k → Multiplicative (ZMod p) // u f = f} * p =
      Nat.card (Fin k → Multiplicative (ZMod p))) :
    (∃ a, u = sgnAut a) ∨ ∃ x : OmPlusIdx k, u = omPlusRefl p x := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨π, ε, hε, hπ⟩ := hu
  have hrange : Nat.card (dHom u).range = p := dHom_range_card hp hcard
  have hex : ∃ i, dHom u (Pi.mulSingle i (ofAdd 1)) ≠ 1 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    have hd : dHom u = 1 := hom_ext_mulSingle fun i => by
      simpa only [MonoidHom.one_apply] using hall i
    have h1 : Nat.card (dHom u).range = 1 := by
      rw [hd]
      have hr : (1 : (Fin k → Multiplicative (ZMod p)) →*
          (Fin k → Multiplicative (ZMod p))).range = ⊥ := by
        ext x
        simp [MonoidHom.mem_range, eq_comm]
      rw [hr]
      exact Subgroup.card_bot
    rw [hrange] at h1
    exact hp.ne_one h1
  obtain ⟨i0, hi0⟩ := hex
  have hpow : ∀ i, dHom u (Pi.mulSingle i (ofAdd 1)) ≠ 1 →
      ∃ c : ℕ, (dHom u (Pi.mulSingle i0 (ofAdd 1))) ^ c = dHom u (Pi.mulSingle i (ofAdd 1)) := by
    intro i hi
    obtain ⟨c, hc⟩ := mem_powers_of_prime_card (G := (dHom u).range) hrange
      (g := ⟨dHom u (Pi.mulSingle i0 (ofAdd 1)), ⟨_, rfl⟩⟩)
      (g' := ⟨dHom u (Pi.mulSingle i (ofAdd 1)), ⟨_, rfl⟩⟩)
      (by intro hc; exact hi0 (congrArg Subtype.val hc))
    exact ⟨c, congrArg Subtype.val hc⟩
  have hsupp : ∀ i, dHom u (Pi.mulSingle i (ofAdd 1)) ≠ 1 → ∀ j,
      toAdd (dHom u (Pi.mulSingle i (ofAdd 1)) j) = 0 ↔
        toAdd (dHom u (Pi.mulSingle i0 (ofAdd 1)) j) = 0 :=
    fun i hi j => coord_supp hp hi (hpow i hi) j
  have hx0 := dHom_mulSingle_apply hπ i0
  have hmem := fun (j : Fin k) (hj : dHom u (Pi.mulSingle j (ofAdd 1)) ≠ 1) =>
    mem_supp_self hp hπ j hj
  by_cases hfix : π i0 = i0
  ·
    have hε0 : ε i0 = -1 := by
      rcases hε i0 with h | h
      · exact absurd ((dHom_eq_one_iff hp hπ hε i0).mpr ⟨hfix, h⟩) hi0
      · exact h
    have hfx : ∀ j, j ≠ i0 → π j = j ∧ ε j = 1 := by
      intro j hj
      refine (dHom_eq_one_iff hp hπ hε j).mp ?_
      by_contra hdj
      refine hmem j hdj ((hsupp j hdj j).mpr ?_)
      rw [hx0 j]
      have hj' : j ≠ π i0 := by rw [hfix]; exact hj
      simp [hj, hj']
    have hπinv : ∀ l, π.symm l = l := fun l => by
      rw [Equiv.symm_apply_eq]
      by_cases hl : l = i0
      · subst hl
        exact hfix.symm
      · exact (hfx l hl).1.symm
    refine Or.inl ⟨i0, MulEquiv.ext fun f => eq_of_toAdd_eq fun l => ?_⟩
    rw [toAdd_apply_symm hπ, hπinv l, sgnAut_apply]
    by_cases hl : l = i0
    · subst hl
      simp only [hε0, Function.update_self, toAdd_inv]
      exact neg_one_mul _
    · simp [Function.update_of_ne hl, (hfx l hl).2]
  ·
    set i1 : Fin k := π i0 with hi1def
    have hi1 : i1 ≠ i0 := hfix
    have hfx : ∀ j, j ≠ i0 → j ≠ i1 → π j = j ∧ ε j = 1 := by
      intro j hj0 hj1
      refine (dHom_eq_one_iff hp hπ hε j).mp ?_
      by_contra hdj
      refine hmem j hdj ((hsupp j hdj j).mpr ?_)
      rw [hx0 j, if_neg hj1, if_neg hj0]
      ring
    have hπi1 : π i1 = i0 := by
      by_contra hne
      have h2 : π i1 ≠ i1 := fun h => hi1 (π.injective (h.trans hi1def))
      exact h2 (π.injective (hfx (π i1) hne h2).1)
    have hεrel : ε i1 * ε i0 = 1 := by
      have h := congrArg (fun g : MulAut (Fin k → Multiplicative (ZMod p)) =>
        g (Pi.mulSingle i0 (ofAdd 1))) hu2
      simp only [MulAut.mul_apply, MulAut.one_apply] at h
      rw [IsSignedPerm.apply_mulSingle hπ i0 1, mul_one, ← hi1def,
        IsSignedPerm.apply_mulSingle hπ i1 (ε i0), hπi1] at h
      have h2 := congrArg (fun f => toAdd (f i0)) h
      simpa [toAdd_mulSingle] using h2
    have hπinv : ∀ l, π.symm l = Equiv.swap i0 i1 l := by
      intro l
      rw [Equiv.symm_apply_eq]
      by_cases h0 : l = i0
      · subst h0
        rw [Equiv.swap_apply_left, hπi1]
      · by_cases h1 : l = i1
        · subst h1
          rw [Equiv.swap_apply_right]
        · rw [Equiv.swap_apply_of_ne_of_ne h0 h1]
          exact ((hfx l h0 h1).1).symm
    have hε1 : ε i1 = ε i0 := by
      rcases hε i0 with h0 | h0 <;> rcases hε i1 with h1 | h1 <;> rw [h0, h1] at hεrel ⊢
      · have h2 : (2 : ZMod p) = 0 := by linear_combination -hεrel
        exact absurd h2 (coord_two_ne_zero hp hp2)
      · have h2 : (2 : ZMod p) = 0 := by linear_combination -hεrel
        exact absurd h2 (coord_two_ne_zero hp hp2)
    have hform : ∀ f l, toAdd (u f l) =
        (if l = i0 ∨ l = i1 then ε i0 else 1) * toAdd (f (Equiv.swap i0 i1 l)) := by
      intro f l
      rw [toAdd_apply_symm hπ, hπinv l]
      by_cases h0 : l = i0
      · subst h0
        rw [Equiv.swap_apply_left, hε1]
        simp
      · by_cases h1 : l = i1
        · subst h1
          rw [Equiv.swap_apply_right]
          simp
        · rw [Equiv.swap_apply_of_ne_of_ne h0 h1, (hfx l h0 h1).2]
          simp [h0, h1]
    rcases lt_or_gt_of_ne hi1 with hlt | hlt
    ·
      refine Or.inr ⟨(⟨(i1, i0), hlt⟩, decide (ε i0 = -1)), MulEquiv.ext fun f =>
        eq_of_toAdd_eq fun l => ?_⟩
      rw [hform]
      rcases hε i0 with he | he
      · have hb : decide (ε i0 = -1) = false := decide_eq_false fun h =>
          coord_zero_ne_one hp (coord_eq_zero_of_eq_neg hp hp2 (he.symm.trans h)).symm
        rw [hb, omPlusRefl_false, permAut_apply, Function.comp_apply, Equiv.swap_inv,
          Equiv.swap_comm, he]
        simp
      · have hb : decide (ε i0 = -1) = true := decide_eq_true he
        rw [hb, omPlusRefl_true, MulAut.mul_apply, MulAut.mul_apply, sgnAut_apply,
          sgnAut_apply, permAut_apply, he]
        by_cases h0 : l = i0
        · subst h0
          simp [Function.update_self, Function.update_of_ne hi1.symm, Equiv.swap_apply_right]
        · by_cases h1 : l = i1
          · subst h1
            simp [Function.update_self, Function.update_of_ne hi1, Equiv.swap_apply_left]
          · simp [Function.update_of_ne h0, Function.update_of_ne h1,
              Equiv.swap_apply_of_ne_of_ne h1 h0, Equiv.swap_apply_of_ne_of_ne h0 h1, h0, h1]
    ·
      refine Or.inr ⟨(⟨(i0, i1), hlt⟩, decide (ε i0 = -1)), MulEquiv.ext fun f =>
        eq_of_toAdd_eq fun l => ?_⟩
      rw [hform]
      rcases hε i0 with he | he
      · have hb : decide (ε i0 = -1) = false := decide_eq_false fun h =>
          coord_zero_ne_one hp (coord_eq_zero_of_eq_neg hp hp2 (he.symm.trans h)).symm
        rw [hb, omPlusRefl_false, permAut_apply, Function.comp_apply, Equiv.swap_inv, he]
        simp
      · have hb : decide (ε i0 = -1) = true := decide_eq_true he
        rw [hb, omPlusRefl_true, MulAut.mul_apply, MulAut.mul_apply, sgnAut_apply,
          sgnAut_apply, permAut_apply, he]
        by_cases h0 : l = i0
        · subst h0
          simp [Function.update_self, Function.update_of_ne hi1.symm, Equiv.swap_apply_left]
        · by_cases h1 : l = i1
          · subst h1
            simp [Function.update_self, Function.update_of_ne hi1, Equiv.swap_apply_right]
          · simp [Function.update_of_ne h0, Function.update_of_ne h1,
              Equiv.swap_apply_of_ne_of_ne h0 h1, h0, h1]

end RealKGSignedRefl

end CFSG.StandardType

end
