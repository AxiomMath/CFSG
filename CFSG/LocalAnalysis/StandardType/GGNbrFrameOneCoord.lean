module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType

namespace NbrFrameOne

open Multiplicative

variable {p k : ℕ}

@[expose] def negAut (i : Fin k) : MulAut (Multiplicative (Fin k → ZMod p)) :=
  (MulAut.congr (MulEquiv.funMultiplicative (Fin k) (ZMod p)).symm) (SpCoord.sgnAut i)

theorem negAut_apply (i : Fin k) (t : Fin k → ZMod p) :
    negAut i (ofAdd t) = ofAdd (Function.update t i (-t i)) := by
  rw [negAut, MulAut.congr_apply]
  simp [SpCoord.sgnAut_apply]
  funext j
  by_cases hj : j = i <;> simp [hj]

theorem negAut_sq (i : Fin k) :
    (negAut i : MulAut (Multiplicative (Fin k → ZMod p))) ^ 2 = 1 := by
  rw [negAut, ← map_pow, SpCoord.sgnAut_sq, map_one]

theorem card_fix_negAut (hp : p.Prime) (hp2 : p ≠ 2) (i : Fin k) :
    Nat.card {f : Multiplicative (Fin k → ZMod p) // negAut i f = f} * p =
      Nat.card (Multiplicative (Fin k → ZMod p)) := by
  set e := MulEquiv.funMultiplicative (Fin k) (ZMod p) with he
  have hcard : Nat.card {f : Multiplicative (Fin k → ZMod p) // negAut i f = f} =
      Nat.card {f : Fin k → Multiplicative (ZMod p) // SpCoord.sgnAut i f = f} := by
    refine Nat.card_congr (Equiv.subtypeEquiv e.toEquiv ?_)
    intro f
    change ((MulAut.congr e.symm (SpCoord.sgnAut i)) f = f) ↔
      SpCoord.sgnAut i (e f) = e f
    rw [MulAut.congr_apply]
    constructor
    · intro h
      have := congrArg e h
      simpa using this
    · intro h
      have := congrArg e.symm h
      simpa using this
  rw [hcard, SpCoord.card_fix_sgnAut hp hp2 i]
  exact (Nat.card_congr e.toEquiv).symm

@[expose] def swapAut (i j : Fin k) : MulAut (Multiplicative (Fin k → ZMod p)) :=
  (MulAut.congr (MulEquiv.funMultiplicative (Fin k) (ZMod p)).symm)
    (SpCoord.permAut (Equiv.swap i j))

theorem swapAut_apply (i j : Fin k) (t : Fin k → ZMod p) :
    swapAut i j (ofAdd t) = ofAdd (t ∘ Equiv.swap i j) := by
  rw [swapAut, MulAut.congr_apply]
  simp [SpCoord.permAut_apply, Equiv.swap_inv]
  rfl

theorem swapAut_sq (i j : Fin k) :
    (swapAut i j : MulAut (Multiplicative (Fin k → ZMod p))) ^ 2 = 1 := by
  rw [swapAut, ← map_pow, SpCoord.permAut_swap_sq, map_one]

theorem card_fix_swapAut (hp : p.Prime) {i j : Fin k} (hij : i ≠ j) :
    Nat.card {f : Multiplicative (Fin k → ZMod p) // swapAut i j f = f} * p =
      Nat.card (Multiplicative (Fin k → ZMod p)) := by
  have := Fact.mk hp
  let δ : Multiplicative (Fin k → ZMod p) →* Multiplicative (ZMod p) :=
    { toFun := fun f => ofAdd (toAdd f i - toAdd f j)
      map_one' := by simp
      map_mul' := by
        intro f g
        simp only [toAdd_mul, Pi.add_apply]
        rw [← ofAdd_add]
        congr 1
        ring }
  have hδapp : ∀ f : Multiplicative (Fin k → ZMod p),
      δ f = ofAdd (toAdd f i - toAdd f j) := fun _ => rfl
  have hker : Nat.card δ.ker =
      Nat.card {f : Multiplicative (Fin k → ZMod p) // swapAut i j f = f} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
    intro f
    rw [MonoidHom.mem_ker, hδapp, ← ofAdd_zero, ofAdd.injective.eq_iff, sub_eq_zero]
    constructor
    · intro h
      rw [← ofAdd_toAdd f, swapAut_apply, ofAdd.injective.eq_iff]
      funext l
      by_cases hl : l = i
      · subst hl
        simp [Equiv.swap_apply_left, h]
      · by_cases hl2 : l = j
        · subst hl2
          simp [Equiv.swap_apply_right, h]
        · simp [Equiv.swap_apply_of_ne_of_ne hl hl2]
    · intro h
      have h' := congrArg (fun x : Multiplicative (Fin k → ZMod p) => toAdd x i) h
      rw [← ofAdd_toAdd f, swapAut_apply] at h'
      simp only [toAdd_ofAdd, Function.comp_apply, Equiv.swap_apply_left] at h'
      exact h'.symm
  have hrange : δ.range = ⊤ := by
    rw [eq_top_iff]
    intro x _
    refine ⟨ofAdd (Pi.single i (toAdd x) : Fin k → ZMod p), ?_⟩
    show ofAdd (toAdd (ofAdd (Pi.single i (toAdd x) : Fin k → ZMod p)) i -
      toAdd (ofAdd (Pi.single i (toAdd x) : Fin k → ZMod p)) j) = x
    rw [toAdd_ofAdd, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij)]
    simpa using ofAdd_toAdd x
  have hcard_range : Nat.card δ.range = p := by
    rw [hrange]
    calc Nat.card (⊤ : Subgroup (Multiplicative (ZMod p)))
        = Nat.card (Multiplicative (ZMod p)) :=
          Nat.card_congr Subgroup.topEquiv.toEquiv
      _ = Nat.card (ZMod p) := Nat.card_congr (Multiplicative.toAdd (α := ZMod p))
      _ = p := Nat.card_zmod p
  have h := TableB.card_range_mul_card_ker δ
  rw [hker, hcard_range, mul_comm] at h
  exact h

theorem orderOf_negAut_mul_swapAut (hp : p.Prime) (hp2 : p ≠ 2) {i j : Fin k} (hij : i ≠ j) :
    orderOf (negAut i * swapAut i j :
      MulAut (Multiplicative (Fin k → ZMod p))) = 4 := by
  have := Fact.mk hp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let w : MulAut (Multiplicative (Fin k → ZMod p)) := negAut i * swapAut i j
  have hconj : (swapAut i j * negAut i * swapAut i j :
      MulAut (Multiplicative (Fin k → ZMod p))) = negAut j := by
    refine MulEquiv.ext fun f => ?_
    rw [← ofAdd_toAdd f, MulAut.mul_apply, MulAut.mul_apply, swapAut_apply, negAut_apply,
      swapAut_apply, negAut_apply, ofAdd.injective.eq_iff]
    funext l
    by_cases hl : l = i
    · subst hl
      simp [Equiv.swap_apply_left, Equiv.swap_apply_right, hij, Ne.symm hij,
        Function.update_of_ne, Function.update_self]
    · by_cases hl2 : l = j
      · subst hl2
        simp [Equiv.swap_apply_left, Equiv.swap_apply_right, hij, Ne.symm hij,
          Function.update_of_ne, Function.update_self]
      · simp [Equiv.swap_apply_of_ne_of_ne hl hl2, Function.update_of_ne hl,
          Function.update_of_ne hl2]
  have hcomm : (negAut i * negAut j : MulAut (Multiplicative (Fin k → ZMod p))) =
      negAut j * negAut i := by
    refine MulEquiv.ext fun f => ?_
    rw [← ofAdd_toAdd f, MulAut.mul_apply, MulAut.mul_apply, negAut_apply, negAut_apply,
      negAut_apply, negAut_apply, ofAdd.injective.eq_iff]
    funext l
    by_cases hl : l = i
    · subst hl
      simp [hij, Ne.symm hij, Function.update_of_ne, Function.update_self]
    · by_cases hl2 : l = j
      · subst hl2
        simp [hij, Ne.symm hij, Function.update_of_ne, Function.update_self]
      · simp [Function.update_of_ne hl, Function.update_of_ne hl2]
  have hw2 : w ^ 2 = negAut i * negAut j := by
    change (negAut i * swapAut i j) ^ 2 = negAut i * negAut j
    rw [pow_two]
    calc (negAut i * swapAut i j) * (negAut i * swapAut i j)
        = negAut i * (swapAut i j * negAut i * swapAut i j) := by group
      _ = negAut i * negAut j := by rw [hconj]
  have hw4 : w ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hw2, pow_two]
    calc (negAut i * negAut j) * (negAut i * negAut j)
        = negAut i * (negAut j * negAut i) * negAut j := by group
      _ = negAut i * (negAut i * negAut j) * negAut j := by rw [hcomm]
      _ = (negAut i * negAut i) * (negAut j * negAut j) := by group
      _ = 1 := by rw [← pow_two, negAut_sq, ← pow_two, negAut_sq, mul_one]
  have hw2ne : w ^ 2 ≠ 1 := by
    intro h
    have h1 : (w ^ 2) (ofAdd (Pi.single j (1 : ZMod p))) =
        (1 : MulAut (Multiplicative (Fin k → ZMod p)))
          (ofAdd (Pi.single j (1 : ZMod p))) := by rw [h]
    rw [hw2, MulAut.mul_apply, negAut_apply, negAut_apply, MulAut.one_apply,
      ofAdd.injective.eq_iff] at h1
    simp [hij, Ne.symm hij, Function.update_of_ne, Function.update_self,
      Pi.single_eq_same] at h1
    have h2 : (2 : ZMod p) = 0 := by
      have h := congrArg (fun v : Fin k → ZMod p => v j) h1
      simp [hij, Ne.symm hij, Function.update_of_ne, Function.update_self,
        Pi.single_eq_same] at h
      linear_combination -h
    exact (SpCoord.coord_two_ne_zero hp hp2) h2
  have hdiv : orderOf w ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr hw4
  have hndiv2 : ¬ orderOf w ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact hw2ne
  have hge : 1 ≤ orderOf w := Nat.pos_of_dvd_of_pos hdiv (by norm_num)
  have hle : orderOf w ≤ 4 := Nat.le_of_dvd (by norm_num) hdiv
  have hnot1 : orderOf w ≠ 1 := by
    intro h
    exact hndiv2 (by rw [h]; norm_num)
  have hnot2 : orderOf w ≠ 2 := by
    intro h
    exact hndiv2 (by rw [h])
  have hnot3 : orderOf w ≠ 3 := by
    intro h
    exact absurd (h ▸ hdiv) (by norm_num)
  have hord : orderOf w = 4 := by omega
  exact hord

end NbrFrameOne

theorem ggIsReflection_congr {p : ℕ} {G : Type} [Group G] {A : Subgroup G} {V : Type}
    [Group V] (Θ : V ≃* ↥A) {s : MulAut V} (hs : s ^ 2 = 1)
    (hfix : Nat.card {f : V // s f = f} * p = Nat.card V) :
    GGIsReflection p (MulAut.congr Θ s) := by
  refine ⟨by rw [← map_pow, hs, map_one], ?_⟩
  have h1 : Nat.card {a : ↥A // MulAut.congr Θ s a = a} =
      Nat.card {f : V // s f = f} := by
    refine Nat.card_congr (Equiv.subtypeEquiv Θ.symm.toEquiv fun a => ?_)
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.toEquiv_eq_coe,
      MulEquiv.coe_toEquiv]
    constructor
    · intro h
      have h' := congrArg Θ.symm h
      rwa [MulEquiv.symm_apply_apply] at h'
    · intro h
      rw [h, MulEquiv.apply_symm_apply]
  rw [h1, hfix]
  exact Nat.card_congr Θ.toEquiv

end CFSG.StandardType

end
