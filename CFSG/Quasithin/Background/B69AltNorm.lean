module

public import CFSG.Quasithin.Background.G6Natural
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin

open G6

namespace B69

section Vec

variable {n : ℕ}

@[expose] def vecOf (T : Finset (Fin n)) : PermMod n :=
  Multiplicative.ofAdd (fun i => if i ∈ T then (1 : ZMod 2) else 0)

@[expose] def vsupp (x : PermMod n) : Finset (Fin n) :=
  Finset.univ.filter fun i => Multiplicative.toAdd x i = 1

theorem zmod_two_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem mem_vsupp {x : PermMod n} {i : Fin n} : i ∈ vsupp x ↔ Multiplicative.toAdd x i = 1 := by
  simp [vsupp]

theorem vecOf_vsupp (x : PermMod n) : vecOf (vsupp x) = x := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [vecOf, toAdd_ofAdd]
  by_cases h : i ∈ vsupp x
  · simp [h, mem_vsupp.1 h]
  · have h1 : Multiplicative.toAdd x i ≠ 1 := fun h' => h (mem_vsupp.2 h')
    rcases zmod_two_cases (Multiplicative.toAdd x i) with h0 | h0
    · simp [h, h0]
    · exact absurd h0 h1

theorem vsupp_vecOf (T : Finset (Fin n)) : vsupp (vecOf T) = T := by
  ext i
  by_cases h : i ∈ T <;> simp [vsupp, vecOf, h]

theorem permAct_vecOf (σ : Equiv.Perm (Fin n)) (T : Finset (Fin n)) :
    permAct n σ (vecOf T) = vecOf (T.image σ) := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [permAct_apply, vecOf, toAdd_ofAdd]
  have : σ⁻¹ i ∈ T ↔ i ∈ T.image σ := by
    constructor
    · intro h
      exact Finset.mem_image.2 ⟨σ⁻¹ i, h, by simp⟩
    · intro h
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h
      simpa using ha
  by_cases h : σ⁻¹ i ∈ T
  · simp only [h, this.1 h, ↓reduceIte]
  · have h2 : i ∉ T.image σ := fun h' => h (this.2 h')
    simp only [h, h2, ↓reduceIte]

theorem toAdd_vecOf (T : Finset (Fin n)) (i : Fin n) :
    Multiplicative.toAdd (vecOf T) i = if i ∈ T then 1 else 0 := rfl

theorem vecOf_injective : Function.Injective (vecOf : Finset (Fin n) → PermMod n) := fun T T' h => by
  rw [← vsupp_vecOf T, ← vsupp_vecOf T', h]

theorem sum_toAdd_eq_card (x : PermMod n) :
    ∑ i, Multiplicative.toAdd x i = ((vsupp x).card : ZMod 2) := by
  conv_lhs => rw [← vecOf_vsupp x]
  simp only [toAdd_vecOf]
  rw [Finset.sum_boole]
  simp

theorem mem_coreMod_iff_even (x : PermMod n) : x ∈ coreMod n ↔ Even (vsupp x).card := by
  rw [mem_coreMod, sum_toAdd_eq_card, ZMod.natCast_eq_zero_iff_even]

@[expose] def uVec (n : ℕ) (i : Fin n) : PermMod n := vecOf (Finset.univ.erase i)

theorem vsupp_uVec (i : Fin n) : vsupp (uVec n i) = Finset.univ.erase i := vsupp_vecOf _

theorem uVec_mem_core (hn : Odd n) (i : Fin n) : uVec n i ∈ coreMod n := by
  rw [mem_coreMod_iff_even, vsupp_uVec, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin]
  exact Nat.Odd.sub_odd hn odd_one

theorem uVec_injective : Function.Injective (uVec n) := by
  intro i j h
  have h2 : Finset.univ.erase i = Finset.univ.erase j := vecOf_injective h
  by_contra hij
  have : i ∈ Finset.univ.erase j := Finset.mem_erase.2 ⟨hij, Finset.mem_univ _⟩
  rw [← h2] at this
  exact (Finset.notMem_erase i _) this

theorem permAct_uVec (σ : Equiv.Perm (Fin n)) (i : Fin n) : permAct n σ (uVec n i) = uVec n (σ i) := by
  unfold uVec
  rw [permAct_vecOf]
  congr 1
  ext j
  simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact fun h => ha (σ.injective h)
  · intro h
    exact ⟨σ.symm j, fun h' => h (by rw [← h']; simp), by simp⟩

@[expose] def uCore (hn : Odd n) (i : Fin n) : ↥(coreMod n) := ⟨uVec n i, uVec_mem_core hn i⟩

theorem coreAct_uCore (hn : Odd n) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    coreAct n σ (uCore hn i) = uCore hn (σ i) :=
  Subtype.ext (permAct_uVec σ i)

end Vec

section Main

variable {n : ℕ}

theorem vsupp_one : vsupp (1 : PermMod n) = ∅ := by
  ext i
  simp [vsupp]

theorem uCore_ne_one (hn : Odd n) (hn5 : 5 ≤ n) (i : Fin n) : uCore hn i ≠ 1 := by
  intro h
  have h1 : uVec n i = 1 := congrArg Subtype.val h
  have h2 : vsupp (uVec n i) = ∅ := by rw [h1, vsupp_one]
  rw [vsupp_uVec] at h2
  have : (Finset.univ.erase i).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  rw [h2, Finset.card_empty] at this
  omega

theorem exists_u_of_normalizes (hn : Odd n) (hn5 : 5 ≤ n) (ψ : MulAut ↥(coreMod n))
    (hψ : ∀ σ ∈ alternatingGroup (Fin n), ∃ τ ∈ alternatingGroup (Fin n),
      ∀ y : ↥(coreMod n), coreAct n σ (ψ y) = ψ (coreAct n τ y)) (i : Fin n) :
    ∃ j, ψ (uCore hn i) = uCore hn j := by
  classical
  by_contra hcon
  push Not at hcon
  set x : ↥(coreMod n) := ψ (uCore hn i) with hx
  set xv : PermMod n := (x : PermMod n) with hxv
  set S : Finset (Fin n) := vsupp xv with hS
  have hSeven : Even S.card := (mem_coreMod_iff_even xv).1 x.2
  have hxne : x ≠ 1 := fun h =>
    uCore_ne_one hn hn5 i (ψ.injective (h.trans (map_one ψ).symm))
  have hSne : S.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    apply hxne
    apply Subtype.ext
    show xv = 1
    rw [← vecOf_vsupp xv, ← hS, hemp]
    apply Multiplicative.toAdd.injective
    funext j
    simp [toAdd_vecOf]
  obtain ⟨m, hm⟩ := hSeven
  have hk : ∃ k, n = 2 * k + 1 := hn
  obtain ⟨k, hk⟩ := hk
  have hwle : S.card ≤ n := by
    simpa using Finset.card_le_univ S
  have hwpos := hSne.card_pos
  have hw3 : S.card + 3 ≤ n := by
    by_cases hw : S.card = n - 1
    · exfalso
      have hc : Sᶜ.card = 1 := by
        rw [Finset.card_compl, Fintype.card_fin]
        omega
      obtain ⟨j, hj⟩ := Finset.card_eq_one.1 hc
      apply hcon j
      apply Subtype.ext
      show xv = uVec n j
      rw [← vecOf_vsupp xv, ← hS]
      unfold uVec
      congr 1
      ext s
      have : s ∈ Sᶜ ↔ s ∈ ({j} : Finset (Fin n)) := by rw [hj]
      simp only [Finset.mem_compl, Finset.mem_singleton, Finset.mem_erase, Finset.mem_univ,
        and_true] at this ⊢
      tauto
    · omega
  set Z : Finset (PermMod n) :=
    Finset.univ.image (fun j : Fin n => ((ψ (uCore hn j) : ↥(coreMod n)) : PermMod n)) with hZ
  have hZcard : Z.card ≤ n := by
    calc Z.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
      _ = n := by simp
  set f : Fin n × Fin n → PermMod n := fun pq => vecOf (insert pq.2 (S.erase pq.1)) with hf
  set Y : Finset (PermMod n) := (S ×ˢ Sᶜ).image f with hY
  have hfinj : Set.InjOn f ↑(S ×ˢ Sᶜ) := by
    rintro ⟨p, q⟩ hpq ⟨p', q'⟩ hpq' h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_compl] at hpq hpq'
    have h2 : insert q (S.erase p) = insert q' (S.erase p') := vecOf_injective h
    have hq : q = q' := by
      have : q ∈ insert q' (S.erase p') := by rw [← h2]; exact Finset.mem_insert_self _ _
      rcases Finset.mem_insert.1 this with h' | h'
      · exact h'
      · exact absurd (Finset.mem_of_mem_erase h') hpq.2
    have hp : p = p' := by
      by_contra hne
      have : p ∈ insert q' (S.erase p') :=
        Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hne, hpq.1⟩)
      rw [← h2] at this
      rcases Finset.mem_insert.1 this with h' | h'
      · exact hpq.2 (h' ▸ hpq.1)
      · exact (Finset.notMem_erase p S) h'
    rw [hq, hp]
  have hYcard : Y.card = S.card * (n - S.card) := by
    rw [hY, Finset.card_image_of_injOn hfinj, Finset.card_product, Finset.card_compl,
      Fintype.card_fin]
  have hYZ : Y ⊆ Z := by
    intro y hy
    obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨hp, hq⟩ := Finset.mem_product.1 hpq
    have hq' : q ∉ S := Finset.mem_compl.1 hq
    have hcomp : 1 < Sᶜ.card := by
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    obtain ⟨r, hr, hrq⟩ := Finset.exists_mem_ne hcomp q
    have hr' : r ∉ S := Finset.mem_compl.1 hr
    have hpq' : p ≠ q := fun h => hq' (h ▸ hp)
    have hpr' : p ≠ r := fun h => hr' (h ▸ hp)
    set σ : Equiv.Perm (Fin n) := Equiv.swap p q * Equiv.swap q r with hσ
    have hσA : σ ∈ alternatingGroup (Fin n) := by
      rw [Equiv.Perm.mem_alternatingGroup, hσ, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hpq',
        Equiv.Perm.sign_swap (Ne.symm hrq)]
      decide
    have himg : S.image σ = insert q (S.erase p) := by
      ext s
      constructor
      · intro hs
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hs
        by_cases hap : a = p
        · subst hap
          have : σ a = q := by
            simp only [hσ, Equiv.Perm.mul_apply]
            rw [Equiv.swap_apply_of_ne_of_ne hpq' hpr', Equiv.swap_apply_left]
          rw [this]
          exact Finset.mem_insert_self _ _
        · have haq : a ≠ q := fun h => hq' (h ▸ ha)
          have har : a ≠ r := fun h => hr' (h ▸ ha)
          have : σ a = a := by
            simp only [hσ, Equiv.Perm.mul_apply]
            rw [Equiv.swap_apply_of_ne_of_ne haq har, Equiv.swap_apply_of_ne_of_ne hap haq]
          rw [this]
          exact Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hap, ha⟩)
      · intro hs
        rcases Finset.mem_insert.1 hs with h | h
        · refine Finset.mem_image.2 ⟨p, hp, ?_⟩
          rw [h]
          simp only [hσ, Equiv.Perm.mul_apply]
          rw [Equiv.swap_apply_of_ne_of_ne hpq' hpr', Equiv.swap_apply_left]
        · obtain ⟨hap, ha⟩ := Finset.mem_erase.1 h
          refine Finset.mem_image.2 ⟨s, ha, ?_⟩
          have haq : s ≠ q := fun h => hq' (h ▸ ha)
          have har : s ≠ r := fun h => hr' (h ▸ ha)
          simp only [hσ, Equiv.Perm.mul_apply]
          rw [Equiv.swap_apply_of_ne_of_ne haq har, Equiv.swap_apply_of_ne_of_ne hap haq]
    obtain ⟨τ, hτA, hτ⟩ := hψ σ hσA
    refine Finset.mem_image.2 ⟨τ i, Finset.mem_univ _, ?_⟩
    have h1 := hτ (uCore hn i)
    rw [coreAct_uCore] at h1
    have h2 : ((coreAct n σ x : ↥(coreMod n)) : PermMod n) = permAct n σ xv := rfl
    have h3 : permAct n σ xv = vecOf (insert q (S.erase p)) := by
      rw [← vecOf_vsupp xv, ← hS, permAct_vecOf, himg]
    show ((ψ (uCore hn (τ i)) : ↥(coreMod n)) : PermMod n) = vecOf (insert q (S.erase p))
    rw [← h3, ← h2]
    exact (congrArg Subtype.val h1).symm
  have hcard := Finset.card_le_card hYZ
  rw [hYcard] at hcard
  have hb : S.card * (n - S.card) ≥ n + 1 := by
    obtain ⟨w, hw⟩ : ∃ w, w = S.card := ⟨_, rfl⟩
    rw [← hw]
    obtain ⟨d, hd⟩ : ∃ d, n = w + 3 + d := ⟨n - (w + 3), by omega⟩
    have hw2 : 2 ≤ w := by omega
    rw [hd, show w + 3 + d - w = d + 3 by omega]
    nlinarith [Nat.mul_le_mul_right d hw2]
  omega

theorem prod_uVec_eq (S : Finset (Fin n)) (hS : Even S.card) :
    ∏ i ∈ S, uVec n i = vecOf S := by
  apply Multiplicative.toAdd.injective
  funext j
  rw [toAdd_prod, Finset.sum_apply, toAdd_vecOf]
  have hu : ∀ i, Multiplicative.toAdd (uVec n i) j = if j ≠ i then (1 : ZMod 2) else 0 := by
    intro i
    simp [uVec, toAdd_vecOf, Finset.mem_erase]
  simp only [hu]
  have h1 : (∑ i ∈ S, (if j ≠ i then (1 : ZMod 2) else 0)) = ((S.erase j).card : ZMod 2) := by
    rw [Finset.sum_boole]
    congr 2
    exact Finset.filter_ne S j
  rw [h1]
  have hc : (S.card : ZMod 2) = 0 := (ZMod.natCast_eq_zero_iff_even).2 hS
  by_cases hj : j ∈ S
  · simp only [hj, ↓reduceIte]
    rw [Finset.card_erase_of_mem hj]
    have : 1 ≤ S.card := Finset.card_pos.2 ⟨j, hj⟩
    rw [Nat.cast_sub this, hc]
    decide
  · simp only [hj, ↓reduceIte]
    rw [Finset.erase_eq_of_notMem hj, hc]

theorem exists_perm_of_normalizes (hn : Odd n) (hn5 : 5 ≤ n) (ψ : MulAut ↥(coreMod n))
    (hψ : ∀ σ ∈ alternatingGroup (Fin n), ∃ τ ∈ alternatingGroup (Fin n),
      ∀ y : ↥(coreMod n), coreAct n σ (ψ y) = ψ (coreAct n τ y)) :
    ∃ ρ : Equiv.Perm (Fin n), ∀ x : ↥(coreMod n), ψ x = coreAct n ρ x := by
  classical
  choose ρ hρ using exists_u_of_normalizes hn hn5 ψ hψ
  have hinj : Function.Injective ρ := fun i j h => by
    have h1 : ψ (uCore hn i) = ψ (uCore hn j) := by rw [hρ i, hρ j, h]
    exact uVec_injective (congrArg Subtype.val (ψ.injective h1))
  have hbij : Function.Bijective ρ := Finite.injective_iff_bijective.1 hinj
  refine ⟨Equiv.ofBijective ρ hbij, fun x => ?_⟩
  have hxprod : x = ∏ i ∈ vsupp (x : PermMod n), uCore hn i := by
    apply Subtype.ext
    have h := map_prod (coreMod n).subtype (fun i => uCore hn i) (vsupp (x : PermMod n))
    refine Eq.trans ?_ h.symm
    exact ((prod_uVec_eq _ ((mem_coreMod_iff_even _).1 x.2)).trans (vecOf_vsupp _)).symm
  conv_lhs => rw [hxprod]
  conv_rhs => rw [hxprod]
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hρ i, coreAct_uCore]
  rfl

end Main

end B69

end CFSG.Quasithin
