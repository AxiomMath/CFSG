module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxLinear

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.LinearGroups
open scoped commutatorElement

section Root

variable {n : ℕ} {K : Type} [Field K]

@[expose] def rootRing (H : Subgroup (SpecialLinearGroup (Fin n) K)) : Set K :=
  {c | ∀ (i j : Fin n) (hij : i ≠ j), SpecialLinearGroup.transvection hij c ∈ H}

theorem transvection_mem_slSub {k : Subfield K} {i j : Fin n} (hij : i ≠ j) {c : K} (hc : c ∈ k) :
    SpecialLinearGroup.transvection hij c ∈ slSub n k := by
  rw [mem_slSub]
  intro a b
  rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases h1 : a = b <;> by_cases h2 : i = a <;> by_cases h3 : j = b <;> simp_all [k.one_mem,
    k.zero_mem]

variable {H : Subgroup (SpecialLinearGroup (Fin n) K)} {k : Subfield K}

theorem commutatorElement_mem' {x y : SpecialLinearGroup (Fin n) K} (hx : x ∈ H) (hy : y ∈ H) :
    ⁅x, y⁆ ∈ H := by
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)

theorem exists_fin_ne_ne' (hn : 3 ≤ n) (a b : Fin n) : ∃ c : Fin n, c ≠ a ∧ c ≠ b := by
  by_contra hcon
  push Not at hcon
  have h0 := hcon ⟨0, by omega⟩
  have h1 := hcon ⟨1, by omega⟩
  have h2 := hcon ⟨2, by omega⟩
  simp only [Fin.ext_iff, ne_eq] at h0 h1 h2
  omega

theorem root_mem_of_root_mem (hk : slSub n k ≤ H) (hn : 3 ≤ n) {a : K} {i j i' j' : Fin n}
    (hij : i ≠ j) (hij' : i' ≠ j') (h : SpecialLinearGroup.transvection hij a ∈ H) :
    SpecialLinearGroup.transvection hij' a ∈ H := by
  have h1 : ∀ {i j : Fin n} (hij : i ≠ j), SpecialLinearGroup.transvection hij (1 : K) ∈ H :=
    fun hij => hk (transvection_mem_slSub hij k.one_mem)
  let P : Fin n → Fin n → Prop := fun i j =>
    ∃ hij : i ≠ j, SpecialLinearGroup.transvection hij a ∈ H
  have tgt : ∀ {i l j : Fin n}, P i l → i ≠ j → l ≠ j → P i j := by
    rintro i l j ⟨hil, hx⟩ hij hlj
    refine ⟨hij, ?_⟩
    have := commutatorElement_mem' (H := H) hx (h1 hlj)
    rwa [SpecialLinearGroup.commutatorElement_transvection hil hlj hij, mul_one] at this
  have src : ∀ {i l j : Fin n}, P l j → i ≠ l → i ≠ j → P i j := by
    rintro i l j ⟨hlj, hx⟩ hil hij
    refine ⟨hij, ?_⟩
    have := commutatorElement_mem' (H := H) (h1 hil) hx
    rwa [SpecialLinearGroup.commutatorElement_transvection hil hlj hij, one_mul] at this
  have hP : P i j := ⟨hij, h⟩
  have key : P i' j' := by
    by_cases hc : i' = j
    · by_cases hd : j' = i
      · obtain ⟨m, hmi, hmj⟩ := exists_fin_ne_ne' hn i j
        have hA : P i m := tgt hP (Ne.symm hmi) (Ne.symm hmj)
        have hB : P j m := src hA (Ne.symm hij) (Ne.symm hmj)
        have hC : P j i := tgt hB (Ne.symm hij) hmi
        rw [hc, hd]
        exact hC
      · have hjj' : j ≠ j' := hc ▸ hij'
        have hA : P i j' := tgt hP (Ne.symm hd) hjj'
        have hB : P j j' := src hA (Ne.symm hij) hjj'
        rw [hc]
        exact hB
    · have hA : P i' j := by
        by_cases hii : i' = i
        · rw [hii]
          exact hP
        · exact src hP hii hc
      by_cases he : j' = j
      · rw [he]
        exact hA
      · exact tgt hA hij' (Ne.symm he)
  obtain ⟨_, hx⟩ := (key : ∃ hij : i' ≠ j', SpecialLinearGroup.transvection hij a ∈ H)
  exact hx

def rootSubring (hk : slSub n k ≤ H) (hn : 3 ≤ n) : Subring K where
  carrier := rootRing H
  zero_mem' := fun i j hij => by
    rw [SpecialLinearGroup.transvection_coeff_zero]
    exact H.one_mem
  one_mem' := fun i j hij => hk (transvection_mem_slSub hij k.one_mem)
  add_mem' := fun {a b} ha hb i j hij => by
    rw [SpecialLinearGroup.transvection_add]
    exact H.mul_mem (ha i j hij) (hb i j hij)
  neg_mem' := fun {a} ha i j hij => by
    rw [← SpecialLinearGroup.transvection_inv]
    exact H.inv_mem (ha i j hij)
  mul_mem' := fun {a b} ha hb i l hil => by
    obtain ⟨j, hji, hjl⟩ := exists_fin_ne_ne' hn i l
    have h := commutatorElement_mem' (H := H) (ha i j (Ne.symm hji)) (hb j l hjl)
    rwa [SpecialLinearGroup.commutatorElement_transvection (Ne.symm hji) hjl hil] at h

theorem le_rootSubring (hk : slSub n k ≤ H) (hn : 3 ≤ n) {c : K} (hc : c ∈ k) :
    c ∈ rootSubring hk hn := fun _ _ hij => hk (transvection_mem_slSub hij hc)

def subringToSubfield [Finite K] (S : Subring K) : Subfield K :=
  { S with
    inv_mem' := fun x hx => by
      classical
      have := Fintype.ofFinite K
      by_cases hx0 : x = 0
      · rw [hx0, _root_.inv_zero]
        exact S.zero_mem
      · have h1 : x ^ (Fintype.card K - 1) = 1 := FiniteField.pow_card_sub_one_eq_one x hx0
        have h2 : 2 ≤ Fintype.card K := by
          have := Fintype.one_lt_card (α := K)
          omega
        have hq : Fintype.card K - 2 + 1 = Fintype.card K - 1 := by omega
        have hmul : x * x ^ (Fintype.card K - 2) = 1 := by
          rw [← pow_succ', hq]
          exact h1
        have h3 : x⁻¹ = x ^ (Fintype.card K - 2) := (eq_inv_of_mul_eq_one_right hmul).symm
        rw [h3]
        exact S.pow_mem hx _ }

theorem subfield_eq_or_eq_top [Finite K] {S : Subfield K} (hkS : k ≤ S) {p : ℕ} (hp : p.Prime)
    (hK : Nat.card K = Nat.card k ^ p) : S = k ∨ S = ⊤ := by
  have hfin : Module.finrank k K = p := by
    have h := Module.natCard_eq_pow_finrank (K := k) (V := K)
    have h2 : 2 ≤ Nat.card k := Finite.one_lt_card
    rw [hK] at h
    exact (Nat.pow_right_injective h2 h).symm
  let F : IntermediateField k K := S.toIntermediateField fun x => hkS x.2
  have hdvd : Module.finrank k F ∣ p := by
    have := IntermediateField.finrank_dvd_of_le_right (K := k) (L := K) (F := F) (E := ⊤)
      le_top
    rwa [IntermediateField.finrank_top', hfin] at this
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | h2
  · left
    have hF : F = ⊥ := IntermediateField.finrank_eq_one_iff.mp h1
    refine le_antisymm (fun x hx => ?_) hkS
    have hxF : x ∈ F := hx
    rw [hF] at hxF
    obtain ⟨y, rfl⟩ := IntermediateField.mem_bot.mp hxF
    exact y.2
  · right
    have hF : F = ⊤ := IntermediateField.eq_of_le_of_finrank_eq le_top (by
      rw [IntermediateField.finrank_top', hfin, h2])
    refine eq_top_iff.mpr fun x _ => ?_
    have : x ∈ F := by rw [hF]; trivial
    exact this

theorem eq_top_of_root_not_mem [Finite K] (hk : slSub n k ≤ H) (hn : 3 ≤ n) {p : ℕ}
    (hp : p.Prime) (hK : Nat.card K = Nat.card k ^ p) {a : K} (ha : a ∉ k) {i j : Fin n}
    (hij : i ≠ j) (h : SpecialLinearGroup.transvection hij a ∈ H) : H = ⊤ := by
  have haR : a ∈ rootSubring hk hn := fun i' j' hij' => root_mem_of_root_mem hk hn hij hij' h
  let S : Subfield K := subringToSubfield (rootSubring hk hn)
  have hkS : k ≤ S := fun c hc => le_rootSubring hk hn hc
  rcases subfield_eq_or_eq_top hkS hp hK with hS | hS
  · exact absurd (hS ▸ (haR : a ∈ S)) ha
  · rw [eq_top_iff, ← special_linear_elementary_generation (n := n) (K := K),
      Subgroup.closure_le]
    rintro _ ⟨i', j', hij', c, rfl⟩
    have hc : c ∈ S := hS ▸ Subfield.mem_top c
    exact (hc : c ∈ rootSubring hk hn) i' j' hij'

end Root

end CFSG.RankThree.PartOne.CTP
