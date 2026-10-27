module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamSVertex

public section

namespace CFSG.Quasithin.F6.GoldAmS

open Equiv

theorem natCard_modEq_fixedPoints {α : Type*} [Finite α] (σ : Perm α) (p : ℕ) [Fact p.Prime]
    (h : σ ^ p = 1) : Nat.card α ≡ Nat.card {a // σ a = a} [MOD p] := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have hσ : σ ^ p ^ 1 = 1 := by rwa [pow_one]
  have key := Equiv.Perm.card_compl_support_modEq hσ
  have h2 : Nat.card {a // σ a = a} = ((Equiv.Perm.support σ)ᶜ).card := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun a => by
      simp [Equiv.Perm.mem_support]))
  rw [h2, Nat.card_eq_fintype_card]
  exact key.symm

theorem eq_or_eq_of_ncard_le_two {α : Type*} {s : Set α} (hs : s.ncard ≤ 2) (hfin : s.Finite)
    {a b : α} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) {q : α} (hq : q ∈ s) :
    q = a ∨ q = b := by
  by_contra h
  rw [not_or] at h
  have hsub : ({q, a, b} : Set α) ⊆ s := by
    intro y hy
    rcases hy with rfl | rfl | rfl
    · exact hq
    · exact ha
    · exact hb
  have h3 : ({q, a, b} : Set α).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_pair hab]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h.1, h.2⟩
  have := Set.ncard_le_ncard hsub hfin
  omega

section Fixed

variable {X : Type*} [Group X] (Q : Subgroup X) [Q.Normal]

def fixedSub (x : X) : Subgroup Q :=
  MonoidHom.eqLocus (MulAut.conjNormal x : MulAut Q).toMonoidHom (MonoidHom.id Q)

theorem mem_fixedSub {x : X} {q : Q} : q ∈ fixedSub Q x ↔ x * (q : X) * x⁻¹ = q := by
  change MulAut.conjNormal x q = q ↔ _
  rw [Subtype.ext_iff, MulAut.conjNormal_apply]

theorem card_fixedSub_eight [Finite Q] (hQ : Nat.card Q = 8) (x : X) (hx : x ^ 3 = 1)
    (hnc : ∃ q ∈ Q, x * q * x⁻¹ ≠ q) : Nat.card (fixedSub Q x) = 2 := by
  have hC : Nat.card (fixedSub Q x) = Nat.card {q : Q // x * (q : X) * x⁻¹ = q} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun q => mem_fixedSub Q)
  have h1 := card_modEq_fixed Q x hx
  rw [← hC, hQ] at h1
  have h2 : Nat.card (fixedSub Q x) ∣ 8 := by
    have := Subgroup.card_subgroup_dvd_card (fixedSub Q x)
    rwa [hQ] at this
  have h4 : Nat.card (fixedSub Q x) ≤ 8 := Nat.le_of_dvd (by norm_num) h2
  have h5 : 0 < Nat.card (fixedSub Q x) := Nat.card_pos
  unfold Nat.ModEq at h1
  interval_cases hc : Nat.card (fixedSub Q x) <;> first | rfl | omega | skip
  exfalso
  have hCtop : fixedSub Q x = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top]
    omega
  obtain ⟨q, hq, hne⟩ := hnc
  have hmem : (⟨q, hq⟩ : Q) ∈ fixedSub Q x := by rw [hCtop]; exact Subgroup.mem_top _
  exact hne ((mem_fixedSub Q).1 hmem)

theorem exists_fixed_elem [Finite Q] (hQ : Nat.card Q = 8) (x : X) (hx : x ^ 3 = 1)
    (hnc : ∃ q ∈ Q, x * q * x⁻¹ ≠ q) :
    ∃ c ∈ Q, c ≠ 1 ∧ c * c = 1 ∧ x * c * x⁻¹ = c ∧
      ∀ q ∈ Q, x * q * x⁻¹ = q → q = 1 ∨ q = c := by
  have hC := card_fixedSub_eight Q hQ x hx hnc
  have hC2 : ∀ c : fixedSub Q x, c * c = 1 := fun c => by
    have := pow_card_eq_one' (G := fixedSub Q x) (x := c)
    rwa [hC, pow_two] at this
  have hnt : Nontrivial (fixedSub Q x) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hC]; norm_num
  obtain ⟨c, hc1⟩ := exists_ne (1 : fixedSub Q x)
  have hcc : (((c : Q) : X)) * ((c : Q) : X) = 1 := by
    have := congrArg (fun y : fixedSub Q x => ((y : Q) : X)) (hC2 c)
    simpa using this
  refine ⟨((c : Q) : X), (c : Q).2, fun h => hc1 (Subtype.ext (Subtype.ext h)), hcc,
    (mem_fixedSub Q).1 c.2, fun q hq hfix => ?_⟩
  by_cases hq1 : q = 1
  · exact Or.inl hq1
  · right
    have hqm : (⟨q, hq⟩ : Q) ∈ fixedSub Q x := (mem_fixedSub Q).2 hfix
    have := eq_of_card_le_two (G := fixedSub Q x) (by rw [hC]) (a := ⟨⟨q, hq⟩, hqm⟩) (b := c)
      (fun h => hq1 (congrArg (fun y : fixedSub Q x => ((y : Q) : X)) h))
      hc1
    exact congrArg (fun y : fixedSub Q x => ((y : Q) : X)) this

end Fixed

section Dichotomy

variable {X : Type*} [Group X] (Q : Subgroup X) [Q.Normal]

omit [Q.Normal] in
theorem card_sq_even [Finite Q] (hQ : Nat.card Q = 8) :
    Nat.card {q : Q // q * q = 1} % 2 = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ : (Equiv.inv Q) ^ 2 = 1 := by
    ext a
    simp [pow_two]
  have h := natCard_modEq_fixedPoints (Equiv.inv Q) 2 hσ
  have h2 : Nat.card {a : Q // (Equiv.inv Q) a = a} = Nat.card {q : Q // q * q = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun a => by
      show a⁻¹ = a ↔ a * a = 1
      exact inv_eq_iff_mul_eq_one))
  rw [h2, hQ] at h
  unfold Nat.ModEq at h
  omega

theorem card_sq_mod_three [Finite Q] (hQ : Nat.card Q = 8) (x : X) (hx : x ^ 3 = 1)
    (hnc : ∃ q ∈ Q, x * q * x⁻¹ ≠ q) :
    Nat.card {q : Q // q * q = 1} ≡ 2 [MOD 3] := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hcQ, hc1, hcc, hxc, hcu⟩ := exists_fixed_elem Q hQ x hx hnc
  let σ : Perm Q := MulAut.toPerm Q (MulAut.conjNormal x)
  have hσ3 : σ ^ 3 = 1 := by
    show (MulAut.toPerm Q (MulAut.conjNormal x)) ^ 3 = 1
    rw [← map_pow, ← map_pow, hx, map_one, map_one]
  have hσq : ∀ q : Q, ((σ q : Q) : X) = x * q * x⁻¹ := fun q => MulAut.conjNormal_apply x q
  have hS : ∀ q : Q, q * q = 1 ↔ σ q * σ q = 1 := by
    intro q
    have h1 : σ q * σ q = σ (q * q) := (map_mul (MulAut.conjNormal x) q q).symm
    rw [h1]
    constructor
    · intro h
      rw [h]
      exact map_one (MulAut.conjNormal x)
    · intro h
      exact σ.injective (h.trans (map_one (MulAut.conjNormal x)).symm)
  let σS : Perm {q : Q // q * q = 1} := σ.subtypePerm (fun q => (hS q).symm)
  have hσS : σS ^ 3 = 1 := by
    show (σ.subtypePerm (fun q => (hS q).symm)) ^ 3 = 1
    rw [Equiv.Perm.subtypePerm_pow]
    ext s
    have := congrArg (fun f : Perm Q => f s.1) hσ3
    simpa using this
  have h := natCard_modEq_fixedPoints σS 3 hσS
  have hC := card_fixedSub_eight Q hQ x hx hnc
  have hC2 : ∀ c : fixedSub Q x, c * c = 1 := fun c => by
    have := pow_card_eq_one' (G := fixedSub Q x) (x := c)
    rwa [hC, pow_two] at this
  have hC2' : ∀ c : fixedSub Q x, (c : Q) * (c : Q) = 1 := fun c => by
    have := congrArg Subtype.val (hC2 c)
    simpa using this
  have hfix : Nat.card {s : {q : Q // q * q = 1} // σS s = s} = 2 := by
    rw [← hC]
    refine Nat.card_congr
      { toFun := fun s => ⟨s.1.1, (mem_fixedSub Q).2 ?_⟩
        invFun := fun c => ⟨⟨c.1, hC2' c⟩, ?_⟩
        left_inv := fun s => ?_
        right_inv := fun c => ?_ }
    · have h1 := congrArg Subtype.val s.2
      have h2 : ((σS s.1 : {q : Q // q * q = 1}) : Q) = σ s.1.1 := rfl
      rw [h2] at h1
      rw [← hσq]
      exact congrArg (fun y : Q => (y : X)) h1
    · apply Subtype.ext
      show σ c.1 = c.1
      apply Subtype.ext
      rw [hσq]
      exact (mem_fixedSub Q).1 c.2
    · rfl
    · rfl
  rw [hfix] at h
  exact h

theorem eight_dichotomy [Finite Q] (hQ : Nat.card Q = 8) (x : X) (hx : x ^ 3 = 1)
    (hnc : ∃ q ∈ Q, x * q * x⁻¹ ≠ q) :
    (∀ q ∈ Q, q * q = 1) ∨
      ∃ c ∈ Q, c ≠ 1 ∧ c * c = 1 ∧ ∀ q ∈ Q, q * q = 1 → q = 1 ∨ q = c := by
  obtain ⟨c, hcQ, hc1, hcc, hxc, hcu⟩ := exists_fixed_elem Q hQ x hx hnc
  have h2 := card_sq_even Q hQ
  have h3 := card_sq_mod_three Q hQ x hx hnc
  have hle : Nat.card {q : Q // q * q = 1} ≤ 8 := by
    rw [← hQ]
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  unfold Nat.ModEq at h3
  have hcases : Nat.card {q : Q // q * q = 1} = 2 ∨ Nat.card {q : Q // q * q = 1} = 8 := by
    omega
  rcases hcases with h | h
  · right
    refine ⟨c, hcQ, hc1, hcc, fun q hq hqq => ?_⟩
    have hs : ({q : Q | q * q = 1} : Set Q).ncard ≤ 2 := by
      rw [← Nat.card_coe_set_eq]
      exact h.le
    have hc1' : (⟨c, hcQ⟩ : Q) * ⟨c, hcQ⟩ = 1 := Subtype.ext hcc
    have := eq_or_eq_of_ncard_le_two (s := {q : Q | q * q = 1}) hs (Set.toFinite _)
      (a := 1) (b := ⟨c, hcQ⟩) (by simp) hc1' (fun h => hc1 (congrArg Subtype.val h).symm)
      (q := ⟨q, hq⟩) (Subtype.ext hqq)
    rcases this with h1 | h1
    · exact Or.inl (congrArg Subtype.val h1)
    · exact Or.inr (congrArg Subtype.val h1)
  · left
    intro q hq
    have hbij : Function.Bijective (Subtype.val : {q : Q // q * q = 1} → Q) :=
      Subtype.val_injective.bijective_of_nat_card_le (by rw [h, hQ])
    obtain ⟨s, hs⟩ := hbij.2 ⟨q, hq⟩
    have := s.2
    rw [hs] at this
    exact congrArg Subtype.val this

end Dichotomy

end CFSG.Quasithin.F6.GoldAmS
