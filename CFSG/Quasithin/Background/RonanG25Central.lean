module

public import CFSG.Quasithin.Background.RonanG25Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

public section

namespace CFSG.Quasithin.RonanG25

section Central

variable {G : Type} [Group G] {F : Type} [Field F] {X : Subgroup G} {ord : Bool}

theorem subgroupOf_normal {A B : Subgroup G} (hnorm : ∀ y ∈ B, ∀ z ∈ A, y * z * y⁻¹ ∈ A) :
    (A.subgroupOf B).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm (g : G) g.2 n hn⟩

theorem isPGroup_quotient_subgroupOf [Finite G] {A B : Subgroup G} [(A.subgroupOf B).Normal]
    (h2 : ∀ y ∈ B, ∃ k : ℕ, y ^ 2 ^ k ∈ A) : IsPGroup 2 (↥B ⧸ A.subgroupOf B) := by
  refine isPGroup_iff_pow_pow_eq_one.mpr fun g => ?_
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨k, hk⟩ := h2 (b : G) b.2
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  simpa using hk

theorem exists_central_involution [Finite G] {A B : Subgroup G} (hAB : A ≤ B) (hne : A ≠ B)
    (hnorm : ∀ y ∈ B, ∀ z ∈ A, y * z * y⁻¹ ∈ A)
    (h2 : ∀ y ∈ B, ∃ k : ℕ, y ^ 2 ^ k ∈ A) :
    ∃ z ∈ B, z ∉ A ∧ z ^ 2 ∈ A ∧ ∀ y ∈ B, y * z * y⁻¹ * z⁻¹ ∈ A := by
  classical
  haveI := subgroupOf_normal hnorm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (↥B ⧸ A.subgroupOf B) := isPGroup_quotient_subgroupOf h2
  have hnt : Nontrivial (↥B ⧸ A.subgroupOf B) := by
    obtain ⟨b, hb, hbA⟩ : ∃ b ∈ B, b ∉ A := by
      by_contra h
      exact hne (le_antisymm hAB fun b hb => Classical.byContradiction fun hbA => h ⟨b, hb, hbA⟩)
    refine nontrivial_of_ne 1 (QuotientGroup.mk (⟨b, hb⟩ : ↥B)) fun h => hbA ?_
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (⟨b, hb⟩ : ↥B)).mp h.symm)
  haveI := hnt
  haveI := hP.center_nontrivial
  obtain ⟨x, hx⟩ := exists_ne (1 : Subgroup.center (↥B ⧸ A.subgroupOf B))
  have hx1 : (x : ↥B ⧸ A.subgroupOf B) ≠ 1 := fun h => hx (Subtype.ext h)
  obtain ⟨k, hk⟩ := hP.exists_orderOf_eq_pow (x : ↥B ⧸ A.subgroupOf B)
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hk
    exact hx1 hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective ((x : ↥B ⧸ A.subgroupOf B) ^ 2 ^ j)
  have hs2 : (QuotientGroup.mk w : ↥B ⧸ A.subgroupOf B) ^ 2 = 1 := by
    rw [hw]
    calc ((x : ↥B ⧸ A.subgroupOf B) ^ 2 ^ j) ^ 2
        = (x : ↥B ⧸ A.subgroupOf B) ^ (2 ^ (j + 1)) := by rw [← pow_mul, pow_succ]
      _ = 1 := by rw [← hk]; exact pow_orderOf_eq_one _
  have hsne : (QuotientGroup.mk w : ↥B ⧸ A.subgroupOf B) ≠ 1 := by
    rw [hw]
    refine pow_ne_one_of_lt_orderOf (by positivity) ?_
    rw [hk]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hscen : ∀ g : ↥B ⧸ A.subgroupOf B, g * QuotientGroup.mk w = QuotientGroup.mk w * g := by
    intro g
    rw [hw]
    exact (Subgroup.mem_center_iff.mp
      ((Subgroup.center (↥B ⧸ A.subgroupOf B)).pow_mem x.2 (2 ^ j))) g
  refine ⟨(w : G), w.2, ?_, ?_, ?_⟩
  · intro hwA
    apply hsne
    exact (QuotientGroup.eq_one_iff w).mpr (Subgroup.mem_subgroupOf.mpr hwA)
  · have h1 : (QuotientGroup.mk (w ^ 2) : ↥B ⧸ A.subgroupOf B) = 1 := by
      rw [QuotientGroup.mk_pow]
      exact hs2
    have h3 := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (w ^ 2)).mp h1)
    simpa using h3
  · intro y hy
    have hc := hscen (QuotientGroup.mk (⟨y, hy⟩ : ↥B))
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at hc
    have hc2 := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hc)
    have hc3 : (y * (w : G))⁻¹ * ((w : G) * y) ∈ A := by simpa using hc2
    have e : y * (w : G) * y⁻¹ * (w : G)⁻¹ =
        (y * (w : G)) * ((y * (w : G))⁻¹ * ((w : G) * y))⁻¹ * (y * (w : G))⁻¹ := by
      group
    rw [e]
    exact hnorm _ (B.mul_mem hy w.2) _ (A.inv_mem hc3)

theorem exists_subgroup_union {A B : Subgroup G} {z : G} (hzB : z ∈ B) (hz2 : z ^ 2 ∈ A)
    (hnorm : ∀ y ∈ B, ∀ w ∈ A, y * w * y⁻¹ ∈ A) :
    ∃ Q : Subgroup G, ∀ g, g ∈ Q ↔ (g ∈ A ∨ g * z⁻¹ ∈ A) := by
  refine ⟨{ carrier := {g | g ∈ A ∨ g * z⁻¹ ∈ A}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun g => Iff.rfl⟩
  · intro a b ha hb
    have ha' : a ∈ A ∨ a * z⁻¹ ∈ A := ha
    have hb' : b ∈ A ∨ b * z⁻¹ ∈ A := hb
    show a * b ∈ A ∨ a * b * z⁻¹ ∈ A
    rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb'
    · exact Or.inl (A.mul_mem ha' hb')
    · refine Or.inr ?_
      rw [mul_assoc]
      exact A.mul_mem ha' hb'
    · refine Or.inr ?_
      have e : a * b * z⁻¹ = (a * z⁻¹) * (z * b * z⁻¹) := by group
      rw [e]
      exact A.mul_mem ha' (hnorm z hzB b hb')
    · refine Or.inl ?_
      have e : a * b = (a * z⁻¹) * (z * (b * z⁻¹) * z⁻¹) * z ^ 2 := by group
      rw [e]
      exact A.mul_mem (A.mul_mem ha' (hnorm z hzB _ hb')) hz2
  · show (1 : G) ∈ A ∨ (1 : G) * z⁻¹ ∈ A
    exact Or.inl A.one_mem
  · intro a ha
    have ha' : a ∈ A ∨ a * z⁻¹ ∈ A := ha
    show a⁻¹ ∈ A ∨ a⁻¹ * z⁻¹ ∈ A
    rcases ha' with ha' | ha'
    · exact Or.inl (A.inv_mem ha')
    · refine Or.inr ?_
      have e : a⁻¹ * z⁻¹ = (z⁻¹ * (a * z⁻¹)⁻¹ * z) * (z ^ 2)⁻¹ := by group
      rw [e]
      have h1 : z⁻¹ * (a * z⁻¹)⁻¹ * z ∈ A := by
        have h4 := hnorm z⁻¹ (B.inv_mem hzB) _ (A.inv_mem ha')
        rwa [inv_inv] at h4
      exact A.mul_mem h1 (A.inv_mem hz2)

theorem exists_chief_step_central [Finite G] {A B : Subgroup G} (hAB : A ≤ B) (hne : A ≠ B)
    (hA : Inv X A) (hnorm : ∀ y ∈ B, ∀ z ∈ A, y * z * y⁻¹ ∈ A) (hcen : FactorCentral X A B)
    (h2 : ∀ y ∈ B, ∃ k : ℕ, y ^ 2 ^ k ∈ A) :
    ∃ Q : Subgroup G, ChiefStep X A Q ∧ FactorCentral X A Q ∧ Nat.card Q = 2 * Nat.card A ∧
      Q ≤ B ∧ ∀ y ∈ B, ∀ w ∈ Q, y * w * y⁻¹ ∈ Q := by
  obtain ⟨z, hzB, hzA, hz2, hzc⟩ := exists_central_involution hAB hne hnorm h2
  obtain ⟨Q, hQ⟩ := exists_subgroup_union hzB hz2 hnorm
  have hAQ : A ≤ Q := fun a ha => (hQ a).2 (Or.inl ha)
  have hzQ : z ∈ Q := (hQ z).2 (Or.inr (by rw [mul_inv_cancel]; exact A.one_mem))
  have hQB : Q ≤ B := by
    intro g hg
    rcases (hQ g).1 hg with h | h
    · exact hAB h
    · have e : g = (g * z⁻¹) * z := by group
      rw [e]
      exact B.mul_mem (hAB h) hzB
  have hQinv : Inv X Q := by
    intro x hx g hg
    rcases (hQ g).1 hg with h | h
    · exact hAQ (hA x hx g h)
    · refine (hQ _).2 (Or.inr ?_)
      have e : x * g * x⁻¹ * z⁻¹ = (x * (g * z⁻¹) * x⁻¹) * (x * z * x⁻¹ * z⁻¹) := by group
      rw [e]
      exact A.mul_mem (hA x hx _ h) (hcen x hx z hzB)
  have hQnorm : ∀ y ∈ B, ∀ w ∈ Q, y * w * y⁻¹ ∈ Q := by
    intro y hy g hg
    rcases (hQ g).1 hg with h | h
    · exact hAQ (hnorm y hy g h)
    · refine (hQ _).2 (Or.inr ?_)
      have e : y * g * y⁻¹ * z⁻¹ = (y * (g * z⁻¹) * y⁻¹) * (y * z * y⁻¹ * z⁻¹) := by group
      rw [e]
      exact A.mul_mem (hnorm y hy _ h) (hzc y hy)
  have hcard : Nat.card Q = 2 * Nat.card A := by
    have hidx : A.relIndex Q = 2 := by
      rw [Subgroup.relIndex_eq_two_iff]
      refine ⟨z, hzQ, fun b hb => ?_⟩
      unfold Xor
      rcases (hQ b).1 hb with hbA | hbz
      · refine Or.inr ⟨hbA, fun h => hzA ?_⟩
        have h' := A.mul_mem (A.inv_mem hbA) h
        simpa using h'
      · have hbz' : b * z ∈ A := by
          have e : b * z = (b * z⁻¹) * z ^ 2 := by group
          rw [e]
          exact A.mul_mem hbz hz2
        refine Or.inl ⟨hbz', fun hbA => hzA ?_⟩
        have h' := A.mul_mem (A.inv_mem hbA) hbz
        simpa using h'
    have hsub : Nat.card (A.subgroupOf Q) = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAQ).toEquiv
    have hmul := Subgroup.card_mul_index (H := A.subgroupOf Q)
    have hidx' : (A.subgroupOf Q).index = 2 := hidx
    rw [hsub, hidx'] at hmul
    rw [← hmul, mul_comm]
  have hlt : A < Q := lt_of_le_of_ne hAQ (fun h => hzA (by rw [h]; exact hzQ))
  refine ⟨Q, ⟨hlt, hA, hQinv, fun y hy z' hz' => hnorm y (hQB hy) z' hz', ?_⟩,
    fun x hx y hy => hcen x hx y (hQB hy), hcard, hQB, hQnorm⟩
  intro Q' hAQ' hQ'Q _ _
  have hApos : 0 < Nat.card A := Nat.card_pos
  have h1 : Nat.card A ∣ Nat.card Q' := Subgroup.card_dvd_of_le hAQ'
  have h2' : Nat.card Q' ∣ 2 * Nat.card A := by
    have := Subgroup.card_dvd_of_le hQ'Q
    rwa [hcard] at this
  obtain ⟨c, hc⟩ := h1
  have h3 : Nat.card A * c ∣ Nat.card A * 2 := by
    rw [← hc, mul_comm (Nat.card A) 2]
    exact h2'
  have hc2 : c ∣ 2 := Nat.dvd_of_mul_dvd_mul_left hApos h3
  rcases (Nat.dvd_prime Nat.prime_two).1 hc2 with rfl | rfl
  · left
    exact (Subgroup.eq_of_le_of_card_ge hAQ' (le_of_eq (by rw [hc, mul_one]))).symm
  · right
    exact Subgroup.eq_of_le_of_card_ge hQ'Q (le_of_eq (by rw [hcard, hc, mul_comm]))

theorem chain_central_aux [Finite G] {B : Subgroup G} (hB : Inv X B) (n : ℕ) :
    ∀ C : Subgroup G, C ≤ B → Inv X C → (∀ y ∈ B, ∀ z ∈ C, y * z * y⁻¹ ∈ C) →
      FactorCentral X C B → (∀ y ∈ B, ∃ k : ℕ, y ^ 2 ^ k ∈ C) →
      Nat.card B = 2 ^ n * Nat.card C → ChainCounts F X ord C B 0 0 := by
  induction n with
  | zero =>
    intro C hCB hC _ _ _ hcard
    have hcard' : Nat.card B ≤ Nat.card C := le_of_eq (by rw [hcard, pow_zero, one_mul])
    have hEq : C = B := Subgroup.eq_of_le_of_card_ge hCB hcard'
    rw [hEq]
    exact ChainCounts.refl B hB
  | succ n ih =>
    intro C hCB hC hnorm hcen h2 hcard
    have hne : C ≠ B := by
      intro hEq
      rw [hEq] at hcard
      have hpos : 0 < Nat.card B := Nat.card_pos
      have h2le : 2 ≤ 2 ^ (n + 1) := by
        have := Nat.pow_le_pow_right (show 2 > 0 by norm_num) (show 1 ≤ n + 1 by omega)
        simpa using this
      nlinarith
    obtain ⟨Q, hs, hc, hcardQ, hQB, hQnorm⟩ :=
      exists_chief_step_central hCB hne hC hnorm hcen h2
    have hCQ : C ≤ Q := hs.lt.le
    have hcardQB : Nat.card B = 2 ^ n * Nat.card Q := by
      rw [hcardQ, hcard, pow_succ]
      ring
    have hIH := ih Q hQB hs.invB hQnorm (fun x hx y hy => hCQ (hcen x hx y hy))
      (fun y hy => by
        obtain ⟨k, hk⟩ := h2 y hy
        exact ⟨k, hCQ hk⟩) hcardQB
    exact ChainCounts.central hs hc Nat.prime_two hcardQ hIH

theorem exists_chain_central [Finite G] {A B : Subgroup G} (hAB : A ≤ B) (hA : Inv X A)
    (hB : Inv X B) (hnorm : ∀ y ∈ B, ∀ z ∈ A, y * z * y⁻¹ ∈ A) (hcen : FactorCentral X A B)
    (h2 : ∀ y ∈ B, ∃ k : ℕ, y ^ 2 ^ k ∈ A) : ChainCounts F X ord A B 0 0 := by
  haveI := subgroupOf_normal hnorm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp (isPGroup_quotient_subgroupOf h2)
  have hsub : Nat.card (A.subgroupOf B) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv
  have hidx := Subgroup.card_mul_index (H := A.subgroupOf B)
  have hidx' : (A.subgroupOf B).index = 2 ^ m := hm
  rw [hidx', hsub] at hidx
  exact chain_central_aux hB m A hAB hA hnorm hcen h2 (by rw [← hidx, mul_comm])

end Central

end CFSG.Quasithin.RonanG25
