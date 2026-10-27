module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.LiftingFixedPoints
public import CFSG.RankThree.PartOne.S9.MinTwoAction.LiftingSign

public section

namespace CFSG.RankThree.PartOne.Lifting36

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY
  CFSG.RankThree.PartOne.Quotient36 SemidirectProduct
open scoped IsMulCommutative commutatorElement

section Core

variable {p q d : ℕ} {S : Type*} [Group S] {A : Type*} [Group A] {φ : A →* MulAut S}

theorem pRank_fixed_eq_finrank [Finite S] {D : Type*} [Group D] [Finite D]
    [MulDistribMulAction (S ⋊[φ] A) D] [Fact q.Prime] [Fact (IsPGroup q D)]
    [IsElementaryAbelian q D] (hq2 : q ≠ 2) (hS : Nat.card S = 2 ^ d) (s : S) :
    CFSG.pRank q (fixedPointSubgroup (Subgroup.zpowers (inl s : S ⋊[φ] A)) D) =
      Module.finrank (ZMod q) ↥(Module.End.eigenspace
        (frattiniRep (E := S ⋊[φ] A) (X := D) q (inl s)) 1) := by
  have hΦ : frattini D = ⊥ := frattini_eq_bot_of_isElementaryAbelian (R := D) (p := q)
  have := finite_zpowers_inl (A := A) (φ := φ) s
  have hp2 := isPGroup_zpowers_inl (A := A) (φ := φ) hS s
  set Fix := fixedPointSubgroup (Subgroup.zpowers (inl s : S ⋊[φ] A)) D with hFix
  have hinj : Function.Injective (QuotientGroup.mk' (frattini D)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hΦ]
  have himg := fixed_mk_eq_image (E := S ⋊[φ] A) (X := D) hq2 (inl s) hp2
  have hcard : Nat.card Fix = Nat.card ↥(Module.End.eigenspace
      (frattiniRep (E := S ⋊[φ] A) (X := D) q (inl s)) 1) := by
    rw [card_eigenspace_eq q (inl s)]
    have h1 : Nat.card {v : D ⧸ frattini D // (letI := frattiniQuotientAction (S ⋊[φ] A) D;
        (inl s : S ⋊[φ] A) • v = v)} =
        Nat.card ↥((QuotientGroup.mk' (frattini D)) '' {c : D | (inl s : S ⋊[φ] A) • c = c}) := by
      rw [← himg]
      rfl
    rw [h1, Nat.card_image_of_injective hinj]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun c =>
      mem_fixedPointSubgroup_zpowers_iff (inl s) c)
  have hexp : ∀ x : ↥Fix, x ^ q = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p q D) x.1)
  have hDc : IsMulCommutative D := (inferInstance : IsElementaryAbelian q D).toIsMulCommutative
  have hcomm : IsMulCommutative ↥Fix :=
    ⟨⟨fun a b => Subtype.ext (hDc.is_comm.comm a.1 b.1)⟩⟩
  have hk : Nat.card Fix = q ^ Module.finrank (ZMod q) ↥(Module.End.eigenspace
      (frattiniRep (E := S ⋊[φ] A) (X := D) q (inl s)) 1) := by
    rw [hcard, Module.natCard_eq_pow_finrank (K := ZMod q), Nat.card_zmod]
  exact CFSG.RankThree.PartTwo.pRank_eq_of_isMulCommutative (Fact.out : q.Prime) hexp hcomm hk

end Core

section Family

variable {p q d : ℕ} {S : Type*} [Group S] {A : Type*} [Group A] {φ : A →* MulAut S}

theorem neg_one_ne_one_of_two_ne_zero {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) :
    (-1 : K) ≠ 1 := by
  intro h
  apply h2
  rw [show (2 : K) = 1 - (-1) by ring, h, sub_self]

theorem abelian_of_family {D : Type*} [Group D] [Finite D] [MulDistribMulAction (S ⋊[φ] A) D]
    [Fact q.Prime] [Fact (IsPGroup q D)] (hq2' : (2 : ZMod q) ≠ 0) (hq2 : q ≠ 2)
    (hDexp : ∀ x : D, x ^ q = 1) (hDcl : commutator D ≤ Subgroup.center D)
    (hfixc : ∀ s : S, ∀ y ∈ commutator D, (inl s : S ⋊[φ] A) • y = y) {n : ℕ}
    (v : Option (Fin n) → Additive (D ⧸ frattini D)) (c : Option (Fin n) → S → ZMod q)
    (hspan : ⊤ ≤ Submodule.span (ZMod q) (Set.range v))
    (heig : ∀ i s, frattiniRep (E := S ⋊[φ] A) (X := D) q (inl s) (v i) = c i s • v i)
    (hsign : ∀ i s, c i s = 1 ∨ c i s = -1) (hdist : ∀ i j, i ≠ j → ∃ s, c i s ≠ c j s) :
    ∀ a b : D, ⁅a, b⁆ = 1 := by
  classical
  have hm1 : (-1 : ZMod q) ≠ 1 := neg_one_ne_one_of_two_ne_zero hq2'
  obtain ⟨x, hx⟩ : ∃ x : Option (Fin n) → D, ∀ i, (x i : D ⧸ frattini D) = Additive.toMul (v i) :=
    ⟨fun i => (QuotientGroup.mk_surjective (Additive.toMul (v i))).choose,
      fun i => (QuotientGroup.mk_surjective (Additive.toMul (v i))).choose_spec⟩
  let σ : S → MulAut D := fun s => MulDistribMulAction.toMulAut (S ⋊[φ] A) D (inl s)
  have hσ : ∀ s y, σ s y = (inl s : S ⋊[φ] A) • y := fun s y => rfl
  let ε : Option (Fin n) → S → ℤˣ := fun i s => if c i s = 1 then 1 else -1
  refine commutator_eq_one_of_signs hq2 hDexp hDcl σ ?_ x ε ?_ ?_ ?_
  · intro s a b
    rw [hσ]
    exact hfixc s _ (by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
  · intro i s
    have h1 := frattiniRep_apply_mk (E := S ⋊[φ] A) (X := D) q (inl s) (x i)
    have hvi : v i = Additive.ofMul (x i : D ⧸ frattini D) := by rw [hx i]; rfl
    rw [← hvi, heig] at h1
    rw [hσ, ← div_eq_mul_inv]
    rcases hsign i s with h | h
    · have : Additive.ofMul (((inl s : S ⋊[φ] A) • x i : D) : D ⧸ frattini D) =
          Additive.ofMul (x i : D ⧸ frattini D) := by rw [← h1, h, one_smul, hvi]
      have h2 : (((inl s : S ⋊[φ] A) • x i : D) : D ⧸ frattini D) = (x i : D ⧸ frattini D) :=
        Additive.ofMul.injective this
      have h3 := (QuotientGroup.eq_iff_div_mem).mp h2
      have hε : (ε i s : ℤ) = 1 := by simp [ε, h]
      rw [hε, zpow_one]
      exact h3
    · have : Additive.ofMul (((inl s : S ⋊[φ] A) • x i : D) : D ⧸ frattini D) =
          Additive.ofMul ((x i : D ⧸ frattini D)⁻¹) := by
        have key : ∀ w : Additive (D ⧸ frattini D), (-1 : ZMod q) • w = -w :=
          fun w => neg_one_smul (ZMod q) w
        rw [← h1, h, key, hvi]
        rfl
      have h2 : (((inl s : S ⋊[φ] A) • x i : D) : D ⧸ frattini D) = (x i : D ⧸ frattini D)⁻¹ :=
        Additive.ofMul.injective this
      have h3 : (((inl s : S ⋊[φ] A) • x i : D) : D ⧸ frattini D) =
          ((x i ^ (-1 : ℤ) : D) : D ⧸ frattini D) := by rw [h2]; simp
      have h4 := (QuotientGroup.eq_iff_div_mem).mp h3
      have hε : (ε i s : ℤ) = -1 := by simp [ε, h, hm1]
      rw [hε]
      exact h4
  · intro i j hij
    obtain ⟨s, hs⟩ := hdist i j hij
    refine ⟨s, ?_⟩
    simp only [ε]
    rcases hsign i s with h1 | h1 <;> rcases hsign j s with h2 | h2
    · exact absurd (h1.trans h2.symm) hs
    · simp [h1, h2, hm1]
    · simp [h1, h2, hm1]
    · exact absurd (h1.trans h2.symm) hs
  · intro d
    have hmem : Additive.ofMul (d : D ⧸ frattini D) ∈ Submodule.span (ZMod q) (Set.range v) :=
      hspan Submodule.mem_top
    have key : ∀ w ∈ Submodule.span (ZMod q) (Set.range v), ∃ u ∈ Subgroup.closure (Set.range x),
        (u : D ⧸ frattini D) = Additive.toMul w := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨i, rfl⟩ := hw
        exact ⟨x i, Subgroup.subset_closure ⟨i, rfl⟩, hx i⟩
      | zero => exact ⟨1, one_mem _, by simp⟩
      | add a b _ _ ha hb =>
        obtain ⟨u, hu, hua⟩ := ha
        obtain ⟨u', hu', hub⟩ := hb
        exact ⟨u * u', mul_mem hu hu', by rw [QuotientGroup.mk_mul, hua, hub]; rfl⟩
      | smul r a _ ha =>
        obtain ⟨u, hu, hua⟩ := ha
        refine ⟨u ^ r.val, pow_mem hu _, ?_⟩
        have h1 : r • a = r.val • a := by
          conv_lhs => rw [← ZMod.natCast_zmod_val r]
          exact Nat.cast_smul_eq_nsmul (ZMod q) r.val a
        rw [h1, toMul_nsmul, ← hua]
        exact QuotientGroup.mk_pow _ u r.val
    obtain ⟨u, hu, hud⟩ := key _ hmem
    refine ⟨u, hu, ?_⟩
    rw [toMul_ofMul] at hud
    exact QuotientGroup.eq.mp hud

end Family

end CFSG.RankThree.PartOne.Lifting36
