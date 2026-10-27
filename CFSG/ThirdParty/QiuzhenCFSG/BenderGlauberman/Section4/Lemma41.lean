module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section4.Basic
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section4.Basic
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.ClassFunction
import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Lemma24
import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Lemma33
import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Lemma34

namespace CFSG
end CFSG
open CFSG

/-!
# Bender--Glauberman: Section 4 — Lemma 4.1

Lemma 4.1: for `χ ∈ ±Irr(G)` with `B′(χ)` nonempty, `|B′(χ)|` is `1` or
`3`, the evaluation at `t`, the congruence on `B`, odd degree, and the
invariance of `{ν̂ | ν ∈ B′(χ)}` under `N_G(B)`, hence under `N_G(S)`.
The proof applies the landed Lemmas 2.4, 3.3 and 3.4 to `B(χ)`, transfers
`B(χ)`-membership to `B′(χ)` through the pair `{ν, λ₂ν}`, and uses
Lemma 1.8 together with the one-to-one Glauberman correspondence for the
normalizer-invariance clauses.
-/

noncomputable section

open scoped BigOperators
open scoped commutatorElement
open scoped Pointwise

namespace CFSG.BenderGlauberman

open GorensteinWalter
open Theory.Character

-- Local instances matching `Theory.Character`'s subgroup-sum convention; see
-- `BenderGlauberman/ClassFunction.lean`.
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

universe u

/-! ## Conjugation of products of class functions -/

/-- Conjugation by a normalizing element distributes over products of class
functions. -/
private lemma conjChar_mul {G : Type u} [Group G] {H0 : Subgroup G} {s : G}
    (hsH0 : ∀ x : ↥H0, s * (x : G) * s⁻¹ ∈ H0) (φ ψ : ClassFunction (↥H0)) :
    conjChar H0 hsH0 (φ * ψ) = conjChar H0 hsH0 φ * conjChar H0 hsH0 ψ := by
  ext x
  rfl

/-- `±Irr(G)` characters are class functions. -/
private lemma isClassFunction_of_isPMIrr {G : Type u} [Group G]
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) : IsClassFunction χ := by
  rcases hχ with h | h
  · exact irreducibleCharacter_isClassFunction h
  · have hψ : IsClassFunction (-χ) := irreducibleCharacter_isClassFunction h
    intro x g
    have h' := hψ x g
    simpa using congrArg Neg.neg h'

/-- The degree of a signed irreducible character is an integer. -/
private lemma pmIrr_one_int {G : Type u} [Group G] {χ : ClassFunction G}
    (hχ : IsPMIrr G χ) : ∃ m : ℤ, (m : ℂ) = χ 1 := by
  rcases hχ with hχpos | hχneg
  · rcases hχpos with ⟨n, ρ, hρ, rfl⟩
    refine ⟨(Module.finrank ℂ (Fin n → ℂ) : ℤ), ?_⟩
    rw [Representation.char_one]
    norm_num
  · rcases hχneg with ⟨n, ρ, hρ, hEq⟩
    have hneg : χ = -ρ.character := by simpa using congrArg Neg.neg hEq
    rw [hneg]
    refine ⟨-(Module.finrank ℂ (Fin n → ℂ) : ℤ), ?_⟩
    rw [Pi.neg_apply, Representation.char_one]
    norm_num

section Section4

variable {G : Type u} [Group G] [Fintype G]
variable (c : Hyp11 G)

/-! ## Section-4 structure: `|S0| = 2` and the dual group `Λ = {1, λ₂}` -/

/-- `|S0| = 2` in the Section-4 case `|S| = 4`. -/
private lemma S0_card_eq_two (hS4 : Section4Hyp c) :
    Nat.card (↥(c.S0 : Subgroup G)) = 2 := by
  unfold Section4Hyp at hS4
  have h4 : 2 * Nat.card (↥(c.S0 : Subgroup G)) = 4 := by
    rw [← c.S_index_two, hS4]
  omega

/-- `S' = 1` in the Section-4 case (`S'` has index `2` in `S0`). -/
private lemma SPrime_eq_bot_s4 (hS4 : Section4Hyp c) : SPrime c = ⊥ := by
  classical
  have hS0card : Nat.card (↥(c.S0 : Subgroup G)) = 2 := S0_card_eq_two c hS4
  have hsq : (c.t1 * c.t2) ^ 2 = 1 := by
    have h2 : (⟨c.t1 * c.t2, S0_generator_mem_S0 c⟩ : ↥(c.S0 : Subgroup G)) ^ 2 = 1 :=
      sq_eq_one_of_card_two hS0card _
    simpa [Subgroup.coe_pow] using congrArg Subtype.val h2
  unfold SPrime
  rw [hsq, Subgroup.zpowers_one_eq_bot]

/-- `X = S'·U` equals `U` in the Section-4 case. -/
private lemma extensionSubgroup_eq_U_s4 (hS4 : Section4Hyp c) :
    extensionSubgroup c = c.U := by
  unfold extensionSubgroup
  rw [SPrime_eq_bot_s4 c hS4, bot_sup_eq]

/-- `t ∉ X = S'·U` in the Section-4 case. -/
private lemma tH0_not_mem_extensionSubgroup_s4 (hS4 : Section4Hyp c) :
    (tH0 c : G) ∉ extensionSubgroup c := by
  rw [extensionSubgroup_eq_U_s4 c hS4]
  exact t_not_mem_U c

/-- `λ₂(t) = -1` (as a unit). -/
private lemma lambdaTwo_at_tH0_eq_neg_one (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) :
    (lambdaTwo c h12).1 (tH0 c) = (-1 : ℂˣ) :=
  lambdaTwo_val_neg_one_of_not_mem_extensionSubgroup c h12 hSC (tH0 c)
    (tH0_not_mem_extensionSubgroup_s4 c hS4)

/-- `λ₂(t) = -1` as a complex number. -/
private lemma lambdaTwo_val_tH0_eq_neg_one (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) :
    ((lambdaTwo c h12).1 (tH0 c) : ℂ) = -1 :=
  congrArg (fun u : ℂˣ => (u : ℂ)) (lambdaTwo_at_tH0_eq_neg_one c h12 hSC hS4)

/-- A `Λ`-character is trivial on `U`. -/
private lemma lambda_trivial_on_U (l : LambdaHom c.H0 c.U) {u : ↥c.H0}
    (hu : (u : G) ∈ c.U) : (l.1 u : ℂ) = 1 := by
  have hl : l.1 ∈ {l : ↥c.H0 →* ℂˣ | ∀ u : ↥c.H0, (u : G) ∈ c.U → l u = 1} := l.2
  exact congrArg (fun u : ℂˣ => (u : ℂ)) (hl u hu)

/-- `λ₂` is fixed by `s` (Lemma 2.1 / `lambda_fixed_by_s_iff`). -/
private lemma lambdaTwo_fixed_by_s (h12 : Hyp12 c)
    :
    conjChar c.H0 (s_normalizes_H0 c h12) (LambdaChar (lambdaTwo c h12).1) =
      LambdaChar (lambdaTwo c h12).1 := by
  exact (lambda_fixed_by_s_iff c h12 (lambdaTwo c h12)).mpr (Or.inr rfl)

/-- For `ν` fixed by `s`, `λ₂ν` is fixed by `s` as well. -/
private lemma lambdaTwoMul_fixed_by_s (h12 : Hyp12 c)
    {ν : Irr (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1) :
    conjChar c.H0 (s_normalizes_H0 c h12) (lambdaTwoMul c h12 ν).1 =
      (lambdaTwoMul c h12 ν).1 := by
  unfold lambdaTwoMul
  rw [conjChar_mul]
  rw [lambdaTwo_fixed_by_s c h12, hνs]

/-- `λ₂ν ≠ ν`: the values at the central involution `t` differ. -/
private lemma lambdaTwoMul_ne_self (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) (ν : Irr (↥c.H0)) :
    lambdaTwoMul c h12 ν ≠ ν := by
  intro hEq
  have hpt := congrFun (congrArg Subtype.val hEq) (tH0 c)
  unfold lambdaTwoMul at hpt
  have hlc : LambdaChar (lambdaTwo c h12).1 (tH0 c) =
      ((lambdaTwo c h12).1 (tH0 c) : ℂ) := rfl
  have hpt' : ((lambdaTwo c h12).1 (tH0 c) : ℂ) * ν.1 (tH0 c) = ν.1 (tH0 c) := by
    simpa [hlc] using hpt
  have hνt0 : ν.1 (tH0 c) ≠ 0 := char_apply_central_ne_zero
    (G := ↥c.H0) (t := tH0 c)
    (by simpa [tH0] using t_central_H0' c) (by simpa [tH0] using t_H0_sq c) ν.2
  have hl1 : ((lambdaTwo c h12).1 (tH0 c) : ℂ) = 1 :=
    mul_right_cancel₀ hνt0 (by simpa using hpt')
  have hlneg : ((lambdaTwo c h12).1 (tH0 c) : ℂ) = -1 :=
    lambdaTwo_val_tH0_eq_neg_one c h12 hSC hS4
  have hbad : (1 : ℂ) = -1 := hl1.symm.trans hlneg
  norm_num at hbad

/-- `|H0 : U| = |S0|`: the direct-product decomposition `H0 = U·S0`. -/
private lemma U_index_eq_S0_card (h12 : Hyp12 c) :
    (c.U.subgroupOf c.H0).index = Nat.card (↥(c.S0 : Subgroup G)) := by
  classical
  let f : ↥c.U × ↥c.S0 → ↥c.H0 := fun p =>
    ⟨(p.1 : G) * (p.2 : G), c.H0.mul_mem ((h12.U_normal_in_H0).1 p.1.2) (S0_le_H0 c p.2.2)⟩
  have hinj : Function.Injective f := by
    intro p q hEq
    have hEq' : (p.1 : G) * (p.2 : G) = (q.1 : G) * (q.2 : G) := congrArg Subtype.val hEq
    have h₁ : (q.1 : G)⁻¹ * (p.1 : G) = (q.2 : G) * (p.2 : G)⁻¹ := by
      calc
        (q.1 : G)⁻¹ * (p.1 : G) = (q.1 : G)⁻¹ * ((p.1 : G) * (p.2 : G)) * (p.2 : G)⁻¹ := by group
        _ = (q.1 : G)⁻¹ * ((q.1 : G) * (q.2 : G)) * (p.2 : G)⁻¹ := by rw [hEq']
        _ = (q.2 : G) * (p.2 : G)⁻¹ := by group
    have hU : (q.1 : G)⁻¹ * (p.1 : G) ∈ c.U := (c.U).mul_mem ((c.U).inv_mem q.1.2) p.1.2
    have hS0 : (q.2 : G) * (p.2 : G)⁻¹ ∈ c.S0 := (c.S0).mul_mem q.2.2 ((c.S0).inv_mem p.2.2)
    have honeU : (q.1 : G)⁻¹ * (p.1 : G) = 1 := U_inter_S0_eq_bot c hU (by
      rw [h₁]
      exact hS0)
    have hS0inU : (q.2 : G) * (p.2 : G)⁻¹ ∈ c.U := by
      rw [← h₁]
      exact hU
    have honeS : (q.2 : G) * (p.2 : G)⁻¹ = 1 := U_inter_S0_eq_bot c hS0inU hS0
    apply Prod.ext
    · apply Subtype.ext
      exact mul_left_cancel (a := (q.1 : G)⁻¹) (by
        calc
          (q.1 : G)⁻¹ * (p.1 : G) = 1 := honeU
          _ = (q.1 : G)⁻¹ * (q.1 : G) := by group)
    · apply Subtype.ext
      exact (calc
        (q.2 : G) = (q.2 : G) * (p.2 : G)⁻¹ * (p.2 : G) := by group
        _ = (p.2 : G) := by rw [honeS]; simp).symm
  have hsurj : ∀ x : ↥c.H0, ∃ p : ↥c.U × ↥c.S0, f p = x := by
    intro x
    rcases H0_eq_U_mul_S0 c h12 (x := x) with ⟨u, r, hEq⟩
    refine ⟨(u, r), ?_⟩
    apply Subtype.ext
    exact hEq.symm
  have hcardcong : Nat.card (↥c.H0) = Nat.card (↥c.U) * Nat.card (↥c.S0) := by
    let e : ↥c.U × ↥c.S0 ≃ ↥c.H0 := Equiv.ofBijective f ⟨hinj, hsurj⟩
    have hc : Nat.card (↥c.U × ↥c.S0) = Nat.card (↥c.H0) := Nat.card_congr e
    rw [← hc]
    simp
  have hUcard : Nat.card (↥(c.U.subgroupOf c.H0)) = Nat.card (↥c.U) := by
    exact Nat.card_congr {
      toFun := fun x : ↥(c.U.subgroupOf c.H0) => ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
      invFun := fun y : ↥c.U => ⟨⟨(y : G), (h12.U_normal_in_H0).1 y.2⟩, Subgroup.mem_subgroupOf.mpr y.2⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro y; apply Subtype.ext; rfl }
  have hcm := Subgroup.card_mul_index (c.U.subgroupOf c.H0)
  have h1 : (c.U.subgroupOf c.H0).index * Nat.card (↥c.U) = Nat.card (↥c.H0) := by
    rw [← hUcard, mul_comm]
    exact hcm
  have h2 : Nat.card (↥c.S0) * Nat.card (↥c.U) = Nat.card (↥c.H0) := by
    calc
      Nat.card (↥c.S0) * Nat.card (↥c.U) = Nat.card (↥c.U) * Nat.card (↥c.S0) := by rw [mul_comm]
      _ = Nat.card (↥c.H0) := hcardcong.symm
  exact mul_right_cancel₀ (b := Nat.card (↥c.U)) (Nat.card_pos (α := ↥c.U)).ne' (by
    calc
      (c.U.subgroupOf c.H0).index * Nat.card (↥c.U) = Nat.card (↥c.H0) := h1
      _ = Nat.card (↥c.S0) * Nat.card (↥c.U) := h2.symm)

/-- `|Λ| = 2` in the Section-4 case. -/
private lemma Lambda_card_eq_two (h12 : Hyp12 c) (hS4 : Section4Hyp c) :
    Nat.card (LambdaHom c.H0 c.U) = 2 := by
  rw [lambda_card_eq_index c h12, U_index_eq_S0_card c h12, S0_card_eq_two c hS4]

/-- `Λ = {1, λ₂}`: the two characters of `H0/U`. -/
private lemma Lambda_pair (h12 : Hyp12 c) (hS4 : Section4Hyp c)
    (l : LambdaHom c.H0 c.U) :
    l = 1 ∨ l = lambdaTwo c h12 := by
  classical
  have hLcard : Fintype.card (LambdaHom c.H0 c.U) = 2 := by
    simpa [Nat.card_eq_fintype_card] using Lambda_card_eq_two c h12 hS4
  have hsub : ({1, lambdaTwo c h12} : Finset (LambdaHom c.H0 c.U)) ⊆ Finset.univ := by
    intro x hx
    simp
  have hEq : ({1, lambdaTwo c h12} : Finset (LambdaHom c.H0 c.U)) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_univ, hLcard]
    rw [Finset.card_insert_of_notMem, Finset.card_singleton]
    · intro h
      exact lambdaTwo_ne_one c h12 (Finset.mem_singleton.mp h).symm
  have hl : l ∈ Finset.univ := Finset.mem_univ l
  rw [← hEq] at hl
  simpa using hl

/-- For Section-4 `ν` (fixed by `s`, `ν(t) = ν(1)`), the `Λ`-orbit has the
full size `[H0 : U]` (Lemma 2.1; the Section-4 case of the landed
infrastructure's private `section4_orbit_card_eq_index`). -/
private lemma orbit_card_eq_index_s4 (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) (ν : Irr (↥c.H0)) :
    (orbit c.H0 c.U ν.1).card = (c.U.subgroupOf c.H0).index := by
  classical
  have hνt0 : ν.1 (tH0 c) ≠ 0 := char_apply_central_ne_zero
    (G := ↥c.H0) (t := tH0 c)
    (by simpa [tH0] using t_central_H0' c) (by simpa [tH0] using t_H0_sq c) ν.2
  have hlne : LambdaChar (lambdaTwo c h12).1 * ν.1 ≠ ν.1 := by
    intro hEq
    have hpt := congrFun hEq (tH0 c)
    have hlc : LambdaChar (lambdaTwo c h12).1 (tH0 c) =
        ((lambdaTwo c h12).1 (tH0 c) : ℂ) := rfl
    have hpt' : ((lambdaTwo c h12).1 (tH0 c) : ℂ) * ν.1 (tH0 c) = ν.1 (tH0 c) := by
      simpa [hlc] using hpt
    have hpt'' : ((lambdaTwo c h12).1 (tH0 c) : ℂ) * ν.1 (tH0 c) =
        1 * ν.1 (tH0 c) := by simpa using hpt'
    have hl1 : ((lambdaTwo c h12).1 (tH0 c) : ℂ) = 1 := mul_right_cancel₀ hνt0 hpt''
    have hlneg : ((lambdaTwo c h12).1 (tH0 c) : ℂ) = -1 :=
      lambdaTwo_val_tH0_eq_neg_one c h12 hSC hS4
    have hbad : (1 : ℂ) = -1 := hl1.symm.trans hlneg
    norm_num at hbad
  have hLcard : Fintype.card (LambdaHom c.H0 c.U) = 2 := by
    simpa [Nat.card_eq_fintype_card] using Lambda_card_eq_two c h12 hS4
  have hLpair : ∀ l : LambdaHom c.H0 c.U, l = 1 ∨ l = lambdaTwo c h12 :=
    Lambda_pair c h12 hS4
  have hstabcard : (Finset.univ.filter
      (fun s : LambdaHom c.H0 c.U => LambdaChar s.1 * ν.1 = ν.1)).card = 1 := by
    have hstab_le : (Finset.univ.filter
        (fun s : LambdaHom c.H0 c.U => LambdaChar s.1 * ν.1 = ν.1)) ⊆
        ({1} : Finset (LambdaHom c.H0 c.U)) := by
      intro l hl
      have hlmem := (Finset.mem_filter.mp hl).1
      have hlfix := (Finset.mem_filter.mp hl).2
      rcases hLpair l with hl1 | hl2
      · rw [Finset.mem_singleton]
        exact hl1
      · exfalso
        exact hlne (by simpa [hl2] using hlfix)
    have hmem1 : (1 : LambdaHom c.H0 c.U) ∈ Finset.univ.filter
        (fun s : LambdaHom c.H0 c.U => LambdaChar s.1 * ν.1 = ν.1) :=
      one_mem_stab c.H0 c.U ν.1
    have hsub1 : ({1} : Finset (LambdaHom c.H0 c.U)) ⊆ Finset.univ.filter
        (fun s : LambdaHom c.H0 c.U => LambdaChar s.1 * ν.1 = ν.1) := by
      intro x hx
      rw [Finset.mem_singleton] at hx
      subst x
      exact hmem1
    have hEq : (Finset.univ.filter
        (fun s : LambdaHom c.H0 c.U => LambdaChar s.1 * ν.1 = ν.1)) =
        ({1} : Finset (LambdaHom c.H0 c.U)) :=
      Finset.eq_of_subset_of_card_le hstab_le (Finset.card_le_card hsub1)
    rw [hEq]
    simp
  have hmul := orbit_card_mul_stab c.H0 c.U ν.1
  rw [hstabcard, hLcard] at hmul
  have horbit : (orbit c.H0 c.U ν.1).card = 2 := by
    norm_num at hmul
    exact hmul
  rw [U_index_eq_S0_card c h12, S0_card_eq_two c hS4]
  exact horbit

/-! ## `Δ`, the `B′(χ)` transfer, and the structure of `B(χ)` -/

/-- `Δ`: the `ν ∈ Irr(H0)` with `ν^s = ν` and `ν(t) = ν(1)`. -/
private noncomputable def DeltaSet (c : Hyp11 G) (h12 : Hyp12 c) :
    Finset (Irr (↥c.H0)) := by
  classical
  exact Finset.univ.filter (fun ν : Irr (↥c.H0) =>
    conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 ∧ ν.1 (tH0 c) = ν.1 1)

/-- Membership in `Δ`. -/
private lemma DeltaSet_mem_iff (h12 : Hyp12 c) (ν : Irr (↥c.H0)) :
    ν ∈ DeltaSet c h12 ↔
      conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 ∧ ν.1 (tH0 c) = ν.1 1 := by
  classical
  simp [DeltaSet]

/-- The `s`-fixedness of a `Δ`-member. -/
private lemma DeltaSet_mem_fixed (h12 : Hyp12 c) {ν : Irr (↥c.H0)}
    (hν : ν ∈ DeltaSet c h12) :
    conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 :=
  (DeltaSet_mem_iff c h12 ν).1 hν |>.1

/-- The `t`-value of a `Δ`-member. -/
private lemma DeltaSet_mem_t (h12 : Hyp12 c) {ν : Irr (↥c.H0)}
    (hν : ν ∈ DeltaSet c h12) : ν.1 (tH0 c) = ν.1 1 :=
  (DeltaSet_mem_iff c h12 ν).1 hν |>.2

/-- Membership in `B′(χ)`: a `Δ`-member with nonzero scalar product against
`δν`. -/
public lemma BPrime_mem_iff_scalar (h12 : Hyp12 c) (χ : ClassFunction G)
    (ν : Irr (↥c.H0)) :
    ν ∈ BPrimeOf c h12 χ ↔
      conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 ∧ ν.1 (tH0 c) = ν.1 1 ∧
        scalarProduct G χ (deltaNu c h12 ν) ≠ 0 := by
  classical
  simp [BPrimeOf]

/-- `(χ, δν) = (χ, ν̃) - (χ, λ̃₂ν)`. -/
private lemma deltaNu_scalar_sub (h12 : Hyp12 c) (χ : ClassFunction G)
    (ν : Irr (↥c.H0)) :
    scalarProduct G χ (deltaNu c h12 ν) =
      scalarProduct G χ (tildeNu c h12 ν) -
        scalarProduct G χ (tildeNu c h12 (lambdaTwoMul c h12 ν)) := by
  classical
  unfold deltaNu
  rw [scalarProduct_sub_right]

/-- The coefficient of one member of a decomposition of an irreducible. -/
private lemma scalarProduct_irr_decomp {ι : Type u} [Fintype ι]
    {χs : ι → ClassFunction G} {ms : ι → ℤ}
    (hirr : ∀ i, IsIrreducibleCharacter (χs i))
    (hdist : ∀ i j, i ≠ j → χs i ≠ χs j) (i : ι) :
    scalarProduct G (χs i) (∑ j, (ms j : ℂ) • χs j) = (ms i : ℂ) := by
  classical
  rw [scalarProduct_sum_right]
  calc
    ∑ j, scalarProduct G (χs i) ((ms j : ℂ) • χs j)
        = ∑ j, scalarProduct G (χs i) (χs j) * star (ms j : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            exact scalarProduct_smul_right (ms j : ℂ) (χs i) (χs j)
    _ = scalarProduct G (χs i) (χs i) * star (ms i : ℂ) := by
            refine Finset.sum_eq_single i ?_ ?_
            · intro j hj hji
              simp [irreducible_scalarProduct_of_ne (hirr i) (hirr j) (hdist i j hji.symm)]
            · intro hnot
              exact (hnot (Finset.mem_univ i)).elim
    _ = (ms i : ℂ) := by simp [irreducible_scalarProduct_self (hirr i)]

/-- Disjoint generalized characters have zero scalar product. -/
private lemma scalarProduct_eq_zero_of_disjoint {φ ψ : ClassFunction G}
    (hφ : IsGeneralizedCharacter φ)
    (hψ : IsGeneralizedCharacter ψ) (h : Disjoint φ ψ) :
    scalarProduct G φ ψ = 0 := by
  classical
  rcases char_decomp_generalized hφ with ⟨ι₁, _, χs, ms, hirr, hdist, hφsum⟩
  rcases char_decomp_generalized hψ with ⟨ι₂, _, ηs, ns, hirr₂, hdist₂, hψsum⟩
  rw [hφsum, hψsum]
  rw [scalarProduct_sum_left]
  refine Finset.sum_eq_zero ?_
  intro i hi
  rw [scalarProduct_smul_left]
  by_cases hmi : ms i = 0
  · simp [hmi]
  · have hφi : scalarProduct G (χs i) (∑ j, (ms j : ℂ) • χs j) = (ms i : ℂ) :=
      scalarProduct_irr_decomp hirr hdist i
    have hφi_ne : scalarProduct G (χs i) φ ≠ 0 := by
      rw [hφsum]
      exact by
        rw [hφi]
        exact_mod_cast hmi
    have hzero : scalarProduct G (χs i) ψ = 0 := h (χs i) (hirr i) hφi_ne
    rw [hψsum] at hzero
    simp [hzero]

/-- Disjointness is symmetric. -/
private lemma disjoint_symm {φ ψ : ClassFunction G} (h : Theory.Character.Disjoint φ ψ) :
    Theory.Character.Disjoint ψ φ := by
  unfold Theory.Character.Disjoint at h ⊢
  intro χ hχ hχψ
  by_contra hχφ
  have hzero := h χ hχ hχφ
  exact hχψ hzero

/-- `ν̃` and `λ̃₂ν` are disjoint for `ν` fixed by `s` (Coherence 2.3(iii)). -/
private lemma tildeNu_disjoint_lambdaTwo (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) {ν : Irr (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1) :
    Theory.Character.Disjoint (tildeNu c h12 (lambdaTwoMul c h12 ν)) (tildeNu c h12 ν) := by
  have hμν : (lambdaTwoMul c h12 ν).1 ∈ orbit c.H0 c.U ν.1 := by
    exact Finset.mem_image.mpr ⟨lambdaTwo c h12, Finset.mem_univ _, rfl⟩
  have hνμ : ν.1 ≠ (lambdaTwoMul c h12 ν).1 := by
    intro hEq
    exact lambdaTwoMul_ne_self c h12 hSC hS4 ν (Subtype.ext hEq.symm)
  have hνs' : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ (lambdaTwoMul c h12 ν).1 := by
    intro hEq
    exact lambdaTwoMul_ne_self c h12 hSC hS4 ν (Subtype.ext (by simpa [hνs] using hEq.symm))
  exact tildeNu_disjoint c h12 hμν hνμ hνs'

/-- `χ ∈ ±Irr(G)` has scalar product `1` with itself. -/
private lemma scalarProduct_self_eq_one_of_isPMIrr {χ : ClassFunction G} (hχ : IsPMIrr G χ) :
    scalarProduct G χ χ = 1 := by
  rcases hχ with hχ | hχ
  · exact scalarProduct_irreducible_self hχ
  · have h' : scalarProduct G (-χ) (-χ) = 1 := scalarProduct_irreducible_self hχ
    rw [scalarProduct_neg_left, scalarProduct_neg_right] at h'
    simpa using h'

/-- `χ ∈ ±Irr(G)` has nonzero degree. -/
private lemma chi_one_ne_zero_of_isPMIrr {χ : ClassFunction G} (hχ : IsPMIrr G χ) : χ 1 ≠ 0 := by
  rcases hχ with h | h
  · exact irreducible_char_one_ne_zero h
  · have h' : (-χ) 1 ≠ 0 := irreducible_char_one_ne_zero h
    simpa using h'

/-- `B(χ)` cannot contain both members of a `Λ`-pair over `Δ`: `ν̃` and
`λ̃₂ν` are disjoint, so `χ ∈ ±Irr(G)` cannot be involved in both. -/
private lemma not_both_in_BOf (h12 : Hyp12 c) (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    {ν : Irr (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1) :
    ¬ (ν ∈ BOf c h12 χ ∧ lambdaTwoMul c h12 ν ∈ BOf c h12 χ) := by
  intro hboth
  rcases hboth with ⟨hνB, hlamB⟩
  have hνne : scalarProduct G χ (tildeNu c h12 ν) ≠ 0 :=
    (BOf_mem_iff c h12 χ ν).1 hνB
  have hlamne : scalarProduct G χ (tildeNu c h12 (lambdaTwoMul c h12 ν)) ≠ 0 :=
    (BOf_mem_iff c h12 χ (lambdaTwoMul c h12 ν)).1 hlamB
  have hdisj := tildeNu_disjoint_lambdaTwo c h12 hSC hS4 hνs
  rcases hχ with hχ | hχ
  · have hzero : scalarProduct G χ (tildeNu c h12 ν) = 0 :=
      hdisj χ hχ hlamne
    exact hνne hzero
  · have hψ : IsIrreducibleCharacter (-χ) := hχ
    have hψne : scalarProduct G (-χ) (tildeNu c h12 (lambdaTwoMul c h12 ν)) ≠ 0 := by
      rw [scalarProduct_neg_left]
      exact neg_ne_zero.mpr hlamne
    have hzero : scalarProduct G (-χ) (tildeNu c h12 ν) = 0 :=
      hdisj (-χ) hψ hψne
    have hzero' : scalarProduct G χ (tildeNu c h12 ν) = 0 := by
      have h' : -scalarProduct G χ (tildeNu c h12 ν) = 0 := by
        simpa [scalarProduct_neg_left] using hzero
      exact neg_eq_zero.mp h'
    exact hνne hzero'

/-- `λ₂ν ∉ Δ` for `ν ∈ Δ`. -/
private lemma lambdaTwoMul_not_mem_DeltaSet (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) {ν : Irr (↥c.H0)}
    (hν : ν ∈ DeltaSet c h12) :
    lambdaTwoMul c h12 ν ∉ DeltaSet c h12 := by
  intro hlam
  have hlamt := DeltaSet_mem_t c h12 hlam
  have hνt := DeltaSet_mem_t c h12 hν
  have hν1 : ν.1 1 ≠ 0 := irreducible_char_one_ne_zero ν.2
  have hneg : ((lambdaTwo c h12).1 (tH0 c) : ℂ) * ν.1 (tH0 c) = -ν.1 1 := by
    rw [hνt, lambdaTwo_val_tH0_eq_neg_one c h12 hSC hS4]
    ring
  have hdeg : (lambdaTwoMul c h12 ν).1 1 = ν.1 1 := by
    simp [lambdaTwoMul, LambdaChar]
  have hEq : (lambdaTwoMul c h12 ν).1 (tH0 c) = (lambdaTwoMul c h12 ν).1 1 := hlamt
  have hEq' : ((lambdaTwo c h12).1 (tH0 c) : ℂ) * ν.1 (tH0 c) = ν.1 1 := by
    simpa [lambdaTwoMul, LambdaChar, hdeg] using hEq
  have hbad : -ν.1 1 = ν.1 1 := hneg.symm.trans hEq'
  have h2 : (2 : ℂ) * ν.1 1 = 0 := by
    have hsum : ν.1 1 + ν.1 1 = 0 := by
      nth_rewrite 1 [← hbad]
      ring
    rw [two_mul]
    exact hsum
  exact (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hν1) h2

/-- For `μ` fixed by `s`, exactly one of `μ`, `λ₂μ` lies in `Δ`. -/
private lemma DeltaSet_or_lambdaTwo (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) {μ : Irr (↥c.H0)}
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1) :
    μ ∈ DeltaSet c h12 ∨ lambdaTwoMul c h12 μ ∈ DeltaSet c h12 := by
  have hsign := char_apply_central_sign (G := ↥c.H0) (t := tH0 c)
    (by simpa [tH0] using t_central_H0' c) (by simpa [tH0] using t_H0_sq c) μ.2
  rcases hsign with hpos | hneg
  · left
    exact (DeltaSet_mem_iff c h12 μ).mpr ⟨hμs, hpos⟩
  · right
    apply (DeltaSet_mem_iff c h12 (lambdaTwoMul c h12 μ)).mpr
    constructor
    · exact lambdaTwoMul_fixed_by_s c h12 hμs
    · have hdeg : (lambdaTwoMul c h12 μ).1 1 = μ.1 1 := by
        simp [lambdaTwoMul, LambdaChar]
      calc
        (lambdaTwoMul c h12 μ).1 (tH0 c)
            = ((lambdaTwo c h12).1 (tH0 c) : ℂ) * μ.1 (tH0 c) := by
                simp [lambdaTwoMul, LambdaChar]
        _ = (-1 : ℂ) * μ.1 (tH0 c) := by
                rw [lambdaTwo_val_tH0_eq_neg_one c h12 hSC hS4]
        _ = μ.1 1 := by rw [hneg]; ring
        _ = (lambdaTwoMul c h12 μ).1 1 := hdeg.symm

/-- Every `ν ∈ B′(χ)` has exactly one of `ν`, `λ₂ν` in `B(χ)`. -/
private lemma BPrime_iff_exactly_one (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) {χ : ClassFunction G}
    (hχ : IsPMIrr G χ)
    {ν : Irr (↥c.H0)} (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (hνt : ν.1 (tH0 c) = ν.1 1) :
    ν ∈ BPrimeOf c h12 χ ↔
      (ν ∈ BOf c h12 χ ∧ lambdaTwoMul c h12 ν ∉ BOf c h12 χ) ∨
      (ν ∉ BOf c h12 χ ∧ lambdaTwoMul c h12 ν ∈ BOf c h12 χ) := by
  classical
  constructor
  · intro hνBp
    have hδne : scalarProduct G χ (deltaNu c h12 ν) ≠ 0 :=
      (BPrime_mem_iff_scalar c h12 χ ν).1 hνBp |>.2.2
    have hnotboth : ¬ (ν ∈ BOf c h12 χ ∧ lambdaTwoMul c h12 ν ∈ BOf c h12 χ) :=
      not_both_in_BOf c h12 hSC hS4 hχ hνs
    have hatleast : ν ∈ BOf c h12 χ ∨ lambdaTwoMul c h12 ν ∈ BOf c h12 χ := by
      by_contra hnone
      have hν0 : scalarProduct G χ (tildeNu c h12 ν) = 0 := by
        by_contra h
        exact (not_or.mp hnone).1 ((BOf_mem_iff c h12 χ ν).mpr h)
      have hlam0 : scalarProduct G χ (tildeNu c h12 (lambdaTwoMul c h12 ν)) = 0 := by
        by_contra h
        exact (not_or.mp hnone).2 ((BOf_mem_iff c h12 χ (lambdaTwoMul c h12 ν)).mpr h)
      have hsc : scalarProduct G χ (deltaNu c h12 ν) = 0 := by
        rw [deltaNu_scalar_sub, hν0, hlam0]
        ring
      exact hδne hsc
    rcases hatleast with hνB | hlamB
    · exact Or.inl ⟨hνB, fun hlam => hnotboth ⟨hνB, hlam⟩⟩
    · exact Or.inr ⟨fun hν => hnotboth ⟨hν, hlamB⟩, hlamB⟩
  · intro hex
    rcases hex with ⟨hνB, hlamnot⟩ | ⟨hνnot, hlamB⟩
    · have hsc1 := BOf_scalar_eq_pm_one c h12 hχ hνB
      have hsc2 : scalarProduct G χ (tildeNu c h12 (lambdaTwoMul c h12 ν)) = 0 := by
        by_contra h
        exact hlamnot ((BOf_mem_iff c h12 χ (lambdaTwoMul c h12 ν)).mpr h)
      have hδne : scalarProduct G χ (deltaNu c h12 ν) ≠ 0 := by
        rw [deltaNu_scalar_sub]
        rcases hsc1 with h1 | h1
        · rw [h1, hsc2]
          norm_num
        · rw [h1, hsc2]
          norm_num
      exact (BPrime_mem_iff_scalar c h12 χ ν).mpr ⟨hνs, hνt, hδne⟩
    · have hsc2 := BOf_scalar_eq_pm_one c h12 hχ hlamB
      have hsc1 : scalarProduct G χ (tildeNu c h12 ν) = 0 := by
        by_contra h
        exact hνnot ((BOf_mem_iff c h12 χ ν).mpr h)
      have hδne : scalarProduct G χ (deltaNu c h12 ν) ≠ 0 := by
        rw [deltaNu_scalar_sub]
        rcases hsc2 with h2 | h2
        · rw [hsc1, h2]
          norm_num
        · rw [hsc1, h2]
          norm_num
      exact (BPrime_mem_iff_scalar c h12 χ ν).mpr ⟨hνs, hνt, hδne⟩

/-- `s`-conjugation is an involution on class functions of `H0`. -/
private lemma conjChar_sq (h12 : Hyp12 c) (φ : ClassFunction (↥c.H0)) :
    conjChar c.H0 (s_normalizes_H0 c h12)
      (conjChar c.H0 (s_normalizes_H0 c h12) φ) = φ := by
  ext x
  change φ (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12)
    (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) x)) = φ x
  congr 1
  apply Subtype.ext
  have hss : c.s * c.s = 1 := by simpa [pow_two] using c.s_involution.2
  calc
    c.s * (c.s * (x : G) * c.s⁻¹) * c.s⁻¹
        = (c.s * c.s) * (x : G) * (c.s⁻¹ * c.s⁻¹) := by group
    _ = 1 * (x : G) * 1 := by
          have hss' : c.s⁻¹ * c.s⁻¹ = 1 := by
            calc
              c.s⁻¹ * c.s⁻¹ = (c.s * c.s)⁻¹ := by group
              _ = 1 := by rw [hss]; simp
          rw [hss, hss']
    _ = (x : G) := by simp

/-- If `B(χ)` contains a character not fixed by `s`, then `B′(χ)` is empty
(Lemma 3.4: `B(χ) = {μ, μ^s}`). -/
public lemma BOf_mem_fixed_of_BPrime_nonempty (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) {χ : ClassFunction G}
    (hχ : IsPMIrr G χ)
    (hB' : (BPrimeOf c h12 χ).Nonempty) {μ : Irr (↥c.H0)} (hμB : μ ∈ BOf c h12 χ) :
    conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1 := by
  by_contra hμs
  have h34 := lemma_3_4 c h12 hSC hχ hμB hμs (Or.inr (orbit_card_eq_index_s4 c h12 hSC hS4 μ))
  rcases hB' with ⟨ν, hνBp⟩
  have hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 :=
    (BPrime_mem_iff_scalar c h12 χ ν).1 hνBp |>.1
  have hδne : scalarProduct G χ (deltaNu c h12 ν) ≠ 0 :=
    (BPrime_mem_iff_scalar c h12 χ ν).1 hνBp |>.2.2
  have hνnot : ν ∉ BOf c h12 χ := by
    intro hνB
    have hEqB : BOf c h12 χ = {μ, conjIrr c h12 μ} := h34.1
    have hcases : ν = μ ∨ ν = conjIrr c h12 μ := by
      rw [hEqB] at hνB
      simpa using hνB
    rcases hcases with hEq | hEq
    · exact hμs (by simpa [hEq] using hνs)
    · have hfix : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1 := by
        rw [hEq, conjIrr_coe, conjChar_sq c h12] at hνs
        exact hνs.symm
      exact hμs hfix
  have hlamnot : lambdaTwoMul c h12 ν ∉ BOf c h12 χ := by
    have hlams : conjChar c.H0 (s_normalizes_H0 c h12) (lambdaTwoMul c h12 ν).1 =
        (lambdaTwoMul c h12 ν).1 := lambdaTwoMul_fixed_by_s c h12 hνs
    intro hlamB
    have hEqB : BOf c h12 χ = {μ, conjIrr c h12 μ} := h34.1
    have hcases : lambdaTwoMul c h12 ν = μ ∨ lambdaTwoMul c h12 ν = conjIrr c h12 μ := by
      rw [hEqB] at hlamB
      simpa using hlamB
    rcases hcases with hEq | hEq
    · exact hμs (by simpa [hEq] using hlams)
    · have hfix : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1 := by
        rw [hEq, conjIrr_coe, conjChar_sq c h12] at hlams
        exact hlams.symm
      exact hμs hfix
  have hδ0 : scalarProduct G χ (deltaNu c h12 ν) = 0 := by
    rw [deltaNu_scalar_sub]
    have hsc1 : scalarProduct G χ (tildeNu c h12 ν) = 0 := by
      by_contra h
      exact hνnot ((BOf_mem_iff c h12 χ ν).mpr h)
    have hsc2 : scalarProduct G χ (tildeNu c h12 (lambdaTwoMul c h12 ν)) = 0 := by
      by_contra h
      exact hlamnot ((BOf_mem_iff c h12 χ (lambdaTwoMul c h12 ν)).mpr h)
    rw [hsc1, hsc2]
    ring
  exact hδne hδ0

/-! ## The bijection `B′(χ) ≃ B(χ)` and the cardinality `1` or `3` -/

/-- `ν ∈ B′(χ)` gives `ν ∈ Δ`. -/
private lemma DeltaSet_of_BPrime (h12 : Hyp12 c) {χ : ClassFunction G}
    {ν : Irr (↥c.H0)} (hνBp : ν ∈ BPrimeOf c h12 χ) : ν ∈ DeltaSet c h12 := by
  exact (DeltaSet_mem_iff c h12 ν).mpr ⟨(BPrime_mem_iff_scalar c h12 χ ν).1 hνBp |>.1,
    (BPrime_mem_iff_scalar c h12 χ ν).1 hνBp |>.2.1⟩

/-- `λ₂(λ₂ν) = ν`. -/
private lemma lambdaTwoMul_sq (h12 : Hyp12 c) (ν : Irr (↥c.H0)) :
    lambdaTwoMul c h12 (lambdaTwoMul c h12 ν) = ν := by
  apply Subtype.ext
  funext x
  have hsq : (lambdaTwo c h12) ^ 2 = (1 : LambdaHom c.H0 c.U) := lambdaTwo_sq_eq_one c h12
  have hx : ((lambdaTwo c h12).1 x : ℂ) * ((lambdaTwo c h12).1 x : ℂ) = 1 := by
    have hpow : (((lambdaTwo c h12) ^ 2).1 x : ℂ) =
        ((lambdaTwo c h12).1 x : ℂ) * ((lambdaTwo c h12).1 x : ℂ) := by
      simp [pow_two]
    have hsq' : (((lambdaTwo c h12) ^ 2).1 x : ℂ) = 1 := by
      exact congrArg (fun l : LambdaHom c.H0 c.U => (l.1 x : ℂ)) hsq
    simpa [← hpow] using hsq'
  change ((lambdaTwo c h12).1 x : ℂ) * (((lambdaTwo c h12).1 x : ℂ) * ν.1 x) = ν.1 x
  rw [← mul_assoc, hx, one_mul]

/-- The map `B′(χ) → B(χ)` sending `ν` to the unique member of
`{ν, λ₂ν} ∩ B(χ)`. -/
private noncomputable def BPrimeToBOf (h12 : Hyp12 c) (χ : ClassFunction G)
    (ν : Irr (↥c.H0)) : Irr (↥c.H0) :=
  if _hνB : ν ∈ BOf c h12 χ then ν else lambdaTwoMul c h12 ν

/-- `BPrimeToBOf` maps to one of the two pair members. -/
private lemma BPrimeToBOf_eq_self_or_lambda (h12 : Hyp12 c) (χ : ClassFunction G)
    (ν : Irr (↥c.H0)) :
    BPrimeToBOf c h12 χ ν = ν ∨ BPrimeToBOf c h12 χ ν = lambdaTwoMul c h12 ν := by
  classical
  by_cases h : ν ∈ BOf c h12 χ
  · left
    simp [BPrimeToBOf, h]
  · right
    simp [BPrimeToBOf, h]

/-- `BPrimeToBOf` lands in `B(χ)`. -/
private lemma BPrimeToBOf_mem (h12 : Hyp12 c) (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    {ν : Irr (↥c.H0)} (hνBp : ν ∈ BPrimeOf c h12 χ) :
    BPrimeToBOf c h12 χ ν ∈ BOf c h12 χ := by
  have hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 :=
    DeltaSet_mem_fixed c h12 (DeltaSet_of_BPrime c h12 hνBp)
  have hνt : ν.1 (tH0 c) = ν.1 1 :=
    DeltaSet_mem_t c h12 (DeltaSet_of_BPrime c h12 hνBp)
  rcases (BPrime_iff_exactly_one c h12 hSC hS4 hχ hνs hνt).1 hνBp with
    ⟨hνB, _⟩ | ⟨hνnot, hlamB⟩
  · rw [BPrimeToBOf, dif_pos hνB]
    exact hνB
  · rw [BPrimeToBOf, dif_neg hνnot]
    exact hlamB

/-- `BPrimeToBOf` is injective on `B′(χ)`. -/
private lemma BPrimeToBOf_injective (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) {χ : ClassFunction G} (_hχ : IsPMIrr G χ)
    (_hB' : (BPrimeOf c h12 χ).Nonempty) :
    Set.InjOn (BPrimeToBOf c h12 χ) (↑(BPrimeOf c h12 χ)) := by
  intro ν hν μ hμ hEq
  have hνΔ := DeltaSet_of_BPrime c h12 hν
  have hμΔ := DeltaSet_of_BPrime c h12 hμ
  rcases BPrimeToBOf_eq_self_or_lambda c h12 χ ν with hπν | hπν
  · rcases BPrimeToBOf_eq_self_or_lambda c h12 χ μ with hπμ | hπμ
    · simpa [hπν, hπμ] using hEq
    · have hEq' : ν = lambdaTwoMul c h12 μ := by simpa [hπν, hπμ] using hEq
      have hlam2ν : lambdaTwoMul c h12 ν = μ := by
        simpa [lambdaTwoMul_sq] using congrArg (lambdaTwoMul c h12) hEq'
      exfalso
      exact lambdaTwoMul_not_mem_DeltaSet c h12 hSC hS4 hνΔ (by simpa [hlam2ν] using hμΔ)
  · rcases BPrimeToBOf_eq_self_or_lambda c h12 χ μ with hπμ | hπμ
    · have hEq' : lambdaTwoMul c h12 ν = μ := by simpa [hπν, hπμ] using hEq
      exfalso
      exact lambdaTwoMul_not_mem_DeltaSet c h12 hSC hS4 hνΔ (by simpa [hEq'] using hμΔ)
    · have hEq' : lambdaTwoMul c h12 ν = lambdaTwoMul c h12 μ := by
        simpa [hπν, hπμ] using hEq
      simpa [lambdaTwoMul_sq] using congrArg (lambdaTwoMul c h12) hEq'

/-- `BPrimeToBOf` is surjective onto `B(χ)`. -/
private lemma BPrimeToBOf_surj (h12 : Hyp12 c) (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) (hB' : (BPrimeOf c h12 χ).Nonempty) :
    ∀ μ ∈ BOf c h12 χ, ∃ ν ∈ BPrimeOf c h12 χ, BPrimeToBOf c h12 χ ν = μ := by
  intro μ hμB
  have hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1 :=
    BOf_mem_fixed_of_BPrime_nonempty c h12 hSC hS4 hχ hB' hμB
  rcases DeltaSet_or_lambdaTwo c h12 hSC hS4 hμs with hμΔ | hlamΔ
  · refine ⟨μ, ?_, ?_⟩
    · exact (BPrime_iff_exactly_one c h12 hSC hS4 hχ hμs (DeltaSet_mem_t c h12 hμΔ)).mpr
        (Or.inl ⟨hμB, fun hlam =>
          not_both_in_BOf c h12 hSC hS4 hχ hμs ⟨hμB, hlam⟩⟩)
    · rw [BPrimeToBOf, dif_pos hμB]
  · have hνs : conjChar c.H0 (s_normalizes_H0 c h12) (lambdaTwoMul c h12 μ).1 =
      (lambdaTwoMul c h12 μ).1 := lambdaTwoMul_fixed_by_s c h12 hμs
    have hνt : (lambdaTwoMul c h12 μ).1 (tH0 c) = (lambdaTwoMul c h12 μ).1 1 :=
      DeltaSet_mem_t c h12 hlamΔ
    have hνnot : lambdaTwoMul c h12 μ ∉ BOf c h12 χ := by
      intro hlam
      exact not_both_in_BOf c h12 hSC hS4 hχ hμs ⟨hμB, hlam⟩
    refine ⟨lambdaTwoMul c h12 μ, ?_, ?_⟩
    · exact (BPrime_iff_exactly_one c h12 hSC hS4 hχ hνs hνt).mpr
        (Or.inr ⟨hνnot, by simpa [lambdaTwoMul_sq] using hμB⟩)
    · rw [BPrimeToBOf, dif_neg hνnot]
      exact lambdaTwoMul_sq c h12 μ

/-- `|B′(χ)| = |B(χ)|`. -/
private lemma BPrime_card_eq_BOf_card (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    (hB' : (BPrimeOf c h12 χ).Nonempty) :
    (BPrimeOf c h12 χ).card = (BOf c h12 χ).card := by
  exact Finset.card_bij (fun ν hν => BPrimeToBOf c h12 χ ν)
    (fun ν hν => BPrimeToBOf_mem c h12 hSC hS4 hχ hν)
    (fun ν hν μ hμ hEq => BPrimeToBOf_injective c h12 hSC hS4 hχ hB' hν hμ hEq)
    (fun μ hμ => by
      rcases BPrimeToBOf_surj c h12 hSC hS4 hχ hB' μ hμ with ⟨ν, hν, hEq⟩
      exact ⟨ν, hν, hEq⟩)

/-- `|B(χ)| ∈ {1, 3}` (Lemmas 3.2–3.4; all members fixed and no `Λ`-pair
meets `B(χ)` twice). -/
private lemma BOf_card_eq_one_or_three (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    (hB' : (BPrimeOf c h12 χ).Nonempty) :
    (BOf c h12 χ).card = 1 ∨ (BOf c h12 χ).card = 3 := by
  classical
  have hle : (BOf c h12 χ).card ≤ 3 := theorem_3_2 c h12 hSC hχ
  have hne0 : (BOf c h12 χ).card ≠ 0 := by
    rcases hB' with ⟨ν, hνBp⟩
    have hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 :=
      DeltaSet_mem_fixed c h12 (DeltaSet_of_BPrime c h12 hνBp)
    have hνt : ν.1 (tH0 c) = ν.1 1 :=
      DeltaSet_mem_t c h12 (DeltaSet_of_BPrime c h12 hνBp)
    rcases (BPrime_iff_exactly_one c h12 hSC hS4 hχ hνs hνt).1 hνBp with
      ⟨hνB, _⟩ | ⟨_, hlamB⟩
    · exact Finset.card_ne_zero_of_mem hνB
    · exact Finset.card_ne_zero_of_mem hlamB
  have hne2 : (BOf c h12 χ).card ≠ 2 := by
    intro hcard2
    rcases (Finset.card_eq_two).mp hcard2 with ⟨μ1, μ2, hμ12, hF⟩
    have hmem1 : μ1 ∈ BOf c h12 χ := by rw [hF]; simp
    have hmem2 : μ2 ∈ BOf c h12 χ := by rw [hF]; simp
    have hfix1 : conjChar c.H0 (s_normalizes_H0 c h12) μ1.1 = μ1.1 :=
      BOf_mem_fixed_of_BPrime_nonempty c h12 hSC hS4 hχ hB' hmem1
    have hfix2 : conjChar c.H0 (s_normalizes_H0 c h12) μ2.1 = μ2.1 :=
      BOf_mem_fixed_of_BPrime_nonempty c h12 hSC hS4 hχ hB' hmem2
    have h33 := lemma_3_3 c h12 hSC hχ ⟨μ1, μ2, hmem1, hmem2, hμ12, hfix1, hfix2,
      orbit_card_eq_index_s4 c h12 hSC hS4 μ1, orbit_card_eq_index_s4 c h12 hSC hS4 μ2⟩
    have hfilter : (BOf c h12 χ).filter (fun ν : Irr (↥c.H0) =>
        conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 ∧
          (orbit c.H0 c.U ν.1).card = (c.U.subgroupOf c.H0).index) = BOf c h12 χ := by
      apply Finset.filter_eq_self.mpr
      intro μ hμ
      exact ⟨BOf_mem_fixed_of_BPrime_nonempty c h12 hSC hS4 hχ hB' hμ,
        orbit_card_eq_index_s4 c h12 hSC hS4 μ⟩
    have hcard3 : (BOf c h12 χ).card = 3 := by
      simpa [hfilter] using h33.1
    omega
  have hcases : (BOf c h12 χ).card = 0 ∨ (BOf c h12 χ).card = 1 ∨
      (BOf c h12 χ).card = 2 ∨ (BOf c h12 χ).card = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · exact False.elim (hne0 h0)
  · exact Or.inl h1
  · exact False.elim (hne2 h2)
  · exact Or.inr h3

/-- `|B′(χ)| ∈ {1, 3}` (Lemma 4.1(i)). -/
private lemma BPrime_card_eq_one_or_three (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    (hB' : (BPrimeOf c h12 χ).Nonempty) :
    (BPrimeOf c h12 χ).card = 1 ∨ (BPrimeOf c h12 χ).card = 3 := by
  have hcard := BPrime_card_eq_BOf_card c h12 hSC hS4 hχ hB'
  rcases BOf_card_eq_one_or_three c h12 hSC hS4 hχ hB' with h1 | h3
  · left
    exact hcard.trans h1
  · right
    exact hcard.trans h3

/-! ## Evaluation at `t` and congruence on `B` -/

/-- `(χ, δν)·ν(1) = (χ,ν̃)·ν(t) + (χ,λ̃₂ν)·λ₂ν(t)` for `ν ∈ Δ`. -/
private lemma sum_pair_at_t (h12 : Hyp12 c) (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {χ : ClassFunction G} (_hχ : IsPMIrr G χ) {ν : Irr (↥c.H0)}
    (hνΔ : ν ∈ DeltaSet c h12) :
    (∑ μ ∈ ({ν, lambdaTwoMul c h12 ν} : Finset (Irr (↥c.H0))).filter
        (fun μ => μ ∈ BOf c h12 χ),
      scalarProduct G χ (tildeNu c h12 μ) * μ.1 (tH0 c)) =
      scalarProduct G χ (deltaNu c h12 ν) * ν.1 1 := by
  classical
  have hne : ν ≠ lambdaTwoMul c h12 ν :=
    (lambdaTwoMul_ne_self c h12 hSC hS4 ν).symm
  have hνt : ν.1 (tH0 c) = ν.1 1 := DeltaSet_mem_t c h12 hνΔ
  have hlamt : (lambdaTwoMul c h12 ν).1 (tH0 c) = -ν.1 1 := by
    calc
      (lambdaTwoMul c h12 ν).1 (tH0 c)
          = ((lambdaTwo c h12).1 (tH0 c) : ℂ) * ν.1 (tH0 c) := by
              simp [lambdaTwoMul, LambdaChar]
      _ = (-1 : ℂ) * ν.1 (tH0 c) := by
              rw [lambdaTwo_val_tH0_eq_neg_one c h12 hSC hS4]
      _ = -ν.1 1 := by rw [hνt]; ring
  rw [Finset.sum_filter, Finset.sum_pair hne]
  rw [BOf_term_eq h12 χ, BOf_term_eq h12 χ]
  rw [hνt, hlamt]
  rw [deltaNu_scalar_sub]
  ring
where
  BOf_term_eq (h12 : Hyp12 c) (χ : ClassFunction G) (ν : Irr (↥c.H0)) :
      (if ν ∈ BOf c h12 χ then scalarProduct G χ (tildeNu c h12 ν) * ν.1 (tH0 c) else 0) =
        scalarProduct G χ (tildeNu c h12 ν) * ν.1 (tH0 c) := by
    classical
    by_cases h : ν ∈ BOf c h12 χ
    · simp [h]
    · have hsc : scalarProduct G χ (tildeNu c h12 ν) = 0 := by
        by_contra hsc
        exact h ((BOf_mem_iff c h12 χ ν).mpr hsc)
      simp [h, hsc]

/-- The `B(χ)`-sum at `t` is the `B′(χ)`-sum (Lemma 4.1(ii)). -/
private lemma sum_BOf_at_t_eq_sum_BPrime (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    (hB' : (BPrimeOf c h12 χ).Nonempty) :
    (∑ μ ∈ BOf c h12 χ, scalarProduct G χ (tildeNu c h12 μ) * μ.1 (tH0 c)) =
      ∑ ν ∈ BPrimeOf c h12 χ, scalarProduct G χ (deltaNu c h12 ν) * ν.1 1 := by
  classical
  have h1' : (∑ ν ∈ BPrimeOf c h12 χ,
        (∑ μ ∈ ({ν, lambdaTwoMul c h12 ν} : Finset (Irr (↥c.H0))).filter
            (fun μ => μ ∈ BOf c h12 χ),
          scalarProduct G χ (tildeNu c h12 μ) * μ.1 (tH0 c))) =
      ∑ μ ∈ BOf c h12 χ, scalarProduct G χ (tildeNu c h12 μ) * μ.1 (tH0 c) := by
    refine Finset.sum_bij (fun ν hν => BPrimeToBOf c h12 χ ν)
      (fun ν hν => BPrimeToBOf_mem c h12 hSC hS4 hχ hν)
      (fun ν hν μ hμ hEq => BPrimeToBOf_injective c h12 hSC hS4 hχ hB' hν hμ hEq)
      (fun μ hμ => by
        rcases BPrimeToBOf_surj c h12 hSC hS4 hχ hB' μ hμ with ⟨ν, hν, hEq⟩
        exact ⟨ν, hν, hEq⟩) ?_
    intro ν hν
    calc
      (∑ μ ∈ ({ν, lambdaTwoMul c h12 ν} : Finset (Irr (↥c.H0))).filter
          (fun μ => μ ∈ BOf c h12 χ),
        scalarProduct G χ (tildeNu c h12 μ) * μ.1 (tH0 c))
          = scalarProduct G χ (deltaNu c h12 ν) * ν.1 1 :=
              sum_pair_at_t c h12 hSC hS4 hχ (DeltaSet_of_BPrime c h12 hν)
      _ = scalarProduct G χ (tildeNu c h12 (BPrimeToBOf c h12 χ ν)) *
            (BPrimeToBOf c h12 χ ν).1 (tH0 c) := by
              rw [BPrimeToBOf_at_t_eq_delta h12 hSC hS4 hχ hν]
  have h1 : (∑ μ ∈ BOf c h12 χ, scalarProduct G χ (tildeNu c h12 μ) * μ.1 (tH0 c)) =
      ∑ ν ∈ BPrimeOf c h12 χ,
        (∑ μ ∈ ({ν, lambdaTwoMul c h12 ν} : Finset (Irr (↥c.H0))).filter
            (fun μ => μ ∈ BOf c h12 χ),
          scalarProduct G χ (tildeNu c h12 μ) * μ.1 (tH0 c)) := h1'.symm
  have h2 : (∑ ν ∈ BPrimeOf c h12 χ,
        (∑ μ ∈ ({ν, lambdaTwoMul c h12 ν} : Finset (Irr (↥c.H0))).filter
            (fun μ => μ ∈ BOf c h12 χ),
          scalarProduct G χ (tildeNu c h12 μ) * μ.1 (tH0 c))) =
      ∑ ν ∈ BPrimeOf c h12 χ, scalarProduct G χ (deltaNu c h12 ν) * ν.1 1 := by
    refine Finset.sum_congr rfl ?_
    intro ν hν
    exact sum_pair_at_t c h12 hSC hS4 hχ (DeltaSet_of_BPrime c h12 hν)
  exact h1.trans h2
where
  BPrimeToBOf_at_t_eq_delta (h12 : Hyp12 c) (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
      {χ : ClassFunction G} (hχ : IsPMIrr G χ) {ν : Irr (↥c.H0)}
      (hνBp : ν ∈ BPrimeOf c h12 χ) :
      scalarProduct G χ (tildeNu c h12 (BPrimeToBOf c h12 χ ν)) *
          (BPrimeToBOf c h12 χ ν).1 (tH0 c) =
        scalarProduct G χ (deltaNu c h12 ν) * ν.1 1 := by
    have hνΔ := DeltaSet_of_BPrime c h12 hνBp
    have hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 :=
      DeltaSet_mem_fixed c h12 hνΔ
    have hνt : ν.1 (tH0 c) = ν.1 1 := DeltaSet_mem_t c h12 hνΔ
    have hex := (BPrime_iff_exactly_one c h12 hSC hS4 hχ hνs hνt).1 hνBp
    rcases BPrimeToBOf_eq_self_or_lambda c h12 χ ν with hπ | hπ
    · have hνF : ν ∈ BOf c h12 χ := by
        by_contra h
        have hπ' : BPrimeToBOf c h12 χ ν = lambdaTwoMul c h12 ν := by
          simp [BPrimeToBOf, h]
        have hEqν : lambdaTwoMul c h12 ν = ν := by
          rw [hπ] at hπ'
          exact hπ'.symm
        exact lambdaTwoMul_ne_self c h12 hSC hS4 ν hEqν
      have hsc2 : scalarProduct G χ (tildeNu c h12 (lambdaTwoMul c h12 ν)) = 0 := by
        rcases hex with ⟨_, hlamnot⟩ | ⟨hνnot, _⟩
        · by_contra hsc
          exact hlamnot ((BOf_mem_iff c h12 χ (lambdaTwoMul c h12 ν)).mpr hsc)
        · exact False.elim (hνnot hνF)
      rw [hπ, deltaNu_scalar_sub, hνt, hsc2]
      ring
    · have hνnot : ν ∉ BOf c h12 χ := by
        by_contra h
        have hπ' : BPrimeToBOf c h12 χ ν = ν := by
          simp [BPrimeToBOf, h]
        have hEqν : lambdaTwoMul c h12 ν = ν := by
          rw [hπ'] at hπ
          exact hπ.symm
        exact lambdaTwoMul_ne_self c h12 hSC hS4 ν hEqν
      have hsc1 : scalarProduct G χ (tildeNu c h12 ν) = 0 := by
        by_contra hsc
        exact hνnot ((BOf_mem_iff c h12 χ ν).mpr hsc)
      have hlamt : (lambdaTwoMul c h12 ν).1 (tH0 c) = -ν.1 1 := by
        calc
          (lambdaTwoMul c h12 ν).1 (tH0 c)
              = ((lambdaTwo c h12).1 (tH0 c) : ℂ) * ν.1 (tH0 c) := by
                  simp [lambdaTwoMul, LambdaChar]
          _ = (-1 : ℂ) * ν.1 (tH0 c) := by
                  rw [lambdaTwo_val_tH0_eq_neg_one c h12 hSC hS4]
          _ = -ν.1 1 := by rw [hνt]; ring
      rw [hπ, deltaNu_scalar_sub, hsc1, hlamt]
      ring

/-! ## Congruence on `B`, odd degree, and the normalizer invariance -/

/-- `B ≤ H0` (through `B ≤ U ≤ H0`). -/
private lemma mem_H0_of_mem_B_s4 (c : Hyp11 G) {b : ↥c.B} : (b : G) ∈ c.H0 :=
  U_le_H0 c (mem_U_of_mem_B_s4 c b.2)

/-- The value of `restrictU` at `u` uses the `U ≤ H0` membership. -/
private lemma restrictU_apply (h12 : Hyp12 c) (μ : ClassFunction (↥c.H0)) (u : ↥c.U) :
    restrictU c h12 μ u = μ ⟨(u : G), U_le_H0 c u.2⟩ := by
  unfold restrictU
  congr 1

/-- `|B|` is odd. -/
private lemma B_coprime_two (c : Hyp11 G) : Nat.Coprime 2 (Nat.card (↥c.B)) := by
  have hEq : Nat.card (↥c.B) = Nat.card (↥(fixedSubgroup (c.S : Subgroup G) c.U)) := by
    exact Nat.card_congr (B_fixedSubgroup_equiv c)
  have hdiv : Nat.card (↥(fixedSubgroup (c.S : Subgroup G) c.U)) ∣ Nat.card (↥c.U) :=
    Subgroup.card_subgroup_dvd_card (fixedSubgroup (c.S : Subgroup G) c.U)
  rw [hEq]
  exact Nat.Coprime.of_dvd_right hdiv (U_coprime_two c)

/-- For `ν ∈ B′(χ)`, the pair value `BPrimeToBOf ν` agrees with `ν` on `B`. -/
private lemma BPrimeToBOf_value_on_B_eq (h12 : Hyp12 c) (_hSC : Section3Hyp c)
    (_hS4 : Section4Hyp c) {χ : ClassFunction G} (_hχ : IsPMIrr G χ) {ν : Irr (↥c.H0)}
    (_hνBp : ν ∈ BPrimeOf c h12 χ) {b : ↥c.B} (hb : (b : G) ∈ c.H0) :
    (BPrimeToBOf c h12 χ ν).1 ⟨(b : G), hb⟩ = ν.1 ⟨(b : G), hb⟩ := by
  classical
  rcases BPrimeToBOf_eq_self_or_lambda c h12 χ ν with hπ | hπ
  · rw [hπ]
  · rw [hπ]
    have hbU : (b : G) ∈ c.U := mem_U_of_mem_B_s4 c b.2
    have hl1 : ((lambdaTwo c h12).1 ⟨(b : G), hb⟩ : ℂ) = 1 :=
      congrArg (fun u : ℂˣ => (u : ℂ)) ((lambdaTwo c h12).2 ⟨(b : G), hb⟩ hbU)
    calc
      (lambdaTwoMul c h12 ν).1 ⟨(b : G), hb⟩
          = ((lambdaTwo c h12).1 ⟨(b : G), hb⟩ : ℂ) * ν.1 ⟨(b : G), hb⟩ := by
              simp [lambdaTwoMul, LambdaChar]
      _ = ν.1 ⟨(b : G), hb⟩ := by rw [hl1]; simp

/-- Pointwise congruences sum over a finset. -/
private lemma sum_congr_mem {α : Type u} (s : Finset α) (f g : α → ℂ)
    (h : ∀ a ∈ s, CongruentModTwo (f a) (g a)) :
    CongruentModTwo (∑ a ∈ s, f a) (∑ a ∈ s, g a) := by
  classical
  let P : Finset α → Prop := fun t =>
    (∀ a ∈ t, CongruentModTwo (f a) (g a)) → CongruentModTwo (∑ a ∈ t, f a) (∑ a ∈ t, g a)
  have hP : ∀ t, P t := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · intro _
      exact CongruentModTwo.refl 0
    · intro a u hau ih hh
      rw [Finset.sum_insert hau, Finset.sum_insert hau]
      exact (hh a (Finset.mem_insert_self a u)).add
        (ih (fun b hb => hh b (Finset.mem_insert_of_mem hb)))
  exact hP s h

/-- Lemma 4.1(iii): `χ ≡ Σ_{ν∈B′(χ)} ν̂` on `B`. -/
private lemma congruent_on_B (h12 : Hyp12 c) (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) (hB' : (BPrimeOf c h12 χ).Nonempty)
    (b : ↥c.B) (hb : (b : G) ∈ c.H0) :
    CongruentModTwo (χ (b : G))
      (∑ ν ∈ BPrimeOf c h12 χ, (nuHat c h12 ν).1 b) := by
  classical
  have h24 := (lemma_2_4 c h12 hχ).2 ⟨(b : G), mem_U_of_mem_B_s4 c b.2⟩ hb
  have hEq' : (∑ ν ∈ BPrimeOf c h12 χ, ν.1 ⟨(b : G), hb⟩) =
      ∑ μ ∈ BOf c h12 χ, μ.1 ⟨(b : G), hb⟩ := by
    refine Finset.sum_bij (fun ν hν => BPrimeToBOf c h12 χ ν)
      (fun ν hν => BPrimeToBOf_mem c h12 hSC hS4 hχ hν)
      (fun ν hν μ hμ hEq' => BPrimeToBOf_injective c h12 hSC hS4 hχ hB' hν hμ hEq')
      (fun μ hμ => by
        rcases BPrimeToBOf_surj c h12 hSC hS4 hχ hB' μ hμ with ⟨ν, hν, hEq'⟩
        exact ⟨ν, hν, hEq'⟩) ?_
    intro ν hν
    exact (BPrimeToBOf_value_on_B_eq c h12 hSC hS4 hχ hν hb).symm
  have hEq : (∑ μ ∈ BOf c h12 χ, μ.1 ⟨(b : G), hb⟩) =
      ∑ ν ∈ BPrimeOf c h12 χ, ν.1 ⟨(b : G), hb⟩ := hEq'.symm
  have hnu : CongruentModTwo
      (∑ ν ∈ BPrimeOf c h12 χ, ν.1 ⟨(b : G), hb⟩)
      (∑ ν ∈ BPrimeOf c h12 χ, (nuHat c h12 ν).1 b) := by
    exact sum_congr_mem (BPrimeOf c h12 χ) (fun ν => ν.1 ⟨(b : G), hb⟩)
      (fun ν => (nuHat c h12 ν).1 b) (fun ν hν =>
        (nuHat_congruence c h12 hSC hS4
          (DeltaSet_mem_fixed c h12 (DeltaSet_of_BPrime c h12 hν))
          (DeltaSet_mem_t c h12 (DeltaSet_of_BPrime c h12 hν)) b hb).symm)
  have hmid : CongruentModTwo (χ (b : G))
      (∑ ν ∈ BPrimeOf c h12 χ, ν.1 ⟨(b : G), hb⟩) := by
    simpa using h24.trans (CongruentModTwo.of_eq hEq)
  exact hmid.trans hnu

/-- Lemma 4.1(iv): `χ(1)` is odd. -/
private lemma chi_one_odd (h12 : Hyp12 c) (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) (hB' : (BPrimeOf c h12 χ).Nonempty) :
    ∃ n : ℤ, (n : ℂ) = χ 1 ∧ Odd n := by
  classical
  have hiii : ∀ b : ↥c.B, (hb : (b : G) ∈ c.H0) →
      CongruentModTwo (χ (b : G)) (∑ ν ∈ BPrimeOf c h12 χ, (nuHat c h12 ν).1 b) :=
    fun b hb => congruent_on_B c h12 hSC hS4 hχ hB' b hb
  have hcong := hiii 1 (c.H0.one_mem)
  have hterm : ∀ ν ∈ BPrimeOf c h12 χ, CongruentModTwo ((nuHat c h12 ν).1 1) (1 : ℂ) := by
    intro ν hν
    rcases irr_degree_odd (B_coprime_two c) (nuHat c h12 ν) with ⟨d, hdodd, hd⟩
    have hcong' : CongruentModTwo ((d : ℂ)) (1 : ℂ) := by
      simpa using CongruentModTwo.odd_mul_congr hdodd (isIntegral_one)
    simpa [hd] using hcong'
  have hsum : CongruentModTwo
      (∑ ν ∈ BPrimeOf c h12 χ, (nuHat c h12 ν).1 1)
      ((BPrimeOf c h12 χ).card : ℂ) := by
    have h' : CongruentModTwo
        (∑ ν ∈ BPrimeOf c h12 χ, (nuHat c h12 ν).1 1)
        (∑ ν ∈ BPrimeOf c h12 χ, (1 : ℂ)) :=
      sum_congr_mem (BPrimeOf c h12 χ) (fun ν => (nuHat c h12 ν).1 1)
        (fun _ => (1 : ℂ)) (fun ν hν => hterm ν hν)
    simpa using h'
  have hcard : CongruentModTwo ((BPrimeOf c h12 χ).card : ℂ) (1 : ℂ) := by
    rcases BPrime_card_eq_one_or_three c h12 hSC hS4 hχ hB' with h1 | h3
    · rw [h1]
      simpa using CongruentModTwo.refl (1 : ℂ)
    · rw [h3]
      simpa using (CongruentModTwo.odd_mul_congr (n := 3) (by decide : Odd (3 : ℕ)) (isIntegral_one))
  have hcong2 : CongruentModTwo (χ 1) ((BPrimeOf c h12 χ).card : ℂ) := hcong.trans hsum
  have hcong1 : CongruentModTwo (χ 1) (1 : ℂ) := hcong2.trans hcard
  rcases pmIrr_one_int hχ with ⟨m, hm⟩
  have hcongm : CongruentModTwo ((m : ℂ)) ((1 : ℤ) : ℂ) := by
    simpa [hm] using hcong1
  have hdvd : (2 : ℤ) ∣ m - 1 := CongruentModTwo.eq_of_int hcongm
  refine ⟨m, hm, ?_⟩
  rcases hdvd with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  omega

/-! ## The normalizer invariance (Lemma 4.1(v)) -/

/-- `S0 = {1, t}` in the Section-4 case. -/
private lemma S0_pair (hS4 : Section4Hyp c) (r : ↥(c.S0 : Subgroup G)) :
    r = 1 ∨ r = ⟨c.t, c.t_mem_S0⟩ := by
  classical
  have hcard : Nat.card (↥(c.S0 : Subgroup G)) = 2 := S0_card_eq_two c hS4
  have htne : (⟨c.t, c.t_mem_S0⟩ : ↥(c.S0 : Subgroup G)) ≠ (1 : ↥(c.S0 : Subgroup G)) := by
    intro hEq
    exact c.t_involution.1 (by simpa using (congrArg Subtype.val hEq))
  have hEq : ({1, ⟨c.t, c.t_mem_S0⟩} : Finset (↥(c.S0 : Subgroup G))) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp
    · rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
      have htne' : (1 : ↥(c.S0 : Subgroup G)) ∉
          ({⟨c.t, c.t_mem_S0⟩} : Finset (↥(c.S0 : Subgroup G))) := by
        intro h1
        exact htne (Finset.mem_singleton.mp h1).symm
      rw [Finset.card_insert_of_notMem htne', Finset.card_singleton]
  have hr : r ∈ Finset.univ := Finset.mem_univ r
  rw [← hEq] at hr
  simpa using hr

/-- For `ν` with `ν(t) = ν(1)`, `ν(ut) = ν(u)` for `u ∈ U` (`t` acts
trivially). -/
private lemma char_trivial_on_t_mul (_h12 : Hyp12 c) {ν : Irr (↥c.H0)}
    (hνt : ν.1 (tH0 c) = ν.1 1) (u : ↥c.U) :
    ν.1 ⟨(u : G) * c.t, c.H0.mul_mem (U_le_H0 c u.2) (S0_le_H0 c c.t_mem_S0)⟩ =
      ν.1 ⟨(u : G), U_le_H0 c u.2⟩ := by
  classical
  rcases ν.2 with ⟨n, ρ, hρ, hνeq⟩
  have htc : ∀ g : ↥c.H0, (tH0 c) * g = g * (tH0 c) := by
    intro g
    exact t_central_H0' c g
  have ht2 : (tH0 c) ^ 2 = 1 := t_H0_sq c
  rcases rep_apply_central_scalar htc ht2 ρ hρ with ⟨a, hscalar, ha2⟩
  have ha : a = 1 := by
    have hval : ν.1 (tH0 c) = a * ν.1 1 := by
      rw [hνeq]
      change LinearMap.trace ℂ (Fin n → ℂ) (ρ (tH0 c)) =
        a * LinearMap.trace ℂ (Fin n → ℂ) (ρ 1)
      rw [hscalar, LinearMap.map_smul, LinearMap.trace_one]
      simp [smul_eq_mul]
    have hν1 : ν.1 1 ≠ 0 := irreducible_char_one_ne_zero ν.2
    exact mul_right_cancel₀ hν1 (by simpa using hval.symm.trans hνt)
  have hEqEl : ⟨(u : G) * c.t, c.H0.mul_mem (U_le_H0 c u.2) (S0_le_H0 c c.t_mem_S0)⟩ =
      (tH0 c) * ⟨(u : G), U_le_H0 c u.2⟩ := by
    have htu : (u : G) * c.t = c.t * (u : G) := by
      simpa using congrArg Subtype.val
        (t_central_H0' c ⟨(u : G), U_le_H0 c u.2⟩).symm
    apply Subtype.ext
    exact htu
  rw [hEqEl, hνeq]
  change LinearMap.trace ℂ (Fin n → ℂ) (ρ ((tH0 c) * ⟨(u : G), U_le_H0 c u.2⟩)) =
    LinearMap.trace ℂ (Fin n → ℂ) (ρ ⟨(u : G), U_le_H0 c u.2⟩)
  rw [map_mul ρ, hscalar]
  have hsmul : (a • (1 : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))) *
        ρ ⟨(u : G), U_le_H0 c u.2⟩ =
      a • ρ ⟨(u : G), U_le_H0 c u.2⟩ := by
    ext v
    simp
  rw [hsmul, map_smul]
  simp [ha]

/-- Characters trivial on `t` are determined by their restriction to `U`
(`H0 = U·⟨t⟩` in the Section-4 case). -/
private lemma restrictU_injective_on_Delta (h12 : Hyp12 c) (_hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) {ν μ : Irr (↥c.H0)} (hνΔ : ν ∈ DeltaSet c h12)
    (hμΔ : μ ∈ DeltaSet c h12) (hEq : restrictU c h12 ν.1 = restrictU c h12 μ.1) :
    ν = μ := by
  apply Subtype.ext
  funext x
  rcases H0_eq_U_mul_S0 c h12 (x := x) with ⟨u, r, hx⟩
  rcases S0_pair c hS4 r with hr | hr
  · have hx1 : (x : G) = (u : G) := by simpa [hr] using hx
    have hArg : x = ⟨(u : G), U_le_H0 c u.2⟩ := by
      apply Subtype.ext
      exact hx1
    calc
      ν.1 x = ν.1 ⟨(u : G), U_le_H0 c u.2⟩ := by rw [hArg]
      _ = (restrictU c h12 ν.1) u := by simp [restrictU_apply]
      _ = (restrictU c h12 μ.1) u := by rw [hEq]
      _ = μ.1 ⟨(u : G), U_le_H0 c u.2⟩ := by simp [restrictU_apply]
      _ = μ.1 x := by rw [hArg]
  · have hx2 : (x : G) = (u : G) * c.t := by simpa [hr] using hx
    have hArg : x = ⟨(u : G) * c.t, c.H0.mul_mem (U_le_H0 c u.2) (S0_le_H0 c c.t_mem_S0)⟩ := by
      apply Subtype.ext
      exact hx2
    calc
      ν.1 x = ν.1 ⟨(u : G) * c.t, c.H0.mul_mem (U_le_H0 c u.2) (S0_le_H0 c c.t_mem_S0)⟩ := by
        rw [hArg]
      _ = ν.1 ⟨(u : G), U_le_H0 c u.2⟩ :=
        char_trivial_on_t_mul c h12 (DeltaSet_mem_t c h12 hνΔ) u
      _ = (restrictU c h12 ν.1) u := by simp [restrictU_apply]
      _ = (restrictU c h12 μ.1) u := by rw [hEq]
      _ = μ.1 ⟨(u : G), U_le_H0 c u.2⟩ := by simp [restrictU_apply]
      _ = μ.1 ⟨(u : G) * c.t, c.H0.mul_mem (U_le_H0 c u.2) (S0_le_H0 c c.t_mem_S0)⟩ :=
        (char_trivial_on_t_mul c h12 (DeltaSet_mem_t c h12 hμΔ) u).symm
      _ = μ.1 x := by rw [hArg]

/-- The Glauberman correspondence `ν ↦ ν̂` is injective on `B′(χ)`. -/
private lemma nuHat_injective_on_BPrime (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) {χ : ClassFunction G} {ν μ : Irr (↥c.H0)}
    (hνBp : ν ∈ BPrimeOf c h12 χ) (hμBp : μ ∈ BPrimeOf c h12 χ)
    (hEq : nuHat c h12 ν = nuHat c h12 μ) : ν = μ := by
  classical
  have hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 :=
    DeltaSet_mem_fixed c h12 (DeltaSet_of_BPrime c h12 hνBp)
  have hνt : ν.1 (tH0 c) = ν.1 1 :=
    DeltaSet_mem_t c h12 (DeltaSet_of_BPrime c h12 hνBp)
  have hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1 :=
    DeltaSet_mem_fixed c h12 (DeltaSet_of_BPrime c h12 hμBp)
  have hμt : μ.1 (tH0 c) = μ.1 1 :=
    DeltaSet_mem_t c h12 (DeltaSet_of_BPrime c h12 hμBp)
  have hνP : ∃ α : Irr (↥c.U), FixedIrr (c.S : Subgroup G) c.U α ∧
      restrictU c h12 ν.1 = α.1 :=
    exists_fixed_alpha_of_section4 c h12 hSC hS4 hνs hνt
  have hμP : ∃ α : Irr (↥c.U), FixedIrr (c.S : Subgroup G) c.U α ∧
      restrictU c h12 μ.1 = α.1 :=
    exists_fixed_alpha_of_section4 c h12 hSC hS4 hμs hμt
  unfold nuHat at hEq
  rw [dif_pos hνP, dif_pos hμP] at hEq
  have hEq' := (glaubermanEquiv c).injective hEq
  have hEqα : Classical.choose hνP = Classical.choose hμP := congrArg Subtype.val hEq'
  have hresν : restrictU c h12 ν.1 = (Classical.choose hνP).1 :=
    (Classical.choose_spec hνP).2
  have hresμ : restrictU c h12 μ.1 = (Classical.choose hμP).1 :=
    (Classical.choose_spec hμP).2
  have hEqRes : restrictU c h12 ν.1 = restrictU c h12 μ.1 := by
    rw [hresν, hresμ]
    simp [hEqα]
  exact restrictU_injective_on_Delta c h12 hSC hS4 (DeltaSet_of_BPrime c h12 hνBp)
    (DeltaSet_of_BPrime c h12 hμBp) hEqRes

/-- Conjugation by an element of `N_G(B)` is injective on `Irr(B)`. -/
private lemma conjIrrB_apply (c : Hyp11 G) {g : G}
    (hg : ∀ b : ↥c.B, g * (b : G) * g⁻¹ ∈ c.B) (β : Irr (↥c.B))
    (b : ↥c.B) :
    (conjIrrB c hg β).1 b = β.1 ⟨g * (b : G) * g⁻¹, hg b⟩ := by
  rfl

private lemma conjIrrB_injective_of_normalizer (c : Hyp11 G) {g : G}
    (hg : g ∈ normalizerB c) :
    Function.Injective (fun β : Irr (↥c.B) =>
      conjIrrB c (B_conj_mem_of_normalizer c hg) β) := by
  intro β1 β2 hEq'
  apply Subtype.ext
  funext b
  have hginv : g⁻¹ ∈ normalizerB c := (normalizerB c).inv_mem hg
  have hsurj : ∃ b' : ↥c.B, g * (b' : G) * g⁻¹ = (b : G) := by
    have hmem : g⁻¹ * (b : G) * g ∈ c.B := by
      simpa using B_conj_mem_of_normalizer c hginv b
    refine ⟨⟨g⁻¹ * (b : G) * g, hmem⟩, ?_⟩
    group
  rcases hsurj with ⟨b', hb'⟩
  have hc' := congrFun (congrArg Subtype.val hEq') b'
  rw [conjIrrB_apply c (B_conj_mem_of_normalizer c hg) β1 b',
      conjIrrB_apply c (B_conj_mem_of_normalizer c hg) β2 b'] at hc'
  have hb'' : g * (b' : G) * g⁻¹ = (b : G) := hb'
  have hArg : (⟨g * (b' : G) * g⁻¹, B_conj_mem_of_normalizer c hg b'⟩ : ↥c.B) = b := by
    apply Subtype.ext
    exact hb''
  rw [hArg] at hc'
  exact hc'

/-- `β^g ≡ β` on `B` for `g ∈ N_G(B)` (from Lemma 4.1(iii) and class-function
invariance of `χ`). -/
private lemma beta_conj_congruence (h12 : Hyp12 c) (_hSC : Section3Hyp c) (_hS4 : Section4Hyp c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) (_hB' : (BPrimeOf c h12 χ).Nonempty)
    (hiii : ∀ b : ↥c.B, (hb : (b : G) ∈ c.H0) →
      CongruentModTwo (χ (b : G)) (∑ ν ∈ BPrimeOf c h12 χ, (nuHat c h12 ν).1 b))
    {g : G} (hg : g ∈ normalizerB c) :
    ∀ b : ↥c.B,
      CongruentModTwo
        (∑ ν ∈ BPrimeOf c h12 χ, (nuHat c h12 ν).1
          ⟨g * (b : G) * g⁻¹, B_conj_mem_of_normalizer c hg b⟩)
        (∑ ν ∈ BPrimeOf c h12 χ, (nuHat c h12 ν).1 b) := by
  intro b
  have h1 := hiii ⟨g * (b : G) * g⁻¹, B_conj_mem_of_normalizer c hg b⟩
    (mem_H0_of_mem_B_s4 c (b := ⟨g * (b : G) * g⁻¹, B_conj_mem_of_normalizer c hg b⟩))
  have h1' : CongruentModTwo (χ (g * (b : G) * g⁻¹))
      (∑ ν ∈ BPrimeOf c h12 χ, (nuHat c h12 ν).1
        ⟨g * (b : G) * g⁻¹, B_conj_mem_of_normalizer c hg b⟩) := by
    simpa using h1
  have h2 : χ (g * (b : G) * g⁻¹) = χ (b : G) :=
    (isClassFunction_of_isPMIrr hχ) (b : G) g
  have h3 := hiii b (mem_H0_of_mem_B_s4 c (b := b))
  have hstep : CongruentModTwo
      (∑ ν ∈ BPrimeOf c h12 χ, (nuHat c h12 ν).1
        ⟨g * (b : G) * g⁻¹, B_conj_mem_of_normalizer c hg b⟩)
      (χ (b : G)) := by
    exact h1'.symm.trans (CongruentModTwo.of_eq h2)
  exact hstep.trans h3

/-- The difference of the two `ν̂`-sums is a `ℤ`-combination of the distinct
irreducibles in `A ∪ Ag`. -/
private lemma sum_indicator_sub {α : Type u} [DecidableEq α] (A Ag : Finset α) (f : α → ℂ) :
    (∑ γ ∈ A ∪ Ag,
      (((if γ ∈ Ag then 1 else 0 : ℤ) - (if γ ∈ A then 1 else 0 : ℤ) : ℤ) : ℂ) * f γ) =
      (∑ γ ∈ Ag, f γ) - (∑ γ ∈ A, f γ) := by
  classical
  calc
    (∑ γ ∈ A ∪ Ag,
        (((if γ ∈ Ag then 1 else 0 : ℤ) - (if γ ∈ A then 1 else 0 : ℤ) : ℤ) : ℂ) * f γ)
        = ∑ γ ∈ A ∪ Ag, ((if γ ∈ Ag then (1 : ℂ) else 0) * f γ -
            (if γ ∈ A then (1 : ℂ) else 0) * f γ) := by
            refine Finset.sum_congr rfl ?_
            intro γ hγ
            by_cases hAg : γ ∈ Ag <;> by_cases hA : γ ∈ A <;> simp [hAg, hA]
    _ = (∑ γ ∈ A ∪ Ag, (if γ ∈ Ag then (1 : ℂ) else 0) * f γ) -
          (∑ γ ∈ A ∪ Ag, (if γ ∈ A then (1 : ℂ) else 0) * f γ) := by
            rw [Finset.sum_sub_distrib]
    _ = (∑ γ ∈ Ag, f γ) - (∑ γ ∈ A, f γ) := by
            congr 1
            · have hAgsub : Ag ⊆ A ∪ Ag := fun γ hγ => Finset.mem_union.mpr (Or.inr hγ)
              calc
                ∑ γ ∈ A ∪ Ag, (if γ ∈ Ag then (1 : ℂ) else 0) * f γ
                    = ∑ γ ∈ Ag, (if γ ∈ Ag then (1 : ℂ) else 0) * f γ :=
                        (Finset.sum_subset hAgsub (fun γ hγ hnot => by simp [hnot])).symm
                _ = ∑ γ ∈ Ag, f γ := Finset.sum_congr rfl (fun γ hγ => by simp [hγ])
            · have hAsub : A ⊆ A ∪ Ag := fun γ hγ => Finset.mem_union.mpr (Or.inl hγ)
              calc
                ∑ γ ∈ A ∪ Ag, (if γ ∈ A then (1 : ℂ) else 0) * f γ
                    = ∑ γ ∈ A, (if γ ∈ A then (1 : ℂ) else 0) * f γ :=
                        (Finset.sum_subset hAsub (fun γ hγ hnot => by simp [hnot])).symm
                _ = ∑ γ ∈ A, f γ := Finset.sum_congr rfl (fun γ hγ => by simp [hγ])

/-- Lemma 4.1(v) for `N_G(B)`: conjugation permutes the set `{ν̂ | ν ∈ B′(χ)}`. -/
private lemma nuHatImage_invariance_NB (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    (hB' : (BPrimeOf c h12 χ).Nonempty)
    (hiii : ∀ b : ↥c.B, (hb : (b : G) ∈ c.H0) →
      CongruentModTwo (χ (b : G)) (∑ ν ∈ BPrimeOf c h12 χ, (nuHat c h12 ν).1 b))
    {g : G} (hg : g ∈ normalizerB c) :
    ∀ β : Irr (↥c.B), β ∈ nuHatImage c h12 (BPrimeOf c h12 χ) →
      conjIrrB c (B_conj_mem_of_normalizer c hg) β ∈
        nuHatImage c h12 (BPrimeOf c h12 χ) := by
  classical
  intro β hβ
  rcases hβ with ⟨ν, hνBp, rfl⟩
  let A : Finset (Irr (↥c.B)) := (BPrimeOf c h12 χ).image (nuHat c h12)
  let Ag : Finset (Irr (↥c.B)) := A.image (fun β0 =>
    conjIrrB c (B_conj_mem_of_normalizer c hg) β0)
  let cfun : Irr (↥c.B) → ℤ := fun γ =>
    (if γ ∈ Ag then 1 else 0) - (if γ ∈ A then 1 else 0)
  have hcong := beta_conj_congruence c h12 hSC hS4 hχ hB' hiii hg
  have hnuInj : Set.InjOn (nuHat c h12) (↑(BPrimeOf c h12 χ)) := by
    intro ν1 hν1 ν2 hν2 hEq'
    exact nuHat_injective_on_BPrime c h12 hSC hS4 hν1 hν2 hEq'
  have hconjInj : Function.Injective (fun β0 : Irr (↥c.B) =>
      conjIrrB c (B_conj_mem_of_normalizer c hg) β0) :=
    conjIrrB_injective_of_normalizer c hg
  have hconjNuInj : Set.InjOn (fun ν0 : Irr (↥c.H0) =>
      conjIrrB c (B_conj_mem_of_normalizer c hg) (nuHat c h12 ν0))
      (↑(BPrimeOf c h12 χ)) := by
    intro ν1 hν1 ν2 hν2 hEq'
    apply hnuInj hν1 hν2
    exact hconjInj hEq'
  have hL : ∀ b : ↥c.B,
      (∑ ν ∈ BPrimeOf c h12 χ, (nuHat c h12 ν).1
        ⟨g * (b : G) * g⁻¹, B_conj_mem_of_normalizer c hg b⟩) =
        ∑ γ ∈ Ag, γ.1 b := by
    intro b
    calc
      (∑ ν ∈ BPrimeOf c h12 χ, (nuHat c h12 ν).1
          ⟨g * (b : G) * g⁻¹, B_conj_mem_of_normalizer c hg b⟩)
          = ∑ ν ∈ BPrimeOf c h12 χ,
              (conjIrrB c (B_conj_mem_of_normalizer c hg) (nuHat c h12 ν)).1 b := by
              refine Finset.sum_congr rfl ?_
              intro ν hν
              rfl
      _ = ∑ γ ∈ Ag, γ.1 b := by
              rw [show Ag = (BPrimeOf c h12 χ).image (fun ν0 =>
                conjIrrB c (B_conj_mem_of_normalizer c hg) (nuHat c h12 ν0)) by
                  unfold Ag A
                  rw [Finset.image_image]
                  rfl]
              rw [Finset.sum_image hconjNuInj]
  have hR : ∀ b : ↥c.B,
      (∑ ν ∈ BPrimeOf c h12 χ, (nuHat c h12 ν).1 b) = ∑ γ ∈ A, γ.1 b := by
    intro b
    rw [show A = (BPrimeOf c h12 χ).image (nuHat c h12) by rfl]
    rw [Finset.sum_image hnuInj]
  have hsum_id : ∀ b : ↥c.B,
      (∑ γ ∈ A ∪ Ag, ((cfun γ : ℂ) * γ.1 b)) =
        (∑ γ ∈ Ag, γ.1 b) - (∑ γ ∈ A, γ.1 b) := by
    intro b
    simpa [cfun] using
      (sum_indicator_sub (A := A) (Ag := Ag) (fun γ : Irr (↥c.B) => γ.1 b))
  have h0 : ∀ b : ↥c.B, CongruentModTwo (∑ γ ∈ A ∪ Ag, ((cfun γ : ℂ) * γ.1 b)) 0 := by
    intro b
    have hc := hcong b
    have hc' : CongruentModTwo (∑ γ ∈ Ag, γ.1 b) (∑ γ ∈ A, γ.1 b) := by
      simpa [hL b, hR b] using hc
    have hdiff : CongruentModTwo ((∑ γ ∈ Ag, γ.1 b) - (∑ γ ∈ A, γ.1 b)) 0 := by
      have h := hc'.sub (CongruentModTwo.refl (∑ γ ∈ A, γ.1 b))
      simpa using h
    simpa [hsum_id b] using hdiff
  let I : Type u := {γ : Irr (↥c.B) // γ ∈ A ∪ Ag}
  let βf : I → ClassFunction (↥c.B) := fun i => i.1.1
  let cf : I → ℂ := fun i => (cfun i.1 : ℂ)
  have hβ : ∀ i : I, IsIrreducibleCharacter (βf i) := by
    intro i
    exact i.1.2
  have hβdist : Pairwise fun i j : I => βf i ≠ βf j := by
    intro i j hij hEq'
    apply hij
    apply Subtype.ext
    apply Subtype.ext
    exact hEq'
  have hc : ∀ i : I, IsIntegral ℤ (cf i) := by
    intro i
    exact isIntegral_intCast (cfun i.1)
  have h0' : ∀ b : ↥c.B, CongruentModTwo (∑ i : I, cf i * βf i b) 0 := by
    intro b
    have hEqSum : (∑ i : I, cf i * βf i b) =
        ∑ γ ∈ A ∪ Ag, ((cfun γ : ℂ) * γ.1 b) := by
      unfold I cf βf
      exact Finset.sum_coe_sort (A ∪ Ag)
        (fun γ : Irr (↥c.B) => ((cfun γ : ℂ) * γ.1 b))
    rw [hEqSum]
    exact h0 b
  have h18 := lemma_1_8 (B := ↥c.B) (B_coprime_two c) (I := I) (β := βf) (c := cf)
    hβ hβdist hc h0'
  have hsub : A ⊆ Ag := by
    intro γ hγA
    let i : I := ⟨γ, Finset.mem_union.mpr (Or.inl hγA)⟩
    have hcongγ : CongruentModTwo ((cfun γ : ℂ)) 0 := by
      have h := h18 i
      simpa [cf] using h
    by_contra hnotAg
    have hcf : cfun γ = -1 := by
      simp [cfun, hγA, hnotAg]
    have hbad : CongruentModTwo ((-1 : ℤ) : ℂ) 0 := by
      simpa [hcf] using hcongγ
    have hdvd : (2 : ℤ) ∣ (0 - (-1 : ℤ)) := by
      exact CongruentModTwo.eq_of_int (by simpa using hbad.symm)
    norm_num at hdvd
  have hcard : A.card = Ag.card := by
    rw [show Ag = A.image (fun β0 =>
        conjIrrB c (B_conj_mem_of_normalizer c hg) β0) by rfl]
    exact (Finset.card_image_of_injOn (fun β1 hβ1 β2 hβ2 hEq' => hconjInj hEq')).symm
  have hEqSet : Ag = A := (Finset.eq_of_subset_of_card_le hsub (by rw [hcard])).symm
  have hβA : (nuHat c h12 ν) ∈ A := by
    rw [show A = (BPrimeOf c h12 χ).image (nuHat c h12) by rfl]
    exact Finset.mem_image.mpr ⟨ν, hνBp, rfl⟩
  have hβAg : conjIrrB c (B_conj_mem_of_normalizer c hg) (nuHat c h12 ν) ∈ Ag := by
    rw [show Ag = A.image (fun β0 =>
        conjIrrB c (B_conj_mem_of_normalizer c hg) β0) by rfl]
    exact Finset.mem_image.mpr ⟨nuHat c h12 ν, hβA, rfl⟩
  rw [hEqSet] at hβAg
  rw [show A = (BPrimeOf c h12 χ).image (nuHat c h12) by rfl] at hβAg
  rcases Finset.mem_image.mp hβAg with ⟨ν', hν', hEq'⟩
  unfold nuHatImage
  exact ⟨ν', hν', hEq'.symm⟩

/-- `N_G(S) ≤ N_G(B)` through the explicit transport
`B_conj_mem_of_normalizerS`. -/
private lemma normalizerS_le_normalizerB (c : Hyp11 G) : normalizerS c ≤ normalizerB c := by
  intro g hg
  change g ∈ Subgroup.normalizer ((c.B : Subgroup G) : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    exact B_conj_mem_of_normalizerS c hg ⟨b, hb⟩
  · intro hb'
    have hginv : g⁻¹ ∈ normalizerS c := (normalizerS c).inv_mem hg
    have h' := B_conj_mem_of_normalizerS c hginv ⟨g * b * g⁻¹, hb'⟩
    convert h' using 1
    group

/-- Lemma 4.1: for `χ ∈ ±Irr(G)` with `B′(χ)` nonempty:
(i) `|B′(χ)| = 1` or `3`; (ii) `χ(t) = Σ_{ν∈B′(χ)} (χ,δν)_G·ν(1)`;
(iii) `χ ≡ Σ_{ν∈B′(χ)} ν̂` on `B`; (iv) `χ(1)` is odd; (v) the set
`{ν̂ | ν ∈ B′(χ)}` is invariant under `N_G(B)`, hence under `N_G(S)`. -/
public theorem lemma_4_1 (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) [Fintype ↥(LambdaHom c.H0 c.U)]
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) (hB' : (BPrimeOf c h12 χ).Nonempty) :
    ((BPrimeOf c h12 χ).card = 1 ∨ (BPrimeOf c h12 χ).card = 3) ∧
    (χ c.t = ∑ ν ∈ BPrimeOf c h12 χ, scalarProduct G χ (deltaNu c h12 ν) * ν.1 1) ∧
    (∀ b : ↥c.B, (hb : (b : G) ∈ c.H0) →
      CongruentModTwo (χ (b : G)) (∑ ν ∈ BPrimeOf c h12 χ, (nuHat c h12 ν).1 b)) ∧
    (∃ n : ℤ, (n : ℂ) = χ 1 ∧ Odd n) ∧
    (∀ g : G, (hg : g ∈ normalizerB c) →
      ∀ β : Irr (↥c.B), β ∈ nuHatImage c h12 (BPrimeOf c h12 χ) →
        conjIrrB c (B_conj_mem_of_normalizer c hg) β ∈
          nuHatImage c h12 (BPrimeOf c h12 χ)) ∧
    (∀ g : G, (hg : g ∈ normalizerS c) →
      ∀ β : Irr (↥c.B), β ∈ nuHatImage c h12 (BPrimeOf c h12 χ) →
        conjIrrB c (B_conj_mem_of_normalizerS c hg) β ∈
          nuHatImage c h12 (BPrimeOf c h12 χ)) := by
  classical
  let hiii : ∀ b : ↥c.B, (hb : (b : G) ∈ c.H0) →
      CongruentModTwo (χ (b : G)) (∑ ν ∈ BPrimeOf c h12 χ, (nuHat c h12 ν).1 b) :=
    fun b hb => congruent_on_B c h12 hSC hS4 hχ hB' b hb
  constructor
  · exact BPrime_card_eq_one_or_three c h12 hSC hS4 hχ hB'
  constructor
  · have h24 := (lemma_2_4 c h12 hχ).1 c.t ⟨S0_le_H0 c c.t_mem_S0, t_not_mem_U c⟩
    have hEq := sum_BOf_at_t_eq_sum_BPrime c h12 hSC hS4 hχ hB'
    rw [← hEq]
    simpa [tH0] using h24 (S0_le_H0 c c.t_mem_S0)
  constructor
  · exact hiii
  constructor
  · exact chi_one_odd c h12 hSC hS4 hχ hB'
  constructor
  · intro g hg
    exact nuHatImage_invariance_NB c h12 hSC hS4 hχ hB' hiii hg
  · intro g hg
    have hgB : g ∈ normalizerB c := normalizerS_le_normalizerB c hg
    intro β hβ
    have hNB := nuHatImage_invariance_NB c h12 hSC hS4 hχ hB' hiii hgB β hβ
    have hEq : conjIrrB c (B_conj_mem_of_normalizerS c hg) β =
        conjIrrB c (B_conj_mem_of_normalizer c hgB) β := by
      congr 1
    simpa [hEq] using hNB

end Section4

end CFSG.BenderGlauberman
