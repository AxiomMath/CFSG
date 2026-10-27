module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section4.Lemma41
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section4.Lemma42
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section4.NuHatOrbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section4.ClassSumOddParity
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section4.ClassSumEvenParity
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Coherence
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Lemma33
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section4.Basic
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section4.Lemma41
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section4.Lemma42
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Lemma33
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.ClassSumFormula
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.ClassFunction

namespace CFSG
end CFSG
open CFSG

/-!
# Bender--Glauberman: Theorem 4.3

The connected-component structure of the Section-4 graph `Δ`.  This module
builds the proof in three layers:

1.  Section-4 `δν` infrastructure: every `δν ∈ Δ` is a generalized
    character of norm four, pairwise orthogonal for distinct vertices, and
    its constituents are exactly the signed irreducibles `χ` with
    `ν ∈ B′(χ)`.
2.  The non-fixed `ν̂` orbit case: three vertices and the four signed
    irreducibles with the displayed sign patterns.
3.  The fixed `ν̂` case: the finite incidence analysis and the class-sum
    contradiction.
-/

noncomputable section

open scoped BigOperators
open scoped commutatorElement
open scoped Pointwise

namespace CFSG.BenderGlauberman

open GorensteinWalter
open Theory.Character

-- Local instances matching `Theory.Character`'s subgroup-sum convention.
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

universe u

section Section4

variable {G : Type u} [Group G] [Fintype G]
variable (c : Hyp11 G)

/-- Conjugation by a normalizing element distributes over products. -/
private lemma conjChar_mul {H0 : Subgroup G} {s : G}
    (hsH0 : ∀ x : ↥H0, s * (x : G) * s⁻¹ ∈ H0)
    (φ ψ : ClassFunction (↥H0)) :
    conjChar H0 hsH0 (φ * ψ) = conjChar H0 hsH0 φ * conjChar H0 hsH0 ψ := by
  ext x
  rfl

/-- `|S0| = 2` in the Section-4 case `|S| = 4`. -/
private lemma S0_card_eq_two (hS4 : Section4Hyp c) :
    Nat.card (↥(c.S0 : Subgroup G)) = 2 := by
  unfold Section4Hyp at hS4
  have h4 : 2 * Nat.card (↥(c.S0 : Subgroup G)) = 4 := by
    rw [← c.S_index_two, hS4]
  omega

/-- `S′ = 1` in the Section-4 case. -/
private lemma SPrime_eq_bot_s4 (hS4 : Section4Hyp c) : SPrime c = ⊥ := by
  classical
  have hS0card : Nat.card (↥(c.S0 : Subgroup G)) = 2 := S0_card_eq_two c hS4
  have hsq : (c.t1 * c.t2) ^ 2 = 1 := by
    have h2 : (⟨c.t1 * c.t2, S0_generator_mem_S0 c⟩ : ↥(c.S0 : Subgroup G)) ^ 2 = 1 :=
      sq_eq_one_of_card_two hS0card _
    simpa [Subgroup.coe_pow] using congrArg Subtype.val h2
  unfold SPrime
  rw [hsq, Subgroup.zpowers_one_eq_bot]

/-- `X = S′·U` equals `U` in the Section-4 case. -/
private lemma extensionSubgroup_eq_U_s4 (hS4 : Section4Hyp c) :
    extensionSubgroup c = c.U := by
  unfold extensionSubgroup
  rw [SPrime_eq_bot_s4 c hS4, bot_sup_eq]

/-- `t ∉ X = S′·U` in the Section-4 case. -/
private lemma tH0_not_mem_extensionSubgroup_s4 (hS4 : Section4Hyp c) :
    (tH0 c : G) ∉ extensionSubgroup c := by
  rw [extensionSubgroup_eq_U_s4 c hS4]
  exact t_not_mem_U c

/-- `λ₂(t) = -1` as a unit. -/
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

/-- `λ₂` is fixed by `s`. -/
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
  rw [conjChar_mul (s_normalizes_H0 c h12)]
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

/-- `|H0 : U| = |S0|` (the `H0 = U·S0` product decomposition). -/
private lemma U_index_eq_S0_card_s4 (h12 : Hyp12 c) :
    (c.U.subgroupOf c.H0).index = Nat.card (c.S0 : Subgroup G) := by
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
      invFun := fun y : ↥c.U => ⟨⟨(y : G), (h12.U_normal_in_H0).1 y.2⟩,
        Subgroup.mem_subgroupOf.mpr y.2⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro y; apply Subtype.ext; rfl }
  have hcm := Subgroup.card_mul_index (c.U.subgroupOf c.H0)
  have h1 : (c.U.subgroupOf c.H0).index * Nat.card (↥c.U) = Nat.card (↥c.H0) := by
    rw [← hUcard]
    rw [mul_comm]
    exact hcm
  have h2 : Nat.card (↥c.S0) * Nat.card (↥c.U) = Nat.card (↥c.H0) := by
    calc
      Nat.card (↥c.S0) * Nat.card (↥c.U) = Nat.card (↥c.U) * Nat.card (↥c.S0) := by rw [mul_comm]
      _ = Nat.card (↥c.H0) := hcardcong.symm
  exact mul_right_cancel₀ (b := Nat.card (↥c.U)) (Nat.card_pos (α := ↥c.U)).ne' (by
    calc
      (c.U.subgroupOf c.H0).index * Nat.card (↥c.U) = Nat.card (↥c.H0) := h1
      _ = Nat.card (↥c.S0) * Nat.card (↥c.U) := h2.symm)

/-- The Section-4 `Λ`-group has order two. -/
private lemma Lambda_card_eq_two (h12 : Hyp12 c) (hS4 : Section4Hyp c) :
    Fintype.card (LambdaHom c.H0 c.U) = 2 := by
  rw [← Nat.card_eq_fintype_card, lambda_card_eq_index c h12]
  rw [U_index_eq_S0_card_s4 c h12]
  exact S0_card_eq_two c hS4

/-- The only elements of `Λ` are `1` and `λ₂`. -/
private lemma lambda_eq_one_or_two (h12 : Hyp12 c) (hS4 : Section4Hyp c)
    (l : LambdaHom c.H0 c.U) : l = 1 ∨ l = lambdaTwo c h12 := by
  classical
  have hcard : Fintype.card (LambdaHom c.H0 c.U) = 2 := Lambda_card_eq_two c h12 hS4
  have hsq : l ^ 2 = (1 : LambdaHom c.H0 c.U) := by
    have hpow : l ^ Fintype.card (LambdaHom c.H0 c.U) = 1 := pow_card_eq_one (x := l)
    simpa [hcard] using hpow
  exact lambda_eq_one_or_two_of_sq_one c h12 l hsq

/-- A class function lies in its own `Λ`-orbit. -/
private lemma orbit_self_mem_s4 (c : Hyp11 G)
    (ν : ClassFunction (↥c.H0)) :
    ν ∈ orbit c.H0 c.U ν := by
  classical
  refine Finset.mem_image.mpr ⟨(1 : LambdaHom c.H0 c.U), Finset.mem_univ _, ?_⟩
  have h1 : LambdaChar (1 : LambdaHom c.H0 c.U).1 = (1 : ClassFunction (↥c.H0)) := by
    ext x
    simp [LambdaChar]
  rw [h1, one_mul]

/-- In Section 4 the `Λ`-orbit of a character is the pair `{ν, λ₂ν}`. -/
private lemma orbit_eq_pair (h12 : Hyp12 c) (hS4 : Section4Hyp c)
    (ν : Irr (↥c.H0)) :
    orbit c.H0 c.U ν.1 = {ν.1, (lambdaTwoMul c h12 ν).1} := by
  classical
  ext φ
  constructor
  · intro hφ
    rcases Finset.mem_image.mp hφ with ⟨l, hl, hEq⟩
    rcases lambda_eq_one_or_two c h12 hS4 l with hl1 | hl2
    · rw [hl1] at hEq
      rw [Finset.mem_insert, Finset.mem_singleton]
      left
      rw [← hEq]
      have h1 : LambdaChar (1 : LambdaHom c.H0 c.U).1 =
          (1 : ClassFunction (↥c.H0)) := by
        ext x
        simp [LambdaChar]
      rw [h1, one_mul]
    · rw [hl2] at hEq
      rw [Finset.mem_insert, Finset.mem_singleton]
      right
      rw [← hEq]
      rfl
  · intro hφ
    rw [Finset.mem_insert, Finset.mem_singleton] at hφ
    rcases hφ with hφ | hφ
    · rw [hφ]
      exact orbit_self_mem_s4 c ν.1
    · rw [hφ]
      exact lambdaTwoMul_equiv c h12 ν

/-- `ν̃` and `λ̃₂ν` are disjoint for `ν` fixed by `s`. -/
private lemma tildeNu_disjoint_lambdaTwo (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) {ν : Irr (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1) :
    Disjoint (tildeNu c h12 (lambdaTwoMul c h12 ν)) (tildeNu c h12 ν) := by
  have hμν : (lambdaTwoMul c h12 ν).1 ∈ orbit c.H0 c.U ν.1 := by
    refine Finset.mem_image.mpr ⟨lambdaTwo c h12, Finset.mem_univ _, ?_⟩
    ext x
    rfl
  have hνμ : ν.1 ≠ (lambdaTwoMul c h12 ν).1 := by
    intro hEq
    exact lambdaTwoMul_ne_self c h12 hSC hS4 ν (Subtype.ext hEq.symm)
  have hνs' : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ (lambdaTwoMul c h12 ν).1 := by
    intro hEq
    exact lambdaTwoMul_ne_self c h12 hSC hS4 ν (Subtype.ext (by simpa [hνs] using hEq.symm))
  exact tildeNu_disjoint c h12 hμν hνμ hνs'

/-- The difference of two generalized characters is a generalized character. -/
private lemma isGeneralizedCharacter_sub {φ ψ : ClassFunction G}
    (hφ : IsGeneralizedCharacter φ) (hψ : IsGeneralizedCharacter ψ) :
    IsGeneralizedCharacter (φ - ψ) := by
  rcases hφ with ⟨δ₁, δ₂, hδ₁, hδ₂, hφeq⟩
  rcases hψ with ⟨ε₁, ε₂, hε₁, hε₂, hψeq⟩
  refine ⟨δ₁ + ε₂, δ₂ + ε₁, isCharacter_add hδ₁ hε₂, isCharacter_add hδ₂ hε₁, ?_⟩
  rw [hφeq, hψeq]
  funext x
  simp [Pi.add_apply, Pi.sub_apply]
  ring

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

/-- `Disjoint` is symmetric. -/
private lemma disjoint_symm {φ ψ : ClassFunction G}
    (h : Theory.Character.Disjoint φ ψ) : Theory.Character.Disjoint ψ φ := by
  unfold Theory.Character.Disjoint at h ⊢
  intro χ hχ hχψ
  by_contra hχφ
  exact hχψ (h χ hχ hχφ)

/-- `δν` is a generalized character. -/
private lemma deltaNu_isGeneralized (h12 : Hyp12 c) (ν : Irr (↥c.H0)) :
    IsGeneralizedCharacter (deltaNu c h12 ν) := by
  exact isGeneralizedCharacter_sub (tildeNu_isGeneralized c h12 ν)
    (tildeNu_isGeneralized c h12 (lambdaTwoMul c h12 ν))

/-- The signed-pair cases produce signed integer coefficients. -/
private lemma signed_pair_coeff {δ χ ψ : ClassFunction G}
    (h : δ = χ - ψ ∨ δ = χ + ψ ∨ δ = -χ - ψ ∨ δ = -χ + ψ) :
    ∃ s t : ℤ, (s = 1 ∨ s = -1) ∧ (t = 1 ∨ t = -1) ∧
      δ = (s : ℂ) • χ + (t : ℂ) • ψ := by
  rcases h with h | h | h | h
  · refine ⟨1, -1, Or.inl rfl, Or.inr rfl, ?_⟩
    rw [h, sub_eq_add_neg]
    simp
  · refine ⟨1, 1, Or.inl rfl, Or.inl rfl, ?_⟩
    rw [h]
    norm_num
  · refine ⟨-1, -1, Or.inr rfl, Or.inr rfl, ?_⟩
    rw [h, sub_eq_add_neg]
    simp
  · refine ⟨-1, 1, Or.inr rfl, Or.inl rfl, ?_⟩
    rw [h]
    norm_num

/-- The first irreducible of a signed pair occurs with nonzero coefficient. -/
private lemma signed_pair_scalar_ne {δ χ ψ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hψ : IsIrreducibleCharacter ψ)
    (hne : χ ≠ ψ)
    (h : δ = χ - ψ ∨ δ = χ + ψ ∨ δ = -χ - ψ ∨ δ = -χ + ψ) :
    scalarProduct G χ δ ≠ 0 := by
  rcases h with h | h | h | h
  · rw [h]
    rw [scalarProduct_sub_right, scalarProduct_irreducible_self hχ,
      scalarProduct_irreducible_orthogonal hχ hψ hne]
    norm_num
  · rw [h]
    rw [scalarProduct_add_right, scalarProduct_irreducible_self hχ,
      scalarProduct_irreducible_orthogonal hχ hψ hne]
    norm_num
  · rw [h]
    rw [scalarProduct_sub_right, scalarProduct_neg_right,
      scalarProduct_irreducible_self hχ, scalarProduct_irreducible_orthogonal hχ hψ hne]
    norm_num
  · rw [h]
    rw [scalarProduct_add_right, scalarProduct_neg_right,
      scalarProduct_irreducible_self hχ, scalarProduct_irreducible_orthogonal hχ hψ hne]
    norm_num

/-- The second irreducible of a signed pair occurs with nonzero coefficient. -/
private lemma signed_pair_scalar_ne_symm {δ χ ψ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hψ : IsIrreducibleCharacter ψ)
    (hne : χ ≠ ψ)
    (h : δ = χ - ψ ∨ δ = χ + ψ ∨ δ = -χ - ψ ∨ δ = -χ + ψ) :
    scalarProduct G ψ δ ≠ 0 := by
  rcases h with h | h | h | h
  · rw [h]
    rw [scalarProduct_sub_right, scalarProduct_irreducible_self hψ,
      scalarProduct_irreducible_orthogonal hψ hχ hne.symm]
    norm_num
  · rw [h]
    rw [scalarProduct_add_right, scalarProduct_irreducible_self hψ,
      scalarProduct_irreducible_orthogonal hψ hχ hne.symm]
    norm_num
  · rw [h]
    rw [scalarProduct_sub_right, scalarProduct_neg_right,
      scalarProduct_irreducible_self hψ, scalarProduct_irreducible_orthogonal hψ hχ hne.symm]
    norm_num
  · rw [h]
    rw [scalarProduct_add_right, scalarProduct_neg_right,
      scalarProduct_irreducible_self hψ, scalarProduct_irreducible_orthogonal hψ hχ hne.symm]
    norm_num

/-- Every Section-4 `δν` is a signed sum of four distinct irreducible
characters. -/
private lemma deltaNu_signed_four_decomp (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) {ν : Irr (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1) :
    ∃ χ₁ χ₂ χ₃ χ₄ : ClassFunction G,
      IsIrreducibleCharacter χ₁ ∧ IsIrreducibleCharacter χ₂ ∧
      IsIrreducibleCharacter χ₃ ∧ IsIrreducibleCharacter χ₄ ∧
      χ₁ ≠ χ₂ ∧ χ₁ ≠ χ₃ ∧ χ₁ ≠ χ₄ ∧ χ₂ ≠ χ₃ ∧ χ₂ ≠ χ₄ ∧ χ₃ ≠ χ₄ ∧
      ∃ s₁ s₂ s₃ s₄ : ℤ,
        (s₁ = 1 ∨ s₁ = -1) ∧ (s₂ = 1 ∨ s₂ = -1) ∧
        (s₃ = 1 ∨ s₃ = -1) ∧ (s₄ = 1 ∨ s₄ = -1) ∧
        deltaNu c h12 ν = (s₁ : ℂ) • χ₁ + (s₂ : ℂ) • χ₂ +
          (s₃ : ℂ) • χ₃ + (s₄ : ℂ) • χ₄ := by
  classical
  have hnormν : normSq G (tildeNu c h12 ν) = 2 := by
    have h := tildeNu_norm c h12 ν
    simpa [hνs] using h
  have hnorm_lam : normSq G (tildeNu c h12 (lambdaTwoMul c h12 ν)) = 2 := by
    have h := tildeNu_norm c h12 (lambdaTwoMul c h12 ν)
    have hfix : conjChar c.H0 (s_normalizes_H0 c h12) (lambdaTwoMul c h12 ν).1 =
        (lambdaTwoMul c h12 ν).1 := lambdaTwoMul_fixed_by_s c h12 hνs
    simpa [hfix] using h
  rcases signed_pair_decomp (tildeNu_isGeneralized c h12 ν) (by simpa [normSq] using hnormν) with
    ⟨a, b, ha, hb, hab, hA⟩
  rcases signed_pair_decomp (tildeNu_isGeneralized c h12 (lambdaTwoMul c h12 ν))
    (by simpa [normSq] using hnorm_lam) with ⟨g₃, g₄, hg₃, hg₄, hg₃g₄, hB⟩
  rcases signed_pair_coeff hA with ⟨s, t, hs, ht, hA'⟩
  rcases signed_pair_coeff hB with ⟨u, v, hu, hv, hB'⟩
  have hdis := tildeNu_disjoint_lambdaTwo c h12 hSC hS4 hνs
  have hcross_13 : a ≠ g₃ := by
    intro hEq
    have h1 : scalarProduct G a (tildeNu c h12 ν) ≠ 0 :=
      signed_pair_scalar_ne ha hb hab hA
    have h2 : scalarProduct G a (tildeNu c h12 (lambdaTwoMul c h12 ν)) ≠ 0 := by
      rw [hEq]
      exact signed_pair_scalar_ne hg₃ hg₄ hg₃g₄ hB
    have hz : scalarProduct G a (tildeNu c h12 ν) = 0 := hdis a ha h2
    exact h1 hz
  have hcross_14 : a ≠ g₄ := by
    intro hEq
    have h1 : scalarProduct G a (tildeNu c h12 ν) ≠ 0 :=
      signed_pair_scalar_ne ha hb hab hA
    have h2 : scalarProduct G a (tildeNu c h12 (lambdaTwoMul c h12 ν)) ≠ 0 := by
      rw [hEq]
      exact signed_pair_scalar_ne_symm hg₃ hg₄ hg₃g₄ hB
    have hz : scalarProduct G a (tildeNu c h12 ν) = 0 := hdis a ha h2
    exact h1 hz
  have hcross_23 : b ≠ g₃ := by
    intro hEq
    have h1 : scalarProduct G b (tildeNu c h12 ν) ≠ 0 :=
      signed_pair_scalar_ne_symm ha hb hab hA
    have h2 : scalarProduct G b (tildeNu c h12 (lambdaTwoMul c h12 ν)) ≠ 0 := by
      rw [hEq]
      exact signed_pair_scalar_ne hg₃ hg₄ hg₃g₄ hB
    have hz : scalarProduct G b (tildeNu c h12 ν) = 0 := hdis b hb h2
    exact h1 hz
  have hcross_24 : b ≠ g₄ := by
    intro hEq
    have h1 : scalarProduct G b (tildeNu c h12 ν) ≠ 0 :=
      signed_pair_scalar_ne_symm ha hb hab hA
    have h2 : scalarProduct G b (tildeNu c h12 (lambdaTwoMul c h12 ν)) ≠ 0 := by
      rw [hEq]
      exact signed_pair_scalar_ne_symm hg₃ hg₄ hg₃g₄ hB
    have hz : scalarProduct G b (tildeNu c h12 ν) = 0 := hdis b hb h2
    exact h1 hz
  refine ⟨a, b, g₃, g₄, ha, hb, hg₃, hg₄, hab, hcross_13, hcross_14,
    hcross_23, hcross_24, hg₃g₄, s, t, -u, -v, hs, ht, ?_, ?_, ?_⟩
  · rcases hu with hu | hu <;> simp [hu]
  · rcases hv with hv | hv <;> simp [hv]
  · rw [deltaNu]
    rw [hA', hB']
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_neg]

/-- The irreducible constituents of a class function. -/
private def involved (δ : ClassFunction G) : Finset (Irr G) :=
  Finset.univ.filter (fun χ : Irr G => scalarProduct G χ.1 δ ≠ 0)

/-- Membership in the constituent set is the non-zero scalar product. -/
private lemma mem_involved_iff (δ : ClassFunction G) (χ : Irr G) :
    χ ∈ involved δ ↔ scalarProduct G χ.1 δ ≠ 0 := by
  classical
  simp [involved]

/-- The `ν̂`-image of a finset of Section-4 characters. -/
private def nuHatFinset (h12 : Hyp12 c) (A : Finset (Irr (↥c.H0))) :
    Finset (Irr (↥c.B)) :=
  A.image (nuHat c h12)

/-- Membership in the `ν̂`-image is the finset image membership. -/
private lemma mem_nuHatImage_iff (h12 : Hyp12 c)
    (A : Finset (Irr (↥c.H0))) (β : Irr (↥c.B)) :
    β ∈ nuHatImage c h12 A ↔ β ∈ nuHatFinset c h12 A := by
  classical
  constructor
  · rintro ⟨ν, hν, hEq⟩
    exact Finset.mem_image.mpr ⟨ν, hν, hEq.symm⟩
  · intro hβ
    rw [nuHatFinset] at hβ
    rcases Finset.mem_image.mp hβ with ⟨ν, hν, hEq⟩
    exact ⟨ν, hν, hEq.symm⟩

/-- Irreducible characters are invariant under group isomorphism. -/
private noncomputable def irrCongr_s4 {G H : Type u} [Group G] [Group H]
    [Fintype G] [Fintype H] (e : H ≃* G) : IrrBG19 G ≃ IrrBG19 H where
  toFun α := ⟨fun h : H => α.1 (e h), isIrreducibleCharacter_congr e α.2⟩
  invFun β := ⟨fun g : G => β.1 (e.symm g), isIrreducibleCharacter_congr e.symm β.2⟩
  left_inv α := by
    apply Subtype.ext
    funext g
    change α.1 (e (e.symm g)) = α.1 g
    rw [e.apply_symm_apply]
  right_inv β := by
    apply Subtype.ext
    funext h
    change β.1 (e.symm (e h)) = β.1 h
    rw [e.symm_apply_apply]

/-- The Glauberman correspondence for Section 4, transported to `B`. -/
private noncomputable def glaubermanEquiv43 (c : Hyp11 G) :
    {α : IrrBG19 (↥c.U) // FixedIrr (c.S : Subgroup G) c.U α} ≃
      IrrBG19 (↥c.B) := by
  classical
  let e0 := Classical.choose (glauberman_correspondence
    (S := ↥(c.S : Subgroup G)) (U := ↥c.U)
    c.S.isPGroup' (U_coprime_two c))
  exact e0.trans (irrCongr_s4 (B_fixedSubgroup_equiv c))

/-- `S0 = {1, t}` in the Section-4 case. -/
private lemma S0_pair43 (hS4 : Section4Hyp c) (r : ↥(c.S0 : Subgroup G)) :
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

/-- For `ν` with `ν(t) = ν(1)`, `ν(ut) = ν(u)` for `u ∈ U`. -/
private lemma char_trivial_on_t_mul43 (h12 : Hyp12 c) {ν : Irr (↥c.H0)}
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

/-- Characters trivial on `t` are determined by their restriction to `U`. -/
private lemma restrictU_injective_on_Delta43 (h12 : Hyp12 c)
    (hS4 : Section4Hyp c) {ν μ : Irr (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (hνt : ν.1 (tH0 c) = ν.1 1)
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1)
    (hμt : μ.1 (tH0 c) = μ.1 1)
    (hEq : restrictU c h12 ν.1 = restrictU c h12 μ.1) :
    ν = μ := by
  apply Subtype.ext
  funext x
  rcases H0_eq_U_mul_S0 c h12 (x := x) with ⟨u, r, hx⟩
  rcases S0_pair43 c hS4 r with hr | hr
  · have hx1 : (x : G) = (u : G) := by simpa [hr] using hx
    have hArg : x = ⟨(u : G), U_le_H0 c u.2⟩ := by
      apply Subtype.ext
      exact hx1
    calc
      ν.1 x = ν.1 ⟨(u : G), U_le_H0 c u.2⟩ := by rw [hArg]
      _ = (restrictU c h12 ν.1) u := rfl
      _ = (restrictU c h12 μ.1) u := by rw [hEq]
      _ = μ.1 ⟨(u : G), U_le_H0 c u.2⟩ := rfl
      _ = μ.1 x := by rw [hArg]
  · have hx2 : (x : G) = (u : G) * c.t := by simpa [hr] using hx
    have hArg : x = ⟨(u : G) * c.t, c.H0.mul_mem (U_le_H0 c u.2) (S0_le_H0 c c.t_mem_S0)⟩ := by
      apply Subtype.ext
      exact hx2
    calc
      ν.1 x = ν.1 ⟨(u : G) * c.t, c.H0.mul_mem (U_le_H0 c u.2) (S0_le_H0 c c.t_mem_S0)⟩ := by
        rw [hArg]
      _ = ν.1 ⟨(u : G), U_le_H0 c u.2⟩ :=
        char_trivial_on_t_mul43 c h12 hνt u
      _ = (restrictU c h12 ν.1) u := rfl
      _ = (restrictU c h12 μ.1) u := by rw [hEq]
      _ = μ.1 ⟨(u : G), U_le_H0 c u.2⟩ := rfl
      _ = μ.1 ⟨(u : G) * c.t, c.H0.mul_mem (U_le_H0 c u.2) (S0_le_H0 c c.t_mem_S0)⟩ :=
        (char_trivial_on_t_mul43 c h12 hμt u).symm
      _ = μ.1 x := by rw [hArg]

/-- `ν ↦ ν̂` is injective on Section-4 `Δ`. -/
public lemma nuHat_injective_on_Delta (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) {ν μ : Irr (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (hνt : ν.1 (tH0 c) = ν.1 1)
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1)
    (hμt : μ.1 (tH0 c) = μ.1 1)
    (hEq : nuHat c h12 ν = nuHat c h12 μ) : ν = μ := by
  classical
  have hνP : ∃ α : Irr (↥c.U), FixedIrr (c.S : Subgroup G) c.U α ∧
      restrictU c h12 ν.1 = α.1 :=
    exists_fixed_alpha_of_section4 c h12 hSC hS4 hνs hνt
  have hμP : ∃ α : Irr (↥c.U), FixedIrr (c.S : Subgroup G) c.U α ∧
      restrictU c h12 μ.1 = α.1 :=
    exists_fixed_alpha_of_section4 c h12 hSC hS4 hμs hμt
  unfold nuHat at hEq
  rw [dif_pos hνP, dif_pos hμP] at hEq
  have hEq' := (glaubermanEquiv43 c).injective hEq
  have hEqα : Classical.choose hνP = Classical.choose hμP := congrArg Subtype.val hEq'
  have hresν : restrictU c h12 ν.1 = (Classical.choose hνP).1 :=
    (Classical.choose_spec hνP).2
  have hresμ : restrictU c h12 μ.1 = (Classical.choose hμP).1 :=
    (Classical.choose_spec hμP).2
  have hEqRes : restrictU c h12 ν.1 = restrictU c h12 μ.1 := by
    rw [hresν, hresμ]
    simp [hEqα]
  exact restrictU_injective_on_Delta43 c h12 hS4 hνs hνt hμs hμt hEqRes

/-- The scalar product of an irreducible against a signed four-sum. -/
private lemma scalarProduct_signed_four {δ χ₁ χ₂ χ₃ χ₄ : ClassFunction G}
    (hχ₁ : IsIrreducibleCharacter χ₁) (hχ₂ : IsIrreducibleCharacter χ₂)
    (hχ₃ : IsIrreducibleCharacter χ₃) (hχ₄ : IsIrreducibleCharacter χ₄)
    (s₁ s₂ s₃ s₄ : ℤ) (hδ : δ = (s₁ : ℂ) • χ₁ + (s₂ : ℂ) • χ₂ +
      (s₃ : ℂ) • χ₃ + (s₄ : ℂ) • χ₄) (φ : Irr G) :
    scalarProduct G φ.1 δ =
      (if φ.1 = χ₁ then (s₁ : ℂ) else 0) +
      (if φ.1 = χ₂ then (s₂ : ℂ) else 0) +
      (if φ.1 = χ₃ then (s₃ : ℂ) else 0) +
      (if φ.1 = χ₄ then (s₄ : ℂ) else 0) := by
  rw [hδ]
  rw [scalarProduct_add_right, scalarProduct_add_right, scalarProduct_add_right]
  rw [scalarProduct_smul_right, scalarProduct_smul_right,
    scalarProduct_smul_right, scalarProduct_smul_right]
  rw [scalarProduct_irr_ite φ.2 hχ₁, scalarProduct_irr_ite φ.2 hχ₂,
    scalarProduct_irr_ite φ.2 hχ₃, scalarProduct_irr_ite φ.2 hχ₄]
  by_cases hφ₁ : φ.1 = χ₁ <;> by_cases hφ₂ : φ.1 = χ₂ <;>
    by_cases hφ₃ : φ.1 = χ₃ <;> by_cases hφ₄ : φ.1 = χ₄ <;>
      simp [hφ₁, hφ₂, hφ₃, hφ₄, star_intCast]

/-- The constituent set of a signed four-sum is exactly the four signed
irreducibles. -/
private lemma involved_eq_of_signed_four {δ χ₁ χ₂ χ₃ χ₄ : ClassFunction G}
    (hχ₁ : IsIrreducibleCharacter χ₁) (hχ₂ : IsIrreducibleCharacter χ₂)
    (hχ₃ : IsIrreducibleCharacter χ₃) (hχ₄ : IsIrreducibleCharacter χ₄)
    (h₁₂ : χ₁ ≠ χ₂) (h₁₃ : χ₁ ≠ χ₃) (h₁₄ : χ₁ ≠ χ₄)
    (h₂₃ : χ₂ ≠ χ₃) (h₂₄ : χ₂ ≠ χ₄) (h₃₄ : χ₃ ≠ χ₄)
    (s₁ s₂ s₃ s₄ : ℤ)
    (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1)
    (hs₃ : s₃ = 1 ∨ s₃ = -1) (hs₄ : s₄ = 1 ∨ s₄ = -1)
    (hδ : δ = (s₁ : ℂ) • χ₁ + (s₂ : ℂ) • χ₂ +
      (s₃ : ℂ) • χ₃ + (s₄ : ℂ) • χ₄) :
    involved δ = {⟨χ₁, hχ₁⟩, ⟨χ₂, hχ₂⟩, ⟨χ₃, hχ₃⟩, ⟨χ₄, hχ₄⟩} := by
  classical
  ext φ
  rw [mem_involved_iff]
  rw [scalarProduct_signed_four hχ₁ hχ₂ hχ₃ hχ₄ s₁ s₂ s₃ s₄ hδ φ]
  constructor
  · intro hne
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    by_contra hnot
    have hφ₁ : φ.1 ≠ χ₁ := by
      intro hEq
      exact hnot (Or.inl (Subtype.ext hEq))
    have hφ₂ : φ.1 ≠ χ₂ := by
      intro hEq
      exact hnot (Or.inr (Or.inl (Subtype.ext hEq)))
    have hφ₃ : φ.1 ≠ χ₃ := by
      intro hEq
      exact hnot (Or.inr (Or.inr (Or.inl (Subtype.ext hEq))))
    have hφ₄ : φ.1 ≠ χ₄ := by
      intro hEq
      exact hnot (Or.inr (Or.inr (Or.inr (Subtype.ext hEq))))
    simp [hφ₁, hφ₂, hφ₃, hφ₄] at hne
  · intro hφ
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hφ
    rcases hφ with rfl | rfl | rfl | rfl
    · rcases hs₁ with h | h <;> simp [h, h₁₂, h₁₃, h₁₄]
    · simp [h₁₂.symm]
      rcases hs₂ with h | h <;> simp [h, h₂₃, h₂₄]
    · simp [h₁₃.symm, h₂₃.symm]
      rcases hs₃ with h | h <;> simp [h, h₃₄]
    · simp [h₁₄.symm, h₂₄.symm, h₃₄.symm]
      rcases hs₄ with h | h <;> simp [h]

/-- Every Section-4 `δν` has exactly four irreducible constituents. -/
private lemma involved_deltaNu_card_eq_four (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) {ν : Irr (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1) :
    (involved (deltaNu c h12 ν)).card = 4 := by
  classical
  rcases deltaNu_signed_four_decomp c h12 hSC hS4 hνs with
    ⟨χ₁, χ₂, χ₃, χ₄, hχ₁, hχ₂, hχ₃, hχ₄,
      h₁₂, h₁₃, h₁₄, h₂₃, h₂₄, h₃₄, s₁, s₂, s₃, s₄,
      hs₁, hs₂, hs₃, hs₄, hδ⟩
  have hEq := involved_eq_of_signed_four hχ₁ hχ₂ hχ₃ hχ₄
    h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ h₃₄ s₁ s₂ s₃ s₄ hs₁ hs₂ hs₃ hs₄ hδ
  rw [hEq]
  have hsub_ne {χ ψ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
      (hψ : IsIrreducibleCharacter ψ) (hne : χ ≠ ψ) :
      (⟨χ, hχ⟩ : Irr G) ≠ ⟨ψ, hψ⟩ := by
    intro hEq
    exact hne (congrArg Subtype.val hEq)
  have h₁not : (⟨χ₁, hχ₁⟩ : Irr G) ∉
      ({⟨χ₂, hχ₂⟩, ⟨χ₃, hχ₃⟩, ⟨χ₄, hχ₄⟩} : Finset (Irr G)) := by
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    intro hEq
    rcases hEq with hEq | hEq | hEq
    · exact h₁₂ (congrArg Subtype.val hEq)
    · exact h₁₃ (congrArg Subtype.val hEq)
    · exact h₁₄ (congrArg Subtype.val hEq)
  have h₂not : (⟨χ₂, hχ₂⟩ : Irr G) ∉
      ({⟨χ₃, hχ₃⟩, ⟨χ₄, hχ₄⟩} : Finset (Irr G)) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    intro hEq
    rcases hEq with hEq | hEq
    · exact h₂₃ (congrArg Subtype.val hEq)
    · exact h₂₄ (congrArg Subtype.val hEq)
  have h₃not : (⟨χ₃, hχ₃⟩ : Irr G) ∉ ({⟨χ₄, hχ₄⟩} : Finset (Irr G)) := by
    rw [Finset.mem_singleton]
    exact hsub_ne hχ₃ hχ₄ h₃₄
  rw [Finset.card_insert_of_notMem h₁not,
    Finset.card_insert_of_notMem h₂not,
    Finset.card_insert_of_notMem h₃not,
    Finset.card_singleton]

/-- `δν` is a vertex of the graph `Δ` whenever `ν ∈ B′(χ)`. -/
private lemma deltaNu_mem_Delta_of_BPrime (h12 : Hyp12 c) {χ : ClassFunction G}
    {ν : Irr (↥c.H0)} (hνB : ν ∈ BPrimeOf c h12 χ) :
    deltaNu c h12 ν ∈ Delta c h12 := by
  classical
  rw [BPrimeOf] at hνB
  rw [Delta]
  exact ⟨ν, (Finset.mem_filter.mp hνB).2.1, (Finset.mem_filter.mp hνB).2.2.1, rfl⟩

/-- In the non-fixed orbit case the `ν̂`-image of `B′(χ)` is exactly the
orbit of `μ̂` (Lemma 4.1(v) + orbit size three). -/
private lemma nuHatFinset_eq_orbit_of_nonfixed (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {μ : Irr (↥c.H0)} {χ : Irr G}
    (hχδ : scalarProduct G χ.1 (deltaNu c h12 μ) ≠ 0)
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1)
    (hμt : μ.1 (tH0 c) = μ.1 1)
    (horb : (nuHatOrbit c h12 (nuHat c h12 μ)).card = 3) :
    nuHatOrbit c h12 (nuHat c h12 μ) = nuHatFinset c h12 (BPrimeOf c h12 χ.1) := by
  classical
  have hμB : μ ∈ BPrimeOf c h12 χ.1 := by
    rw [BPrimeOf]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ μ, hμs, hμt, hχδ⟩
  have hB' : (BPrimeOf c h12 χ.1).Nonempty := ⟨μ, hμB⟩
  have h41 := lemma_4_1 c h12 hSC hS4 (χ := χ.1) (Or.inl χ.2) hB'
  let O : Finset (Irr (↥c.B)) := nuHatFinset c h12 (BPrimeOf c h12 χ.1)
  have hμO : nuHat c h12 μ ∈ O := by
    exact Finset.mem_image.mpr ⟨μ, hμB, rfl⟩
  have hNSinv : ∀ (g : G) (hg : g ∈ normalizerS c) (β : Irr (↥c.B)),
      β ∈ O → conjIrrB c (B_conj_mem_of_normalizerS c hg) β ∈ O := by
    intro g hg β hβ
    have hβ' : β ∈ nuHatImage c h12 (BPrimeOf c h12 χ.1) :=
      (mem_nuHatImage_iff c h12 (BPrimeOf c h12 χ.1) β).2 hβ
    have h' := h41.2.2.2.2.2 g hg β hβ'
    exact (mem_nuHatImage_iff c h12 (BPrimeOf c h12 χ.1)
      (conjIrrB c (B_conj_mem_of_normalizerS c hg) β)).1 h'
  have horbit_subset : nuHatOrbit c h12 (nuHat c h12 μ) ⊆ O := by
    intro β hβ
    rw [nuHatOrbit] at hβ
    rcases (Finset.mem_filter.mp hβ).2 with ⟨g, hg, hEq⟩
    rw [← hEq]
    exact hNSinv g hg (nuHat c h12 μ) hμO
  have hOcard_le : O.card ≤ 3 := by
    have hle : O.card ≤ (BPrimeOf c h12 χ.1).card := by
      exact Finset.card_image_le
    rcases h41.1 with h1 | h3
    · rw [h1] at hle
      omega
    · rw [h3] at hle
      omega
  have hOcard_ge : 3 ≤ O.card := by
    have hle : (nuHatOrbit c h12 (nuHat c h12 μ)).card ≤ O.card :=
      Finset.card_le_card horbit_subset
    rw [horb] at hle
    omega
  have hOcard : O.card = 3 := le_antisymm hOcard_le hOcard_ge
  exact Finset.eq_of_subset_of_card_le horbit_subset (by rw [hOcard, horb])

/-- The forward direction of Lemma 4.1(v) in the non-fixed case: if `ν̂`
lies in the orbit of `μ̂`, then `ν ∈ B′(χ)` for every constituent `χ` of
`δμ`. -/
private lemma BPrime_mem_of_orbit_of_nonfixed (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {μ ν : Irr (↥c.H0)} {χ : Irr G}
    (hχδ : scalarProduct G χ.1 (deltaNu c h12 μ) ≠ 0)
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1)
    (hμt : μ.1 (tH0 c) = μ.1 1)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (hνt : ν.1 (tH0 c) = ν.1 1)
    (horb : (nuHatOrbit c h12 (nuHat c h12 μ)).card = 3)
    (hνorbit : nuHat c h12 ν ∈ nuHatOrbit c h12 (nuHat c h12 μ)) :
    ν ∈ BPrimeOf c h12 χ.1 := by
  classical
  have hEqFinset := nuHatFinset_eq_orbit_of_nonfixed c h12 hSC hS4
    hχδ hμs hμt horb
  have hνimg : nuHat c h12 ν ∈ nuHatFinset c h12 (BPrimeOf c h12 χ.1) := by
    rw [← hEqFinset]
    exact hνorbit
  rw [nuHatFinset] at hνimg
  rcases Finset.mem_image.mp hνimg with ⟨ν', hν'B, hEqν'⟩
  have hν's : conjChar c.H0 (s_normalizes_H0 c h12) ν'.1 = ν'.1 := by
    rw [BPrimeOf] at hν'B
    exact (Finset.mem_filter.mp hν'B).2.1
  have hν't : ν'.1 (tH0 c) = ν'.1 1 := by
    rw [BPrimeOf] at hν'B
    exact (Finset.mem_filter.mp hν'B).2.2.1
  have hEqν : ν' = ν := nuHat_injective_on_Delta c h12 hSC hS4
    hν's hν't hνs hνt hEqν'
  rw [← hEqν]
  exact hν'B

/-- If `ν̂` is in the orbit of `μ̂`, then every constituent of `δμ` is also
a constituent of `δν`. -/
private lemma constituent_mem_of_orbit_of_nonfixed (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {μ ν : Irr (↥c.H0)} {χ : Irr G}
    (hχδ : scalarProduct G χ.1 (deltaNu c h12 μ) ≠ 0)
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1)
    (hμt : μ.1 (tH0 c) = μ.1 1)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (hνt : ν.1 (tH0 c) = ν.1 1)
    (horb : (nuHatOrbit c h12 (nuHat c h12 μ)).card = 3)
    (hνorbit : nuHat c h12 ν ∈ nuHatOrbit c h12 (nuHat c h12 μ)) :
    scalarProduct G χ.1 (deltaNu c h12 ν) ≠ 0 := by
  have hνB := BPrime_mem_of_orbit_of_nonfixed c h12 hSC hS4
    hχδ hμs hμt hνs hνt horb hνorbit
  rw [BPrimeOf] at hνB
  exact (Finset.mem_filter.mp hνB).2.2.2

/-- In the non-fixed orbit case the constituent sets of `δμ` and `δν` agree
for every `ν` with `ν̂` in the orbit of `μ̂`. -/
private lemma involved_eq_of_orbit_of_nonfixed (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {μ ν : Irr (↥c.H0)}
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1)
    (hμt : μ.1 (tH0 c) = μ.1 1)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (hνt : ν.1 (tH0 c) = ν.1 1)
    (horb : (nuHatOrbit c h12 (nuHat c h12 μ)).card = 3)
    (hνorbit : nuHat c h12 ν ∈ nuHatOrbit c h12 (nuHat c h12 μ)) :
    involved (deltaNu c h12 ν) = involved (deltaNu c h12 μ) := by
  classical
  have hsub : involved (deltaNu c h12 μ) ⊆ involved (deltaNu c h12 ν) := by
    intro χ hχ
    rw [mem_involved_iff] at hχ ⊢
    exact constituent_mem_of_orbit_of_nonfixed c h12 hSC hS4
      hχ hμs hμt hνs hνt horb hνorbit
  have hcard₁ : (involved (deltaNu c h12 μ)).card = 4 :=
    involved_deltaNu_card_eq_four c h12 hSC hS4 hμs
  have hcard₂ : (involved (deltaNu c h12 ν)).card = 4 :=
    involved_deltaNu_card_eq_four c h12 hSC hS4 hνs
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard₂, hcard₁])).symm

/-- In a one-element `N_G(S)`-orbit every normalizer conjugate is the
character itself. -/
private lemma conjIrrB_eq_self_of_orbit_card_one (h12 : Hyp12 c)
    {β : Irr (↥c.B)} (hcard : (nuHatOrbit c h12 β).card = 1)
    {g : G} (hg : g ∈ normalizerS c) :
    conjIrrB c (B_conj_mem_of_normalizerS c hg) β = β := by
  classical
  have hmem : conjIrrB c (B_conj_mem_of_normalizerS c hg) β ∈ nuHatOrbit c h12 β := by
    rw [nuHatOrbit]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, g, hg, rfl⟩
  have hβ : β ∈ nuHatOrbit c h12 β := nuHatOrbit_self_mem c h12 β
  rcases Finset.card_eq_one.mp hcard with ⟨γ, hγ⟩
  rw [hγ] at hmem hβ
  have hβeq : β = γ := by simpa using hβ
  have hconj : conjIrrB c (B_conj_mem_of_normalizerS c hg) β = γ := by simpa using hmem
  rw [← hβeq] at hconj
  exact hconj

/-- In the fixed case, the character `μ'` of Lemma 4.2 detects exactly
`ν = μ`: `(δν, μ')` is odd iff `ν̂ = μ̂` iff `ν = μ`. -/
private lemma scalarProduct_odd_iff_eq_of_fixed (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {μ : Irr (↥c.H0)}
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1)
    (hμt : μ.1 (tH0 c) = μ.1 1)
    (hfixed : (nuHatOrbit c h12 (nuHat c h12 μ)).card = 1) :
    ∃ μ' : ClassFunction G, IsCharacter μ' ∧
      ∀ ν : Irr (↥c.H0), conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 →
        ν.1 (tH0 c) = ν.1 1 →
        ((∃ n : ℤ, (n : ℂ) = scalarProduct G (deltaNu c h12 ν) μ' ∧ Odd n) ↔ ν = μ) := by
  classical
  rcases lemma_4_2 c h12 hSC hS4 (μ := μ) with ⟨μ', hμ'char, hμ'⟩
  refine ⟨μ', hμ'char, ?_⟩
  intro ν hνs hνt
  have hμ'ν : ((∃ n : ℤ, (n : ℂ) = scalarProduct G (deltaNu c h12 ν) μ' ∧ Odd n) ↔
      ∃ g : G, ∃ hg : g ∈ normalizerS c,
        conjIrrB c (B_conj_mem_of_normalizerS c hg) (nuHat c h12 ν) = nuHat c h12 μ) :=
    hμ' ν hνs hνt
  have hSiff : (∃ g : G, ∃ hg : g ∈ normalizerS c,
      conjIrrB c (B_conj_mem_of_normalizerS c hg) (nuHat c h12 ν) = nuHat c h12 μ) ↔
      nuHat c h12 ν = nuHat c h12 μ := by
    constructor
    · rintro ⟨g, hg, hEq⟩
      have hμorbν : nuHat c h12 μ ∈ nuHatOrbit c h12 (nuHat c h12 ν) := by
        rw [nuHatOrbit]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, g, hg, hEq⟩
      have hEqOrbit := nuHatOrbit_eq_of_mem c h12 hμorbν
      have hνfixed : (nuHatOrbit c h12 (nuHat c h12 ν)).card = 1 := by
        rw [← hEqOrbit, hfixed]
      have hνself : conjIrrB c (B_conj_mem_of_normalizerS c hg) (nuHat c h12 ν) =
          nuHat c h12 ν :=
        conjIrrB_eq_self_of_orbit_card_one c h12 hνfixed hg
      rwa [hνself] at hEq
    · intro hEq
      exact ⟨1, (normalizerS c).one_mem, by
        simpa [conjIrrB_one_local c (nuHat c h12 ν)] using hEq⟩
  have hνμ : nuHat c h12 ν = nuHat c h12 μ ↔ ν = μ := by
    constructor
    · intro hEq
      exact nuHat_injective_on_Delta c h12 hSC hS4 hνs hνt hμs hμt hEq
    · intro hEq
      exact congrArg (nuHat c h12) hEq
  rwa [hSiff, hνμ] at hμ'ν

/-- A natural-number multiple of a character is a character. -/
private lemma isCharacter_nsmul (k : ℕ) {χ : ClassFunction G} (hχ : IsCharacter χ) :
    IsCharacter ((k : ℂ) • χ) := by
  induction k with
  | zero => simpa using (isCharacter_zero (G := G))
  | succ k ih =>
      have hEq : ((k + 1 : ℕ) : ℂ) • χ = (k : ℂ) • χ + χ := by
        ext x
        simp [Nat.cast_add]
        ring
      rw [hEq]
      exact isCharacter_add ih hχ

/-- An integer multiple of a generalized character is generalized. -/
private lemma isGeneralizedCharacter_smul_int (n : ℤ) {φ : ClassFunction G}
    (hφ : IsGeneralizedCharacter φ) : IsGeneralizedCharacter ((n : ℂ) • φ) := by
  rcases hφ with ⟨δ₁, δ₂, hδ₁, hδ₂, hφeq⟩
  have hEq0 : (n : ℂ) • φ = (n : ℂ) • δ₁ - (n : ℂ) • δ₂ := by
    rw [hφeq]
    ext x
    simp
    ring
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · refine ⟨(k : ℂ) • δ₁, (k : ℂ) • δ₂, isCharacter_nsmul k hδ₁,
      isCharacter_nsmul k hδ₂, ?_⟩
    simpa [hEq0, Int.cast_ofNat] using hEq0
  · refine ⟨(k : ℂ) • δ₂, (k : ℂ) • δ₁, isCharacter_nsmul k hδ₂,
      isCharacter_nsmul k hδ₁, ?_⟩
    rw [hφeq]
    ext x
    simp
    ring

/-- The sum of two generalized characters is generalized. -/
private lemma isGeneralizedCharacter_add {φ ψ : ClassFunction G}
    (hφ : IsGeneralizedCharacter φ) (hψ : IsGeneralizedCharacter ψ) :
    IsGeneralizedCharacter (φ + ψ) := by
  rcases hφ with ⟨δ₁, δ₂, hδ₁, hδ₂, hφeq⟩
  rcases hψ with ⟨ε₁, ε₂, hε₁, hε₂, hψeq⟩
  refine ⟨δ₁ + ε₁, δ₂ + ε₂, isCharacter_add hδ₁ hε₁, isCharacter_add hδ₂ hε₂, ?_⟩
  rw [hφeq, hψeq]
  funext x
  simp [Pi.add_apply, Pi.sub_apply]
  ring

/-- The scalar product of a generalized character with a character is an
integer. -/
private lemma scalarProduct_int_of_generalized_char {δ ψ : ClassFunction G}
    (hδ : IsGeneralizedCharacter δ) (hψ : IsCharacter ψ) :
    ∃ m : ℤ, (m : ℂ) = scalarProduct G δ ψ := by
  classical
  rcases char_decomp_generalized hδ with ⟨ι, _, χs, ms, hirr, hdist, hδsum⟩
  have hψgen : IsGeneralizedCharacter ψ := by
    exact ⟨ψ, 0, hψ, isCharacter_zero, by simp⟩
  have hterm : ∀ i, ∃ a : ℤ, (a : ℂ) = scalarProduct G (χs i) ψ := by
    intro i
    rcases multiplicity_int (hirr i) ψ hψgen with ⟨a, ha⟩
    exact ⟨a, ha.symm⟩
  choose a ha using hterm
  have hsp : scalarProduct G δ ψ = ((∑ i, ms i * a i : ℤ) : ℂ) := by
    rw [hδsum]
    rw [scalarProduct_sum_left]
    calc
      (∑ i, scalarProduct G ((ms i : ℂ) • χs i) ψ)
          = ∑ i, ((ms i * a i : ℤ) : ℂ) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [scalarProduct_smul_left]
              rw [← ha i]
              norm_num
      _ = ((∑ i, ms i * a i : ℤ) : ℂ) := by
              rw [Int.cast_sum]
  exact ⟨∑ i, ms i * a i, hsp.symm⟩

/-- Fixed case, parity rule: for a fixed `μ̂`, every integral combination
with odd coefficient at `δμ` has an irreducible constituent of odd
multiplicity (source L1068-1083). -/
private lemma exists_odd_multiplicity_of_fixed_sum (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {μ : Irr (↥c.H0)}
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1)
    (hμt : μ.1 (tH0 c) = μ.1 1)
    (hfixed : (nuHatOrbit c h12 (nuHat c h12 μ)).card = 1) :
    ∃ μ' : ClassFunction G, IsCharacter μ' ∧
      ∀ (I : Finset (Irr (↥c.H0))) (n : Irr (↥c.H0) → ℤ) (nμ : ℤ),
        (∀ ν ∈ I, conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 ∧
          ν.1 (tH0 c) = ν.1 1 ∧ ν ≠ μ) →
        Odd nμ →
        ∃ χ : ClassFunction G, IsIrreducibleCharacter χ ∧
          ∃ m : ℤ, (m : ℂ) = scalarProduct G χ
            ((nμ : ℂ) • deltaNu c h12 μ +
              ∑ ν ∈ I, (n ν : ℂ) • deltaNu c h12 ν) ∧ Odd m := by
  classical
  rcases scalarProduct_odd_iff_eq_of_fixed c h12 hSC hS4 hμs hμt hfixed with
    ⟨μ', hμ'char, hodd⟩
  refine ⟨μ', hμ'char, ?_⟩
  intro I n nμ hI hOddnμ
  let φ : ClassFunction G := (nμ : ℂ) • deltaNu c h12 μ + ∑ ν ∈ I, (n ν : ℂ) • deltaNu c h12 ν
  have hspμ : ∃ n0 : ℤ, (n0 : ℂ) = scalarProduct G (deltaNu c h12 μ) μ' ∧ Odd n0 :=
    (hodd μ hμs hμt).2 rfl
  rcases hspμ with ⟨nμ0, hnμ0, hOddμ0⟩
  have hspI : ∀ ν : Irr (↥c.H0), ν ∈ I →
      ∃ m : ℤ, (m : ℂ) = scalarProduct G (deltaNu c h12 ν) μ' ∧ Even m := by
    intro ν hνI
    have hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 := (hI ν hνI).1
    have hνt : ν.1 (tH0 c) = ν.1 1 := (hI ν hνI).2.1
    have hνμ : ν ≠ μ := (hI ν hνI).2.2
    have hnot : ¬ ∃ m : ℤ, (m : ℂ) = scalarProduct G (deltaNu c h12 ν) μ' ∧ Odd m := by
      intro h
      exact hνμ ((hodd ν hνs hνt).1 h)
    rcases scalarProduct_int_of_generalized_char (deltaNu_isGeneralized c h12 ν) hμ'char with
      ⟨m, hm⟩
    refine ⟨m, hm, ?_⟩
    by_contra hnotEven
    have hOddm : Odd m := (Int.not_even_iff_odd).1 hnotEven
    exact hnot ⟨m, hm, hOddm⟩
  let mν : Irr (↥c.H0) → ℤ := fun ν => if hν : ν ∈ I then Classical.choose (hspI ν hν) else 0
  have hmν : ∀ ν ∈ I, (mν ν : ℂ) = scalarProduct G (deltaNu c h12 ν) μ' ∧ Even (mν ν) := by
    intro ν hν
    have h := Classical.choose_spec (hspI ν hν)
    simpa [mν, hν] using h
  have hφsp : scalarProduct G φ μ' =
      ((nμ * nμ0 + ∑ ν ∈ I, n ν * mν ν : ℤ) : ℂ) := by
    dsimp [φ]
    rw [scalarProduct_add_left, scalarProduct_smul_left]
    have hsum_left : scalarProduct G (∑ ν ∈ I, (n ν : ℂ) • deltaNu c h12 ν) μ' =
        ∑ ν ∈ I, (n ν : ℂ) * scalarProduct G (deltaNu c h12 ν) μ' := by
      calc
        scalarProduct G (∑ ν ∈ I, (n ν : ℂ) • deltaNu c h12 ν) μ'
            = scalarProduct G (∑ j : {ν : Irr (↥c.H0) // ν ∈ I},
                (n j.1 : ℂ) • deltaNu c h12 j.1) μ' := by
                rw [Finset.sum_coe_sort I (fun ν => (n ν : ℂ) • deltaNu c h12 ν)]
        _ = ∑ j : {ν : Irr (↥c.H0) // ν ∈ I},
                (n j.1 : ℂ) * scalarProduct G (deltaNu c h12 j.1) μ' := by
                rw [scalarProduct_sum_left]
                refine Finset.sum_congr rfl ?_
                intro j hj
                rw [scalarProduct_smul_left]
        _ = ∑ ν ∈ I, (n ν : ℂ) * scalarProduct G (deltaNu c h12 ν) μ' := by
                rw [← Finset.sum_coe_sort I (fun ν =>
                  (n ν : ℂ) * scalarProduct G (deltaNu c h12 ν) μ')]
    rw [hsum_left]
    have h1 : (nμ : ℂ) * scalarProduct G (deltaNu c h12 μ) μ' =
        ((nμ * nμ0 : ℤ) : ℂ) := by
      rw [← hnμ0]
      norm_num
    have h2 : (∑ ν ∈ I, (n ν : ℂ) * scalarProduct G (deltaNu c h12 ν) μ') =
        ((∑ ν ∈ I, n ν * mν ν : ℤ) : ℂ) := by
      calc
        (∑ ν ∈ I, (n ν : ℂ) * scalarProduct G (deltaNu c h12 ν) μ')
            = ∑ ν ∈ I, ((n ν * mν ν : ℤ) : ℂ) := by
                refine Finset.sum_congr rfl ?_
                intro ν hν
                rw [← (hmν ν hν).1]
                norm_num
        _ = ((∑ ν ∈ I, n ν * mν ν : ℤ) : ℂ) := by
                rw [Int.cast_sum]
    rw [h1, h2]
    rw [Int.cast_add]
  have hOddN : Odd (nμ * nμ0 + ∑ ν ∈ I, n ν * mν ν) := by
    have hOddProd : Odd (nμ * nμ0) := hOddnμ.mul hOddμ0
    have hEvenSum : Even (∑ ν ∈ I, n ν * mν ν) := by
      apply Finset.even_sum
      intro ν hν
      exact (Int.even_mul).2 (Or.inr (hmν ν hν).2)
    exact hOddProd.add_even hEvenSum
  have hφgen : IsGeneralizedCharacter φ := by
    dsimp [φ]
    have hgen1 : IsGeneralizedCharacter ((nμ : ℂ) • deltaNu c h12 μ) :=
      isGeneralizedCharacter_smul_int nμ (deltaNu_isGeneralized c h12 μ)
    have hgen2 : IsGeneralizedCharacter (∑ ν ∈ I, (n ν : ℂ) • deltaNu c h12 ν) := by
      refine Finset.induction_on I ?_ ?_
      · have hz : IsGeneralizedCharacter (0 : ClassFunction G) :=
          ⟨0, 0, isCharacter_zero, isCharacter_zero, by simp⟩
        simpa using hz
      · intro a s has ih
        rw [Finset.sum_insert has]
        exact isGeneralizedCharacter_add
          (isGeneralizedCharacter_smul_int (n a) (deltaNu_isGeneralized c h12 a)) ih
    exact isGeneralizedCharacter_add hgen1 hgen2
  rcases char_decomp_generalized hφgen with ⟨ι, _, χs, ms, hirr, hdist, hφsum⟩
  have hterm : ∀ i, ∃ a : ℤ, (a : ℂ) = scalarProduct G (χs i) μ' := by
    intro i
    rcases multiplicity_int (hirr i) μ'
      (by exact ⟨μ', 0, hμ'char, isCharacter_zero, by simp⟩) with ⟨a, ha⟩
    exact ⟨a, ha.symm⟩
  choose a ha using hterm
  have hsp2 : scalarProduct G φ μ' = ((∑ i, ms i * a i : ℤ) : ℂ) := by
    rw [hφsum]
    rw [scalarProduct_sum_left]
    calc
      (∑ i, scalarProduct G ((ms i : ℂ) • χs i) μ')
          = ∑ i, ((ms i * a i : ℤ) : ℂ) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [scalarProduct_smul_left]
              rw [← ha i]
              norm_num
      _ = ((∑ i, ms i * a i : ℤ) : ℂ) := by
              rw [Int.cast_sum]
  have hOddExists : ∃ i, Odd (ms i) := by
    by_contra hnone
    have hallEven : ∀ i, Even (ms i) := by
      intro i
      by_contra hnotEven
      have hOddm : Odd (ms i) := (Int.not_even_iff_odd).1 hnotEven
      exact hnone ⟨i, hOddm⟩
    have hEvenSum : Even (∑ i, ms i * a i : ℤ) := by
      apply Finset.even_sum
      intro i hi
      exact (Int.even_mul).2 (Or.inl (hallEven i))
    have hN : (nμ * nμ0 + ∑ ν ∈ I, n ν * mν ν : ℤ) = (∑ i, ms i * a i : ℤ) := by
      have hNℂ : ((nμ * nμ0 + ∑ ν ∈ I, n ν * mν ν : ℤ) : ℂ) =
          ((∑ i, ms i * a i : ℤ) : ℂ) :=
        hφsp.symm.trans hsp2
      exact_mod_cast hNℂ
    have hEvenN : Even (nμ * nμ0 + ∑ ν ∈ I, n ν * mν ν) := by
      rwa [hN]
    exact (Int.not_even_iff_odd).2 hOddN hEvenN
  rcases hOddExists with ⟨i, hOddi⟩
  refine ⟨χs i, hirr i, ms i, ?_, hOddi⟩
  change (ms i : ℂ) = scalarProduct G (χs i) φ
  rw [hφsum]
  exact (scalarProduct_irr_decomp hirr hdist i).symm

/-- The parity of a sum of odd integers is the parity of the number of
summands. -/
private lemma odd_sum_iff_odd_card {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hf : ∀ i ∈ s, Odd (f i)) :
    Odd (∑ i ∈ s, f i) ↔ Odd s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
      rw [Finset.sum_insert has, Finset.card_insert_of_notMem has]
      have hfa : Odd (f a) := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, Odd (f i) := by
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)
      have ih' : Odd (∑ i ∈ s, f i) ↔ Odd s.card := ih hfs
      have hsumOdd : Odd (f a + ∑ i ∈ s, f i) ↔ ¬ Odd (∑ i ∈ s, f i) := by
        constructor
        · intro h
          by_contra hb
          exact (Int.not_even_iff_odd.mpr h) (hfa.add_odd hb)
        · intro hnb
          exact hfa.add_even (Int.not_odd_iff_even.mp hnb)
      have hcardOdd : Odd (s.card + 1) ↔ ¬ Odd s.card := by
        constructor
        · intro h
          by_contra hb
          have h' : Odd (1 + s.card) := by simpa [Nat.add_comm] using h
          exact (Nat.not_even_iff_odd.mpr h')
            ((by norm_num : Odd (1 : ℕ)).add_odd hb)
        · intro hnb
          simpa [Nat.add_comm] using
            (Nat.not_odd_iff_even.mp hnb).add_odd (by norm_num : Odd (1 : ℕ))
      calc
        Odd (f a + ∑ i ∈ s, f i) ↔ ¬ Odd (∑ i ∈ s, f i) := hsumOdd
        _ ↔ ¬ Odd s.card := by rw [ih']
        _ ↔ Odd (s.card + 1) := by
          constructor
          · intro h
            exact hcardOdd.mpr h
          · intro h
            exact (hcardOdd.mp h)

/-- Scalar product against a signed `Fin 4` sum, expanded on the left. -/
private lemma scalarProduct_signed_sum_left {δ : ClassFunction G}
    {a : Fin 4 → ClassFunction G} (ha : ∀ i, IsIrreducibleCharacter (a i))
    {s : Fin 4 → ℤ} (hδ : δ = ∑ i, (s i : ℂ) • a i) (ε : ClassFunction G) :
    scalarProduct G δ ε = ∑ i, (s i : ℂ) * scalarProduct G (a i) ε := by
  rw [hδ, scalarProduct_sum_left]
  apply Finset.sum_congr rfl
  intro i hi
  rw [scalarProduct_smul_left]

/-- Scalar product of an irreducible against a signed `Fin 4` sum, expanded
on the right. -/
private lemma scalarProduct_irr_decomp_right {ε : ClassFunction G}
    {b : Fin 4 → ClassFunction G} (hb : ∀ i, IsIrreducibleCharacter (b i))
    (hbinj : Function.Injective b) {t : Fin 4 → ℤ}
    (hε : ε = ∑ i, (t i : ℂ) • b i) {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) :
    scalarProduct G χ ε =
      (if h : ∃ i, b i = χ then (t (Classical.choose h) : ℂ) else 0) := by
  classical
  rw [hε]
  by_cases h : ∃ i, b i = χ
  · let i₀ := Classical.choose h
    have hi₀ : b i₀ = χ := Classical.choose_spec h
    have hchoose : Classical.choose h = i₀ := hbinj (by
      simpa [Classical.choose_spec h] using hi₀.symm)
    rw [scalarProduct_sum_right]
    rw [Finset.sum_eq_single i₀ ?_ ?_]
    · have hχi₀ : χ = b i₀ := hi₀.symm
      rw [dif_pos h]
      rw [hchoose]
      rw [scalarProduct_smul_right, scalarProduct_irr_ite hχ (hb i₀)]
      simp [hχi₀]
    · intro i hi hne
      rw [scalarProduct_smul_right]
      have hbi : b i ≠ χ := by
        intro hEq
        exact hne (hbinj (hEq.trans hi₀.symm))
      have hχi : χ ≠ b i := by
        intro hEq
        exact hbi hEq.symm
      rw [scalarProduct_irr_ite hχ (hb i)]
      simp [hχi]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ i₀))
  · rw [scalarProduct_sum_right]
    have hzero : (if h : ∃ i, b i = χ then (t (Classical.choose h) : ℂ) else 0) = 0 := by
      simp [h]
    rw [hzero]
    apply Finset.sum_eq_zero
    intro i hi
    rw [scalarProduct_smul_right, scalarProduct_irr_ite hχ (hb i)]
    have hbi : b i ≠ χ := by
      intro hEq
      exact h (⟨i, hEq⟩)
    have hχi : χ ≠ b i := by
      intro hEq
      exact hbi hEq.symm
    simp [hχi]

/-- The scalar product of two signed `Fin 4` sums is an integer sum of
`0, ±1` terms, one per equality of an `a`-basis member with a `b`-basis
member. -/
private lemma scalarProduct_signed_four_eq_int_sum {δ ε : ClassFunction G}
    {a : Fin 4 → ClassFunction G} (ha : ∀ i, IsIrreducibleCharacter (a i))
    (hainj : Function.Injective a) {s : Fin 4 → ℤ}
    (hs : ∀ i, s i = 1 ∨ s i = -1)
    (hδ : δ = ∑ i, (s i : ℂ) • a i)
    {b : Fin 4 → ClassFunction G} (hb : ∀ i, IsIrreducibleCharacter (b i))
    (hbinj : Function.Injective b) {t : Fin 4 → ℤ}
    (ht : ∀ i, t i = 1 ∨ t i = -1)
    (hε : ε = ∑ i, (t i : ℂ) • b i) :
    ∃ z : ℤ, ∃ c : Fin 4 → ℤ,
      (z : ℂ) = scalarProduct G δ ε ∧
      (∀ i, c i = 0 ∨ c i = 1 ∨ c i = -1) ∧
      (∀ i, c i ≠ 0 ↔ ∃ j, b j = a i) ∧
      z = ∑ i, c i := by
  classical
  let c : Fin 4 → ℤ := fun i =>
    if h : ∃ j, b j = a i then s i * t (Classical.choose h) else 0
  have hc_mem : ∀ i, c i = 0 ∨ c i = 1 ∨ c i = -1 := by
    intro i
    by_cases h : ∃ j, b j = a i
    · have hc : c i = s i * t (Classical.choose h) := by simp [c, h]
      rcases hs i with hs | hs <;> rcases ht (Classical.choose h) with ht | ht <;>
        simp [hc, hs, ht]
    · simp [c, h]
  have hc_iff : ∀ i, c i ≠ 0 ↔ ∃ j, b j = a i := by
    intro i
    constructor
    · intro hne
      by_contra hnot
      exact hne (by simp [c, hnot])
    · rintro ⟨j, hj⟩
      have h' : ∃ k, b k = a i := ⟨j, hj⟩
      have hchoose : Classical.choose h' = j := hbinj (by
        rw [Classical.choose_spec h']
        exact hj.symm)
      have hcval : c i = s i * t j := by
        simp [c, h', hchoose]
      intro hc0
      rcases hs i with hs | hs <;> rcases ht j with ht | ht <;>
        simp [hcval, hs, ht] at hc0
  have hz : scalarProduct G δ ε = ((∑ i, c i : ℤ) : ℂ) := by
    rw [scalarProduct_signed_sum_left ha hδ ε]
    calc
      (∑ i, (s i : ℂ) * scalarProduct G (a i) ε)
          = ∑ i, ((c i : ℤ) : ℂ) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [scalarProduct_irr_decomp_right (ε := ε) (b := b) (t := t)
                hb hbinj hε (χ := a i) (ha i)]
              by_cases h : ∃ j, b j = a i
              · simp [c, h]
              · simp [c, h]
      _ = ((∑ i, c i : ℤ) : ℂ) := by rw [Int.cast_sum]
  exact ⟨∑ i, c i, c, hz.symm, hc_mem, hc_iff, rfl⟩

/-- Scalar product of two signed four-sums whose only common constituents
are `x` and `y`, given matching indices. -/
private lemma scalarProduct_two_common_of_indices
    {δ₁ δ₂ : ClassFunction G}
    {a : Fin 4 → ClassFunction G} (ha : ∀ i, IsIrreducibleCharacter (a i))
    (hainj : Function.Injective a) {s : Fin 4 → ℤ}
    (hs : ∀ i, s i = 1 ∨ s i = -1)
    (hδ₁ : δ₁ = ∑ i, (s i : ℂ) • a i)
    {b : Fin 4 → ClassFunction G} (hb : ∀ i, IsIrreducibleCharacter (b i))
    (hbinj : Function.Injective b) {t : Fin 4 → ℤ}
    (ht : ∀ i, t i = 1 ∨ t i = -1)
    (hδ₂ : δ₂ = ∑ i, (t i : ℂ) • b i)
    {i₁ i₂ j₁ j₂ : Fin 4} {x y : Irr G}
    (hx₁ : a i₁ = x.1) (hx₂ : b j₁ = x.1)
    (hy₁ : a i₂ = y.1) (hy₂ : b j₂ = y.1)
    (hi : i₁ ≠ i₂) (hj : j₁ ≠ j₂)
    (hother : ∀ i, i ≠ i₁ → i ≠ i₂ → ∀ j, b j ≠ a i) :
    scalarProduct G δ₁ δ₂ =
      (((s i₁ * t j₁ + s i₂ * t j₂ : ℤ) : ℂ)) := by
  classical
  rw [scalarProduct_signed_sum_left ha hδ₁ δ₂]
  let f : Fin 4 → ℂ := fun i => (s i : ℂ) * scalarProduct G (a i) δ₂
  have hx₁₂ : a i₁ = b j₁ := hx₁.trans hx₂.symm
  have hy₁₂ : a i₂ = b j₂ := hy₁.trans hy₂.symm
  have hterm₁ : f i₁ = ((s i₁ * t j₁ : ℤ) : ℂ) := by
    dsimp [f]
    rw [scalarProduct_irr_decomp_right (ε := δ₂) (b := b) (t := t)
      hb hbinj hδ₂ (χ := a i₁) (ha i₁)]
    have h'ex : ∃ j, b j = a i₁ := ⟨j₁, hx₁₂.symm⟩
    have hchoose : Classical.choose h'ex = j₁ := hbinj (by
      simpa [Classical.choose_spec h'ex] using hx₁₂)
    rw [dif_pos h'ex, hchoose]
    norm_num
  have hterm₂ : f i₂ = ((s i₂ * t j₂ : ℤ) : ℂ) := by
    dsimp [f]
    rw [scalarProduct_irr_decomp_right (ε := δ₂) (b := b) (t := t)
      hb hbinj hδ₂ (χ := a i₂) (ha i₂)]
    have h'ex : ∃ j, b j = a i₂ := ⟨j₂, hy₁₂.symm⟩
    have hchoose : Classical.choose h'ex = j₂ := hbinj (by
      simpa [Classical.choose_spec h'ex] using hy₁₂)
    rw [dif_pos h'ex, hchoose]
    norm_num
  have hzero : ∀ i, i ≠ i₁ → i ≠ i₂ → f i = 0 := by
    intro i hi₁ hi₂
    dsimp [f]
    rw [scalarProduct_irr_decomp_right (ε := δ₂) (b := b) (t := t)
      hb hbinj hδ₂ (χ := a i) (ha i)]
    by_cases h'ex : ∃ j, b j = a i
    · rcases h'ex with ⟨j, hj⟩
      exact False.elim ((hother i hi₁ hi₂ j) hj)
    · simp [h'ex]
  have hsum0 : (∑ i ∈ ((Finset.univ.erase i₁).erase i₂), f i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_erase] at hi
    rcases hi with ⟨hi₂, hi₁mem⟩
    rw [Finset.mem_erase] at hi₁mem
    have hi₁ : i ≠ i₁ := hi₁mem.1
    exact hzero i hi₁ hi₂
  calc
    (∑ i, f i) = f i₁ + f i₂ + (∑ i ∈ ((Finset.univ.erase i₁).erase i₂), f i) := by
      change (∑ i ∈ (Finset.univ : Finset (Fin 4)), f i) =
        f i₁ + f i₂ + (∑ i ∈ ((Finset.univ.erase i₁).erase i₂), f i)
      rw [← Finset.add_sum_erase (s := Finset.univ) f (a := i₁) (by simp)]
      rw [← Finset.add_sum_erase (s := (Finset.univ.erase i₁)) f (a := i₂) (by simp [hi.symm])]
      abel
    _ = ((s i₁ * t j₁ + s i₂ * t j₂ : ℤ) : ℂ) := by
      rw [hterm₁, hterm₂, hsum0]
      norm_num

/-- For a non-fixed `μ̂`, every `ν ∈ B′(χ)` with `χ` involved in `δμ` has
`ν̂` in the `N_G(S)`-orbit of `μ̂` (Lemma 4.1(v) plus the orbit-size
hypothesis). -/
private lemma nuHat_mem_orbit_of_BPrime (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) {μ ν : Irr (↥c.H0)} {χ : Irr G}
    (hχδ : scalarProduct G χ.1 (deltaNu c h12 μ) ≠ 0)
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1)
    (hμt : μ.1 (tH0 c) = μ.1 1)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (hνt : ν.1 (tH0 c) = ν.1 1)
    (horb : (nuHatOrbit c h12 (nuHat c h12 μ)).card = 3)
    (hνB : ν ∈ BPrimeOf c h12 χ.1) :
    nuHat c h12 ν ∈ nuHatOrbit c h12 (nuHat c h12 μ) := by
  classical
  have hEqSets := nuHatFinset_eq_orbit_of_nonfixed c h12 hSC hS4
    hχδ hμs hμt horb
  rw [hEqSets]
  exact Finset.mem_image.mpr ⟨ν, hνB, rfl⟩

/-- If `ν₀̂` is in the orbit of `μ̂`, then every `ν ∈ B′(χ)` for a
constituent `χ` of `δν₀` also has `ν̂` in that orbit. -/
private lemma nuHat_mem_orbit_of_BPrime_of_orbit (c : Hyp11 G) (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {μ ν₀ ν : Irr (↥c.H0)} {χ : Irr G}
    (hν₀orbit : nuHat c h12 ν₀ ∈ nuHatOrbit c h12 (nuHat c h12 μ))
    (hχδ : scalarProduct G χ.1 (deltaNu c h12 ν₀) ≠ 0)
    (hν₀s : conjChar c.H0 (s_normalizes_H0 c h12) ν₀.1 = ν₀.1)
    (hν₀t : ν₀.1 (tH0 c) = ν₀.1 1)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (hνt : ν.1 (tH0 c) = ν.1 1)
    (horb : (nuHatOrbit c h12 (nuHat c h12 μ)).card = 3)
    (hνB : ν ∈ BPrimeOf c h12 χ.1) :
    nuHat c h12 ν ∈ nuHatOrbit c h12 (nuHat c h12 μ) := by
  classical
  have hEqOrbit := nuHatOrbit_eq_of_mem c h12 hν₀orbit
  have horb' : (nuHatOrbit c h12 (nuHat c h12 ν₀)).card = 3 := by
    rw [hEqOrbit, horb]
  have hres := nuHat_mem_orbit_of_BPrime c h12 hSC hS4 hχδ
    hν₀s hν₀t hνs hνt horb' hνB
  rw [hEqOrbit] at hres
  exact hres

/-- The `ν̂`-image of `B′(χ)` has exactly three elements in the non-fixed
orbit case. -/
private lemma image_card_eq_three_of_nonfixed_orbit (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {μ : Irr (↥c.H0)} {χ : Irr G}
    (hχδ : scalarProduct G χ.1 (deltaNu c h12 μ) ≠ 0)
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1)
    (hμt : μ.1 (tH0 c) = μ.1 1)
    (horb : (nuHatOrbit c h12 (nuHat c h12 μ)).card = 3) :
    (nuHatFinset c h12 (BPrimeOf c h12 χ.1)).card = 3 := by
  classical
  have hμB : μ ∈ BPrimeOf c h12 χ.1 := by
    rw [BPrimeOf]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ μ, hμs, hμt, hχδ⟩
  have hB' : (BPrimeOf c h12 χ.1).Nonempty := ⟨μ, hμB⟩
  have h41 := lemma_4_1 c h12 hSC hS4 (χ := χ.1) (Or.inl χ.2) hB'
  let O : Finset (Irr (↥c.B)) := nuHatFinset c h12 (BPrimeOf c h12 χ.1)
  have hμO : nuHat c h12 μ ∈ O := by
    exact Finset.mem_image.mpr ⟨μ, hμB, rfl⟩
  have hNSinv : ∀ (g : G) (hg : g ∈ normalizerS c) (β : Irr (↥c.B)),
      β ∈ O → conjIrrB c (B_conj_mem_of_normalizerS c hg) β ∈ O := by
    intro g hg β hβ
    have hβ' : β ∈ nuHatImage c h12 (BPrimeOf c h12 χ.1) :=
      (mem_nuHatImage_iff c h12 (BPrimeOf c h12 χ.1) β).2 hβ
    have h' := h41.2.2.2.2.2 g hg β hβ'
    exact (mem_nuHatImage_iff c h12 (BPrimeOf c h12 χ.1)
      (conjIrrB c (B_conj_mem_of_normalizerS c hg) β)).1 h'
  have horbit_subset : nuHatOrbit c h12 (nuHat c h12 μ) ⊆ O := by
    intro β hβ
    rw [nuHatOrbit] at hβ
    rcases (Finset.mem_filter.mp hβ).2 with ⟨g, hg, hEq⟩
    rw [← hEq]
    exact hNSinv g hg (nuHat c h12 μ) hμO
  have hOcard_le : O.card ≤ 3 := by
    have hle : O.card ≤ (BPrimeOf c h12 χ.1).card := by
      exact Finset.card_image_le
    rcases h41.1 with h1 | h3
    · rw [h1] at hle
      omega
    · rw [h3] at hle
      omega
  have hOcard_ge : 3 ≤ O.card := by
    have hle : (nuHatOrbit c h12 (nuHat c h12 μ)).card ≤ O.card :=
      Finset.card_le_card horbit_subset
    rw [horb] at hle
    omega
  exact le_antisymm hOcard_le hOcard_ge


/-- In the non-fixed orbit case, `B′(χ)` has exactly three members. -/
private lemma BPrime_card_eq_three_of_nonfixed_orbit (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {μ : Irr (↥c.H0)} {χ : Irr G}
    (hχδ : scalarProduct G χ.1 (deltaNu c h12 μ) ≠ 0)
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1)
    (hμt : μ.1 (tH0 c) = μ.1 1)
    (horb : (nuHatOrbit c h12 (nuHat c h12 μ)).card = 3) :
    (BPrimeOf c h12 χ.1).card = 3 := by
  classical
  have hOcard := image_card_eq_three_of_nonfixed_orbit c h12 hSC hS4
    hχδ hμs hμt horb
  have hle : (nuHatFinset c h12 (BPrimeOf c h12 χ.1)).card ≤
      (BPrimeOf c h12 χ.1).card := by
    exact Finset.card_image_le
  rw [hOcard] at hle
  have hμB : μ ∈ BPrimeOf c h12 χ.1 := by
    rw [BPrimeOf]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ μ, hμs, hμt, hχδ⟩
  have hB' : (BPrimeOf c h12 χ.1).Nonempty := ⟨μ, hμB⟩
  have h41 := lemma_4_1 c h12 hSC hS4 (χ := χ.1) (Or.inl χ.2) hB'
  rcases h41.1 with h1 | h3
  · rw [h1] at hle
    omega
  · exact h3

/-- `ν ↦ ν̂` is injective on `B′(χ)` in the non-fixed orbit case. -/
private lemma nuHat_injective_on_BPrime_of_nonfixed (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {μ : Irr (↥c.H0)} {χ : Irr G}
    (hχδ : scalarProduct G χ.1 (deltaNu c h12 μ) ≠ 0)
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1)
    (hμt : μ.1 (tH0 c) = μ.1 1)
    (horb : (nuHatOrbit c h12 (nuHat c h12 μ)).card = 3) :
    Set.InjOn (nuHat c h12) ↑(BPrimeOf c h12 χ.1) := by
  classical
  have hcard := BPrime_card_eq_three_of_nonfixed_orbit c h12 hSC hS4
    hχδ hμs hμt horb
  have himg := image_card_eq_three_of_nonfixed_orbit c h12 hSC hS4
    hχδ hμs hμt horb
  have hEq : ((BPrimeOf c h12 χ.1).image (nuHat c h12)).card =
      (BPrimeOf c h12 χ.1).card := by
    change (nuHatFinset c h12 (BPrimeOf c h12 χ.1)).card =
      (BPrimeOf c h12 χ.1).card
    rw [himg, hcard]
  exact Finset.injOn_of_card_image_eq hEq

/-- Three distinct `ν`'s in `B′(χ)` exist in the non-fixed orbit case. -/
private lemma exists_three_BPrime_of_nonfixed_orbit (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {μ : Irr (↥c.H0)} {χ : Irr G}
    (hχδ : scalarProduct G χ.1 (deltaNu c h12 μ) ≠ 0)
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1)
    (hμt : μ.1 (tH0 c) = μ.1 1)
    (horb : (nuHatOrbit c h12 (nuHat c h12 μ)).card = 3) :
    ∃ ν₁ ν₂ ν₃ : Irr (↥c.H0),
      ν₁ ∈ BPrimeOf c h12 χ.1 ∧ ν₂ ∈ BPrimeOf c h12 χ.1 ∧
      ν₃ ∈ BPrimeOf c h12 χ.1 ∧ ν₁ ≠ ν₂ ∧ ν₁ ≠ ν₃ ∧ ν₂ ≠ ν₃ := by
  classical
  have hcard := BPrime_card_eq_three_of_nonfixed_orbit c h12 hSC hS4
    hχδ hμs hμt horb
  rcases Finset.card_eq_three.mp hcard with
    ⟨ν₁, ν₂, ν₃, h₁₂, h₁₃, h₂₃, hset⟩
  have hmem₁ : ν₁ ∈ BPrimeOf c h12 χ.1 := by
    rw [hset]
    simp
  have hmem₂ : ν₂ ∈ BPrimeOf c h12 χ.1 := by
    rw [hset]
    simp
  have hmem₃ : ν₃ ∈ BPrimeOf c h12 χ.1 := by
    rw [hset]
    simp
  exact ⟨ν₁, ν₂, ν₃, hmem₁, hmem₂, hmem₃, h₁₂, h₁₃, h₂₃⟩

/-- Adjacent vertices share an irreducible constituent. -/
private lemma exists_shared_constituent_of_adjacent (h12 : Hyp12 c)
    {δ ε : ClassFunction G}
    (h : deltaAdjacent c h12 δ ε) :
    ∃ χ : Irr G, χ ∈ involved δ ∧ χ ∈ involved ε := by
  classical
  unfold deltaAdjacent at h
  rcases h with ⟨_hδ, _hε, hne, hdis⟩
  by_contra hnone
  apply hdis
  intro χ hχ hχδ
  by_contra hχε
  exact False.elim (hnone ⟨⟨χ, hχ⟩,
    (mem_involved_iff δ ⟨χ, hχ⟩).2 hχδ,
    (mem_involved_iff ε ⟨χ, hχ⟩).2 hχε⟩)

/-- Adjacency is symmetric. -/
private lemma deltaAdjacent_symm (c : Hyp11 G) (h12 : Hyp12 c)
    {δ ε : ClassFunction G}
    (h : deltaAdjacent c h12 δ ε) : deltaAdjacent c h12 ε δ := by
  classical
  rcases h with ⟨hδ, hε, hne, hdis⟩
  exact ⟨hε, hδ, hne.symm, by
    intro hDis
    exact hdis (disjoint_symm hDis)⟩

/-- Reversal of a reflexive-transitive path for a symmetric relation. -/
private lemma reflTransGen_symm {α : Type*} {r : α → α → Prop}
    (hrsymm : ∀ {a b : α}, r a b → r b a) {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h₁ h₂ ih =>
      exact ((Relation.ReflTransGen.single (hrsymm h₂)).trans ih)

/-- A vertex of `Δ` adjacent to a member of a connected component lies in
the same component. -/
private lemma mem_Delta0_of_adjacent (c : Hyp11 G) (h12 : Hyp12 c)
    {Δ0 : Set (ClassFunction G)}
    (hcomp : IsConnectedComponent c h12 Δ0) {δ ε : ClassFunction G}
    (hδ : δ ∈ Δ0) (hεΔ : ε ∈ Delta c h12)
    (hadj : deltaAdjacent c h12 δ ε) : ε ∈ Δ0 := by
  by_contra hnot
  exact (hcomp.2.2.2 ε hnot δ hδ) (deltaAdjacent_symm c h12 hadj)

/-- If `ν ∈ B′(χ)` for a constituent `χ` of `δμ ∈ Δ0`, then `δν` is in the
same component. -/
private lemma deltaNu_mem_Delta0_of_BPrime (c : Hyp11 G) (h12 : Hyp12 c)
    {Δ0 : Set (ClassFunction G)}
    (hcomp : IsConnectedComponent c h12 Δ0)
    {μ : Irr (↥c.H0)} (hμΔ0 : deltaNu c h12 μ ∈ Δ0)
    {χ : Irr G} (hχδ : χ ∈ involved (deltaNu c h12 μ))
    {ν : Irr (↥c.H0)} (hνB : ν ∈ BPrimeOf c h12 χ.1) :
    deltaNu c h12 ν ∈ Δ0 := by
  classical
  have hνΔ : deltaNu c h12 ν ∈ Delta c h12 := deltaNu_mem_Delta_of_BPrime c h12 hνB
  by_cases hEq : deltaNu c h12 ν = deltaNu c h12 μ
  · simpa [hEq] using hμΔ0
  · have hχδ' : scalarProduct G χ.1 (deltaNu c h12 μ) ≠ 0 :=
      (mem_involved_iff (deltaNu c h12 μ) χ).1 hχδ
    have hχδν : scalarProduct G χ.1 (deltaNu c h12 ν) ≠ 0 := by
      rw [BPrimeOf] at hνB
      exact (Finset.mem_filter.mp hνB).2.2.2
    have hadj : deltaAdjacent c h12 (deltaNu c h12 μ) (deltaNu c h12 ν) := by
      refine ⟨hcomp.2.1 hμΔ0, hνΔ, Ne.symm hEq, ?_⟩
      intro hDis
      exact hχδν (hDis χ.1 χ.2 hχδ')
    exact mem_Delta0_of_adjacent c h12 hcomp hμΔ0 hνΔ hadj

/-- `δν` has norm four for Section-4 `ν`. -/
private lemma deltaNu_normSq_eq_four (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) {ν : Irr (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1) :
    normSq G (deltaNu c h12 ν) = 4 := by
  classical
  have h1 : normSq G (tildeNu c h12 ν) = 2 := by
    have h := tildeNu_norm c h12 ν
    simpa [hνs] using h
  have h2 : normSq G (tildeNu c h12 (lambdaTwoMul c h12 ν)) = 2 := by
    have h := tildeNu_norm c h12 (lambdaTwoMul c h12 ν)
    have hfix : conjChar c.H0 (s_normalizes_H0 c h12) (lambdaTwoMul c h12 ν).1 =
        (lambdaTwoMul c h12 ν).1 := lambdaTwoMul_fixed_by_s c h12 hνs
    simpa [hfix] using h
  have hdis := tildeNu_disjoint_lambdaTwo c h12 hSC hS4 hνs
  unfold deltaNu
  unfold normSq
  rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
  have h_nu_lam : scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 (lambdaTwoMul c h12 ν)) = 0 := by
    exact scalarProduct_eq_zero_of_disjoint
      (tildeNu_isGeneralized c h12 ν)
      (tildeNu_isGeneralized c h12 (lambdaTwoMul c h12 ν)) (disjoint_symm hdis)
  have h_lam_nu : scalarProduct G (tildeNu c h12 (lambdaTwoMul c h12 ν)) (tildeNu c h12 ν) = 0 := by
    exact scalarProduct_eq_zero_of_disjoint
      (tildeNu_isGeneralized c h12 (lambdaTwoMul c h12 ν))
      (tildeNu_isGeneralized c h12 ν) hdis
  have h1' : scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 ν) = 2 := by
    simpa [normSq] using h1
  have h2' : scalarProduct G (tildeNu c h12 (lambdaTwoMul c h12 ν))
      (tildeNu c h12 (lambdaTwoMul c h12 ν)) = 2 := by
    simpa [normSq] using h2
  rw [h1', h2', h_nu_lam, h_lam_nu]
  norm_num

/-- Distinct Section-4 `δν` are orthogonal. -/
private lemma deltaNu_orthogonal (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c)
    {ν μ : Irr (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (hνt : ν.1 (tH0 c) = ν.1 1)
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1)
    (hμt : μ.1 (tH0 c) = μ.1 1)
    (hne : ν ≠ μ) :
    scalarProduct G (deltaNu c h12 ν) (deltaNu c h12 μ) = 0 := by
  classical
  have horbitν : ν.1 ∉ orbit c.H0 c.U μ.1 := by
    intro hνμ
    have hEq_orbit : orbit c.H0 c.U μ.1 = {μ.1, (lambdaTwoMul c h12 μ).1} :=
      orbit_eq_pair c h12 hS4 μ
    rw [hEq_orbit] at hνμ
    rw [Finset.mem_insert, Finset.mem_singleton] at hνμ
    rcases hνμ with hEq | hEq
    · exact hne (Subtype.ext hEq)
    · have hν1 : ν.1 1 ≠ 0 := irreducible_char_one_ne_zero ν.2
      have hdeg : ν.1 1 = μ.1 1 := by
        simpa [lambdaTwoMul, LambdaChar] using congrFun hEq 1
      have hbad : ν.1 (tH0 c) = -ν.1 1 := by
        have hEq' : ν.1 (tH0 c) =
            ((lambdaTwo c h12).1 (tH0 c) : ℂ) * μ.1 (tH0 c) := by
          simpa [lambdaTwoMul, LambdaChar] using congrFun hEq (tH0 c)
        rw [hEq']
        rw [lambdaTwo_val_tH0_eq_neg_one c h12 hSC hS4]
        rw [hμt]
        rw [hdeg]
        ring_nf
      have hEq1 : ν.1 (tH0 c) = ν.1 1 := hνt
      have hEq2 : ν.1 (tH0 c) = -ν.1 1 := hbad
      have hzero : (2 : ℂ) * ν.1 1 = 0 := by
        have hsum : ν.1 1 + ν.1 1 = 0 := by
          have hneg1 : ν.1 1 = -ν.1 1 := by
            calc
              ν.1 1 = ν.1 (tH0 c) := hEq1.symm
              _ = -ν.1 1 := hEq2
          nth_rw 1 [hneg1]
          ring
        rw [two_mul]
        exact hsum
      exact (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hν1) hzero
  have hνs' : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ∉ orbit c.H0 c.U μ.1 := by
    simpa [hνs] using horbitν
  have h_lam_nu : (lambdaTwoMul c h12 ν).1 ∈ orbit c.H0 c.U ν.1 :=
    by
      refine Finset.mem_image.mpr ⟨lambdaTwo c h12, Finset.mem_univ _, ?_⟩
      ext x
      rfl
  have h_lam_mu : (lambdaTwoMul c h12 μ).1 ∈ orbit c.H0 c.U μ.1 :=
    by
      refine Finset.mem_image.mpr ⟨lambdaTwo c h12, Finset.mem_univ _, ?_⟩
      ext x
      rfl
  have horth := tildeNu_orthogonal c h12
    (ν₁ := ν) (μ₁ := lambdaTwoMul c h12 ν)
    (ν₂ := μ) (μ₂ := lambdaTwoMul c h12 μ) h_lam_nu h_lam_mu horbitν hνs'
  have hEq : deltaNu c h12 ν = -(tildeNu c h12 (lambdaTwoMul c h12 ν) - tildeNu c h12 ν) := by
    ext x
    simp [deltaNu]
  have hEq' : deltaNu c h12 μ = -(tildeNu c h12 (lambdaTwoMul c h12 μ) - tildeNu c h12 μ) := by
    ext x
    simp [deltaNu]
  rw [hEq, hEq']
  rw [scalarProduct_neg_left, scalarProduct_neg_right]
  simpa using horth

/-- Distinct Section-4 `ν` give distinct `δν`. -/
public lemma deltaNu_injective (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) {ν μ : Irr (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (hνt : ν.1 (tH0 c) = ν.1 1)
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1)
    (hμt : μ.1 (tH0 c) = μ.1 1)
    (hEq : deltaNu c h12 ν = deltaNu c h12 μ) : ν = μ := by
  by_contra hne
  have horth := deltaNu_orthogonal c h12 hSC hS4 hνs hνt hμs hμt hne
  have hnorm : normSq G (deltaNu c h12 ν) = 4 :=
    deltaNu_normSq_eq_four c h12 hSC hS4 hνs
  have hself : scalarProduct G (deltaNu c h12 ν) (deltaNu c h12 ν) = 0 := by
    simpa [hEq] using horth
  have hself' : scalarProduct G (deltaNu c h12 ν) (deltaNu c h12 ν) = 4 := by
    simpa [normSq] using hnorm
  have hbad : (0 : ℂ) = 4 := hself.symm.trans hself'
  norm_num at hbad

/-- In the non-fixed case every vertex of the component has its `ν̂` in the
same `N_G(S)`-orbit. -/
private lemma deltaNu_mem_orbit_of_Delta0 (c : Hyp11 G) (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {Δ0 : Set (ClassFunction G)} (hcomp : IsConnectedComponent c h12 Δ0)
    {μ : Irr (↥c.H0)}
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1)
    (hμt : μ.1 (tH0 c) = μ.1 1)
    (hμΔ0 : deltaNu c h12 μ ∈ Δ0)
    (horb : (nuHatOrbit c h12 (nuHat c h12 μ)).card = 3) :
    ∀ δ ∈ Δ0, ∃ ν : Irr (↥c.H0),
      δ ∈ Δ0 ∧ δ = deltaNu c h12 ν ∧
      conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 ∧
      ν.1 (tH0 c) = ν.1 1 ∧
      nuHat c h12 ν ∈ nuHatOrbit c h12 (nuHat c h12 μ) := by
  intro δ hδ
  have hpath : Relation.ReflTransGen (deltaAdjacent c h12) (deltaNu c h12 μ) δ :=
    hcomp.2.2.1 (deltaNu c h12 μ) δ hμΔ0 hδ
  have hrev : Relation.ReflTransGen (deltaAdjacent c h12) δ (deltaNu c h12 μ) :=
    reflTransGen_symm (fun {a b : ClassFunction G} h => deltaAdjacent_symm c h12 h) hpath
  refine Relation.ReflTransGen.head_induction_on hrev ?refl ?head
  · exact ⟨μ, hμΔ0, rfl, hμs, hμt, nuHatOrbit_self_mem c h12 (nuHat c h12 μ)⟩
  · intro x y hadj hpath' ih
    rcases ih with ⟨ν_y, hyΔ0, hEqy, hνys, hνyt, horby⟩
    have hxΔ0 : x ∈ Δ0 := by
      by_contra hnot
      exact (hcomp.2.2.2 x hnot y hyΔ0) hadj
    have hxΔ : x ∈ Delta c h12 := hcomp.2.1 hxΔ0
    rcases hxΔ with ⟨ν_x, hνxs, hνxt, hEqx⟩
    rcases exists_shared_constituent_of_adjacent c h12 hadj with ⟨χ, hχa, hχc⟩
    have hν_xB : ν_x ∈ BPrimeOf c h12 χ.1 := by
      rw [BPrimeOf]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ ν_x, hνxs, hνxt,
        by simpa [hEqx] using (mem_involved_iff x χ).1 hχa⟩
    have hχδy : scalarProduct G χ.1 (deltaNu c h12 ν_y) ≠ 0 := by
      simpa [hEqy] using (mem_involved_iff y χ).1 hχc
    have horbx : nuHat c h12 ν_x ∈ nuHatOrbit c h12 (nuHat c h12 μ) :=
      nuHat_mem_orbit_of_BPrime_of_orbit c h12 hSC hS4 horby hχδy
        hνys hνyt hνxs hνxt horb hν_xB
    exact ⟨ν_x, hxΔ0, hEqx, hνxs, hνxt, horbx⟩

/-- Three distinct vertices of the component exist in the non-fixed orbit
case, all with `ν̂` in the same `N_G(S)`-orbit. -/
private lemma exists_three_delta_of_nonfixed_orbit (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {Δ0 : Set (ClassFunction G)} (hcomp : IsConnectedComponent c h12 Δ0)
    {μ : Irr (↥c.H0)}
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1)
    (hμt : μ.1 (tH0 c) = μ.1 1)
    (hμΔ0 : deltaNu c h12 μ ∈ Δ0)
    (horb : (nuHatOrbit c h12 (nuHat c h12 μ)).card = 3) :
    ∃ ν₁ ν₂ ν₃ : Irr (↥c.H0),
      deltaNu c h12 ν₁ ∈ Δ0 ∧ deltaNu c h12 ν₂ ∈ Δ0 ∧
      deltaNu c h12 ν₃ ∈ Δ0 ∧
      deltaNu c h12 ν₁ ≠ deltaNu c h12 ν₂ ∧
      deltaNu c h12 ν₁ ≠ deltaNu c h12 ν₃ ∧
      deltaNu c h12 ν₂ ≠ deltaNu c h12 ν₃ ∧
      nuHat c h12 ν₁ ∈ nuHatOrbit c h12 (nuHat c h12 μ) ∧
      nuHat c h12 ν₂ ∈ nuHatOrbit c h12 (nuHat c h12 μ) ∧
      nuHat c h12 ν₃ ∈ nuHatOrbit c h12 (nuHat c h12 μ) ∧
      ∃ χ : Irr G,
        χ ∈ involved (deltaNu c h12 μ) ∧
        ν₁ ∈ BPrimeOf c h12 χ.1 ∧ ν₂ ∈ BPrimeOf c h12 χ.1 ∧
        ν₃ ∈ BPrimeOf c h12 χ.1 ∧
      Δ0 = ({deltaNu c h12 ν₁, deltaNu c h12 ν₂, deltaNu c h12 ν₃} : Set (ClassFunction G)) := by
  classical
  have hχnonempty : (involved (deltaNu c h12 μ)).Nonempty := by
    rw [← Finset.card_pos]
    rw [involved_deltaNu_card_eq_four c h12 hSC hS4 hμs]
    norm_num
  let χ : Irr G := Classical.choose hχnonempty
  have hχmem : χ ∈ involved (deltaNu c h12 μ) := Classical.choose_spec hχnonempty
  have hχδ : scalarProduct G χ.1 (deltaNu c h12 μ) ≠ 0 :=
    (mem_involved_iff (deltaNu c h12 μ) χ).1 hχmem
  rcases exists_three_BPrime_of_nonfixed_orbit c h12 hSC hS4 hχδ hμs hμt horb with
    ⟨ν₁, ν₂, ν₃, hν₁B, hν₂B, hν₃B, hν₁₂, hν₁₃, hν₂₃⟩
  have hδ₁ : deltaNu c h12 ν₁ ∈ Δ0 :=
    deltaNu_mem_Delta0_of_BPrime c h12 hcomp hμΔ0 hχmem hν₁B
  have hδ₂ : deltaNu c h12 ν₂ ∈ Δ0 :=
    deltaNu_mem_Delta0_of_BPrime c h12 hcomp hμΔ0 hχmem hν₂B
  have hδ₃ : deltaNu c h12 ν₃ ∈ Δ0 :=
    deltaNu_mem_Delta0_of_BPrime c h12 hcomp hμΔ0 hχmem hν₃B
  have hν₁s : conjChar c.H0 (s_normalizes_H0 c h12) ν₁.1 = ν₁.1 := by
    rw [BPrimeOf] at hν₁B
    exact (Finset.mem_filter.mp hν₁B).2.1
  have hν₁t : ν₁.1 (tH0 c) = ν₁.1 1 := by
    rw [BPrimeOf] at hν₁B
    exact (Finset.mem_filter.mp hν₁B).2.2.1
  have hν₂s : conjChar c.H0 (s_normalizes_H0 c h12) ν₂.1 = ν₂.1 := by
    rw [BPrimeOf] at hν₂B
    exact (Finset.mem_filter.mp hν₂B).2.1
  have hν₂t : ν₂.1 (tH0 c) = ν₂.1 1 := by
    rw [BPrimeOf] at hν₂B
    exact (Finset.mem_filter.mp hν₂B).2.2.1
  have hν₃s : conjChar c.H0 (s_normalizes_H0 c h12) ν₃.1 = ν₃.1 := by
    rw [BPrimeOf] at hν₃B
    exact (Finset.mem_filter.mp hν₃B).2.1
  have hν₃t : ν₃.1 (tH0 c) = ν₃.1 1 := by
    rw [BPrimeOf] at hν₃B
    exact (Finset.mem_filter.mp hν₃B).2.2.1
  have hδ₁₂ : deltaNu c h12 ν₁ ≠ deltaNu c h12 ν₂ := by
    intro hEq
    exact hν₁₂ (deltaNu_injective c h12 hSC hS4 hν₁s hν₁t hν₂s hν₂t hEq)
  have hδ₁₃ : deltaNu c h12 ν₁ ≠ deltaNu c h12 ν₃ := by
    intro hEq
    exact hν₁₃ (deltaNu_injective c h12 hSC hS4 hν₁s hν₁t hν₃s hν₃t hEq)
  have hδ₂₃ : deltaNu c h12 ν₂ ≠ deltaNu c h12 ν₃ := by
    intro hEq
    exact hν₂₃ (deltaNu_injective c h12 hSC hS4 hν₂s hν₂t hν₃s hν₃t hEq)
  have horb₁ : nuHat c h12 ν₁ ∈ nuHatOrbit c h12 (nuHat c h12 μ) :=
    nuHat_mem_orbit_of_BPrime c h12 hSC hS4 hχδ hμs hμt hν₁s hν₁t horb hν₁B
  have horb₂ : nuHat c h12 ν₂ ∈ nuHatOrbit c h12 (nuHat c h12 μ) :=
    nuHat_mem_orbit_of_BPrime c h12 hSC hS4 hχδ hμs hμt hν₂s hν₂t horb hν₂B
  have horb₃ : nuHat c h12 ν₃ ∈ nuHatOrbit c h12 (nuHat c h12 μ) :=
    nuHat_mem_orbit_of_BPrime c h12 hSC hS4 hχδ hμs hμt hν₃s hν₃t horb hν₃B
  have hinj := nuHat_injective_on_BPrime_of_nonfixed c h12 hSC hS4 hχδ hμs hμt horb
  have hβ₁₂ : nuHat c h12 ν₁ ≠ nuHat c h12 ν₂ := by
    intro hEq
    exact hδ₁₂ (by rw [hinj hν₁B hν₂B hEq])
  have hβ₁₃ : nuHat c h12 ν₁ ≠ nuHat c h12 ν₃ := by
    intro hEq
    exact hδ₁₃ (by rw [hinj hν₁B hν₃B hEq])
  have hβ₂₃ : nuHat c h12 ν₂ ≠ nuHat c h12 ν₃ := by
    intro hEq
    exact hδ₂₃ (by rw [hinj hν₂B hν₃B hEq])
  let β₁ : Irr (↥c.B) := nuHat c h12 ν₁
  let β₂ : Irr (↥c.B) := nuHat c h12 ν₂
  let β₃ : Irr (↥c.B) := nuHat c h12 ν₃
  have hβ₁not : β₁ ∉ ({β₂, β₃} : Finset (Irr (↥c.B))) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    intro hEq
    rcases hEq with hEq | hEq
    · exact hβ₁₂ (by simpa [β₁, β₂] using hEq)
    · exact hβ₁₃ (by simpa [β₁, β₃] using hEq)
  have hβ₂not : β₂ ∉ ({β₃} : Finset (Irr (↥c.B))) := by
    rw [Finset.mem_singleton]
    intro hEq
    exact hβ₂₃ (by simpa [β₂, β₃] using hEq)
  have hβset_card : ({β₁, β₂, β₃} : Finset (Irr (↥c.B))).card = 3 := by
    rw [Finset.card_insert_of_notMem hβ₁not,
      Finset.card_insert_of_notMem hβ₂not, Finset.card_singleton]
  have hsubset : ({β₁, β₂, β₃} : Finset (Irr (↥c.B))) ⊆
      nuHatOrbit c h12 (nuHat c h12 μ) := by
    intro β hβ
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hβ
    rcases hβ with rfl | rfl | rfl
    · simpa [β₁] using horb₁
    · simpa [β₂] using horb₂
    · simpa [β₃] using horb₃
  have hEqOrbit : ({β₁, β₂, β₃} : Finset (Irr (↥c.B))) =
      nuHatOrbit c h12 (nuHat c h12 μ) :=
    Finset.eq_of_subset_of_card_le hsubset (by rw [horb, hβset_card])
  have hsubset_vertices : Δ0 ⊆
      ({deltaNu c h12 ν₁, deltaNu c h12 ν₂, deltaNu c h12 ν₃} : Set (ClassFunction G)) := by
    intro δ hδ
    rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases deltaNu_mem_orbit_of_Delta0 c h12 hSC hS4 hcomp hμs hμt hμΔ0 horb δ hδ with
      ⟨ν, _, hEqδ, hνs, hνt, hνorbit⟩
    rw [← hEqOrbit] at hνorbit
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hνorbit
    have hν₁s : conjChar c.H0 (s_normalizes_H0 c h12) ν₁.1 = ν₁.1 := by
      rw [BPrimeOf] at hν₁B
      exact (Finset.mem_filter.mp hν₁B).2.1
    have hν₁t : ν₁.1 (tH0 c) = ν₁.1 1 := by
      rw [BPrimeOf] at hν₁B
      exact (Finset.mem_filter.mp hν₁B).2.2.1
    have hν₂s : conjChar c.H0 (s_normalizes_H0 c h12) ν₂.1 = ν₂.1 := by
      rw [BPrimeOf] at hν₂B
      exact (Finset.mem_filter.mp hν₂B).2.1
    have hν₂t : ν₂.1 (tH0 c) = ν₂.1 1 := by
      rw [BPrimeOf] at hν₂B
      exact (Finset.mem_filter.mp hν₂B).2.2.1
    have hν₃s : conjChar c.H0 (s_normalizes_H0 c h12) ν₃.1 = ν₃.1 := by
      rw [BPrimeOf] at hν₃B
      exact (Finset.mem_filter.mp hν₃B).2.1
    have hν₃t : ν₃.1 (tH0 c) = ν₃.1 1 := by
      rw [BPrimeOf] at hν₃B
      exact (Finset.mem_filter.mp hν₃B).2.2.1
    rcases hνorbit with hEqβ₁ | hEqβ₂ | hEqβ₃
    · left
      have hνEq : ν = ν₁ :=
        nuHat_injective_on_Delta c h12 hSC hS4 hνs hνt hν₁s hν₁t
          (by simpa [β₁] using hEqβ₁)
      rw [hEqδ, hνEq]
    · right
      left
      have hνEq : ν = ν₂ :=
        nuHat_injective_on_Delta c h12 hSC hS4 hνs hνt hν₂s hν₂t
          (by simpa [β₂] using hEqβ₂)
      rw [hEqδ, hνEq]
    · right
      right
      have hνEq : ν = ν₃ :=
        nuHat_injective_on_Delta c h12 hSC hS4 hνs hνt hν₃s hν₃t
          (by simpa [β₃] using hEqβ₃)
      rw [hEqδ, hνEq]
  have hsuperset_vertices :
      ({deltaNu c h12 ν₁, deltaNu c h12 ν₂, deltaNu c h12 ν₃} : Set (ClassFunction G)) ⊆ Δ0 := by
    intro δ hδ
    rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hδ
    rcases hδ with rfl | rfl | rfl
    · exact hδ₁
    · exact hδ₂
    · exact hδ₃
  exact ⟨ν₁, ν₂, ν₃, hδ₁, hδ₂, hδ₃, hδ₁₂, hδ₁₃, hδ₂₃,
    horb₁, horb₂, horb₃, χ, hχmem, hν₁B, hν₂B, hν₃B,
    Set.Subset.antisymm hsubset_vertices hsuperset_vertices⟩

/-- In the non-fixed orbit case the component is exactly the three deltas
built from the orbit. -/
private lemma component_eq_three_of_nonfixed_orbit (c : Hyp11 G)
    (h12 : Hyp12 c) (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {Δ0 : Set (ClassFunction G)} (hcomp : IsConnectedComponent c h12 Δ0)
    {μ : Irr (↥c.H0)}
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1)
    (hμt : μ.1 (tH0 c) = μ.1 1)
    (hμΔ0 : deltaNu c h12 μ ∈ Δ0)
    (horb : (nuHatOrbit c h12 (nuHat c h12 μ)).card = 3) :
    ∃ ν₁ ν₂ ν₃ : Irr (↥c.H0),
      deltaNu c h12 ν₁ ∈ Δ0 ∧ deltaNu c h12 ν₂ ∈ Δ0 ∧
      deltaNu c h12 ν₃ ∈ Δ0 ∧
      deltaNu c h12 ν₁ ≠ deltaNu c h12 ν₂ ∧
      deltaNu c h12 ν₁ ≠ deltaNu c h12 ν₃ ∧
      deltaNu c h12 ν₂ ≠ deltaNu c h12 ν₃ ∧
      Δ0 = ({deltaNu c h12 ν₁, deltaNu c h12 ν₂, deltaNu c h12 ν₃} : Set (ClassFunction G)) := by
  classical
  rcases exists_three_delta_of_nonfixed_orbit c h12 hSC hS4 hcomp hμs hμt hμΔ0 horb with
    ⟨ν₁, ν₂, ν₃, hδ₁, hδ₂, hδ₃, hδ₁₂, hδ₁₃, hδ₂₃,
      horb₁, horb₂, horb₃, χ, hχmem, hν₁B, hν₂B, hν₃B, hΔ0eq⟩
  exact ⟨ν₁, ν₂, ν₃, hδ₁, hδ₂, hδ₃, hδ₁₂, hδ₁₃, hδ₂₃, hΔ0eq⟩

/-- The concrete signed four-decomposition of `δν`, indexed by `Fin 4`. -/
public lemma signed_four_decomp_fin (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) {ν : Irr (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1) :
    ∃ (a : Fin 4 → ClassFunction G) (s : Fin 4 → ℤ),
      (∀ i, IsIrreducibleCharacter (a i)) ∧ Function.Injective a ∧
      (∀ i, s i = 1 ∨ s i = -1) ∧
      deltaNu c h12 ν = ∑ i, (s i : ℂ) • a i := by
  classical
  rcases deltaNu_signed_four_decomp c h12 hSC hS4 hνs with
    ⟨a₁, a₂, a₃, a₄, ha₁, ha₂, ha₃, ha₄,
      h₁₂, h₁₃, h₁₄, h₂₃, h₂₄, h₃₄,
      s₁, s₂, s₃, s₄, hs₁, hs₂, hs₃, hs₄, hδ⟩
  let a : Fin 4 → ClassFunction G := ![a₁, a₂, a₃, a₄]
  let s : Fin 4 → ℤ := ![s₁, s₂, s₃, s₄]
  refine ⟨a, s, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [a] <;> assumption
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [a, h₁₂, h₁₂.symm, h₁₃, h₁₃.symm,
      h₁₄, h₁₄.symm, h₂₃, h₂₃.symm, h₂₄, h₂₄.symm, h₃₄, h₃₄.symm] at hij ⊢
  · intro i
    fin_cases i <;> simp [s] <;> assumption
  · rw [Fin.sum_univ_four]
    simpa [a, s] using hδ

/-- The constituent set of a signed four-sum over `Fin 4`. -/
private lemma involved_eq_of_signed_four_fin {δ : ClassFunction G}
    {a : Fin 4 → ClassFunction G} (ha : ∀ i, IsIrreducibleCharacter (a i))
    (hainj : Function.Injective a) {s : Fin 4 → ℤ}
    (hs : ∀ i, s i = 1 ∨ s i = -1)
    (hδ : δ = ∑ i, (s i : ℂ) • a i) :
    involved δ = Finset.univ.image (fun i : Fin 4 => ⟨a i, ha i⟩) := by
  classical
  ext φ
  rw [mem_involved_iff]
  constructor
  · intro hne
    rw [Finset.mem_image]
    by_contra hnot
    have hφne : ∀ i, φ.1 ≠ a i := by
      intro i hi
      exact hnot ⟨i, Finset.mem_univ i, (Subtype.ext hi).symm⟩
    have hsum0 : (∑ i, scalarProduct G φ.1 ((s i : ℂ) • a i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [scalarProduct_smul_right]
      rw [scalarProduct_irr_ite φ.2 (ha i)]
      simp [hφne i]
    rw [hδ] at hne
    rw [scalarProduct_sum_right] at hne
    exact hne hsum0
  · intro hφ
    rw [Finset.mem_image] at hφ
    rcases hφ with ⟨i, hi, rfl⟩
    rw [hδ]
    rw [scalarProduct_sum_right]
    have hsum : (∑ j, scalarProduct G (a i) ((s j : ℂ) • a j)) = (s i : ℂ) := by
      rw [Finset.sum_eq_single i
        (by
          intro j hj hji
          rw [scalarProduct_smul_right]
          rw [scalarProduct_irr_ite (ha i) (ha j)]
          have hne : a i ≠ a j := by
            intro hEq
            exact hji (hainj hEq).symm
          simp [hne])
        (by
          intro hk
          exact False.elim (hk (Finset.mem_univ i)))]
      rw [scalarProduct_smul_right]
      rw [scalarProduct_irr_ite (ha i) (ha i)]
      simp
    rw [hsum]
    rcases hs i with h | h <;> norm_num [h]


/-- Matching indices for the two common constituents of two signed
four-sums. -/
private lemma exists_indices_of_common_two
    {δ ε : ClassFunction G}
    {a : Fin 4 → ClassFunction G} (ha : ∀ i, IsIrreducibleCharacter (a i))
    (hainj : Function.Injective a) {s : Fin 4 → ℤ}
    (hs : ∀ i, s i = 1 ∨ s i = -1)
    (hδ : δ = ∑ i, (s i : ℂ) • a i)
    {b : Fin 4 → ClassFunction G} (hb : ∀ i, IsIrreducibleCharacter (b i))
    (hbinj : Function.Injective b) {t : Fin 4 → ℤ}
    (ht : ∀ i, t i = 1 ∨ t i = -1)
    (hε : ε = ∑ i, (t i : ℂ) • b i)
    {x y : Irr G} (hinter : involved δ ∩ involved ε = ({x, y} : Finset (Irr G)))
    (hxy : x ≠ y) :
    ∃ i₁ i₂ j₁ j₂ : Fin 4,
      a i₁ = x.1 ∧ b j₁ = x.1 ∧ a i₂ = y.1 ∧ b j₂ = y.1 ∧
      i₁ ≠ i₂ ∧ j₁ ≠ j₂ ∧
      ∀ i, i ≠ i₁ → i ≠ i₂ → ∀ j, b j ≠ a i := by
  classical
  have hδeq : involved δ = Finset.univ.image (fun i : Fin 4 => ⟨a i, ha i⟩) :=
    involved_eq_of_signed_four_fin ha hainj hs hδ
  have hεeq : involved ε = Finset.univ.image (fun i : Fin 4 => ⟨b i, hb i⟩) :=
    involved_eq_of_signed_four_fin hb hbinj ht hε
  have hx : x ∈ involved δ ∩ involved ε := by
    rw [hinter]
    simp
  have hy : y ∈ involved δ ∩ involved ε := by
    rw [hinter]
    simp
  rcases Finset.mem_image.mp (by
    have hxδ : x ∈ involved δ := (Finset.mem_inter.mp hx).1
    rwa [hδeq] at hxδ) with ⟨i₁, hi₁, hEq₁⟩
  rcases Finset.mem_image.mp (by
    have hxε : x ∈ involved ε := (Finset.mem_inter.mp hx).2
    rwa [hεeq] at hxε) with ⟨j₁, hj₁, hEq₂⟩
  rcases Finset.mem_image.mp (by
    have hyδ : y ∈ involved δ := (Finset.mem_inter.mp hy).1
    rwa [hδeq] at hyδ) with ⟨i₂, hi₂, hEq₃⟩
  rcases Finset.mem_image.mp (by
    have hyε : y ∈ involved ε := (Finset.mem_inter.mp hy).2
    rwa [hεeq] at hyε) with ⟨j₂, hj₂, hEq₄⟩
  have ha₁ : a i₁ = x.1 := congrArg Subtype.val hEq₁
  have hb₁ : b j₁ = x.1 := congrArg Subtype.val hEq₂
  have ha₂ : a i₂ = y.1 := congrArg Subtype.val hEq₃
  have hb₂ : b j₂ = y.1 := congrArg Subtype.val hEq₄
  have hi₁₂ : i₁ ≠ i₂ := by
    intro hEq
    exact hxy (Subtype.ext (by simpa [ha₁, ha₂] using congrArg (fun i => a i) hEq))
  have hj₁₂ : j₁ ≠ j₂ := by
    intro hEq
    exact hxy (Subtype.ext (by simpa [hb₁, hb₂] using congrArg (fun j => b j) hEq))
  have hother : ∀ i, i ≠ i₁ → i ≠ i₂ → ∀ j, b j ≠ a i := by
    intro i hi₁ hi₂ j hj
    have hmem : (⟨a i, ha i⟩ : Irr G) ∈ involved δ ∩ involved ε := by
      rw [Finset.mem_inter]
      constructor
      · rw [hδeq]
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      · rw [hεeq]
        exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, Subtype.ext hj⟩
    rw [hinter] at hmem
    rw [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hEq | hEq
    · have hEq' : a i = x.1 := congrArg Subtype.val hEq
      exact hi₁ (hainj (hEq'.trans ha₁.symm))
    · have hEq' : a i = y.1 := congrArg Subtype.val hEq
      exact hi₂ (hainj (hEq'.trans ha₂.symm))
  exact ⟨i₁, i₂, j₁, j₂, ha₁, hb₁, ha₂, hb₂, hi₁₂, hj₁₂, hother⟩

/-- A two-element intersection containing two distinct points is exactly
their pair. -/
private lemma inter_eq_pair_of_card_two {ι : Type*} [DecidableEq ι]
    {A B : Finset ι} {x y : ι} (hinter : (A ∩ B).card = 2) (hxy : x ≠ y)
    (hx : x ∈ A ∩ B) (hy : y ∈ A ∩ B) :
    A ∩ B = ({x, y} : Finset ι) := by
  have hsub : ({x, y} : Finset ι) ⊆ A ∩ B := by
    intro z hz
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have hcard : ({x, y} : Finset ι).card = 2 := by
    rw [Finset.card_insert_of_notMem (by
      rw [Finset.mem_singleton]
      exact hxy), Finset.card_singleton]
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hinter, hcard])).symm

/-- Three pairwise-orthogonal signed vectors cannot share two common
coordinates with opposite sign relations in each pair. -/
private lemma signs_three_pairwise_contradiction
    (r s : Fin 2 → ℤ) (hr : ∀ i, r i = 1 ∨ r i = -1)
    (hs : ∀ i, s i = 1 ∨ s i = -1)
    (h12 : r 0 + r 1 = 0) (h13 : s 0 + s 1 = 0)
    (h23 : (∑ i, r i * s i) = 0) : False := by
  rw [Fin.sum_univ_two] at h23
  rcases hr 0 with r0 | r0 <;> rcases hr 1 with r1 | r1 <;>
    rcases hs 0 with s0 | s0 <;> rcases hs 1 with s1 | s1 <;>
      simp [r0, r1, s0, s1] at h12 h13 h23 <;> omega
/-- Three pairwise-orthogonal signed four-sums with pairwise two-element
common sets share exactly one constituent. -/
private lemma triple_inter_card_eq_one_of_pairwise_orthogonal
    {δ₁ δ₂ δ₃ : ClassFunction G}
    {a₁ : Fin 4 → ClassFunction G} (ha₁ : ∀ i, IsIrreducibleCharacter (a₁ i))
    (hainj₁ : Function.Injective a₁) {s₁ : Fin 4 → ℤ}
    (hs₁ : ∀ i, s₁ i = 1 ∨ s₁ i = -1)
    (hδ₁ : δ₁ = ∑ i, (s₁ i : ℂ) • a₁ i)
    {a₂ : Fin 4 → ClassFunction G} (ha₂ : ∀ i, IsIrreducibleCharacter (a₂ i))
    (hainj₂ : Function.Injective a₂) {s₂ : Fin 4 → ℤ}
    (hs₂ : ∀ i, s₂ i = 1 ∨ s₂ i = -1)
    (hδ₂ : δ₂ = ∑ i, (s₂ i : ℂ) • a₂ i)
    {a₃ : Fin 4 → ClassFunction G} (ha₃ : ∀ i, IsIrreducibleCharacter (a₃ i))
    (hainj₃ : Function.Injective a₃) {s₃ : Fin 4 → ℤ}
    (hs₃ : ∀ i, s₃ i = 1 ∨ s₃ i = -1)
    (hδ₃ : δ₃ = ∑ i, (s₃ i : ℂ) • a₃ i)
    (horth12 : scalarProduct G δ₁ δ₂ = 0)
    (horth13 : scalarProduct G δ₁ δ₃ = 0)
    (horth23 : scalarProduct G δ₂ δ₃ = 0)
    (hinter12 : (involved δ₁ ∩ involved δ₂).card = 2)
    (hinter13 : (involved δ₁ ∩ involved δ₃).card = 2)
    (hinter23 : (involved δ₂ ∩ involved δ₃).card = 2)
    {χ : Irr G}
    (hχ : χ ∈ ((involved δ₁ ∩ involved δ₂) ∩ involved δ₃)) :
    ((involved δ₁ ∩ involved δ₂) ∩ involved δ₃).card = 1 := by
  classical
  let T : Finset (Irr G) := (involved δ₁ ∩ involved δ₂) ∩ involved δ₃
  have hTsub12 : T ⊆ involved δ₁ ∩ involved δ₂ := by
    intro x hx
    exact (Finset.mem_inter.mp hx).1
  have hχT : χ ∈ T := hχ
  have hle : T.card ≤ 2 := by
    have hle' := Finset.card_le_card hTsub12
    rwa [hinter12] at hle'
  have hge : 1 ≤ T.card := Finset.card_pos.mpr ⟨χ, hχT⟩
  by_contra hnot
  have hTcard : T.card = 2 := by
    interval_cases T.card <;> omega
  rcases Finset.card_eq_two.mp hTcard with ⟨x, y, hxy, hTset⟩
  have hxT : x ∈ T := by rw [hTset]; simp
  have hyT : y ∈ T := by rw [hTset]; simp
  have hx12 : x ∈ involved δ₁ ∩ involved δ₂ := hTsub12 hxT
  have hy12 : y ∈ involved δ₁ ∩ involved δ₂ := hTsub12 hyT
  have hx3 : x ∈ involved δ₃ := (Finset.mem_inter.mp hxT).2
  have hy3 : y ∈ involved δ₃ := (Finset.mem_inter.mp hyT).2
  have hx13 : x ∈ involved δ₁ ∩ involved δ₃ := by
    rw [Finset.mem_inter]
    exact ⟨(Finset.mem_inter.mp hx12).1, hx3⟩
  have hy13 : y ∈ involved δ₁ ∩ involved δ₃ := by
    rw [Finset.mem_inter]
    exact ⟨(Finset.mem_inter.mp hy12).1, hy3⟩
  have hx23 : x ∈ involved δ₂ ∩ involved δ₃ := by
    rw [Finset.mem_inter]
    exact ⟨(Finset.mem_inter.mp hx12).2, hx3⟩
  have hy23 : y ∈ involved δ₂ ∩ involved δ₃ := by
    rw [Finset.mem_inter]
    exact ⟨(Finset.mem_inter.mp hy12).2, hy3⟩
  have hinter12eq : involved δ₁ ∩ involved δ₂ = ({x, y} : Finset (Irr G)) :=
    inter_eq_pair_of_card_two hinter12 hxy hx12 hy12
  have hinter13eq : involved δ₁ ∩ involved δ₃ = ({x, y} : Finset (Irr G)) :=
    inter_eq_pair_of_card_two hinter13 hxy hx13 hy13
  have hinter23eq : involved δ₂ ∩ involved δ₃ = ({x, y} : Finset (Irr G)) :=
    inter_eq_pair_of_card_two hinter23 hxy hx23 hy23
  rcases exists_indices_of_common_two (δ := δ₁) (ε := δ₂) (a := a₁)
    ha₁ hainj₁ (s := s₁) hs₁ hδ₁ (b := a₂) ha₂ hainj₂ (t := s₂) hs₂ hδ₂
    hinter12eq hxy with ⟨i₁, i₂, j₁, j₂, ha₁i, ha₂i, ha₁y, ha₂y, hi₁₂, hj₁₂, hother12⟩
  rcases exists_indices_of_common_two (δ := δ₁) (ε := δ₃) (a := a₁)
    ha₁ hainj₁ (s := s₁) hs₁ hδ₁ (b := a₃) ha₃ hainj₃ (t := s₃) hs₃ hδ₃
    hinter13eq hxy with ⟨k₁, k₂, l₁, l₂, ha₁k, ha₃l, ha₁l, ha₃m, hk₁₂, hl₁₂, hother13⟩
  rcases exists_indices_of_common_two (δ := δ₂) (ε := δ₃) (a := a₂)
    ha₂ hainj₂ (s := s₂) hs₂ hδ₂ (b := a₃) ha₃ hainj₃ (t := s₃) hs₃ hδ₃
    hinter23eq hxy with ⟨m₁, m₂, n₁, n₂, ha₂m, ha₃n, ha₂n, ha₃o, hm₁₂, hn₁₂, hother23⟩
  have hk₁i : k₁ = i₁ := hainj₁ (ha₁k.trans ha₁i.symm)
  have hk₂i : k₂ = i₂ := hainj₁ (ha₁l.trans ha₁y.symm)
  have hm₁j : m₁ = j₁ := hainj₂ (ha₂m.trans ha₂i.symm)
  have hm₂j : m₂ = j₂ := hainj₂ (ha₂n.trans ha₂y.symm)
  have hn₁l : n₁ = l₁ := hainj₃ (ha₃n.trans ha₃l.symm)
  have hn₂l : n₂ = l₂ := hainj₃ (ha₃o.trans ha₃m.symm)
  have hsp12 := scalarProduct_two_common_of_indices
    ha₁ hainj₁ hs₁ hδ₁ ha₂ hainj₂ hs₂ hδ₂
    (i₁ := i₁) (i₂ := i₂) (j₁ := j₁) (j₂ := j₂) (x := x) (y := y)
    ha₁i ha₂i ha₁y ha₂y hi₁₂ hj₁₂ hother12
  have hEq12 : (s₁ i₁ * s₂ j₁ + s₁ i₂ * s₂ j₂ : ℤ) = 0 := by
    have hℂ : (((s₁ i₁ * s₂ j₁ + s₁ i₂ * s₂ j₂ : ℤ) : ℂ) = 0) :=
      hsp12.symm.trans horth12
    exact_mod_cast hℂ
  have hsp13 := scalarProduct_two_common_of_indices
    ha₁ hainj₁ hs₁ hδ₁ ha₃ hainj₃ hs₃ hδ₃
    (i₁ := k₁) (i₂ := k₂) (j₁ := l₁) (j₂ := l₂) (x := x) (y := y)
    ha₁k ha₃l ha₁l ha₃m hk₁₂ hl₁₂ hother13
  have hsp13' : scalarProduct G δ₁ δ₃ =
      (((s₁ i₁ * s₃ l₁ + s₁ i₂ * s₃ l₂ : ℤ) : ℂ)) := by
    simpa [hk₁i, hk₂i] using hsp13
  have hEq13 : (s₁ i₁ * s₃ l₁ + s₁ i₂ * s₃ l₂ : ℤ) = 0 := by
    have hℂ : (((s₁ i₁ * s₃ l₁ + s₁ i₂ * s₃ l₂ : ℤ) : ℂ) = 0) :=
      hsp13'.symm.trans horth13
    exact_mod_cast hℂ
  have hsp23 := scalarProduct_two_common_of_indices
    ha₂ hainj₂ hs₂ hδ₂ ha₃ hainj₃ hs₃ hδ₃
    (i₁ := m₁) (i₂ := m₂) (j₁ := n₁) (j₂ := n₂) (x := x) (y := y)
    ha₂m ha₃n ha₂n ha₃o hm₁₂ hn₁₂ hother23
  have hsp23' : scalarProduct G δ₂ δ₃ =
      (((s₂ j₁ * s₃ l₁ + s₂ j₂ * s₃ l₂ : ℤ) : ℂ)) := by
    simpa [hm₁j, hm₂j, hn₁l, hn₂l] using hsp23
  have hEq23 : (s₂ j₁ * s₃ l₁ + s₂ j₂ * s₃ l₂ : ℤ) = 0 := by
    have hℂ : (((s₂ j₁ * s₃ l₁ + s₂ j₂ * s₃ l₂ : ℤ) : ℂ) = 0) :=
      hsp23'.symm.trans horth23
    exact_mod_cast hℂ
  let r : Fin 2 → ℤ := ![s₁ i₁ * s₂ j₁, s₁ i₂ * s₂ j₂]
  let s : Fin 2 → ℤ := ![s₁ i₁ * s₃ l₁, s₁ i₂ * s₃ l₂]
  have hr : ∀ i, r i = 1 ∨ r i = -1 := by
    intro i
    fin_cases i
    · rcases hs₁ i₁ with h | h <;> rcases hs₂ j₁ with h' | h' <;> simp [r, h, h']
    · rcases hs₁ i₂ with h | h <;> rcases hs₂ j₂ with h' | h' <;> simp [r, h, h']
  have hs : ∀ i, s i = 1 ∨ s i = -1 := by
    intro i
    fin_cases i
    · rcases hs₁ i₁ with h | h <;> rcases hs₃ l₁ with h' | h' <;> simp [s, h, h']
    · rcases hs₁ i₂ with h | h <;> rcases hs₃ l₂ with h' | h' <;> simp [s, h, h']
  have h12eq : r 0 + r 1 = 0 := by simpa [r] using hEq12
  have h13eq : s 0 + s 1 = 0 := by simpa [s] using hEq13
  have hr0s0 : r 0 * s 0 = s₂ j₁ * s₃ l₁ := by
    rcases hs₁ i₁ with h | h <;> simp [r, s, h]
  have hr1s1 : r 1 * s 1 = s₂ j₂ * s₃ l₂ := by
    rcases hs₁ i₂ with h | h <;> simp [r, s, h]
  have h23eq : (∑ i, r i * s i) = 0 := by
    rw [Fin.sum_univ_two]
    rw [hr0s0, hr1s1]
    exact hEq23
  exact False.elim (signs_three_pairwise_contradiction r s hr hs h12eq h13eq h23eq)


/-- The `N_G(S)`-orbit of a character of `B` has size one or three, encoded
for the decision procedure. -/
private theorem standard_sign_perm_bool :
    ∀ w₂ w₃ : Fin 4 → Bool,
      (∑ i, (if w₂ i then (1 : ℤ) else -1)) = 0 →
      (∑ i, (if w₃ i then (1 : ℤ) else -1)) = 0 →
      (∑ i, (if w₂ i then (1 : ℤ) else -1) * (if w₃ i then (1 : ℤ) else -1)) = 0 →
      ∃ σ : Equiv.Perm (Fin 4),
        (∀ i, (if w₂ (σ i) then (1 : ℤ) else -1) = (if i = 1 ∨ i = 3 then (-1 : ℤ) else 1)) ∧
        (∀ i, (if w₃ (σ i) then (1 : ℤ) else -1) = (if i = 2 ∨ i = 3 then (-1 : ℤ) else 1)) := by
  decide

/-- Two sign vectors with zero total sum and zero dot product are the two
displayed patterns up to a permutation of the coordinates. -/
private lemma standard_sign_perm (w₂ w₃ : Fin 4 → ℤ)
    (hw₂ : ∀ i, w₂ i = 1 ∨ w₂ i = -1)
    (hw₃ : ∀ i, w₃ i = 1 ∨ w₃ i = -1)
    (h₂ : ∑ i, w₂ i = 0) (h₃ : ∑ i, w₃ i = 0)
    (h₂₃ : ∑ i, w₂ i * w₃ i = 0) :
    ∃ σ : Equiv.Perm (Fin 4),
      (∀ i, w₂ (σ i) = if i = 1 ∨ i = 3 then (-1 : ℤ) else 1) ∧
      (∀ i, w₃ (σ i) = if i = 2 ∨ i = 3 then (-1 : ℤ) else 1) := by
  classical
  let b₂ : Fin 4 → Bool := fun i => w₂ i = 1
  let b₃ : Fin 4 → Bool := fun i => w₃ i = 1
  have hb₂eq : ∀ i, (if b₂ i then (1 : ℤ) else -1) = w₂ i := by
    intro i
    rcases hw₂ i with h | h <;> simp [b₂, h]
  have hb₃eq : ∀ i, (if b₃ i then (1 : ℤ) else -1) = w₃ i := by
    intro i
    rcases hw₃ i with h | h <;> simp [b₃, h]
  have h₂b : (∑ i, (if b₂ i then (1 : ℤ) else -1)) = 0 := by
    simpa [hb₂eq] using h₂
  have h₃b : (∑ i, (if b₃ i then (1 : ℤ) else -1)) = 0 := by
    simpa [hb₃eq] using h₃
  have h₂₃b : (∑ i, (if b₂ i then (1 : ℤ) else -1) * (if b₃ i then (1 : ℤ) else -1)) = 0 := by
    simpa [hb₂eq, hb₃eq] using h₂₃
  rcases standard_sign_perm_bool b₂ b₃ h₂b h₃b h₂₃b with ⟨σ, hσ₂, hσ₃⟩
  refine ⟨σ, ?_, ?_⟩
  · intro i
    rcases hw₂ (σ i) with h | h
    · rw [h]
      simpa [b₂, h] using hσ₂ i
    · rw [h]
      simpa [b₂, h] using hσ₂ i
  · intro i
    rcases hw₃ (σ i) with h | h
    · rw [h]
      simpa [b₃, h] using hσ₃ i
    · rw [h]
      simpa [b₃, h] using hσ₃ i

/-- Reindexing a signed sum by a permutation. -/
private lemma sum_smul_perm {χ : Fin 4 → ClassFunction G} (σ : Equiv.Perm (Fin 4))
    {u w : Fin 4 → ℤ} (huw : ∀ j, u j = w (σ.symm j)) :
    (∑ i, (u i : ℂ) • χ i) = ∑ j, (w j : ℂ) • χ (σ j) := by
  calc
    (∑ i, (u i : ℂ) • χ i) = ∑ j, (u (σ j) : ℂ) • χ (σ j) := by
      have h1 := Equiv.sum_comp σ.symm (fun i => (u (σ i) : ℂ) • χ (σ i))
      simpa [Equiv.apply_symm_apply] using h1
    _ = ∑ j, (w j : ℂ) • χ (σ j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [huw (σ j)]
      simp

/-- A signed irreducible character is a plus-minus irreducible. -/
private lemma pmIrr_sign_smul {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    {t : ℤ} (ht : t = 1 ∨ t = -1) : IsPMIrr G ((t : ℂ) • χ) := by
  rcases ht with h | h
  · left
    simpa [h] using hχ
  · right
    rw [h]
    simpa using hχ

/-- The product of two signs is a sign. -/
private lemma mul_sign_one_or_neg_one {a b : ℤ} (ha : a = 1 ∨ a = -1)
    (hb : b = 1 ∨ b = -1) : a * b = 1 ∨ a * b = -1 := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]

/-- Swapping the second and third terms of a four-term signed sum. -/
private lemma four_sum_swap_mid {δ : ClassFunction G} {p q r s : Irr G}
    (u : Fin 4 → ℤ)
    (hδ : δ = (u 0 : ℂ) • p.1 + (u 1 : ℂ) • q.1 +
      (u 2 : ℂ) • r.1 + (u 3 : ℂ) • s.1) :
    δ = (u 0 : ℂ) • p.1 + (u 2 : ℂ) • r.1 +
      (u 1 : ℂ) • q.1 + (u 3 : ℂ) • s.1 := by
  rw [hδ]
  ext x
  simp
  ring

/-- Reindexing a signed four-sum whose constituent set is exactly the four
named distinct points `x, y, u, v`. -/
private lemma reindex_signed_four_by_points {δ : ClassFunction G}
    {a : Fin 4 → ClassFunction G} (ha : ∀ i, IsIrreducibleCharacter (a i))
    (hainj : Function.Injective a) {s : Fin 4 → ℤ}
    (hs : ∀ i, s i = 1 ∨ s i = -1)
    (hδ : δ = ∑ i, (s i : ℂ) • a i)
    {x y u v : Irr G}
    (hx : x ∈ involved δ) (hy : y ∈ involved δ)
    (hu : u ∈ involved δ) (hv : v ∈ involved δ)
    (hxy : x ≠ y) (hxu : x ≠ u) (hxv : x ≠ v)
    (hyu : y ≠ u) (hyv : y ≠ v) (huv : u ≠ v) :
    ∃ t : Fin 4 → ℤ,
      (∀ i, t i = 1 ∨ t i = -1) ∧
      δ = (t 0 : ℂ) • x.1 + (t 1 : ℂ) • y.1 +
          (t 2 : ℂ) • u.1 + (t 3 : ℂ) • v.1 := by
  classical
  have hδeq : involved δ = Finset.univ.image (fun i : Fin 4 => ⟨a i, ha i⟩) :=
    involved_eq_of_signed_four_fin ha hainj hs hδ
  rcases (by simpa [hδeq] using hx) with ⟨ix, hxeq⟩
  rcases (by simpa [hδeq] using hy) with ⟨iy, hyeq⟩
  rcases (by simpa [hδeq] using hu) with ⟨iu, hueq⟩
  rcases (by simpa [hδeq] using hv) with ⟨iv, hveq⟩
  have hxval : a ix = x.1 := congrArg Subtype.val hxeq
  have hyval : a iy = y.1 := congrArg Subtype.val hyeq
  have huval : a iu = u.1 := congrArg Subtype.val hueq
  have hvval : a iv = v.1 := congrArg Subtype.val hveq
  have hixiy : ix ≠ iy := by
    intro hEq
    exact hxy (Subtype.ext (hxval.symm.trans ((congrArg (fun i => a i) hEq).trans hyval)))
  have hixiu : ix ≠ iu := by
    intro hEq
    exact hxu (Subtype.ext (hxval.symm.trans ((congrArg (fun i => a i) hEq).trans huval)))
  have hixiv : ix ≠ iv := by
    intro hEq
    exact hxv (Subtype.ext (hxval.symm.trans ((congrArg (fun i => a i) hEq).trans hvval)))
  have hiyiu : iy ≠ iu := by
    intro hEq
    exact hyu (Subtype.ext (hyval.symm.trans ((congrArg (fun i => a i) hEq).trans huval)))
  have hiyiv : iy ≠ iv := by
    intro hEq
    exact hyv (Subtype.ext (hyval.symm.trans ((congrArg (fun i => a i) hEq).trans hvval)))
  have hiuv : iu ≠ iv := by
    intro hEq
    exact huv (Subtype.ext (huval.symm.trans ((congrArg (fun i => a i) hEq).trans hvval)))
  let p : Fin 4 → Fin 4 := ![ix, iy, iu, iv]
  have hpinj : Function.Injective p := by
    intro j k hjk
    fin_cases j <;> fin_cases k <;>
      simp [p, hixiy, hixiu, hixiv, hiyiu, hiyiv, hiuv,
        (Ne.symm hixiy), (Ne.symm hixiu), (Ne.symm hixiv),
        (Ne.symm hiyiu), (Ne.symm hiyiv), (Ne.symm hiuv)] at hjk ⊢
  have hp_bij : Function.Bijective p :=
    (Fintype.bijective_iff_injective_and_card p).2 ⟨hpinj, rfl⟩
  let e : Fin 4 ≃ Fin 4 := Equiv.ofBijective p hp_bij
  let t : Fin 4 → ℤ := fun i => s (e i)
  have ht : ∀ i, t i = 1 ∨ t i = -1 := by
    intro i
    exact hs (e i)
  have hδeq4 : δ = (t 0 : ℂ) • x.1 + (t 1 : ℂ) • y.1 +
      (t 2 : ℂ) • u.1 + (t 3 : ℂ) • v.1 := by
    rw [hδ]
    calc
      (∑ i, (s i : ℂ) • a i) = ∑ j, (s (e j) : ℂ) • a (e j) := by
        have h1 := Equiv.sum_comp e (fun i => (s i : ℂ) • a i)
        simpa [Equiv.apply_symm_apply] using h1.symm
      _ = ∑ j, (t j : ℂ) • a (p j) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [t, e, p]
      _ = (t 0 : ℂ) • x.1 + (t 1 : ℂ) • y.1 +
          (t 2 : ℂ) • u.1 + (t 3 : ℂ) • v.1 := by
        rw [Fin.sum_univ_four]
        simp [p, hxval, hyval, huval, hvval]
  exact ⟨t, ht, hδeq4⟩

/-- The scalar product of two four-term signed sums over irreducibles that
share exactly the first two named points. -/
private lemma scalarProduct_four_points_common_two
    {δ ε : ClassFunction G} {a b u v w x : Irr G}
    (s t : Fin 4 → ℤ)
    (hδ : δ = (s 0 : ℂ) • a.1 + (s 1 : ℂ) • b.1 +
      (s 2 : ℂ) • u.1 + (s 3 : ℂ) • v.1)
    (hε : ε = (t 0 : ℂ) • a.1 + (t 1 : ℂ) • b.1 +
      (t 2 : ℂ) • w.1 + (t 3 : ℂ) • x.1)
    (hab : a ≠ b) (hau : a ≠ u) (hav : a ≠ v) (haw : a ≠ w) (hax : a ≠ x)
    (hbu : b ≠ u) (hbv : b ≠ v) (hbw : b ≠ w) (hbx : b ≠ x)
    (huv : u ≠ v) (hwx : w ≠ x)
    (huw : u ≠ w) (hux : u ≠ x) (hvw : v ≠ w) (hvx : v ≠ x) :
    scalarProduct G δ ε = (((s 0 * t 0 + s 1 * t 1 : ℤ) : ℂ)) := by
  rw [hδ, hε]
  have hsc0 (p q : Irr G) (hpq : p ≠ q) : scalarProduct G p.1 q.1 = 0 := by
    rw [scalarProduct_irr_ite p.2 q.2]
    have hne : p.1 ≠ q.1 := by
      intro h
      exact hpq (Subtype.ext h)
    simp [hne]
  have hsc1 (p : Irr G) : scalarProduct G p.1 p.1 = 1 := by
    rw [scalarProduct_irr_ite p.2 p.2]
    simp
  simp [scalarProduct_add_left, scalarProduct_add_right, scalarProduct_smul_left,
    scalarProduct_smul_right, star_intCast,
    hsc0 a b hab, hsc0 b a hab.symm,
    hsc0 a u hau, hsc0 u a hau.symm,
    hsc0 a v hav, hsc0 v a hav.symm,
    hsc0 a w haw, hsc0 w a haw.symm,
    hsc0 a x hax, hsc0 x a hax.symm,
    hsc0 b u hbu, hsc0 u b hbu.symm,
    hsc0 b v hbv, hsc0 v b hbv.symm,
    hsc0 b w hbw, hsc0 w b hbw.symm,
    hsc0 b x hbx, hsc0 x b hbx.symm,
    hsc0 u v huv, hsc0 v u huv.symm,
    hsc0 w x hwx, hsc0 x w hwx.symm,
    hsc0 u w huw, hsc0 w u huw.symm,
    hsc0 u x hux, hsc0 x u hux.symm,
    hsc0 v w hvw, hsc0 w v hvw.symm,
    hsc0 v x hvx, hsc0 x v hvx.symm,
    hsc1 a, hsc1 b]

/-- The first three fixed deltas have the source's displayed signed
patterns, up to a global sign on each equation. -/
private lemma fixed_signed_three_pattern
    {δ₁ δ₂ δ₃ : ClassFunction G}
    {A₁ : Fin 4 → ClassFunction G} (hA₁ : ∀ i, IsIrreducibleCharacter (A₁ i))
    (hAinj₁ : Function.Injective A₁) {s₁ : Fin 4 → ℤ}
    (hs₁ : ∀ i, s₁ i = 1 ∨ s₁ i = -1)
    (hδ₁ : δ₁ = ∑ i, (s₁ i : ℂ) • A₁ i)
    {A₂ : Fin 4 → ClassFunction G} (hA₂ : ∀ i, IsIrreducibleCharacter (A₂ i))
    (hAinj₂ : Function.Injective A₂) {s₂ : Fin 4 → ℤ}
    (hs₂ : ∀ i, s₂ i = 1 ∨ s₂ i = -1)
    (hδ₂ : δ₂ = ∑ i, (s₂ i : ℂ) • A₂ i)
    {A₃ : Fin 4 → ClassFunction G} (hA₃ : ∀ i, IsIrreducibleCharacter (A₃ i))
    (hAinj₃ : Function.Injective A₃) {s₃ : Fin 4 → ℤ}
    (hs₃ : ∀ i, s₃ i = 1 ∨ s₃ i = -1)
    (hδ₃ : δ₃ = ∑ i, (s₃ i : ℂ) • A₃ i)
    {a b c₀ d e f g : Irr G}
    (ha : a ∈ involved δ₁ ∩ involved δ₂ ∩ involved δ₃)
    (hb : b ∈ (involved δ₁ ∩ involved δ₂) \ involved δ₃)
    (hc : c₀ ∈ (involved δ₁ ∩ involved δ₃) \ involved δ₂)
    (hd : d ∈ involved δ₁ \ (involved δ₂ ∪ involved δ₃))
    (he : e ∈ (involved δ₂ ∩ involved δ₃) \ involved δ₁)
    (hf : f ∈ involved δ₂ \ (involved δ₁ ∪ involved δ₃))
    (hg : g ∈ involved δ₃ \ (involved δ₁ ∪ involved δ₂))
    (hab : a ≠ b) (hac : a ≠ c₀) (had : a ≠ d)
    (hbc : b ≠ c₀) (hbd : b ≠ d) (hcd : c₀ ≠ d)
    (hae : a ≠ e) (haf : a ≠ f) (hag : a ≠ g)
    (hbe : b ≠ e) (hbf : b ≠ f) (hbg : b ≠ g)
    (hce : c₀ ≠ e) (hcf : c₀ ≠ f) (hcg : c₀ ≠ g)
    (hde : d ≠ e) (hdf : d ≠ f) (hdg : d ≠ g)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (horth12 : scalarProduct G δ₁ δ₂ = 0)
    (horth13 : scalarProduct G δ₁ δ₃ = 0)
    (horth23 : scalarProduct G δ₂ δ₃ = 0) :
    ∃ η₁ η₂ η₃ : ℤ,
      (η₁ = 1 ∨ η₁ = -1) ∧ (η₂ = 1 ∨ η₂ = -1) ∧ (η₃ = 1 ∨ η₃ = -1) ∧
      ∃ χ₁ χ₂ χ₃ ψ₁ ψ₂ ψ₃ φ : ClassFunction G,
        IsPMIrr G χ₁ ∧ IsPMIrr G χ₂ ∧ IsPMIrr G χ₃ ∧
        IsPMIrr G ψ₁ ∧ IsPMIrr G ψ₂ ∧ IsPMIrr G ψ₃ ∧ IsPMIrr G φ ∧
        δ₁ = (η₁ : ℂ) • (χ₁ + χ₂ + χ₃ + ψ₁) ∧
        δ₂ = (η₂ : ℂ) • (χ₁ - χ₂ + φ + ψ₂) ∧
        δ₃ = (η₃ : ℂ) • (χ₁ - χ₃ - φ + ψ₃) := by
  classical
  have ha12 : a ∈ involved δ₁ ∩ involved δ₂ := (Finset.mem_inter.mp ha).1
  have ha1 : a ∈ involved δ₁ := (Finset.mem_inter.mp ha12).1
  have ha2 : a ∈ involved δ₂ := (Finset.mem_inter.mp ha12).2
  have ha3 : a ∈ involved δ₃ := (Finset.mem_inter.mp ha).2
  have hb1 : b ∈ involved δ₁ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hb).1).1
  have hb2 : b ∈ involved δ₂ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hb).1).2
  have hc1 : c₀ ∈ involved δ₁ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hc).1).1
  have hc3 : c₀ ∈ involved δ₃ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hc).1).2
  have hd1 : d ∈ involved δ₁ := (Finset.mem_sdiff.mp hd).1
  have he2 : e ∈ involved δ₂ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp he).1).1
  have he3 : e ∈ involved δ₃ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp he).1).2
  have hf2 : f ∈ involved δ₂ := (Finset.mem_sdiff.mp hf).1
  have hg3 : g ∈ involved δ₃ := (Finset.mem_sdiff.mp hg).1
  rcases reindex_signed_four_by_points hA₁ hAinj₁ hs₁ hδ₁
    (x := a) (y := b) (u := c₀) (v := d) ha1 hb1 hc1 hd1
    hab hac had hbc hbd hcd with ⟨t₁, ht₁, hδ₁'⟩
  rcases reindex_signed_four_by_points hA₂ hAinj₂ hs₂ hδ₂
    (x := a) (y := b) (u := e) (v := f) ha2 hb2 he2 hf2
    hab hae haf hbe hbf hef with ⟨t₂, ht₂, hδ₂'⟩
  rcases reindex_signed_four_by_points hA₃ hAinj₃ hs₃ hδ₃
    (x := a) (y := c₀) (u := e) (v := g) ha3 hc3 he3 hg3
    hac hae hag hce hcg heg with ⟨t₃, ht₃, hδ₃'⟩
  have hsp12 := scalarProduct_four_points_common_two t₁ t₂ hδ₁' hδ₂'
    hab hac had hae haf hbc hbd hbe hbf hcd hef hce hcf hde hdf
  have hEq12 : (t₁ 0 * t₂ 0 + t₁ 1 * t₂ 1 : ℤ) = 0 := by
    have hℂ : (((t₁ 0 * t₂ 0 + t₁ 1 * t₂ 1 : ℤ) : ℂ) = 0) :=
      hsp12.symm.trans horth12
    exact_mod_cast hℂ
  let t₁c : Fin 4 → ℤ := ![t₁ 0, t₁ 2, t₁ 1, t₁ 3]
  have hδ₁_ac : δ₁ = (t₁c 0 : ℂ) • a.1 + (t₁c 1 : ℂ) • c₀.1 +
      (t₁c 2 : ℂ) • b.1 + (t₁c 3 : ℂ) • d.1 := by
    rw [hδ₁']
    ext x
    simp [t₁c]
    ring
  have hsp13 := scalarProduct_four_points_common_two t₁c t₃ hδ₁_ac hδ₃'
    hac hab had hae hag (hbc.symm) hcd hce hcg hbd heg hbe hbg hde hdg
  have hEq13' : (t₁c 0 * t₃ 0 + t₁c 1 * t₃ 1 : ℤ) = 0 := by
    have hℂ : (((t₁c 0 * t₃ 0 + t₁c 1 * t₃ 1 : ℤ) : ℂ) = 0) :=
      hsp13.symm.trans horth13
    exact_mod_cast hℂ
  have hEq13 : (t₁ 0 * t₃ 0 + t₁ 2 * t₃ 1 : ℤ) = 0 := by
    simpa [t₁c] using hEq13'
  let t₂c : Fin 4 → ℤ := ![t₂ 0, t₂ 2, t₂ 1, t₂ 3]
  let t₃c : Fin 4 → ℤ := ![t₃ 0, t₃ 2, t₃ 1, t₃ 3]
  have hδ₂_ae : δ₂ = (t₂c 0 : ℂ) • a.1 + (t₂c 1 : ℂ) • e.1 +
      (t₂c 2 : ℂ) • b.1 + (t₂c 3 : ℂ) • f.1 := by
    rw [hδ₂']
    ext x
    simp [t₂c]
    ring
  have hδ₃_ae : δ₃ = (t₃c 0 : ℂ) • a.1 + (t₃c 1 : ℂ) • e.1 +
      (t₃c 2 : ℂ) • c₀.1 + (t₃c 3 : ℂ) • g.1 := by
    rw [hδ₃']
    ext x
    simp [t₃c]
    ring
  have hsp23 := scalarProduct_four_points_common_two t₂c t₃c hδ₂_ae hδ₃_ae
    hae hab haf hac hag (hbe.symm) hef (hce.symm) heg hbf hcg hbc hbg (hcf.symm) hfg
  have hEq23' : (t₂c 0 * t₃c 0 + t₂c 1 * t₃c 1 : ℤ) = 0 := by
    have hℂ : (((t₂c 0 * t₃c 0 + t₂c 1 * t₃c 1 : ℤ) : ℂ) = 0) :=
      hsp23.symm.trans horth23
    exact_mod_cast hℂ
  have hEq23 : (t₂ 0 * t₃ 0 + t₂ 2 * t₃ 2 : ℤ) = 0 := by
    simpa [t₂c, t₃c] using hEq23'
  let η₁ : ℤ := t₁ 0
  let η₂ : ℤ := t₂ 0
  let η₃ : ℤ := t₃ 0
  have hη₁ : η₁ = 1 ∨ η₁ = -1 := by simpa [η₁] using ht₁ 0
  have hη₂ : η₂ = 1 ∨ η₂ = -1 := by simpa [η₂] using ht₂ 0
  have hη₃ : η₃ = 1 ∨ η₃ = -1 := by simpa [η₃] using ht₃ 0
  let χ₁ : ClassFunction G := a.1
  let χ₂ : ClassFunction G := ((t₁ 0 * t₁ 1 : ℤ) : ℂ) • b.1
  let χ₃ : ClassFunction G := ((t₁ 0 * t₁ 2 : ℤ) : ℂ) • c₀.1
  let ψ₁ : ClassFunction G := ((t₁ 0 * t₁ 3 : ℤ) : ℂ) • d.1
  let φ : ClassFunction G := ((t₂ 0 * t₂ 2 : ℤ) : ℂ) • e.1
  let ψ₂ : ClassFunction G := ((t₂ 0 * t₂ 3 : ℤ) : ℂ) • f.1
  let ψ₃ : ClassFunction G := ((t₃ 0 * t₃ 3 : ℤ) : ℂ) • g.1
  have hχ₁pm : IsPMIrr G χ₁ := Or.inl a.2
  have hχ₂pm : IsPMIrr G χ₂ := by
    simpa [χ₂] using pmIrr_sign_smul b.2 (mul_sign_one_or_neg_one (ht₁ 0) (ht₁ 1))
  have hχ₃pm : IsPMIrr G χ₃ := by
    simpa [χ₃] using pmIrr_sign_smul c₀.2 (mul_sign_one_or_neg_one (ht₁ 0) (ht₁ 2))
  have hψ₁pm : IsPMIrr G ψ₁ := by
    simpa [ψ₁] using pmIrr_sign_smul d.2 (mul_sign_one_or_neg_one (ht₁ 0) (ht₁ 3))
  have hφpm : IsPMIrr G φ := by
    simpa [φ] using pmIrr_sign_smul e.2 (mul_sign_one_or_neg_one (ht₂ 0) (ht₂ 2))
  have hψ₂pm : IsPMIrr G ψ₂ := by
    simpa [ψ₂] using pmIrr_sign_smul f.2 (mul_sign_one_or_neg_one (ht₂ 0) (ht₂ 3))
  have hψ₃pm : IsPMIrr G ψ₃ := by
    simpa [ψ₃] using pmIrr_sign_smul g.2 (mul_sign_one_or_neg_one (ht₃ 0) (ht₃ 3))
  have hsq11 : t₁ 0 * t₁ 0 = (1 : ℤ) := by
    rcases ht₁ 0 with h | h <;> simp [h]
  have hsq12 : t₁ 1 * t₁ 1 = (1 : ℤ) := by
    rcases ht₁ 1 with h | h <;> simp [h]
  have hsq13 : t₁ 2 * t₁ 2 = (1 : ℤ) := by
    rcases ht₁ 2 with h | h <;> simp [h]
  have hsq21 : t₂ 0 * t₂ 0 = (1 : ℤ) := by
    rcases ht₂ 0 with h | h <;> simp [h]
  have hsq23 : t₂ 2 * t₂ 2 = (1 : ℤ) := by
    rcases ht₂ 2 with h | h <;> simp [h]
  have hsq31 : t₃ 0 * t₃ 0 = (1 : ℤ) := by
    rcases ht₃ 0 with h | h <;> simp [h]
  have hbcoef : t₂ 0 * (t₁ 0 * t₁ 1) = -t₂ 1 := by
    have hprod : t₁ 0 * t₂ 0 = -(t₁ 1 * t₂ 1) := by
      linarith [hEq12]
    calc
      t₂ 0 * (t₁ 0 * t₁ 1) = (t₁ 0 * t₂ 0) * t₁ 1 := by ring
      _ = (-(t₁ 1 * t₂ 1)) * t₁ 1 := by rw [hprod]
      _ = -(t₂ 1 * (t₁ 1 * t₁ 1)) := by ring
      _ = -t₂ 1 := by rw [hsq12]; ring
  have hc1coef : t₃ 0 * (t₁ 0 * t₁ 2) = -t₃ 1 := by
    have hprod : t₁ 0 * t₃ 0 = -(t₁ 2 * t₃ 1) := by
      linarith [hEq13]
    calc
      t₃ 0 * (t₁ 0 * t₁ 2) = (t₁ 0 * t₃ 0) * t₁ 2 := by ring
      _ = (-(t₁ 2 * t₃ 1)) * t₁ 2 := by rw [hprod]
      _ = -(t₃ 1 * (t₁ 2 * t₁ 2)) := by ring
      _ = -t₃ 1 := by rw [hsq13]; ring
  have hc2coef : t₃ 0 * (t₂ 0 * t₂ 2) = -t₃ 2 := by
    have hprod : t₂ 0 * t₃ 0 = -(t₂ 2 * t₃ 2) := by
      linarith [hEq23]
    calc
      t₃ 0 * (t₂ 0 * t₂ 2) = (t₂ 0 * t₃ 0) * t₂ 2 := by ring
      _ = (-(t₂ 2 * t₃ 2)) * t₂ 2 := by rw [hprod]
      _ = -(t₃ 2 * (t₂ 2 * t₂ 2)) := by ring
      _ = -t₃ 2 := by rw [hsq23]; ring
  have hsq11ℂ : (t₁ 0 : ℂ) * (t₁ 0 : ℂ) = 1 := by
    exact_mod_cast hsq11
  have hsq21ℂ : (t₂ 0 : ℂ) * (t₂ 0 : ℂ) = 1 := by
    exact_mod_cast hsq21
  have hsq31ℂ : (t₃ 0 : ℂ) * (t₃ 0 : ℂ) = 1 := by
    exact_mod_cast hsq31
  have hbcoefℂ : (t₂ 0 : ℂ) * (t₁ 0 : ℂ) * (t₁ 1 : ℂ) = - (t₂ 1 : ℂ) := by
    calc
      (t₂ 0 : ℂ) * (t₁ 0 : ℂ) * (t₁ 1 : ℂ) =
          ((t₂ 0 * (t₁ 0 * t₁ 1) : ℤ) : ℂ) := by
            norm_num
            ring
      _ = (-t₂ 1 : ℤ) := by rw [hbcoef]
      _ = - (t₂ 1 : ℂ) := by norm_num
  have hc1coefℂ : (t₃ 0 : ℂ) * (t₁ 0 : ℂ) * (t₁ 2 : ℂ) = - (t₃ 1 : ℂ) := by
    calc
      (t₃ 0 : ℂ) * (t₁ 0 : ℂ) * (t₁ 2 : ℂ) =
          ((t₃ 0 * (t₁ 0 * t₁ 2) : ℤ) : ℂ) := by
            norm_num
            ring
      _ = (-t₃ 1 : ℤ) := by rw [hc1coef]
      _ = - (t₃ 1 : ℂ) := by norm_num
  have hc2coefℂ : (t₃ 0 : ℂ) * (t₂ 0 : ℂ) * (t₂ 2 : ℂ) = - (t₃ 2 : ℂ) := by
    calc
      (t₃ 0 : ℂ) * (t₂ 0 : ℂ) * (t₂ 2 : ℂ) =
          ((t₃ 0 * (t₂ 0 * t₂ 2) : ℤ) : ℂ) := by
            norm_num
            ring
      _ = (-t₃ 2 : ℤ) := by rw [hc2coef]
      _ = - (t₃ 2 : ℂ) := by norm_num
  have hδ₁eq : δ₁ = (η₁ : ℂ) • (χ₁ + χ₂ + χ₃ + ψ₁) := by
    rw [hδ₁']
    ext x
    simp [η₁, χ₁, χ₂, χ₃, ψ₁, hsq11ℂ]
    linear_combination -((t₁ 1 : ℂ) * b.1 x + (t₁ 2 : ℂ) * c₀.1 x +
      (t₁ 3 : ℂ) * d.1 x) * hsq11ℂ
  have hδ₂eq : δ₂ = (η₂ : ℂ) • (χ₁ - χ₂ + φ + ψ₂) := by
    rw [hδ₂']
    ext x
    simp [η₂, χ₁, χ₂, φ, ψ₂, hsq21ℂ]
    linear_combination b.1 x * hbcoefℂ -
      ((t₂ 2 : ℂ) * e.1 x + (t₂ 3 : ℂ) * f.1 x) * hsq21ℂ
  have hδ₃eq : δ₃ = (η₃ : ℂ) • (χ₁ - χ₃ - φ + ψ₃) := by
    rw [hδ₃']
    ext x
    simp [η₃, χ₁, χ₃, φ, ψ₃, hsq31ℂ]
    linear_combination c₀.1 x * hc1coefℂ + e.1 x * hc2coefℂ -
      (t₃ 3 : ℂ) * g.1 x * hsq31ℂ
  exact ⟨η₁, η₂, η₃, hη₁, hη₂, hη₃, χ₁, χ₂, χ₃, ψ₁, ψ₂, ψ₃, φ,
    hχ₁pm, hχ₂pm, hχ₃pm, hψ₁pm, hψ₂pm, hψ₃pm, hφpm,
    hδ₁eq, hδ₂eq, hδ₃eq⟩

/-- The scalar product of `χₖ` against a signed combination of an
orthonormal system is the coefficient of `χₖ`. -/
private lemma scalarProduct_chi_sum {G : Type u} [Group G] [Fintype G]
    {χ : Fin 4 → ClassFunction G}
    (hχ : ∀ i, IsPMIrr G (χ i))
    (hχorth : ∀ {i j}, i ≠ j → scalarProduct G (χ i) (χ j) = 0)
    {u : Fin 4 → ℤ} (k : Fin 4) :
    scalarProduct G (χ k) (∑ i, (u i : ℂ) • χ i) = (u k : ℂ) := by
  classical
  rw [scalarProduct_sum_right]
  rw [Finset.sum_eq_single k
    (by
      intro i hi hik
      rw [scalarProduct_smul_right]
      rw [hχorth (Ne.symm hik)]
      simp)
    (by
      intro hknot
      exact False.elim (hknot (Finset.mem_univ k)))]
  rw [scalarProduct_smul_right]
  have hself : scalarProduct G (χ k) (χ k) = 1 := by
    rcases hχ k with h | h
    · exact scalarProduct_irreducible_self h
    · have h' : scalarProduct G (-χ k) (-χ k) = 1 := scalarProduct_irreducible_self h
      rw [scalarProduct_neg_left, scalarProduct_neg_right] at h'
      simpa using h'
  rw [hself]
  simp

/-- Three signed sums over one orthonormal system with pairwise orthogonal
values have the displayed sign patterns (up to reordering the `χ`'s). -/
private lemma signed_four_pattern {δ₁ δ₂ δ₃ : ClassFunction G}
    {χ : Fin 4 → ClassFunction G}
    {u v : Fin 4 → ℤ}
    (hδ₁ : δ₁ = ∑ i, χ i)
    (hδ₂ : δ₂ = ∑ i, (u i : ℂ) • χ i)
    (hδ₃ : δ₃ = ∑ i, (v i : ℂ) • χ i)
    (hu : ∀ i, u i = 1 ∨ u i = -1)
    (hv : ∀ i, v i = 1 ∨ v i = -1)
    (h₂ : ∑ i, u i = 0) (h₃ : ∑ i, v i = 0)
    (h₂₃ : ∑ i, u i * v i = 0)
    (hpm : ∀ i, IsPMIrr G (χ i))
    (horth : ∀ {i j}, i ≠ j → scalarProduct G (χ i) (χ j) = 0) :
    ∃ χ₁ χ₂ χ₃ χ₄ : ClassFunction G,
      IsPMIrr G χ₁ ∧ IsPMIrr G χ₂ ∧ IsPMIrr G χ₃ ∧ IsPMIrr G χ₄ ∧
      scalarProduct G χ₁ χ₂ = 0 ∧ scalarProduct G χ₁ χ₃ = 0 ∧
      scalarProduct G χ₁ χ₄ = 0 ∧ scalarProduct G χ₂ χ₃ = 0 ∧
      scalarProduct G χ₂ χ₄ = 0 ∧ scalarProduct G χ₃ χ₄ = 0 ∧
      δ₁ = χ₁ + χ₂ + χ₃ + χ₄ ∧
      δ₂ = χ₁ - χ₂ + χ₃ - χ₄ ∧
      δ₃ = χ₁ + χ₂ - χ₃ - χ₄ := by
  rcases standard_sign_perm u v hu hv h₂ h₃ h₂₃ with ⟨σ, hσ₂, hσ₃⟩
  let w₂ : Fin 4 → ℤ := fun i => if i = 1 ∨ i = 3 then (-1 : ℤ) else 1
  let w₃ : Fin 4 → ℤ := fun i => if i = 2 ∨ i = 3 then (-1 : ℤ) else 1
  let χ' : Fin 4 → ClassFunction G := fun i => χ (σ i)
  have huσ : ∀ j, u j = w₂ (σ.symm j) := by
    intro j
    have h := hσ₂ (σ.symm j)
    simpa [Equiv.apply_symm_apply] using h
  have hvσ : ∀ j, v j = w₃ (σ.symm j) := by
    intro j
    have h := hσ₃ (σ.symm j)
    simpa [Equiv.apply_symm_apply] using h
  have hσne {i j : Fin 4} (hij : i ≠ j) : σ i ≠ σ j := by
    intro hEq
    exact hij (σ.injective hEq)
  refine ⟨χ' 0, χ' 1, χ' 2, χ' 3, hpm (σ 0), hpm (σ 1), hpm (σ 2), hpm (σ 3),
    horth (hσne (by decide : (0 : Fin 4) ≠ 1)),
    horth (hσne (by decide : (0 : Fin 4) ≠ 2)),
    horth (hσne (by decide : (0 : Fin 4) ≠ 3)),
    horth (hσne (by decide : (1 : Fin 4) ≠ 2)),
    horth (hσne (by decide : (1 : Fin 4) ≠ 3)),
    horth (hσne (by decide : (2 : Fin 4) ≠ 3)), ?_, ?_, ?_⟩
  · rw [hδ₁]
    calc
      (∑ i, χ i) = ∑ j, χ (σ j) := (Equiv.sum_comp σ χ).symm
      _ = χ' 0 + χ' 1 + χ' 2 + χ' 3 := by
        rw [Fin.sum_univ_four]
  · rw [hδ₂]
    calc
      (∑ i, (u i : ℂ) • χ i) = ∑ j, (w₂ j : ℂ) • χ (σ j) := sum_smul_perm σ huσ
      _ = ∑ j, (w₂ j : ℂ) • χ' j := rfl
      _ = χ' 0 - χ' 1 + χ' 2 - χ' 3 := by
        rw [Fin.sum_univ_four]
        simp [w₂]
        abel
  · rw [hδ₃]
    calc
      (∑ i, (v i : ℂ) • χ i) = ∑ j, (w₃ j : ℂ) • χ (σ j) := sum_smul_perm σ hvσ
      _ = ∑ j, (w₃ j : ℂ) • χ' j := rfl
      _ = χ' 0 + χ' 1 - χ' 2 - χ' 3 := by
        rw [Fin.sum_univ_four]
        simp [w₃]
        abel

/-- The coefficient vector of a signed four-sum with the same constituent
set as another signed four-sum, expressed in the second sum's basis. -/
private lemma coeff_vector_of_signed_four {δ₁ δ₂ : ClassFunction G}
    {a : Fin 4 → ClassFunction G} (ha : ∀ i, IsIrreducibleCharacter (a i))
    (hainj : Function.Injective a) {s : Fin 4 → ℤ} (hs : ∀ i, s i = 1 ∨ s i = -1)
    (hδ₁ : δ₁ = ∑ i, (s i : ℂ) • a i)
    {b : Fin 4 → ClassFunction G} (hb : ∀ i, IsIrreducibleCharacter (b i))
    (hbinj : Function.Injective b) {t : Fin 4 → ℤ} (ht : ∀ i, t i = 1 ∨ t i = -1)
    (hδ₂ : δ₂ = ∑ i, (t i : ℂ) • b i)
    (hEq : involved δ₂ = involved δ₁) :
    ∃ u : Fin 4 → ℤ,
      (∀ i, u i = 1 ∨ u i = -1) ∧
      δ₂ = ∑ i, (u i : ℂ) • ((s i : ℂ) • a i) := by
  classical
  let A : Fin 4 → Irr G := fun i => ⟨a i, ha i⟩
  let B : Fin 4 → Irr G := fun i => ⟨b i, hb i⟩
  have hEqA : involved δ₁ = ({A 0, A 1, A 2, A 3} : Finset (Irr G)) := by
    rw [show involved δ₁ = Finset.univ.image (fun i : Fin 4 => ⟨a i, ha i⟩) by
      exact involved_eq_of_signed_four_fin ha hainj hs hδ₁]
    ext β
    rw [Finset.mem_image]
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp [A]
    · intro hβ
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_singleton] at hβ
      rcases hβ with rfl | rfl | rfl | rfl
      · exact ⟨0, Finset.mem_univ 0, rfl⟩
      · exact ⟨1, Finset.mem_univ 1, rfl⟩
      · exact ⟨2, Finset.mem_univ 2, rfl⟩
      · exact ⟨3, Finset.mem_univ 3, rfl⟩
  have hEqB : involved δ₂ = ({B 0, B 1, B 2, B 3} : Finset (Irr G)) := by
    rw [show involved δ₂ = Finset.univ.image (fun i : Fin 4 => ⟨b i, hb i⟩) by
      exact involved_eq_of_signed_four_fin hb hbinj ht hδ₂]
    ext β
    rw [Finset.mem_image]
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp [B]
    · intro hβ
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_singleton] at hβ
      rcases hβ with rfl | rfl | rfl | rfl
      · exact ⟨0, Finset.mem_univ 0, rfl⟩
      · exact ⟨1, Finset.mem_univ 1, rfl⟩
      · exact ⟨2, Finset.mem_univ 2, rfl⟩
      · exact ⟨3, Finset.mem_univ 3, rfl⟩
  have hBmem₁ : ∀ j, B j ∈ involved δ₁ := by
    intro j
    rw [← hEq, hEqB]
    fin_cases j <;> simp
  have hAne {i j : Fin 4} (hij : i ≠ j) : A i ≠ A j := by
    intro hEq
    exact hij (hainj (congrArg Subtype.val hEq))
  have hA01 : A 0 ≠ A 1 := hAne (by decide)
  have hA02 : A 0 ≠ A 2 := hAne (by decide)
  have hA03 : A 0 ≠ A 3 := hAne (by decide)
  have hA12 : A 1 ≠ A 2 := hAne (by decide)
  have hA13 : A 1 ≠ A 3 := hAne (by decide)
  have hA23 : A 2 ≠ A 3 := hAne (by decide)
  let p : Fin 4 → Fin 4 := fun j =>
    if B j = A 0 then 0 else if B j = A 1 then 1 else if B j = A 2 then 2 else 3
  have hp_eq : ∀ j, B j = A (p j) := by
    intro j
    have hmem : B j ∈ ({A 0, A 1, A 2, A 3} : Finset (Irr G)) := by
      rw [← hEqA]
      exact hBmem₁ j
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton] at hmem
    rcases hmem with h0 | h1 | h2 | h3
    · have hpj : p j = 0 := by simp [p, h0]
      rw [hpj, h0]
    · have hne0 : B j ≠ A 0 := by
        intro hEq
        exact hA01 (h1.symm.trans hEq).symm
      have hpj : p j = 1 := by
        unfold p
        rw [h1]
        simp [hA01.symm]
      rw [hpj, h1]
    · have hne0 : B j ≠ A 0 := by
        intro hEq
        exact hA02 (h2.symm.trans hEq).symm
      have hne1 : B j ≠ A 1 := by
        intro hEq
        exact hA12 (h2.symm.trans hEq).symm
      have hpj : p j = 2 := by
        unfold p
        rw [h2]
        simp [hA02.symm, hA12.symm]
      rw [hpj, h2]
    · have hne0 : B j ≠ A 0 := by
        intro hEq
        exact hA03 (h3.symm.trans hEq).symm
      have hne1 : B j ≠ A 1 := by
        intro hEq
        exact hA13 (h3.symm.trans hEq).symm
      have hne2 : B j ≠ A 2 := by
        intro hEq
        exact hA23 (h3.symm.trans hEq).symm
      have hpj : p j = 3 := by
        unfold p
        rw [h3]
        simp [hA03.symm, hA13.symm, hA23.symm]
      rw [hpj, h3]
  have hb_eq : ∀ j, b j = a (p j) := by
    intro j
    exact congrArg Subtype.val (hp_eq j)
  have hpinj : Function.Injective p := by
    intro j k hjk
    have hBj : B j = B k := by
      rw [hp_eq j, hp_eq k, hjk]
    have hbj : b j = b k := congrArg Subtype.val hBj
    exact hbinj hbj
  have hp_bij : Function.Bijective p :=
    (Fintype.bijective_iff_injective_and_card p).2 ⟨hpinj, rfl⟩
  let e : Fin 4 ≃ Fin 4 := Equiv.ofBijective p hp_bij
  let u : Fin 4 → ℤ := fun i => t (e.symm i) * s i
  let chi : Fin 4 → ClassFunction G := fun i => (s i : ℂ) • a i
  have ha_chi : ∀ k, a k = (s k : ℂ) • chi k := by
    intro k
    dsimp [chi]
    rcases hs k with h | h <;> simp [h]
  have hu : ∀ i, u i = 1 ∨ u i = -1 := by
    intro i
    rcases ht (e.symm i) with h | h <;> rcases hs i with h' | h' <;> simp [u, h, h']
  have hδ₂eq : δ₂ = ∑ i, (u i : ℂ) • ((s i : ℂ) • a i) := by
    calc
      δ₂ = ∑ j, (t j : ℂ) • b j := hδ₂
      _ = ∑ j, (t j : ℂ) • a (p j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hb_eq j]
      _ = ∑ j, (t j * s (p j) : ℂ) • chi (p j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [ha_chi (p j)]
        rw [smul_smul]
      _ = ∑ i, (u i : ℂ) • ((s i : ℂ) • a i) := by
        have h := Equiv.sum_comp e (fun i => (u i : ℂ) • ((s i : ℂ) • a i))
        simpa [u, e, Equiv.symm_apply_apply] using h
  exact ⟨u, hu, hδ₂eq⟩

/-- Two signed four-sums with an odd number of common constituents are not
orthogonal. -/
private lemma scalarProduct_ne_zero_of_inter_card_odd {δ ε : ClassFunction G}
    {a : Fin 4 → ClassFunction G} (ha : ∀ i, IsIrreducibleCharacter (a i))
    (hainj : Function.Injective a) {s : Fin 4 → ℤ}
    (hs : ∀ i, s i = 1 ∨ s i = -1)
    (hδ : δ = ∑ i, (s i : ℂ) • a i)
    {b : Fin 4 → ClassFunction G} (hb : ∀ i, IsIrreducibleCharacter (b i))
    (hbinj : Function.Injective b) {t : Fin 4 → ℤ}
    (ht : ∀ i, t i = 1 ∨ t i = -1)
    (hε : ε = ∑ i, (t i : ℂ) • b i)
    (hodd : Odd ((involved δ ∩ involved ε).card)) :
    scalarProduct G δ ε ≠ 0 := by
  classical
  rcases scalarProduct_signed_four_eq_int_sum ha hainj hs hδ hb hbinj ht hε with
    ⟨z, c, hz, hc_sign, hc_iff, hzdef⟩
  let shared : Finset (Fin 4) := Finset.univ.filter (fun i => c i ≠ 0)
  have hc_odd : ∀ i ∈ shared, Odd (c i) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rcases hc_sign i with h0 | h1 | hneg
    · exact False.elim (hi.2 h0)
    · rw [h1]
      norm_num
    · rw [hneg]
      norm_num
  have hshared_card : shared.card = (involved δ ∩ involved ε).card := by
    let A : Fin 4 → Irr G := fun i => ⟨a i, ha i⟩
    have hAinj : Function.Injective A := by
      intro i j hEq
      exact hainj (congrArg Subtype.val hEq)
    have hδeq : involved δ = Finset.univ.image A :=
      involved_eq_of_signed_four_fin ha hainj hs hδ
    have hεeq : involved ε = Finset.univ.image (fun i : Fin 4 => ⟨b i, hb i⟩) :=
      involved_eq_of_signed_four_fin hb hbinj ht hε
    apply Finset.card_bij (s := shared) (t := involved δ ∩ involved ε)
      (fun i hi => A i)
    · intro i hi
      rw [Finset.mem_inter]
      constructor
      · rw [hδeq]
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      · rw [hεeq]
        rcases (hc_iff i).1 (Finset.mem_filter.mp hi).2 with ⟨j, hj⟩
        refine Finset.mem_image.mpr ⟨j, Finset.mem_univ j, ?_⟩
        apply Subtype.ext
        exact hj
    · intro i hi j hj hEq
      exact hAinj hEq
    · intro χ hχ
      rw [Finset.mem_inter] at hχ
      rw [hδeq] at hχ
      rcases Finset.mem_image.mp hχ.1 with ⟨i, hi, rfl⟩
      refine ⟨i, ?_, rfl⟩
      rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_univ i
      · exact (hc_iff i).2 (by
          rw [hεeq] at hχ
          rcases Finset.mem_image.mp hχ.2 with ⟨j, hj, hEq⟩
          refine ⟨j, ?_⟩
          exact congrArg Subtype.val hEq)
  have hshared_odd : Odd shared.card := by
    rwa [hshared_card]
  have hsum_shared : (∑ i : Fin 4, c i) = ∑ i ∈ shared, c i := by
    calc
      (∑ i : Fin 4, c i) = ∑ i, (if c i ≠ 0 then c i else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases h : c i ≠ 0
        · simp [h]
        · have hci : c i = 0 := by
            by_contra hc
            exact h hc
          simp [hci]
      _ = ∑ i ∈ shared, c i := by rw [Finset.sum_filter]
  have hz_odd : Odd z := by
    rw [hzdef, hsum_shared]
    exact (odd_sum_iff_odd_card shared c hc_odd).mpr hshared_odd
  intro hzero
  have hz0 : (z : ℂ) = 0 := by rwa [hz]
  have hzInt : z = 0 := by exact_mod_cast hz0
  rcases hz_odd with ⟨k, hk⟩
  omega

/-- If two signed four-sums have the same constituent set, the scalar
product of any irreducible with their difference is an even integer. -/
private lemma scalarProduct_even_of_signed_four_eq {δ₁ δ₂ : ClassFunction G}
    {a : Fin 4 → ClassFunction G} (ha : ∀ i, IsIrreducibleCharacter (a i))
    (hainj : Function.Injective a) {s : Fin 4 → ℤ}
    (hs : ∀ i, s i = 1 ∨ s i = -1)
    (hδ₁ : δ₁ = ∑ i, (s i : ℂ) • a i)
    {u : Fin 4 → ℤ} (hu : ∀ i, u i = 1 ∨ u i = -1)
    (hδ₂ : δ₂ = ∑ i, (u i : ℂ) • ((s i : ℂ) • a i)) :
    ∀ χ : ClassFunction G, IsIrreducibleCharacter χ →
      ∃ k : ℤ, (k : ℂ) = scalarProduct G χ (δ₁ - δ₂) ∧ Even k := by
  classical
  intro χ hχ
  have hδeq : δ₁ - δ₂ =
      ∑ i, (((1 - u i) * s i : ℤ) : ℂ) • a i := by
    rw [hδ₁, hδ₂]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rcases hu i with hu | hu <;> rcases hs i with hs | hs <;>
      ext x <;> simp [hu, hs] <;> ring
  by_cases hmem : ∃ i, χ = a i
  · let i₀ := Classical.choose hmem
    have hi₀ : χ = a i₀ := Classical.choose_spec hmem
    have hsp : scalarProduct G χ (δ₁ - δ₂) =
        (((1 - u i₀) * s i₀ : ℤ) : ℂ) := by
      rw [scalarProduct_irr_decomp_right (ε := δ₁ - δ₂) (b := a) (t := fun i =>
        (1 - u i) * s i) ha hainj hδeq (χ := χ) hχ]
      have hχeq : ∃ i, a i = χ := ⟨i₀, hi₀.symm⟩
      have hchoose : Classical.choose hχeq = i₀ := hainj (by
        simpa [Classical.choose_spec hχeq] using hi₀)
      simp [hχeq, hchoose]
    refine ⟨(1 - u i₀) * s i₀, hsp.symm, ?_⟩
    rcases hu i₀ with hu | hu <;> rcases hs i₀ with hs | hs <;>
      simp [hu, hs]
  · have hsp : scalarProduct G χ (δ₁ - δ₂) = 0 := by
      rw [scalarProduct_irr_decomp_right (ε := δ₁ - δ₂) (b := a) (t := fun i =>
        (1 - u i) * s i) ha hainj hδeq (χ := χ) hχ]
      have hnone : ¬ ∃ i, a i = χ := by
        intro h
        rcases h with ⟨i, hi⟩
        exact hmem ⟨i, hi.symm⟩
      simp [hnone]
    exact ⟨0, by simpa using hsp.symm, by norm_num⟩

/-- The scalar product of an irreducible with a signed irreducible is an
integer. -/
private lemma scalarProduct_pmIrr_int {ρ : ClassFunction G}
    (hρ : IsPMIrr G ρ) (χ : ClassFunction G)
    (hχ : IsIrreducibleCharacter χ) :
    ∃ a : ℤ, (a : ℂ) = scalarProduct G χ ρ := by
  rcases hρ with hpos | hneg
  · refine ⟨if χ = ρ then 1 else 0, ?_⟩
    rw [scalarProduct_irr_ite hχ hpos]
    by_cases h : χ = ρ <;> simp [h]
  · have hsp : scalarProduct G χ (-ρ) = if χ = -ρ then 1 else 0 :=
      scalarProduct_irr_ite hχ hneg
    refine ⟨-(if χ = -ρ then 1 else 0), ?_⟩
    have hEq : scalarProduct G χ ρ = - scalarProduct G χ (-ρ) := by
      rw [← neg_neg ρ, scalarProduct_neg_right]
      simp
    rw [hEq, hsp]
    by_cases h : χ = -ρ <;> simp [h]

/-- A sum of doubled signed irreducibles has only even scalar products with
irreducibles. -/
private lemma scalarProduct_even_of_two_smul_pmIrr_sum
    {ρ : Fin 4 → ClassFunction G} (hρ : ∀ i, IsPMIrr G (ρ i))
    (δ : ClassFunction G) (hδ : δ = ∑ i, (2 : ℂ) • ρ i) :
    ∀ χ : ClassFunction G, IsIrreducibleCharacter χ →
      ∃ m : ℤ, (m : ℂ) = scalarProduct G χ δ ∧ Even m := by
  intro χ hχ
  have hterm : ∀ i, ∃ a : ℤ, (a : ℂ) = scalarProduct G χ (ρ i) :=
    fun i => scalarProduct_pmIrr_int (hρ i) χ hχ
  choose a ha using hterm
  have hsum : scalarProduct G χ δ = ((∑ i, 2 * a i : ℤ) : ℂ) := by
    rw [hδ, scalarProduct_sum_right]
    calc
      (∑ i, scalarProduct G χ ((2 : ℂ) • ρ i))
          = ∑ i, ((2 * a i : ℤ) : ℂ) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [scalarProduct_smul_right]
              rw [← ha i]
              norm_num [star_intCast]
              ring
      _ = ((∑ i, 2 * a i : ℤ) : ℂ) := by rw [Int.cast_sum]
  refine ⟨∑ i, 2 * a i, hsum.symm, ?_⟩
  apply Finset.even_sum
  intro i hi
  exact (Int.even_mul).2 (Or.inl (by norm_num : Even (2 : ℤ)))

/-! The next two helpers forget the signs and retain only the support of a
signed four-decomposition.  This is the parity form needed for the
four-block incidence contradiction. -/

/-- A signed four-sum has an integral scalar product whose nonzero status is
exactly membership in its involved constituent set. -/
private lemma scalarProduct_signed_four_support
    {δ : ClassFunction G}
    {a : Fin 4 → ClassFunction G} (ha : ∀ i, IsIrreducibleCharacter (a i))
    (hainj : Function.Injective a) {s : Fin 4 → ℤ}
    (hs : ∀ i, s i = 1 ∨ s i = -1)
    (hδ : δ = ∑ i, (s i : ℂ) • a i)
    (χ : Irr G) :
    ∃ z : ℤ, (z : ℂ) = scalarProduct G χ.1 δ ∧
      (z = 0 ∨ z = 1 ∨ z = -1) ∧
      (z ≠ 0 ↔ χ ∈ involved δ) := by
  classical
  by_cases hmem : ∃ i, a i = χ
  · let i₀ : Fin 4 := Classical.choose hmem
    have hi₀ : a i₀ = χ := Classical.choose_spec hmem
    have hsp : scalarProduct G χ.1 δ = (s i₀ : ℂ) := by
      rw [scalarProduct_irr_decomp_right (ε := δ) (b := a) (t := s)
        ha hainj hδ (χ := χ.1) χ.2]
      have hchoose : Classical.choose hmem = i₀ := rfl
      simp [hmem, hchoose, hi₀]
    refine ⟨s i₀, hsp.symm, ?_, ?_⟩
    · rcases hs i₀ with h | h <;> simp [h]
    · have hinvolved : χ ∈ involved δ := by
        rw [involved_eq_of_signed_four_fin ha hainj hs hδ]
        exact Finset.mem_image.mpr ⟨i₀, Finset.mem_univ _, Subtype.ext hi₀⟩
      constructor
      · intro _
        exact hinvolved
      · intro _
        rcases hs i₀ with h | h <;> simp [h]
  · have hsp : scalarProduct G χ.1 δ = 0 := by
      rw [scalarProduct_irr_decomp_right (ε := δ) (b := a) (t := s)
        ha hainj hδ (χ := χ.1) χ.2]
      simp [hmem]
    refine ⟨0, by simpa using hsp.symm, Or.inl rfl, ?_⟩
    constructor
    · intro hz
      exact False.elim (hz rfl)
    · intro hχmem
      rw [involved_eq_of_signed_four_fin ha hainj hs hδ] at hχmem
      rcases Finset.mem_image.mp hχmem with ⟨i, _, hi⟩
      exact False.elim (hmem ⟨i, congrArg Subtype.val hi⟩)

/-- If four signed four-sums contain every irreducible an even number of
times, then every irreducible scalar product with their sum is even. -/
private lemma scalarProduct_even_of_four_signed_support
    {δ₀ δ₁ δ₂ δ₃ : ClassFunction G}
    {a₀ a₁ a₂ a₃ : Fin 4 → ClassFunction G}
    {s₀ s₁ s₂ s₃ : Fin 4 → ℤ}
    (ha₀ : ∀ i, IsIrreducibleCharacter (a₀ i))
    (hi₀ : Function.Injective a₀) (hs₀ : ∀ i, s₀ i = 1 ∨ s₀ i = -1)
    (hδ₀ : δ₀ = ∑ i, (s₀ i : ℂ) • a₀ i)
    (ha₁ : ∀ i, IsIrreducibleCharacter (a₁ i))
    (hi₁ : Function.Injective a₁) (hs₁ : ∀ i, s₁ i = 1 ∨ s₁ i = -1)
    (hδ₁ : δ₁ = ∑ i, (s₁ i : ℂ) • a₁ i)
    (ha₂ : ∀ i, IsIrreducibleCharacter (a₂ i))
    (hi₂ : Function.Injective a₂) (hs₂ : ∀ i, s₂ i = 1 ∨ s₂ i = -1)
    (hδ₂ : δ₂ = ∑ i, (s₂ i : ℂ) • a₂ i)
    (ha₃ : ∀ i, IsIrreducibleCharacter (a₃ i))
    (hi₃ : Function.Injective a₃) (hs₃ : ∀ i, s₃ i = 1 ∨ s₃ i = -1)
    (hδ₃ : δ₃ = ∑ i, (s₃ i : ℂ) • a₃ i)
    (hcount : ∀ χ : Irr G,
      Even ((if χ ∈ involved δ₀ then 1 else 0) +
        (if χ ∈ involved δ₁ then 1 else 0) +
        (if χ ∈ involved δ₂ then 1 else 0) +
        (if χ ∈ involved δ₃ then 1 else 0))) :
    ∀ χ : Irr G,
      ∃ k : ℤ, (k : ℂ) = scalarProduct G χ.1 (δ₀ + δ₁ + δ₂ + δ₃) ∧ Even k := by
  classical
  intro χ
  rcases scalarProduct_signed_four_support ha₀ hi₀ hs₀ hδ₀ χ with
    ⟨z₀, hz₀, hsz₀, hmem₀⟩
  rcases scalarProduct_signed_four_support ha₁ hi₁ hs₁ hδ₁ χ with
    ⟨z₁, hz₁, hsz₁, hmem₁⟩
  rcases scalarProduct_signed_four_support ha₂ hi₂ hs₂ hδ₂ χ with
    ⟨z₂, hz₂, hsz₂, hmem₂⟩
  rcases scalarProduct_signed_four_support ha₃ hi₃ hs₃ hδ₃ χ with
    ⟨z₃, hz₃, hsz₃, hmem₃⟩
  have hcountz : Even ((if z₀ ≠ 0 then 1 else 0) +
      (if z₁ ≠ 0 then 1 else 0) + (if z₂ ≠ 0 then 1 else 0) +
      (if z₃ ≠ 0 then 1 else 0)) := by
    simpa [hmem₀, hmem₁, hmem₂, hmem₃] using hcount χ
  have hsum_even : Even (z₀ + z₁ + z₂ + z₃) := by
    rcases hcountz with ⟨q, hq⟩
    rcases hsz₀ with h0 | h0 | h0 <;>
      rcases hsz₁ with h1 | h1 | h1 <;>
      rcases hsz₂ with h2 | h2 | h2 <;>
      rcases hsz₃ with h3 | h3 | h3 <;>
      simp [h0, h1, h2, h3] at hq ⊢ <;>
      norm_num [even_iff_two_dvd] at hq ⊢ <;> omega
  refine ⟨z₀ + z₁ + z₂ + z₃, ?_, hsum_even⟩
  rw [scalarProduct_add_right, scalarProduct_add_right, scalarProduct_add_right]
  simpa [Int.cast_add, hz₀, hz₁, hz₂, hz₃]

/-- A four-element finset containing three named distinct points has a
fourth point outside those three. -/
private lemma exists_fourth_of_card_four {ι : Type*} [DecidableEq ι]
    {A : Finset ι} {a b c : ι} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hA : A.card = 4) :
    ∃ d : ι, d ∈ A ∧ d ≠ a ∧ d ≠ b ∧ d ≠ c ∧
      A = ({a, b, c, d} : Finset ι) := by
  classical
  have htriple : ({a, b, c} : Finset ι).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
      simp [hab, hac]), Finset.card_insert_of_notMem (by simp [hbc]),
      Finset.card_singleton]
  have hex : ∃ d : ι, d ∈ A ∧ d ≠ a ∧ d ≠ b ∧ d ≠ c := by
    by_contra h
    have hsub : A ⊆ ({a, b, c} : Finset ι) := by
      intro x hx
      by_contra hnot
      apply h
      refine ⟨x, hx, ?_, ?_, ?_⟩
      · intro hxa
        subst x
        exact hnot (by simp)
      · intro hxb
        subst x
        exact hnot (by simp)
      · intro hxc
        subst x
        exact hnot (by simp)
    have hle := Finset.card_le_card hsub
    rw [hA, htriple] at hle
    omega
  rcases hex with ⟨d, hd, hda, hdb, hdc⟩
  refine ⟨d, hd, hda, hdb, hdc, ?_⟩
  have hsub : ({a, b, c, d} : Finset ι) ⊆ A := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have hcard : ({a, b, c, d} : Finset ι).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, hda.symm]),
      Finset.card_insert_of_notMem (by simp [hbc, hdb.symm]),
      Finset.card_insert_of_notMem (by simp [hdc.symm]), Finset.card_singleton]
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hA])).symm

/-- Sign equations forced by the five-block repeated-incidence pattern. -/
private lemma repeated_incidence_sign_contradiction
    {A0 A1 A2 B0 B1 B2 B3 C0 C1 C2 C3 D0 D1 D2 D3 F0 F1 F2 : ℤ}
    (hA0 : A0 * A0 = 1) (hA1 : A1 * A1 = 1) (hA2 : A2 * A2 = 1)
    (hB0 : B0 * B0 = 1) (hB1 : B1 * B1 = 1) (hB2 : B2 * B2 = 1)
    (hB3 : B3 * B3 = 1) (hC0 : C0 * C0 = 1) (hC1 : C1 * C1 = 1)
    (hC2 : C2 * C2 = 1) (hC3 : C3 * C3 = 1) (hD0 : D0 * D0 = 1)
    (hD1 : D1 * D1 = 1) (hD2 : D2 * D2 = 1) (hD3 : D3 * D3 = 1)
    (hF0 : F0 * F0 = 1) (hF1 : F1 * F1 = 1) (hF2 : F2 * F2 = 1)
    (hAB : A0 * B0 + A1 * B1 = 0)
    (hAC : A0 * C0 + A2 * C1 = 0)
    (hBC : B0 * C0 + B2 * C2 = 0)
    (hAD : A1 * D0 + A2 * D1 = 0)
    (hBD : B1 * D0 + B3 * D2 = 0)
    (hCD : C1 * D1 + C3 * D3 = 0)
    (hBF : B2 * F0 + B3 * F1 = 0)
    (hCF : C2 * F0 + C3 * F2 = 0) :
    D2 * F1 + D3 * F2 ≠ 0 := by
  have eB1 : B1 = -(A0 * B0 * A1) := by
    calc
      B1 = (A1 * A1) * B1 := by rw [hA1]; ring
      _ = A1 * (A1 * B1) := by ring
      _ = A1 * (-(A0 * B0)) := by
        have h : A1 * B1 = -(A0 * B0) := by linarith [hAB]
        rw [h]
      _ = -(A0 * B0 * A1) := by ring
  have eC1 : C1 = -(A0 * C0 * A2) := by
    calc
      C1 = (A2 * A2) * C1 := by rw [hA2]; ring
      _ = A2 * (A2 * C1) := by ring
      _ = A2 * (-(A0 * C0)) := by
        have h : A2 * C1 = -(A0 * C0) := by linarith [hAC]
        rw [h]
      _ = -(A0 * C0 * A2) := by ring
  have eB2 : B2 = -(B0 * C0 * C2) := by
    calc
      B2 = (C2 * C2) * B2 := by rw [hC2]; ring
      _ = C2 * (B2 * C2) := by ring
      _ = C2 * (-(B0 * C0)) := by
        have h : B2 * C2 = -(B0 * C0) := by linarith [hBC]
        rw [h]
      _ = -(B0 * C0 * C2) := by ring
  have eD1 : D1 = -(A1 * D0 * A2) := by
    calc
      D1 = (A2 * A2) * D1 := by rw [hA2]; ring
      _ = A2 * (A2 * D1) := by ring
      _ = A2 * (-(A1 * D0)) := by
        have h : A2 * D1 = -(A1 * D0) := by linarith [hAD]
        rw [h]
      _ = -(A1 * D0 * A2) := by ring
  have eD2 : D2 = -(B1 * D0 * B3) := by
    calc
      D2 = (B3 * B3) * D2 := by rw [hB3]; ring
      _ = B3 * (B3 * D2) := by ring
      _ = B3 * (-(B1 * D0)) := by
        have h : B3 * D2 = -(B1 * D0) := by linarith [hBD]
        rw [h]
      _ = -(B1 * D0 * B3) := by ring
  have eD3 : D3 = -(C1 * D1 * C3) := by
    calc
      D3 = (C3 * C3) * D3 := by rw [hC3]; ring
      _ = C3 * (C3 * D3) := by ring
      _ = C3 * (-(C1 * D1)) := by
        have h : C3 * D3 = -(C1 * D1) := by linarith [hCD]
        rw [h]
      _ = -(C1 * D1 * C3) := by ring
  have eF1 : F1 = -(B2 * F0 * B3) := by
    calc
      F1 = (B3 * B3) * F1 := by rw [hB3]; ring
      _ = B3 * (B3 * F1) := by ring
      _ = B3 * (-(B2 * F0)) := by
        have h : B3 * F1 = -(B2 * F0) := by linarith [hBF]
        rw [h]
      _ = -(B2 * F0 * B3) := by ring
  have eF2 : F2 = -(C2 * F0 * C3) := by
    calc
      F2 = (C3 * C3) * F2 := by rw [hC3]; ring
      _ = C3 * (C3 * F2) := by ring
      _ = C3 * (-(C2 * F0)) := by
        have h : C3 * F2 = -(C2 * F0) := by linarith [hCF]
        rw [h]
      _ = -(C2 * F0 * C3) := by ring
  have hprod : D2 * F1 = D3 * F2 := by
    calc
      D2 * F1 = B1 * B2 * D0 * F0 := by
        rw [eD2, eF1]
        linear_combination (B1 * B2 * D0 * F0) * hB3
      _ = A0 * A1 * C0 * C2 * D0 * F0 := by
        rw [eB1, eB2]
        linear_combination (A0 * A1 * C0 * C2 * D0 * F0) * hB0
      _ = C1 * D1 * C2 * F0 := by
        rw [eC1, eD1]
        linear_combination -(A0 * A1 * C0 * C2 * D0 * F0) * hA2
      _ = D3 * F2 := by
        rw [eD3, eF2]
        linear_combination -(C1 * D1 * C2 * F0) * hC3
  intro hz
  rw [hprod] at hz
  have hD2ne : D2 ≠ 0 := by
    intro h
    rw [h] at hD2
    norm_num at hD2
  have hF1ne : F1 ≠ 0 := by
    intro h
    rw [h] at hF1
    norm_num at hF1
  have hprodne : D2 * F1 ≠ 0 := mul_ne_zero hD2ne hF1ne
  apply hprodne
  omega

/-- Five signed four-sums with the repeated incidence pattern cannot all be
pairwise orthogonal in the indicated pairs. -/
private lemma repeated_incidence_orthogonality_contradiction
    {δA δB δC δD δF : ClassFunction G}
    {AA AB AC AD AF : Fin 4 → ClassFunction G}
    {sA sB sC sD sF : Fin 4 → ℤ}
    (hAA : ∀ i, IsIrreducibleCharacter (AA i)) (hiA : Function.Injective AA)
    (hsA : ∀ i, sA i = 1 ∨ sA i = -1)
    (hδA : δA = ∑ i, (sA i : ℂ) • AA i)
    (hAB : ∀ i, IsIrreducibleCharacter (AB i)) (hiB : Function.Injective AB)
    (hsB : ∀ i, sB i = 1 ∨ sB i = -1)
    (hδB : δB = ∑ i, (sB i : ℂ) • AB i)
    (hAC : ∀ i, IsIrreducibleCharacter (AC i)) (hiC : Function.Injective AC)
    (hsC : ∀ i, sC i = 1 ∨ sC i = -1)
    (hδC : δC = ∑ i, (sC i : ℂ) • AC i)
    (hAD : ∀ i, IsIrreducibleCharacter (AD i)) (hiD : Function.Injective AD)
    (hsD : ∀ i, sD i = 1 ∨ sD i = -1)
    (hδD : δD = ∑ i, (sD i : ℂ) • AD i)
    (hAF : ∀ i, IsIrreducibleCharacter (AF i)) (hiF : Function.Injective AF)
    (hsF : ∀ i, sF i = 1 ∨ sF i = -1)
    (hδF : δF = ∑ i, (sF i : ℂ) • AF i)
    {a b c₀ d e f g h : Irr G}
    (hAset : involved δA = {a, b, c₀, d})
    (hBset : involved δB = {a, b, e, f})
    (hCset : involved δC = {a, c₀, e, g})
    (hDset : involved δD = {b, c₀, f, g})
    (hFset : involved δF = {e, f, g, h})
    (hab : a ≠ b) (hac : a ≠ c₀) (had : a ≠ d)
    (hbc : b ≠ c₀) (hbd : b ≠ d) (hcd : c₀ ≠ d)
    (hae : a ≠ e) (haf : a ≠ f) (hag : a ≠ g)
    (hbe : b ≠ e) (hbf : b ≠ f) (hbg : b ≠ g)
    (hce : c₀ ≠ e) (hcf : c₀ ≠ f) (hcg : c₀ ≠ g)
    (hde : d ≠ e) (hdf : d ≠ f) (hdg : d ≠ g)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hha : h ≠ a) (hhb : h ≠ b) (hhc : h ≠ c₀)
    (hhe : h ≠ e) (hhf : h ≠ f) (hhg : h ≠ g)
    (hortAB : scalarProduct G δA δB = 0)
    (hortAC : scalarProduct G δA δC = 0)
    (hortBC : scalarProduct G δB δC = 0)
    (hortAD : scalarProduct G δA δD = 0)
    (hortBD : scalarProduct G δB δD = 0)
    (hortCD : scalarProduct G δC δD = 0)
    (hortBF : scalarProduct G δB δF = 0)
    (hortCF : scalarProduct G δC δF = 0)
    (hortDF : scalarProduct G δD δF = 0) : False := by
  classical
  have mem_of_set {δ : ClassFunction G} {x : Irr G} {T : Finset (Irr G)}
      (hset : involved δ = T) (hx : x ∈ T) : x ∈ involved δ := by
    rwa [hset]
  have haA := mem_of_set hAset (by simp : a ∈ ({a, b, c₀, d} : Finset (Irr G)))
  have hbA := mem_of_set hAset (by simp : b ∈ ({a, b, c₀, d} : Finset (Irr G)))
  have hcA := mem_of_set hAset (by simp : c₀ ∈ ({a, b, c₀, d} : Finset (Irr G)))
  have hdA := mem_of_set hAset (by simp : d ∈ ({a, b, c₀, d} : Finset (Irr G)))
  have haB := mem_of_set hBset (by simp : a ∈ ({a, b, e, f} : Finset (Irr G)))
  have hbB := mem_of_set hBset (by simp : b ∈ ({a, b, e, f} : Finset (Irr G)))
  have heB := mem_of_set hBset (by simp : e ∈ ({a, b, e, f} : Finset (Irr G)))
  have hfB := mem_of_set hBset (by simp : f ∈ ({a, b, e, f} : Finset (Irr G)))
  have haC := mem_of_set hCset (by simp : a ∈ ({a, c₀, e, g} : Finset (Irr G)))
  have hcC := mem_of_set hCset (by simp : c₀ ∈ ({a, c₀, e, g} : Finset (Irr G)))
  have heC := mem_of_set hCset (by simp : e ∈ ({a, c₀, e, g} : Finset (Irr G)))
  have hgC := mem_of_set hCset (by simp : g ∈ ({a, c₀, e, g} : Finset (Irr G)))
  have hbD := mem_of_set hDset (by simp : b ∈ ({b, c₀, f, g} : Finset (Irr G)))
  have hcD := mem_of_set hDset (by simp : c₀ ∈ ({b, c₀, f, g} : Finset (Irr G)))
  have hfD := mem_of_set hDset (by simp : f ∈ ({b, c₀, f, g} : Finset (Irr G)))
  have hgD := mem_of_set hDset (by simp : g ∈ ({b, c₀, f, g} : Finset (Irr G)))
  have heF := mem_of_set hFset (by simp : e ∈ ({e, f, g, h} : Finset (Irr G)))
  have hfF := mem_of_set hFset (by simp : f ∈ ({e, f, g, h} : Finset (Irr G)))
  have hgF := mem_of_set hFset (by simp : g ∈ ({e, f, g, h} : Finset (Irr G)))
  have hhF := mem_of_set hFset (by simp : h ∈ ({e, f, g, h} : Finset (Irr G)))
  rcases reindex_signed_four_by_points hAA hiA hsA hδA haA hbA hcA hdA
    hab hac had hbc hbd hcd with ⟨tA, htA, hAeq⟩
  rcases reindex_signed_four_by_points hAB hiB hsB hδB haB hbB heB hfB
    hab hae haf hbe hbf hef with ⟨tB, htB, hBeq⟩
  rcases reindex_signed_four_by_points hAC hiC hsC hδC haC hcC heC hgC
    hac hae hag hce hcg heg with ⟨tC, htC, hCeq⟩
  rcases reindex_signed_four_by_points hAD hiD hsD hδD hbD hcD hfD hgD
    hbc hbf hbg hcf hcg hfg with ⟨tD, htD, hDeq⟩
  rcases reindex_signed_four_by_points hAF hiF hsF hδF heF hfF hgF hhF
    hef heg hhe.symm hfg hhf.symm hhg.symm with ⟨tF, htF, hFeq⟩
  have int_eq_zero {z : ℤ} (hz : (z : ℂ) = 0) : z = 0 := by exact_mod_cast hz
  have hEqAB : tA 0 * tB 0 + tA 1 * tB 1 = 0 := by
    apply int_eq_zero
    exact (scalarProduct_four_points_common_two tA tB hAeq hBeq
      hab hac had hae haf hbc hbd hbe hbf hcd hef hce hcf hde hdf).symm.trans hortAB
  have hEqAC : tA 0 * tC 0 + tA 2 * tC 1 = 0 := by
    let tA' : Fin 4 → ℤ := ![tA 0, tA 2, tA 1, tA 3]
    have hAeq' : δA = (tA' 0 : ℂ) • a.1 + (tA' 1 : ℂ) • c₀.1 +
        (tA' 2 : ℂ) • b.1 + (tA' 3 : ℂ) • d.1 := by
      rw [hAeq]
      ext x
      simp [tA']
      ring
    apply int_eq_zero
    simpa [tA'] using
      (scalarProduct_four_points_common_two tA' tC hAeq' hCeq
        hac hab had hae hag hbc.symm hcd hce hcg hbd heg hbe hbg hde hdg).symm.trans hortAC
  have hEqBC : tB 0 * tC 0 + tB 2 * tC 2 = 0 := by
    let tB' : Fin 4 → ℤ := ![tB 0, tB 2, tB 1, tB 3]
    let tC' : Fin 4 → ℤ := ![tC 0, tC 2, tC 1, tC 3]
    have hBeq' : δB = (tB' 0 : ℂ) • a.1 + (tB' 1 : ℂ) • e.1 +
        (tB' 2 : ℂ) • b.1 + (tB' 3 : ℂ) • f.1 := by
      rw [hBeq]
      ext x
      simp [tB']
      ring
    have hCeq' : δC = (tC' 0 : ℂ) • a.1 + (tC' 1 : ℂ) • e.1 +
        (tC' 2 : ℂ) • c₀.1 + (tC' 3 : ℂ) • g.1 := by
      rw [hCeq]
      ext x
      simp [tC']
      ring
    apply int_eq_zero
    simpa [tB', tC'] using
      (scalarProduct_four_points_common_two tB' tC' hBeq' hCeq'
        hae hab haf hac hag hbe.symm hef hce.symm heg hbf hcg hbc hbg hcf.symm hfg).symm.trans hortBC
  have hEqAD : tA 1 * tD 0 + tA 2 * tD 1 = 0 := by
    let tA' : Fin 4 → ℤ := ![tA 1, tA 2, tA 0, tA 3]
    have hAeq' : δA = (tA' 0 : ℂ) • b.1 + (tA' 1 : ℂ) • c₀.1 +
        (tA' 2 : ℂ) • a.1 + (tA' 3 : ℂ) • d.1 := by
      rw [hAeq]
      ext x
      simp [tA']
      ring
    apply int_eq_zero
    simpa [tA'] using
      (scalarProduct_four_points_common_two tA' tD hAeq' hDeq
        hbc hab.symm hbd hbf hbg hac.symm hcd hcf hcg had hfg haf hag hdf hdg).symm.trans hortAD
  have hEqBD : tB 1 * tD 0 + tB 3 * tD 2 = 0 := by
    let tB' : Fin 4 → ℤ := ![tB 1, tB 3, tB 0, tB 2]
    let tD' : Fin 4 → ℤ := ![tD 0, tD 2, tD 1, tD 3]
    have hBeq' : δB = (tB' 0 : ℂ) • b.1 + (tB' 1 : ℂ) • f.1 +
        (tB' 2 : ℂ) • a.1 + (tB' 3 : ℂ) • e.1 := by
      rw [hBeq]
      ext x
      simp [tB']
      ring
    have hDeq' : δD = (tD' 0 : ℂ) • b.1 + (tD' 1 : ℂ) • f.1 +
        (tD' 2 : ℂ) • c₀.1 + (tD' 3 : ℂ) • g.1 := by
      rw [hDeq]
      ext x
      simp [tD']
      ring
    apply int_eq_zero
    simpa [tB', tD'] using
      (scalarProduct_four_points_common_two tB' tD' hBeq' hDeq'
        hbf hab.symm hbe hbc hbg haf.symm hef.symm hcf.symm hfg hae hcg
        hac hag hce.symm heg).symm.trans hortBD
  have hEqCD : tC 1 * tD 1 + tC 3 * tD 3 = 0 := by
    let tC' : Fin 4 → ℤ := ![tC 1, tC 3, tC 0, tC 2]
    let tD' : Fin 4 → ℤ := ![tD 1, tD 3, tD 0, tD 2]
    have hCeq' : δC = (tC' 0 : ℂ) • c₀.1 + (tC' 1 : ℂ) • g.1 +
        (tC' 2 : ℂ) • a.1 + (tC' 3 : ℂ) • e.1 := by
      rw [hCeq]
      ext x
      simp [tC']
      ring
    have hDeq' : δD = (tD' 0 : ℂ) • c₀.1 + (tD' 1 : ℂ) • g.1 +
        (tD' 2 : ℂ) • b.1 + (tD' 3 : ℂ) • f.1 := by
      rw [hDeq]
      ext x
      simp [tD']
      ring
    apply int_eq_zero
    simpa [tC', tD'] using
      (scalarProduct_four_points_common_two tC' tD' hCeq' hDeq'
        hcg hac.symm hce hbc.symm hcf hag.symm heg.symm hbg.symm hfg.symm
        hae hbf hab haf hbe.symm hef).symm.trans hortCD
  have hEqBF : tB 2 * tF 0 + tB 3 * tF 1 = 0 := by
    let tB' : Fin 4 → ℤ := ![tB 2, tB 3, tB 0, tB 1]
    have hBeq' : δB = (tB' 0 : ℂ) • e.1 + (tB' 1 : ℂ) • f.1 +
        (tB' 2 : ℂ) • a.1 + (tB' 3 : ℂ) • b.1 := by
      rw [hBeq]
      ext x
      simp [tB']
      ring
    apply int_eq_zero
    simpa [tB'] using
      (scalarProduct_four_points_common_two tB' tF hBeq' hFeq
        hef hae.symm hbe.symm heg hhe.symm haf.symm hbf.symm hfg hhf.symm
        hab hhg.symm hag hha.symm hbg hhb.symm).symm.trans hortBF
  have hEqCF : tC 2 * tF 0 + tC 3 * tF 2 = 0 := by
    let tC' : Fin 4 → ℤ := ![tC 2, tC 3, tC 0, tC 1]
    let tF' : Fin 4 → ℤ := ![tF 0, tF 2, tF 1, tF 3]
    have hCeq' : δC = (tC' 0 : ℂ) • e.1 + (tC' 1 : ℂ) • g.1 +
        (tC' 2 : ℂ) • a.1 + (tC' 3 : ℂ) • c₀.1 := by
      rw [hCeq]
      ext x
      simp [tC']
      ring
    have hFeq' : δF = (tF' 0 : ℂ) • e.1 + (tF' 1 : ℂ) • g.1 +
        (tF' 2 : ℂ) • f.1 + (tF' 3 : ℂ) • h.1 := by
      rw [hFeq]
      ext x
      simp [tF']
      ring
    apply int_eq_zero
    simpa [tC', tF'] using
      (scalarProduct_four_points_common_two tC' tF' hCeq' hFeq'
        heg hae.symm hce.symm hef hhe.symm hag.symm hcg.symm hfg.symm hhg.symm
        hac hhf.symm haf hha.symm hcf hhc.symm).symm.trans hortCF
  have sq_of_sign {z : ℤ} (hz : z = 1 ∨ z = -1) : z * z = 1 := by
    rcases hz with h | h <;> simp [h]
  have hnonzero := repeated_incidence_sign_contradiction
    (sq_of_sign (htA 0)) (sq_of_sign (htA 1)) (sq_of_sign (htA 2))
    (sq_of_sign (htB 0)) (sq_of_sign (htB 1)) (sq_of_sign (htB 2)) (sq_of_sign (htB 3))
    (sq_of_sign (htC 0)) (sq_of_sign (htC 1)) (sq_of_sign (htC 2)) (sq_of_sign (htC 3))
    (sq_of_sign (htD 0)) (sq_of_sign (htD 1)) (sq_of_sign (htD 2)) (sq_of_sign (htD 3))
    (sq_of_sign (htF 0)) (sq_of_sign (htF 1)) (sq_of_sign (htF 2))
    hEqAB hEqAC hEqBC hEqAD hEqBD hEqCD hEqBF hEqCF
  let tD' : Fin 4 → ℤ := ![tD 2, tD 3, tD 0, tD 1]
  let tF' : Fin 4 → ℤ := ![tF 1, tF 2, tF 0, tF 3]
  have hDeq' : δD = (tD' 0 : ℂ) • f.1 + (tD' 1 : ℂ) • g.1 +
      (tD' 2 : ℂ) • b.1 + (tD' 3 : ℂ) • c₀.1 := by
    rw [hDeq]
    ext x
    simp [tD']
    ring
  have hFeq' : δF = (tF' 0 : ℂ) • f.1 + (tF' 1 : ℂ) • g.1 +
      (tF' 2 : ℂ) • e.1 + (tF' 3 : ℂ) • h.1 := by
    rw [hFeq]
    ext x
    simp [tF']
    ring
  have hspDF := scalarProduct_four_points_common_two tD' tF' hDeq' hFeq'
    hfg hbf.symm hcf.symm hef.symm hhf.symm hbg.symm hcg.symm heg.symm hhg.symm
    hbc hhe.symm hbe hhb.symm hce hhc.symm
  have hzero : tD 2 * tF 1 + tD 3 * tF 2 = 0 := by
    apply int_eq_zero
    simpa [tD', tF'] using hspDF.symm.trans hortDF
  exact hnonzero hzero

/-- The pairwise-distinct `δ₄, δ₅, δ₆` case contradicts the fixed parity
rule. -/
private lemma incidence_distinct_contradiction
    {δ₁ δ₂ δ₅ δ₆ : ClassFunction G}
    {χ₁ χ₂ χ₃ ψ₁ ψ₂ ψ₃ φ σ : ClassFunction G}
    (hpm : IsPMIrr G χ₁ ∧ IsPMIrr G χ₃ ∧ IsPMIrr G φ ∧ IsPMIrr G ψ₃)
    (hδ₁ : δ₁ = χ₁ + χ₂ + χ₃ + ψ₁)
    (hδ₂ : δ₂ = χ₁ - χ₂ + φ + ψ₂)
    (hδ₅ : δ₅ = χ₃ - ψ₁ + ψ₃ - σ)
    (hδ₆ : δ₆ = φ - ψ₂ + ψ₃ + σ)
    (hparity : ∃ χ : ClassFunction G, IsIrreducibleCharacter χ ∧
      ∃ m : ℤ, (m : ℂ) = scalarProduct G χ (δ₁ + δ₂ + δ₅ + δ₆) ∧ Odd m) :
    False := by
  rcases hpm with ⟨hχ₁, hχ₃, hφ, hψ₃⟩
  have hsum : δ₁ + δ₂ + δ₅ + δ₆ =
      (2 : ℂ) • χ₁ + (2 : ℂ) • χ₃ + (2 : ℂ) • φ + (2 : ℂ) • ψ₃ := by
    rw [hδ₁, hδ₂, hδ₅, hδ₆]
    ext x
    simp
    ring
  let ρ : Fin 4 → ClassFunction G := ![χ₁, χ₃, φ, ψ₃]
  have hδsum : δ₁ + δ₂ + δ₅ + δ₆ = ∑ i, (2 : ℂ) • ρ i := by
    rw [hsum, Fin.sum_univ_four]
    rfl
  rcases hparity with ⟨χ, hχ, m, hm, hOddm⟩
  rcases scalarProduct_even_of_two_smul_pmIrr_sum
    (ρ := ρ) (by
      intro i
      fin_cases i
      · simpa [ρ] using hχ₁
      · simpa [ρ] using hχ₃
      · simpa [ρ] using hφ
      · simpa [ρ] using hψ₃) (δ₁ + δ₂ + δ₅ + δ₆) hδsum χ hχ with
    ⟨k, hk, hEvenk⟩
  have hEqmk : m = k := by
    have hℂ : (m : ℂ) = (k : ℂ) := hm.trans hk.symm
    exact_mod_cast hℂ
  have hEvenm : Even m := by
    rwa [hEqmk]
  exact (Int.not_even_iff_odd).2 hOddm hEvenm


/-- If two 2-element intersections with `A` share one point and carry two
further distinct points, the two third blocks cannot coincide. -/
private lemma incidence_pair_neq_of_third_blocks {ι : Type*} [DecidableEq ι]
    {A D E : Finset ι} (hAD : (A ∩ D).card = 2) (hAE : (A ∩ E).card = 2)
    {b c d : ι}
    (hbD : b ∈ D) (hdD : d ∈ D) (hcE : c ∈ E) (hdE : d ∈ E)
    (hbA : b ∈ A) (hcA : c ∈ A) (hdA : d ∈ A)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    D ≠ E := by
  intro hEq
  have hb : b ∈ A ∩ D := by
    rw [Finset.mem_inter]
    exact ⟨hbA, hbD⟩
  have hc : c ∈ A ∩ D := by
    rw [Finset.mem_inter]
    exact ⟨hcA, by rwa [hEq]⟩
  have hd : d ∈ A ∩ D := by
    rw [Finset.mem_inter]
    exact ⟨hdA, hdD⟩
  have hsub : ({b, c, d} : Finset ι) ⊆ A ∩ D := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hb
    · exact hc
    · exact hd
  have hbnot : b ∉ ({c, d} : Finset ι) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    intro h
    rcases h with h | h
    · exact hbc h
    · exact hbd h
  have hcnot : c ∉ ({d} : Finset ι) := by
    rw [Finset.mem_singleton]
    intro h
    exact hcd h
  have hcard : ({b, c, d} : Finset ι).card = 3 := by
    rw [Finset.card_insert_of_notMem hbnot,
      Finset.card_insert_of_notMem hcnot, Finset.card_singleton]
  have hle : ({b, c, d} : Finset ι).card ≤ (A ∩ D).card :=
    Finset.card_le_card hsub
  rw [hAD] at hle
  omega

/-- Pure set-level contradiction: the six incidence blocks cannot have two
of `δ₄, δ₅, δ₆` equal. -/
private lemma incidence_six_pairwise_ne {ι : Type*} [DecidableEq ι]
    {A B C D E F : Finset ι}
    (hAD : (A ∩ D).card = 2) (hAE : (A ∩ E).card = 2)
    (hBD : (B ∩ D).card = 2) (hBF : (B ∩ F).card = 2)
    (hCE : (C ∩ E).card = 2) (hCF : (C ∩ F).card = 2)
    {b c d e f g : ι}
    (hbD : b ∈ D) (hdD : d ∈ D) (hcE : c ∈ E) (hdE : d ∈ E)
    (hcF : c ∈ F) (hgF : g ∈ F) (heE : e ∈ E) (hgE : g ∈ E)
    (heF : e ∈ F)
    (hbF : b ∈ F) (hfF : f ∈ F) (heD : e ∈ D) (hfD : f ∈ D)
    (hbA : b ∈ A) (hcA : c ∈ A) (hdA : d ∈ A)
    (hcC : c ∈ C) (heC : e ∈ C) (hgC : g ∈ C)
    (hbB : b ∈ B) (heB : e ∈ B) (hfB : f ∈ B)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hce : c ≠ e) (hcg : c ≠ g) (heg : e ≠ g)
    (hbe : b ≠ e) (hbf : b ≠ f) (hef : e ≠ f) :
    D ≠ E ∧ E ≠ F ∧ F ≠ D := by
  constructor
  · exact incidence_pair_neq_of_third_blocks hAD hAE hbD hdD hcE hdE
      hbA hcA hdA hbc hbd hcd
  constructor
  · exact incidence_pair_neq_of_third_blocks hCE hCF hcE hgE heF hgF
      hcC heC hgC hce hcg heg
  · exact incidence_pair_neq_of_third_blocks hBF hBD hbF hfF heD hfD
      hbB heB hfB hbe hbf hef

/-- In a three-block configuration, `(A∩B) \ C` is a singleton. -/
private lemma card_sdiff_inter_eq_one {ι : Type*} [DecidableEq ι]
    (A B C : Finset ι) (hAB : (A ∩ B).card = 2)
    (hABC : (A ∩ B ∩ C).card = 1) :
    ((A ∩ B) \ C).card = 1 := by
  rw [Finset.card_sdiff]
  rw [hAB]
  have h : (C ∩ (A ∩ B)).card = 1 := by
    simpa [Finset.inter_assoc, Finset.inter_comm] using hABC
  rw [h]

/-- In a three-block configuration, `A \ (B ∪ C)` is a singleton. -/
private lemma card_sdiff_union_eq_one {ι : Type*} [DecidableEq ι]
    (A B C : Finset ι) (hA : A.card = 4) (hAB : (A ∩ B).card = 2)
    (hAC : (A ∩ C).card = 2) (hABC : (A ∩ B ∩ C).card = 1) :
    (A \ (B ∪ C)).card = 1 := by
  rw [Finset.card_sdiff]
  have hinter : ((B ∪ C) ∩ A).card = 3 := by
    have h1 : ((B ∪ C) ∩ A) = (B ∩ A) ∪ (C ∩ A) := by
      ext x
      simp [Finset.mem_inter, Finset.mem_union]
      tauto
    have hcard := Finset.card_union_add_card_inter (B ∩ A) (C ∩ A)
    have h2 : (B ∩ A).card = 2 := by simpa [Finset.inter_comm] using hAB
    have h3 : (C ∩ A).card = 2 := by simpa [Finset.inter_comm] using hAC
    have h4 : ((B ∩ A) ∩ (C ∩ A)).card = 1 := by
      have h5 : (B ∩ A) ∩ (C ∩ A) = A ∩ B ∩ C := by
        ext x
        simp [Finset.mem_inter]
        tauto
      rw [h5]
      exact hABC
    rw [h1]
    omega
  rw [hA, hinter]

/-- Name the four elements of the three-block partition of `A`. -/
private lemma exists_partition_abc {ι : Type*} [DecidableEq ι]
    (A B C : Finset ι) (hA : A.card = 4) (hAB : (A ∩ B).card = 2)
    (hAC : (A ∩ C).card = 2) (hABC : (A ∩ B ∩ C).card = 1) :
    ∃ a b c d : ι,
      a ∈ A ∩ B ∩ C ∧ b ∈ (A ∩ B) \ C ∧ c ∈ (A ∩ C) \ B ∧
      d ∈ A \ (B ∪ C) ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  classical
  rcases Finset.card_eq_one.mp hABC with ⟨a, ha⟩
  have ha_mem : a ∈ A ∩ B ∩ C := by rw [ha]; simp
  rcases Finset.card_eq_one.mp (card_sdiff_inter_eq_one A B C hAB hABC) with ⟨b, hb⟩
  have hb_mem : b ∈ (A ∩ B) \ C := by rw [hb]; simp
  rcases Finset.card_eq_one.mp (card_sdiff_inter_eq_one A C B (by
      simpa [Finset.inter_comm, Finset.inter_left_comm] using hAC)
      (by
        have h' : (A ∩ C ∩ B).card = 1 := by
          simpa [Finset.inter_assoc, Finset.inter_comm, Finset.inter_left_comm] using hABC
        exact h')) with ⟨c, hc⟩
  have hc_mem : c ∈ (A ∩ C) \ B := by rw [hc]; simp
  rcases Finset.card_eq_one.mp (card_sdiff_union_eq_one A B C hA hAB hAC hABC) with ⟨d, hd⟩
  have hd_mem : d ∈ A \ (B ∪ C) := by rw [hd]; simp
  have hbc : b ≠ c := by
    intro hEq
    have hbC : b ∉ C := (Finset.mem_sdiff.mp hb_mem).2
    have hcC : c ∈ C := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hc_mem).1).2
    exact hbC (by rwa [hEq])
  have hbd : b ≠ d := by
    intro hEq
    have hbB : b ∈ B := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hb_mem).1).2
    have hdB : d ∉ B := by
      intro hdBmem
      exact (Finset.mem_sdiff.mp hd_mem).2 (Finset.mem_union.mpr (Or.inl hdBmem))
    exact hdB (by rwa [← hEq])
  have hcd : c ≠ d := by
    intro hEq
    have hcC : c ∈ C := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hc_mem).1).2
    have hdC : d ∉ C := by
      intro hdCmem
      exact (Finset.mem_sdiff.mp hd_mem).2 (Finset.mem_union.mpr (Or.inr hdCmem))
    exact hdC (by rwa [← hEq])
  exact ⟨a, b, c, d, ha_mem, hb_mem, hc_mem, hd_mem, hbc, hbd, hcd⟩

/-- Membership in a singleton set identifies the element. -/
private lemma eq_of_mem_singleton_set {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {a x : ι} (hs : s = ({a} : Finset ι)) (hx : x ∈ s) :
    x = a := by
  rw [hs] at hx
  simpa using hx

/-- An element outside a set differs from every element inside it. -/
private lemma ne_of_not_mem_of_mem {ι : Type*} {x y : ι} {s : Finset ι}
    (hx : x ∉ s) (hy : y ∈ s) : x ≠ y := by
  intro hEq
  exact hx (by rwa [hEq])

/-- The full `a,b,c,d,e,f,g` partition of three four-element blocks. -/
private lemma exists_partition_abcdefg {ι : Type*} [DecidableEq ι]
    (A B C : Finset ι) (hA : A.card = 4) (hB : B.card = 4) (hC : C.card = 4)
    (hAB : (A ∩ B).card = 2) (hAC : (A ∩ C).card = 2)
    (hBC : (B ∩ C).card = 2) (hABC : (A ∩ B ∩ C).card = 1) :
    ∃ a b c d e f g : ι,
      a ∈ A ∩ B ∩ C ∧ b ∈ (A ∩ B) \ C ∧ c ∈ (A ∩ C) \ B ∧
      d ∈ A \ (B ∪ C) ∧ e ∈ (B ∩ C) \ A ∧ f ∈ B \ (A ∪ C) ∧
      g ∈ C \ (A ∪ B) ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      a ≠ e ∧ a ≠ f ∧ a ≠ g ∧ b ≠ e ∧ b ≠ f ∧ b ≠ g ∧
      c ≠ e ∧ c ≠ f ∧ c ≠ g ∧ d ≠ e ∧ d ≠ f ∧ d ≠ g ∧
      e ≠ f ∧ e ≠ g ∧ f ≠ g := by
  classical
  rcases exists_partition_abc A B C hA hAB hAC hABC with
    ⟨a, b, c, d, haABC, hbABC, hcACB, hdAB, hbc, hbd, hcd⟩
  have haAB : a ∈ A ∩ B := (Finset.mem_inter.mp haABC).1
  have haA : a ∈ A := (Finset.mem_inter.mp haAB).1
  have haB : a ∈ B := (Finset.mem_inter.mp haAB).2
  have haC : a ∈ C := (Finset.mem_inter.mp haABC).2
  have hbC : b ∉ C := (Finset.mem_sdiff.mp hbABC).2
  have hcB : c ∉ B := (Finset.mem_sdiff.mp hcACB).2
  have hdB : d ∉ B := by
    intro hd
    exact (Finset.mem_sdiff.mp hdAB).2 (Finset.mem_union.mpr (Or.inl hd))
  have hdC : d ∉ C := by
    intro hd
    exact (Finset.mem_sdiff.mp hdAB).2 (Finset.mem_union.mpr (Or.inr hd))
  have hab : a ≠ b := (ne_of_not_mem_of_mem hbC haC).symm
  have hac : a ≠ c := (ne_of_not_mem_of_mem hcB haB).symm
  have had : a ≠ d := (ne_of_not_mem_of_mem hdB haB).symm
  rcases Finset.card_eq_one.mp hABC with ⟨a₀, ha₀set⟩
  have ha₀ : a₀ ∈ A ∩ B ∩ C := by rw [ha₀set]; simp
  have ha₀a : a₀ = a := by
    rw [ha₀set] at haABC
    have haa₀ : a = a₀ := by simpa using haABC
    exact haa₀.symm
  have hABCsing : A ∩ B ∩ C = ({a} : Finset ι) := by
    rw [← ha₀a, ha₀set]
  have hBA : (B ∩ A).card = 2 := by simpa [Finset.inter_comm] using hAB
  have hBAC : (B ∩ A ∩ C).card = 1 := by
    have h' : B ∩ A ∩ C = A ∩ B ∩ C := by
      ext x
      simp [Finset.mem_inter]
      tauto
    rw [h', hABC]
  rcases exists_partition_abc B A C hB hBA hBC hBAC with
    ⟨a₁, b₁, e, f, ha₁BAC, hb₁BA, heBCA, hfBA, hb₁e, hb₁f, hef⟩
  have ha₁ : a₁ ∈ A ∩ B ∩ C := by
    have h' : B ∩ A ∩ C = A ∩ B ∩ C := by
      ext x
      simp [Finset.mem_inter]
      tauto
    rwa [h'] at ha₁BAC
  have ha₁a : a₁ = a := eq_of_mem_singleton_set hABCsing ha₁
  have hb₁ : b₁ ∈ (A ∩ B) \ C := by
    have h' : (B ∩ A) \ C = (A ∩ B) \ C := by
      ext x
      simp [Finset.mem_inter, Finset.mem_sdiff]
      tauto
    rwa [h'] at hb₁BA
  have hb₁b : b₁ = b := by
    rcases Finset.card_eq_one.mp (card_sdiff_inter_eq_one A B C hAB hABC) with ⟨b₀, hb₀set⟩
    have hb₀ : b₀ ∈ (A ∩ B) \ C := by rw [hb₀set]; simp
    have hb₀b : b₀ = b := by
      rw [hb₀set] at hbABC
      have hbb₀ : b = b₀ := by simpa using hbABC
      exact hbb₀.symm
    rw [hb₀set] at hb₁
    have hb₁b₀ : b₁ = b₀ := by simpa using hb₁
    exact hb₁b₀.trans hb₀b
  have hCA : (C ∩ A).card = 2 := by simpa [Finset.inter_comm] using hAC
  have hCB : (C ∩ B).card = 2 := by simpa [Finset.inter_comm] using hBC
  have hCAB : (C ∩ A ∩ B).card = 1 := by
    have h' : C ∩ A ∩ B = A ∩ B ∩ C := by
      ext x
      simp [Finset.mem_inter]
      tauto
    rw [h', hABC]
  rcases exists_partition_abc C A B hC hCA hCB hCAB with
    ⟨a₂, c₂, e₂, g, ha₂CAB, hc₂CA, he₂CBA, hgCA, hc₂e₂, hc₂g, he₂g⟩
  have ha₂ : a₂ ∈ A ∩ B ∩ C := by
    have h' : C ∩ A ∩ B = A ∩ B ∩ C := by
      ext x
      simp [Finset.mem_inter]
      tauto
    rwa [h'] at ha₂CAB
  have ha₂a : a₂ = a := eq_of_mem_singleton_set hABCsing ha₂
  have hc₂ : c₂ ∈ (A ∩ C) \ B := by
    have h' : (C ∩ A) \ B = (A ∩ C) \ B := by
      ext x
      simp [Finset.mem_inter, Finset.mem_sdiff]
      tauto
    rwa [h'] at hc₂CA
  have hc₂c : c₂ = c := by
    rcases Finset.card_eq_one.mp (card_sdiff_inter_eq_one A C B (by
      simpa [Finset.inter_comm] using hAC) (by
        have h' : A ∩ C ∩ B = A ∩ B ∩ C := by
          ext x
          simp [Finset.mem_inter]
          tauto
        rw [h', hABC])) with ⟨c₀, hc₀set⟩
    have hc₀ : c₀ ∈ (A ∩ C) \ B := by rw [hc₀set]; simp
    have hc₀c : c₀ = c := by
      rw [hc₀set] at hcACB
      have hcc₀ : c = c₀ := by simpa using hcACB
      exact hcc₀.symm
    rw [hc₀set] at hc₂
    have hc₂c₀ : c₂ = c₀ := by simpa using hc₂
    exact hc₂c₀.trans hc₀c
  have he₂ : e₂ ∈ (B ∩ C) \ A := by
    have h' : (C ∩ B) \ A = (B ∩ C) \ A := by
      ext x
      simp [Finset.mem_inter, Finset.mem_sdiff]
      tauto
    rwa [h'] at he₂CBA
  have he₂e : e₂ = e := by
    rcases Finset.card_eq_one.mp (card_sdiff_inter_eq_one B C A hBC (by
      have h' : B ∩ C ∩ A = A ∩ B ∩ C := by
        ext x
        simp [Finset.mem_inter]
        tauto
      rw [h', hABC])) with ⟨e₀, he₀set⟩
    have he₀ : e₀ ∈ (B ∩ C) \ A := by rw [he₀set]; simp
    have he₀e : e₀ = e := by
      rw [he₀set] at heBCA
      have hee₀ : e = e₀ := by simpa using heBCA
      exact hee₀.symm
    rw [he₀set] at he₂
    have he₂e₀ : e₂ = e₀ := by simpa using he₂
    exact he₂e₀.trans he₀e
  -- distinctness
  have eB : e ∈ B := (Finset.mem_inter.mp (Finset.mem_sdiff.mp heBCA).1).1
  have eC : e ∈ C := (Finset.mem_inter.mp (Finset.mem_sdiff.mp heBCA).1).2
  have eA : e ∉ A := (Finset.mem_sdiff.mp heBCA).2
  have fB : f ∈ B := (Finset.mem_sdiff.mp hfBA).1
  have fA : f ∉ A := by
    intro hf
    exact (Finset.mem_sdiff.mp hfBA).2 (Finset.mem_union.mpr (Or.inl hf))
  have fC : f ∉ C := by
    intro hf
    exact (Finset.mem_sdiff.mp hfBA).2 (Finset.mem_union.mpr (Or.inr hf))
  have gC : g ∈ C := (Finset.mem_sdiff.mp hgCA).1
  have gA : g ∉ A := by
    intro hg
    exact (Finset.mem_sdiff.mp hgCA).2 (Finset.mem_union.mpr (Or.inl hg))
  have gB : g ∉ B := by
    intro hg
    exact (Finset.mem_sdiff.mp hgCA).2 (Finset.mem_union.mpr (Or.inr hg))
  have bA : b ∈ A := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hbABC).1).1
  have cA : c ∈ A := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hcACB).1).1
  have ne_mem_not : ∀ {x y : ι} {s : Finset ι}, x ∈ s → y ∉ s → x ≠ y :=
    fun {x y s} hx hy => (ne_of_not_mem_of_mem hy hx).symm
  have hae : a ≠ e := ne_mem_not haA eA
  have haf : a ≠ f := ne_mem_not haA fA
  have hag : a ≠ g := ne_mem_not haA gA
  have hbe : b ≠ e := ne_mem_not bA eA
  have hbf : b ≠ f := ne_mem_not bA fA
  have hbg : b ≠ g := ne_mem_not bA gA
  have hce : c ≠ e := ne_mem_not cA eA
  have hcf : c ≠ f := ne_mem_not cA fA
  have hcg : c ≠ g := ne_mem_not cA gA
  have hde : d ≠ e := (ne_mem_not eB hdB).symm
  have hdf : d ≠ f := (ne_mem_not fB hdB).symm
  have hdg : d ≠ g := (ne_mem_not gC hdC).symm
  have hef : e ≠ f := ne_mem_not eC fC
  have heg : e ≠ g := ne_mem_not eB gB
  have hfg : f ≠ g := ne_mem_not fB gB
  exact ⟨a, b, c, d, e, f, g, haABC, hbABC, hcACB, hdAB, heBCA, hfBA, hgCA,
    hab, hac, had, hbc, hbd, hcd,
    hae, haf, hag, hbe, hbf, hbg,
    hce, hcf, hcg, hde, hdf, hdg,
    hef, heg, hfg⟩


/-- Four distinct members of a four-element finset fill it. -/
private lemma finset_eq_of_card_four {ι : Type*} [DecidableEq ι]
    (A : Finset ι) {a b c d : ι} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hd : d ∈ A) (hA : A.card = 4) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) :
    A = ({a, b, c, d} : Finset ι) := by
  have hsub : ({a, b, c, d} : Finset ι) ⊆ A := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have hcard : ({a, b, c, d} : Finset ι).card = 4 := by
    have h₁not : a ∉ ({b, c, d} : Finset ι) := by
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
      intro h
      rcases h with h | h | h
      · exact hab h
      · exact hac h
      · exact had h
    have h₂not : b ∉ ({c, d} : Finset ι) := by
      rw [Finset.mem_insert, Finset.mem_singleton]
      intro h
      rcases h with h | h
      · exact hbc h
      · exact hbd h
    have h₃not : c ∉ ({d} : Finset ι) := by
      rw [Finset.mem_singleton]
      intro h
      exact hcd h
    rw [Finset.card_insert_of_notMem h₁not,
      Finset.card_insert_of_notMem h₂not,
      Finset.card_insert_of_notMem h₃not, Finset.card_singleton]
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hA, hcard])).symm

/-- If a two-element intersection with a partitioned four-set contains `b`
and excludes `a, c`, it must contain `d`. -/
private lemma other_point_mem_of_inter_two {ι : Type*} [DecidableEq ι]
    {A D : Finset ι} {a b c d : ι}
    (hA : A = ({a, b, c, d} : Finset ι)) (hAD : (A ∩ D).card = 2)
    (hbD : b ∈ D) (haD : a ∉ D) (hcD : c ∉ D) : d ∈ D := by
  by_contra hdD
  have hsub : A ∩ D ⊆ ({b} : Finset ι) := by
    intro x hx
    have hxA : x ∈ A := (Finset.mem_inter.mp hx).1
    have hxD : x ∈ D := (Finset.mem_inter.mp hx).2
    rw [hA] at hxA
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton] at hxA
    rcases hxA with rfl | rfl | rfl | rfl
    · exact False.elim (haD hxD)
    · simp
    · exact False.elim (hcD hxD)
    · exact False.elim (hdD hxD)
  have hle : (A ∩ D).card ≤ 1 := by
    exact Finset.card_le_card hsub
  rw [hAD] at hle
  omega

/-- Once two distinct points fill a two-element intersection, a third
distinct point of the first set cannot lie in the second. -/
private lemma third_not_mem_of_inter_two {ι : Type*} [DecidableEq ι]
    {A D : Finset ι} {x y z : ι} (hAD : (A ∩ D).card = 2)
    (hxA : x ∈ A) (hxD : x ∈ D) (hyA : y ∈ A) (hyD : y ∈ D)
    (hzA : z ∈ A) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    z ∉ D := by
  intro hzD
  have hsub : ({x, y, z} : Finset ι) ⊆ A ∩ D := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hxA, hxD⟩
    · exact Finset.mem_inter.mpr ⟨hyA, hyD⟩
    · exact Finset.mem_inter.mpr ⟨hzA, hzD⟩
  have hcard : ({x, y, z} : Finset ι).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
      Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
  have hle := Finset.card_le_card hsub
  rw [hcard, hAD] at hle
  omega

/-- If a four-set's first three named points are absent from another set,
their intersection has at most the remaining point. -/
private lemma inter_card_le_one_of_three_not_mem {ι : Type*} [DecidableEq ι]
    {A D : Finset ι} {a b c d : ι}
    (hA : A = ({a, b, c, d} : Finset ι))
    (haD : a ∉ D) (hbD : b ∉ D) (hcD : c ∉ D) :
    (A ∩ D).card ≤ 1 := by
  have hsub : A ∩ D ⊆ ({d} : Finset ι) := by
    intro x hx
    have hxA := (Finset.mem_inter.mp hx).1
    have hxD := (Finset.mem_inter.mp hx).2
    rw [hA] at hxA
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxA ⊢
    rcases hxA with rfl | rfl | rfl | rfl
    · exact False.elim (haD hxD)
    · exact False.elim (hbD hxD)
    · exact False.elim (hcD hxD)
    · rfl
  simpa using Finset.card_le_card hsub

/-- In the repeated-incidence case, the two remaining four-sets have the
forced supports used by the sign contradiction. -/
private lemma repeated_supports_of_intersections {ι : Type*} [DecidableEq ι]
    {B C D F : Finset ι} {a b c₀ e f g : ι}
    (hBset : B = ({a, b, e, f} : Finset ι))
    (hCset : C = ({a, c₀, e, g} : Finset ι))
    (hDcard : D.card = 4) (hFcard : F.card = 4)
    (hbD : b ∈ D) (hcD : c₀ ∈ D) (heF : e ∈ F)
    (hBD : (B ∩ D).card = 2) (hCD : (C ∩ D).card = 2)
    (hBF : (B ∩ F).card = 2) (hCF : (C ∩ F).card = 2)
    (haD : a ∉ D) (heD : e ∉ D)
    (haF : a ∉ F) (hbF : b ∉ F) (hcF : c₀ ∉ F)
    (hab : a ≠ b) (hac : a ≠ c₀) (hae : a ≠ e)
    (haf : a ≠ f) (hag : a ≠ g) (hbc : b ≠ c₀)
    (hbe : b ≠ e) (hbf : b ≠ f) (hbg : b ≠ g)
    (hce : c₀ ≠ e) (hcf : c₀ ≠ f) (hcg : c₀ ≠ g)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    ∃ h : ι,
      D = ({b, c₀, f, g} : Finset ι) ∧
      F = ({e, f, g, h} : Finset ι) ∧
      h ≠ a ∧ h ≠ b ∧ h ≠ c₀ ∧ h ≠ e ∧ h ≠ f ∧ h ≠ g := by
  classical
  have hfD : f ∈ D :=
    other_point_mem_of_inter_two hBset hBD hbD haD heD
  have hgD : g ∈ D :=
    other_point_mem_of_inter_two hCset hCD hcD haD heD
  have hDset : D = ({b, c₀, f, g} : Finset ι) :=
    finset_eq_of_card_four D hbD hcD hfD hgD hDcard
      hcf hcg hfg hbc hbf hbg
  have hBset' : B = ({a, e, b, f} : Finset ι) := by
    rw [hBset]
    ext x
    simp
    tauto
  have hCset' : C = ({a, e, c₀, g} : Finset ι) := by
    rw [hCset]
    ext x
    simp
    tauto
  have hfF : f ∈ F :=
    other_point_mem_of_inter_two hBset' hBF heF haF hbF
  have hgF : g ∈ F :=
    other_point_mem_of_inter_two hCset' hCF heF haF hcF
  rcases exists_fourth_of_card_four heF hfF hgF hef heg hfg hFcard with
    ⟨h, hhF, hhe, hhf, hhg, hFset⟩
  have hha : h ≠ a := by
    intro hEq
    apply haF
    rw [← hEq]
    exact hhF
  have hhb : h ≠ b := by
    intro hEq
    apply hbF
    rw [← hEq]
    exact hhF
  have hhc : h ≠ c₀ := by
    intro hEq
    apply hcF
    rw [← hEq]
    exact hhF
  exact ⟨h, hDset, hFset, hha, hhb, hhc, hhe, hhf, hhg⟩




/-- Constituent membership makes a Section-4 `ν` a member of `B′(χ)`. -/
private lemma BPrime_of_involved (h12 : Hyp12 c) {ν : Irr (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (hνt : ν.1 (tH0 c) = ν.1 1) {χ : Irr G}
    (hχ : χ ∈ involved (deltaNu c h12 ν)) :
    ν ∈ BPrimeOf c h12 χ.1 := by
  rw [BPrimeOf]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ ν, hνs, hνt,
    (mem_involved_iff (deltaNu c h12 ν) χ).1 hχ⟩

/-- In the fixed case, two distinct deltas in the same component share at
most two irreducible constituents: parity excludes four shared, and
orthogonality excludes three. -/
private lemma involved_inter_card_le_two_of_fixed (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {μ ν : Irr (↥c.H0)}
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1)
    (hμt : μ.1 (tH0 c) = μ.1 1)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (hνt : ν.1 (tH0 c) = ν.1 1)
    (hfixed : (nuHatOrbit c h12 (nuHat c h12 μ)).card = 1)
    (hneδ : deltaNu c h12 μ ≠ deltaNu c h12 ν) :
    ((involved (deltaNu c h12 μ) ∩ involved (deltaNu c h12 ν)).card ≤ 2) := by
  classical
  let δμ : ClassFunction G := deltaNu c h12 μ
  let δν : ClassFunction G := deltaNu c h12 ν
  have hneν : μ ≠ ν := by
    intro hEq
    exact hneδ (by rw [hEq])
  have horth := deltaNu_orthogonal c h12 hSC hS4 hμs hμt hνs hνt hneν
  rcases signed_four_decomp_fin c h12 hSC hS4 hμs with ⟨a, s, ha, hainj, hs, hδμs⟩
  rcases signed_four_decomp_fin c h12 hSC hS4 hνs with ⟨b, t, hb, hbinj, ht, hδνs⟩
  by_contra hgt
  have hgt' : ¬ (involved δμ ∩ involved δν).card ≤ 2 := by
    simpa [δμ, δν] using hgt
  have h3 : 3 ≤ (involved δμ ∩ involved δν).card := by omega
  have hcard_le : (involved δμ ∩ involved δν).card ≤ 4 := by
    have hle := Finset.card_le_card
      (Finset.inter_subset_left : involved δμ ∩ involved δν ⊆ involved δμ)
    rw [involved_deltaNu_card_eq_four c h12 hSC hS4 hμs] at hle
    exact hle
  have hnot3 : (involved δμ ∩ involved δν).card ≠ 3 := by
    intro hc
    have hodd : Odd ((involved δμ ∩ involved δν).card) := by
      rw [hc]
      decide
    exact scalarProduct_ne_zero_of_inter_card_odd ha hainj hs hδμs hb hbinj ht hδνs
      (by simpa [δμ, δν] using hodd)
      (by simpa [δμ, δν] using horth)
  have hnot4 : (involved δμ ∩ involved δν).card ≠ 4 := by
    intro hc
    have hEqInter : involved δμ ∩ involved δν = involved δμ := by
      apply Finset.eq_of_subset_of_card_le
        (Finset.inter_subset_left : involved δμ ∩ involved δν ⊆ involved δμ)
      rw [hc, involved_deltaNu_card_eq_four c h12 hSC hS4 hμs]
    have hsub : involved δμ ⊆ involved δν := by
      rw [← hEqInter]
      exact Finset.inter_subset_right
    have hEqInv : involved δμ = involved δν :=
      Finset.eq_of_subset_of_card_le hsub (by
        rw [involved_deltaNu_card_eq_four c h12 hSC hS4 hνs,
          involved_deltaNu_card_eq_four c h12 hSC hS4 hμs])
    rcases coeff_vector_of_signed_four ha hainj hs hδμs hb hbinj ht hδνs hEqInv.symm with
      ⟨u, hu, hδνu⟩
    rcases exists_odd_multiplicity_of_fixed_sum c h12 hSC hS4 hμs hμt hfixed with
      ⟨μ', hμ'char, hrule⟩
    have hoddRule := hrule
      {ν} (fun _ => -1) 1
      (by
        intro ν' hν'
        simp at hν'
        subst ν'
        exact ⟨hνs, hνt, hneν.symm⟩)
      (by norm_num)
    rcases hoddRule with ⟨χ, hχ, m, hm, hOddm⟩
    have hφ : ((1 : ℂ) • deltaNu c h12 μ + ∑ ν' ∈ ({ν} : Finset (Irr (↥c.H0))),
        ((-1 : ℤ) : ℂ) • deltaNu c h12 ν') =
        deltaNu c h12 μ - deltaNu c h12 ν := by
      ext x
      simp
      ring
    have hm' : (m : ℂ) = scalarProduct G χ (deltaNu c h12 μ - deltaNu c h12 ν) := by
      simpa [hφ, sub_eq_add_neg] using hm
    have heven := scalarProduct_even_of_signed_four_eq ha hainj hs hδμs hu
      (by simpa [δμ, δν] using hδνu) χ hχ
    rcases heven with ⟨k, hk, hEvenk⟩
    have hEqmk : m = k := by
      have hℂ : (m : ℂ) = (k : ℂ) := by
        rw [hm']
        exact hk.symm
      exact_mod_cast hℂ
    have hEvenm : Even m := by
      rwa [hEqmk]
    exact (Int.not_even_iff_odd).2 hOddm hEvenm
  omega


/-- If `B′(χ)` contains two distinct members, it has exactly three. -/
private lemma BPrime_card_eq_three_of_two (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {χ : Irr G} (hχ : IsPMIrr G χ.1)
    {ν₁ ν₂ : Irr (↥c.H0)}
    (hν₁B : ν₁ ∈ BPrimeOf c h12 χ.1) (hν₂B : ν₂ ∈ BPrimeOf c h12 χ.1)
    (hν₁₂ : ν₁ ≠ ν₂) :
    (BPrimeOf c h12 χ.1).card = 3 := by
  have hB' : (BPrimeOf c h12 χ.1).Nonempty := ⟨ν₁, hν₁B⟩
  rcases (lemma_4_1 c h12 hSC hS4 (χ := χ.1) hχ hB').1 with h1 | h3
  · rcases Finset.card_eq_one.mp h1 with ⟨γ, hγ⟩
    have hν₁γ : ν₁ = γ := by
      rw [hγ] at hν₁B
      simpa using hν₁B
    have hν₂γ : ν₂ = γ := by
      rw [hγ] at hν₂B
      simpa using hν₂B
    exact False.elim (hν₁₂ (hν₁γ.trans hν₂γ.symm))
  · exact h3

/-- A third member of `B′(χ)` distinct from two given distinct members. -/
private lemma exists_third_BPrime (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {χ : Irr G} (hχ : IsPMIrr G χ.1)
    {ν₁ ν₂ : Irr (↥c.H0)}
    (hν₁B : ν₁ ∈ BPrimeOf c h12 χ.1) (hν₂B : ν₂ ∈ BPrimeOf c h12 χ.1)
    (hν₁₂ : ν₁ ≠ ν₂) :
    ∃ ν₃ : Irr (↥c.H0),
      ν₃ ∈ BPrimeOf c h12 χ.1 ∧ ν₁ ≠ ν₃ ∧ ν₂ ≠ ν₃ := by
  classical
  have hcard := BPrime_card_eq_three_of_two c h12 hSC hS4 hχ hν₁B hν₂B hν₁₂
  let S : Finset (Irr (↥c.H0)) := ((BPrimeOf c h12 χ.1).erase ν₁).erase ν₂
  have hν₂erase : ν₂ ∈ (BPrimeOf c h12 χ.1).erase ν₁ := by
    rw [Finset.mem_erase]
    exact ⟨hν₁₂.symm, hν₂B⟩
  have hS_card : S.card = 1 := by
    have h1 : ((BPrimeOf c h12 χ.1).erase ν₁).card = 2 := by
      rw [Finset.card_erase_of_mem hν₁B, hcard]
    have h2 : (((BPrimeOf c h12 χ.1).erase ν₁).erase ν₂).card = 1 := by
      rw [Finset.card_erase_of_mem hν₂erase, h1]
    simpa [S] using h2
  rcases Finset.card_eq_one.mp hS_card with ⟨ν₃, hν₃eq⟩
  have hν₃S : ν₃ ∈ S := by
    rw [hν₃eq]
    simp
  have hν₃B : ν₃ ∈ BPrimeOf c h12 χ.1 := by
    rw [Finset.mem_erase] at hν₃S
    rcases hν₃S with ⟨hν₃₂, hν₃in⟩
    rw [Finset.mem_erase] at hν₃in
    exact hν₃in.2
  have hν₁₃ : ν₁ ≠ ν₃ := by
    rw [Finset.mem_erase] at hν₃S
    rcases hν₃S with ⟨hν₃₂, hν₃in⟩
    rw [Finset.mem_erase] at hν₃in
    exact hν₃in.1.symm
  have hν₂₃ : ν₂ ≠ ν₃ := by
    rw [Finset.mem_erase] at hν₃S
    rcases hν₃S with ⟨hν₃₂, hν₃in⟩
    exact hν₃₂.symm
  exact ⟨ν₃, hν₃B, hν₁₃, hν₂₃⟩

/-- Adjacent fixed deltas share exactly two irreducible constituents. -/
private lemma involved_inter_card_eq_two_of_adjacent_fixed (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {μ ν : Irr (↥c.H0)}
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1)
    (hμt : μ.1 (tH0 c) = μ.1 1)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (hνt : ν.1 (tH0 c) = ν.1 1)
    (hfixed : (nuHatOrbit c h12 (nuHat c h12 μ)).card = 1)
    (hneδ : deltaNu c h12 μ ≠ deltaNu c h12 ν)
    (hshare : ∃ χ : Irr G, χ ∈ involved (deltaNu c h12 μ) ∧
      χ ∈ involved (deltaNu c h12 ν)) :
    ((involved (deltaNu c h12 μ) ∩ involved (deltaNu c h12 ν)).card = 2) := by
  classical
  have hle := involved_inter_card_le_two_of_fixed c h12 hSC hS4
    hμs hμt hνs hνt hfixed hneδ
  have hneν : μ ≠ ν := by
    intro hEq
    exact hneδ (by rw [hEq])
  have horth := deltaNu_orthogonal c h12 hSC hS4 hμs hμt hνs hνt hneν
  have hnot1 : (involved (deltaNu c h12 μ) ∩ involved (deltaNu c h12 ν)).card ≠ 1 := by
    intro hc
    rcases signed_four_decomp_fin c h12 hSC hS4 hμs with ⟨a, s, ha, hainj, hs, hδμs⟩
    rcases signed_four_decomp_fin c h12 hSC hS4 hνs with ⟨b, t, hb, hbinj, ht, hδνs⟩
    have hodd : Odd ((involved (deltaNu c h12 μ) ∩ involved (deltaNu c h12 ν)).card) := by
      rw [hc]
      decide
    exact scalarProduct_ne_zero_of_inter_card_odd ha hainj hs hδμs hb hbinj ht hδνs
      hodd horth
  have hpos : 0 < (involved (deltaNu c h12 μ) ∩ involved (deltaNu c h12 ν)).card := by
    rcases hshare with ⟨χ, hχμ, hχν⟩
    have hmem : χ ∈ (involved (deltaNu c h12 μ) ∩ involved (deltaNu c h12 ν)) := by
      rw [Finset.mem_inter]
      exact ⟨hχμ, hχν⟩
    exact Finset.card_pos.mpr ⟨χ, hmem⟩
  omega

/-- If `B′(χ)` already has three distinct members, a fourth member cannot
exist. -/
private lemma not_fourth_BPrime (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) {χ : Irr G} (hχ : IsPMIrr G χ.1)
    {ν₁ ν₂ ν₃ ν : Irr (↥c.H0)}
    (hν₁B : ν₁ ∈ BPrimeOf c h12 χ.1) (hν₂B : ν₂ ∈ BPrimeOf c h12 χ.1)
    (hν₃B : ν₃ ∈ BPrimeOf c h12 χ.1)
    (hν₁₂ : ν₁ ≠ ν₂) (hν₁₃ : ν₁ ≠ ν₃) (hν₂₃ : ν₂ ≠ ν₃)
    (hνB : ν ∈ BPrimeOf c h12 χ.1)
    (hν₁ : ν ≠ ν₁) (hν₂ : ν ≠ ν₂) (hν₃ : ν ≠ ν₃) :
    False := by
  have hcard := BPrime_card_eq_three_of_two c h12 hSC hS4 hχ hν₁B hν₂B hν₁₂
  rcases Finset.card_eq_three.mp hcard with ⟨α, β, γ, hαβ, hαγ, hβγ, hset⟩
  have hsub : ({ν₁, ν₂, ν₃} : Finset (Irr (↥c.H0))) ⊆
      ({α, β, γ} : Finset (Irr (↥c.H0))) := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · rw [← hset]
      exact hν₁B
    · rw [← hset]
      exact hν₂B
    · rw [← hset]
      exact hν₃B
  have hsrc_card : ({ν₁, ν₂, ν₃} : Finset (Irr (↥c.H0))).card = 3 := by
    have h₁not : ν₁ ∉ ({ν₂, ν₃} : Finset (Irr (↥c.H0))) := by
      rw [Finset.mem_insert, Finset.mem_singleton]
      intro h
      rcases h with h | h
      · exact hν₁₂ h
      · exact hν₁₃ h
    have h₂not : ν₂ ∉ ({ν₃} : Finset (Irr (↥c.H0))) := by
      rw [Finset.mem_singleton]
      intro h
      exact hν₂₃ h
    rw [Finset.card_insert_of_notMem h₁not,
      Finset.card_insert_of_notMem h₂not, Finset.card_singleton]
  have htarget_card : ({α, β, γ} : Finset (Irr (↥c.H0))).card = 3 := by
    rw [← hset, hcard]
  have hEqSet : ({ν₁, ν₂, ν₃} : Finset (Irr (↥c.H0))) =
      ({α, β, γ} : Finset (Irr (↥c.H0))) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hsrc_card, htarget_card])
  have hνs : ν ∈ ({ν₁, ν₂, ν₃} : Finset (Irr (↥c.H0))) := by
    have hνsα : ν ∈ ({α, β, γ} : Finset (Irr (↥c.H0))) := by
      rw [← hset]
      exact hνB
    rwa [← hEqSet] at hνsα
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hνs
  rcases hνs with rfl | rfl | rfl
  · exact hν₁ rfl
  · exact hν₂ rfl
  · exact hν₃ rfl

/-- A fourth delta for a constituent whose `B′(χ)` is already full cannot
contain that constituent. -/
private lemma not_involved_of_fourth (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) {ν : Irr (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (hνt : ν.1 (tH0 c) = ν.1 1) {χ : Irr G}
    (hχ : IsPMIrr G χ.1) {ν₁ ν₂ ν₃ : Irr (↥c.H0)}
    (hν₁B : ν₁ ∈ BPrimeOf c h12 χ.1) (hν₂B : ν₂ ∈ BPrimeOf c h12 χ.1)
    (hν₃B : ν₃ ∈ BPrimeOf c h12 χ.1)
    (hν₁₂ : ν₁ ≠ ν₂) (hν₁₃ : ν₁ ≠ ν₃) (hν₂₃ : ν₂ ≠ ν₃)
    (hν₁ : ν ≠ ν₁) (hν₂ : ν ≠ ν₂) (hν₃ : ν ≠ ν₃) :
    χ ∉ involved (deltaNu c h12 ν) := by
  intro hχδ
  have hνB : ν ∈ BPrimeOf c h12 χ.1 := BPrime_of_involved c h12 hνs hνt hχδ
  exact not_fourth_BPrime c h12 hSC hS4 hχ hν₁B hν₂B hν₃B
    hν₁₂ hν₁₃ hν₂₃ hνB hν₁ hν₂ hν₃

/-- Given two distinct fixed deltas sharing a constituent, there is a third
delta in the component containing that constituent. -/
private lemma exists_fixed_third_delta_of_shared (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {Δ0 : Set (ClassFunction G)} (hcomp : IsConnectedComponent c h12 Δ0)
    {ν₁ ν₂ : Irr (↥c.H0)} {χ : Irr G}
    (hν₁Δ0 : deltaNu c h12 ν₁ ∈ Δ0)
    (hν₁s : conjChar c.H0 (s_normalizes_H0 c h12) ν₁.1 = ν₁.1)
    (hν₁t : ν₁.1 (tH0 c) = ν₁.1 1)
    (hν₂s : conjChar c.H0 (s_normalizes_H0 c h12) ν₂.1 = ν₂.1)
    (hν₂t : ν₂.1 (tH0 c) = ν₂.1 1)
    (hfix₁ : (nuHatOrbit c h12 (nuHat c h12 ν₁)).card = 1)
    (hfix₂ : (nuHatOrbit c h12 (nuHat c h12 ν₂)).card = 1)
    (hχ₁ : χ ∈ involved (deltaNu c h12 ν₁))
    (hχ₂ : χ ∈ involved (deltaNu c h12 ν₂))
    (hν₁₂ : ν₁ ≠ ν₂) :
    ∃ ν₃ : Irr (↥c.H0),
      ν₃ ∈ BPrimeOf c h12 χ.1 ∧ ν₁ ≠ ν₃ ∧ ν₂ ≠ ν₃ ∧
      deltaNu c h12 ν₃ ∈ Δ0 ∧
      (involved (deltaNu c h12 ν₁) ∩ involved (deltaNu c h12 ν₃)).card = 2 ∧
      (involved (deltaNu c h12 ν₂) ∩ involved (deltaNu c h12 ν₃)).card = 2 := by
  classical
  have hχpm : IsPMIrr G χ.1 := Or.inl χ.2
  have hν₁B : ν₁ ∈ BPrimeOf c h12 χ.1 := by
    rw [BPrimeOf]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ ν₁, hν₁s, hν₁t,
      (mem_involved_iff (deltaNu c h12 ν₁) χ).1 hχ₁⟩
  have hν₂B : ν₂ ∈ BPrimeOf c h12 χ.1 := by
    rw [BPrimeOf]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ ν₂, hν₂s, hν₂t,
      (mem_involved_iff (deltaNu c h12 ν₂) χ).1 hχ₂⟩
  rcases exists_third_BPrime c h12 hSC hS4 hχpm hν₁B hν₂B hν₁₂ with
    ⟨ν₃, hν₃B, hν₁₃, hν₂₃⟩
  have hν₃s : conjChar c.H0 (s_normalizes_H0 c h12) ν₃.1 = ν₃.1 :=
    (Finset.mem_filter.mp hν₃B).2.1
  have hν₃t : ν₃.1 (tH0 c) = ν₃.1 1 :=
    (Finset.mem_filter.mp hν₃B).2.2.1
  have hχ₃ : χ ∈ involved (deltaNu c h12 ν₃) := by
    rw [mem_involved_iff]
    exact (Finset.mem_filter.mp hν₃B).2.2.2
  have hδ₃Δ0 : deltaNu c h12 ν₃ ∈ Δ0 :=
    deltaNu_mem_Delta0_of_BPrime c h12 hcomp hν₁Δ0 hχ₁ hν₃B
  have hδ₁₃ : deltaNu c h12 ν₁ ≠ deltaNu c h12 ν₃ := by
    intro hEq
    exact hν₁₃ (deltaNu_injective c h12 hSC hS4 hν₁s hν₁t hν₃s hν₃t hEq)
  have hδ₂₃ : deltaNu c h12 ν₂ ≠ deltaNu c h12 ν₃ := by
    intro hEq
    exact hν₂₃ (deltaNu_injective c h12 hSC hS4 hν₂s hν₂t hν₃s hν₃t hEq)
  have hpair₁ : (involved (deltaNu c h12 ν₁) ∩ involved (deltaNu c h12 ν₃)).card = 2 :=
    involved_inter_card_eq_two_of_adjacent_fixed c h12 hSC hS4
      hν₁s hν₁t hν₃s hν₃t hfix₁ hδ₁₃ ⟨χ, hχ₁, hχ₃⟩
  have hpair₂ : (involved (deltaNu c h12 ν₂) ∩ involved (deltaNu c h12 ν₃)).card = 2 :=
    involved_inter_card_eq_two_of_adjacent_fixed c h12 hSC hS4
      hν₂s hν₂t hν₃s hν₃t hfix₂ hδ₂₃ ⟨χ, hχ₂, hχ₃⟩
  exact ⟨ν₃, hν₃B, hν₁₃, hν₂₃, hδ₃Δ0, hpair₁, hpair₂⟩

/-- From the first three fixed deltas, name the seven-point incidence
partition. -/
private lemma fixed_incidence_three_partition (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {ν₁ ν₂ ν₃ : Irr (↥c.H0)} {χ : Irr G}
    (hν₁s : conjChar c.H0 (s_normalizes_H0 c h12) ν₁.1 = ν₁.1)
    (hν₂s : conjChar c.H0 (s_normalizes_H0 c h12) ν₂.1 = ν₂.1)
    (hν₃s : conjChar c.H0 (s_normalizes_H0 c h12) ν₃.1 = ν₃.1)
    (hχ₁ : χ ∈ involved (deltaNu c h12 ν₁))
    (hχ₂ : χ ∈ involved (deltaNu c h12 ν₂))
    (hχ₃ : χ ∈ involved (deltaNu c h12 ν₃))
    (hpair12 : (involved (deltaNu c h12 ν₁) ∩ involved (deltaNu c h12 ν₂)).card = 2)
    (hpair13 : (involved (deltaNu c h12 ν₁) ∩ involved (deltaNu c h12 ν₃)).card = 2)
    (hpair23 : (involved (deltaNu c h12 ν₂) ∩ involved (deltaNu c h12 ν₃)).card = 2)
    (hABC : ((involved (deltaNu c h12 ν₁) ∩ involved (deltaNu c h12 ν₂)) ∩
      involved (deltaNu c h12 ν₃)).card = 1) :
    ∃ a b c₀ d e f g : Irr G,
      a ∈ involved (deltaNu c h12 ν₁) ∩ involved (deltaNu c h12 ν₂) ∩
        involved (deltaNu c h12 ν₃) ∧
      b ∈ (involved (deltaNu c h12 ν₁) ∩ involved (deltaNu c h12 ν₂)) \
        involved (deltaNu c h12 ν₃) ∧
      c₀ ∈ (involved (deltaNu c h12 ν₁) ∩ involved (deltaNu c h12 ν₃)) \
        involved (deltaNu c h12 ν₂) ∧
      d ∈ involved (deltaNu c h12 ν₁) \
        (involved (deltaNu c h12 ν₂) ∪ involved (deltaNu c h12 ν₃)) ∧
      e ∈ (involved (deltaNu c h12 ν₂) ∩ involved (deltaNu c h12 ν₃)) \
        involved (deltaNu c h12 ν₁) ∧
      f ∈ involved (deltaNu c h12 ν₂) \
        (involved (deltaNu c h12 ν₁) ∪ involved (deltaNu c h12 ν₃)) ∧
      g ∈ involved (deltaNu c h12 ν₃) \
        (involved (deltaNu c h12 ν₁) ∪ involved (deltaNu c h12 ν₂)) ∧
      a ≠ b ∧ a ≠ c₀ ∧ a ≠ d ∧ b ≠ c₀ ∧ b ≠ d ∧ c₀ ≠ d ∧
      a ≠ e ∧ a ≠ f ∧ a ≠ g ∧ b ≠ e ∧ b ≠ f ∧ b ≠ g ∧
      c₀ ≠ e ∧ c₀ ≠ f ∧ c₀ ≠ g ∧ d ≠ e ∧ d ≠ f ∧ d ≠ g ∧
      e ≠ f ∧ e ≠ g ∧ f ≠ g := by
  classical
  let A : Finset (Irr G) := involved (deltaNu c h12 ν₁)
  let B : Finset (Irr G) := involved (deltaNu c h12 ν₂)
  let C : Finset (Irr G) := involved (deltaNu c h12 ν₃)
  have hA : A.card = 4 := by simpa [A] using involved_deltaNu_card_eq_four c h12 hSC hS4 hν₁s
  have hB : B.card = 4 := by simpa [B] using involved_deltaNu_card_eq_four c h12 hSC hS4 hν₂s
  have hC : C.card = 4 := by simpa [C] using involved_deltaNu_card_eq_four c h12 hSC hS4 hν₃s
  have hAB : (A ∩ B).card = 2 := by simpa [A, B] using hpair12
  have hAC : (A ∩ C).card = 2 := by simpa [A, C] using hpair13
  have hBC : (B ∩ C).card = 2 := by simpa [B, C] using hpair23
  have hABC' : (A ∩ B ∩ C).card = 1 := by simpa [A, B, C] using hABC
  rcases exists_partition_abcdefg A B C hA hB hC hAB hAC hBC hABC' with
    ⟨a, b, c₀, d, e, f, g, ha, hb, hc₀, hd, he, hf, hg,
      hab, hac, had, hbc, hbd, hcd,
      hae, haf, hag, hbe, hbf, hbg,
      hce, hcf, hcg, hde, hdf, hdg,
      hef, heg, hfg⟩
  exact ⟨a, b, c₀, d, e, f, g,
    by simpa [A, B, C] using ha,
    by simpa [A, B, C] using hb,
    by simpa [A, B, C] using hc₀,
    by simpa [A, B, C] using hd,
    by simpa [A, B, C] using he,
    by simpa [A, B, C] using hf,
    by simpa [A, B, C] using hg,
    hab, hac, had, hbc, hbd, hcd,
    hae, haf, hag, hbe, hbf, hbg,
    hce, hcf, hcg, hde, hdf, hdg,
    hef, heg, hfg⟩

/-- The first three fixed deltas of the incidence construction, with the
full seven-point partition. -/
private lemma fixed_incidence_three_deltas (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {Δ0 : Set (ClassFunction G)} (hcomp : IsConnectedComponent c h12 Δ0)
    {ν₁ ν₂ : Irr (↥c.H0)} {χ : Irr G}
    (hν₁Δ0 : deltaNu c h12 ν₁ ∈ Δ0)
    (hν₁s : conjChar c.H0 (s_normalizes_H0 c h12) ν₁.1 = ν₁.1)
    (hν₁t : ν₁.1 (tH0 c) = ν₁.1 1)
    (hν₂s : conjChar c.H0 (s_normalizes_H0 c h12) ν₂.1 = ν₂.1)
    (hν₂t : ν₂.1 (tH0 c) = ν₂.1 1)
    (hfix₁ : (nuHatOrbit c h12 (nuHat c h12 ν₁)).card = 1)
    (hfix₂ : (nuHatOrbit c h12 (nuHat c h12 ν₂)).card = 1)
    (hχ₁ : χ ∈ involved (deltaNu c h12 ν₁))
    (hχ₂ : χ ∈ involved (deltaNu c h12 ν₂))
    (hν₁₂ : ν₁ ≠ ν₂) :
    ∃ ν₃ : Irr (↥c.H0), ∃ a b c₀ d e f g : Irr G,
      ν₃ ∈ BPrimeOf c h12 χ.1 ∧ deltaNu c h12 ν₃ ∈ Δ0 ∧
      a ∈ involved (deltaNu c h12 ν₁) ∩ involved (deltaNu c h12 ν₂) ∩
        involved (deltaNu c h12 ν₃) ∧
      b ∈ (involved (deltaNu c h12 ν₁) ∩ involved (deltaNu c h12 ν₂)) \
        involved (deltaNu c h12 ν₃) ∧
      c₀ ∈ (involved (deltaNu c h12 ν₁) ∩ involved (deltaNu c h12 ν₃)) \
        involved (deltaNu c h12 ν₂) ∧
      d ∈ involved (deltaNu c h12 ν₁) \
        (involved (deltaNu c h12 ν₂) ∪ involved (deltaNu c h12 ν₃)) ∧
      e ∈ (involved (deltaNu c h12 ν₂) ∩ involved (deltaNu c h12 ν₃)) \
        involved (deltaNu c h12 ν₁) ∧
      f ∈ involved (deltaNu c h12 ν₂) \
        (involved (deltaNu c h12 ν₁) ∪ involved (deltaNu c h12 ν₃)) ∧
      g ∈ involved (deltaNu c h12 ν₃) \
        (involved (deltaNu c h12 ν₁) ∪ involved (deltaNu c h12 ν₂)) ∧
      a ≠ b ∧ a ≠ c₀ ∧ a ≠ d ∧ b ≠ c₀ ∧ b ≠ d ∧ c₀ ≠ d ∧
      a ≠ e ∧ a ≠ f ∧ a ≠ g ∧ b ≠ e ∧ b ≠ f ∧ b ≠ g ∧
      c₀ ≠ e ∧ c₀ ≠ f ∧ c₀ ≠ g ∧ d ≠ e ∧ d ≠ f ∧ d ≠ g ∧
      e ≠ f ∧ e ≠ g ∧ f ≠ g := by
  classical
  rcases exists_fixed_third_delta_of_shared c h12 hSC hS4 hcomp
    hν₁Δ0 hν₁s hν₁t hν₂s hν₂t hfix₁ hfix₂ hχ₁ hχ₂ hν₁₂ with
    ⟨ν₃, hν₃B, hν₁₃, hν₂₃, hδ₃Δ0, hpair13, hpair23⟩
  have hν₃s : conjChar c.H0 (s_normalizes_H0 c h12) ν₃.1 = ν₃.1 :=
    (Finset.mem_filter.mp hν₃B).2.1
  have hν₃t : ν₃.1 (tH0 c) = ν₃.1 1 :=
    (Finset.mem_filter.mp hν₃B).2.2.1
  have hχ₃ : χ ∈ involved (deltaNu c h12 ν₃) := by
    rw [mem_involved_iff]
    exact (Finset.mem_filter.mp hν₃B).2.2.2
  have hδ₁₂ : deltaNu c h12 ν₁ ≠ deltaNu c h12 ν₂ := by
    intro hEq
    exact hν₁₂ (deltaNu_injective c h12 hSC hS4 hν₁s hν₁t hν₂s hν₂t hEq)
  have hpair12 : (involved (deltaNu c h12 ν₁) ∩ involved (deltaNu c h12 ν₂)).card = 2 :=
    involved_inter_card_eq_two_of_adjacent_fixed c h12 hSC hS4
      hν₁s hν₁t hν₂s hν₂t hfix₁ hδ₁₂ ⟨χ, hχ₁, hχ₂⟩
  have horth12 : scalarProduct G (deltaNu c h12 ν₁) (deltaNu c h12 ν₂) = 0 :=
    deltaNu_orthogonal c h12 hSC hS4 hν₁s hν₁t hν₂s hν₂t hν₁₂
  have horth13 : scalarProduct G (deltaNu c h12 ν₁) (deltaNu c h12 ν₃) = 0 :=
    deltaNu_orthogonal c h12 hSC hS4 hν₁s hν₁t hν₃s hν₃t hν₁₃
  have horth23 : scalarProduct G (deltaNu c h12 ν₂) (deltaNu c h12 ν₃) = 0 :=
    deltaNu_orthogonal c h12 hSC hS4 hν₂s hν₂t hν₃s hν₃t hν₂₃
  rcases signed_four_decomp_fin c h12 hSC hS4 hν₁s with ⟨a₁, s₁, ha₁, hainj₁, hs₁, hδ₁⟩
  rcases signed_four_decomp_fin c h12 hSC hS4 hν₂s with ⟨a₂, s₂, ha₂, hainj₂, hs₂, hδ₂⟩
  rcases signed_four_decomp_fin c h12 hSC hS4 hν₃s with ⟨a₃, s₃, ha₃, hainj₃, hs₃, hδ₃⟩
  have hχmem : χ ∈ ((involved (deltaNu c h12 ν₁) ∩ involved (deltaNu c h12 ν₂)) ∩
      involved (deltaNu c h12 ν₃)) := by
    rw [Finset.mem_inter]
    constructor
    · rw [Finset.mem_inter]
      exact ⟨hχ₁, hχ₂⟩
    · exact hχ₃
  have hABC : ((involved (deltaNu c h12 ν₁) ∩ involved (deltaNu c h12 ν₂)) ∩
      involved (deltaNu c h12 ν₃)).card = 1 :=
    triple_inter_card_eq_one_of_pairwise_orthogonal
      ha₁ hainj₁ hs₁ hδ₁ ha₂ hainj₂ hs₂ hδ₂ ha₃ hainj₃ hs₃ hδ₃
      horth12 horth13 horth23 hpair12 hpair13 hpair23 hχmem
  rcases fixed_incidence_three_partition c h12 hSC hS4
    hν₁s hν₂s hν₃s hχ₁ hχ₂ hχ₃ hpair12 hpair13 hpair23 hABC with
    ⟨a, b, c₀, d, e, f, g, ha, hb, hc, hd, he, hf, hg,
      hab, hac, had, hbc, hbd, hcd,
      hae, haf, hag, hbe, hbf, hbg,
      hce, hcf, hcg, hde, hdf, hdg,
      hef, heg, hfg⟩
  exact ⟨ν₃, a, b, c₀, d, e, f, g, hν₃B, hδ₃Δ0, ha, hb, hc, hd, he, hf, hg,
    hab, hac, had, hbc, hbd, hcd,
    hae, haf, hag, hbe, hbf, hbg,
    hce, hcf, hcg, hde, hdf, hdg,
    hef, heg, hfg⟩


/-- The graph `Delta` is finite. -/
private lemma Delta_finite (h12 : Hyp12 c) : (Delta c h12).Finite := by
  classical
  have hEq : Delta c h12 =
      (fun ν : Irr (↥c.H0) => deltaNu c h12 ν) ''
        {ν : Irr (↥c.H0) |
          conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 ∧
            ν.1 (tH0 c) = ν.1 1} := by
    ext δ
    constructor
    · rintro ⟨ν, hνs, hνt, rfl⟩
      exact ⟨ν, ⟨hνs, hνt⟩, rfl⟩
    · rintro ⟨ν, hν, rfl⟩
      exact ⟨ν, hν.1, hν.2, rfl⟩
  rw [hEq]
  exact Set.Finite.image _ (Set.toFinite _)

/-- A connected component with `ncard ≠ 1` has two distinct vertices. -/
private lemma exists_two_distinct_of_ncard_ne_one (c : Hyp11 G)
    (h12 : Hyp12 c) {Δ0 : Set (ClassFunction G)}
    (hcomp : IsConnectedComponent c h12 Δ0) (hcard : Δ0.ncard ≠ 1) :
    ∃ δ ε : ClassFunction G, δ ∈ Δ0 ∧ ε ∈ Δ0 ∧ δ ≠ ε := by
  classical
  rcases hcomp.1 with ⟨δ₀, hδ₀⟩
  by_contra hnone
  have hfin : Δ0.Finite := (Delta_finite c h12).subset hcomp.2.1
  have hle : Δ0.ncard ≤ 1 := (Set.ncard_le_one hfin).2 (by
    intro a ha b hb
    by_contra hne
    exact hnone ⟨a, b, ha, hb, hne⟩)
  have hpos : 0 < Δ0.ncard := (Set.ncard_pos hfin).2 hcomp.1
  omega

/-- Two distinct vertices in the same component have an adjacent pair. -/
private lemma exists_adjacent_pair_of_two (c : Hyp11 G) (h12 : Hyp12 c)
    {Δ0 : Set (ClassFunction G)} (hcomp : IsConnectedComponent c h12 Δ0)
    {δ₀ δ₁ : ClassFunction G} (hδ₀ : δ₀ ∈ Δ0) (hδ₁ : δ₁ ∈ Δ0)
    (hne : δ₀ ≠ δ₁) :
    ∃ δ ε : ClassFunction G, δ ∈ Δ0 ∧ ε ∈ Δ0 ∧ deltaAdjacent c h12 δ ε := by
  have hpath : Relation.ReflTransGen (deltaAdjacent c h12) δ₀ δ₁ :=
    hcomp.2.2.1 δ₀ δ₁ hδ₀ hδ₁
  have hall : ∀ {x : ClassFunction G},
      Relation.ReflTransGen (deltaAdjacent c h12) δ₀ x → x ∈ Δ0 := by
    intro x hx
    have hrev : Relation.ReflTransGen (deltaAdjacent c h12) x δ₀ :=
      reflTransGen_symm (fun {a b : ClassFunction G} h => deltaAdjacent_symm c h12 h) hx
    refine Relation.ReflTransGen.head_induction_on hrev
      (motive := fun y _ => y ∈ Δ0) ?base ?step
    · exact hδ₀
    · intro a c hadj hpath' ih
      by_contra hnot
      exact (hcomp.2.2.2 a hnot c ih) hadj
  match hpath with
  | Relation.ReflTransGen.refl => exact False.elim (hne rfl)
  | @Relation.ReflTransGen.tail _ _ _ b _ hprev hadj =>
      have hbΔ0 : b ∈ Δ0 := hall hprev
      exact ⟨b, δ₁, hbΔ0, hδ₁, hadj⟩


/-- In the non-fixed orbit case the component is exactly the three vertices
with the four shared signed irreducibles in the displayed patterns. -/
private lemma exists_signed_four_of_nonfixed (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {Δ0 : Set (ClassFunction G)} (hcomp : IsConnectedComponent c h12 Δ0)
    {μ : Irr (↥c.H0)}
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1)
    (hμt : μ.1 (tH0 c) = μ.1 1)
    (hμΔ0 : deltaNu c h12 μ ∈ Δ0)
    (horb : (nuHatOrbit c h12 (nuHat c h12 μ)).card = 3) :
    ∃ ν₁ ν₂ ν₃ : Irr (↥c.H0),
      deltaNu c h12 ν₁ ∈ Δ0 ∧ deltaNu c h12 ν₂ ∈ Δ0 ∧ deltaNu c h12 ν₃ ∈ Δ0 ∧
      deltaNu c h12 ν₁ ≠ deltaNu c h12 ν₂ ∧ deltaNu c h12 ν₂ ≠ deltaNu c h12 ν₃ ∧
      deltaNu c h12 ν₁ ≠ deltaNu c h12 ν₃ ∧
      nuHat c h12 ν₁ ∈ nuHatOrbit c h12 (nuHat c h12 μ) ∧
      nuHat c h12 ν₂ ∈ nuHatOrbit c h12 (nuHat c h12 μ) ∧
      nuHat c h12 ν₃ ∈ nuHatOrbit c h12 (nuHat c h12 μ) ∧
      Δ0 = ({deltaNu c h12 ν₁, deltaNu c h12 ν₂, deltaNu c h12 ν₃} : Set (ClassFunction G)) ∧
      ∃ χ₁ χ₂ χ₃ χ₄ : ClassFunction G,
        IsPMIrr G χ₁ ∧ IsPMIrr G χ₂ ∧ IsPMIrr G χ₃ ∧ IsPMIrr G χ₄ ∧
        scalarProduct G χ₁ χ₂ = 0 ∧ scalarProduct G χ₁ χ₃ = 0 ∧
        scalarProduct G χ₁ χ₄ = 0 ∧ scalarProduct G χ₂ χ₃ = 0 ∧
        scalarProduct G χ₂ χ₄ = 0 ∧ scalarProduct G χ₃ χ₄ = 0 ∧
        deltaNu c h12 ν₁ = χ₁ + χ₂ + χ₃ + χ₄ ∧
        deltaNu c h12 ν₂ = χ₁ - χ₂ + χ₃ - χ₄ ∧
        deltaNu c h12 ν₃ = χ₁ + χ₂ - χ₃ - χ₄ := by
  classical
  rcases exists_three_delta_of_nonfixed_orbit c h12 hSC hS4 hcomp hμs hμt hμΔ0 horb with
    ⟨ν₁, ν₂, ν₃, hδ₁, hδ₂, hδ₃, hδ₁₂, hδ₁₃, hδ₂₃,
      horb₁, horb₂, horb₃, χ, hχmem, hν₁B, hν₂B, hν₃B, hΔ0eq⟩
  have hν₁s : conjChar c.H0 (s_normalizes_H0 c h12) ν₁.1 = ν₁.1 := by
    rw [BPrimeOf] at hν₁B
    exact (Finset.mem_filter.mp hν₁B).2.1
  have hν₁t : ν₁.1 (tH0 c) = ν₁.1 1 := by
    rw [BPrimeOf] at hν₁B
    exact (Finset.mem_filter.mp hν₁B).2.2.1
  have hν₂s : conjChar c.H0 (s_normalizes_H0 c h12) ν₂.1 = ν₂.1 := by
    rw [BPrimeOf] at hν₂B
    exact (Finset.mem_filter.mp hν₂B).2.1
  have hν₂t : ν₂.1 (tH0 c) = ν₂.1 1 := by
    rw [BPrimeOf] at hν₂B
    exact (Finset.mem_filter.mp hν₂B).2.2.1
  have hν₃s : conjChar c.H0 (s_normalizes_H0 c h12) ν₃.1 = ν₃.1 := by
    rw [BPrimeOf] at hν₃B
    exact (Finset.mem_filter.mp hν₃B).2.1
  have hν₃t : ν₃.1 (tH0 c) = ν₃.1 1 := by
    rw [BPrimeOf] at hν₃B
    exact (Finset.mem_filter.mp hν₃B).2.2.1
  have hEq₁ : involved (deltaNu c h12 ν₁) = involved (deltaNu c h12 μ) :=
    involved_eq_of_orbit_of_nonfixed c h12 hSC hS4 hμs hμt hν₁s hν₁t horb horb₁
  have hEq₂ : involved (deltaNu c h12 ν₂) = involved (deltaNu c h12 μ) :=
    involved_eq_of_orbit_of_nonfixed c h12 hSC hS4 hμs hμt hν₂s hν₂t horb horb₂
  have hEq₃ : involved (deltaNu c h12 ν₃) = involved (deltaNu c h12 μ) :=
    involved_eq_of_orbit_of_nonfixed c h12 hSC hS4 hμs hμt hν₃s hν₃t horb horb₃
  have hEq₁₂ : involved (deltaNu c h12 ν₂) = involved (deltaNu c h12 ν₁) :=
    hEq₂.trans hEq₁.symm
  have hEq₁₃ : involved (deltaNu c h12 ν₃) = involved (deltaNu c h12 ν₁) :=
    hEq₃.trans hEq₁.symm
  rcases signed_four_decomp_fin c h12 hSC hS4 hν₁s with ⟨a, s, ha, hainj, hs, hδ₁sum⟩
  let chi : Fin 4 → ClassFunction G := fun i => (s i : ℂ) • a i
  have hchiPM : ∀ i, IsPMIrr G (chi i) := by
    intro i
    rcases hs i with h | h
    · left
      dsimp [chi]
      rw [h]
      simpa using ha i
    · right
      dsimp [chi]
      rw [h]
      simpa using ha i
  have hchiOrth : ∀ {i j}, i ≠ j → scalarProduct G (chi i) (chi j) = 0 := by
    intro i j hij
    dsimp [chi]
    rw [scalarProduct_smul_left, scalarProduct_smul_right]
    rw [scalarProduct_irr_ite (ha i) (ha j)]
    have hne : a i ≠ a j := by
      intro hEq
      exact hij (hainj hEq)
    simp [hne]
  have hδ₁chi : deltaNu c h12 ν₁ = ∑ i, chi i := by
    simpa [chi, Fin.sum_univ_four] using hδ₁sum
  rcases signed_four_decomp_fin c h12 hSC hS4 hν₂s with ⟨b, t, hb, hbinj, ht, hδ₂sum⟩
  rcases signed_four_decomp_fin c h12 hSC hS4 hν₃s with ⟨d, r, hd, hdinj, hr, hδ₃sum⟩
  rcases coeff_vector_of_signed_four ha hainj hs hδ₁sum hb hbinj ht hδ₂sum hEq₁₂ with
    ⟨u, hu, hδ₂chi⟩
  rcases coeff_vector_of_signed_four ha hainj hs hδ₁sum hd hdinj hr hδ₃sum hEq₁₃ with
    ⟨v, hv, hδ₃chi⟩
  have hδ₂chi' : deltaNu c h12 ν₂ = ∑ i, (u i : ℂ) • chi i := by
    simpa [chi] using hδ₂chi
  have hδ₃chi' : deltaNu c h12 ν₃ = ∑ i, (v i : ℂ) • chi i := by
    simpa [chi] using hδ₃chi
  have hν₁₂ : ν₁ ≠ ν₂ := by
    intro hEq
    exact hδ₁₂ (by rw [hEq])
  have hν₁₃ : ν₁ ≠ ν₃ := by
    intro hEq
    exact hδ₁₃ (by rw [hEq])
  have hν₂₃ : ν₂ ≠ ν₃ := by
    intro hEq
    exact hδ₂₃ (by rw [hEq])
  have h₁₂sp : scalarProduct G (deltaNu c h12 ν₁) (deltaNu c h12 ν₂) = 0 :=
    deltaNu_orthogonal c h12 hSC hS4 hν₁s hν₁t hν₂s hν₂t hν₁₂
  have h₁₃sp : scalarProduct G (deltaNu c h12 ν₁) (deltaNu c h12 ν₃) = 0 :=
    deltaNu_orthogonal c h12 hSC hS4 hν₁s hν₁t hν₃s hν₃t hν₁₃
  have h₂₃sp : scalarProduct G (deltaNu c h12 ν₂) (deltaNu c h12 ν₃) = 0 :=
    deltaNu_orthogonal c h12 hSC hS4 hν₂s hν₂t hν₃s hν₃t hν₂₃
  have h₂ : (∑ i, u i : ℤ) = 0 := by
    have hsum : (∑ i, (u i : ℂ)) = 0 := by
      have hsp : scalarProduct G (∑ i, chi i) (∑ i, (u i : ℂ) • chi i) =
          ∑ i, (u i : ℂ) := by
        rw [scalarProduct_sum_left]
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact scalarProduct_chi_sum hchiPM hchiOrth (u := u) i
      rw [← hδ₁chi, ← hδ₂chi'] at hsp
      rw [h₁₂sp] at hsp
      exact hsp.symm
    have hcast : ((∑ i, u i : ℤ) : ℂ) = ∑ i, (u i : ℂ) := by
      rw [Int.cast_sum]
    rw [← hcast] at hsum
    exact_mod_cast hsum
  have h₃ : (∑ i, v i : ℤ) = 0 := by
    have hsum : (∑ i, (v i : ℂ)) = 0 := by
      have hsp : scalarProduct G (∑ i, chi i) (∑ i, (v i : ℂ) • chi i) =
          ∑ i, (v i : ℂ) := by
        rw [scalarProduct_sum_left]
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact scalarProduct_chi_sum hchiPM hchiOrth (u := v) i
      rw [← hδ₁chi, ← hδ₃chi'] at hsp
      rw [h₁₃sp] at hsp
      exact hsp.symm
    have hcast : ((∑ i, v i : ℤ) : ℂ) = ∑ i, (v i : ℂ) := by
      rw [Int.cast_sum]
    rw [← hcast] at hsum
    exact_mod_cast hsum
  have h₂₃ : (∑ i, u i * v i : ℤ) = 0 := by
    have hsum : (∑ i, (u i : ℂ) * (v i : ℂ)) = 0 := by
      have hsp : scalarProduct G (∑ i, (u i : ℂ) • chi i) (∑ i, (v i : ℂ) • chi i) =
          ∑ i, (u i : ℂ) * (v i : ℂ) := by
        rw [scalarProduct_sum_left]
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [scalarProduct_smul_left]
        rw [scalarProduct_chi_sum hchiPM hchiOrth (u := v) i]
      rw [← hδ₂chi', ← hδ₃chi'] at hsp
      rw [h₂₃sp] at hsp
      exact hsp.symm
    have hcast : ((∑ i, u i * v i : ℤ) : ℂ) = ∑ i, (u i : ℂ) * (v i : ℂ) := by
      rw [Int.cast_sum]
      apply Finset.sum_congr rfl
      intro i hi
      norm_num
    rw [← hcast] at hsum
    exact_mod_cast hsum
  rcases signed_four_pattern hδ₁chi hδ₂chi' hδ₃chi' hu hv h₂ h₃ h₂₃ hchiPM hchiOrth with
    ⟨χ₁, χ₂, χ₃, χ₄, hpm₁, hpm₂, hpm₃, hpm₄,
      horth₁₂, horth₁₃, horth₁₄, horth₂₃, horth₂₄, horth₃₄,
      hpat₁, hpat₂, hpat₃⟩
  exact ⟨ν₁, ν₂, ν₃, hδ₁, hδ₂, hδ₃, hδ₁₂, hδ₂₃, hδ₁₃,
    horb₁, horb₂, horb₃, hΔ0eq,
    χ₁, χ₂, χ₃, χ₄, hpm₁, hpm₂, hpm₃, hpm₄,
    horth₁₂, horth₁₃, horth₁₄, horth₂₃, horth₂₄, horth₃₄,
    hpat₁, hpat₂, hpat₃⟩

/-- `ν ↦ ν̂` is injective on every `B′(χ)`. -/
private lemma nuHat_injective_on_BPrime (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c) {χ : ClassFunction G} :
    Set.InjOn (nuHat c h12) ↑(BPrimeOf c h12 χ) := by
  intro ν hνB ν' hν'B hEq
  have hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 :=
    (Finset.mem_filter.mp hνB).2.1
  have hνt : ν.1 (tH0 c) = ν.1 1 :=
    (Finset.mem_filter.mp hνB).2.2.1
  have hν's : conjChar c.H0 (s_normalizes_H0 c h12) ν'.1 = ν'.1 :=
    (Finset.mem_filter.mp hν'B).2.1
  have hν't : ν'.1 (tH0 c) = ν'.1 1 :=
    (Finset.mem_filter.mp hν'B).2.2.1
  exact nuHat_injective_on_Delta c h12 hSC hS4 hνs hνt hν's hν't hEq

/-- If `μ̂` is fixed and `χ` is involved in `δμ`, then every
`ν ∈ B′(χ)` also has fixed `ν̂`. -/
private lemma nuHat_fixed_of_BPrime_of_fixed (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {μ ν : Irr (↥c.H0)} {χ : Irr G}
    (hχδ : scalarProduct G χ.1 (deltaNu c h12 μ) ≠ 0)
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1)
    (hμt : μ.1 (tH0 c) = μ.1 1)
    (hμfixed : (nuHatOrbit c h12 (nuHat c h12 μ)).card = 1)
    (hνB : ν ∈ BPrimeOf c h12 χ.1) :
    (nuHatOrbit c h12 (nuHat c h12 ν)).card = 1 := by
  classical
  have hμB : μ ∈ BPrimeOf c h12 χ.1 := by
    rw [BPrimeOf]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ μ, hμs, hμt, hχδ⟩
  have hB' : (BPrimeOf c h12 χ.1).Nonempty := ⟨μ, hμB⟩
  have h41 := lemma_4_1 c h12 hSC hS4 (χ := χ.1) (Or.inl χ.2) hB'
  by_cases hνμ : ν = μ
  · rw [hνμ]
    exact hμfixed
  · have hBcard : (BPrimeOf c h12 χ.1).card = 3 := by
      rcases h41.1 with h1 | h3
      · rcases Finset.card_eq_one.mp h1 with ⟨γ, hγ⟩
        have hμγ : μ = γ := by
          rw [hγ] at hμB
          simpa using hμB
        have hνγ : ν = γ := by
          rw [hγ] at hνB
          simpa using hνB
        exact False.elim (hνμ (hνγ.trans hμγ.symm))
      · exact h3
    let O : Finset (Irr (↥c.B)) := nuHatFinset c h12 (BPrimeOf c h12 χ.1)
    have hOcard : O.card = 3 := by
      dsimp [O, nuHatFinset]
      rw [Finset.card_image_of_injOn (nuHat_injective_on_BPrime c h12 hSC hS4)]
      exact hBcard
    have hOinv : ∀ (g : G) (hg : g ∈ normalizerS c) (β : Irr (↥c.B)),
        β ∈ O → conjIrrB c (B_conj_mem_of_normalizerS c hg) β ∈ O := by
      intro g hg β hβ
      have hβ' : β ∈ nuHatImage c h12 (BPrimeOf c h12 χ.1) :=
        (mem_nuHatImage_iff c h12 (BPrimeOf c h12 χ.1) β).2 hβ
      have h' := h41.2.2.2.2.2 g hg β hβ'
      exact (mem_nuHatImage_iff c h12 (BPrimeOf c h12 χ.1)
        (conjIrrB c (B_conj_mem_of_normalizerS c hg) β)).1 h'
    let βν : Irr (↥c.B) := nuHat c h12 ν
    have hβO : βν ∈ O := by
      exact Finset.mem_image.mpr ⟨ν, hνB, rfl⟩
    have hμO : nuHat c h12 μ ∈ O := by
      exact Finset.mem_image.mpr ⟨μ, hμB, rfl⟩
    have horbit_subset : nuHatOrbit c h12 βν ⊆ O := by
      intro β hβ
      rw [nuHatOrbit] at hβ
      rcases (Finset.mem_filter.mp hβ).2 with ⟨g, hg, hEq⟩
      rw [← hEq]
      exact hOinv g hg βν hβO
    rcases nuHatOrbit_card_eq_one_or_three c h12 hS4 ν with h1 | h3
    · simpa [βν] using h1
    · have hβne : βν ≠ nuHat c h12 μ := by
        intro hEq
        have hEqOrbit : nuHatOrbit c h12 βν = nuHatOrbit c h12 (nuHat c h12 μ) := by
          rw [hEq]
        have hcard1 : (nuHatOrbit c h12 βν).card = 1 := by
          rw [hEqOrbit, hμfixed]
        have hcard3 : (nuHatOrbit c h12 βν).card = 3 := by
          simpa [βν] using h3
        omega
      have hμnot : nuHat c h12 μ ∉ nuHatOrbit c h12 βν := by
        intro hmem
        have hEqOrbit := nuHatOrbit_eq_of_mem c h12 hmem
        have hcard1 : (nuHatOrbit c h12 (nuHat c h12 ν)).card = 1 := by
          rw [← hEqOrbit, hμfixed]
        omega
      have hinsert_subset : insert (nuHat c h12 μ) (nuHatOrbit c h12 βν) ⊆ O := by
        intro β hβ
        rw [Finset.mem_insert] at hβ
        rcases hβ with rfl | hβ
        · exact hμO
        · exact horbit_subset hβ
      have hβcard3 : (nuHatOrbit c h12 βν).card = 3 := by
        simpa [βν] using h3
      have hcard_insert : (insert (nuHat c h12 μ) (nuHatOrbit c h12 βν)).card = 4 := by
        rw [Finset.card_insert_of_notMem hμnot, hβcard3]
      have hle : (insert (nuHat c h12 μ) (nuHatOrbit c h12 βν)).card ≤ O.card :=
        Finset.card_le_card hinsert_subset
      omega


/-- If one member of a connected component has fixed `ν̂`, then every
member of the component has fixed `ν̂`. -/
private lemma exists_fixed_witness_of_Delta0_of_fixed (c : Hyp11 G)
    (h12 : Hyp12 c) (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {Δ0 : Set (ClassFunction G)} (hcomp : IsConnectedComponent c h12 Δ0)
    {μ : Irr (↥c.H0)}
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1)
    (hμt : μ.1 (tH0 c) = μ.1 1)
    (hμΔ0 : deltaNu c h12 μ ∈ Δ0)
    (hμfixed : (nuHatOrbit c h12 (nuHat c h12 μ)).card = 1) :
    ∀ δ ∈ Δ0, ∃ ν : Irr (↥c.H0),
      δ ∈ Δ0 ∧ δ = deltaNu c h12 ν ∧
      conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 ∧
      ν.1 (tH0 c) = ν.1 1 ∧
      (nuHatOrbit c h12 (nuHat c h12 ν)).card = 1 := by
  classical
  intro δ hδ
  have hpath : Relation.ReflTransGen (deltaAdjacent c h12) (deltaNu c h12 μ) δ :=
    hcomp.2.2.1 (deltaNu c h12 μ) δ hμΔ0 hδ
  have hrev : Relation.ReflTransGen (deltaAdjacent c h12) δ (deltaNu c h12 μ) :=
    reflTransGen_symm (fun {a b : ClassFunction G} h => deltaAdjacent_symm c h12 h) hpath
  refine Relation.ReflTransGen.head_induction_on hrev ?refl ?head
  · exact ⟨μ, hμΔ0, rfl, hμs, hμt, hμfixed⟩
  · intro x y hadj hpath' ih
    rcases ih with ⟨ν_y, hyΔ0, hEqy, hνys, hνyt, hfix_y⟩
    have hxΔ0 : x ∈ Δ0 := by
      by_contra hnot
      exact (hcomp.2.2.2 x hnot y hyΔ0) hadj
    have hxΔ : x ∈ Delta c h12 := hcomp.2.1 hxΔ0
    rcases hxΔ with ⟨ν_x, hνxs, hνxt, hEqx⟩
    rcases exists_shared_constituent_of_adjacent c h12 hadj with ⟨χ, hχa, hχc⟩
    have hχδy : scalarProduct G χ.1 (deltaNu c h12 ν_y) ≠ 0 := by
      simpa [hEqy] using (mem_involved_iff y χ).1 hχc
    have hν_xB : ν_x ∈ BPrimeOf c h12 χ.1 := by
      rw [BPrimeOf]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ ν_x, hνxs, hνxt,
        by simpa [hEqx] using (mem_involved_iff x χ).1 hχa⟩
    have hfix_x := nuHat_fixed_of_BPrime_of_fixed c h12 hSC hS4
      hχδy hνys hνyt hfix_y hν_xB
    exact ⟨ν_x, hxΔ0, hEqx, hνxs, hνxt, hfix_x⟩

/-- A repeated vertex in any relabeling of the fixed incidence triangle
contradicts orthogonality. -/
private lemma fixed_repeated_incidence_contradiction (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {νA νB νC νD νF : Irr (↥c.H0)}
    (hνAs : conjChar c.H0 (s_normalizes_H0 c h12) νA.1 = νA.1)
    (hνAt : νA.1 (tH0 c) = νA.1 1)
    (hνBs : conjChar c.H0 (s_normalizes_H0 c h12) νB.1 = νB.1)
    (hνBt : νB.1 (tH0 c) = νB.1 1)
    (hνCs : conjChar c.H0 (s_normalizes_H0 c h12) νC.1 = νC.1)
    (hνCt : νC.1 (tH0 c) = νC.1 1)
    (hνDs : conjChar c.H0 (s_normalizes_H0 c h12) νD.1 = νD.1)
    (hνDt : νD.1 (tH0 c) = νD.1 1)
    (hνFs : conjChar c.H0 (s_normalizes_H0 c h12) νF.1 = νF.1)
    (hνFt : νF.1 (tH0 c) = νF.1 1)
    (hνAB : νA ≠ νB) (hνAC : νA ≠ νC) (hνAD : νA ≠ νD)
    (hνAF : νA ≠ νF) (hνBC : νB ≠ νC) (hνBD : νB ≠ νD)
    (hνBF : νB ≠ νF) (hνCD : νC ≠ νD) (hνCF : νC ≠ νF)
    (hνDF : νD ≠ νF)
    {a b c₀ d e f g : Irr G}
    (hAset : involved (deltaNu c h12 νA) = {a, b, c₀, d})
    (hBset : involved (deltaNu c h12 νB) = {a, b, e, f})
    (hCset : involved (deltaNu c h12 νC) = {a, c₀, e, g})
    (hbD : b ∈ involved (deltaNu c h12 νD))
    (hcD : c₀ ∈ involved (deltaNu c h12 νD))
    (heF : e ∈ involved (deltaNu c h12 νF))
    (hBD : (involved (deltaNu c h12 νB) ∩
      involved (deltaNu c h12 νD)).card = 2)
    (hCD : (involved (deltaNu c h12 νC) ∩
      involved (deltaNu c h12 νD)).card = 2)
    (hBF : (involved (deltaNu c h12 νB) ∩
      involved (deltaNu c h12 νF)).card = 2)
    (hCF : (involved (deltaNu c h12 νC) ∩
      involved (deltaNu c h12 νF)).card = 2)
    (hab : a ≠ b) (hac : a ≠ c₀) (had : a ≠ d)
    (hbc : b ≠ c₀) (hbd : b ≠ d) (hcd : c₀ ≠ d)
    (hae : a ≠ e) (haf : a ≠ f) (hag : a ≠ g)
    (hbe : b ≠ e) (hbf : b ≠ f) (hbg : b ≠ g)
    (hce : c₀ ≠ e) (hcf : c₀ ≠ f) (hcg : c₀ ≠ g)
    (hde : d ≠ e) (hdf : d ≠ f) (hdg : d ≠ g)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) : False := by
  classical
  have haA : a ∈ involved (deltaNu c h12 νA) := by rw [hAset]; simp
  have hbA : b ∈ involved (deltaNu c h12 νA) := by rw [hAset]; simp
  have hcA : c₀ ∈ involved (deltaNu c h12 νA) := by rw [hAset]; simp
  have hdA : d ∈ involved (deltaNu c h12 νA) := by rw [hAset]; simp
  have haB : a ∈ involved (deltaNu c h12 νB) := by rw [hBset]; simp
  have hbB : b ∈ involved (deltaNu c h12 νB) := by rw [hBset]; simp
  have heB : e ∈ involved (deltaNu c h12 νB) := by rw [hBset]; simp
  have hfB : f ∈ involved (deltaNu c h12 νB) := by rw [hBset]; simp
  have haC : a ∈ involved (deltaNu c h12 νC) := by rw [hCset]; simp
  have hcC : c₀ ∈ involved (deltaNu c h12 νC) := by rw [hCset]; simp
  have heC : e ∈ involved (deltaNu c h12 νC) := by rw [hCset]; simp
  have hgC : g ∈ involved (deltaNu c h12 νC) := by rw [hCset]; simp
  have haAB := BPrime_of_involved c h12 hνAs hνAt haA
  have haBB := BPrime_of_involved c h12 hνBs hνBt haB
  have haCB := BPrime_of_involved c h12 hνCs hνCt haC
  have hbAB := BPrime_of_involved c h12 hνAs hνAt hbA
  have hbBB := BPrime_of_involved c h12 hνBs hνBt hbB
  have hbDB := BPrime_of_involved c h12 hνDs hνDt hbD
  have hcAB := BPrime_of_involved c h12 hνAs hνAt hcA
  have hcCB := BPrime_of_involved c h12 hνCs hνCt hcC
  have hcDB := BPrime_of_involved c h12 hνDs hνDt hcD
  have heBB := BPrime_of_involved c h12 hνBs hνBt heB
  have heCB := BPrime_of_involved c h12 hνCs hνCt heC
  have heFB := BPrime_of_involved c h12 hνFs hνFt heF
  have haD : a ∉ involved (deltaNu c h12 νD) :=
    not_involved_of_fourth c h12 hSC hS4 hνDs hνDt (Or.inl a.2)
      haAB haBB haCB hνAB hνAC hνBC hνAD.symm hνBD.symm hνCD.symm
  have heD : e ∉ involved (deltaNu c h12 νD) :=
    not_involved_of_fourth c h12 hSC hS4 hνDs hνDt (Or.inl e.2)
      heBB heCB heFB hνBC hνBF hνCF hνBD.symm hνCD.symm hνDF
  have haF : a ∉ involved (deltaNu c h12 νF) :=
    not_involved_of_fourth c h12 hSC hS4 hνFs hνFt (Or.inl a.2)
      haAB haBB haCB hνAB hνAC hνBC hνAF.symm hνBF.symm hνCF.symm
  have hbF : b ∉ involved (deltaNu c h12 νF) :=
    not_involved_of_fourth c h12 hSC hS4 hνFs hνFt (Or.inl b.2)
      hbAB hbBB hbDB hνAB hνAD hνBD hνAF.symm hνBF.symm hνDF.symm
  have hcF : c₀ ∉ involved (deltaNu c h12 νF) :=
    not_involved_of_fourth c h12 hSC hS4 hνFs hνFt (Or.inl c₀.2)
      hcAB hcCB hcDB hνAC hνAD hνCD hνAF.symm hνCF.symm hνDF.symm
  have hDcard := involved_deltaNu_card_eq_four c h12 hSC hS4 hνDs
  have hFcard := involved_deltaNu_card_eq_four c h12 hSC hS4 hνFs
  rcases repeated_supports_of_intersections hBset hCset hDcard hFcard
      hbD hcD heF hBD hCD hBF hCF haD heD haF hbF hcF
      hab hac hae haf hag hbc hbe hbf hbg hce hcf hcg hef heg hfg with
    ⟨h, hDset, hFset, hha, hhb, hhc, hhe, hhf, hhg⟩
  rcases signed_four_decomp_fin c h12 hSC hS4 hνAs with
    ⟨AA, sA, hAA, hiA, hsA, hδA⟩
  rcases signed_four_decomp_fin c h12 hSC hS4 hνBs with
    ⟨AB, sB, hAB, hiB, hsB, hδB⟩
  rcases signed_four_decomp_fin c h12 hSC hS4 hνCs with
    ⟨AC, sC, hAC, hiC, hsC, hδC⟩
  rcases signed_four_decomp_fin c h12 hSC hS4 hνDs with
    ⟨AD, sD, hAD, hiD, hsD, hδD⟩
  rcases signed_four_decomp_fin c h12 hSC hS4 hνFs with
    ⟨AF, sF, hAF, hiF, hsF, hδF⟩
  have hortAB := deltaNu_orthogonal c h12 hSC hS4
    hνAs hνAt hνBs hνBt hνAB
  have hortAC := deltaNu_orthogonal c h12 hSC hS4
    hνAs hνAt hνCs hνCt hνAC
  have hortBC := deltaNu_orthogonal c h12 hSC hS4
    hνBs hνBt hνCs hνCt hνBC
  have hortAD := deltaNu_orthogonal c h12 hSC hS4
    hνAs hνAt hνDs hνDt hνAD
  have hortBD := deltaNu_orthogonal c h12 hSC hS4
    hνBs hνBt hνDs hνDt hνBD
  have hortCD := deltaNu_orthogonal c h12 hSC hS4
    hνCs hνCt hνDs hνDt hνCD
  have hortBF := deltaNu_orthogonal c h12 hSC hS4
    hνBs hνBt hνFs hνFt hνBF
  have hortCF := deltaNu_orthogonal c h12 hSC hS4
    hνCs hνCt hνFs hνFt hνCF
  have hortDF := deltaNu_orthogonal c h12 hSC hS4
    hνDs hνDt hνFs hνFt hνDF
  exact repeated_incidence_orthogonality_contradiction
    hAA hiA hsA hδA hAB hiB hsB hδB hAC hiC hsC hδC
    hAD hiD hsD hδD hAF hiF hsF hδF
    hAset hBset hCset hDset hFset
    hab hac had hbc hbd hcd hae haf hag hbe hbf hbg hce hcf hcg
    hde hdf hdg hef heg hfg hha hhb hhc hhe hhf hhg
    hortAB hortAC hortBC hortAD hortBD hortCD hortBF hortCF hortDF

/-- If the three added fixed witnesses are pairwise distinct, four of the
signed supports have even incidence everywhere, contradicting fixed parity. -/
private lemma fixed_distinct_incidence_contradiction (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {ν₁ ν₂ ν₃ ν₄ ν₅ ν₆ : Irr (↥c.H0)}
    (hν₁s : conjChar c.H0 (s_normalizes_H0 c h12) ν₁.1 = ν₁.1)
    (hν₁t : ν₁.1 (tH0 c) = ν₁.1 1)
    (hν₂s : conjChar c.H0 (s_normalizes_H0 c h12) ν₂.1 = ν₂.1)
    (hν₂t : ν₂.1 (tH0 c) = ν₂.1 1)
    (hν₃s : conjChar c.H0 (s_normalizes_H0 c h12) ν₃.1 = ν₃.1)
    (hν₃t : ν₃.1 (tH0 c) = ν₃.1 1)
    (hν₄s : conjChar c.H0 (s_normalizes_H0 c h12) ν₄.1 = ν₄.1)
    (hν₄t : ν₄.1 (tH0 c) = ν₄.1 1)
    (hν₅s : conjChar c.H0 (s_normalizes_H0 c h12) ν₅.1 = ν₅.1)
    (hν₅t : ν₅.1 (tH0 c) = ν₅.1 1)
    (hν₆s : conjChar c.H0 (s_normalizes_H0 c h12) ν₆.1 = ν₆.1)
    (hν₆t : ν₆.1 (tH0 c) = ν₆.1 1)
    (hfix₁ : (nuHatOrbit c h12 (nuHat c h12 ν₁)).card = 1)
    (hfix₅ : (nuHatOrbit c h12 (nuHat c h12 ν₅)).card = 1)
    (hν₁₂ : ν₁ ≠ ν₂) (hν₁₃ : ν₁ ≠ ν₃) (hν₂₃ : ν₂ ≠ ν₃)
    (hν₁₄ : ν₁ ≠ ν₄) (hν₂₄ : ν₂ ≠ ν₄) (hν₃₄ : ν₃ ≠ ν₄)
    (hν₁₅ : ν₁ ≠ ν₅) (hν₂₅ : ν₂ ≠ ν₅) (hν₃₅ : ν₃ ≠ ν₅)
    (hν₁₆ : ν₁ ≠ ν₆) (hν₂₆ : ν₂ ≠ ν₆) (hν₃₆ : ν₃ ≠ ν₆)
    (hν₄₅ : ν₄ ≠ ν₅) (hν₄₆ : ν₄ ≠ ν₆) (hν₅₆ : ν₅ ≠ ν₆)
    {a b c₀ d e f g : Irr G}
    (hAset : involved (deltaNu c h12 ν₁) = {a, b, c₀, d})
    (hBset : involved (deltaNu c h12 ν₂) = {a, b, e, f})
    (hCset : involved (deltaNu c h12 ν₃) = {a, c₀, e, g})
    (hb₄ : b ∈ involved (deltaNu c h12 ν₄))
    (hc₅ : c₀ ∈ involved (deltaNu c h12 ν₅))
    (he₆ : e ∈ involved (deltaNu c h12 ν₆))
    (hA4 : (involved (deltaNu c h12 ν₁) ∩
      involved (deltaNu c h12 ν₄)).card = 2)
    (hB4 : (involved (deltaNu c h12 ν₂) ∩
      involved (deltaNu c h12 ν₄)).card = 2)
    (hA5 : (involved (deltaNu c h12 ν₁) ∩
      involved (deltaNu c h12 ν₅)).card = 2)
    (hC5 : (involved (deltaNu c h12 ν₃) ∩
      involved (deltaNu c h12 ν₅)).card = 2)
    (hB6 : (involved (deltaNu c h12 ν₂) ∩
      involved (deltaNu c h12 ν₆)).card = 2)
    (hC6 : (involved (deltaNu c h12 ν₃) ∩
      involved (deltaNu c h12 ν₆)).card = 2)
    (hab : a ≠ b) (hac : a ≠ c₀) (had : a ≠ d)
    (hbc : b ≠ c₀) (hbd : b ≠ d) (hcd : c₀ ≠ d)
    (hae : a ≠ e) (haf : a ≠ f) (hag : a ≠ g)
    (hbe : b ≠ e) (hbf : b ≠ f) (hbg : b ≠ g)
    (hce : c₀ ≠ e) (hcf : c₀ ≠ f) (hcg : c₀ ≠ g)
    (hde : d ≠ e) (hdf : d ≠ f) (hdg : d ≠ g)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) : False := by
  classical
  have ha₁ : a ∈ involved (deltaNu c h12 ν₁) := by rw [hAset]; simp
  have hb₁ : b ∈ involved (deltaNu c h12 ν₁) := by rw [hAset]; simp
  have hc₁ : c₀ ∈ involved (deltaNu c h12 ν₁) := by rw [hAset]; simp
  have hd₁ : d ∈ involved (deltaNu c h12 ν₁) := by rw [hAset]; simp
  have ha₂ : a ∈ involved (deltaNu c h12 ν₂) := by rw [hBset]; simp
  have hb₂ : b ∈ involved (deltaNu c h12 ν₂) := by rw [hBset]; simp
  have he₂ : e ∈ involved (deltaNu c h12 ν₂) := by rw [hBset]; simp
  have hf₂ : f ∈ involved (deltaNu c h12 ν₂) := by rw [hBset]; simp
  have ha₃ : a ∈ involved (deltaNu c h12 ν₃) := by rw [hCset]; simp
  have hc₃ : c₀ ∈ involved (deltaNu c h12 ν₃) := by rw [hCset]; simp
  have he₃ : e ∈ involved (deltaNu c h12 ν₃) := by rw [hCset]; simp
  have hg₃ : g ∈ involved (deltaNu c h12 ν₃) := by rw [hCset]; simp
  have ha₁B := BPrime_of_involved c h12 hν₁s hν₁t ha₁
  have ha₂B := BPrime_of_involved c h12 hν₂s hν₂t ha₂
  have ha₃B := BPrime_of_involved c h12 hν₃s hν₃t ha₃
  have hb₁B := BPrime_of_involved c h12 hν₁s hν₁t hb₁
  have hb₂B := BPrime_of_involved c h12 hν₂s hν₂t hb₂
  have hb₄B := BPrime_of_involved c h12 hν₄s hν₄t hb₄
  have hc₁B := BPrime_of_involved c h12 hν₁s hν₁t hc₁
  have hc₃B := BPrime_of_involved c h12 hν₃s hν₃t hc₃
  have hc₅B := BPrime_of_involved c h12 hν₅s hν₅t hc₅
  have he₂B := BPrime_of_involved c h12 hν₂s hν₂t he₂
  have he₃B := BPrime_of_involved c h12 hν₃s hν₃t he₃
  have he₆B := BPrime_of_involved c h12 hν₆s hν₆t he₆
  have ha₄ : a ∉ involved (deltaNu c h12 ν₄) :=
    not_involved_of_fourth c h12 hSC hS4 hν₄s hν₄t (Or.inl a.2)
      ha₁B ha₂B ha₃B hν₁₂ hν₁₃ hν₂₃ hν₁₄.symm hν₂₄.symm hν₃₄.symm
  have hc₄ : c₀ ∉ involved (deltaNu c h12 ν₄) :=
    not_involved_of_fourth c h12 hSC hS4 hν₄s hν₄t (Or.inl c₀.2)
      hc₁B hc₃B hc₅B hν₁₃ hν₁₅ hν₃₅ hν₁₄.symm hν₃₄.symm hν₄₅
  have he₄ : e ∉ involved (deltaNu c h12 ν₄) :=
    not_involved_of_fourth c h12 hSC hS4 hν₄s hν₄t (Or.inl e.2)
      he₂B he₃B he₆B hν₂₃ hν₂₆ hν₃₆ hν₂₄.symm hν₃₄.symm hν₄₆
  have hd₄ : d ∈ involved (deltaNu c h12 ν₄) :=
    other_point_mem_of_inter_two hAset hA4 hb₄ ha₄ hc₄
  have hf₄ : f ∈ involved (deltaNu c h12 ν₄) :=
    other_point_mem_of_inter_two hBset hB4 hb₄ ha₄ he₄
  have ha₅ : a ∉ involved (deltaNu c h12 ν₅) :=
    not_involved_of_fourth c h12 hSC hS4 hν₅s hν₅t (Or.inl a.2)
      ha₁B ha₂B ha₃B hν₁₂ hν₁₃ hν₂₃ hν₁₅.symm hν₂₅.symm hν₃₅.symm
  have hb₅ : b ∉ involved (deltaNu c h12 ν₅) :=
    not_involved_of_fourth c h12 hSC hS4 hν₅s hν₅t (Or.inl b.2)
      hb₁B hb₂B hb₄B hν₁₂ hν₁₄ hν₂₄ hν₁₅.symm hν₂₅.symm hν₄₅.symm
  have he₅ : e ∉ involved (deltaNu c h12 ν₅) :=
    not_involved_of_fourth c h12 hSC hS4 hν₅s hν₅t (Or.inl e.2)
      he₂B he₃B he₆B hν₂₃ hν₂₆ hν₃₆ hν₂₅.symm hν₃₅.symm hν₅₆
  have hAset' : involved (deltaNu c h12 ν₁) = {a, c₀, b, d} := by
    simpa [Finset.insert_comm] using hAset
  have hd₅ : d ∈ involved (deltaNu c h12 ν₅) :=
    other_point_mem_of_inter_two hAset' hA5 hc₅ ha₅ hb₅
  have hg₅ : g ∈ involved (deltaNu c h12 ν₅) :=
    other_point_mem_of_inter_two hCset hC5 hc₅ ha₅ he₅
  have ha₆ : a ∉ involved (deltaNu c h12 ν₆) :=
    not_involved_of_fourth c h12 hSC hS4 hν₆s hν₆t (Or.inl a.2)
      ha₁B ha₂B ha₃B hν₁₂ hν₁₃ hν₂₃ hν₁₆.symm hν₂₆.symm hν₃₆.symm
  have hb₆ : b ∉ involved (deltaNu c h12 ν₆) :=
    not_involved_of_fourth c h12 hSC hS4 hν₆s hν₆t (Or.inl b.2)
      hb₁B hb₂B hb₄B hν₁₂ hν₁₄ hν₂₄ hν₁₆.symm hν₂₆.symm hν₄₆.symm
  have hc₆ : c₀ ∉ involved (deltaNu c h12 ν₆) :=
    not_involved_of_fourth c h12 hSC hS4 hν₆s hν₆t (Or.inl c₀.2)
      hc₁B hc₃B hc₅B hν₁₃ hν₁₅ hν₃₅ hν₁₆.symm hν₃₆.symm hν₅₆.symm
  have hBset' : involved (deltaNu c h12 ν₂) = {a, e, b, f} := by
    simpa [Finset.insert_comm] using hBset
  have hCset' : involved (deltaNu c h12 ν₃) = {a, e, c₀, g} := by
    simpa [Finset.insert_comm] using hCset
  have hf₆ : f ∈ involved (deltaNu c h12 ν₆) :=
    other_point_mem_of_inter_two hBset' hB6 he₆ ha₆ hb₆
  have hg₆ : g ∈ involved (deltaNu c h12 ν₆) :=
    other_point_mem_of_inter_two hCset' hC6 he₆ ha₆ hc₆
  have hd₄B := BPrime_of_involved c h12 hν₄s hν₄t hd₄
  have hd₅B := BPrime_of_involved c h12 hν₅s hν₅t hd₅
  have hd₆ : d ∉ involved (deltaNu c h12 ν₆) :=
    not_involved_of_fourth c h12 hSC hS4 hν₆s hν₆t (Or.inl d.2)
      (BPrime_of_involved c h12 hν₁s hν₁t hd₁) hd₄B hd₅B
      hν₁₄ hν₁₅ hν₄₅ hν₁₆.symm hν₄₆.symm hν₅₆.symm
  have hf₄B := BPrime_of_involved c h12 hν₄s hν₄t hf₄
  have hf₆B := BPrime_of_involved c h12 hν₆s hν₆t hf₆
  have hf₅ : f ∉ involved (deltaNu c h12 ν₅) :=
    not_involved_of_fourth c h12 hSC hS4 hν₅s hν₅t (Or.inl f.2)
      (BPrime_of_involved c h12 hν₂s hν₂t hf₂) hf₄B hf₆B
      hν₂₄ hν₂₆ hν₄₆ hν₂₅.symm hν₄₅.symm hν₅₆
  have hδ₅₆ : deltaNu c h12 ν₅ ≠ deltaNu c h12 ν₆ := by
    intro hEq
    exact hν₅₆ (deltaNu_injective c h12 hSC hS4
      hν₅s hν₅t hν₆s hν₆t hEq)
  have hE6 : (involved (deltaNu c h12 ν₅) ∩
      involved (deltaNu c h12 ν₆)).card = 2 :=
    involved_inter_card_eq_two_of_adjacent_fixed c h12 hSC hS4
      hν₅s hν₅t hν₆s hν₆t hfix₅ hδ₅₆ ⟨g, hg₅, hg₆⟩
  have hEcard := involved_deltaNu_card_eq_four c h12 hSC hS4 hν₅s
  rcases exists_fourth_of_card_four hc₅ hd₅ hg₅ hcd hcg hdg hEcard with
    ⟨σ, hσ₅, hσc, hσd, hσg, hEset⟩
  have hEset' : involved (deltaNu c h12 ν₅) = {c₀, g, d, σ} := by
    simpa [Finset.insert_comm] using hEset
  have hσ₆ : σ ∈ involved (deltaNu c h12 ν₆) :=
    other_point_mem_of_inter_two hEset' hE6 hg₆ hc₆ hd₆
  have hσa : σ ≠ a := by
    intro hEq
    exact ha₅ (by simpa [hEq] using hσ₅)
  have hσb : σ ≠ b := by
    intro hEq
    exact hb₅ (by simpa [hEq] using hσ₅)
  have hσe : σ ≠ e := by
    intro hEq
    exact he₅ (by simpa [hEq] using hσ₅)
  have hσf : σ ≠ f := by
    intro hEq
    exact hf₅ (by simpa [hEq] using hσ₅)
  have hFcard := involved_deltaNu_card_eq_four c h12 hSC hS4 hν₆s
  have hFset : involved (deltaNu c h12 ν₆) = {e, f, g, σ} :=
    finset_eq_of_card_four _ he₆ hf₆ hg₆ hσ₆ hFcard
      hfg hσf.symm hσg.symm hef heg hσe.symm
  rcases signed_four_decomp_fin c h12 hSC hS4 hν₁s with
    ⟨A₁, s₁, hA₁, hi₁, hs₁, hδ₁⟩
  rcases signed_four_decomp_fin c h12 hSC hS4 hν₂s with
    ⟨A₂, s₂, hA₂, hi₂, hs₂, hδ₂⟩
  rcases signed_four_decomp_fin c h12 hSC hS4 hν₅s with
    ⟨A₅, s₅, hA₅, hi₅, hs₅, hδ₅⟩
  rcases signed_four_decomp_fin c h12 hSC hS4 hν₆s with
    ⟨A₆, s₆, hA₆, hi₆, hs₆, hδ₆⟩
  have hcount : ∀ x : Irr G,
      Even ((if x ∈ involved (deltaNu c h12 ν₁) then 1 else 0) +
        (if x ∈ involved (deltaNu c h12 ν₂) then 1 else 0) +
        (if x ∈ involved (deltaNu c h12 ν₅) then 1 else 0) +
        (if x ∈ involved (deltaNu c h12 ν₆) then 1 else 0)) := by
    intro x
    rw [hAset, hBset, hEset, hFset]
    by_cases hxa : x = a
    · subst x; simp [hab, hac, had, hae, haf, hag, hσa, hσa.symm]
    by_cases hxb : x = b
    · subst x; simp [hxa, hab, hbc, hbd, hbe, hbf, hbg, hσb, hσb.symm]
    by_cases hxc : x = c₀
    · subst x; simp [hxa, hxb, hac, hbc, hcd, hce, hcf, hcg, hσc, hσc.symm]
    by_cases hxd : x = d
    · subst x; simp [hxa, hxb, hxc, had, hbd, hcd, hde, hdf, hdg, hσd, hσd.symm]
    by_cases hxe : x = e
    · subst x; simp [hxa, hxb, hxc, hxd, hae, hbe, hce, hde, hef, heg,
        hσe, hσe.symm]
    by_cases hxf : x = f
    · subst x; simp [hxa, hxb, hxc, hxd, hxe, haf, hbf, hcf, hdf, hef, hfg,
        hσf, hσf.symm]
    by_cases hxg : x = g
    · subst x; simp [hxa, hxb, hxc, hxd, hxe, hxf, hag, hbg, hcg, hdg, heg,
        hfg, hσg, hσg.symm]
    by_cases hxσ : x = σ
    · subst x; simp [hσa, hσb, hσc, hσd, hσe, hσf, hσg]
    simp [hxa, hxb, hxc, hxd, hxe, hxf, hxg, hxσ]
  have heven := scalarProduct_even_of_four_signed_support
    hA₁ hi₁ hs₁ hδ₁ hA₂ hi₂ hs₂ hδ₂ hA₅ hi₅ hs₅ hδ₅
    hA₆ hi₆ hs₆ hδ₆ hcount
  rcases exists_odd_multiplicity_of_fixed_sum c h12 hSC hS4
      hν₁s hν₁t hfix₁ with ⟨μ', hμ'char, hoddRule⟩
  have hodd := hoddRule ({ν₂, ν₅, ν₆} : Finset (Irr (↥c.H0)))
    (fun _ => 1) 1 (by
      intro ν hν
      simp only [Finset.mem_insert, Finset.mem_singleton] at hν
      rcases hν with rfl | rfl | rfl
      · exact ⟨hν₂s, hν₂t, hν₁₂.symm⟩
      · exact ⟨hν₅s, hν₅t, hν₁₅.symm⟩
      · exact ⟨hν₆s, hν₆t, hν₁₆.symm⟩) (by norm_num)
  have hsum : (((1 : ℤ) : ℂ)) • deltaNu c h12 ν₁ +
      ∑ ν ∈ ({ν₂, ν₅, ν₆} : Finset (Irr (↥c.H0))),
        ((1 : ℤ) : ℂ) • deltaNu c h12 ν =
      deltaNu c h12 ν₁ + deltaNu c h12 ν₂ +
        deltaNu c h12 ν₅ + deltaNu c h12 ν₆ := by
    ext x
    simp [hν₂₅, hν₂₆, hν₅₆]
    ring
  rcases hodd with ⟨χ, hχ, m, hm, hOddm⟩
  rw [hsum] at hm
  rcases heven ⟨χ, hχ⟩ with ⟨k, hk, hEvenk⟩
  have hmk : m = k := by
    exact_mod_cast hm.trans hk.symm
  have hEvenm : Even m := by rwa [hmk]
  exact (Int.not_even_iff_odd).2 hOddm hEvenm

/-- Build the six fixed witnesses and all incidence data needed for the
finite case split. -/
private lemma fixed_six_incidence_data (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {Δ0 : Set (ClassFunction G)} (hcomp : IsConnectedComponent c h12 Δ0)
    {ν₁ ν₂ : Irr (↥c.H0)} {χ : Irr G}
    (hν₁Δ0 : deltaNu c h12 ν₁ ∈ Δ0)
    (hν₂Δ0 : deltaNu c h12 ν₂ ∈ Δ0)
    (hν₁s : conjChar c.H0 (s_normalizes_H0 c h12) ν₁.1 = ν₁.1)
    (hν₁t : ν₁.1 (tH0 c) = ν₁.1 1)
    (hν₂s : conjChar c.H0 (s_normalizes_H0 c h12) ν₂.1 = ν₂.1)
    (hν₂t : ν₂.1 (tH0 c) = ν₂.1 1)
    (hfix₁ : (nuHatOrbit c h12 (nuHat c h12 ν₁)).card = 1)
    (hfix₂ : (nuHatOrbit c h12 (nuHat c h12 ν₂)).card = 1)
    (hχ₁ : χ ∈ involved (deltaNu c h12 ν₁))
    (hχ₂ : χ ∈ involved (deltaNu c h12 ν₂))
    (hν₁₂ : ν₁ ≠ ν₂) :
    ∃ ν₃ ν₄ ν₅ ν₆ : Irr (↥c.H0), ∃ a b c₀ d e f g : Irr G,
      conjChar c.H0 (s_normalizes_H0 c h12) ν₃.1 = ν₃.1 ∧
      ν₃.1 (tH0 c) = ν₃.1 1 ∧
      (nuHatOrbit c h12 (nuHat c h12 ν₃)).card = 1 ∧
      deltaNu c h12 ν₃ ∈ Δ0 ∧
      conjChar c.H0 (s_normalizes_H0 c h12) ν₄.1 = ν₄.1 ∧
      ν₄.1 (tH0 c) = ν₄.1 1 ∧
      (nuHatOrbit c h12 (nuHat c h12 ν₄)).card = 1 ∧
      deltaNu c h12 ν₄ ∈ Δ0 ∧
      conjChar c.H0 (s_normalizes_H0 c h12) ν₅.1 = ν₅.1 ∧
      ν₅.1 (tH0 c) = ν₅.1 1 ∧
      (nuHatOrbit c h12 (nuHat c h12 ν₅)).card = 1 ∧
      deltaNu c h12 ν₅ ∈ Δ0 ∧
      conjChar c.H0 (s_normalizes_H0 c h12) ν₆.1 = ν₆.1 ∧
      ν₆.1 (tH0 c) = ν₆.1 1 ∧
      (nuHatOrbit c h12 (nuHat c h12 ν₆)).card = 1 ∧
      deltaNu c h12 ν₆ ∈ Δ0 ∧
      ν₁ ≠ ν₃ ∧ ν₂ ≠ ν₃ ∧
      ν₁ ≠ ν₄ ∧ ν₂ ≠ ν₄ ∧ ν₃ ≠ ν₄ ∧
      ν₁ ≠ ν₅ ∧ ν₃ ≠ ν₅ ∧ ν₂ ≠ ν₅ ∧
      ν₂ ≠ ν₆ ∧ ν₃ ≠ ν₆ ∧ ν₁ ≠ ν₆ ∧
      involved (deltaNu c h12 ν₁) = {a, b, c₀, d} ∧
      involved (deltaNu c h12 ν₂) = {a, b, e, f} ∧
      involved (deltaNu c h12 ν₃) = {a, c₀, e, g} ∧
      b ∈ involved (deltaNu c h12 ν₄) ∧
      c₀ ∈ involved (deltaNu c h12 ν₅) ∧
      e ∈ involved (deltaNu c h12 ν₆) ∧
      (involved (deltaNu c h12 ν₁) ∩ involved (deltaNu c h12 ν₄)).card = 2 ∧
      (involved (deltaNu c h12 ν₂) ∩ involved (deltaNu c h12 ν₄)).card = 2 ∧
      (involved (deltaNu c h12 ν₁) ∩ involved (deltaNu c h12 ν₅)).card = 2 ∧
      (involved (deltaNu c h12 ν₃) ∩ involved (deltaNu c h12 ν₅)).card = 2 ∧
      (involved (deltaNu c h12 ν₂) ∩ involved (deltaNu c h12 ν₆)).card = 2 ∧
      (involved (deltaNu c h12 ν₃) ∩ involved (deltaNu c h12 ν₆)).card = 2 ∧
      a ≠ b ∧ a ≠ c₀ ∧ a ≠ d ∧ b ≠ c₀ ∧ b ≠ d ∧ c₀ ≠ d ∧
      a ≠ e ∧ a ≠ f ∧ a ≠ g ∧ b ≠ e ∧ b ≠ f ∧ b ≠ g ∧
      c₀ ≠ e ∧ c₀ ≠ f ∧ c₀ ≠ g ∧ d ≠ e ∧ d ≠ f ∧ d ≠ g ∧
      e ≠ f ∧ e ≠ g ∧ f ≠ g := by
  classical
  rcases fixed_incidence_three_deltas c h12 hSC hS4 hcomp
      hν₁Δ0 hν₁s hν₁t hν₂s hν₂t hfix₁ hfix₂ hχ₁ hχ₂ hν₁₂ with
    ⟨ν₃, a, b, c₀, d, e, f, g, hν₃B, hν₃Δ0,
      ha, hb, hc, hd, he, hf, hg,
      hab, hac, had, hbc, hbd, hcd,
      hae, haf, hag, hbe, hbf, hbg,
      hce, hcf, hcg, hde, hdf, hdg,
      hef, heg, hfg⟩
  have hν₃s : conjChar c.H0 (s_normalizes_H0 c h12) ν₃.1 = ν₃.1 :=
    (Finset.mem_filter.mp hν₃B).2.1
  have hν₃t : ν₃.1 (tH0 c) = ν₃.1 1 :=
    (Finset.mem_filter.mp hν₃B).2.2.1
  have hfix₃ : (nuHatOrbit c h12 (nuHat c h12 ν₃)).card = 1 :=
    nuHat_fixed_of_BPrime_of_fixed c h12 hSC hS4
      ((mem_involved_iff (deltaNu c h12 ν₁) χ).1 hχ₁)
      hν₁s hν₁t hfix₁ hν₃B
  have ha₁ : a ∈ involved (deltaNu c h12 ν₁) :=
    (Finset.mem_inter.mp (Finset.mem_inter.mp ha).1).1
  have ha₂ : a ∈ involved (deltaNu c h12 ν₂) :=
    (Finset.mem_inter.mp (Finset.mem_inter.mp ha).1).2
  have ha₃ : a ∈ involved (deltaNu c h12 ν₃) := (Finset.mem_inter.mp ha).2
  have hb₁ : b ∈ involved (deltaNu c h12 ν₁) :=
    (Finset.mem_inter.mp (Finset.mem_sdiff.mp hb).1).1
  have hb₂ : b ∈ involved (deltaNu c h12 ν₂) :=
    (Finset.mem_inter.mp (Finset.mem_sdiff.mp hb).1).2
  have hb₃not : b ∉ involved (deltaNu c h12 ν₃) := (Finset.mem_sdiff.mp hb).2
  have hc₁ : c₀ ∈ involved (deltaNu c h12 ν₁) :=
    (Finset.mem_inter.mp (Finset.mem_sdiff.mp hc).1).1
  have hc₃ : c₀ ∈ involved (deltaNu c h12 ν₃) :=
    (Finset.mem_inter.mp (Finset.mem_sdiff.mp hc).1).2
  have hc₂not : c₀ ∉ involved (deltaNu c h12 ν₂) := (Finset.mem_sdiff.mp hc).2
  have hd₁ : d ∈ involved (deltaNu c h12 ν₁) := (Finset.mem_sdiff.mp hd).1
  have he₂ : e ∈ involved (deltaNu c h12 ν₂) :=
    (Finset.mem_inter.mp (Finset.mem_sdiff.mp he).1).1
  have he₃ : e ∈ involved (deltaNu c h12 ν₃) :=
    (Finset.mem_inter.mp (Finset.mem_sdiff.mp he).1).2
  have he₁not : e ∉ involved (deltaNu c h12 ν₁) := (Finset.mem_sdiff.mp he).2
  have hf₂ : f ∈ involved (deltaNu c h12 ν₂) := (Finset.mem_sdiff.mp hf).1
  have hg₃ : g ∈ involved (deltaNu c h12 ν₃) := (Finset.mem_sdiff.mp hg).1
  have hν₁₃ : ν₁ ≠ ν₃ := by
    intro hEq
    exact hb₃not (by simpa [hEq] using hb₁)
  have hν₂₃ : ν₂ ≠ ν₃ := by
    intro hEq
    exact hc₂not (by simpa [hEq] using hc₃)
  have hAcard := involved_deltaNu_card_eq_four c h12 hSC hS4 hν₁s
  have hBcard := involved_deltaNu_card_eq_four c h12 hSC hS4 hν₂s
  have hCcard := involved_deltaNu_card_eq_four c h12 hSC hS4 hν₃s
  have hAset : involved (deltaNu c h12 ν₁) = {a, b, c₀, d} :=
    finset_eq_of_card_four _ ha₁ hb₁ hc₁ hd₁ hAcard hbc hbd hcd hab hac had
  have hBset : involved (deltaNu c h12 ν₂) = {a, b, e, f} :=
    finset_eq_of_card_four _ ha₂ hb₂ he₂ hf₂ hBcard hbe hbf hef hab hae haf
  have hCset : involved (deltaNu c h12 ν₃) = {a, c₀, e, g} :=
    finset_eq_of_card_four _ ha₃ hc₃ he₃ hg₃ hCcard hce hcg heg hac hae hag
  rcases exists_fixed_third_delta_of_shared c h12 hSC hS4 hcomp
      hν₁Δ0 hν₁s hν₁t hν₂s hν₂t hfix₁ hfix₂ hb₁ hb₂ hν₁₂ with
    ⟨ν₄, hν₄B, hν₁₄, hν₂₄, hν₄Δ0, hA4, hB4⟩
  have hν₄s : conjChar c.H0 (s_normalizes_H0 c h12) ν₄.1 = ν₄.1 :=
    (Finset.mem_filter.mp hν₄B).2.1
  have hν₄t : ν₄.1 (tH0 c) = ν₄.1 1 :=
    (Finset.mem_filter.mp hν₄B).2.2.1
  have hb₄ : b ∈ involved (deltaNu c h12 ν₄) := by
    rw [mem_involved_iff]
    exact (Finset.mem_filter.mp hν₄B).2.2.2
  have hν₃₄ : ν₃ ≠ ν₄ := by
    intro hEq
    exact hb₃not (by simpa [← hEq] using hb₄)
  have hfix₄ : (nuHatOrbit c h12 (nuHat c h12 ν₄)).card = 1 :=
    nuHat_fixed_of_BPrime_of_fixed c h12 hSC hS4
      ((mem_involved_iff (deltaNu c h12 ν₁) b).1 hb₁)
      hν₁s hν₁t hfix₁ hν₄B
  rcases exists_fixed_third_delta_of_shared c h12 hSC hS4 hcomp
      hν₁Δ0 hν₁s hν₁t hν₃s hν₃t hfix₁ hfix₃ hc₁ hc₃ hν₁₃ with
    ⟨ν₅, hν₅B, hν₁₅, hν₃₅, hν₅Δ0, hA5, hC5⟩
  have hν₅s : conjChar c.H0 (s_normalizes_H0 c h12) ν₅.1 = ν₅.1 :=
    (Finset.mem_filter.mp hν₅B).2.1
  have hν₅t : ν₅.1 (tH0 c) = ν₅.1 1 :=
    (Finset.mem_filter.mp hν₅B).2.2.1
  have hc₅ : c₀ ∈ involved (deltaNu c h12 ν₅) := by
    rw [mem_involved_iff]
    exact (Finset.mem_filter.mp hν₅B).2.2.2
  have hν₂₅ : ν₂ ≠ ν₅ := by
    intro hEq
    exact hc₂not (by simpa [← hEq] using hc₅)
  have hfix₅ : (nuHatOrbit c h12 (nuHat c h12 ν₅)).card = 1 :=
    nuHat_fixed_of_BPrime_of_fixed c h12 hSC hS4
      ((mem_involved_iff (deltaNu c h12 ν₁) c₀).1 hc₁)
      hν₁s hν₁t hfix₁ hν₅B
  rcases exists_fixed_third_delta_of_shared c h12 hSC hS4 hcomp
      hν₂Δ0 hν₂s hν₂t hν₃s hν₃t hfix₂ hfix₃ he₂ he₃ hν₂₃ with
    ⟨ν₆, hν₆B, hν₂₆, hν₃₆, hν₆Δ0, hB6, hC6⟩
  have hν₆s : conjChar c.H0 (s_normalizes_H0 c h12) ν₆.1 = ν₆.1 :=
    (Finset.mem_filter.mp hν₆B).2.1
  have hν₆t : ν₆.1 (tH0 c) = ν₆.1 1 :=
    (Finset.mem_filter.mp hν₆B).2.2.1
  have he₆ : e ∈ involved (deltaNu c h12 ν₆) := by
    rw [mem_involved_iff]
    exact (Finset.mem_filter.mp hν₆B).2.2.2
  have hν₁₆ : ν₁ ≠ ν₆ := by
    intro hEq
    exact he₁not (by simpa [← hEq] using he₆)
  have hfix₆ : (nuHatOrbit c h12 (nuHat c h12 ν₆)).card = 1 :=
    nuHat_fixed_of_BPrime_of_fixed c h12 hSC hS4
      ((mem_involved_iff (deltaNu c h12 ν₂) e).1 he₂)
      hν₂s hν₂t hfix₂ hν₆B
  exact ⟨ν₃, ν₄, ν₅, ν₆, a, b, c₀, d, e, f, g,
    hν₃s, hν₃t, hfix₃, hν₃Δ0,
    hν₄s, hν₄t, hfix₄, hν₄Δ0,
    hν₅s, hν₅t, hfix₅, hν₅Δ0,
    hν₆s, hν₆t, hfix₆, hν₆Δ0,
    hν₁₃, hν₂₃, hν₁₄, hν₂₄, hν₃₄,
    hν₁₅, hν₃₅, hν₂₅, hν₂₆, hν₃₆, hν₁₆,
    hAset, hBset, hCset, hb₄, hc₅, he₆,
    hA4, hB4, hA5, hC5, hB6, hC6,
    hab, hac, had, hbc, hbd, hcd,
    hae, haf, hag, hbe, hbf, hbg,
    hce, hcf, hcg, hde, hdf, hdg,
    hef, heg, hfg⟩

/-- The finite fixed-incidence analysis leaves only the four-vertex
tetrahedral support configuration. -/
private lemma fixed_incidence_four_configuration (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {Δ0 : Set (ClassFunction G)} (hcomp : IsConnectedComponent c h12 Δ0)
    {ν₁ ν₂ : Irr (↥c.H0)} {χ : Irr G}
    (hν₁Δ0 : deltaNu c h12 ν₁ ∈ Δ0)
    (hν₂Δ0 : deltaNu c h12 ν₂ ∈ Δ0)
    (hν₁s : conjChar c.H0 (s_normalizes_H0 c h12) ν₁.1 = ν₁.1)
    (hν₁t : ν₁.1 (tH0 c) = ν₁.1 1)
    (hν₂s : conjChar c.H0 (s_normalizes_H0 c h12) ν₂.1 = ν₂.1)
    (hν₂t : ν₂.1 (tH0 c) = ν₂.1 1)
    (hfix₁ : (nuHatOrbit c h12 (nuHat c h12 ν₁)).card = 1)
    (hfix₂ : (nuHatOrbit c h12 (nuHat c h12 ν₂)).card = 1)
    (hχ₁ : χ ∈ involved (deltaNu c h12 ν₁))
    (hχ₂ : χ ∈ involved (deltaNu c h12 ν₂))
    (hν₁₂ : ν₁ ≠ ν₂) :
    ∃ ν₃ ν₄ : Irr (↥c.H0), ∃ a b c₀ d e f g h : Irr G,
      conjChar c.H0 (s_normalizes_H0 c h12) ν₃.1 = ν₃.1 ∧
      ν₃.1 (tH0 c) = ν₃.1 1 ∧
      (nuHatOrbit c h12 (nuHat c h12 ν₃)).card = 1 ∧
      deltaNu c h12 ν₃ ∈ Δ0 ∧
      conjChar c.H0 (s_normalizes_H0 c h12) ν₄.1 = ν₄.1 ∧
      ν₄.1 (tH0 c) = ν₄.1 1 ∧
      (nuHatOrbit c h12 (nuHat c h12 ν₄)).card = 1 ∧
      deltaNu c h12 ν₄ ∈ Δ0 ∧
      ν₁ ≠ ν₃ ∧ ν₂ ≠ ν₃ ∧ ν₁ ≠ ν₄ ∧ ν₂ ≠ ν₄ ∧ ν₃ ≠ ν₄ ∧
      involved (deltaNu c h12 ν₁) = {a, b, c₀, d} ∧
      involved (deltaNu c h12 ν₂) = {a, b, e, f} ∧
      involved (deltaNu c h12 ν₃) = {a, c₀, e, g} ∧
      involved (deltaNu c h12 ν₄) = {b, c₀, e, h} ∧
      a ≠ b ∧ a ≠ c₀ ∧ a ≠ d ∧ b ≠ c₀ ∧ b ≠ d ∧ c₀ ≠ d ∧
      a ≠ e ∧ a ≠ f ∧ a ≠ g ∧ b ≠ e ∧ b ≠ f ∧ b ≠ g ∧
      c₀ ≠ e ∧ c₀ ≠ f ∧ c₀ ≠ g ∧ d ≠ e ∧ d ≠ f ∧ d ≠ g ∧
      e ≠ f ∧ e ≠ g ∧ f ≠ g ∧
      h ≠ a ∧ h ≠ b ∧ h ≠ c₀ ∧ h ≠ d ∧ h ≠ e ∧ h ≠ f ∧ h ≠ g := by
  classical
  rcases fixed_six_incidence_data c h12 hSC hS4 hcomp
      hν₁Δ0 hν₂Δ0 hν₁s hν₁t hν₂s hν₂t hfix₁ hfix₂ hχ₁ hχ₂ hν₁₂ with
    ⟨ν₃, ν₄, ν₅, ν₆, a, b, c₀, d, e, f, g,
      hν₃s, hν₃t, hfix₃, hν₃Δ0,
      hν₄s, hν₄t, hfix₄, hν₄Δ0,
      hν₅s, hν₅t, hfix₅, hν₅Δ0,
      hν₆s, hν₆t, hfix₆, hν₆Δ0,
      hν₁₃, hν₂₃, hν₁₄, hν₂₄, hν₃₄,
      hν₁₅, hν₃₅, hν₂₅, hν₂₆, hν₃₆, hν₁₆,
      hAset, hBset, hCset, hb₄, hc₅, he₆,
      hA4, hB4, hA5, hC5, hB6, hC6,
      hab, hac, had, hbc, hbd, hcd,
      hae, haf, hag, hbe, hbf, hbg,
      hce, hcf, hcg, hde, hdf, hdg,
      hef, heg, hfg⟩
  by_cases hν₄₅ : ν₄ = ν₅
  · by_cases hν₄₆ : ν₄ = ν₆
    · subst ν₅
      subst ν₆
      have hb₁ : b ∈ involved (deltaNu c h12 ν₁) := by rw [hAset]; simp
      have hc₁ : c₀ ∈ involved (deltaNu c h12 ν₁) := by rw [hAset]; simp
      have ha₁ : a ∈ involved (deltaNu c h12 ν₁) := by rw [hAset]; simp
      have hd₁ : d ∈ involved (deltaNu c h12 ν₁) := by rw [hAset]; simp
      have hb₂ : b ∈ involved (deltaNu c h12 ν₂) := by rw [hBset]; simp
      have he₂ : e ∈ involved (deltaNu c h12 ν₂) := by rw [hBset]; simp
      have hf₂ : f ∈ involved (deltaNu c h12 ν₂) := by rw [hBset]; simp
      have hc₃ : c₀ ∈ involved (deltaNu c h12 ν₃) := by rw [hCset]; simp
      have he₃ : e ∈ involved (deltaNu c h12 ν₃) := by rw [hCset]; simp
      have hg₃ : g ∈ involved (deltaNu c h12 ν₃) := by rw [hCset]; simp
      have ha₄ : a ∉ involved (deltaNu c h12 ν₄) :=
        third_not_mem_of_inter_two hA4 hb₁ hb₄ hc₁ hc₅ ha₁
          hbc hab.symm hac.symm
      have hd₄ : d ∉ involved (deltaNu c h12 ν₄) :=
        third_not_mem_of_inter_two hA4 hb₁ hb₄ hc₁ hc₅ hd₁
          hbc hbd hcd
      have hf₄ : f ∉ involved (deltaNu c h12 ν₄) :=
        third_not_mem_of_inter_two hB4 hb₂ hb₄ he₂ he₆ hf₂
          hbe hbf hef
      have hg₄ : g ∉ involved (deltaNu c h12 ν₄) :=
        third_not_mem_of_inter_two hC5 hc₃ hc₅ he₃ he₆ hg₃
          hce hcg heg
      have hDcard := involved_deltaNu_card_eq_four c h12 hSC hS4 hν₄s
      rcases exists_fourth_of_card_four hb₄ hc₅ he₆ hbc hbe hce hDcard with
        ⟨h, hh₄, hhb, hhc, hhe, hDset⟩
      have hha : h ≠ a := by
        intro hEq
        exact ha₄ (by simpa [hEq] using hh₄)
      have hhd : h ≠ d := by
        intro hEq
        exact hd₄ (by simpa [hEq] using hh₄)
      have hhf : h ≠ f := by
        intro hEq
        exact hf₄ (by simpa [hEq] using hh₄)
      have hhg : h ≠ g := by
        intro hEq
        exact hg₄ (by simpa [hEq] using hh₄)
      exact ⟨ν₃, ν₄, a, b, c₀, d, e, f, g, h,
        hν₃s, hν₃t, hfix₃, hν₃Δ0,
        hν₄s, hν₄t, hfix₄, hν₄Δ0,
        hν₁₃, hν₂₃, hν₁₄, hν₂₄, hν₃₄,
        hAset, hBset, hCset, hDset,
        hab, hac, had, hbc, hbd, hcd,
        hae, haf, hag, hbe, hbf, hbg,
        hce, hcf, hcg, hde, hdf, hdg,
        hef, heg, hfg, hha, hhb, hhc, hhd, hhe, hhf, hhg⟩
    · exact False.elim (fixed_repeated_incidence_contradiction c h12 hSC hS4
        hν₁s hν₁t hν₂s hν₂t hν₃s hν₃t hν₄s hν₄t hν₆s hν₆t
        hν₁₂ hν₁₃ hν₁₄ hν₁₆ hν₂₃ hν₂₄ hν₂₆ hν₃₄ hν₃₆ hν₄₆
        hAset hBset hCset hb₄ (by simpa [← hν₄₅] using hc₅) he₆
        hB4 (by simpa [← hν₄₅] using hC5) hB6 hC6
        hab hac had hbc hbd hcd hae haf hag hbe hbf hbg hce hcf hcg
        hde hdf hdg hef heg hfg)
  · by_cases hν₄₆ : ν₄ = ν₆
    · have hCset' : involved (deltaNu c h12 ν₃) = {a, e, c₀, g} := by
        simpa [Finset.insert_comm] using hCset
      exact False.elim (fixed_repeated_incidence_contradiction c h12 hSC hS4
        hν₂s hν₂t hν₁s hν₁t hν₃s hν₃t hν₄s hν₄t hν₅s hν₅t
        hν₁₂.symm hν₂₃ hν₂₄ hν₂₅ hν₁₃ hν₁₄ hν₁₅ hν₃₄ hν₃₅ hν₄₅
        hBset hAset hCset' hb₄ (by simpa [← hν₄₆] using he₆) hc₅
        hA4 (by simpa [← hν₄₆] using hC6) hA5 hC5
        hab hae haf hbe hbf hef hac had hag hbc hbd hbg hce.symm hde.symm heg
        hcf.symm hdf.symm hfg hcd hcg hdg)
    · by_cases hν₅₆ : ν₅ = ν₆
      · have hAset' : involved (deltaNu c h12 ν₁) = {a, c₀, b, d} := by
          simpa [Finset.insert_comm] using hAset
        have hBset' : involved (deltaNu c h12 ν₂) = {a, e, b, f} := by
          simpa [Finset.insert_comm] using hBset
        exact False.elim (fixed_repeated_incidence_contradiction c h12 hSC hS4
          hν₃s hν₃t hν₁s hν₁t hν₂s hν₂t hν₅s hν₅t hν₄s hν₄t
          hν₁₃.symm hν₂₃.symm hν₃₅ hν₃₄ hν₁₂ hν₁₅ hν₁₄ hν₂₅ hν₂₄
          (Ne.symm hν₄₅)
          hCset hAset' hBset' hc₅ (by simpa [← hν₅₆] using he₆) hb₄
          hA5 (by simpa [← hν₅₆] using hB6) hA4 hB4
          hac hae hag hce hcg heg hab had haf hbc.symm hcd hcf hbe.symm
          hde.symm hef hbg.symm hdg.symm hfg.symm hbd hbf hdf)
      · exact False.elim (fixed_distinct_incidence_contradiction c h12 hSC hS4
          hν₁s hν₁t hν₂s hν₂t hν₃s hν₃t hν₄s hν₄t hν₅s hν₅t hν₆s hν₆t
          hfix₁ hfix₅ hν₁₂ hν₁₃ hν₂₃ hν₁₄ hν₂₄ hν₃₄
          hν₁₅ hν₂₅ hν₃₅ hν₁₆ hν₂₆ hν₃₆ hν₄₅ hν₄₆ hν₅₆
          hAset hBset hCset hb₄ hc₅ he₆ hA4 hB4 hA5 hC5 hB6 hC6
          hab hac had hbc hbd hcd hae haf hag hbe hbf hbg hce hcf hcg
          hde hdf hdg hef heg hfg)

/-- The saturated tetrahedral support configuration is the whole connected
component: an outside neighbor could share at most one constituent. -/
private lemma fixed_tetrahedron_component_eq (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {Δ0 : Set (ClassFunction G)} (hcomp : IsConnectedComponent c h12 Δ0)
    {ν₁ ν₂ ν₃ ν₄ : Irr (↥c.H0)}
    (hν₁Δ0 : deltaNu c h12 ν₁ ∈ Δ0)
    (hν₂Δ0 : deltaNu c h12 ν₂ ∈ Δ0)
    (hν₃Δ0 : deltaNu c h12 ν₃ ∈ Δ0)
    (hν₄Δ0 : deltaNu c h12 ν₄ ∈ Δ0)
    (hν₁s : conjChar c.H0 (s_normalizes_H0 c h12) ν₁.1 = ν₁.1)
    (hν₁t : ν₁.1 (tH0 c) = ν₁.1 1)
    (hν₂s : conjChar c.H0 (s_normalizes_H0 c h12) ν₂.1 = ν₂.1)
    (hν₂t : ν₂.1 (tH0 c) = ν₂.1 1)
    (hν₃s : conjChar c.H0 (s_normalizes_H0 c h12) ν₃.1 = ν₃.1)
    (hν₃t : ν₃.1 (tH0 c) = ν₃.1 1)
    (hν₄s : conjChar c.H0 (s_normalizes_H0 c h12) ν₄.1 = ν₄.1)
    (hν₄t : ν₄.1 (tH0 c) = ν₄.1 1)
    (hfix₁ : (nuHatOrbit c h12 (nuHat c h12 ν₁)).card = 1)
    (hfix₂ : (nuHatOrbit c h12 (nuHat c h12 ν₂)).card = 1)
    (hfix₃ : (nuHatOrbit c h12 (nuHat c h12 ν₃)).card = 1)
    (hfix₄ : (nuHatOrbit c h12 (nuHat c h12 ν₄)).card = 1)
    (hν₁₂ : ν₁ ≠ ν₂) (hν₁₃ : ν₁ ≠ ν₃) (hν₁₄ : ν₁ ≠ ν₄)
    (hν₂₃ : ν₂ ≠ ν₃) (hν₂₄ : ν₂ ≠ ν₄) (hν₃₄ : ν₃ ≠ ν₄)
    {a b c₀ d e f g h : Irr G}
    (hAset : involved (deltaNu c h12 ν₁) = {a, b, c₀, d})
    (hBset : involved (deltaNu c h12 ν₂) = {a, b, e, f})
    (hCset : involved (deltaNu c h12 ν₃) = {a, c₀, e, g})
    (hDset : involved (deltaNu c h12 ν₄) = {b, c₀, e, h}) :
    Δ0 = ({deltaNu c h12 ν₁, deltaNu c h12 ν₂,
      deltaNu c h12 ν₃, deltaNu c h12 ν₄} : Set (ClassFunction G)) := by
  classical
  let T : Set (ClassFunction G) :=
    {deltaNu c h12 ν₁, deltaNu c h12 ν₂,
      deltaNu c h12 ν₃, deltaNu c h12 ν₄}
  have ha₁ : a ∈ involved (deltaNu c h12 ν₁) := by rw [hAset]; simp
  have hb₁ : b ∈ involved (deltaNu c h12 ν₁) := by rw [hAset]; simp
  have hc₁ : c₀ ∈ involved (deltaNu c h12 ν₁) := by rw [hAset]; simp
  have ha₂ : a ∈ involved (deltaNu c h12 ν₂) := by rw [hBset]; simp
  have hb₂ : b ∈ involved (deltaNu c h12 ν₂) := by rw [hBset]; simp
  have he₂ : e ∈ involved (deltaNu c h12 ν₂) := by rw [hBset]; simp
  have ha₃ : a ∈ involved (deltaNu c h12 ν₃) := by rw [hCset]; simp
  have hc₃ : c₀ ∈ involved (deltaNu c h12 ν₃) := by rw [hCset]; simp
  have he₃ : e ∈ involved (deltaNu c h12 ν₃) := by rw [hCset]; simp
  have hb₄ : b ∈ involved (deltaNu c h12 ν₄) := by rw [hDset]; simp
  have hc₄ : c₀ ∈ involved (deltaNu c h12 ν₄) := by rw [hDset]; simp
  have he₄ : e ∈ involved (deltaNu c h12 ν₄) := by rw [hDset]; simp
  have ha₁B := BPrime_of_involved c h12 hν₁s hν₁t ha₁
  have ha₂B := BPrime_of_involved c h12 hν₂s hν₂t ha₂
  have ha₃B := BPrime_of_involved c h12 hν₃s hν₃t ha₃
  have hb₁B := BPrime_of_involved c h12 hν₁s hν₁t hb₁
  have hb₂B := BPrime_of_involved c h12 hν₂s hν₂t hb₂
  have hb₄B := BPrime_of_involved c h12 hν₄s hν₄t hb₄
  have hc₁B := BPrime_of_involved c h12 hν₁s hν₁t hc₁
  have hc₃B := BPrime_of_involved c h12 hν₃s hν₃t hc₃
  have hc₄B := BPrime_of_involved c h12 hν₄s hν₄t hc₄
  have he₂B := BPrime_of_involved c h12 hν₂s hν₂t he₂
  have he₃B := BPrime_of_involved c h12 hν₃s hν₃t he₃
  have he₄B := BPrime_of_involved c h12 hν₄s hν₄t he₄
  have hrepr := exists_fixed_witness_of_Delta0_of_fixed c h12 hSC hS4
    hcomp hν₁s hν₁t hν₁Δ0 hfix₁
  have hTsub : T ⊆ Δ0 := by
    intro δ hδ
    change δ ∈ ({deltaNu c h12 ν₁, deltaNu c h12 ν₂,
      deltaNu c h12 ν₃, deltaNu c h12 ν₄} : Set (ClassFunction G)) at hδ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hδ
    rcases hδ with rfl | rfl | rfl | rfl
    · exact hν₁Δ0
    · exact hν₂Δ0
    · exact hν₃Δ0
    · exact hν₄Δ0
  have hclosed : ∀ {x y : ClassFunction G}, x ∈ T → y ∈ Δ0 →
      deltaAdjacent c h12 x y → y ∈ T := by
    intro x y hx hy hadj
    by_cases hy₁ : y = deltaNu c h12 ν₁
    · rw [hy₁]
      simp [T]
    by_cases hy₂ : y = deltaNu c h12 ν₂
    · rw [hy₂]
      simp [T]
    by_cases hy₃ : y = deltaNu c h12 ν₃
    · rw [hy₃]
      simp [T]
    by_cases hy₄ : y = deltaNu c h12 ν₄
    · rw [hy₄]
      simp [T]
    rcases hrepr y hy with ⟨ν, _, hEqy, hνs, hνt, hfixν⟩
    have hν₁ : ν ≠ ν₁ := by
      intro hEq
      apply hy₁
      rw [hEqy, hEq]
    have hν₂ : ν ≠ ν₂ := by
      intro hEq
      apply hy₂
      rw [hEqy, hEq]
    have hν₃ : ν ≠ ν₃ := by
      intro hEq
      apply hy₃
      rw [hEqy, hEq]
    have hν₄ : ν ≠ ν₄ := by
      intro hEq
      apply hy₄
      rw [hEqy, hEq]
    have haν : a ∉ involved (deltaNu c h12 ν) :=
      not_involved_of_fourth c h12 hSC hS4 hνs hνt (Or.inl a.2)
        ha₁B ha₂B ha₃B hν₁₂ hν₁₃ hν₂₃ hν₁ hν₂ hν₃
    have hbν : b ∉ involved (deltaNu c h12 ν) :=
      not_involved_of_fourth c h12 hSC hS4 hνs hνt (Or.inl b.2)
        hb₁B hb₂B hb₄B hν₁₂ hν₁₄ hν₂₄ hν₁ hν₂ hν₄
    have hcν : c₀ ∉ involved (deltaNu c h12 ν) :=
      not_involved_of_fourth c h12 hSC hS4 hνs hνt (Or.inl c₀.2)
        hc₁B hc₃B hc₄B hν₁₃ hν₁₄ hν₃₄ hν₁ hν₃ hν₄
    have heν : e ∉ involved (deltaNu c h12 ν) :=
      not_involved_of_fourth c h12 hSC hS4 hνs hνt (Or.inl e.2)
        he₂B he₃B he₄B hν₂₃ hν₂₄ hν₃₄ hν₂ hν₃ hν₄
    change x ∈ ({deltaNu c h12 ν₁, deltaNu c h12 ν₂,
      deltaNu c h12 ν₃, deltaNu c h12 ν₄} : Set (ClassFunction G)) at hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have hadj' : deltaAdjacent c h12 (deltaNu c h12 ν₁)
          (deltaNu c h12 ν) := by simpa [hEqy] using hadj
      have hδne : deltaNu c h12 ν₁ ≠ deltaNu c h12 ν := hadj'.2.2.1
      have hpair := involved_inter_card_eq_two_of_adjacent_fixed c h12 hSC hS4
        hν₁s hν₁t hνs hνt hfix₁ hδne
        (exists_shared_constituent_of_adjacent c h12 hadj')
      have hle := inter_card_le_one_of_three_not_mem hAset haν hbν hcν
      omega
    · have hadj' : deltaAdjacent c h12 (deltaNu c h12 ν₂)
          (deltaNu c h12 ν) := by simpa [hEqy] using hadj
      have hδne : deltaNu c h12 ν₂ ≠ deltaNu c h12 ν := hadj'.2.2.1
      have hpair := involved_inter_card_eq_two_of_adjacent_fixed c h12 hSC hS4
        hν₂s hν₂t hνs hνt hfix₂ hδne
        (exists_shared_constituent_of_adjacent c h12 hadj')
      have hle := inter_card_le_one_of_three_not_mem hBset haν hbν heν
      omega
    · have hadj' : deltaAdjacent c h12 (deltaNu c h12 ν₃)
          (deltaNu c h12 ν) := by simpa [hEqy] using hadj
      have hδne : deltaNu c h12 ν₃ ≠ deltaNu c h12 ν := hadj'.2.2.1
      have hpair := involved_inter_card_eq_two_of_adjacent_fixed c h12 hSC hS4
        hν₃s hν₃t hνs hνt hfix₃ hδne
        (exists_shared_constituent_of_adjacent c h12 hadj')
      have hle := inter_card_le_one_of_three_not_mem hCset haν hcν heν
      omega
    · have hadj' : deltaAdjacent c h12 (deltaNu c h12 ν₄)
          (deltaNu c h12 ν) := by simpa [hEqy] using hadj
      have hδne : deltaNu c h12 ν₄ ≠ deltaNu c h12 ν := hadj'.2.2.1
      have hpair := involved_inter_card_eq_two_of_adjacent_fixed c h12 hSC hS4
        hν₄s hν₄t hνs hνt hfix₄ hδne
        (exists_shared_constituent_of_adjacent c h12 hadj')
      have hle := inter_card_le_one_of_three_not_mem hDset hbν hcν heν
      omega
  have hpath_mem : ∀ {x : ClassFunction G},
      Relation.ReflTransGen (deltaAdjacent c h12) (deltaNu c h12 ν₁) x →
      x ∈ Δ0 := by
    intro x hx
    have hrev : Relation.ReflTransGen (deltaAdjacent c h12) x
        (deltaNu c h12 ν₁) :=
      reflTransGen_symm (fun {p q : ClassFunction G} hpq =>
        deltaAdjacent_symm c h12 hpq) hx
    refine Relation.ReflTransGen.head_induction_on hrev
      (motive := fun y _ => y ∈ Δ0) hν₁Δ0 ?_
    intro p q hpq hpath ih
    by_contra hnot
    exact (hcomp.2.2.2 p hnot q ih) hpq
  have hsub : Δ0 ⊆ T := by
    intro δ hδ
    have hpath : Relation.ReflTransGen (deltaAdjacent c h12)
        (deltaNu c h12 ν₁) δ := hcomp.2.2.1 _ _ hν₁Δ0 hδ
    have hboth : δ ∈ Δ0 ∧ δ ∈ T := by
      induction hpath with
      | refl => exact ⟨hν₁Δ0, by simp [T]⟩
      | @tail x y hprev hadj ih =>
        have hxΔ0 : x ∈ Δ0 := hpath_mem hprev
        have hxBoth : x ∈ Δ0 ∧ x ∈ T := ih hxΔ0
        have hxT : x ∈ T := hxBoth.2
        have hyΔ0 : y ∈ Δ0 := hpath_mem (hprev.tail hadj)
        exact ⟨hyΔ0, hclosed hxT hyΔ0 hadj⟩
    exact hboth.2
  change Δ0 = T
  exact Set.Subset.antisymm hsub hTsub

private lemma BPrime_eq_singleton_of_tetrahedron
    (h12 : Hyp12 c) (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {Δ0 : Set (ClassFunction G)}
    (hcomp : IsConnectedComponent c h12 Δ0)
    {ν₀ ν₁ ν₂ ν₃ : Irr (↥c.H0)}
    (hν₀s : conjChar c.H0 (s_normalizes_H0 c h12) ν₀.1 = ν₀.1)
    (hν₀t : ν₀.1 (tH0 c) = ν₀.1 1)
    (hν₁s : conjChar c.H0 (s_normalizes_H0 c h12) ν₁.1 = ν₁.1)
    (hν₁t : ν₁.1 (tH0 c) = ν₁.1 1)
    (hν₂s : conjChar c.H0 (s_normalizes_H0 c h12) ν₂.1 = ν₂.1)
    (hν₂t : ν₂.1 (tH0 c) = ν₂.1 1)
    (hν₃s : conjChar c.H0 (s_normalizes_H0 c h12) ν₃.1 = ν₃.1)
    (hν₃t : ν₃.1 (tH0 c) = ν₃.1 1)
    (hfixset : Δ0 = ({deltaNu c h12 ν₀, deltaNu c h12 ν₁,
      deltaNu c h12 ν₂, deltaNu c h12 ν₃} : Set (ClassFunction G)))
    (hδ₀ : deltaNu c h12 ν₀ ∈ Δ0)
    {χ : Irr G}
    (hχ₀ : χ ∈ involved (deltaNu c h12 ν₀))
    (hχ₁ : χ ∉ involved (deltaNu c h12 ν₁))
    (hχ₂ : χ ∉ involved (deltaNu c h12 ν₂))
    (hχ₃ : χ ∉ involved (deltaNu c h12 ν₃)) :
    BPrimeOf c h12 χ.1 = {ν₀} := by
  classical
  ext ν
  constructor
  · intro hνB
    have hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 :=
      (Finset.mem_filter.mp hνB).2.1
    have hνt : ν.1 (tH0 c) = ν.1 1 :=
      (Finset.mem_filter.mp hνB).2.2.1
    have hχν : χ ∈ involved (deltaNu c h12 ν) :=
      (mem_involved_iff (deltaNu c h12 ν) χ).2
        (Finset.mem_filter.mp hνB).2.2.2
    have hδν := deltaNu_mem_Delta0_of_BPrime c h12 hcomp hδ₀ hχ₀ hνB
    rw [hfixset] at hδν
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hδν
    rcases hδν with h | h | h | h
    · have heq := deltaNu_injective c h12 hSC hS4 hνs hνt hν₀s hν₀t h
      simpa [heq]
    · exfalso
      apply hχ₁
      have heq := deltaNu_injective c h12 hSC hS4 hνs hνt hν₁s hν₁t h
      simpa [heq] using hχν
    · exfalso
      apply hχ₂
      have heq := deltaNu_injective c h12 hSC hS4 hνs hνt hν₂s hν₂t h
      simpa [heq] using hχν
    · exfalso
      apply hχ₃
      have heq := deltaNu_injective c h12 hSC hS4 hνs hνt hν₃s hν₃t h
      simpa [heq] using hχν
  · intro hν
    simp only [Finset.mem_singleton] at hν
    subst ν
    exact BPrime_of_involved c h12 hν₀s hν₀t hχ₀

private noncomputable def tripleFinset {α : Type*}
    (a b d : α) : Finset α := by
  classical
  exact {a, b, d}

private lemma BPrime_eq_triple_of_tetrahedron
    (h12 : Hyp12 c) (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {Δ0 : Set (ClassFunction G)}
    (hcomp : IsConnectedComponent c h12 Δ0)
    {ν₀ ν₁ ν₂ ν₃ : Irr (↥c.H0)}
    (hν₀s : conjChar c.H0 (s_normalizes_H0 c h12) ν₀.1 = ν₀.1)
    (hν₀t : ν₀.1 (tH0 c) = ν₀.1 1)
    (hν₁s : conjChar c.H0 (s_normalizes_H0 c h12) ν₁.1 = ν₁.1)
    (hν₁t : ν₁.1 (tH0 c) = ν₁.1 1)
    (hν₂s : conjChar c.H0 (s_normalizes_H0 c h12) ν₂.1 = ν₂.1)
    (hν₂t : ν₂.1 (tH0 c) = ν₂.1 1)
    (hν₃s : conjChar c.H0 (s_normalizes_H0 c h12) ν₃.1 = ν₃.1)
    (hν₃t : ν₃.1 (tH0 c) = ν₃.1 1)
    (hfixset : Δ0 = ({deltaNu c h12 ν₀, deltaNu c h12 ν₁,
      deltaNu c h12 ν₂, deltaNu c h12 ν₃} : Set (ClassFunction G)))
    (hδ₀ : deltaNu c h12 ν₀ ∈ Δ0)
    {χ : Irr G}
    (hχ₀ : χ ∈ involved (deltaNu c h12 ν₀))
    (hχ₁ : χ ∈ involved (deltaNu c h12 ν₁))
    (hχ₂ : χ ∈ involved (deltaNu c h12 ν₂))
    (hχ₃ : χ ∉ involved (deltaNu c h12 ν₃)) :
    BPrimeOf c h12 χ.1 = tripleFinset ν₀ ν₁ ν₂ := by
  classical
  ext ν
  constructor
  · intro hνB
    have hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 :=
      (Finset.mem_filter.mp hνB).2.1
    have hνt : ν.1 (tH0 c) = ν.1 1 :=
      (Finset.mem_filter.mp hνB).2.2.1
    have hχν : χ ∈ involved (deltaNu c h12 ν) :=
      (mem_involved_iff (deltaNu c h12 ν) χ).2
        (Finset.mem_filter.mp hνB).2.2.2
    have hδν := deltaNu_mem_Delta0_of_BPrime c h12 hcomp hδ₀ hχ₀ hνB
    rw [hfixset] at hδν
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hδν
    rcases hδν with h | h | h | h
    · have heq := deltaNu_injective c h12 hSC hS4 hνs hνt hν₀s hν₀t h
      simp [tripleFinset, heq]
    · have heq := deltaNu_injective c h12 hSC hS4 hνs hνt hν₁s hν₁t h
      simp [tripleFinset, heq]
    · have heq := deltaNu_injective c h12 hSC hS4 hνs hνt hν₂s hν₂t h
      simp [tripleFinset, heq]
    · exfalso
      apply hχ₃
      have heq := deltaNu_injective c h12 hSC hS4 hνs hνt hν₃s hν₃t h
      simpa [heq] using hχν
  · intro hν
    simp only [tripleFinset, Finset.mem_insert, Finset.mem_singleton] at hν
    rcases hν with rfl | rfl | rfl
    · exact BPrime_of_involved c h12 hν₀s hν₀t hχ₀
    · exact BPrime_of_involved c h12 hν₁s hν₁t hχ₁
    · exact BPrime_of_involved c h12 hν₂s hν₂t hχ₂

/-! The fixed tetrahedron is excluded by the class-sum parity argument.  The
following small helpers isolate the group-theoretic reduction from the
character-theoretic calculation. -/

private lemma odd_class_has_centralizing_rep (x : G)
    (hodd : Odd (Nat.card (ConjClasses.mk x).carrier)) :
    ∃ y : G, y ∈ (ConjClasses.mk x).carrier ∧ y ∈ centralizerS c := by
  classical
  let : MulAction ↥(c.S : Subgroup G) G :=
    MulAction.compHom G
      ((ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom.comp
        (c.S : Subgroup G).subtype)
  let C : SubMulAction ↥(c.S : Subgroup G) G := {
    carrier := (ConjClasses.mk x).carrier
    smul_mem' := by
      intro s y hy
      have hconj : ConjClasses.mk ((s : G) * y * (s : G)⁻¹) =
          ConjClasses.mk y := by
        rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
        exact ⟨(s : G)⁻¹, by group⟩
      rw [ConjClasses.mem_carrier_iff_mk_eq] at hy ⊢
      exact hconj.trans hy }
  have hnot : ¬ 2 ∣ Nat.card C := by
    have hnot' : ¬ 2 ∣ Nat.card (ConjClasses.mk x).carrier :=
      (by simpa [even_iff_two_dvd] using (Nat.not_even_iff_odd.mpr hodd))
    let e : C ≃ (ConjClasses.mk x).carrier := {
      toFun := fun y => ⟨(y : G), y.2⟩
      invFun := fun y => ⟨(y : G), y.2⟩
      left_inv := by intro y; rfl
      right_inv := by intro y; rfl }
    rw [Nat.card_congr e]
    exact hnot'
  have hfixed := c.S.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card C hnot
  rcases hfixed with ⟨y, hy⟩
  refine ⟨(y : G), y.2, ?_⟩
  change (y : G) ∈ Subgroup.centralizer ((c.S : Subgroup G) : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have heq := congrArg (fun z : C => (z : G))
    ((MulAction.mem_fixedPoints.mp hy) (⟨s, hs⟩ : ↥(c.S : Subgroup G)))
  change s * (y : G) * s⁻¹ = (y : G) at heq
  calc
    s * (y : G) = (s * (y : G) * s⁻¹) * s := by group
    _ = (y : G) * s := by rw [heq]

private lemma centralizer_rep (hS4 : Section4Hyp c) {y : G}
    (hy : y ∈ centralizerS c) :
    (∃ b : ↥c.B, y = (b : G)) ∨
      ∃ b : ↥c.B, ∃ n : G, n ∈ normalizerS c ∧
        n⁻¹ * y * n = c.t * (b : G) := by
  classical
  let yC : ↥(centralizerS c) := ⟨y, hy⟩
  let p : ↥(c.S : Subgroup G) × ↥c.B := centralizerS_equiv c hS4 yC
  have hprod : (p.1 : G) * (p.2 : G) = y := by
    have heq := congrArg Subtype.val
      ((centralizerS_equiv c hS4).symm_apply_apply yC)
    exact heq
  by_cases hs : p.1 = 1
  · left
    refine ⟨p.2, ?_⟩
    rw [← hprod, hs]
    simp
  · right
    rcases exists_normalizer_conj_t c hS4 p.1 hs with ⟨n, hn, hnt⟩
    have hninv : n⁻¹ ∈ normalizerS c := (normalizerS c).inv_mem hn
    let b : ↥c.B :=
      ⟨n⁻¹ * (p.2 : G) * (n⁻¹)⁻¹,
        B_conj_mem_of_normalizerS c hninv p.2⟩
    refine ⟨b, n, hn, ?_⟩
    dsimp [b]
    rw [← hprod, ← hnt]
    group

private lemma odd_class_common_reduction (hS4 : Section4Hyp c)
    {x : G} (hodd : Odd (Nat.card (ConjClasses.mk x).carrier)) :
    ∃ b : ↥c.B, ∀ (φ : Theory.Character.ClassFunction G),
      Theory.Character.IsGeneralizedCharacter φ →
      CongruentModTwo (φ x) (φ (b : G)) := by
  classical
  rcases odd_class_has_centralizing_rep c x hodd with ⟨y, hyclass, hyC⟩
  rcases centralizer_rep c hS4 hyC with ⟨b, hby⟩ | ⟨b, n, hn, hEq⟩
  · refine ⟨b, ?_⟩
    intro φ hφ
    have hclass := isClassFunction_of_isGeneralizedCharacter hφ
    have hxy : φ x = φ y := by
      have hconj : IsConj y x :=
        (ConjClasses.mk_eq_mk_iff_isConj.mp
          ((ConjClasses.mem_carrier_iff_mk_eq.mp hyclass)))
      rcases isConj_iff.mp hconj with ⟨g, hg⟩
      have hv := hclass y g
      rwa [hg] at hv
    rw [hby] at hxy
    exact CongruentModTwo.of_eq hxy
  · refine ⟨b, ?_⟩
    intro φ hφ
    have hclass := isClassFunction_of_isGeneralizedCharacter hφ
    have hxy : φ x = φ y := by
      have hconj : IsConj y x :=
        (ConjClasses.mk_eq_mk_iff_isConj.mp
          ((ConjClasses.mem_carrier_iff_mk_eq.mp hyclass)))
      rcases isConj_iff.mp hconj with ⟨g, hg⟩
      have hv := hclass y g
      rwa [hg] at hv
    have hval : φ x = φ (c.t * (b : G)) := by
      have hv := hclass y n⁻¹
      simp only [inv_inv] at hv
      rw [hEq] at hv
      exact hxy.trans hv.symm
    have hbcent : (b : G) ∈ GorensteinWalter.centralizerIn (⊤ : Subgroup G) c.t := by
      rw [GorensteinWalter.centralizerIn]
      constructor
      · simp
      · change (b : G) ∈ Subgroup.centralizer ({c.t} : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        have hzt : z = c.t := by simpa using hz
        subst z
        exact (Subgroup.mem_centralizer_iff.mp (B_le_centralizerS c b.2))
          c.t (c.S0_le_S c.t_mem_S0)
    have hbodd : Nat.Coprime 2 (orderOf (b : G)) := by
      have horder : orderOf (b : G) = orderOf b :=
        orderOf_injective c.B.subtype (Subgroup.subtype_injective c.B) b
      rw [horder]
      exact Nat.Coprime.of_dvd_right
        (orderOf_dvd_card (G := ↥c.B) (x := b))
        (by simpa [Nat.card_eq_fintype_card] using (B_coprime_two c))
    exact (CongruentModTwo.of_eq hval).trans
      (lemma_1_6 φ hφ c.t_involution hbcent hbodd)

private lemma representation_degree_odd
    {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    [Representation.IsIrreducible ρ] {χ : Irr G}
    (hχρ : χ.1 = ρ.character)
    (hodd : ∃ m : ℤ, (m : ℂ) = χ.1 1 ∧ Odd m) :
    Odd (Module.finrank ℂ (Fin n → ℂ)) := by
  rcases hodd with ⟨m, hm, hmodd⟩
  have hchar : χ.1 1 = (Module.finrank ℂ (Fin n → ℂ) : ℂ) := by
    rw [hχρ]
    simp [Representation.character]
  have hmeq : m = (Module.finrank ℂ (Fin n → ℂ) : ℤ) := by
    exact_mod_cast hm.trans hchar
  rw [hmeq] at hmodd
  exact_mod_cast hmodd

private noncomputable def classRepChoice (s : ConjClasses G) : G :=
  Classical.choose (ConjClasses.exists_rep s)

private lemma classRepChoice_spec (s : ConjClasses G) :
    ConjClasses.mk (classRepChoice s) = s :=
  Classical.choose_spec (ConjClasses.exists_rep s)

private noncomputable def classSumCoefficient
    (i j s : ConjClasses G) : ℕ :=
  Theory.Character.classSumPairCountMul i j (classRepChoice s)

private lemma classSumCoefficient_data :
    ∀ i j s : ConjClasses G, ∀ x : G, x ∈ s.carrier →
      classSumCoefficient i j s =
        Nat.card {p : i.carrier × j.carrier // p.1.1 * p.2.1 = x} := by
  classical
  intro i j s x hx
  have hxmk : ConjClasses.mk x = s :=
    ConjClasses.mem_carrier_iff_mk_eq.mp hx
  have hconj : IsConj (classRepChoice s) x :=
    ConjClasses.mk_eq_mk_iff_isConj.mp
      ((classRepChoice_spec s).trans hxmk.symm)
  rcases isConj_iff.mp hconj with ⟨g, hg⟩
  have hcf :=
    Theory.Character.classSumPairCountMul_isClassFunction (G := G) i j
      (classRepChoice s) g
  rw [hg] at hcf
  have hnat :
      Theory.Character.classSumPairCountMul i j (classRepChoice s) =
        Theory.Character.classSumPairCountMul i j x := by
    exact Nat.cast_injective hcf.symm
  rw [classSumCoefficient, hnat]
  rfl

private lemma classSum_products_congr
    {V₀ V₁ V₂ V₃ : Type*}
    [AddCommGroup V₀] [Module ℂ V₀] [FiniteDimensional ℂ V₀]
    [AddCommGroup V₁] [Module ℂ V₁] [FiniteDimensional ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] [FiniteDimensional ℂ V₂]
    [AddCommGroup V₃] [Module ℂ V₃] [FiniteDimensional ℂ V₃]
    (ρ₀ : Representation ℂ G V₀) [Representation.IsIrreducible ρ₀]
    (ρ₁ : Representation ℂ G V₁) [Representation.IsIrreducible ρ₁]
    (ρ₂ : Representation ℂ G V₂) [Representation.IsIrreducible ρ₂]
    (ρ₃ : Representation ℂ G V₃) [Representation.IsIrreducible ρ₃]
    (hscalar : ∀ s : ConjClasses G,
      CongruentModTwo
        (Theory.Character.classSumScalar (ρ := ρ₀) s)
        (Theory.Character.classSumScalar (ρ := ρ₁) s +
          Theory.Character.classSumScalar (ρ := ρ₂) s +
          Theory.Character.classSumScalar (ρ := ρ₃) s))
    (i j : ConjClasses G) :
    CongruentModTwo
      (Theory.Character.classSumScalar (ρ := ρ₁) i *
          Theory.Character.classSumScalar (ρ := ρ₁) j +
        Theory.Character.classSumScalar (ρ := ρ₂) i *
          Theory.Character.classSumScalar (ρ := ρ₂) j +
        Theory.Character.classSumScalar (ρ := ρ₃) i *
          Theory.Character.classSumScalar (ρ := ρ₃) j)
      (Theory.Character.classSumScalar (ρ := ρ₀) i *
        Theory.Character.classSumScalar (ρ := ρ₀) j) := by
  classical
  let : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)
  let A : ConjClasses G → ConjClasses G → ConjClasses G → ℕ :=
    classSumCoefficient
  have hdata : ∀ i j s : ConjClasses G, ∀ x : G, x ∈ s.carrier →
      A i j s = Nat.card {p : i.carrier × j.carrier //
        p.1.1 * p.2.1 = x} := by
    exact classSumCoefficient_data
  have hprod₀ :=
    Theory.Character.classSumScalar_mul_eq_sum_of_coefficients
      ρ₀ A hdata i j
  have hprod₁ :=
    Theory.Character.classSumScalar_mul_eq_sum_of_coefficients
      ρ₁ A hdata i j
  have hprod₂ :=
    Theory.Character.classSumScalar_mul_eq_sum_of_coefficients
      ρ₂ A hdata i j
  have hprod₃ :=
    Theory.Character.classSumScalar_mul_eq_sum_of_coefficients
      ρ₃ A hdata i j
  have hleft :
      Theory.Character.classSumScalar (ρ := ρ₁) i *
          Theory.Character.classSumScalar (ρ := ρ₁) j +
        Theory.Character.classSumScalar (ρ := ρ₂) i *
          Theory.Character.classSumScalar (ρ := ρ₂) j +
        Theory.Character.classSumScalar (ρ := ρ₃) i *
          Theory.Character.classSumScalar (ρ := ρ₃) j =
      ∑ s : ConjClasses G, (A i j s : ℂ) *
        (Theory.Character.classSumScalar (ρ := ρ₁) s +
          Theory.Character.classSumScalar (ρ := ρ₂) s +
          Theory.Character.classSumScalar (ρ := ρ₃) s) := by
    rw [hprod₁, hprod₂, hprod₃]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  have hsum : CongruentModTwo
      (∑ s : ConjClasses G, (A i j s : ℂ) *
        (Theory.Character.classSumScalar (ρ := ρ₁) s +
          Theory.Character.classSumScalar (ρ := ρ₂) s +
          Theory.Character.classSumScalar (ρ := ρ₃) s))
      (∑ s : ConjClasses G, (A i j s : ℂ) *
        Theory.Character.classSumScalar (ρ := ρ₀) s) := by
    apply CongruentModTwo.sum
    intro s
    exact CongruentModTwo.mul_right (CongruentModTwo.symm (hscalar s))
      (isIntegral_natCast (A i j s))
  exact (CongruentModTwo.of_eq hleft).trans
    (hsum.trans (CongruentModTwo.of_eq hprod₀.symm))

private lemma classSum_scalar_congr
    (c : Hyp11 G) (hS4 : Section4Hyp c)
    {V₀ V₁ V₂ V₃ : Type*}
    [AddCommGroup V₀] [Module ℂ V₀] [FiniteDimensional ℂ V₀]
    [AddCommGroup V₁] [Module ℂ V₁] [FiniteDimensional ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] [FiniteDimensional ℂ V₂]
    [AddCommGroup V₃] [Module ℂ V₃] [FiniteDimensional ℂ V₃]
    (ρ₀ : Representation ℂ G V₀) [Representation.IsIrreducible ρ₀]
    (ρ₁ : Representation ℂ G V₁) [Representation.IsIrreducible ρ₁]
    (ρ₂ : Representation ℂ G V₂) [Representation.IsIrreducible ρ₂]
    (ρ₃ : Representation ℂ G V₃) [Representation.IsIrreducible ρ₃]
    {χ₀ χ₁ χ₂ χ₃ : Theory.Character.ClassFunction G}
    (hχ₀ : χ₀ = ρ₀.character) (hχ₁ : χ₁ = ρ₁.character)
    (hχ₂ : χ₂ = ρ₂.character) (hχ₃ : χ₃ = ρ₃.character)
    (hgen₀ : Theory.Character.IsGeneralizedCharacter χ₀)
    (hgen₁ : Theory.Character.IsGeneralizedCharacter χ₁)
    (hgen₂ : Theory.Character.IsGeneralizedCharacter χ₂)
    (hgen₃ : Theory.Character.IsGeneralizedCharacter χ₃)
    (hdeg₀ : Odd (Module.finrank ℂ V₀))
    (hdeg₁ : Odd (Module.finrank ℂ V₁))
    (hdeg₂ : Odd (Module.finrank ℂ V₂))
    (hdeg₃ : Odd (Module.finrank ℂ V₃))
    (hB : ∀ b : ↥c.B,
      CongruentModTwo (χ₀ (b : G))
        (χ₁ (b : G) + χ₂ (b : G) + χ₃ (b : G))) :
    ∀ s : ConjClasses G,
      CongruentModTwo
        (Theory.Character.classSumScalar (ρ := ρ₀) s)
        (Theory.Character.classSumScalar (ρ := ρ₁) s +
          Theory.Character.classSumScalar (ρ := ρ₂) s +
          Theory.Character.classSumScalar (ρ := ρ₃) s) := by
  classical
  intro s
  rcases ConjClasses.exists_rep s with ⟨x, hxs⟩
  have hx : x ∈ s.carrier := (ConjClasses.mem_carrier_iff_mk_eq).2 hxs
  by_cases hodd : Odd (Nat.card s.carrier)
  · have hoddx : Odd (Nat.card (ConjClasses.mk x).carrier) := by
      simpa [hxs] using hodd
    rcases odd_class_common_reduction c hS4 hoddx with ⟨b, hb⟩
    have hbH0 : (b : G) ∈ c.H0 :=
      U_le_H0 c (mem_U_of_mem_B_s4 c b.2)
    have hsc₀ : CongruentModTwo
        (Theory.Character.classSumScalar (ρ := ρ₀) s) (χ₀ x) := by
      simpa [hxs] using ((classSumScalar_congruent_character_of_odd_degree_and_class
        ρ₀ x hdeg₀ hoddx).trans
          (CongruentModTwo.of_eq (congrFun hχ₀.symm x)))
    have hsc₁ : CongruentModTwo
        (Theory.Character.classSumScalar (ρ := ρ₁) s) (χ₁ x) := by
      simpa [hxs] using ((classSumScalar_congruent_character_of_odd_degree_and_class
        ρ₁ x hdeg₁ hoddx).trans
          (CongruentModTwo.of_eq (congrFun hχ₁.symm x)))
    have hsc₂ : CongruentModTwo
        (Theory.Character.classSumScalar (ρ := ρ₂) s) (χ₂ x) := by
      simpa [hxs] using ((classSumScalar_congruent_character_of_odd_degree_and_class
        ρ₂ x hdeg₂ hoddx).trans
          (CongruentModTwo.of_eq (congrFun hχ₂.symm x)))
    have hsc₃ : CongruentModTwo
        (Theory.Character.classSumScalar (ρ := ρ₃) s) (χ₃ x) := by
      simpa [hxs] using ((classSumScalar_congruent_character_of_odd_degree_and_class
        ρ₃ x hdeg₃ hoddx).trans
          (CongruentModTwo.of_eq (congrFun hχ₃.symm x)))
    have hred₀ := hb χ₀ hgen₀
    have hred₁ := hb χ₁ hgen₁
    have hred₂ := hb χ₂ hgen₂
    have hred₃ := hb χ₃ hgen₃
    have hB' := hB b
    have h0 := hsc₀.trans (hred₀.trans hB')
    have h123 : CongruentModTwo
        (χ₁ x + χ₂ x + χ₃ x)
        (χ₁ (b : G) + χ₂ (b : G) + χ₃ (b : G)) := by
      exact (hred₁.add hred₂).add hred₃
    have hsumsc : CongruentModTwo
        (Theory.Character.classSumScalar (ρ := ρ₁) s +
          Theory.Character.classSumScalar (ρ := ρ₂) s +
          Theory.Character.classSumScalar (ρ := ρ₃) s)
        (χ₁ x + χ₂ x + χ₃ x) := by
      exact (hsc₁.add hsc₂).add hsc₃
    exact h0.trans (h123.symm.trans hsumsc.symm)
  · have heven : Even (Nat.card s.carrier) :=
      (Nat.even_or_odd (Nat.card s.carrier)).resolve_right hodd
    have hevenx : Even (Nat.card (ConjClasses.mk x).carrier) := by
      simpa [hxs] using heven
    have h0 := classSumScalar_congruent_zero_of_odd_degree_and_even_class
      ρ₀ x hdeg₀ hevenx
    have h1 := classSumScalar_congruent_zero_of_odd_degree_and_even_class
      ρ₁ x hdeg₁ hevenx
    have h2 := classSumScalar_congruent_zero_of_odd_degree_and_even_class
      ρ₂ x hdeg₂ hevenx
    have h3 := classSumScalar_congruent_zero_of_odd_degree_and_even_class
      ρ₃ x hdeg₃ hevenx
    have h123 : CongruentModTwo
        (Theory.Character.classSumScalar (ρ := ρ₁) s +
          Theory.Character.classSumScalar (ρ := ρ₂) s +
          Theory.Character.classSumScalar (ρ := ρ₃) s) 0 := by
      simpa [hxs] using (h1.add h2).add h3
    simpa [hxs] using h0.trans h123.symm

private lemma congruent_mul_of_integral
    {a b d e : ℂ} (hab : CongruentModTwo a b)
    (hde : CongruentModTwo d e) (ha : IsIntegral ℤ a)
    (he : IsIntegral ℤ e) : CongruentModTwo (a * d) (b * e) :=
  (CongruentModTwo.mul_right hde ha).trans
    (CongruentModTwo.mul_left hab he)

private lemma classSum_product_congruent_character_product_on_B
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    {χ : Irr G} (hχ : χ.1 = ρ.character)
    (hdeg : Odd (Module.finrank ℂ V)) (u v : ↥c.B) :
    CongruentModTwo
      (classSumScalar (ρ := ρ) (ConjClasses.mk (u : G)) *
        classSumScalar (ρ := ρ) (ConjClasses.mk (v : G)))
      (χ.1 (u : G) * χ.1 (v : G)) := by
  have hu : CongruentModTwo
      (classSumScalar (ρ := ρ) (ConjClasses.mk (u : G)))
      (χ.1 (u : G)) :=
    (classSumScalar_congruent_character_of_odd_degree_and_class
      ρ (u : G) hdeg (odd_index_of_mem_B c u.2)).trans
        (CongruentModTwo.of_eq (congrFun hχ.symm (u : G)))
  have hv : CongruentModTwo
      (classSumScalar (ρ := ρ) (ConjClasses.mk (v : G)))
      (χ.1 (v : G)) :=
    (classSumScalar_congruent_character_of_odd_degree_and_class
      ρ (v : G) hdeg (odd_index_of_mem_B c v.2)).trans
        (CongruentModTwo.of_eq (congrFun hχ.symm (v : G)))
  exact congruent_mul_of_integral hu hv
    (classSumScalar_isIntegral (ρ := ρ) (ConjClasses.mk (u : G)))
    (irr_value_isIntegral χ (v : G))

private lemma deltaNu_normSq_eq_zero_or_two_of_not_fixed
    (h12 : Hyp12 c) (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {ν : Irr (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ ν.1) :
    normSq G (deltaNu c h12 ν) = 0 ∨
      normSq G (deltaNu c h12 ν) = 2 := by
  classical
  have hlamS : conjChar c.H0 (s_normalizes_H0 c h12)
      (lambdaTwoMul c h12 ν).1 ≠ (lambdaTwoMul c h12 ν).1 := by
    intro hfix
    have hfix' := lambdaTwoMul_fixed_by_s c h12 hfix
    rw [lambdaTwoMul_sq c h12 ν] at hfix'
    exact hνs hfix'
  by_cases hconj : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 =
      (lambdaTwoMul c h12 ν).1
  · left
    have hEq : conjIrr c h12 ν = lambdaTwoMul c h12 ν :=
      Subtype.ext (by simpa using hconj)
    have htilde : tildeNu c h12 (lambdaTwoMul c h12 ν) =
        tildeNu c h12 ν := by
      rw [← hEq]
      exact tildeNu_invariance c h12 ν
    unfold deltaNu
    rw [htilde]
    simp [normSq, scalarProduct_zero_right]
  · right
    have hμν : (lambdaTwoMul c h12 ν).1 ∈ orbit c.H0 c.U ν.1 := by
      exact lambdaTwoMul_equiv c h12 ν
    have hνμ : ν.1 ≠ (lambdaTwoMul c h12 ν).1 := by
      intro hEq
      exact lambdaTwoMul_ne_self c h12 hSC hS4 ν (Subtype.ext hEq.symm)
    have hdis : Disjoint (tildeNu c h12 (lambdaTwoMul c h12 ν))
        (tildeNu c h12 ν) :=
      tildeNu_disjoint c h12 hμν hνμ hconj
    have h1 : normSq G (tildeNu c h12 ν) = 1 := by
      have h := tildeNu_norm c h12 ν
      simpa [hνs] using h
    have h2 : normSq G (tildeNu c h12 (lambdaTwoMul c h12 ν)) = 1 := by
      have h := tildeNu_norm c h12 (lambdaTwoMul c h12 ν)
      simpa [hlamS] using h
    unfold deltaNu normSq
    rw [scalarProduct_sub_left, scalarProduct_sub_right,
      scalarProduct_sub_right]
    have hnuLam : scalarProduct G (tildeNu c h12 ν)
        (tildeNu c h12 (lambdaTwoMul c h12 ν)) = 0 :=
      scalarProduct_eq_zero_of_disjoint
        (tildeNu_isGeneralized c h12 ν)
        (tildeNu_isGeneralized c h12 (lambdaTwoMul c h12 ν))
        (disjoint_symm hdis)
    have hlamNu : scalarProduct G (tildeNu c h12 (lambdaTwoMul c h12 ν))
        (tildeNu c h12 ν) = 0 :=
      scalarProduct_eq_zero_of_disjoint
        (tildeNu_isGeneralized c h12 (lambdaTwoMul c h12 ν))
        (tildeNu_isGeneralized c h12 ν) hdis
    have h1' : scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 ν) = 1 := by
      simpa [normSq] using h1
    have h2' : scalarProduct G (tildeNu c h12 (lambdaTwoMul c h12 ν))
        (tildeNu c h12 (lambdaTwoMul c h12 ν)) = 1 := by
      simpa [normSq] using h2
    rw [h1', h2', hnuLam, hlamNu]
    norm_num

private lemma fixed_of_deltaNu_eq_fixed
    (h12 : Hyp12 c) (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {ν μ : Irr (↥c.H0)}
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1)
    (hEq : deltaNu c h12 ν = deltaNu c h12 μ) :
    conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 := by
  by_contra hνs
  have hnormμ := deltaNu_normSq_eq_four c h12 hSC hS4 hμs
  have hnormEq := congrArg (normSq G) hEq
  rcases deltaNu_normSq_eq_zero_or_two_of_not_fixed c h12 hSC hS4 hνs with
    hzero | htwo
  · rw [hzero, hnormμ] at hnormEq
    norm_num at hnormEq
  · rw [htwo, hnormμ] at hnormEq
    norm_num at hnormEq

private lemma t_fixed_of_deltaNu_eq_fixed
    (h12 : Hyp12 c) (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {ν μ : Irr (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1)
    (hμt : μ.1 (tH0 c) = μ.1 1)
    (hEq : deltaNu c h12 ν = deltaNu c h12 μ) :
    ν.1 (tH0 c) = ν.1 1 := by
  rcases char_apply_central_sign (G := ↥c.H0) (t := tH0 c)
      (by simpa [tH0] using t_central_H0' c)
      (by simpa [tH0] using t_H0_sq c) ν.2 with hpos | hneg
  · exact hpos
  · exfalso
    let κ : Irr (↥c.H0) := lambdaTwoMul c h12 ν
    have hκs : conjChar c.H0 (s_normalizes_H0 c h12) κ.1 = κ.1 :=
      lambdaTwoMul_fixed_by_s c h12 hνs
    have hκt : κ.1 (tH0 c) = κ.1 1 := by
      have hdeg : κ.1 1 = ν.1 1 := by
        simp [κ, lambdaTwoMul, LambdaChar]
      calc
        κ.1 (tH0 c) = ((lambdaTwo c h12).1 (tH0 c) : ℂ) *
            ν.1 (tH0 c) := by simp [κ, lambdaTwoMul, LambdaChar]
        _ = (-1 : ℂ) * ν.1 (tH0 c) := by
              rw [lambdaTwo_val_tH0_eq_neg_one c h12 hSC hS4]
        _ = ν.1 1 := by rw [hneg]; ring
        _ = κ.1 1 := hdeg.symm
    have hδκ : deltaNu c h12 κ = -deltaNu c h12 ν := by
      dsimp [κ]
      unfold deltaNu
      rw [lambdaTwoMul_sq c h12 ν]
      ext x
      simp
    have hδκμ : deltaNu c h12 κ = -deltaNu c h12 μ :=
      hδκ.trans (congrArg Neg.neg hEq)
    by_cases hκμ : κ = μ
    · have hself : deltaNu c h12 μ = -deltaNu c h12 μ := by
        simpa [hκμ] using hδκμ
      have hzero : deltaNu c h12 μ = 0 := by
        ext x
        change deltaNu c h12 μ x = (0 : ℂ)
        have hx := congrFun hself x
        simpa only [Pi.neg_apply, CharZero.eq_neg_self_iff] using hx
      have hnorm := deltaNu_normSq_eq_four c h12 hSC hS4 hμs
      rw [hzero] at hnorm
      norm_num [normSq, scalarProduct_zero_right] at hnorm
    · have horth := deltaNu_orthogonal c h12 hSC hS4
        hκs hκt hμs hμt hκμ
      rw [hδκμ, scalarProduct_neg_left] at horth
      have hnorm := deltaNu_normSq_eq_four c h12 hSC hS4 hμs
      have hself : scalarProduct G (deltaNu c h12 μ) (deltaNu c h12 μ) = 4 := by
        simpa [normSq] using hnorm
      rw [hself] at horth
      norm_num at horth

public lemma section4_conditions_of_deltaNu_mem_component
    (h12 : Hyp12 c) (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {Δ0 : Set (ClassFunction G)} (hcomp : IsConnectedComponent c h12 Δ0)
    {ν : Irr (↥c.H0)} (hνΔ0 : deltaNu c h12 ν ∈ Δ0) :
    conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 ∧
      ν.1 (tH0 c) = ν.1 1 := by
  rcases hcomp.2.1 hνΔ0 with ⟨μ, hμs, hμt, hEq⟩
  have hνs := fixed_of_deltaNu_eq_fixed c h12 hSC hS4 hμs hEq
  exact ⟨hνs, t_fixed_of_deltaNu_eq_fixed c h12 hSC hS4
    hνs hμs hμt hEq⟩

private lemma fixed_tetrahedron_contradiction
    (h12 : Hyp12 c) (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    [Fintype ↥(LambdaHom c.H0 c.U)]
    {Δ0 : Set (ClassFunction G)} (hcomp : IsConnectedComponent c h12 Δ0)
    {ν₁ ν₂ ν₃ ν₄ : Irr (↥c.H0)}
    (hν₁Δ0 : deltaNu c h12 ν₁ ∈ Δ0)
    (hν₂Δ0 : deltaNu c h12 ν₂ ∈ Δ0)
    (hν₃Δ0 : deltaNu c h12 ν₃ ∈ Δ0)
    (hν₄Δ0 : deltaNu c h12 ν₄ ∈ Δ0)
    (hν₁s : conjChar c.H0 (s_normalizes_H0 c h12) ν₁.1 = ν₁.1)
    (hν₁t : ν₁.1 (tH0 c) = ν₁.1 1)
    (hν₂s : conjChar c.H0 (s_normalizes_H0 c h12) ν₂.1 = ν₂.1)
    (hν₂t : ν₂.1 (tH0 c) = ν₂.1 1)
    (hν₃s : conjChar c.H0 (s_normalizes_H0 c h12) ν₃.1 = ν₃.1)
    (hν₃t : ν₃.1 (tH0 c) = ν₃.1 1)
    (hν₄s : conjChar c.H0 (s_normalizes_H0 c h12) ν₄.1 = ν₄.1)
    (hν₄t : ν₄.1 (tH0 c) = ν₄.1 1)
    (hν₁₂ : ν₁ ≠ ν₂) (hν₁₃ : ν₁ ≠ ν₃) (hν₁₄ : ν₁ ≠ ν₄)
    (hν₂₃ : ν₂ ≠ ν₃) (hν₂₄ : ν₂ ≠ ν₄) (hν₃₄ : ν₃ ≠ ν₄)
    {a b c₀ d e f g h : Irr G}
    (hAset : involved (deltaNu c h12 ν₁) = {a, b, c₀, d})
    (hBset : involved (deltaNu c h12 ν₂) = {a, b, e, f})
    (hCset : involved (deltaNu c h12 ν₃) = {a, c₀, e, g})
    (hDset : involved (deltaNu c h12 ν₄) = {b, c₀, e, h})
    (hab : a ≠ b) (hac : a ≠ c₀) (had : a ≠ d)
    (hbc : b ≠ c₀) (hbd : b ≠ d) (hcd : c₀ ≠ d)
    (hae : a ≠ e) (haf : a ≠ f) (hag : a ≠ g)
    (hbe : b ≠ e) (hbf : b ≠ f) (hbg : b ≠ g)
    (hce : c₀ ≠ e) (hcf : c₀ ≠ f) (hcg : c₀ ≠ g)
    (hde : d ≠ e) (hdf : d ≠ f) (hdg : d ≠ g)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hha : h ≠ a) (hhb : h ≠ b) (hhc : h ≠ c₀)
    (hhd : h ≠ d) (hhe : h ≠ e) (hhf : h ≠ f) (hhg : h ≠ g)
    (hΔeq : Δ0 = ({deltaNu c h12 ν₁, deltaNu c h12 ν₂,
      deltaNu c h12 ν₃, deltaNu c h12 ν₄} : Set (ClassFunction G))) : False := by
  classical
  have ha₁ : a ∈ involved (deltaNu c h12 ν₁) := by rw [hAset]; simp
  have ha₂ : a ∈ involved (deltaNu c h12 ν₂) := by rw [hBset]; simp
  have ha₃ : a ∈ involved (deltaNu c h12 ν₃) := by rw [hCset]; simp
  have ha₄ : a ∉ involved (deltaNu c h12 ν₄) := by
    rw [hDset]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hab, hac, hae, hha.symm⟩
  have hd₁ : d ∈ involved (deltaNu c h12 ν₁) := by rw [hAset]; simp
  have hd₂ : d ∉ involved (deltaNu c h12 ν₂) := by
    rw [hBset]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨had.symm, hbd.symm, hde, hdf⟩
  have hd₃ : d ∉ involved (deltaNu c h12 ν₃) := by
    rw [hCset]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨had.symm, hcd.symm, hde, hdg⟩
  have hd₄ : d ∉ involved (deltaNu c h12 ν₄) := by
    rw [hDset]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hbd.symm, hcd.symm, hde, hhd.symm⟩
  have hf₂ : f ∈ involved (deltaNu c h12 ν₂) := by rw [hBset]; simp
  have hf₁ : f ∉ involved (deltaNu c h12 ν₁) := by
    rw [hAset]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨haf.symm, hbf.symm, hcf.symm, hdf.symm⟩
  have hf₃ : f ∉ involved (deltaNu c h12 ν₃) := by
    rw [hCset]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨haf.symm, hcf.symm, hef.symm, hfg⟩
  have hf₄ : f ∉ involved (deltaNu c h12 ν₄) := by
    rw [hDset]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hbf.symm, hcf.symm, hef.symm, hhf.symm⟩
  have hg₃ : g ∈ involved (deltaNu c h12 ν₃) := by rw [hCset]; simp
  have hg₁ : g ∉ involved (deltaNu c h12 ν₁) := by
    rw [hAset]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hag.symm, hbg.symm, hcg.symm, hdg.symm⟩
  have hg₂ : g ∉ involved (deltaNu c h12 ν₂) := by
    rw [hBset]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hag.symm, hbg.symm, heg.symm, hfg.symm⟩
  have hg₄ : g ∉ involved (deltaNu c h12 ν₄) := by
    rw [hDset]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hbg.symm, hcg.symm, heg.symm, hhg.symm⟩
  have hBd : BPrimeOf c h12 d.1 = {ν₁} :=
    BPrime_eq_singleton_of_tetrahedron c h12 hSC hS4 hcomp
      hν₁s hν₁t hν₂s hν₂t hν₃s hν₃t hν₄s hν₄t
      hΔeq hν₁Δ0 hd₁ hd₂ hd₃ hd₄
  have hΔeq₂ : Δ0 = ({deltaNu c h12 ν₂, deltaNu c h12 ν₁,
      deltaNu c h12 ν₃, deltaNu c h12 ν₄} : Set (ClassFunction G)) := by
    exact hΔeq.trans (Set.insert_comm _ _ _)
  have hBf : BPrimeOf c h12 f.1 = {ν₂} :=
    BPrime_eq_singleton_of_tetrahedron c h12 hSC hS4 hcomp
      hν₂s hν₂t hν₁s hν₁t hν₃s hν₃t hν₄s hν₄t
      hΔeq₂ hν₂Δ0 hf₂ hf₁ hf₃ hf₄
  have hΔeq₃ : Δ0 = ({deltaNu c h12 ν₃, deltaNu c h12 ν₁,
      deltaNu c h12 ν₂, deltaNu c h12 ν₄} : Set (ClassFunction G)) := by
    calc
      Δ0 = ({deltaNu c h12 ν₁, deltaNu c h12 ν₃,
          deltaNu c h12 ν₂, deltaNu c h12 ν₄} : Set (ClassFunction G)) :=
        hΔeq.trans (congrArg (Set.insert (deltaNu c h12 ν₁))
          (Set.insert_comm _ _ _))
      _ = {deltaNu c h12 ν₃, deltaNu c h12 ν₁,
          deltaNu c h12 ν₂, deltaNu c h12 ν₄} :=
        Set.insert_comm _ _ _
  have hBg : BPrimeOf c h12 g.1 = {ν₃} :=
    BPrime_eq_singleton_of_tetrahedron c h12 hSC hS4 hcomp
      hν₃s hν₃t hν₁s hν₁t hν₂s hν₂t hν₄s hν₄t
      hΔeq₃ hν₃Δ0 hg₃ hg₁ hg₂ hg₄
  have hBa : BPrimeOf c h12 a.1 = tripleFinset ν₁ ν₂ ν₃ :=
    BPrime_eq_triple_of_tetrahedron c h12 hSC hS4 hcomp
      hν₁s hν₁t hν₂s hν₂t hν₃s hν₃t hν₄s hν₄t
      hΔeq hν₁Δ0 ha₁ ha₂ ha₃ ha₄
  have hBdne : (BPrimeOf c h12 d.1).Nonempty := by rw [hBd]; simp
  have hBfne : (BPrimeOf c h12 f.1).Nonempty := by rw [hBf]; simp
  have hBgne : (BPrimeOf c h12 g.1).Nonempty := by rw [hBg]; simp
  have hBane : (BPrimeOf c h12 a.1).Nonempty := by
    rw [hBa]
    simp [tripleFinset]
  have h41d := lemma_4_1 c h12 hSC hS4 (χ := d.1) (Or.inl d.2) hBdne
  have h41f := lemma_4_1 c h12 hSC hS4 (χ := f.1) (Or.inl f.2) hBfne
  have h41g := lemma_4_1 c h12 hSC hS4 (χ := g.1) (Or.inl g.2) hBgne
  have h41a := lemma_4_1 c h12 hSC hS4 (χ := a.1) (Or.inl a.2) hBane
  have hbH0 : ∀ u : ↥c.B, (u : G) ∈ c.H0 := fun u =>
    U_le_H0 c (mem_U_of_mem_B_s4 c u.2)
  have hdB : ∀ u : ↥c.B,
      CongruentModTwo (d.1 (u : G)) ((nuHat c h12 ν₁).1 u) := by
    intro u
    have hu := h41d.2.2.1 u (hbH0 u)
    rw [hBd] at hu
    simpa using hu
  have hfB : ∀ u : ↥c.B,
      CongruentModTwo (f.1 (u : G)) ((nuHat c h12 ν₂).1 u) := by
    intro u
    have hu := h41f.2.2.1 u (hbH0 u)
    rw [hBf] at hu
    simpa using hu
  have hgB : ∀ u : ↥c.B,
      CongruentModTwo (g.1 (u : G)) ((nuHat c h12 ν₃).1 u) := by
    intro u
    have hu := h41g.2.2.1 u (hbH0 u)
    rw [hBg] at hu
    simpa using hu
  have haB : ∀ u : ↥c.B, CongruentModTwo (a.1 (u : G))
      ((nuHat c h12 ν₁).1 u + (nuHat c h12 ν₂).1 u +
        (nuHat c h12 ν₃).1 u) := by
    intro u
    have hu := h41a.2.2.1 u (hbH0 u)
    rw [hBa] at hu
    simpa [tripleFinset, hν₁₂, hν₁₃, hν₂₃, add_assoc] using hu
  rcases a.2 with ⟨na, ρa, hρa, hχa⟩
  rcases d.2 with ⟨nd, ρd, hρd, hχd⟩
  rcases f.2 with ⟨nf, ρf, hρf, hχf⟩
  rcases g.2 with ⟨ng, ρg, hρg, hχg⟩
  let : Representation.IsIrreducible ρa := hρa
  let : Representation.IsIrreducible ρd := hρd
  let : Representation.IsIrreducible ρf := hρf
  let : Representation.IsIrreducible ρg := hρg
  have hgena : IsGeneralizedCharacter a.1 :=
    ⟨a.1, 0, isCharacter_of_isIrreducibleCharacter a.2,
      isCharacter_zero, by simp⟩
  have hgend : IsGeneralizedCharacter d.1 :=
    ⟨d.1, 0, isCharacter_of_isIrreducibleCharacter d.2,
      isCharacter_zero, by simp⟩
  have hgenf : IsGeneralizedCharacter f.1 :=
    ⟨f.1, 0, isCharacter_of_isIrreducibleCharacter f.2,
      isCharacter_zero, by simp⟩
  have hgeng : IsGeneralizedCharacter g.1 :=
    ⟨g.1, 0, isCharacter_of_isIrreducibleCharacter g.2,
      isCharacter_zero, by simp⟩
  have hdega := representation_degree_odd ρa hχa h41a.2.2.2.1
  have hdegd := representation_degree_odd ρd hχd h41d.2.2.2.1
  have hdegf := representation_degree_odd ρf hχf h41f.2.2.2.1
  have hdegg := representation_degree_odd ρg hχg h41g.2.2.2.1
  have hscalar := classSum_scalar_congr c hS4 ρa ρd ρf ρg
    hχa hχd hχf hχg hgena hgend hgenf hgeng
    hdega hdegd hdegf hdegg (by
      intro u
      exact (haB u).trans (((hdB u).add (hfB u)).add (hgB u)).symm)
  have hproducts := classSum_products_congr ρa ρd ρf ρg hscalar
  have hcharProducts : ∀ u v : ↥c.B, CongruentModTwo
      (d.1 (u : G) * d.1 (v : G) + f.1 (u : G) * f.1 (v : G) +
        g.1 (u : G) * g.1 (v : G))
      (a.1 (u : G) * a.1 (v : G)) := by
    intro u v
    have hpd := classSum_product_congruent_character_product_on_B c ρd hχd hdegd u v
    have hpf := classSum_product_congruent_character_product_on_B c ρf hχf hdegf u v
    have hpg := classSum_product_congruent_character_product_on_B c ρg hχg hdegg u v
    have hpa := classSum_product_congruent_character_product_on_B c ρa hχa hdega u v
    have hp := hproducts (ConjClasses.mk (u : G)) (ConjClasses.mk (v : G))
    exact ((hpd.add hpf).add hpg).symm.trans (hp.trans hpa)
  have hbetaProducts : ∀ u v : ↥c.B, CongruentModTwo
      ((nuHat c h12 ν₁).1 u * (nuHat c h12 ν₁).1 v +
        (nuHat c h12 ν₂).1 u * (nuHat c h12 ν₂).1 v +
        (nuHat c h12 ν₃).1 u * (nuHat c h12 ν₃).1 v)
      (((nuHat c h12 ν₁).1 u + (nuHat c h12 ν₂).1 u +
          (nuHat c h12 ν₃).1 u) *
        ((nuHat c h12 ν₁).1 v + (nuHat c h12 ν₂).1 v +
          (nuHat c h12 ν₃).1 v)) := by
    intro u v
    have hpd := congruent_mul_of_integral (hdB u) (hdB v)
      (irr_value_isIntegral d (u : G))
      (irr_value_isIntegral (nuHat c h12 ν₁) v)
    have hpf := congruent_mul_of_integral (hfB u) (hfB v)
      (irr_value_isIntegral f (u : G))
      (irr_value_isIntegral (nuHat c h12 ν₂) v)
    have hpg := congruent_mul_of_integral (hgB u) (hgB v)
      (irr_value_isIntegral g (u : G))
      (irr_value_isIntegral (nuHat c h12 ν₃) v)
    have hsumv : IsIntegral ℤ
        ((nuHat c h12 ν₁).1 v + (nuHat c h12 ν₂).1 v +
          (nuHat c h12 ν₃).1 v) :=
      ((irr_value_isIntegral (nuHat c h12 ν₁) v).add
        (irr_value_isIntegral (nuHat c h12 ν₂) v)).add
          (irr_value_isIntegral (nuHat c h12 ν₃) v)
    have hpa := congruent_mul_of_integral (haB u) (haB v)
      (irr_value_isIntegral a (u : G)) hsumv
    exact ((hpd.add hpf).add hpg).symm.trans
      ((hcharProducts u v).trans hpa)
  let I : Type u := ULift.{u} (Fin 3)
  let βIrr : I → Irr (↥c.B) := fun i =>
    ![nuHat c h12 ν₁, nuHat c h12 ν₂, nuHat c h12 ν₃] i.down
  let β : I → ClassFunction (↥c.B) := fun i => (βIrr i).1
  have hβirr : ∀ i, IsIrreducibleCharacter (β i) := fun i => (βIrr i).2
  have hhat₁₂ : (nuHat c h12 ν₁).1 ≠ (nuHat c h12 ν₂).1 := by
    intro hEq
    exact hν₁₂ (nuHat_injective_on_Delta c h12 hSC hS4
      hν₁s hν₁t hν₂s hν₂t (Subtype.ext hEq))
  have hhat₁₃ : (nuHat c h12 ν₁).1 ≠ (nuHat c h12 ν₃).1 := by
    intro hEq
    exact hν₁₃ (nuHat_injective_on_Delta c h12 hSC hS4
      hν₁s hν₁t hν₃s hν₃t (Subtype.ext hEq))
  have hhat₂₃ : (nuHat c h12 ν₂).1 ≠ (nuHat c h12 ν₃).1 := by
    intro hEq
    exact hν₂₃ (nuHat_injective_on_Delta c h12 hSC hS4
      hν₂s hν₂t hν₃s hν₃t (Subtype.ext hEq))
  have hβdist : Pairwise fun i j => β i ≠ β j := by
    intro i j hij
    rcases i with ⟨i⟩
    rcases j with ⟨j⟩
    fin_cases i <;> fin_cases j <;>
      simp [β, βIrr, hhat₁₂, hhat₁₃, hhat₂₃,
        hhat₁₂.symm, hhat₁₃.symm, hhat₂₃.symm] at hij ⊢
  have hIuniv : (Finset.univ : Finset I) =
      ({ULift.up (0 : Fin 3), ULift.up (1 : Fin 3),
        ULift.up (2 : Fin 3)} : Finset I) := by
    ext i
    rcases i with ⟨i⟩
    fin_cases i <;> simp
  have hsumI (f : I → ℂ) : (∑ i : I, f i) =
      f (ULift.up (0 : Fin 3)) + f (ULift.up (1 : Fin 3)) +
        f (ULift.up (2 : Fin 3)) := by
    rw [hIuniv, Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  have hsumβ (u : ↥c.B) : (∑ i : I, β i u) =
      (nuHat c h12 ν₁).1 u + (nuHat c h12 ν₂).1 u +
        (nuHat c h12 ν₃).1 u := by
    rw [hsumI]
    simp [β, βIrr]
  let coeff (u : ↥c.B) (i : I) : ℂ := β i u - ∑ j, β j u
  have hfirst : ∀ u : ↥c.B,
      CongruentModTwo (β (ULift.up (0 : Fin 3)) u) (∑ j, β j u) := by
    intro u
    have hsumInt : IsIntegral ℤ (∑ j : I, β j u) := by
      rw [hsumβ]
      exact ((irr_value_isIntegral (nuHat c h12 ν₁) u).add
        (irr_value_isIntegral (nuHat c h12 ν₂) u)).add
          (irr_value_isIntegral (nuHat c h12 ν₃) u)
    have hc : ∀ i, IsIntegral ℤ (coeff u i) := by
      intro i
      have hi := (irr_value_isIntegral (βIrr i) u).sub hsumInt
      simpa [coeff, β] using hi
    have hzero : ∀ v : ↥c.B,
        CongruentModTwo (∑ i, coeff u i * β i v) 0 := by
      intro v
      have hp := hbetaProducts u v
      have hz := CongruentModTwo.sub hp
        (CongruentModTwo.refl
          (((nuHat c h12 ν₁).1 u + (nuHat c h12 ν₂).1 u +
              (nuHat c h12 ν₃).1 u) *
            ((nuHat c h12 ν₁).1 v + (nuHat c h12 ν₂).1 v +
              (nuHat c h12 ν₃).1 v)))
      have hz0 : CongruentModTwo
          ((nuHat c h12 ν₁).1 u * (nuHat c h12 ν₁).1 v +
              (nuHat c h12 ν₂).1 u * (nuHat c h12 ν₂).1 v +
              (nuHat c h12 ν₃).1 u * (nuHat c h12 ν₃).1 v -
            ((nuHat c h12 ν₁).1 u + (nuHat c h12 ν₂).1 u +
                (nuHat c h12 ν₃).1 u) *
              ((nuHat c h12 ν₁).1 v + (nuHat c h12 ν₂).1 v +
                (nuHat c h12 ν₃).1 v)) 0 := by
        simpa only [sub_self] using hz
      have heq : (∑ i : I, coeff u i * β i v) =
          ((nuHat c h12 ν₁).1 u * (nuHat c h12 ν₁).1 v +
              (nuHat c h12 ν₂).1 u * (nuHat c h12 ν₂).1 v +
              (nuHat c h12 ν₃).1 u * (nuHat c h12 ν₃).1 v) -
            ((nuHat c h12 ν₁).1 u + (nuHat c h12 ν₂).1 u +
                (nuHat c h12 ν₃).1 u) *
              ((nuHat c h12 ν₁).1 v + (nuHat c h12 ν₂).1 v +
                (nuHat c h12 ν₃).1 v) := by
        rw [hsumI]
        simp [coeff, β, βIrr, hsumβ]
        ring
      exact (CongruentModTwo.of_eq heq).trans hz0
    have h18 := lemma_1_8 (B := ↥c.B) (B_coprime_two c)
      (I := I) (β := β) (c := coeff u)
      hβirr hβdist hc hzero
    have hadd := (h18 (ULift.up (0 : Fin 3))).add
      (CongruentModTwo.refl (∑ j : I, β j u))
    convert hadd using 1 <;> simp [coeff]
  have h23 : ∀ u : ↥c.B,
      CongruentModTwo
        (β (ULift.up (1 : Fin 3)) u + β (ULift.up (2 : Fin 3)) u) 0 := by
    intro u
    have hs := CongruentModTwo.sub (hfirst u)
      (CongruentModTwo.refl (β (ULift.up (0 : Fin 3)) u))
    convert hs.symm using 1 <;> simp [hsumβ, β, βIrr] <;> ring
  let coeff₂ : I → ℂ := fun i => ![(0 : ℂ), 1, 1] i.down
  have hc₂ : ∀ i, IsIntegral ℤ (coeff₂ i) := by
    intro i
    rcases i with ⟨i⟩
    fin_cases i <;> simp [coeff₂, isIntegral_zero, isIntegral_one]
  have hzero₂ : ∀ u : ↥c.B,
      CongruentModTwo (∑ i, coeff₂ i * β i u) 0 := by
    intro u
    have heq : (∑ i : I, coeff₂ i * β i u) =
        β (ULift.up (1 : Fin 3)) u + β (ULift.up (2 : Fin 3)) u := by
      rw [hsumI]
      simp [coeff₂, β, βIrr]
    exact (CongruentModTwo.of_eq heq).trans (h23 u)
  have h18₂ := lemma_1_8 (B := ↥c.B) (B_coprime_two c)
    (I := I) (β := β) (c := coeff₂)
    hβirr hβdist hc₂ hzero₂
  have hone : CongruentModTwo (1 : ℂ) 0 := by
    simpa [coeff₂] using h18₂ (ULift.up (1 : Fin 3))
  exact (CongruentModTwo.not_zero_of_odd_nat (n := 1) (by norm_num))
    (by simpa using hone.symm)

/-- Theorem 4.3: every nonsingleton component of `Δ` consists of three
signed four-constituent vertices, and all of its `ν̂` representatives are
conjugate under `N_G(S)`. -/
public theorem theorem_4_3 (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) [Fintype ↥(LambdaHom c.H0 c.U)]
    (Δ0 : Set (ClassFunction G)) (hΔ0 : IsConnectedComponent c h12 Δ0)
    (hcard : Δ0.ncard ≠ 1) :
    ∃ ν1 ν2 ν3 : Irr (↥c.H0),
      deltaNu c h12 ν1 ∈ Δ0 ∧ deltaNu c h12 ν2 ∈ Δ0 ∧ deltaNu c h12 ν3 ∈ Δ0 ∧
      deltaNu c h12 ν1 ≠ deltaNu c h12 ν2 ∧ deltaNu c h12 ν2 ≠ deltaNu c h12 ν3 ∧
      deltaNu c h12 ν1 ≠ deltaNu c h12 ν3 ∧
      ∃ χ1 χ2 χ3 χ4 : ClassFunction G,
        IsPMIrr G χ1 ∧ IsPMIrr G χ2 ∧ IsPMIrr G χ3 ∧ IsPMIrr G χ4 ∧
        scalarProduct G χ1 χ2 = 0 ∧ scalarProduct G χ1 χ3 = 0 ∧
        scalarProduct G χ1 χ4 = 0 ∧ scalarProduct G χ2 χ3 = 0 ∧
        scalarProduct G χ2 χ4 = 0 ∧ scalarProduct G χ3 χ4 = 0 ∧
        deltaNu c h12 ν1 = χ1 + χ2 + χ3 + χ4 ∧
        deltaNu c h12 ν2 = χ1 - χ2 + χ3 - χ4 ∧
        deltaNu c h12 ν3 = χ1 + χ2 - χ3 - χ4 ∧
        Δ0 = {deltaNu c h12 ν1, deltaNu c h12 ν2, deltaNu c h12 ν3} ∧
        ∀ ν ν' : Irr (↥c.H0), deltaNu c h12 ν ∈ Δ0 → deltaNu c h12 ν' ∈ Δ0 →
          ∃ g : G, ∃ hg : g ∈ normalizerS c,
            conjIrrB c (B_conj_mem_of_normalizerS c hg) (nuHat c h12 ν) =
              nuHat c h12 ν' := by
  classical
  rcases hΔ0.1 with ⟨δμ, hδμ⟩
  rcases hΔ0.2.1 hδμ with ⟨μ, hμs, hμt, hδμeq⟩
  have hμΔ0 : deltaNu c h12 μ ∈ Δ0 := by
    rw [← hδμeq]
    exact hδμ
  rcases nuHatOrbit_card_eq_one_or_three c h12 hS4 μ with hfix | horb
  · rcases exists_two_distinct_of_ncard_ne_one c h12 hΔ0 hcard with
      ⟨δ₀, δ₁, hδ₀, hδ₁, hδ₀₁⟩
    rcases exists_adjacent_pair_of_two c h12 hΔ0 hδ₀ hδ₁ hδ₀₁ with
      ⟨δa, δb, hδa, hδb, hadj⟩
    have hfixed := exists_fixed_witness_of_Delta0_of_fixed c h12 hSC hS4
      hΔ0 hμs hμt hμΔ0 hfix
    rcases hfixed δa hδa with
      ⟨ν₁, hδaΔ0, hδaeq, hν₁s, hν₁t, hfix₁⟩
    rcases hfixed δb hδb with
      ⟨ν₂, hδbΔ0, hδbeq, hν₂s, hν₂t, hfix₂⟩
    have hν₁Δ0 : deltaNu c h12 ν₁ ∈ Δ0 := by
      rw [← hδaeq]
      exact hδaΔ0
    have hν₂Δ0 : deltaNu c h12 ν₂ ∈ Δ0 := by
      rw [← hδbeq]
      exact hδbΔ0
    have hν₁₂ : ν₁ ≠ ν₂ := by
      intro hEq
      apply hadj.2.2.1
      rw [hδaeq, hδbeq, hEq]
    rcases exists_shared_constituent_of_adjacent c h12 hadj with
      ⟨χ, hχa, hχb⟩
    have hχ₁ : χ ∈ involved (deltaNu c h12 ν₁) := by
      simpa [hδaeq] using hχa
    have hχ₂ : χ ∈ involved (deltaNu c h12 ν₂) := by
      simpa [hδbeq] using hχb
    rcases fixed_incidence_four_configuration c h12 hSC hS4 hΔ0
      hν₁Δ0 hν₂Δ0 hν₁s hν₁t hν₂s hν₂t hfix₁ hfix₂ hχ₁ hχ₂ hν₁₂ with
      ⟨ν₃, ν₄, a, b, c₀, d, e, f, g, h,
        hν₃s, hν₃t, hfix₃, hν₃Δ0,
        hν₄s, hν₄t, hfix₄, hν₄Δ0,
        hν₁₃, hν₂₃, hν₁₄, hν₂₄, hν₃₄,
        hAset, hBset, hCset, hDset,
        hab, hac, had, hbc, hbd, hcd,
        hae, haf, hag, hbe, hbf, hbg,
        hce, hcf, hcg, hde, hdf, hdg,
        hef, heg, hfg, hha, hhb, hhc, hhd, hhe, hhf, hhg⟩
    have hΔeq := fixed_tetrahedron_component_eq c h12 hSC hS4 hΔ0
      hν₁Δ0 hν₂Δ0 hν₃Δ0 hν₄Δ0
      hν₁s hν₁t hν₂s hν₂t hν₃s hν₃t hν₄s hν₄t
      hfix₁ hfix₂ hfix₃ hfix₄
      hν₁₂ hν₁₃ hν₁₄ hν₂₃ hν₂₄ hν₃₄
      hAset hBset hCset hDset
    exact False.elim (fixed_tetrahedron_contradiction c h12 hSC hS4 hΔ0
      hν₁Δ0 hν₂Δ0 hν₃Δ0 hν₄Δ0
      hν₁s hν₁t hν₂s hν₂t hν₃s hν₃t hν₄s hν₄t
      hν₁₂ hν₁₃ hν₁₄ hν₂₃ hν₂₄ hν₃₄
      hAset hBset hCset hDset
      hab hac had hbc hbd hcd hae haf hag hbe hbf hbg
      hce hcf hcg hde hdf hdg hef heg hfg
      hha hhb hhc hhd hhe hhf hhg hΔeq)
  · rcases exists_signed_four_of_nonfixed c h12 hSC hS4 hΔ0
      hμs hμt hμΔ0 horb with
      ⟨ν₁, ν₂, ν₃, hδ₁, hδ₂, hδ₃, hδ₁₂, hδ₂₃, hδ₁₃,
        horb₁, horb₂, horb₃, hΔeq,
        χ₁, χ₂, χ₃, χ₄, hpm₁, hpm₂, hpm₃, hpm₄,
        horth₁₂, horth₁₃, horth₁₄, horth₂₃, horth₂₄, horth₃₄,
        hpat₁, hpat₂, hpat₃⟩
    refine ⟨ν₁, ν₂, ν₃, hδ₁, hδ₂, hδ₃, hδ₁₂, hδ₂₃, hδ₁₃,
      χ₁, χ₂, χ₃, χ₄, hpm₁, hpm₂, hpm₃, hpm₄,
      horth₁₂, horth₁₃, horth₁₄, horth₂₃, horth₂₄, horth₃₄,
      hpat₁, hpat₂, hpat₃, hΔeq, ?_⟩
    intro ν ν' hν hν'
    have hνfixed := section4_conditions_of_deltaNu_mem_component c h12 hSC hS4
      hΔ0 hν
    have hν'fixed := section4_conditions_of_deltaNu_mem_component c h12 hSC hS4
      hΔ0 hν'
    rcases deltaNu_mem_orbit_of_Delta0 c h12 hSC hS4 hΔ0
      hμs hμt hμΔ0 horb (deltaNu c h12 ν) hν with
      ⟨νc, _, hEqc, hνcs, hνct, hνcorb⟩
    rcases deltaNu_mem_orbit_of_Delta0 c h12 hSC hS4 hΔ0
      hμs hμt hμΔ0 horb (deltaNu c h12 ν') hν' with
      ⟨νc', _, hEqc', hνc's, hνc't, hνc'orb⟩
    have hνEq : ν = νc := deltaNu_injective c h12 hSC hS4
      hνfixed.1 hνfixed.2 hνcs hνct hEqc
    have hν'Eq : ν' = νc' := deltaNu_injective c h12 hSC hS4
      hν'fixed.1 hν'fixed.2 hνc's hνc't hEqc'
    have hνorb : nuHat c h12 ν ∈ nuHatOrbit c h12 (nuHat c h12 μ) := by
      simpa [hνEq] using hνcorb
    have hν'orb : nuHat c h12 ν' ∈ nuHatOrbit c h12 (nuHat c h12 μ) := by
      simpa [hν'Eq] using hνc'orb
    have hνorbitEq := nuHatOrbit_eq_of_mem c h12 hνorb
    have hν'orbν : nuHat c h12 ν' ∈ nuHatOrbit c h12 (nuHat c h12 ν) := by
      rw [hνorbitEq]
      exact hν'orb
    rw [nuHatOrbit] at hν'orbν
    rcases (Finset.mem_filter.mp hν'orbν).2 with ⟨g₀, hg₀, hconj⟩
    exact ⟨g₀, hg₀, hconj⟩

end Section4

end CFSG.BenderGlauberman

end
