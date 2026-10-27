module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_3

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 3, Proposition (3.4)

This file starts the Lean translation of PF (3.4).  The first closed node is
the support statement: the functions
`1_W - omega i j0 - omega i0 j + omega i j` vanish off
`V = W \ (W1 ∪ W2)`.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section3

universe v
universe u

/-! ## (3.4) -/

/--
Peterfalvi (3.4): the functions
`αᵢⱼ = 1_W - ωᵢ₀ - ω₀ⱼ + ωᵢⱼ`, for non-base indices `i,j`, form a basis
of the complex vector space of class functions of `W` supported on
`V = W \\ (W₁ ∪ W₂)`.
-/
@[expose] public def proposition_3_4_statement
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (I J : Type*) [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (_h : hypothesis_3_1_statement W1 W2 W)
    (_hω : notation_3_3_statement W1 W2 W I J i0 j0 ω) : Prop :=
  IsBasisForCFOn W (cyclicTISet W1 W2 W)
    (fun p : {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0} =>
      alphaIJ W i0 j0 ω p.1.1 p.1.2)


private theorem alphaIJ_apply
    {G : Type u} [Group G] (W : Subgroup G)
    {I J : Type*} (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W) (i : I) (j : J) (x : W) :
    alphaIJ W i0 j0 ω i j x =
      1 - ω i j0 x - ω i0 j x + ω i j x := by
  simp [alphaIJ, Section1.principalCharacter]

private theorem omega_left_kernel_value
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (i : I) {x : W} (hx : (x : G) ∈ W2) :
    ω i j0 x = 1 := by
  have hker := hω.left_kernel i ⟨x, hx⟩
  simpa [hω.degree_one i j0] using hker

private theorem omega_right_kernel_value
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (j : J) {x : W} (hx : (x : G) ∈ W1) :
    ω i0 j x = 1 := by
  have hker := hω.right_kernel j ⟨x, hx⟩
  simpa [hω.degree_one i0 j] using hker

private theorem alphaIJ_eq_zero_of_mem_left
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (i : I) (j : J) {x : W} (hx : (x : G) ∈ W1) :
    alphaIJ W i0 j0 ω i j x = 0 := by
  have hright : ω i0 j x = 1 := omega_right_kernel_value hω j hx
  calc
    alphaIJ W i0 j0 ω i j x =
        1 - ω i j0 x - ω i0 j x + ω i j x := alphaIJ_apply W i0 j0 ω i j x
    _ = 1 - ω i j0 x - 1 + ω i j x := by rw [hright]
    _ = 1 - ω i j0 x - 1 + (ω i j0 x * 1) := by rw [hω.product i j x, hright]
    _ = 0 := by ring

private theorem alphaIJ_eq_zero_of_mem_right
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (i : I) (j : J) {x : W} (hx : (x : G) ∈ W2) :
    alphaIJ W i0 j0 ω i j x = 0 := by
  have hleft : ω i j0 x = 1 := omega_left_kernel_value hω i hx
  calc
    alphaIJ W i0 j0 ω i j x =
        1 - ω i j0 x - ω i0 j x + ω i j x := alphaIJ_apply W i0 j0 ω i j x
    _ = 1 - 1 - ω i0 j x + ω i j x := by rw [hleft]
    _ = 1 - 1 - ω i0 j x + (1 * ω i0 j x) := by rw [hω.product i j x, hleft]
    _ = 0 := by ring

private theorem scalarProduct_sub_left'
    {H : Type*} [Finite H]
    (φ ψ η : Section1.ClassFunction H) :
    Section1.scalarProduct H (φ - ψ) η =
      Section1.scalarProduct H φ η - Section1.scalarProduct H ψ η := by
  calc
    Section1.scalarProduct H (φ - ψ) η =
        Section1.scalarProduct H (φ + (-1 : ℂ) • ψ) η := by
          congr
          ext x
          simp [sub_eq_add_neg]
    _ = Section1.scalarProduct H φ η +
          Section1.scalarProduct H ((-1 : ℂ) • ψ) η := by
          rw [Section1.scalarProduct_add_left]
    _ = Section1.scalarProduct H φ η - Section1.scalarProduct H ψ η := by
          rw [Section1.scalarProduct_smul_left]
          ring

private theorem alphaIJ_scalarProduct_omega
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (i : I) (j : J) {p : I} {q : J} (hp : p ≠ i0) (hq : q ≠ j0) :
    Section1.scalarProduct W (alphaIJ W i0 j0 ω i j) (ω p q) =
      if i = p ∧ j = q then 1 else 0 := by
  have h00_ne : (i0, j0) ≠ (p, q) := by
    intro hpair
    exact hp (congrArg Prod.fst hpair).symm
  have hi0_ne : (i, j0) ≠ (p, q) := by
    intro hpair
    exact hq (congrArg Prod.snd hpair).symm
  have h0j_ne : (i0, j) ≠ (p, q) := by
    intro hpair
    exact hp (congrArg Prod.fst hpair).symm
  have hprincipal :
      Section1.scalarProduct W (Section1.principalCharacter W) (ω p q) = 0 := by
    simpa [hω.principal, h00_ne] using
      Section3.isOrthonormalDoubleFamily_apply hω.orthonormal (i0, j0) (p, q)
  have hi0 :
      Section1.scalarProduct W (ω i j0) (ω p q) = 0 := by
    simpa [hi0_ne] using
      Section3.isOrthonormalDoubleFamily_apply hω.orthonormal (i, j0) (p, q)
  have h0j :
      Section1.scalarProduct W (ω i0 j) (ω p q) = 0 := by
    simpa [h0j_ne] using
      Section3.isOrthonormalDoubleFamily_apply hω.orthonormal (i0, j) (p, q)
  have hij :
      Section1.scalarProduct W (ω i j) (ω p q) =
        if i = p ∧ j = q then 1 else 0 := by
    by_cases hpair : (i, j) = (p, q)
    · have hi : i = p := congrArg Prod.fst hpair
      have hj : j = q := congrArg Prod.snd hpair
      simp [hi, hj] at *
      simpa using
        Section3.isOrthonormalDoubleFamily_apply hω.orthonormal (p, q) (p, q)
    · have hneq : ¬ (i = p ∧ j = q) := by
        intro h
        exact hpair (by simp [h.1, h.2])
      simpa [hpair, hneq] using
        Section3.isOrthonormalDoubleFamily_apply hω.orthonormal (i, j) (p, q)
  calc
    Section1.scalarProduct W (alphaIJ W i0 j0 ω i j) (ω p q) =
        Section1.scalarProduct W
          ((Section1.principalCharacter W - ω i j0 - ω i0 j) + ω i j) (ω p q) := by
            simp [alphaIJ, sub_eq_add_neg, add_assoc]
    _ = Section1.scalarProduct W (Section1.principalCharacter W - ω i j0 - ω i0 j)
          (ω p q) + Section1.scalarProduct W (ω i j) (ω p q) := by
            rw [Section1.scalarProduct_add_left]
    _ = (Section1.scalarProduct W (Section1.principalCharacter W - ω i j0) (ω p q) -
          Section1.scalarProduct W (ω i0 j) (ω p q)) +
          Section1.scalarProduct W (ω i j) (ω p q) := by
            rw [scalarProduct_sub_left']
    _ = ((Section1.scalarProduct W (Section1.principalCharacter W) (ω p q) -
          Section1.scalarProduct W (ω i j0) (ω p q)) -
          Section1.scalarProduct W (ω i0 j) (ω p q)) +
          Section1.scalarProduct W (ω i j) (ω p q) := by
            rw [scalarProduct_sub_left']
    _ = if i = p ∧ j = q then 1 else 0 := by
            rw [hprincipal, hi0, h0j, hij]
            by_cases h : i = p ∧ j = q <;> simp [h]

public theorem alphaIJ_CFOn_cyclicTISet
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (i : I) (j : J) :
    Section2.CFOn W (cyclicTISet W1 W2 W) (alphaIJ W i0 j0 ω i j) := by
  constructor
  · intro x g
    simp [alphaIJ, Section1.principalCharacter,
      hω.is_class i j0 x g, hω.is_class i0 j x g, hω.is_class i j x g]
  · intro x hx
    have hxW : (x : G) ∈ W := x.2
    have hx_union : (x : G) ∈ (W1 : Set G) ∪ (W2 : Set G) := by
      by_contra hnot
      exact hx ⟨hxW, hnot⟩
    rcases hx_union with hx1 | hx2
    · exact alphaIJ_eq_zero_of_mem_left hω i j hx1
    · exact alphaIJ_eq_zero_of_mem_right hω i j hx2

private theorem internalDirectProduct_mul_unique
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : Section2.IsInternalDirectProduct C H K)
    {h₁ h₂ k₁ k₂ : G}
    (hh₁ : h₁ ∈ H) (hh₂ : h₂ ∈ H)
    (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K)
    (hmul : h₁ * k₁ = h₂ * k₂) :
    h₁ = h₂ ∧ k₁ = k₂ := by
  have hleft_eq_right : h₂⁻¹ * h₁ = k₂ * k₁⁻¹ := by
    calc
      h₂⁻¹ * h₁ = h₂⁻¹ * (h₁ * k₁) * k₁⁻¹ := by
        simp [mul_assoc]
      _ = h₂⁻¹ * (h₂ * k₂) * k₁⁻¹ := by
        rw [hmul]
      _ = k₂ * k₁⁻¹ := by
        simp
  have hmemH : h₂⁻¹ * h₁ ∈ H := H.mul_mem (H.inv_mem hh₂) hh₁
  have hmemK : h₂⁻¹ * h₁ ∈ K := by
    rw [hleft_eq_right]
    exact K.mul_mem hk₂ (K.inv_mem hk₁)
  have hbot : h₂⁻¹ * h₁ ∈ (⊥ : Subgroup G) := by
    have hinf : h₂⁻¹ * h₁ ∈ H ⊓ K := Subgroup.mem_inf.mpr ⟨hmemH, hmemK⟩
    simpa [h.inf_eq_bot] using hinf
  have hh_eq_one : h₂⁻¹ * h₁ = 1 := by
    simpa using hbot
  have hh : h₁ = h₂ := by
    calc
      h₁ = h₂ * (h₂⁻¹ * h₁) := by simp
      _ = h₂ := by simp [hh_eq_one]
  have hk : k₁ = k₂ := by
    have hmul' := congrArg (fun z : G => h₂⁻¹ * z) hmul
    simpa [hh, mul_assoc] using hmul'
  exact ⟨hh, hk⟩

private noncomputable def pairSubtypeEquiv
    {X Y : Type*} (x0 : X) (y0 : Y) :
    {p : X × Y // p.1 ≠ x0 ∧ p.2 ≠ y0} ≃
      ({x : X // x ≠ x0} × {y : Y // y ≠ y0}) := by
  refine
    { toFun := fun p => (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
      invFun := fun q => ⟨(q.1.1, q.2.1), ⟨q.1.2, q.2.2⟩⟩
      left_inv := by
        intro p
        rfl
      right_inv := by
        intro q
        rfl }

private def cfSupportedOn {G : Type u} [Group G]
    (W : Subgroup G) (A : Set G) : Submodule ℂ (Section1.ClassFunction W) where
  carrier := {φ | ∀ x : W, (x : G) ∉ A → φ x = 0}
  zero_mem' := by
    intro x hx
    simp
  add_mem' := by
    intro φ ψ hφ hψ x hx
    simp [hφ x hx, hψ x hx]
  smul_mem' := by
    intro c φ hφ x hx
    simp [hφ x hx]

private noncomputable def cfSupportedOnEquivFun
    {G : Type u} [Group G] (W : Subgroup G) (A : Set G) :
    cfSupportedOn W A ≃ₗ[ℂ] ({x : W // (x : G) ∈ A} → ℂ) := by
  classical
  refine
    { toFun := fun φ x => (φ : Section1.ClassFunction W) x.1
      invFun := fun f =>
        ⟨fun x => if hx : (x : G) ∈ A then f ⟨x, hx⟩ else 0, by
          intro x hx
          simp [hx]⟩
      map_add' := by
        intro φ ψ
        ext x
        rfl
      map_smul' := by
        intro c φ
        ext x
        rfl
      left_inv := by
        intro φ
        ext x
        by_cases hx : (x : G) ∈ A
        · simp [hx]
        · have hsupport : ∀ x : W, (x : G) ∉ A → (φ : Section1.ClassFunction W) x = 0 := by
            exact φ.2
          simp [hx, hsupport x hx]
      right_inv := by
        intro f
        ext x
        simp [x.2] }

private theorem scalarProduct_sum_left'
    {H : Type*} [Finite H] {ι : Type*} [Fintype ι]
    (φ : Section1.ClassFunction H) (d : ι → ℂ) (psi : ι → Section1.ClassFunction H) :
    Section1.scalarProduct H (∑ i, d i • psi i) φ =
      ∑ i, d i * Section1.scalarProduct H (psi i) φ := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      simp [Section1.scalarProduct]
  | @insert i s hi hs =>
      simp [hi, hs, Section1.scalarProduct_add_left, Section1.scalarProduct_smul_left]

private theorem cfSupportedOn_finrank_eq_card
    {G : Type u} [Group G] (W : Subgroup G) (A : Set G)
    [Fintype {x : W // (x : G) ∈ A}] :
    Module.finrank ℂ (cfSupportedOn W A) =
      Fintype.card {x : W // (x : G) ∈ A} := by
  calc
    Module.finrank ℂ (cfSupportedOn W A) =
        Module.finrank ℂ ({x : W // (x : G) ∈ A} → ℂ) := by
          exact LinearEquiv.finrank_eq (cfSupportedOnEquivFun W A)
    _ = Fintype.card {x : W // (x : G) ∈ A} := by
          simp

public theorem cyclicTISetSubgroup_card
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (h : hypothesis_3_1_statement W1 W2 W) :
    Nat.card (cyclicTISetSubgroup W1 W2 W) =
      (Nat.card W1 - 1) * (Nat.card W2 - 1) := by
  classical
  change isCyclicTIHypothesis W1 W2 W at h
  rcases h with ⟨hW1, hW2, hIP, _hcyc, _hodd, _hcard1, _hcard2, _hTI⟩
  let f :
      {p : W1 × W2 // p.1 ≠ 1 ∧ p.2 ≠ 1} → cyclicTISetSubgroup W1 W2 W := by
    intro p
    refine ⟨⟨(p.1.1 : G) * (p.1.2 : G), ?_⟩, ?_⟩
    · exact W.mul_mem (hIP.left_le p.1.1.2) (hIP.right_le p.1.2.2)
    · have hmemW : (p.1.1 : G) * (p.1.2 : G) ∈ (cyclicTISet W1 W2 W) := by
        refine (cyclicTISet_mem_iff W1 W2 W).2 ?_
        constructor
        · exact W.mul_mem (hIP.left_le p.1.1.2) (hIP.right_le p.1.2.2)
        · constructor
          · intro h1
            have hbot : (p.1.2 : G) ∈ (⊥ : Subgroup G) := by
              have hW1' : (p.1.2 : G) ∈ (W1 : Set G) := by
                have : (p.1.1 : G)⁻¹ * ((p.1.1 : G) * (p.1.2 : G)) ∈ (W1 : Subgroup G) :=
                  W1.mul_mem (W1.inv_mem p.1.1.2) h1
                simpa [mul_assoc] using this
              simpa [hIP.inf_eq_bot] using
                (Subgroup.mem_inf.mpr ⟨hW1', p.1.2.2⟩)
            exact p.2.2 (by simpa using hbot)
          · intro h2
            have hbot : (p.1.1 : G) ∈ (⊥ : Subgroup G) := by
              have hW2' : (p.1.1 : G) ∈ (W2 : Set G) := by
                have : ((p.1.1 : G) * (p.1.2 : G)) * (p.1.2 : G)⁻¹ ∈ (W2 : Subgroup G) :=
                  W2.mul_mem h2 (W2.inv_mem p.1.2.2)
                simpa [mul_assoc] using this
              simpa [hIP.inf_eq_bot] using
                (Subgroup.mem_inf.mpr ⟨p.1.1.2, hW2'⟩)
            exact p.2.1 (by simpa using hbot)
      exact hmemW
  have hf_inj : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      have hmul :
          (p.1.1 : G) * (p.1.2 : G) = (q.1.1 : G) * (q.1.2 : G) := by
        simpa [f] using congrArg (fun z : cyclicTISetSubgroup W1 W2 W => ((z : W) : G)) hpq
      have huniq :=
        internalDirectProduct_mul_unique hIP p.1.1.2 q.1.1.2 p.1.2.2 q.1.2.2 hmul
      exact huniq.1
    · apply Subtype.ext
      have hmul :
          (p.1.1 : G) * (p.1.2 : G) = (q.1.1 : G) * (q.1.2 : G) := by
        simpa [f] using congrArg (fun z : cyclicTISetSubgroup W1 W2 W => ((z : W) : G)) hpq
      have huniq :=
        internalDirectProduct_mul_unique hIP p.1.1.2 q.1.1.2 p.1.2.2 q.1.2.2 hmul
      exact huniq.2
  have hf_surj : Function.Surjective f := by
    intro x
    have hxcyc := (cyclicTISet_mem_iff W1 W2 W).mp x.2
    rcases hIP.mul_surjective (x : G) hxcyc.1 with ⟨h₀, hh₀, k₀, hk₀, hx⟩
    have hh₀ne : (⟨h₀, hh₀⟩ : W1) ≠ 1 := by
      intro hh₀eq
      have hh₀eq' : h₀ = 1 := by
        simpa using congrArg Subtype.val hh₀eq
      have hxW2 : (x : G) ∈ (W2 : Set G) := by
        simpa [hx, hh₀eq'] using hk₀
      exact hxcyc.2.2 hxW2
    have hk₀ne : (⟨k₀, hk₀⟩ : W2) ≠ 1 := by
      intro hk₀eq
      have hk₀eq' : k₀ = 1 := by
        simpa using congrArg Subtype.val hk₀eq
      have hxW1 : (x : G) ∈ (W1 : Set G) := by
        simpa [hx, hk₀eq'] using hh₀
      exact hxcyc.2.1 hxW1
    refine ⟨⟨(⟨h₀, hh₀⟩, ⟨k₀, hk₀⟩), ⟨hh₀ne, hk₀ne⟩⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hx.symm
  have hpair :
      Fintype.card {p : W1 × W2 // p.1 ≠ 1 ∧ p.2 ≠ 1} =
        Fintype.card ({x : W1 // x ≠ 1} × {y : W2 // y ≠ 1}) := by
    simpa using
      (Fintype.card_congr (pairSubtypeEquiv (X := W1) (Y := W2) (1 : W1) (1 : W2)))
  have hW1card :
      Fintype.card {x : W1 // x ≠ 1} = Nat.card W1 - 1 := by
    simp [Nat.card_eq_fintype_card]
  have hW2card :
      Fintype.card {y : W2 // y ≠ 1} = Nat.card W2 - 1 := by
    simp [Nat.card_eq_fintype_card]
  calc
    Nat.card (cyclicTISetSubgroup W1 W2 W) =
        Fintype.card {p : W1 × W2 // p.1 ≠ 1 ∧ p.2 ≠ 1} := by
          simpa [Nat.card_eq_fintype_card] using
            (Fintype.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)).symm
    _ = Fintype.card ({x : W1 // x ≠ 1} × {y : W2 // y ≠ 1}) := hpair
    _ = (Nat.card W1 - 1) * (Nat.card W2 - 1) := by
          rw [Fintype.card_prod]
          simp [hW1card, hW2card]

private theorem alphaIJ_linearIndependent
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω) :
    LinearIndependent ℂ
      (fun p : {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0} =>
        alphaIJ W i0 j0 ω p.1.1 p.1.2) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha p
  have hcoord :
      ∀ q : {q : I × J // q.1 ≠ i0 ∧ q.2 ≠ j0},
        Section1.scalarProduct W
          (alphaIJ W i0 j0 ω q.1.1 q.1.2)
          (ω p.1.1 p.1.2) =
            if q = p then 1 else 0 := by
    intro q
    have hraw :=
      alphaIJ_scalarProduct_omega hω q.1.1 q.1.2 p.2.1 p.2.2
    by_cases hqp : q = p
    · subst hqp
      simpa using hraw
    · have hpair : ¬ (q.1.1 = p.1.1 ∧ q.1.2 = p.1.2) := by
        intro hp
        exact hqp (Subtype.ext (Prod.ext hp.1 hp.2))
      simpa [hpair, hqp] using hraw
  have hinner :
      Section1.scalarProduct W
        (∑ q, a q • alphaIJ W i0 j0 ω q.1.1 q.1.2)
        (ω p.1.1 p.1.2) = 0 := by
    rw [ha]
    simp [Section1.scalarProduct]
  have hcoeff :
      Section1.scalarProduct W
        (∑ q, a q • alphaIJ W i0 j0 ω q.1.1 q.1.2)
        (ω p.1.1 p.1.2) = a p := by
    rw [scalarProduct_sum_left']
    simp [hcoord]
  exact hcoeff ▸ hinner

public theorem proposition_3_4
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (omega : I → J → Section1.ClassFunction W)
    (h : hypothesis_3_1_statement W1 W2 W)
    (homega : notation_3_3_statement W1 W2 W I J i0 j0 omega) :
    proposition_3_4_statement W1 W2 W I J i0 j0 omega h homega := by
  classical
  let V : Set G := cyclicTISet W1 W2 W
  let alpha :
      {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0} → Section1.ClassFunction W :=
    fun p => alphaIJ W i0 j0 omega p.1.1 p.1.2
  have h_support : ∀ p, Section2.CFOn W V (alpha p) := by
    intro p
    simpa [alpha] using
      alphaIJ_CFOn_cyclicTISet W1 W2 W I J i0 j0 omega homega p.1.1 p.1.2
  have h_li : LinearIndependent ℂ alpha := by
    simpa [alpha] using alphaIJ_linearIndependent (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := omega) homega
  have hcard_idx :
      Fintype.card {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0} =
        (Nat.card W1 - 1) * (Nat.card W2 - 1) := by
    have hI : Fintype.card {i : I // i ≠ i0} = Nat.card W1 - 1 := by
      simp [homega.card_left]
    have hJ : Fintype.card {j : J // j ≠ j0} = Nat.card W2 - 1 := by
      simp [homega.card_right]
    calc
      Fintype.card {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0} =
          Fintype.card ({i : I // i ≠ i0} × {j : J // j ≠ j0}) := by
            simpa using (Fintype.card_congr (pairSubtypeEquiv (X := I) (Y := J) i0 j0))
      _ = (Nat.card W1 - 1) * (Nat.card W2 - 1) := by
            rw [Fintype.card_prod]
            simp [hI, hJ]
  have hcard_V :
      Fintype.card (cyclicTISetSubgroup W1 W2 W) =
        (Nat.card W1 - 1) * (Nat.card W2 - 1) := by
    simpa [Nat.card_eq_fintype_card] using cyclicTISetSubgroup_card W1 W2 W h
  have hfinrank_V :
      Module.finrank ℂ (cfSupportedOn W V) =
        Fintype.card (cyclicTISetSubgroup W1 W2 W) := by
    have hV :
        ({x : W | (x : G) ∈ V} : Set W) = cyclicTISetSubgroup W1 W2 W := by
      ext x
      simp [V, cyclicTISetSubgroup]
    calc
      Module.finrank ℂ (cfSupportedOn W V) =
          Fintype.card {x : W // (x : G) ∈ V} :=
        cfSupportedOn_finrank_eq_card W V
      _ = Fintype.card (cyclicTISetSubgroup W1 W2 W) :=
        Fintype.card_congr (Set.equivOfEq hV)
  have hcard :
      Fintype.card {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0} =
        Module.finrank ℂ (cfSupportedOn W V) := by
    calc
      Fintype.card {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0} =
          (Nat.card W1 - 1) * (Nat.card W2 - 1) := hcard_idx
      _ = Fintype.card (cyclicTISetSubgroup W1 W2 W) := by
          symm
          exact hcard_V
      _ = Module.finrank ℂ (cfSupportedOn W V) := by
          symm
          exact hfinrank_V
  let e : {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0} → cfSupportedOn W V := fun p =>
    ⟨alpha p, by
      intro x hx
      exact (h_support p).2 x hx⟩
  have h_li_sub : LinearIndependent ℂ e := by
    simpa [e, alpha] using
      (LinearIndependent.of_comp
        (Submodule.subtype (cfSupportedOn W V))
        (v := e)
        (hfv := h_li))
  have hspan :
      ⊤ ≤ Submodule.span ℂ (Set.range e) := by
    rw [LinearIndependent.span_eq_top_of_card_eq_finrank' h_li_sub hcard]
  let hbasis : Module.Basis
      {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0} ℂ (cfSupportedOn W V) :=
    Module.Basis.mk h_li_sub hspan
  refine ⟨h_support, h_li, ?_⟩
  intro ψ hψ
  let x : cfSupportedOn W V := ⟨ψ, hψ.2⟩
  refine ⟨hbasis.repr x, ?_⟩
  have hx :
      ((∑ p, hbasis.repr x p • (hbasis p : cfSupportedOn W V)) :
          cfSupportedOn W V) = x := by
    exact hbasis.sum_repr x
  simpa [hbasis, e, alpha] using (congrArg Subtype.val hx).symm

end CFSG.Section3
