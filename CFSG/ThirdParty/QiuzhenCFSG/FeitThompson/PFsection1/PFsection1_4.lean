module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_3
public import Mathlib.Analysis.Complex.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.RepEquiv
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Unbundled

namespace CFSG
end CFSG
open CFSG
/-!
# Peterfalvi, Section 1, Proposition (1.4)

This file is the Lean target for `PFtest/Blueprint/section1/proposition_1_4.tex`.

Current scope discipline:

* Only Mathlib modules are imported.
* No Lean files outside `PFtest` are imported or read.
* The coefficient model endpoint is kept private: it is useful proof
  infrastructure, but it is not counted as Proposition (1.4) until the bridge
  from the model to actual irreducible characters of `G` is formalized.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section1
universe u
universe v

/-! ## Basic notation for Proposition (1.4) -/

@[expose] public def degree {G : Type*} [One G] (phi : ClassFunction G) : ℂ := phi 1

public theorem degree_apply {G : Type*} [One G] (phi : ClassFunction G) : degree phi = phi 1 := rfl

@[expose] public def IsSign (eps : ℂ) : Prop :=
  eps = 1 ∨ eps = -1

@[expose] public def IsIrreducibleCharacterFamily {G I : Type*} (mu : I → ClassFunction G) : Prop :=
  Pairwise fun i j => mu i ≠ mu j

@[expose] public def IsIrreducibleCharacterOnGroup
    {G : Type*} [Group G] [Finite G] (mu : ClassFunction G) : Prop :=
  ∃ n : ℕ, ∃ ρ : Representation ℂ G (Fin n → ℂ),
    Representation.IsIrreducible ρ ∧ mu = ρ.character

@[expose] public noncomputable def standardizeRepresentation
    {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    Representation ℂ G (Fin (Module.finrank ℂ V) → ℂ) := by
  let b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V := Module.finBasis ℂ V
  let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := b.equivFun
  refine
    { toFun := fun g => e.conj (ρ g)
      map_one' := by
        ext x
        simp [LinearEquiv.conj_apply]
      map_mul' := by
        intro g h
        ext x
        simp [LinearEquiv.conj_apply, map_mul] }

public theorem standardizeRepresentation_character
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    (standardizeRepresentation ρ).character g = ρ.character g := by
  dsimp [standardizeRepresentation, Representation.character]
  exact LinearMap.trace_conj' (R := ℂ) (M := V)
    (N := Fin (Module.finrank ℂ V) → ℂ) (ρ g)
    (Module.Basis.equivFun (Module.finBasis ℂ V))

public theorem standardizeRepresentation_irreducible
    {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : Representation.IsIrreducible ρ) :
    Representation.IsIrreducible (standardizeRepresentation ρ) := by
  let b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V := Module.finBasis ℂ V
  let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := b.equivFun
  let eRep : Theory.Representation.RepEquiv ρ (standardizeRepresentation ρ) := by
    refine
      { toLinearEquiv := e
        isIntertwining' := ?_ }
    intro g
    ext v i
    have h := congrArg (fun w => w i)
      (LinearMap.toMatrix_mulVec_repr (v₁ := b) (v₂ := b) (f := ρ g) v)
    simp [standardizeRepresentation, e, b, b.equivFun_apply]
  exact (Theory.Representation.RepEquiv.irreducible_euqiv eRep).1 hρ

public theorem isIrreducibleCharacterOnGroup_of_representation
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : Representation.IsIrreducible ρ) :
    IsIrreducibleCharacterOnGroup ρ.character := by
  refine ⟨Module.finrank ℂ V, standardizeRepresentation ρ, ?_, ?_⟩
  · exact standardizeRepresentation_irreducible ρ hρ
  · ext g
    exact (standardizeRepresentation_character ρ g).symm

@[expose] public def IsIrreducibleCharacterBasis
    {G I : Type*} [Group G] [Finite G] (mu : I → ClassFunction G) : Prop :=
  (∀ i, IsIrreducibleCharacterOnGroup (mu i)) ∧ IsIrreducibleCharacterFamily mu


@[expose] public def IsOrthonormalFamily
    {G I : Type*} [Finite G] [DecidableEq I] (chi : I → ClassFunction G) : Prop :=
  ∀ i j, scalarProduct G (chi i) (chi j) = if i = j then 1 else 0


/-! ### Honest coefficient-space model for the codomain

This is the combinatorial model used for the current local proof nodes. It
models `Z[Irr(G), G^#]` as integer coefficient vectors on a finite
ambient family of irreducibles.
-/

public abbrev CoeffVector (J : Type*) := J → Int

@[expose] public def IsSignInt (eps : Int) : Prop :=
  eps = 1 ∨ eps = -1

@[expose] public def basisVector {J : Type*} [DecidableEq J] (j : J) : CoeffVector J :=
  fun k => if k = j then 1 else 0

@[expose] public def coeffSupport {J : Type*} [Fintype J] [DecidableEq J] (v : CoeffVector J) : Finset J :=
  Finset.univ.filter fun j => v j ≠ 0

@[expose] public def coeffDot {J : Type*} [Fintype J] (v w : CoeffVector J) : Int :=
  ∑ j : J, v j * w j

@[expose] public def coeffSqNorm {J : Type*} [Fintype J] [DecidableEq J] (v : CoeffVector J) : Nat :=
  Finset.sum (coeffSupport v) fun j => (Int.natAbs (v j)) ^ 2

@[expose] public def coeffDegree {J : Type*} [Fintype J] [DecidableEq J]
    (d : J → Nat) (v : CoeffVector J) : Int :=
  Finset.sum (coeffSupport v) fun j => v j * d j

@[expose] public def signedBasisDifference {J : Type*} [DecidableEq J]
    (eps : Int) (j1 j2 : J) : CoeffVector J :=
  eps • (basisVector j2 - basisVector j1)

@[expose] public def evalCoeff {G J : Type*} [Fintype J]
    (mu : J → ClassFunction G) (v : CoeffVector J) : ClassFunction G :=
  ∑ j : J, (v j : ℂ) • mu j

/--
The integral isometry data in Peterfalvi (1.4), expressed on the differences
`chi i - chi 0`.  The coefficients are taken in the irreducible-character
basis of `G`, the weight `d j` is explicitly tied to the character degree, and
`map_degree_zero` records that the image lies in the `G#` lattice.
-/
@[expose] public def IsIntegralIsometryOnCharacterDifferences
    {G H J : Type*} [Finite G] [Finite H] [One G] [One H]
    [Fintype J] [DecidableEq J]
    {n : ℕ} [NeZero n]
    (muBasis : J → ClassFunction G) (d : J → Nat)
    (chi : Fin n → ClassFunction H) (T : ClassFunction H → ClassFunction G) : Prop :=
  (∀ j, degree (muBasis j) = (d j : ℂ)) ∧
    (∀ j, 0 < d j) ∧
    ∃ coeff : Fin n → CoeffVector J,
      coeff 0 = 0 ∧
        (∀ i : Fin n, degree (T (chi i - chi 0)) = 0) ∧
        (∀ i j : Fin n,
          (coeffDot (coeff i) (coeff j) : ℂ) =
            scalarProduct H (chi i - chi 0) (chi j - chi 0)) ∧
        ∀ i : Fin n, T (chi i - chi 0) = evalCoeff muBasis (coeff i)

@[simp] public theorem mem_coeffSupport
    {J : Type*} [Fintype J] [DecidableEq J] (v : CoeffVector J) (j : J) :
    j ∈ coeffSupport v ↔ v j ≠ 0 := by
  simp [coeffSupport]

public theorem coeff_eq_zero_of_not_mem_support
    {J : Type*} [Fintype J] [DecidableEq J] (v : CoeffVector J) {j : J}
    (hj : j ∉ coeffSupport v) :
    v j = 0 := by
  by_contra hne
  exact hj ((mem_coeffSupport v j).2 hne)

public theorem degree_evalCoeff_eq_coeffDegree
    {G J : Type*} [One G] [Fintype J] [DecidableEq J]
    (mu : J → ClassFunction G) (d : J → Nat)
    (hdeg : ∀ j, degree (mu j) = (d j : ℂ))
    (v : CoeffVector J) :
    degree (evalCoeff mu v) = (coeffDegree d v : ℂ) := by
  calc
    degree (evalCoeff mu v)
        = ∑ j : J, (v j : ℂ) * degree (mu j) := by
            simp [degree, evalCoeff]
    _ = ∑ j : J, (v j : ℂ) * (d j : ℂ) := by
          simp [hdeg]
    _ = Finset.sum (coeffSupport v) (fun j => (v j : ℂ) * (d j : ℂ)) := by
          symm
          apply Finset.sum_subset
          · intro j _hj
            simp
          · intro j _hj hjNotMem
            have hj0 : v j = 0 := coeff_eq_zero_of_not_mem_support v hjNotMem
            simp [hj0]
    _ = (coeffDegree d v : ℂ) := by
          simp [coeffDegree]

@[simp] lemma coeffSupport_basisVector
    {J : Type*} [Fintype J] [DecidableEq J] (j : J) :
    coeffSupport (basisVector j) = {j} := by
  ext k
  by_cases h : k = j
  · subst h
    simp [coeffSupport, basisVector]
  · simp [coeffSupport, basisVector, h]

@[simp] lemma basisVector_apply_eq {J : Type*} [DecidableEq J] (j : J) :
    basisVector j j = 1 := by
  simp [basisVector]

@[simp] lemma basisVector_apply_ne {J : Type*} [DecidableEq J] {j k : J} (h : k ≠ j) :
    basisVector j k = 0 := by
  simp [basisVector, h]

@[simp] lemma coeffDot_basis_left
    {J : Type*} [Fintype J] [DecidableEq J] (j : J) (v : CoeffVector J) :
    coeffDot (basisVector j) v = v j := by
  simp [coeffDot, basisVector]

@[simp] lemma coeffDot_basis_right
    {J : Type*} [Fintype J] [DecidableEq J] (v : CoeffVector J) (j : J) :
    coeffDot v (basisVector j) = v j := by
  simp [coeffDot, basisVector]

@[simp] lemma coeffDot_basis_basis
    {J : Type*} [Fintype J] [DecidableEq J] (i j : J) :
    coeffDot (basisVector i) (basisVector j) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h
    simp
  · have hji : j ≠ i := by
      intro h'
      exact h h'.symm
    simp [basisVector, coeffDot, h, hji]


lemma coeffDot_sub_left
    {J : Type*} [Fintype J] (u v w : CoeffVector J) :
    coeffDot (u - v) w = coeffDot u w - coeffDot v w := by
  unfold coeffDot
  calc
    ∑ x : J, (u x - v x) * w x = ∑ x : J, (u x * w x - v x * w x) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      ring
    _ = (∑ x : J, u x * w x) - ∑ x : J, v x * w x := by
      simp [sub_eq_add_neg, Finset.sum_add_distrib]


lemma coeffDot_sub_right
    {J : Type*} [Fintype J] (u v w : CoeffVector J) :
    coeffDot u (v - w) = coeffDot u v - coeffDot u w := by
  unfold coeffDot
  calc
    ∑ x : J, u x * (v x - w x) = ∑ x : J, (u x * v x - u x * w x) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      ring
    _ = (∑ x : J, u x * v x) - ∑ x : J, u x * w x := by
      simp [sub_eq_add_neg, Finset.sum_add_distrib]

lemma coeffDot_basis_difference_basis_difference
    {J : Type*} [Fintype J] [DecidableEq J]
    (a b c d : J) :
    coeffDot (basisVector b - basisVector a) (basisVector d - basisVector c) =
      (if b = d then 1 else 0) - (if b = c then 1 else 0) -
        (if a = d then 1 else 0) + (if a = c then 1 else 0) := by
  rw [coeffDot_sub_left, coeffDot_sub_right, coeffDot_sub_right]
  simp [basisVector, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, eq_comm]

lemma coeffSupport_basis_difference
    {J : Type*} [Fintype J] [DecidableEq J] {j1 j2 : J} (h12 : j1 ≠ j2) :
    coeffSupport (basisVector j2 - basisVector j1) = {j1, j2} := by
  have h21 : j2 ≠ j1 := by
    intro h
    exact h12 h.symm
  ext j
  by_cases h1 : j = j1
  · subst h1
    simp [basisVector, h12]
  · by_cases h2 : j = j2
    · subst h2
      simp [basisVector, h21]
    · simp [basisVector, h1, h2]


lemma coeffSqNorm_signedBasisDifference
    {J : Type*} [Fintype J] [DecidableEq J]
    (eps : Int) (heps : IsSignInt eps) {j1 j2 : J} (h12 : j1 ≠ j2) :
    coeffSqNorm (signedBasisDifference eps j1 j2) = 2 := by
  have h21 : j2 ≠ j1 := by
    intro h
    exact h12 h.symm
  rcases heps with rfl | rfl
  · have hb :
        signedBasisDifference 1 j1 j2 = basisVector j2 - basisVector j1 := by
        ext j
        simp [signedBasisDifference]
    rw [hb]
    rw [coeffSqNorm, coeffSupport_basis_difference h12]
    simp [basisVector, h12, h21]
  · have hb :
        signedBasisDifference (-1) j1 j2 = basisVector j1 - basisVector j2 := by
        ext j
        simp [signedBasisDifference]
    rw [hb]
    rw [coeffSqNorm, coeffSupport_basis_difference h21]
    simp [basisVector, h12, h21]


lemma coeffSqNorm_term_le
    {J : Type*} [Fintype J] [DecidableEq J] (v : CoeffVector J) {j : J}
    (hj : j ∈ coeffSupport v) :
    (Int.natAbs (v j)) ^ 2 ≤ coeffSqNorm v := by
  simpa [coeffSqNorm] using
    (Finset.single_le_sum
      (s := coeffSupport v)
      (a := j)
      (f := fun i => (Int.natAbs (v i)) ^ 2)
      (by
        intro i hi
        positivity)
      hj)

lemma natAbs_eq_one_of_mem_support_of_coeffSqNorm_eq_two
    {J : Type*} [Fintype J] [DecidableEq J] (v : CoeffVector J) {j : J}
    (hj : j ∈ coeffSupport v) (hnorm : coeffSqNorm v = 2) :
    Int.natAbs (v j) = 1 := by
  set n : Nat := Int.natAbs (v j)
  have hsq : n ^ 2 ≤ 2 := by
    simpa [n, hnorm] using coeffSqNorm_term_le v hj
  have hne0 : n ≠ 0 := by
    intro h0
    have hv0 : v j = 0 := by
      exact Int.natAbs_eq_zero.mp (by simpa [n] using h0)
    exact (mem_coeffSupport v j).1 hj hv0
  have hpos : 0 < n := Nat.pos_of_ne_zero hne0
  have hle1 : n ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ n := by omega
    have h4 : 4 ≤ n ^ 2 := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ n ^ 2 := by
          gcongr
    omega
  omega

lemma coeffSqNorm_ne_two_of_three_mem_support
    {J : Type*} [Fintype J] [DecidableEq J] (v : CoeffVector J)
    {a b c : J}
    (ha : a ∈ coeffSupport v) (hb : b ∈ coeffSupport v) (hc : c ∈ coeffSupport v)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    coeffSqNorm v ≠ 2 := by
  intro hnorm
  let t : Finset J := {a, b, c}
  have ht_sub : t ⊆ coeffSupport v := by
    intro j hj
    have hj' : j = a ∨ j = b ∨ j = c := by
      simpa [t, or_assoc, or_left_comm, or_comm] using hj
    rcases hj' with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have hle :
      Finset.sum t (fun j => (Int.natAbs (v j)) ^ 2) ≤ coeffSqNorm v := by
    unfold coeffSqNorm
    exact Finset.sum_le_sum_of_subset_of_nonneg ht_sub (by
      intro j hj _
      positivity)
  have hthree :
      Finset.sum t (fun j => (Int.natAbs (v j)) ^ 2) = 3 := by
    have ha1 : Int.natAbs (v a) = 1 :=
      natAbs_eq_one_of_mem_support_of_coeffSqNorm_eq_two v ha hnorm
    have hb1 : Int.natAbs (v b) = 1 :=
      natAbs_eq_one_of_mem_support_of_coeffSqNorm_eq_two v hb hnorm
    have hc1 : Int.natAbs (v c) = 1 :=
      natAbs_eq_one_of_mem_support_of_coeffSqNorm_eq_two v hc hnorm
    simp [t, ha1, hb1, hc1, hab, hac, hbc]
  rw [hthree, hnorm] at hle
  omega

lemma coeffSupport_card_le_two_of_coeffSqNorm_eq_two
    {J : Type*} [Fintype J] [DecidableEq J] (v : CoeffVector J)
    (hnorm : coeffSqNorm v = 2) :
    (coeffSupport v).card ≤ 2 := by
  by_contra hcard
  have hlt : 2 < (coeffSupport v).card := by
    omega
  rcases Finset.two_lt_card.1 hlt with ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩
  exact coeffSqNorm_ne_two_of_three_mem_support v ha hb hc hab hac hbc hnorm

lemma coeffSupport_nonempty_of_coeffSqNorm_eq_two
    {J : Type*} [Fintype J] [DecidableEq J] (v : CoeffVector J)
    (hnorm : coeffSqNorm v = 2) :
    (coeffSupport v).Nonempty := by
  by_contra hempty
  have hs : coeffSupport v = ∅ := by
    exact Finset.not_nonempty_iff_eq_empty.mp hempty
  rw [coeffSqNorm, hs] at hnorm
  simp at hnorm

lemma coeffSupport_card_ne_one_of_coeffSqNorm_eq_two
    {J : Type*} [Fintype J] [DecidableEq J] (v : CoeffVector J)
    (hnorm : coeffSqNorm v = 2) :
    (coeffSupport v).card ≠ 1 := by
  intro hcard
  rcases Finset.card_eq_one.1 hcard with ⟨a, ha⟩
  have ha_mem : a ∈ coeffSupport v := by
    simp [ha]
  have ha1 : Int.natAbs (v a) = 1 :=
    natAbs_eq_one_of_mem_support_of_coeffSqNorm_eq_two v ha_mem hnorm
  rw [coeffSqNorm, ha] at hnorm
  simp [ha1] at hnorm

lemma coeffSupport_card_eq_two_of_coeffSqNorm_eq_two
    {J : Type*} [Fintype J] [DecidableEq J] (v : CoeffVector J)
    (hnorm : coeffSqNorm v = 2) :
    (coeffSupport v).card = 2 := by
  have hle : (coeffSupport v).card ≤ 2 :=
    coeffSupport_card_le_two_of_coeffSqNorm_eq_two v hnorm
  have hne0 : (coeffSupport v).card ≠ 0 := by
    intro h0
    have hempty : coeffSupport v = ∅ := Finset.card_eq_zero.mp h0
    rw [coeffSqNorm, hempty] at hnorm
    simp at hnorm
  have hne1 : (coeffSupport v).card ≠ 1 :=
    coeffSupport_card_ne_one_of_coeffSqNorm_eq_two v hnorm
  omega

lemma coeff_eq_sign_of_natAbs_eq_one {z : Int} (hz : Int.natAbs z = 1) :
    z = 1 ∨ z = -1 := by
  simpa using (Int.natAbs_eq_iff.mp hz)

lemma exists_support_pair_of_coeffSqNorm_eq_two
    {J : Type*} [Fintype J] [DecidableEq J] (v : CoeffVector J)
    (hnorm : coeffSqNorm v = 2) :
    ∃ a b : J, a ≠ b ∧ coeffSupport v = {a, b} := by
  classical
  let s := coeffSupport v
  have hs2 : s.card = 2 := coeffSupport_card_eq_two_of_coeffSqNorm_eq_two v hnorm
  rcases coeffSupport_nonempty_of_coeffSqNorm_eq_two v hnorm with ⟨a, ha⟩
  have hcardErase : (s.erase a).card = 1 := by
    have := Finset.card_erase_add_one ha (s := s)
    omega
  rcases Finset.card_eq_one.1 hcardErase with ⟨b, hb⟩
  have hab : a ≠ b := by
    intro hab'
    subst hab'
    have : a ∈ ({a} : Finset J) := by simp
    rw [← hb] at this
    simp at this
  refine ⟨a, b, hab, ?_⟩
  calc
    coeffSupport v = s := rfl
    _ = insert a (s.erase a) := by rw [Finset.insert_erase ha]
    _ = {a, b} := by rw [hb]

lemma coeff_eq_zero_of_not_mem_support_pair
    {J : Type*} [Fintype J] [DecidableEq J] {v : CoeffVector J} {a b j : J}
    (hs : coeffSupport v = {a, b}) (hj : j ≠ a) (hj' : j ≠ b) :
    v j = 0 := by
  apply coeff_eq_zero_of_not_mem_support v
  rw [hs]
  simp [hj, hj']

lemma coeff_eq_signedBasisDifference_of_coeffSqNorm_eq_two_of_coeffDegree_eq_zero
    {J : Type*} [Fintype J] [DecidableEq J]
    (d : J → Nat) (v : CoeffVector J)
    (hpos : ∀ j, 0 < d j)
    (hnorm : coeffSqNorm v = 2)
    (hdeg : coeffDegree d v = 0) :
    ∃ eps : Int, IsSignInt eps ∧ ∃ a b : J, a ≠ b ∧ v = signedBasisDifference eps a b := by
  rcases exists_support_pair_of_coeffSqNorm_eq_two v hnorm with ⟨a, b, hab, hs⟩
  have ha_mem : a ∈ coeffSupport v := by rw [hs]; simp
  have hb_mem : b ∈ coeffSupport v := by rw [hs]; simp
  have ha_abs : Int.natAbs (v a) = 1 :=
    natAbs_eq_one_of_mem_support_of_coeffSqNorm_eq_two v ha_mem hnorm
  have hb_abs : Int.natAbs (v b) = 1 :=
    natAbs_eq_one_of_mem_support_of_coeffSqNorm_eq_two v hb_mem hnorm
  have hva : v a = 1 ∨ v a = -1 := coeff_eq_sign_of_natAbs_eq_one ha_abs
  have hvb : v b = 1 ∨ v b = -1 := coeff_eq_sign_of_natAbs_eq_one hb_abs
  have hba : b ≠ a := by
    intro h
    exact hab h.symm
  rcases hva with ha1 | ha_1 <;> rcases hvb with hb1 | hb_1
  · exfalso
    rw [coeffDegree, hs] at hdeg
    simp [ha1, hb1, hab] at hdeg
    have hpa : (0 : Int) < d a := by exact_mod_cast hpos a
    have hpb : (0 : Int) < d b := by exact_mod_cast hpos b
    linarith
  · refine ⟨-1, Or.inr rfl, a, b, hab, ?_⟩
    ext j
    by_cases hja : j = a
    · subst hja
      simp [signedBasisDifference, ha1, hab]
    · by_cases hjb : j = b
      · subst hjb
        simp [signedBasisDifference, hb_1, hba]
      · have hv0 := coeff_eq_zero_of_not_mem_support_pair hs hja hjb
        simp [signedBasisDifference, hja, hjb, hv0]
  · refine ⟨1, Or.inl rfl, a, b, hab, ?_⟩
    ext j
    by_cases hja : j = a
    · subst hja
      simp [signedBasisDifference, ha_1, hab]
    · by_cases hjb : j = b
      · subst hjb
        simp [signedBasisDifference, hb1, hba]
      · have hv0 := coeff_eq_zero_of_not_mem_support_pair hs hja hjb
        simp [signedBasisDifference, hja, hjb, hv0]
  · exfalso
    rw [coeffDegree, hs] at hdeg
    simp [ha_1, hb_1, hab] at hdeg
    have hpa : (0 : Int) < d a := by exact_mod_cast hpos a
    have hpb : (0 : Int) < d b := by exact_mod_cast hpos b
    linarith

lemma coeff_normTwo_degreeZero_classification
    {J : Type*} [Fintype J] [DecidableEq J]
    (d : J → Nat) (v : CoeffVector J)
    (hpos : ∀ j, 0 < d j)
    (hnorm : coeffSqNorm v = 2)
    (hdeg : coeffDegree d v = 0) :
    ∃ eps : Int, IsSignInt eps ∧ ∃ a b : J, a ≠ b ∧ v = signedBasisDifference eps a b :=
  coeff_eq_signedBasisDifference_of_coeffSqNorm_eq_two_of_coeffDegree_eq_zero d v hpos hnorm hdeg

lemma signedBasisDifference_neg_eq_swap
    {J : Type*} [DecidableEq J] (a b : J) :
    signedBasisDifference (-1) a b = signedBasisDifference 1 b a := by
  ext j
  simp [signedBasisDifference]

lemma signedBasisDifference_neg_sign_swap
    {J : Type*} [DecidableEq J] {eps : Int} (heps : IsSignInt eps) (a b : J) :
    signedBasisDifference (-eps) a b = signedBasisDifference eps b a := by
  rcases heps with rfl | rfl <;> simp [signedBasisDifference]

lemma signedBasisDifference_one_injective
    {J : Type*} [Fintype J] [DecidableEq J]
    {a b c d : J} (hab : a ≠ b) (hcd : c ≠ d)
    (hEq : signedBasisDifference 1 a b = signedBasisDifference 1 c d) :
    a = c ∧ b = d := by
  have hb := congrArg (fun v => v b) hEq
  have hdb : d = b := by
    by_cases hdb : d = b
    · exact hdb
    · by_cases hcb : c = b
      · have : b ≠ d := by
          intro h
          exact hdb h.symm
        have hba : b ≠ a := hab.symm
        exfalso
        simp [signedBasisDifference, hcb, this] at hb
        simp [hba] at hb
      · have : b ≠ d := by
          intro h
          exact hdb h.symm
        have hba : b ≠ a := hab.symm
        have hbc : b ≠ c := by
          intro h
          exact hcb h.symm
        exfalso
        simp [signedBasisDifference, this] at hb
        simp [hba, hbc] at hb
  have ha := congrArg (fun v => v a) hEq
  have hac : a = c := by
    have hcb : c ≠ b := by
      intro h
      exact hcd (h.trans hdb.symm)
    have had : a ≠ d := by
      rw [hdb]
      exact hab
    by_cases hac : a = c
    · exact hac
    · exfalso
      simp [signedBasisDifference, hac, hab, hdb] at ha
  exact ⟨hac, hdb.symm⟩

lemma signedBasisDifference_eq_cases
    {J : Type*} [Fintype J] [DecidableEq J]
    {eps1 eps2 : Int} {a b c d : J}
    (he1 : IsSignInt eps1) (he2 : IsSignInt eps2)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hEq : signedBasisDifference eps1 a b = signedBasisDifference eps2 c d) :
    (eps1 = eps2 ∧ a = c ∧ b = d) ∨
      (eps1 = -eps2 ∧ a = d ∧ b = c) := by
  rcases he1 with rfl | rfl <;> rcases he2 with rfl | rfl
  · rcases signedBasisDifference_one_injective hab hcd hEq with ⟨hac, hbd⟩
    exact Or.inl ⟨rfl, hac, hbd⟩
  · rw [signedBasisDifference_neg_eq_swap] at hEq
    rcases signedBasisDifference_one_injective hab (by simpa using hcd.symm) hEq with
      ⟨had, hbc⟩
    exact Or.inr ⟨rfl, had, hbc⟩
  · rw [signedBasisDifference_neg_eq_swap a b] at hEq
    rcases signedBasisDifference_one_injective (by simpa using hab.symm) hcd hEq with
      ⟨hbc, had⟩
    exact Or.inr ⟨rfl, had, hbc⟩
  · rw [signedBasisDifference_neg_eq_swap a b, signedBasisDifference_neg_eq_swap c d] at hEq
    rcases signedBasisDifference_one_injective (by simpa using hab.symm)
        (by simpa using hcd.symm) hEq with ⟨hbd, hac⟩
    exact Or.inl ⟨rfl, hac, hbd⟩

/- Old proof block retained only for reference while the stable replacement below is built.
The text in this region became structurally corrupted and triggers spurious
`No goals to be solved` diagnostics. -/

/-
lemma coeff_normTwo_degreeZero_classification_eps_one
    {J : Type*} [Fintype J] [DecidableEq J]
    (d : J → Nat) (v : CoeffVector J)
    (hpos : ∀ j, 0 < d j)
    (hnorm : coeffSqNorm v = 2)
    (hdeg : coeffDegree d v = 0) :
    ∃ a b : J, a ≠ b ∧ v = signedBasisDifference 1 a b := by
  rcases coeff_normTwo_degreeZero_classification d v hpos hnorm hdeg with
    ⟨eps, heps, a, b, hab, hv⟩;
  cases heps with
  | inl h1 =>
      subst h1
      exact Exists.intro a <| Exists.intro b <| And.intro hab hv
  | inr hneg1 =>
      subst hneg1
      refine Exists.intro b ?_
      refine Exists.intro a ?_
      exact And.intro
        (by
          intro h
          exact hab h.symm)
        (by
          calc
            v = signedBasisDifference (-1) a b := hv
            _ = signedBasisDifference 1 b a := signedBasisDifference_neg_eq_swap a b)

lemma coeffDot_eq_one_of_basisDifferences_cases
    {J : Type*} [Fintype J] [DecidableEq J]
    {a1 b1 a2 b2 : J}
    (ha1b1 : a1 ≠ b1) (ha2b2 : a2 ≠ b2)
    (hdot :
      coeffDot (signedBasisDifference 1 a1 b1) (signedBasisDifference 1 a2 b2) = 1) :
    (a1 = a2 ∧ b1 ≠ b2) ∨ (b1 = b2 ∧ a1 ≠ a2) := by
  rw [show signedBasisDifference 1 a1 b1 = basisVector b1 - basisVector a1 by
    ext j
    simp [signedBasisDifference]] at hdot
  rw [show signedBasisDifference 1 a2 b2 = basisVector b2 - basisVector a2 by
    ext j
    simp [signedBasisDifference]] at hdot
  rw [coeffDot_basis_difference_basis_difference] at hdot
  if haa : a1 = a2 then
    apply Or.inl
    refine And.intro haa ?_
    intro hbb
    subst haa
    subst hbb
    have hb1a1 : b1 ≠ a1 := by
      intro h
      exact ha1b1 h.symm
    have h' := hdot
    simp [ha1b1, hb1a1] at h'
    exact h'
  else
    if hbb : b1 = b2 then
      exact Or.inr <| And.intro hbb haa
    else
      exfalso
      have hb2a2 : b2 ≠ a2 := by
        intro h
        exact ha2b2 h.symm
      if hba : b1 = a2 then
        if hab : a1 = b2 then
          have h' := hdot
          simp [hba, hab, ha2b2, hb2a2] at h'
          norm_num at h'
        else
          have h' := hdot
          simp [haa, hba, hab, ha2b2] at h'
          norm_num at h'
      else
        if hab : a1 = b2 then
          have h' := hdot
          simp [hbb, hba, hab, hb2a2] at h'
          norm_num at h'
        else
          have h' := hdot
          simp [hbb, hba, hab] at h'
          exact haa h'

lemma coeff_shared_base_of_coeffDot_eq_one
    {J : Type*} [Fintype J] [DecidableEq J]
    (d : J → Nat) (v1 v2 : CoeffVector J)
    (hpos : ∀ j, 0 < d j)
    (hNorm1 : coeffSqNorm v1 = 2) (hNorm2 : coeffSqNorm v2 = 2)
    (hDeg1 : coeffDegree d v1 = 0) (hDeg2 : coeffDegree d v2 = 0)
    (hDot : coeffDot v1 v2 = 1) :
    ∃ eps : Int, IsSignInt eps ∧ ∃ a b c : J,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      v1 = signedBasisDifference eps a b ∧
      v2 = signedBasisDifference eps a c := by
  rcases coeff_normTwo_degreeZero_classification_eps_one d v1 hpos hNorm1 hDeg1 with
    ⟨a1, b1, ha1b1, hv1⟩;
  rcases coeff_normTwo_degreeZero_classification_eps_one d v2 hpos hNorm2 hDeg2 with
    ⟨a2, b2, ha2b2, hv2⟩;
  have hDot' : coeffDot (signedBasisDifference 1 a1 b1) (signedBasisDifference 1 a2 b2) = 1 := by
    simpa [hv1, hv2] using hDot
  have hcases := coeffDot_eq_one_of_basisDifferences_cases ha1b1 ha2b2 hDot'
  cases hcases with
  | inl hleft =>
    rcases hleft with ⟨haa, hb⟩;
    refine Exists.intro 1 ?_
    refine And.intro (Or.inl rfl) ?_
    refine Exists.intro a1 ?_
    refine Exists.intro b1 ?_
    refine Exists.intro b2 ?_
    refine And.intro ha1b1 ?_
    refine And.intro
      (by
        rw [haa]
        exact ha2b2)
      ?_
    refine And.intro hb ?_
    refine And.intro hv1 ?_
    rw [haa]
    exact hv2
  | inr hright =>
    rcases hright with ⟨hbb, ha⟩;
    refine Exists.intro (-1) ?_
    refine And.intro (Or.inr rfl) ?_
    refine Exists.intro b1 ?_
    refine Exists.intro a1 ?_
    refine Exists.intro a2 ?_
    refine And.intro
      (by
        intro h
        exact ha1b1 h.symm)
      ?_
    refine And.intro
      (by
        intro h
        exact ha2b2 (h.symm.trans hbb))
      ?_
    refine And.intro ha ?_
    refine And.intro
      (by
        rw [hv1, signedBasisDifference_neg_eq_swap])
      (by
        rw [hv2, hbb, signedBasisDifference_neg_eq_swap])

lemma coeff_normTwo_degreeZero_classification_eps_one_clean
    {J : Type*} [Fintype J] [DecidableEq J]
    (d : J → Nat) (v : CoeffVector J)
    (hpos : ∀ j, 0 < d j)
    (hnorm : coeffSqNorm v = 2)
    (hdeg : coeffDegree d v = 0) :
    ∃ a b : J, a ≠ b ∧ v = signedBasisDifference 1 a b := by
  rcases coeff_normTwo_degreeZero_classification d v hpos hnorm hdeg with
    ⟨eps, heps, a, b, hab, hv⟩
  exact
    match heps with
    | Or.inl h1 => by
        subst h1
        exact ⟨a, b, hab, hv⟩
    | Or.inr hneg1 => by
        subst hneg1
        refine ⟨b, a, ?_, ?_⟩
        · intro h
          exact hab h.symm
        · calc
            v = signedBasisDifference (-1) a b := hv
            _ = signedBasisDifference 1 b a := signedBasisDifference_neg_eq_swap a b

lemma coeffDot_eq_one_of_basisDifferences_cases_clean
    {J : Type*} [Fintype J] [DecidableEq J]
    {a1 b1 a2 b2 : J}
    (ha1b1 : a1 ≠ b1) (ha2b2 : a2 ≠ b2)
    (hdot :
      coeffDot (signedBasisDifference 1 a1 b1) (signedBasisDifference 1 a2 b2) = 1) :
    (a1 = a2 ∧ b1 ≠ b2) ∨ (b1 = b2 ∧ a1 ≠ a2) := by
  rw [show signedBasisDifference 1 a1 b1 = basisVector b1 - basisVector a1 by
    ext j
    simp [signedBasisDifference]] at hdot
  rw [show signedBasisDifference 1 a2 b2 = basisVector b2 - basisVector a2 by
    ext j
    simp [signedBasisDifference]] at hdot
  rw [coeffDot_basis_difference_basis_difference] at hdot
  exact
    dite (a1 = a2)
      (fun haa =>
        Or.inl <| And.intro haa <| by
          intro hbb
          subst haa
          subst hbb
          have hb1a1 : b1 ≠ a1 := by
            intro h
            exact ha1b1 h.symm
          have h' := hdot
          simp [ha1b1, hb1a1] at h'
          norm_num at h')
      (fun haa =>
        dite (b1 = b2)
          (fun hbb => Or.inr <| And.intro hbb haa)
          (fun hbb =>
            dite (b1 = a2)
              (fun hba =>
                dite (a1 = b2)
                  (fun hab =>
                    False.elim <| by
                      have hb2a2 : b2 ≠ a2 := by
                        intro h
                        exact ha2b2 h.symm
                      have h' := hdot
                      simp [hba, hab, ha2b2, hb2a2] at h'
                      norm_num at h')
                  (fun hab =>
                    False.elim <| by
                      have h' := hdot
                      simp [haa, hba, hab, ha2b2] at h'
                      norm_num at h'))
              (fun hba =>
                dite (a1 = b2)
                  (fun hab =>
                    False.elim <| by
                      have hb2a2 : b2 ≠ a2 := by
                        intro h
                        exact ha2b2 h.symm
                      have h' := hdot
                      simp [hbb, hba, hab, hb2a2] at h'
                      norm_num at h')
                  (fun hab =>
                    False.elim <| by
                      have h' := hdot
                      simp [hbb, hba, hab] at h'
                      exact haa h'))))

lemma coeff_shared_base_of_coeffDot_eq_one_clean
    {J : Type*} [Fintype J] [DecidableEq J]
    (d : J → Nat) (v1 v2 : CoeffVector J)
    (hpos : ∀ j, 0 < d j)
    (hNorm1 : coeffSqNorm v1 = 2) (hNorm2 : coeffSqNorm v2 = 2)
    (hDeg1 : coeffDegree d v1 = 0) (hDeg2 : coeffDegree d v2 = 0)
    (hDot : coeffDot v1 v2 = 1) :
    ∃ eps : Int, IsSignInt eps ∧ ∃ a b c : J,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      v1 = signedBasisDifference eps a b ∧
      v2 = signedBasisDifference eps a c := by
  rcases coeff_normTwo_degreeZero_classification_eps_one_clean d v1 hpos hNorm1 hDeg1 with
    ⟨a1, b1, ha1b1, hv1⟩
  rcases coeff_normTwo_degreeZero_classification_eps_one_clean d v2 hpos hNorm2 hDeg2 with
    ⟨a2, b2, ha2b2, hv2⟩
  have hDot' : coeffDot (signedBasisDifference 1 a1 b1) (signedBasisDifference 1 a2 b2) = 1 := by
    simpa [hv1, hv2] using hDot
  exact match coeffDot_eq_one_of_basisDifferences_cases_clean ha1b1 ha2b2 hDot' with
  | Or.inl hleft =>
      match hleft with
      | And.intro haa hb =>
          Exists.intro 1 <|
            And.intro (Or.inl rfl) <|
              Exists.intro a1 <|
                Exists.intro b1 <|
                  Exists.intro b2 <|
                    And.intro ha1b1 <|
                      And.intro
                        (by
                          rw [haa]
                          exact ha2b2)
                        <|
                        And.intro hb <|
                          And.intro hv1 <|
                            by
                              rw [haa]
                              exact hv2
  | Or.inr hright =>
      match hright with
      | And.intro hbb ha =>
          Exists.intro (-1) <|
            And.intro (Or.inr rfl) <|
              Exists.intro b1 <|
                Exists.intro a1 <|
                  Exists.intro a2 <|
                    And.intro
                      (by
                        intro h
                        exact ha1b1 h.symm)
                      <|
                      And.intro
                        (by
                          intro h
                          exact ha2b2 (h.symm.trans hbb))
                        <|
                        And.intro ha <|
                          And.intro
                            (by
                              rw [hv1, signedBasisDifference_neg_eq_swap])
                            (by
                              rw [hv2, hbb, signedBasisDifference_neg_eq_swap])

-/

lemma coeff_normTwo_degreeZero_classification_eps_one_stable
    {J : Type*} [Fintype J] [DecidableEq J]
    (d : J → Nat) (v : CoeffVector J)
    (hpos : ∀ j, 0 < d j)
    (hnorm : coeffSqNorm v = 2)
    (hdeg : coeffDegree d v = 0) :
    ∃ a b : J, a ≠ b ∧ v = signedBasisDifference 1 a b := by
  rcases coeff_normTwo_degreeZero_classification d v hpos hnorm hdeg with
    ⟨eps, heps, a, b, hab, hv⟩
  rcases heps with rfl | rfl
  · exact ⟨a, b, hab, hv⟩
  · refine ⟨b, a, ?_, ?_⟩
    · intro h
      exact hab h.symm
    · calc
        v = signedBasisDifference (-1) a b := hv
        _ = signedBasisDifference 1 b a := signedBasisDifference_neg_eq_swap a b

lemma coeffDot_eq_one_of_basisDifferences_cases_stable
    {J : Type*} [Fintype J] [DecidableEq J]
    {a1 b1 a2 b2 : J}
    (ha1b1 : a1 ≠ b1) (ha2b2 : a2 ≠ b2)
    (hdot :
      coeffDot (signedBasisDifference 1 a1 b1) (signedBasisDifference 1 a2 b2) = 1) :
    (a1 = a2 ∧ b1 ≠ b2) ∨ (b1 = b2 ∧ a1 ≠ a2) := by
  rw [show signedBasisDifference 1 a1 b1 = basisVector b1 - basisVector a1 by
    ext j
    simp [signedBasisDifference]] at hdot
  rw [show signedBasisDifference 1 a2 b2 = basisVector b2 - basisVector a2 by
    ext j
    simp [signedBasisDifference]] at hdot
  rw [coeffDot_basis_difference_basis_difference] at hdot
  by_cases haa : a1 = a2
  · left
    refine ⟨haa, ?_⟩
    intro hbb
    subst haa
    subst hbb
    have hb1a1 : b1 ≠ a1 := by
      intro h
      exact ha1b1 h.symm
    have h' := hdot
    simp [ha1b1, hb1a1] at h'
  · right
    by_cases hbb : b1 = b2
    · exact ⟨hbb, haa⟩
    · exfalso
      have hb2a2 : b2 ≠ a2 := by
        intro h
        exact ha2b2 h.symm
      by_cases hba : b1 = a2
      · by_cases hab : a1 = b2
        · have h' := hdot
          simp [hba, hab, ha2b2, hb2a2] at h'
        · have h' := hdot
          simp [haa, hba, hab, ha2b2] at h'
      · by_cases hab : a1 = b2
        · have h' := hdot
          simp [hbb, hba, hab, hb2a2] at h'
        · have h' := hdot
          simp [hbb, hba, hab] at h'
          exact haa h'

lemma coeff_shared_base_of_coeffDot_eq_one_stable
    {J : Type*} [Fintype J] [DecidableEq J]
    (d : J → Nat) (v1 v2 : CoeffVector J)
    (hpos : ∀ j, 0 < d j)
    (hNorm1 : coeffSqNorm v1 = 2) (hNorm2 : coeffSqNorm v2 = 2)
    (hDeg1 : coeffDegree d v1 = 0) (hDeg2 : coeffDegree d v2 = 0)
    (hDot : coeffDot v1 v2 = 1) :
    ∃ eps : Int, IsSignInt eps ∧ ∃ a b c : J,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      v1 = signedBasisDifference eps a b ∧
      v2 = signedBasisDifference eps a c := by
  rcases coeff_normTwo_degreeZero_classification_eps_one_stable d v1 hpos hNorm1 hDeg1 with
    ⟨a1, b1, ha1b1, hv1⟩
  rcases coeff_normTwo_degreeZero_classification_eps_one_stable d v2 hpos hNorm2 hDeg2 with
    ⟨a2, b2, ha2b2, hv2⟩
  have hDot' : coeffDot (signedBasisDifference 1 a1 b1) (signedBasisDifference 1 a2 b2) = 1 := by
    simpa [hv1, hv2] using hDot
  rcases coeffDot_eq_one_of_basisDifferences_cases_stable ha1b1 ha2b2 hDot' with
    ⟨haa, hb⟩ | ⟨hbb, ha⟩
  · refine ⟨1, Or.inl rfl, a1, b1, b2, ha1b1, ?_, hb, hv1, ?_⟩
    · rw [haa]
      exact ha2b2
    · rw [haa]
      exact hv2
  · refine ⟨-1, Or.inr rfl, b1, a1, a2, ?_, ?_, ha, ?_, ?_⟩
    · intro h
      exact ha1b1 h.symm
    · intro h
      exact ha2b2 (h.symm.trans hbb)
    · rw [hv1, signedBasisDifference_neg_eq_swap]
    · rw [hv2, hbb, signedBasisDifference_neg_eq_swap]


lemma coeffDot_eq_one_of_basisDifferences_cases
    {J : Type*} [Fintype J] [DecidableEq J]
    {a1 b1 a2 b2 : J}
    (ha1b1 : a1 ≠ b1) (ha2b2 : a2 ≠ b2)
    (hdot :
      coeffDot (signedBasisDifference 1 a1 b1) (signedBasisDifference 1 a2 b2) = 1) :
    (a1 = a2 ∧ b1 ≠ b2) ∨ (b1 = b2 ∧ a1 ≠ a2) := by
  simpa using coeffDot_eq_one_of_basisDifferences_cases_stable ha1b1 ha2b2 hdot

lemma coeff_shared_base_of_coeffDot_eq_one
    {J : Type*} [Fintype J] [DecidableEq J]
    (d : J → Nat) (v1 v2 : CoeffVector J)
    (hpos : ∀ j, 0 < d j)
    (hNorm1 : coeffSqNorm v1 = 2) (hNorm2 : coeffSqNorm v2 = 2)
    (hDeg1 : coeffDegree d v1 = 0) (hDeg2 : coeffDegree d v2 = 0)
    (hDot : coeffDot v1 v2 = 1) :
    ∃ eps : Int, IsSignInt eps ∧ ∃ a b c : J,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      v1 = signedBasisDifference eps a b ∧
      v2 = signedBasisDifference eps a c := by
  simpa using coeff_shared_base_of_coeffDot_eq_one_stable d v1 v2 hpos hNorm1 hNorm2 hDeg1 hDeg2 hDot

/-! ### Coefficient-model packages matching the book-level node shapes

These package the honest coefficient-space results in the same logical shape as
the abstract book-level nodes. The remaining blocker is to construct a bridge
from `ClassFunction G` data to this coefficient model. -/


public theorem coeffDot_self_eq_coeffSqNorm
    {J : Type*} [Fintype J] [DecidableEq J] (v : CoeffVector J) :
    ((coeffSqNorm v : Nat) : Int) = coeffDot v v := by
  unfold coeffSqNorm coeffDot coeffSupport
  rw [Finset.sum_filter]
  calc
    ((∑ j : J, if v j ≠ 0 then (Int.natAbs (v j)) ^ 2 else 0 : Nat) : Int)
        = ∑ j : J, if v j ≠ 0 then (((Int.natAbs (v j)) ^ 2 : Nat) : Int) else 0 := by
            rw [Nat.cast_sum]
            refine Finset.sum_congr rfl ?_
            intro j hj
            by_cases h : v j ≠ 0 <;> simp [h]
    _ = ∑ j : J, if v j ≠ 0 then v j * v j else 0 := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          by_cases h : v j ≠ 0
          · rw [if_pos h, if_pos h, pow_two, Int.natAbs_mul_self]
          · rw [if_neg h, if_neg h]
    _ = ∑ j : J, v j * v j := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          by_cases h : v j ≠ 0
          · rw [if_pos h]
          · rw [if_neg h]
            simp at h
            simp [h]

@[expose] public def signIntToComplex (eps : Int) : ℂ := (eps : ℂ)

@[simp] lemma signedBasisDifference_self
    {J : Type*} [DecidableEq J] (eps : Int) (j : J) :
    signedBasisDifference eps j j = 0 := by
  ext k
  simp [signedBasisDifference]

@[simp] lemma evalCoeff_zero
    {G J : Type*} [Fintype J] (mu : J → ClassFunction G) :
    evalCoeff mu 0 = 0 := by
  ext g
  simp [evalCoeff]

public theorem evalCoeff_signedBasisDifference
    {G J : Type*} [Fintype J] [DecidableEq J]
    (mu : J → ClassFunction G) (eps : Int) (a b : J) :
    evalCoeff mu (signedBasisDifference eps a b) =
      signIntToComplex eps • (mu b - mu a) := by
  ext g
  classical
  by_cases hab : a = b
  · subst hab
    simp [evalCoeff, signedBasisDifference, signIntToComplex]
  · have hba : b ≠ a := by
      intro h
      exact hab h.symm
    simp [evalCoeff, signedBasisDifference, basisVector, signIntToComplex,
      sub_eq_add_neg, mul_add, Finset.sum_add_distrib, mul_comm]

public theorem isSign_of_isSignInt {eps : Int} (heps : IsSignInt eps) :
    IsSign (signIntToComplex eps) := by
  rcases heps with rfl | rfl <;> simp [signIntToComplex, IsSign]

lemma coeff_extend_from_two_reference_differences
    {J : Type*} [Fintype J] [DecidableEq J]
    (d : J → Nat) (v : CoeffVector J)
    (hpos : ∀ j, 0 < d j)
    {eps : Int} {a b c : J}
    (heps : IsSignInt eps)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hDeg1 : coeffDegree d (signedBasisDifference eps a b) = 0)
    (hNorm : coeffSqNorm v = 2)
    (hDeg : coeffDegree d v = 0)
    (hCross1 : coeffDot (signedBasisDifference eps a b) v = 1)
    (hCross2 : coeffDot (signedBasisDifference eps a c) v = 1) :
    ∃ q : J, a ≠ q ∧ b ≠ q ∧ c ≠ q ∧
      v = signedBasisDifference eps a q := by
  have hNorm1 : coeffSqNorm (signedBasisDifference eps a b) = 2 :=
    coeffSqNorm_signedBasisDifference eps heps hab
  rcases coeff_shared_base_of_coeffDot_eq_one d
      (signedBasisDifference eps a b) v hpos hNorm1 hNorm hDeg1 hDeg hCross1 with
    ⟨eps1, heps1, a1, b1, q, ha1b1, ha1q, hb1q, hv1, hv⟩
  have hcmp :
      (eps = eps1 ∧ a = a1 ∧ b = b1) ∨
        (eps = -eps1 ∧ a = b1 ∧ b = a1) :=
    signedBasisDifference_eq_cases heps heps1 hab ha1b1 hv1
  rcases hcmp with ⟨heqeps, haa, hbb⟩ | ⟨heqeps, hab1, hba1⟩
  · subst heqeps
    subst haa
    subst hbb
    refine ⟨q, ha1q, hb1q, ?_, hv⟩
    intro hcq
    have hdot_self :
        coeffDot (signedBasisDifference eps a c) (signedBasisDifference eps a c) = 2 := by
      have hsq : coeffSqNorm (signedBasisDifference eps a c) = 2 :=
        coeffSqNorm_signedBasisDifference eps heps hac
      rw [← coeffDot_self_eq_coeffSqNorm, hsq]
      norm_num
    have hc : (1 : Int) = 2 := by
      calc
        (1 : Int) = coeffDot (signedBasisDifference eps a c) v := hCross2.symm
        _ = coeffDot (signedBasisDifference eps a c)
            (signedBasisDifference eps a c) := by rw [hv, hcq]
        _ = 2 := hdot_self
    omega
  · have hqnea : q ≠ a := by
      intro hqa
      have : b1 = q := by simpa [hab1] using hqa.symm
      exact hb1q this
    have hqneb : q ≠ b := by
      intro hqb
      have : a1 = q := by simpa [hba1] using hqb.symm
      exact ha1q this
    have hvAlt : v = signedBasisDifference eps q b := by
      have heqeps' : eps1 = -eps := by omega
      calc
        v = signedBasisDifference eps1 a1 q := hv
        _ = signedBasisDifference (-eps) b q := by rw [heqeps', ← hba1]
        _ = signedBasisDifference eps q b := signedBasisDifference_neg_sign_swap heps b q
    have hdot :
        coeffDot (signedBasisDifference eps a c) (signedBasisDifference eps q b) = 1 := by
      simpa [hvAlt] using hCross2
    rcases heps with rfl | rfl
    · have hcases := coeffDot_eq_one_of_basisDifferences_cases hac hqneb hdot
      rcases hcases with ⟨haq, hcb⟩ | ⟨hbc', haq⟩
      · exact (hqnea haq.symm).elim
      · exact (hbc hbc'.symm).elim
    · have hdot' :
          coeffDot (signedBasisDifference 1 c a) (signedBasisDifference 1 b q) = 1 := by
        simpa [signedBasisDifference_neg_eq_swap] using hdot
      have hbq : b ≠ q := by
        intro h
        exact hqneb h.symm
      have hcases := coeffDot_eq_one_of_basisDifferences_cases hac.symm hbq hdot'
      rcases hcases with ⟨hca, hbq'⟩ | ⟨hbq', hca⟩
      · exact (hbc hca.symm).elim
      · exact (hqnea hbq'.symm).elim

lemma proposition_1_4_coeff_lattice_base_two
    {J : Type*} [Fintype J] [DecidableEq J]
    (d : J → Nat) (hpos : ∀ j, 0 < d j)
    (v : Fin 2 → CoeffVector J)
    (hzero : v 0 = 0)
    (hDeg : ∀ i : Fin 2, coeffDegree d (v i) = 0)
    (hNorm : ∀ i : Fin 2, i ≠ 0 → coeffSqNorm (v i) = 2) :
    ∃ eps : Int, IsSignInt eps ∧
      ∃ nu : Fin 2 → J,
        Pairwise (fun i j => nu i ≠ nu j) ∧
        ∀ i : Fin 2, v i = signedBasisDifference eps (nu 0) (nu i) := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  rcases coeff_normTwo_degreeZero_classification d (v 1) hpos
      (hNorm 1 h10) (hDeg 1) with
    ⟨eps, heps, a, b, hab, hv1⟩
  let nu : Fin 2 → J := fun i => if i = 0 then a else b
  refine ⟨eps, heps, nu, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · contradiction
    · simpa [nu] using hab
    · simpa [nu] using fun h => hab h.symm
    · contradiction
  · intro i
    fin_cases i
    · simp [nu, hzero]
    · simpa [nu, h10] using hv1


theorem proposition_1_4_coeff_lattice_three_plus
    {J : Type*} [Fintype J] [DecidableEq J]
    {n : ℕ}
    (d : J → Nat) (hpos : ∀ j, 0 < d j)
    (v : Fin (n + 3) → CoeffVector J)
    (hzero : v 0 = 0)
    (hDeg : ∀ i : Fin (n + 3), coeffDegree d (v i) = 0)
    (hNorm : ∀ i : Fin (n + 3), i ≠ 0 → coeffSqNorm (v i) = 2)
    (hCross : ∀ i j : Fin (n + 3), i ≠ 0 → j ≠ 0 → i ≠ j →
      coeffDot (v i) (v j) = 1) :
    ∃ eps : Int, IsSignInt eps ∧
      ∃ nu : Fin (n + 3) → J,
        Pairwise (fun i j => nu i ≠ nu j) ∧
        ∀ i : Fin (n + 3), v i = signedBasisDifference eps (nu 0) (nu i) := by
  have h10 : (1 : Fin (n + 3)) ≠ 0 := by norm_num
  have h20 : (2 : Fin (n + 3)) ≠ 0 := by
    intro h
    have hval : (2 : Nat) % (n + 3) = 2 := Nat.mod_eq_of_lt (by omega)
    have hzero' : (2 : Nat) % (n + 3) = 0 := by
      simpa using congrArg Fin.val h
    rw [hval] at hzero'
    norm_num at hzero'
  have h12 : (1 : Fin (n + 3)) ≠ 2 := by
    intro h
    have hval2 : (2 : Nat) % (n + 3) = 2 := Nat.mod_eq_of_lt (by omega)
    have hc := congrArg Fin.val h
    simp [hval2] at hc
  have h21 : (2 : Fin (n + 3)) ≠ 1 := by
    intro h
    exact h12 h.symm
  rcases coeff_shared_base_of_coeffDot_eq_one d (v 1) (v 2) hpos
      (hNorm 1 h10) (hNorm 2 h20) (hDeg 1) (hDeg 2)
      (hCross 1 2 h10 h20 h12) with
    ⟨eps, heps, a, b, c, hab, hac, hbc, hv1, hv2⟩
  let nu : Fin (n + 3) → J := fun i =>
    if h0 : i = 0 then a else
    if h1 : i = 1 then b else
    if h2 : i = 2 then c else
      Classical.choose (coeff_extend_from_two_reference_differences d (v i) hpos
        heps hab hac hbc (by rw [← hv1]; exact hDeg 1)
        (hNorm i h0) (hDeg i)
        (by simpa [hv1] using hCross 1 i h10 h0 (by intro h; exact h1 h.symm))
        (by simpa [hv2] using hCross 2 i h20 h0 (by intro h; exact h2 h.symm)))
  have hnu_spec :
      ∀ {i : Fin (n + 3)} (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ 2),
        a ≠ nu i ∧ b ≠ nu i ∧ c ≠ nu i ∧
          v i = signedBasisDifference eps a (nu i) := by
    intro i hi0 hi1 hi2
    dsimp [nu]
    simp [hi0, hi1, hi2]
    exact Classical.choose_spec
      (coeff_extend_from_two_reference_differences d (v i) hpos
        heps hab hac hbc (by rw [← hv1]; exact hDeg 1)
        (hNorm i hi0) (hDeg i)
        (by simpa [hv1] using hCross 1 i h10 hi0 (by intro h; exact hi1 h.symm))
        (by simpa [hv2] using hCross 2 i h20 hi0 (by intro h; exact hi2 h.symm)))
  refine ⟨eps, heps, nu, ?_, ?_⟩
  · intro i j hij
    by_cases hi0 : i = 0
    · subst hi0
      by_cases hj1 : j = 1
      · subst hj1
        simpa [nu] using hab
      by_cases hj2 : j = 2
      · subst hj2
        simpa [nu, h20, h21] using hac
      have hj0 : j ≠ 0 := by simpa using hij.symm
      have hspec := hnu_spec hj0 hj1 hj2
      simpa [nu, hj0, hj1, hj2] using hspec.1
    by_cases hi1 : i = 1
    · subst hi1
      by_cases hj0 : j = 0
      · subst hj0
        simpa [nu] using hab.symm
      by_cases hj2 : j = 2
      · subst hj2
        simpa [nu, h20, h21] using hbc
      have hj1 : j ≠ 1 := by
        intro h
        exact hij h.symm
      have hspec := hnu_spec hj0 hj1 hj2
      simpa [nu, hj0, hj1, hj2] using hspec.2.1
    by_cases hi2 : i = 2
    · subst hi2
      by_cases hj0 : j = 0
      · subst hj0
        simpa [nu, h20, h21] using hac.symm
      by_cases hj1 : j = 1
      · subst hj1
        simpa [nu, h20, h21] using hbc.symm
      have hj2 : j ≠ 2 := by
        intro h
        exact hij h.symm
      have hspec := hnu_spec hj0 hj1 hj2
      simpa [nu, h20, h21, hj0, hj1, hj2] using hspec.2.2.1
    by_cases hj0 : j = 0
    · have hspec := hnu_spec hi0 hi1 hi2
      subst hj0
      simpa [nu, hi0, hi1, hi2] using hspec.1.symm
    by_cases hj1 : j = 1
    · have hspec := hnu_spec hi0 hi1 hi2
      subst hj1
      simpa [nu, hi0, hi1, hi2] using hspec.2.1.symm
    by_cases hj2 : j = 2
    · have hspec := hnu_spec hi0 hi1 hi2
      subst hj2
      simpa [nu, h20, h21, hi0, hi1, hi2] using hspec.2.2.1.symm
    have hspeci := hnu_spec hi0 hi1 hi2
    have hspecj := hnu_spec hj0 hj1 hj2
    intro hnu
    have hSame : v i = v j := by
      rw [hspeci.2.2.2, hspecj.2.2.2, hnu]
    have hc : (1 : Int) = 2 := by
      calc
        (1 : Int) = coeffDot (v i) (v j) := (hCross i j hi0 hj0 hij).symm
        _ = coeffDot (v i) (v i) := by rw [hSame]
        _ = 2 := by
            rw [← coeffDot_self_eq_coeffSqNorm, hNorm i hi0]
            norm_num
    omega
  · intro i
    by_cases hi0 : i = 0
    · subst hi0
      simp [nu, hzero]
    by_cases hi1 : i = 1
    · subst hi1
      simpa [nu, h10] using hv1
    by_cases hi2 : i = 2
    · subst hi2
      simpa [nu, h20, h21] using hv2
    have hspec := hnu_spec hi0 hi1 hi2
    simpa [nu, hi0, hi1, hi2] using hspec.2.2.2

public theorem proposition_1_4_coeff_lattice
    {J : Type*} [Fintype J] [DecidableEq J]
    {n : ℕ} [NeZero n]
    (_hn : 2 ≤ n)
    (d : J → Nat) (hpos : ∀ j, 0 < d j)
    (v : Fin n → CoeffVector J)
    (hzero : v 0 = 0)
    (hDeg : ∀ i : Fin n, coeffDegree d (v i) = 0)
    (hNorm : ∀ i : Fin n, i ≠ 0 → coeffSqNorm (v i) = 2)
    (hCross : ∀ i j : Fin n, i ≠ 0 → j ≠ 0 → i ≠ j →
      coeffDot (v i) (v j) = 1) :
    ∃ eps : Int, IsSignInt eps ∧
      ∃ nu : Fin n → J,
        Pairwise (fun i j => nu i ≠ nu j) ∧
        ∀ i : Fin n, v i = signedBasisDifference eps (nu 0) (nu i) := by
  cases n with
  | zero =>
      omega
  | succ n =>
      cases n with
      | zero =>
          omega
      | succ m =>
          cases m with
          | zero =>
              simpa using proposition_1_4_coeff_lattice_base_two d hpos v hzero hDeg hNorm
          | succ k =>
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                proposition_1_4_coeff_lattice_three_plus
                  (n := k) d hpos v hzero hDeg hNorm hCross


namespace CoeffCharacterModel

variable {G J : Type*} [Finite G] [One G] [Fintype J] [DecidableEq J]


end CoeffCharacterModel

/-! ## Proof nodes for Proposition (1.4) -/

private lemma scalarProduct_add_left
    {H : Type*} [Finite H] (phi1 phi2 psi : ClassFunction H) :
    scalarProduct H (phi1 + phi2) psi =
      scalarProduct H phi1 psi + scalarProduct H phi2 psi := by
  simp [scalarProduct, mul_add, Finset.sum_add_distrib, right_distrib]

private lemma scalarProduct_smul_left
    {H : Type*} [Finite H] (z : ℂ) (phi psi : ClassFunction H) :
    scalarProduct H (z • phi) psi = z * scalarProduct H phi psi := by
  calc
    scalarProduct H (z • phi) psi
        = (Nat.card H : ℂ)⁻¹ * ∑ g : H, z * (phi g * star (psi g)) := by
            simp [scalarProduct, mul_assoc]
    _ = (Nat.card H : ℂ)⁻¹ * (z * ∑ g : H, phi g * star (psi g)) := by
          rw [← Finset.mul_sum]
    _ = z * scalarProduct H phi psi := by
          simp [scalarProduct, mul_left_comm]

private lemma scalarProduct_add_right
    {H : Type*} [Finite H] (phi psi1 psi2 : ClassFunction H) :
    scalarProduct H phi (psi1 + psi2) =
      scalarProduct H phi psi1 + scalarProduct H phi psi2 := by
  simp [scalarProduct, mul_add, Finset.sum_add_distrib]

private lemma scalarProduct_smul_right
    {H : Type*} [Finite H] (z : ℂ) (phi psi : ClassFunction H) :
    scalarProduct H phi (z • psi) = scalarProduct H phi psi * star z := by
  calc
    scalarProduct H phi (z • psi)
        = (Nat.card H : ℂ)⁻¹ * ∑ g : H, (phi g * star (psi g)) * star z := by
            unfold scalarProduct
            congr 1
            refine Finset.sum_congr rfl ?_
            intro g hg
            simp [mul_left_comm, mul_comm]
    _ = (Nat.card H : ℂ)⁻¹ * ((∑ g : H, phi g * star (psi g)) * star z) := by
          rw [Finset.sum_mul]
    _ = scalarProduct H phi psi * star z := by
          simp [scalarProduct, mul_left_comm, mul_comm]

private lemma scalarProduct_sub_right
    {H : Type*} [Finite H] (phi psi1 psi2 : ClassFunction H) :
    scalarProduct H phi (psi1 - psi2) =
      scalarProduct H phi psi1 - scalarProduct H phi psi2 := by
  calc
    scalarProduct H phi (psi1 - psi2)
        = scalarProduct H phi (psi1 + (-1 : ℂ) • psi2) := by
            congr 1
            ext g
            simp [sub_eq_add_neg]
    _ = scalarProduct H phi psi1 + scalarProduct H phi ((-1 : ℂ) • psi2) := by
          rw [scalarProduct_add_right]
    _ = scalarProduct H phi psi1 - scalarProduct H phi psi2 := by
          rw [scalarProduct_smul_right]
          simp [sub_eq_add_neg]

lemma scalarProduct_sub_left
    {H : Type*} [Finite H] (phi1 phi2 psi : ClassFunction H) :
    scalarProduct H (phi1 - phi2) psi =
      scalarProduct H phi1 psi - scalarProduct H phi2 psi := by
  calc
    scalarProduct H (phi1 - phi2) psi
        = scalarProduct H (phi1 + (-1 : ℂ) • phi2) psi := by
            congr 1
            ext g
            simp [sub_eq_add_neg]
    _ = scalarProduct H phi1 psi + scalarProduct H ((-1 : ℂ) • phi2) psi := by
          rw [scalarProduct_add_left]
    _ = scalarProduct H phi1 psi - scalarProduct H phi2 psi := by
          rw [scalarProduct_smul_left]
          simp [sub_eq_add_neg]


lemma difference_scalar_eq_one_of_ne
    {H I : Type*} [Finite H] [DecidableEq I]
    (chi : I → ClassFunction H) (base i j : I)
    (hOrtho : IsOrthonormalFamily chi)
    (hib : i ≠ base) (hjb : j ≠ base) (hij : i ≠ j) :
    scalarProduct H (chi i - chi base) (chi j - chi base) = 1 := by
  have hij0 : scalarProduct H (chi i) (chi j) = 0 := by
    simpa [IsOrthonormalFamily, hij] using hOrtho i j
  have hib0 : scalarProduct H (chi i) (chi base) = 0 := by
    simpa [IsOrthonormalFamily, hib] using hOrtho i base
  have hbj0 : scalarProduct H (chi base) (chi j) = 0 := by
    simpa [IsOrthonormalFamily, hjb.symm] using hOrtho base j
  have hbb : scalarProduct H (chi base) (chi base) = 1 := by
    simpa [IsOrthonormalFamily] using hOrtho base base
  calc
    scalarProduct H (chi i - chi base) (chi j - chi base)
        = scalarProduct H (chi i) (chi j - chi base) -
            scalarProduct H (chi base) (chi j - chi base) := by
              rw [scalarProduct_sub_left]
    _ = (scalarProduct H (chi i) (chi j) - scalarProduct H (chi i) (chi base)) -
          (scalarProduct H (chi base) (chi j) - scalarProduct H (chi base) (chi base)) := by
            rw [scalarProduct_sub_right, scalarProduct_sub_right]
    _ = 1 := by
          simp [hij0, hib0, hbj0, hbb]

lemma difference_norm_eq_two_of_ne
    {H I : Type*} [Finite H] [DecidableEq I]
    (chi : I → ClassFunction H) (base i : I)
    (hOrtho : IsOrthonormalFamily chi)
    (hib : i ≠ base) :
    scalarProduct H (chi i - chi base) (chi i - chi base) = 2 := by
  have hii : scalarProduct H (chi i) (chi i) = 1 := by
    simpa [IsOrthonormalFamily] using hOrtho i i
  have hib0 : scalarProduct H (chi i) (chi base) = 0 := by
    simpa [IsOrthonormalFamily, hib] using hOrtho i base
  have hbi0 : scalarProduct H (chi base) (chi i) = 0 := by
    simpa [IsOrthonormalFamily, hib.symm] using hOrtho base i
  have hbb : scalarProduct H (chi base) (chi base) = 1 := by
    simpa [IsOrthonormalFamily] using hOrtho base base
  calc
    scalarProduct H (chi i - chi base) (chi i - chi base)
        = scalarProduct H (chi i) (chi i - chi base) -
            scalarProduct H (chi base) (chi i - chi base) := by
              rw [scalarProduct_sub_left]
    _ = (scalarProduct H (chi i) (chi i) - scalarProduct H (chi i) (chi base)) -
          (scalarProduct H (chi base) (chi i) - scalarProduct H (chi base) (chi base)) := by
            rw [scalarProduct_sub_right, scalarProduct_sub_right]
    _ = 2 := by
          norm_num [hii, hib0, hbi0, hbb]


/--
Coefficient-vector compatibility endpoint for Peterfalvi (1.4).  Use
`proposition_1_4_source` when the hypotheses are still expressed as an
isometry of the source and target character lattices.
-/
public theorem proposition_1_4
    {G H J : Type*} [Group G] [Finite G] [Finite H]
    [Fintype J] [DecidableEq J]
    {n : ℕ} [NeZero n]
    (_hn : 2 ≤ n)
    (muBasis : J → ClassFunction G)
    (hmuBasis : IsIrreducibleCharacterBasis muBasis)
    (d : J → Nat) (hpos : ∀ j, 0 < d j)
    (chi : Fin n → ClassFunction H)
    (hOrtho : IsOrthonormalFamily chi)
    (v : Fin n → CoeffVector J)
    (hzero : v 0 = 0)
    (hDeg : ∀ i : Fin n, coeffDegree d (v i) = 0)
    (hCoeffIso : ∀ i j : Fin n,
      (coeffDot (v i) (v j) : ℂ) =
        scalarProduct H (chi i - chi 0) (chi j - chi 0))
    (T : ClassFunction H → ClassFunction G)
    (hT : ∀ i : Fin n, T (chi i - chi 0) = evalCoeff muBasis (v i)) :
    ∃ eps : ℂ, IsSign eps ∧
      ∃ mu : Fin n → ClassFunction G,
        IsIrreducibleCharacterBasis mu ∧
        ∀ i : Fin n, T (chi i - chi 0) = eps • (mu i - mu 0) := by
  have hNorm : ∀ i : Fin n, i ≠ 0 → coeffSqNorm (v i) = 2 := by
    intro i hi0
    have hdot : coeffDot (v i) (v i) = 2 := by
      have hc : ((coeffDot (v i) (v i) : Int) : ℂ) = 2 := by
        calc
          ((coeffDot (v i) (v i) : Int) : ℂ)
              = scalarProduct H (chi i - chi 0) (chi i - chi 0) := hCoeffIso i i
          _ = 2 := difference_norm_eq_two_of_ne chi 0 i hOrtho hi0
      exact_mod_cast hc
    have hs : ((coeffSqNorm (v i) : Nat) : Int) = 2 := by
      rw [coeffDot_self_eq_coeffSqNorm]
      exact hdot
    exact_mod_cast hs
  have hCross : ∀ i j : Fin n, i ≠ 0 → j ≠ 0 → i ≠ j →
      coeffDot (v i) (v j) = 1 := by
    intro i j hi0 hj0 hij
    have hc : ((coeffDot (v i) (v j) : Int) : ℂ) = 1 := by
      calc
        ((coeffDot (v i) (v j) : Int) : ℂ)
            = scalarProduct H (chi i - chi 0) (chi j - chi 0) := hCoeffIso i j
        _ = 1 := difference_scalar_eq_one_of_ne chi 0 i j hOrtho hi0 hj0 hij
    exact_mod_cast hc
  rcases proposition_1_4_coeff_lattice _hn d hpos v hzero hDeg hNorm hCross with
    ⟨eps, heps, nu, hnu_pairwise, hν⟩
  let mu : Fin n → ClassFunction G := fun i => muBasis (nu i)
  refine ⟨signIntToComplex eps, isSign_of_isSignInt heps, mu, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro i
      exact hmuBasis.1 (nu i)
    · intro i j hij
      exact hmuBasis.2 (hnu_pairwise hij)
  · intro i
    calc
      T (chi i - chi 0) = evalCoeff muBasis (v i) := hT i
      _ = evalCoeff muBasis (signedBasisDifference eps (nu 0) (nu i)) := by rw [hν i]
      _ = signIntToComplex eps • (mu i - mu 0) := by
          simp [mu, evalCoeff_signedBasisDifference]

/--
Peterfalvi (1.4), source-facing form.  The family `chi` is the indexed set
`\mathcal X ⊂ Irr(H)` with equal degrees, `T` is the isometry on the integral
difference lattice, and `muBasis` is the irreducible-character basis of `G`.

The coefficient-vector theorem `proposition_1_4` is retained for downstream
code that has already expanded the isometry into integer coefficient vectors.
-/
public theorem proposition_1_4_source
    {G H J : Type*} [Group G] [Finite G] [Group H] [Finite H]
    [Fintype J] [DecidableEq J]
    {n : ℕ} [NeZero n]
    (hn : 2 ≤ n)
    (muBasis : J → ClassFunction G)
    (hmuBasis : IsIrreducibleCharacterBasis muBasis)
    (d : J → Nat)
    (chi : Fin n → ClassFunction H)
    (_hchiBasis : IsIrreducibleCharacterBasis chi)
    (_hchiDegree : ∀ i : Fin n, degree (chi i) = degree (chi 0))
    (hOrtho : IsOrthonormalFamily chi)
    (T : ClassFunction H → ClassFunction G)
    (hT : IsIntegralIsometryOnCharacterDifferences muBasis d chi T) :
    ∃ eps : ℂ, IsSign eps ∧
      ∃ mu : Fin n → ClassFunction G,
        IsIrreducibleCharacterBasis mu ∧
        ∀ i : Fin n, T (chi i - chi 0) = eps • (mu i - mu 0) := by
  rcases hT with ⟨hdegBasis, hpos, coeff, hzero, hTdeg, hCoeffIso, hTcoeff⟩
  have hDeg : ∀ i : Fin n, coeffDegree d (coeff i) = 0 := by
    intro i
    have hdeg_eval :
        degree (evalCoeff muBasis (coeff i)) = (coeffDegree d (coeff i) : ℂ) :=
      degree_evalCoeff_eq_coeffDegree muBasis d hdegBasis (coeff i)
    have hcoeff_zero_complex : (coeffDegree d (coeff i) : ℂ) = 0 := by
      rw [← hdeg_eval, ← hTcoeff i]
      exact hTdeg i
    exact_mod_cast hcoeff_zero_complex
  exact proposition_1_4 hn muBasis hmuBasis d hpos chi hOrtho
    coeff hzero hDeg hCoeffIso T hTcoeff

end CFSG.Section1
