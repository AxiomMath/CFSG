module

public import CFSG.RankThree.Lattice.SteinbergBIE6EvenCommutant

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.E6 CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley
open CFSG.LieType.Chevalley.C2E6Std
open scoped Pointwise commutatorElement

section Psi

variable (Ω : Type) [Field Ω] [CharP Ω 2]

@[expose] def e6PsiRep (J : Set (Fin Tag.E6.rank)) : ModGL Tag.E6 Ω :=
  canonicalRep (coxeterSystem Tag.E6) Ω (e6Longest J) * canonicalRep (coxeterSystem Tag.E6) Ω e6W0

@[expose] def e6Psi (J : Set (Fin Tag.E6.rank)) (f : ℕ) : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω :=
  (MulAut.conj (e6PsiRep Ω J)).toMonoidHom.comp
    (Units.map (entrywiseHom (iterateFrobenius Ω 2 f)))

variable {Ω}

theorem E6EvenFixedRootDatum.psi_eq_e6Psi [IsAlgClosed Ω] (D : E6EvenFixedRootDatum Ω) :
    D.psi = e6Psi Ω D.J D.f :=
  rfl

theorem e6PsiRep_conj_pinnedX (J : Set (Fin Tag.E6.rank)) {γ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot Tag.E6 γ) (c : Ω) :
    e6PsiRep Ω J * pinnedX Tag.E6 Ω γ c * (e6PsiRep Ω J)⁻¹ =
      pinnedX Tag.E6 Ω (e6Delta J γ) c := by
  have h0 := E6EvenFixedRootDatum.canonicalRep_conj_pinnedX e6W0 hγ c
  have h1 := E6EvenFixedRootDatum.canonicalRep_conj_pinnedX (e6Longest J)
    (IsRoot.smul hγ e6W0) c
  calc e6PsiRep Ω J * pinnedX Tag.E6 Ω γ c * (e6PsiRep Ω J)⁻¹
      = canonicalRep (coxeterSystem Tag.E6) Ω (e6Longest J) *
          (canonicalRep (coxeterSystem Tag.E6) Ω e6W0 * pinnedX Tag.E6 Ω γ c *
            (canonicalRep (coxeterSystem Tag.E6) Ω e6W0)⁻¹) *
          (canonicalRep (coxeterSystem Tag.E6) Ω (e6Longest J))⁻¹ := by
        rw [e6PsiRep, _root_.mul_inv_rev]
        group
    _ = pinnedX Tag.E6 Ω (e6Longest J • e6W0 • γ) c := by rw [h0, h1]
    _ = pinnedX Tag.E6 Ω (e6Delta J γ) c := by
        rw [e6W0_smul, smul_neg]
        rfl

theorem e6Psi_pinnedX (J : Set (Fin Tag.E6.rank)) (f : ℕ) {γ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot Tag.E6 γ) (c : Ω) :
    e6Psi Ω J f (pinnedX Tag.E6 Ω γ c) = pinnedX Tag.E6 Ω (e6Delta J γ) (c ^ 2 ^ f) := by
  change e6PsiRep Ω J * entrywiseFrobGL Tag.E6 Ω 2 f (pinnedX Tag.E6 Ω γ c) *
    (e6PsiRep Ω J)⁻¹ = _
  rw [entrywiseFrobGL_pinnedX, e6PsiRep_conj_pinnedX J hγ, iterateFrobenius_def]

end Psi

section Quad

variable {Ω : Type} [Field Ω]

theorem pinnedCoeff_E6_three (α : Fin Tag.E6.rank → ℤ) : pinnedCoeff Tag.E6 Ω α 3 = 0 := by
  simp [pinnedCoeff, xCoeff_E6_three]

theorem pinnedX_E6_eq (α : Fin Tag.E6.rank → ℤ) (c : Ω) :
    (pinnedX Tag.E6 Ω α c : Module.End Ω (RootModule Tag.E6 Ω)) =
      1 + c • pinnedCoeff Tag.E6 Ω α 1 + c ^ 2 • pinnedCoeff Tag.E6 Ω α 2 := by
  rw [pinnedX_eq_sum, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, pinnedCoeff_zero, pinnedCoeff_E6_three, pow_zero, one_smul, pow_one,
    smul_zero, add_zero]

theorem commute_pinnedX_of_three_le_card {X : Module.End Ω (RootModule Tag.E6 Ω)}
    {α : Fin Tag.E6.rank → ℤ} {F : Finset Ω} (hF : 3 ≤ F.card)
    (h : ∀ c ∈ F, Commute X (pinnedX Tag.E6 Ω α c : Module.End Ω (RootModule Tag.E6 Ω)))
    (c : Ω) : Commute X (pinnedX Tag.E6 Ω α c : Module.End Ω (RootModule Tag.E6 Ω)) := by
  obtain ⟨hA, hB⟩ := commute_of_three_le_card hF fun c hc => by
    rw [← pinnedX_E6_eq]
    exact h c hc
  rw [pinnedX_E6_eq]
  exact commute_one_add_of_commute hA hB c

theorem exists_pow_sub_add_eq_zero [IsAlgClosed Ω] {q : ℕ} (hq : 2 ≤ q) (b : Ω) :
    ∃ c : Ω, c ^ q - c + b = 0 := by
  have hdeg : (Polynomial.X ^ q - Polynomial.X + Polynomial.C b : Polynomial Ω).natDegree = q := by
    compute_degree!
    · have h1 : (1 : ℕ) ≠ q := by omega
      have h0 : q ≠ 0 := by omega
      simp [h1, h0]
    · omega
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_root
    (Polynomial.X ^ q - Polynomial.X + Polynomial.C b : Polynomial Ω) (by
      rw [Polynomial.degree_eq_natDegree (by intro h; rw [h] at hdeg; simp at hdeg; omega), hdeg]
      exact_mod_cast (by omega : q ≠ 0))
  refine ⟨c, ?_⟩
  simpa using hc

theorem exists_finset_frobeniusFixed [CharP Ω 2] [IsAlgClosed Ω] {n : ℕ} (hn : 0 < n) :
    ∃ F : Finset Ω, F.card = 2 ^ n ∧ ∀ a, a ∈ F ↔ a ^ 2 ^ n = a := by
  have h := card_frobeniusFixedField (k := Ω) (p := 2) hn
  have hfin : ((frobeniusFixedField Ω 2 n : Subfield Ω) : Set Ω).Finite := by
    have : Finite (frobeniusFixedField Ω 2 n) := Nat.finite_of_card_ne_zero (by
      rw [h]
      positivity)
    exact Set.toFinite _
  refine ⟨hfin.toFinset, ?_, fun a => ?_⟩
  · rw [← Nat.card_eq_card_finite_toFinset hfin]
    exact h
  · rw [hfin.mem_toFinset, SetLike.mem_coe, mem_frobeniusFixedField]

end Quad

section Factor

abbrev e6Supp24 : Set (Fin Tag.E6.rank) :=
  e6QpSupport 12

@[expose] def e6Q24 (Ω : Type) [Field Ω] : Subgroup (ModGL Tag.E6 Ω) :=
  rootSpan Tag.E6 Ω (parabolicRoots Tag.E6 e6Supp24)

@[expose] def e6P24 (Ω : Type) [Field Ω] [CharP Ω 2] (J : Set (Fin Tag.E6.rank)) (f : ℕ) :
    Subgroup (ModGL Tag.E6 Ω) :=
  e6Q24 Ω ⊓ (e6Psi Ω J f).eqLocus (MonoidHom.id _)

abbrev e6ε : Fin Tag.E6.rank → ℤ :=
  Pi.single 1 1

abbrev e6ε' : Fin Tag.E6.rank → ℤ :=
  Pi.single 3 1

theorem e6Q24_eq_subsystemGroup (Ω : Type) [Field Ω] :
    e6Q24 Ω = subsystemGroup Tag.E6 Ω e6Supp24 :=
  (subsystemGroup_eq_rootSpan _).symm

theorem one_mem_e6Supp24 : (1 : Fin Tag.E6.rank) ∈ e6Supp24 := by
  show (1 : Fin Tag.E6.rank) ∈ e6QpSupportList 12
  decide

theorem three_mem_e6Supp24 : (3 : Fin Tag.E6.rank) ∈ e6Supp24 := by
  show (3 : Fin Tag.E6.rank) ∈ e6QpSupportList 12
  decide

theorem mem_e6Supp24_iff {j : Fin Tag.E6.rank} : j ∈ e6Supp24 ↔ j = 1 ∨ j = 3 := by
  show j ∈ e6QpSupportList 12 ↔ _
  fin_cases j <;> decide

theorem isRoot_e6ε_add : IsRoot Tag.E6 (e6ε + e6ε') := by
  obtain ⟨k, hk⟩ : ∃ k : Fin 72, e6Root k = e6ε + e6ε' := by decide
  rw [← hk]
  exact isRoot_e6Root k

theorem not_isRoot_add_e6ε : ¬ IsRoot Tag.E6 (e6ε + e6ε' + e6ε) := by
  intro h
  obtain ⟨k, hk⟩ := exists_e6Root_eq h
  revert k
  decide

theorem not_isRoot_add_e6ε' : ¬ IsRoot Tag.E6 (e6ε + e6ε' + e6ε') := by
  intro h
  obtain ⟨k, hk⟩ := exists_e6Root_eq h
  revert k
  decide

theorem not_isRoot_neg_add_e6ε : ¬ IsRoot Tag.E6 (-(e6ε + e6ε') + -e6ε) := by
  intro h
  obtain ⟨k, hk⟩ := exists_e6Root_eq h
  revert k
  decide

theorem not_isRoot_neg_add_e6ε' : ¬ IsRoot Tag.E6 (-(e6ε + e6ε') + -e6ε') := by
  intro h
  obtain ⟨k, hk⟩ := exists_e6Root_eq h
  revert k
  decide

theorem e6ε_add_mem : e6ε + e6ε' ∈ parabolicRoots Tag.E6 e6Supp24 := by
  refine ⟨isRoot_e6ε_add, fun i hi => ?_⟩
  rw [mem_e6Supp24_iff, not_or] at hi
  simp [hi.1, hi.2]

theorem e6ε_mem : e6ε ∈ parabolicRoots Tag.E6 e6Supp24 :=
  single_mem_parabolicRoots one_mem_e6Supp24

theorem e6ε'_mem : e6ε' ∈ parabolicRoots Tag.E6 e6Supp24 :=
  single_mem_parabolicRoots three_mem_e6Supp24

variable {J : Set (Fin Tag.E6.rank)}

theorem e6Delta_e6ε (hJ : J = e6QpSupport 12 ∨ J = e6QpSupport 13) : e6Delta J e6ε = e6ε' := by
  rcases hJ with rfl | rfl
  · exact e6Delta_qp_single 12 (by show (1 : Fin Tag.E6.rank) ∈ e6QpSupportList 12; decide)
  · exact e6Delta_qp_single 13 (by show (1 : Fin Tag.E6.rank) ∈ e6QpSupportList 13; decide)

theorem e6Delta_e6ε' (hJ : J = e6QpSupport 12 ∨ J = e6QpSupport 13) : e6Delta J e6ε' = e6ε := by
  rcases hJ with rfl | rfl
  · exact e6Delta_qp_single 12 (by show (3 : Fin Tag.E6.rank) ∈ e6QpSupportList 12; decide)
  · exact e6Delta_qp_single 13 (by show (3 : Fin Tag.E6.rank) ∈ e6QpSupportList 13; decide)

theorem e6Delta_neg' (hJ : J = e6QpSupport 12 ∨ J = e6QpSupport 13) (x : Fin Tag.E6.rank → ℤ) :
    e6Delta J (-x) = -e6Delta J x := by
  rcases hJ with rfl | rfl
  · exact e6Delta_qp_neg 12 x
  · exact e6Delta_qp_neg 13 x

theorem e6Delta_γ₀ (hJ : J = e6QpSupport 12 ∨ J = e6QpSupport 13) :
    e6Delta J (e6ε + e6ε') = e6ε + e6ε' := by
  have hadd : e6Delta J (e6ε + e6ε') = e6Delta J e6ε + e6Delta J e6ε' := by
    rcases hJ with rfl | rfl
    · exact e6Delta_qp_add 12 _ _
    · exact e6Delta_qp_add 13 _ _
  rw [hadd, e6Delta_e6ε hJ, e6Delta_e6ε' hJ, add_comm]

variable {Ω : Type} [Field Ω] [CharP Ω 2] [IsAlgClosed Ω]

omit [IsAlgClosed Ω] in
theorem intCast_eq_one_of_charTwo {ε : ℤ} (h : ε = 1 ∨ ε = -1) : (ε : Ω) = 1 := by
  rcases h with rfl | rfl
  · exact Int.cast_one
  · rw [Int.cast_neg, Int.cast_one]
    exact CharTwo.neg_eq 1

omit [IsAlgClosed Ω] in
theorem pinnedX_e6ε'_mul_pinnedX_e6ε (s t : Ω) :
    pinnedX Tag.E6 Ω e6ε' s * pinnedX Tag.E6 Ω e6ε t =
      pinnedX Tag.E6 Ω (e6ε + e6ε') (s * t) *
        (pinnedX Tag.E6 Ω e6ε t * pinnedX Tag.E6 Ω e6ε' s) := by
  have hroot : IsRoot Tag.E6 (e6ε' + e6ε) := by rw [add_comm]; exact isRoot_e6ε_add
  obtain ⟨hε, hc⟩ := (simply_laced_root_commutator_unit Tag.E6 (Or.inr (Or.inl rfl))
    (isRoot_single _ 3) (isRoot_single _ 1) (by decide) (by decide)).1 hroot
  have h := hc Ω s t
  rw [commutatorElement_def, intCast_eq_one_of_charTwo hε, one_mul, add_comm] at h
  rw [← h]
  group

omit [IsAlgClosed Ω] in
theorem pinnedX_neg_e6ε'_mul_pinnedX_neg_e6ε (s t : Ω) :
    pinnedX Tag.E6 Ω (-e6ε') s * pinnedX Tag.E6 Ω (-e6ε) t =
      pinnedX Tag.E6 Ω (-(e6ε + e6ε')) (s * t) *
        (pinnedX Tag.E6 Ω (-e6ε) t * pinnedX Tag.E6 Ω (-e6ε') s) := by
  have hroot : IsRoot Tag.E6 (-e6ε' + -e6ε) := by
    rw [← neg_add, add_comm]
    exact IsRoot.neg isRoot_e6ε_add
  obtain ⟨hε, hc⟩ := (simply_laced_root_commutator_unit Tag.E6 (Or.inr (Or.inl rfl))
    (IsRoot.neg (isRoot_single _ 3)) (IsRoot.neg (isRoot_single _ 1)) (by decide)
    (by decide)).1 hroot
  have h := hc Ω s t
  rw [commutatorElement_def, intCast_eq_one_of_charTwo hε, one_mul, ← neg_add, add_comm e6ε'] at h
  rw [← h]
  group

omit [CharP Ω 2] [IsAlgClosed Ω] in
theorem commute_pinnedX_γ₀ {β : Fin Tag.E6.rank → ℤ} (hβ : β = e6ε ∨ β = e6ε') (u t : Ω) :
    Commute (pinnedX Tag.E6 Ω (e6ε + e6ε') u) (pinnedX Tag.E6 Ω β t) := by
  have hnot : ¬ IsRoot Tag.E6 (e6ε + e6ε' + β) := by
    rcases hβ with rfl | rfl
    · exact not_isRoot_add_e6ε
    · exact not_isRoot_add_e6ε'
  have hβr : IsRoot Tag.E6 β := by rcases hβ with rfl | rfl <;> exact isRoot_single _ _
  have hne : e6ε + e6ε' ≠ β := by rcases hβ with rfl | rfl <;> decide
  have hne' : e6ε + e6ε' ≠ -β := by rcases hβ with rfl | rfl <;> decide
  exact (simply_laced_root_commutator_unit Tag.E6 (Or.inr (Or.inl rfl)) isRoot_e6ε_add hβr hne
    hne').2 hnot Ω _ (Subgroup.subset_closure ⟨u, rfl⟩) _ (Subgroup.subset_closure ⟨t, rfl⟩)

omit [CharP Ω 2] [IsAlgClosed Ω] in
theorem commute_pinnedX_neg_γ₀ {β : Fin Tag.E6.rank → ℤ} (hβ : β = e6ε ∨ β = e6ε') (u t : Ω) :
    Commute (pinnedX Tag.E6 Ω (-(e6ε + e6ε')) u) (pinnedX Tag.E6 Ω (-β) t) := by
  have hnot : ¬ IsRoot Tag.E6 (-(e6ε + e6ε') + -β) := by
    rcases hβ with rfl | rfl
    · exact not_isRoot_neg_add_e6ε
    · exact not_isRoot_neg_add_e6ε'
  have hβr : IsRoot Tag.E6 (-β) := by
    rcases hβ with rfl | rfl <;> exact IsRoot.neg (isRoot_single _ _)
  have hne : -(e6ε + e6ε') ≠ -β := by rcases hβ with rfl | rfl <;> decide
  have hne' : -(e6ε + e6ε') ≠ -(-β) := by rcases hβ with rfl | rfl <;> decide
  exact (simply_laced_root_commutator_unit Tag.E6 (Or.inr (Or.inl rfl))
    (IsRoot.neg isRoot_e6ε_add) hβr hne hne').2 hnot Ω _ (Subgroup.subset_closure ⟨u, rfl⟩) _
    (Subgroup.subset_closure ⟨t, rfl⟩)

variable (hJ : J = e6QpSupport 12 ∨ J = e6QpSupport 13) (f : ℕ)
include hJ

omit [IsAlgClosed Ω] in
theorem pinnedX_γ₀_mem_e6P24 {u : Ω} (hu : u ^ 2 ^ f = u) :
    pinnedX Tag.E6 Ω (e6ε + e6ε') u ∈ e6P24 Ω J f :=
  ⟨pinnedX_mem_rootSpan e6ε_add_mem u, by
    change e6Psi Ω J f _ = _
    rw [e6Psi_pinnedX J f isRoot_e6ε_add, e6Delta_γ₀ hJ, hu]
    rfl⟩

omit [IsAlgClosed Ω] in
theorem pinnedX_neg_γ₀_mem_e6P24 {u : Ω} (hu : u ^ 2 ^ f = u) :
    pinnedX Tag.E6 Ω (-(e6ε + e6ε')) u ∈ e6P24 Ω J f :=
  ⟨pinnedX_mem_rootSpan (neg_mem_parabolicRoots e6ε_add_mem) u, by
    change e6Psi Ω J f _ = _
    rw [e6Psi_pinnedX J f (IsRoot.neg isRoot_e6ε_add), e6Delta_neg' hJ, e6Delta_γ₀ hJ, hu]
    rfl⟩

theorem exists_mem_e6P24 (hf : 1 ≤ f) {a : Ω} (ha : a ^ (2 ^ f) ^ 2 = a) :
    ∃ c : Ω, pinnedX Tag.E6 Ω e6ε a * pinnedX Tag.E6 Ω e6ε' (a ^ 2 ^ f) *
      pinnedX Tag.E6 Ω (e6ε + e6ε') c ∈ e6P24 Ω J f := by
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨c, hc⟩ := exists_pow_sub_add_eq_zero hq (a ^ 2 ^ f * a)
  refine ⟨c, mul_mem (mul_mem (pinnedX_mem_rootSpan e6ε_mem a)
    (pinnedX_mem_rootSpan e6ε'_mem _)) (pinnedX_mem_rootSpan e6ε_add_mem c), ?_⟩
  change e6Psi Ω J f _ = _
  rw [map_mul, map_mul, e6Psi_pinnedX J f (isRoot_single _ 1),
    e6Psi_pinnedX J f (isRoot_single _ 3), e6Psi_pinnedX J f isRoot_e6ε_add,
    show (Pi.single 1 1 : Fin Tag.E6.rank → ℤ) = e6ε from rfl,
    show (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) = e6ε' from rfl, e6Delta_e6ε hJ, e6Delta_e6ε' hJ,
    e6Delta_γ₀ hJ, ← pow_mul, ← sq, ha, pinnedX_e6ε'_mul_pinnedX_e6ε]
  have hcq : a ^ 2 ^ f * a + c ^ 2 ^ f = c := by linear_combination hc
  set P := pinnedX Tag.E6 Ω (e6ε + e6ε') (a ^ 2 ^ f * a)
  set Q := pinnedX Tag.E6 Ω (e6ε + e6ε') (c ^ 2 ^ f)
  set A := pinnedX Tag.E6 Ω e6ε a
  set B := pinnedX Tag.E6 Ω e6ε' (a ^ 2 ^ f)
  have h1 : P * A = A * P := (commute_pinnedX_γ₀ (Ω := Ω) (Or.inl rfl) _ _).eq
  have h2 : P * B = B * P := (commute_pinnedX_γ₀ (Ω := Ω) (Or.inr rfl) _ _).eq
  calc P * (A * B) * Q = P * A * B * Q := by simp only [mul_assoc]
    _ = A * (P * B) * Q := by rw [h1]; simp only [mul_assoc]
    _ = A * B * (P * Q) := by rw [h2]; simp only [mul_assoc]
    _ = A * B * pinnedX Tag.E6 Ω (e6ε + e6ε') c := by rw [← pinnedX_add, hcq]

theorem exists_neg_mem_e6P24 (hf : 1 ≤ f) {a : Ω} (ha : a ^ (2 ^ f) ^ 2 = a) :
    ∃ c : Ω, pinnedX Tag.E6 Ω (-e6ε) a * pinnedX Tag.E6 Ω (-e6ε') (a ^ 2 ^ f) *
      pinnedX Tag.E6 Ω (-(e6ε + e6ε')) c ∈ e6P24 Ω J f := by
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨c, hc⟩ := exists_pow_sub_add_eq_zero hq (a ^ 2 ^ f * a)
  refine ⟨c, mul_mem (mul_mem (pinnedX_mem_rootSpan (neg_mem_parabolicRoots e6ε_mem) a)
    (pinnedX_mem_rootSpan (neg_mem_parabolicRoots e6ε'_mem) _))
    (pinnedX_mem_rootSpan (neg_mem_parabolicRoots e6ε_add_mem) c), ?_⟩
  change e6Psi Ω J f _ = _
  rw [map_mul, map_mul, e6Psi_pinnedX J f (IsRoot.neg (isRoot_single _ 1)),
    e6Psi_pinnedX J f (IsRoot.neg (isRoot_single _ 3)),
    e6Psi_pinnedX J f (IsRoot.neg isRoot_e6ε_add), e6Delta_neg' hJ, e6Delta_neg' hJ,
    e6Delta_neg' hJ,
    show (Pi.single 1 1 : Fin Tag.E6.rank → ℤ) = e6ε from rfl,
    show (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) = e6ε' from rfl, e6Delta_e6ε hJ, e6Delta_e6ε' hJ,
    e6Delta_γ₀ hJ, ← pow_mul, ← sq, ha, pinnedX_neg_e6ε'_mul_pinnedX_neg_e6ε]
  have hcq : a ^ 2 ^ f * a + c ^ 2 ^ f = c := by linear_combination hc
  set P := pinnedX Tag.E6 Ω (-(e6ε + e6ε')) (a ^ 2 ^ f * a)
  set Q := pinnedX Tag.E6 Ω (-(e6ε + e6ε')) (c ^ 2 ^ f)
  set A := pinnedX Tag.E6 Ω (-e6ε) a
  set B := pinnedX Tag.E6 Ω (-e6ε') (a ^ 2 ^ f)
  have h1 : P * A = A * P := (commute_pinnedX_neg_γ₀ (Ω := Ω) (Or.inl rfl) _ _).eq
  have h2 : P * B = B * P := (commute_pinnedX_neg_γ₀ (Ω := Ω) (Or.inr rfl) _ _).eq
  calc P * (A * B) * Q = P * A * B * Q := by simp only [mul_assoc]
    _ = A * (P * B) * Q := by rw [h1]; simp only [mul_assoc]
    _ = A * B * (P * Q) := by rw [h2]; simp only [mul_assoc]
    _ = A * B * pinnedX Tag.E6 Ω (-(e6ε + e6ε')) c := by rw [← pinnedX_add, hcq]

omit hJ [IsAlgClosed Ω] in
theorem e6P24_le_e6Q24 : e6P24 Ω J f ≤ e6Q24 Ω :=
  inf_le_left

theorem e6Commutant_e6P24 (hf : 2 ≤ f) :
    e6Commutant (e6P24 Ω J f : Set (ModGL Tag.E6 Ω)) =
      e6Commutant (e6Q24 Ω : Set (ModGL Tag.E6 Ω)) := by
  refine Set.Subset.antisymm (fun X hX => ?_) (e6Commutant_anti (e6P24_le_e6Q24 f))
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨F₁, hF₁, hF₁'⟩ := exists_finset_frobeniusFixed (Ω := Ω) (n := f) (by omega)
  obtain ⟨F₂, hF₂, hF₂'⟩ := exists_finset_frobeniusFixed (Ω := Ω) (n := f * 2) (by omega)
  have hF₂c : F₂.card = (2 ^ f) ^ 2 := by rw [hF₂, pow_mul]
  have hγ : ∀ t : Ω, Commute X (pinnedX Tag.E6 Ω (e6ε + e6ε') t :
      Module.End Ω (RootModule Tag.E6 Ω)) :=
    commute_pinnedX_of_three_le_card (F := F₁) (by omega) fun u hu =>
      hX _ (pinnedX_γ₀_mem_e6P24 hJ f ((hF₁' u).1 hu))
  have hγ' : ∀ t : Ω, Commute X (pinnedX Tag.E6 Ω (-(e6ε + e6ε')) t :
      Module.End Ω (RootModule Tag.E6 Ω)) :=
    commute_pinnedX_of_three_le_card (F := F₁) (by omega) fun u hu =>
      hX _ (pinnedX_neg_γ₀_mem_e6P24 hJ f ((hF₁' u).1 hu))
  have hpos : ∀ a ∈ F₂, Commute X ((pinnedX Tag.E6 Ω e6ε a * pinnedX Tag.E6 Ω e6ε' (a ^ 2 ^ f) :
      ModGL Tag.E6 Ω) : Module.End Ω (RootModule Tag.E6 Ω)) := by
    intro a ha
    have ha' : a ^ (2 ^ f) ^ 2 = a := by rw [← pow_mul, ← hF₂'] ; exact ha
    obtain ⟨c, hc⟩ := exists_mem_e6P24 hJ f (by omega) ha'
    have h1 := hX _ hc
    have h2 := (hγ (-c))
    rw [← pinnedX_neg] at h2
    have h3 := h1.mul_right ((Commute.units_inv_right (hγ c)))
    rw [← Units.val_mul, mul_inv_cancel_right] at h3
    exact h3
  have hneg : ∀ a ∈ F₂, Commute X ((pinnedX Tag.E6 Ω (-e6ε) a *
      pinnedX Tag.E6 Ω (-e6ε') (a ^ 2 ^ f) : ModGL Tag.E6 Ω) :
        Module.End Ω (RootModule Tag.E6 Ω)) := by
    intro a ha
    have ha' : a ^ (2 ^ f) ^ 2 = a := by rw [← pow_mul, ← hF₂'] ; exact ha
    obtain ⟨c, hc⟩ := exists_neg_mem_e6P24 hJ f (by omega) ha'
    have h1 := hX _ hc
    have h3 := h1.mul_right ((Commute.units_inv_right (hγ' c)))
    rw [← Units.val_mul, mul_inv_cancel_right] at h3
    exact h3
  obtain ⟨hA₁, hB₁, hA₂, hB₂⟩ := commute_of_pair_card (by omega) hF₂c (X := X)
    (A₁ := xCoeff Tag.E6 Ω 1 1) (B₁ := xCoeff Tag.E6 Ω 1 2)
    (A₂ := xCoeff Tag.E6 Ω 3 1) (B₂ := xCoeff Tag.E6 Ω 3 2) fun a ha => by
      have := hpos a ha
      rwa [Units.val_mul, pinnedX_single, pinnedX_single, coe_xUnit, coe_xUnit, xOp_E6_eq,
        xOp_E6_eq] at this
  obtain ⟨hC₁, hD₁, hC₂, hD₂⟩ := commute_of_pair_card (by omega) hF₂c (X := X)
    (A₁ := yCoeff Tag.E6 Ω 1 1) (B₁ := yCoeff Tag.E6 Ω 1 2)
    (A₂ := yCoeff Tag.E6 Ω 3 1) (B₂ := yCoeff Tag.E6 Ω 3 2) fun a ha => by
      have := hneg a ha
      rwa [Units.val_mul, pinnedX_neg_single, pinnedX_neg_single, coe_yUnit, coe_yUnit,
        yOp_E6_eq, yOp_E6_eq] at this
  rw [e6Q24_eq_subsystemGroup]
  refine mem_e6Commutant_subsystemGroup (fun j hj c => ?_) (fun j hj c => ?_)
  · rcases mem_e6Supp24_iff.1 hj with rfl | rfl
    · rw [xOp_E6_eq]
      exact commute_one_add_of_commute hA₁ hB₁ c
    · rw [xOp_E6_eq]
      exact commute_one_add_of_commute hA₂ hB₂ c
  · rcases mem_e6Supp24_iff.1 hj with rfl | rfl
    · rw [yOp_E6_eq]
      exact commute_one_add_of_commute hC₁ hD₁ c
    · rw [yOp_E6_eq]
      exact commute_one_add_of_commute hC₂ hD₂ c

end Factor

end CFSG.RankThree.Lattice
