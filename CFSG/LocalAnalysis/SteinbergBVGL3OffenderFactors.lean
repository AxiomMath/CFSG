module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceIrreducibleModules
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceFixedCodimensions

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u

namespace CFSG.LocalAnalysis.SteinbergBV

open Module CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

abbrev subrepChainFactor {k G W : Type*} [Field k] [Monoid G] [AddCommGroup W] [Module k W]
    {ρ : Representation k G W} {n : ℕ} (c : Fin (n + 1) → Subrepresentation ρ) (i : Fin n) :=
  (inSubrep (c i.castSucc) (c i.succ)).quotient

namespace OffenderFactors

variable {k G : Type*} [Field k] [Group G]

theorem finrank_invariants_eq_of_equiv {M N : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] {ρ : Representation k G M} {σ : Representation k G N}
    (φ : ρ.Equiv σ) (B : Subgroup G) :
    finrank k (Representation.invariants (ρ.comp B.subtype)) =
      finrank k (Representation.invariants (σ.comp B.subtype)) := by
  have hint : ∀ g x, φ (ρ g x) = σ g (φ x) := fun g x =>
    Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g x
  have hmap : (Representation.invariants (ρ.comp B.subtype)).map (φ.toLinearEquiv : M →ₗ[k] N) =
      Representation.invariants (σ.comp B.subtype) := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [Representation.mem_invariants]
      intro b
      have hb := (Representation.mem_invariants _ x).1 hx b
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at hb ⊢
      change σ b (φ x) = φ x
      rw [← hint, hb]
    · intro y hy
      refine ⟨φ.toLinearEquiv.symm y, ?_, φ.toLinearEquiv.apply_symm_apply y⟩
      rw [SetLike.mem_coe, Representation.mem_invariants]
      intro b
      have hb := (Representation.mem_invariants _ y).1 hy b
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at hb ⊢
      apply φ.toLinearEquiv.injective
      change φ (ρ b (φ.toLinearEquiv.symm y)) = φ (φ.toLinearEquiv.symm y)
      rw [hint]
      change σ b (φ.toLinearEquiv (φ.toLinearEquiv.symm y)) = φ.toLinearEquiv _
      rw [φ.toLinearEquiv.apply_symm_apply, hb]
  rw [← hmap, LinearEquiv.finrank_map_eq]

theorem finrank_quotient_inSubrep_add {M : Type*} [AddCommGroup M] [Module k M]
    [FiniteDimensional k M] {ρ : Representation k G M} {A A' : Subrepresentation ρ}
    (h : A ≤ A') :
    finrank k (A'.toSubmodule ⧸ (inSubrep A A').toSubmodule) + finrank k A.toSubmodule =
      finrank k A'.toSubmodule := by
  have e : (inSubrep A A').toSubmodule ≃ₗ[k] A.toSubmodule :=
    Submodule.comapSubtypeEquivOfLe (show A.toSubmodule ≤ A'.toSubmodule from h)
  rw [← e.finrank_eq]
  exact Submodule.finrank_quotient_add_finrank _

theorem finrank_invariants_inf_le {M : Type*} [AddCommGroup M] [Module k M]
    [FiniteDimensional k M] {ρ : Representation k G M} (B : Subgroup G)
    (A A' : Subrepresentation ρ) :
    finrank k ↥(Representation.invariants (ρ.comp B.subtype) ⊓ A'.toSubmodule) ≤
      finrank k ↥(Representation.invariants (ρ.comp B.subtype) ⊓ A.toSubmodule) +
        finrank k (Representation.invariants ((inSubrep A A').quotient.comp B.subtype)) := by
  set C := Representation.invariants (ρ.comp B.subtype) with hC
  set P := inSubrep A A' with hP
  let ψ : ↥(C ⊓ A'.toSubmodule) →ₗ[k] A'.toSubmodule ⧸ P.toSubmodule :=
    P.toSubmodule.mkQ ∘ₗ Submodule.inclusion inf_le_right
  have hrange : LinearMap.range ψ ≤ Representation.invariants (P.quotient.comp B.subtype) := by
    rintro _ ⟨x, rfl⟩
    rw [Representation.mem_invariants]
    intro b
    simp only [ψ, LinearMap.comp_apply, Submodule.mkQ_apply, MonoidHom.comp_apply,
      Subgroup.coe_subtype]
    show Submodule.Quotient.mk (A'.toRepresentation (b : G) (Submodule.inclusion _ x)) = _
    congr 1
    apply Subtype.ext
    exact (Representation.mem_invariants _ _).1 (Submodule.mem_inf.1 x.2).1 b
  have hker : finrank k (LinearMap.ker ψ) ≤ finrank k ↥(C ⊓ A.toSubmodule) := by
    let ι : LinearMap.ker ψ →ₗ[k] ↥(C ⊓ A.toSubmodule) :=
      ((C ⊓ A'.toSubmodule).subtype ∘ₗ (LinearMap.ker ψ).subtype).codRestrict _ fun x => by
        refine Submodule.mem_inf.2 ⟨(Submodule.mem_inf.1 x.1.2).1, ?_⟩
        have hx := x.2
        rw [LinearMap.mem_ker] at hx
        simp only [ψ, LinearMap.comp_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero] at hx
        exact hx
    refine LinearMap.finrank_le_finrank_of_injective (f := ι) fun x y hxy => ?_
    have h := congrArg (fun z : ↥(C ⊓ A.toSubmodule) => (z : M)) hxy
    exact Subtype.ext (Subtype.ext h)
  have h1 := LinearMap.finrank_range_add_finrank_ker ψ
  have h2 := Submodule.finrank_mono hrange
  omega

theorem sum_add_le_of_step : ∀ {n : ℕ} (x y : Fin (n + 1) → ℕ) (d : Fin n → ℕ), x 0 = 0 →
    y 0 = 0 → (∀ i : Fin n, d i + y i.succ + x i.castSucc ≤ x i.succ + y i.castSucc) →
    ∑ i, d i + y (Fin.last n) ≤ x (Fin.last n)
  | 0, x, y, d, hx0, hy0, _ => by
    simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add]
    exact (show y (Fin.last 0) = 0 from hy0).le.trans (Nat.zero_le _)
  | n + 1, x, y, d, hx0, hy0, h => by
    have ih := sum_add_le_of_step (fun i => x i.castSucc) (fun i => y i.castSucc)
      (fun i => d i.castSucc) hx0 hy0 fun i => by
        have := h i.castSucc
        rwa [Fin.succ_castSucc] at this
    have hl : d (Fin.last n) + y (Fin.last (n + 1)) + x (Fin.last n).castSucc ≤
        x (Fin.last (n + 1)) + y (Fin.last n).castSucc := h (Fin.last n)
    rw [Fin.sum_univ_castSucc]
    beta_reduce at ih
    omega

theorem sum_codim_factor_le {M : Type*} [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    {ρ : Representation k G M} (B : Subgroup G) {n : ℕ} (c : Fin (n + 1) → Subrepresentation ρ)
    (hc0 : c 0 = ⊥) (hcn : c (Fin.last n) = ⊤) (hmono : ∀ i : Fin n, c i.castSucc ≤ c i.succ) :
    ∑ i : Fin n, (finrank k ((c i.succ).toSubmodule ⧸
        (inSubrep (c i.castSucc) (c i.succ)).toSubmodule) -
      finrank k (Representation.invariants
        ((inSubrep (c i.castSucc) (c i.succ)).quotient.comp B.subtype))) ≤
      finrank k M - finrank k (Representation.invariants (ρ.comp B.subtype)) := by
  have key := sum_add_le_of_step (fun j => finrank k (c j).toSubmodule)
    (fun j => finrank k ↥(Representation.invariants (ρ.comp B.subtype) ⊓ (c j).toSubmodule))
    (fun i => finrank k ((c i.succ).toSubmodule ⧸
      (inSubrep (c i.castSucc) (c i.succ)).toSubmodule) -
      finrank k (Representation.invariants
        ((inSubrep (c i.castSucc) (c i.succ)).quotient.comp B.subtype)))
    (by rw [hc0]; exact finrank_bot k M)
    (by
      show finrank k ↥(Representation.invariants (ρ.comp B.subtype) ⊓ (c 0).toSubmodule) = 0
      rw [hc0]
      show finrank k ↥(Representation.invariants (ρ.comp B.subtype) ⊓ ⊥) = 0
      rw [inf_bot_eq]
      exact finrank_bot k M)
    (fun i => by
      have h1 := finrank_quotient_inSubrep_add (hmono i)
      have h2 := finrank_invariants_inf_le B (c i.castSucc) (c i.succ)
      have h3 := Submodule.finrank_le (Representation.invariants
        ((inSubrep (c i.castSucc) (c i.succ)).quotient.comp B.subtype))
      omega)
  have hx : finrank k (c (Fin.last n)).toSubmodule = finrank k M := by
    rw [hcn]
    exact finrank_top k M
  have hy : finrank k ↥(Representation.invariants (ρ.comp B.subtype) ⊓
      (c (Fin.last n)).toSubmodule) = finrank k (Representation.invariants (ρ.comp B.subtype)) := by
    rw [hcn]
    show finrank k ↥(Representation.invariants (ρ.comp B.subtype) ⊓ ⊤) = _
    rw [inf_top_eq]
  beta_reduce at key
  rw [hx, hy] at key
  omega

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem invariants_trivRep (B : Subgroup (V ≃ₗ[ZMod 2] V)) :
    Representation.invariants ((trivRep V).comp B.subtype) = ⊤ :=
  eq_top_iff.2 fun _ _ _ => rfl

theorem invariants_natRep (B : Subgroup (V ≃ₗ[ZMod 2] V)) :
    Representation.invariants ((natRep V).comp B.subtype) = fixedVec B := by
  ext v
  change (∀ b : B, natRep V b v = v) ↔ ∀ b ∈ B, b v = v
  exact ⟨fun h b hb => h ⟨b, hb⟩, fun h b => h b b.2⟩

theorem invariants_dualRep (B : Subgroup (V ≃ₗ[ZMod 2] V)) :
    Representation.invariants ((dualRep V).comp B.subtype) = fixedDual B := by
  ext f
  change (∀ b : B, dualRep V b f = f) ↔ ∀ b ∈ B, b.symm.dualMap f = f
  have key : ∀ b : V ≃ₗ[ZMod 2] V, dualRep V b f = b.symm.dualMap f := fun b =>
    LinearMap.ext fun v => by rw [dualRep_apply, LinearEquiv.dualMap_apply]
  exact ⟨fun h b hb => (key b).symm.trans (h ⟨b, hb⟩), fun h b => (key b).trans (h b b.2)⟩

theorem finrank_invariants_adjRep (B : Subgroup (V ≃ₗ[ZMod 2] V)) :
    finrank (ZMod 2) (Representation.invariants ((adjRep V).comp B.subtype)) =
      finrank (ZMod 2) (fixedTraceZeroEnd B) := by
  have hmap : (Representation.invariants ((adjRep V).comp B.subtype)).map
      (traceZeroEnd V).subtype = fixedTraceZeroEnd B := by
    ext X
    constructor
    · rintro ⟨Y, hY, rfl⟩
      refine ⟨Y.2, fun b hb => ?_⟩
      have h := congrArg Subtype.val ((Representation.mem_invariants _ Y).1 hY ⟨b, hb⟩)
      exact h
    · rintro ⟨hX, hXb⟩
      refine ⟨⟨X, hX⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Representation.mem_invariants]
      exact fun b => Subtype.ext (hXb b b.2)
  rw [← hmap]
  exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
    (traceZeroEnd V).injective_subtype _)

end OffenderFactors

open OffenderFactors in
theorem GL3_offender_composition_factor_production {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (hV : finrank (ZMod 2) V = 3) {E : Type u} [AddCommGroup E]
    [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) (V ≃ₗ[ZMod 2] V) E) (B : Subgroup (V ≃ₗ[ZMod 2] V))
    (hBe : CFSG.Open.IsElemAbelian 2 B) (hB : B ≠ ⊥) (r : ℕ) (hr : Nat.card B = 2 ^ r)
    (hoff : finrank (ZMod 2) E -
      finrank (ZMod 2) (Representation.invariants (ρ.comp B.subtype)) ≤ r)
    (n : ℕ) (c : Fin (n + 1) → Subrepresentation ρ) (hc0 : c 0 = ⊥) (hcn : c (Fin.last n) = ⊤)
    (hc : ∀ i : Fin n, c i.castSucc < c i.succ ∧ (subrepChainFactor c i).IsIrreducible) :
    (∀ i : Fin n, IsEmpty ((subrepChainFactor c i).Equiv (adjRep V))) ∧
    ((∀ i : Fin n, Nonempty ((subrepChainFactor c i).Equiv (trivRep V)) ∨
        Nonempty ((subrepChainFactor c i).Equiv (natRep V))) ∨
      ∀ i : Fin n, Nonempty ((subrepChainFactor c i).Equiv (trivRep V)) ∨
        Nonempty ((subrepChainFactor c i).Equiv (dualRep V))) ∧
    Nat.card {i : Fin n // IsEmpty ((subrepChainFactor c i).Equiv (trivRep V))} ≤ 2 ∧
    (Nat.card {i : Fin n // IsEmpty ((subrepChainFactor c i).Equiv (trivRep V))} = 2 →
      r = 2 ∧
      ((∃ i : Fin n, Nonempty ((subrepChainFactor c i).Equiv (natRep V))) →
        finrank (ZMod 2) V -
          finrank (ZMod 2) (Representation.invariants ((natRep V).comp B.subtype)) = 1) ∧
      ((∃ i : Fin n, Nonempty ((subrepChainFactor c i).Equiv (dualRep V))) →
        finrank (ZMod 2) (Dual (ZMod 2) V) -
          finrank (ZMod 2) (Representation.invariants ((dualRep V).comp B.subtype)) = 1)) := by
  classical
  have : FiniteDimensional (ZMod 2) V := Module.finite_of_finrank_eq_succ hV
  have hdual3 : finrank (ZMod 2) (Dual (ZMod 2) V) = 3 := by rw [Subspace.dual_finrank_eq, hV]
  obtain ⟨hr12, hr1, hr2, hA⟩ := GL3_elementary_abelian_fixed_codimensions hV B hBe hB r hr
  set dV := finrank (ZMod 2) V - finrank (ZMod 2) (fixedVec B) with hdV
  set dW := finrank (ZMod 2) (Dual (ZMod 2) V) - finrank (ZMod 2) (fixedDual B) with hdW
  set dA := finrank (ZMod 2) (traceZeroEnd V) - finrank (ZMod 2) (fixedTraceZeroEnd B) with hdA
  have hVW : 1 ≤ dV ∧ 1 ≤ dW ∧ r < dV + dW := by
    rcases hr12 with rfl | rfl
    · obtain ⟨h1, h2⟩ := Prod.mk.inj (hr1 rfl)
      omega
    · rcases hr2 rfl with h | h
      · obtain ⟨h1, h2⟩ := Prod.mk.inj h
        omega
      · obtain ⟨h1, h2⟩ := Prod.mk.inj h
        omega
  have hA4 : 4 ≤ dA := by
    rw [hA, hr]
    rcases hr12 with h | h <;> subst h <;> norm_num
  have hr2' : r ≤ 2 := by omega
  set d : Fin n → ℕ := fun i =>
    finrank (ZMod 2) ((c i.succ).toSubmodule ⧸ (inSubrep (c i.castSucc) (c i.succ)).toSubmodule) -
      finrank (ZMod 2) (Representation.invariants ((subrepChainFactor c i).comp B.subtype)) with hd
  have hsum : ∑ i, d i ≤ r := (sum_codim_factor_le B c hc0 hcn fun i => (hc i).1.le).trans hoff
  have hle1 : ∀ i, d i ≤ r := fun i =>
    (Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i)).trans hsum
  have hle2 : ∀ i j, i ≠ j → d i + d j ≤ r := fun i j hij => by
    have h := Finset.sum_le_sum_of_subset (f := d) (Finset.subset_univ {i, j})
    rw [Finset.sum_pair hij] at h
    exact h.trans hsum
  have hcls : ∀ i, Nonempty ((subrepChainFactor c i).Equiv (trivRep V)) ∨
      Nonempty ((subrepChainFactor c i).Equiv (natRep V)) ∨
      Nonempty ((subrepChainFactor c i).Equiv (dualRep V)) ∨
      Nonempty ((subrepChainFactor c i).Equiv (adjRep V)) := by
    intro i
    obtain ⟨j, hj, -⟩ :=
      (irreducible_binary_GL3_module_production hV).1 _ (subrepChainFactor c i) (hc i).2
    fin_cases j
    · exact Or.inl hj
    · exact Or.inr (Or.inl hj)
    · exact Or.inr (Or.inr (Or.inl hj))
    · exact Or.inr (Or.inr (Or.inr hj))
  have hdtriv : ∀ i, Nonempty ((subrepChainFactor c i).Equiv (trivRep V)) → d i = 0 := by
    rintro i ⟨φ⟩
    simp only [hd]
    rw [φ.toLinearEquiv.finrank_eq, finrank_invariants_eq_of_equiv φ, invariants_trivRep,
      finrank_top, Nat.sub_self]
  have hdnat : ∀ i, Nonempty ((subrepChainFactor c i).Equiv (natRep V)) → d i = dV := by
    rintro i ⟨φ⟩
    simp only [hd]
    rw [φ.toLinearEquiv.finrank_eq, finrank_invariants_eq_of_equiv φ, invariants_natRep]
  have hddual : ∀ i, Nonempty ((subrepChainFactor c i).Equiv (dualRep V)) → d i = dW := by
    rintro i ⟨φ⟩
    simp only [hd]
    rw [φ.toLinearEquiv.finrank_eq, finrank_invariants_eq_of_equiv φ, invariants_dualRep]
  have hdadj : ∀ i, Nonempty ((subrepChainFactor c i).Equiv (adjRep V)) → d i = dA := by
    rintro i ⟨φ⟩
    simp only [hd]
    rw [φ.toLinearEquiv.finrank_eq, finrank_invariants_eq_of_equiv φ, finrank_invariants_adjRep]
  have hnotA : ∀ i, IsEmpty ((subrepChainFactor c i).Equiv (adjRep V)) := fun i =>
    ⟨fun φ => by
      have h1 := hdadj i ⟨φ⟩
      have h2 := hle1 i
      omega⟩
  have hnat_nt : ∀ i, Nonempty ((subrepChainFactor c i).Equiv (natRep V)) →
      IsEmpty ((subrepChainFactor c i).Equiv (trivRep V)) := fun i ⟨φ⟩ =>
    ⟨fun ψ => by
      have h := ψ.toLinearEquiv.finrank_eq.symm.trans φ.toLinearEquiv.finrank_eq
      rw [finrank_self, hV] at h
      omega⟩
  have hdual_nt : ∀ i, Nonempty ((subrepChainFactor c i).Equiv (dualRep V)) →
      IsEmpty ((subrepChainFactor c i).Equiv (trivRep V)) := fun i ⟨φ⟩ =>
    ⟨fun ψ => by
      have h := ψ.toLinearEquiv.finrank_eq.symm.trans φ.toLinearEquiv.finrank_eq
      rw [finrank_self, hdual3] at h
      omega⟩
  have hnontriv : ∀ i, IsEmpty ((subrepChainFactor c i).Equiv (trivRep V)) → 1 ≤ d i := by
    intro i hi
    rcases hcls i with h | h | h | h
    · exact absurd h (not_nonempty_iff.2 hi)
    · rw [hdnat i h]
      exact hVW.1
    · rw [hddual i h]
      exact hVW.2.1
    · exact absurd h (not_nonempty_iff.2 (hnotA i))
  have hcard : Nat.card {i : Fin n // IsEmpty ((subrepChainFactor c i).Equiv (trivRep V))} =
      (Finset.univ.filter fun i => IsEmpty ((subrepChainFactor c i).Equiv (trivRep V))).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcount : (Finset.univ.filter fun i =>
      IsEmpty ((subrepChainFactor c i).Equiv (trivRep V))).card ≤ r := by
    have h1 := Finset.card_nsmul_le_sum (Finset.univ.filter fun i =>
      IsEmpty ((subrepChainFactor c i).Equiv (trivRep V))) d 1
      fun i hi => hnontriv i (Finset.mem_filter.1 hi).2
    rw [smul_eq_mul, mul_one] at h1
    exact h1.trans ((Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans hsum)
  refine ⟨hnotA, ?_, by rw [hcard]; omega, fun h2 => ?_⟩
  ·
    by_cases hex : ∃ i, Nonempty ((subrepChainFactor c i).Equiv (natRep V))
    · left
      obtain ⟨i₀, hi₀⟩ := hex
      intro j
      rcases hcls j with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso
        by_cases hij : i₀ = j
        · subst hij
          obtain ⟨φ⟩ := hi₀
          obtain ⟨ψ⟩ := h
          exact (isEmpty_equiv_natRep_dualRep hV).elim (φ.symm.trans ψ)
        · have h1 := hle2 i₀ j hij
          rw [hdnat i₀ hi₀, hddual j h] at h1
          omega
      · exact absurd h (not_nonempty_iff.2 (hnotA j))
    · right
      intro j
      rcases hcls j with h | h | h | h
      · exact Or.inl h
      · exact absurd ⟨j, h⟩ hex
      · exact Or.inr h
      · exact absurd h (not_nonempty_iff.2 (hnotA j))
  ·
    rw [hcard] at h2
    obtain ⟨a, b, hab, hS⟩ := Finset.card_eq_two.1 h2
    have ha : IsEmpty ((subrepChainFactor c a).Equiv (trivRep V)) := by
      have h : a ∈ Finset.univ.filter fun i =>
          IsEmpty ((subrepChainFactor c i).Equiv (trivRep V)) := by
        rw [hS]
        exact Finset.mem_insert_self a {b}
      exact (Finset.mem_filter.1 h).2
    have hb : IsEmpty ((subrepChainFactor c b).Equiv (trivRep V)) := by
      have h : b ∈ Finset.univ.filter fun i =>
          IsEmpty ((subrepChainFactor c i).Equiv (trivRep V)) := by
        rw [hS]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
      exact (Finset.mem_filter.1 h).2
    have hda := hnontriv a ha
    have hdb := hnontriv b hb
    have hab2 := hle2 a b hab
    have hother : ∀ i, IsEmpty ((subrepChainFactor c i).Equiv (trivRep V)) →
        ∃ j, j ≠ i ∧ 1 ≤ d j := by
      intro i hi
      have h : i ∈ Finset.univ.filter fun i =>
          IsEmpty ((subrepChainFactor c i).Equiv (trivRep V)) :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩
      rw [hS] at h
      rcases Finset.mem_insert.1 h with rfl | h
      · exact ⟨b, hab.symm, hdb⟩
      · rw [Finset.mem_singleton] at h
        subst h
        exact ⟨a, hab, hda⟩
    refine ⟨by omega, ?_, ?_⟩
    · rintro ⟨i₀, hi₀⟩
      rw [invariants_natRep]
      obtain ⟨j, hj, hdj⟩ := hother i₀ (hnat_nt i₀ hi₀)
      have h1 := hle2 i₀ j hj.symm
      rw [hdnat i₀ hi₀] at h1
      omega
    · rintro ⟨i₀, hi₀⟩
      rw [invariants_dualRep]
      obtain ⟨j, hj, hdj⟩ := hother i₀ (hdual_nt i₀ hi₀)
      have h1 := hle2 i₀ j hj.symm
      rw [hddual i₀ hi₀] at h1
      omega

end CFSG.LocalAnalysis.SteinbergBV
