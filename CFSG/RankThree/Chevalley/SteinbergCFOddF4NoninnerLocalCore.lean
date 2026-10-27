module

public import CFSG.RankThree.Chevalley.SteinbergCFOddInnerFieldLocalCore

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank
open scoped Pointwise

theorem odd_F4_noninner_prime_local_core_trivial {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime)
    (B : Subgroup (MulAut (adjointGroup .F4 K)))
    (hB : (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range ≤ B) :
    (∀ α : B, (α : MulAut (adjointGroup .F4 K)) ∉
        (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range →
      orderOf α = p →
      aschbacherSolvableCore p (Subgroup.centralizer {α} : Subgroup B) = ⊥) ∧
    ∀ A : Subgroup B, IsElementaryAbelian p A → Nat.card A = p ^ 2 →
      ¬A.map B.subtype ≤
        (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range →
      Nat.card ↥(A ⊓ (MulAut.conj : adjointGroup .F4 K →*
          MulAut (adjointGroup .F4 K)).range.comap B.subtype) = p ∧
        (⨅ (a : B) (_ : a ∈ A) (_ : a ≠ 1),
          inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer {a})) = ⊥ ∧
        ∀ t ∈ A, (t : MulAut (adjointGroup .F4 K)) ∉
            (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range →
          ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer {t}), A⁆ :
              Subgroup B) : Set B) *
            (((⨅ (a : B) (_ : a ∈ A) (_ : a ≠ 1),
              inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer {a})) :
                Subgroup B) : Set B) = {1} := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hNFpt, Θ, -, -, hΘker, -⟩ :=
    odd_F4_and_nonexceptional_G2_automorphism_normal_form hℓ hℓ2 hf K hK .F4 (Or.inl rfl)
  have hNF := conj_normalForm_of_pointwise hNFpt
  set R := (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range
  have hcore : ∀ α : B, (α : MulAut (adjointGroup .F4 K)) ∉ R → orderOf α = p →
      aschbacherSolvableCore p (Subgroup.centralizer {α} : Subgroup B) = ⊥ := by
    intro α hα hαp
    obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF α
    exact (odd_Chevalley_inner_field_noninner_prime_local_core_trivial .F4 hℓ hℓ2 hf K hK hNF hp
      B hB α hα hαp x σ hxσ).2.2.2
  refine ⟨hcore, fun A hA hAcard hAinn => ?_⟩
  have : IsElementaryAbelian p A := hA
  have hApow : ∀ a : A, a ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p A)
  have hord : ∀ t ∈ A, (t : MulAut (adjointGroup .F4 K)) ∉ R → orderOf t = p := by
    intro t ht htinn
    refine orderOf_eq_prime (by simpa using congrArg Subtype.val (hApow ⟨t, ht⟩))
      fun h => htinn ?_
    rw [h]
    exact one_mem _
  obtain ⟨t, htA, htinn⟩ : ∃ t ∈ A, (t : MulAut (adjointGroup .F4 K)) ∉ R := by
    by_contra h
    push Not at h
    exact hAinn (by rintro _ ⟨t, ht, rfl⟩; exact h t ht)
  have hIB : (⨅ (a : B) (_ : a ∈ A) (_ : a ≠ 1),
      inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer {a})) = ⊥ := by
    have ht1 : t ≠ 1 := fun h => htinn (by rw [h]; exact one_mem _)
    have htcore : inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer {t}) = ⊥ := by
      rw [inSubgroup, hcore t htinn (hord t htA htinn), Subgroup.map_bot]
    exact eq_bot_iff.2 (iInf_le_of_le t (iInf_le_of_le htA (iInf_le_of_le ht1 htcore.le)))
  obtain ⟨φ, -, -, hφgen, hcardAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ hf hK
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨φ, hφgen⟩
  set ΘA : A →* (K ≃+* K) := Θ.comp (B.subtype.comp A.subtype)
  have hker : ∀ a : A, ΘA a = 1 ↔ ((a : B) : MulAut (adjointGroup .F4 K)) ∈ R := fun a => by
    have h := (MonoidHom.mem_ker (f := Θ) (x := ((a : B) : MulAut (adjointGroup .F4 K)))).symm
    rw [hΘker] at h
    exact h
  have hrange : Nat.card ΘA.range = p := by
    have hexp : Monoid.exponent ΘA.range ∣ p := by
      refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
      obtain ⟨_, a, rfl⟩ := g
      exact Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← map_pow, hApow, map_one])
    rw [IsCyclic.exponent_eq_card] at hexp
    rcases (Nat.dvd_prime hp).1 hexp with h1 | h1
    · exfalso
      have hmem : ΘA ⟨t, htA⟩ ∈ ΘA.range := ⟨⟨t, htA⟩, rfl⟩
      rw [Subgroup.card_eq_one.1 h1, Subgroup.mem_bot, hker] at hmem
      exact htinn hmem
    · exact h1
  have hcardA := Subgroup.card_mul_index ΘA.ker
  rw [Subgroup.index_ker, hrange, hAcard] at hcardA
  have hkercard : Nat.card ΘA.ker = p :=
    Nat.eq_of_mul_eq_mul_right hp.pos (by rw [hcardA, sq])
  have hkerEq : ΘA.ker = (R.comap B.subtype).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    rfl
  have hint : Nat.card ↥(A ⊓ R.comap B.subtype) = p := by
    rw [inf_comm, ← Subgroup.subgroupOf_map_subtype,
      Subgroup.card_map_of_injective A.subtype_injective, ← hkerEq, hkercard]
  refine ⟨hint, hIB, fun t' ht'A ht'inn => ?_⟩
  rw [hIB, inSubgroup, hcore t' ht'inn (hord t' ht'A ht'inn), Subgroup.map_bot,
    Subgroup.commutator_bot_left, Subgroup.coe_bot, Set.singleton_mul_singleton, mul_one]

end CFSG.RankThree.Chevalley
