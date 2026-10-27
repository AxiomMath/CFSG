module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.RankThree.GF2n.Smith81.S81Z

open MonoidAlgebra

variable {K : Type} [Field K] [CharP K 2] {T : Type} [CommGroup T] {ι : Type}

noncomputable def charHom (χ : T →* Kˣ) : MonoidAlgebra ℤ T →+* K :=
  (MonoidAlgebra.lift ℤ K T ((Units.coeHom K).comp χ)).toRingHom

theorem charHom_single (χ : T →* Kˣ) (t : T) :
    charHom χ (MonoidAlgebra.single t 1) = ((χ t : Kˣ) : K) := by
  simp [charHom]

theorem charHom_surjective (χ : T →* Kˣ) (hχ : Function.Surjective χ) :
    Function.Surjective (charHom χ) := by
  intro x
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  · obtain ⟨t, ht⟩ := hχ (Units.mk0 x hx)
    refine ⟨MonoidAlgebra.single t 1, ?_⟩
    rw [charHom_single, ht]
    rfl

theorem exists_ringEquiv_of_ker_eq (χ ψ : T →* Kˣ) (hχ : Function.Surjective χ)
    (hψ : Function.Surjective ψ) (h : RingHom.ker (charHom χ) = RingHom.ker (charHom ψ)) :
    ∃ σ : K ≃+* K, ∀ t, σ ((χ t : Kˣ) : K) = (ψ t : Kˣ) := by
  let e1 := RingHom.quotientKerEquivOfSurjective (charHom_surjective χ hχ)
  let e2 := RingHom.quotientKerEquivOfSurjective (charHom_surjective ψ hψ)
  let σ : K ≃+* K := (e1.symm.trans (Ideal.quotEquivOfEq h)).trans e2
  refine ⟨σ, fun t => ?_⟩
  have h1 : e1.symm (((χ t : Kˣ) : K)) = Ideal.Quotient.mk _ (MonoidAlgebra.single t 1) := by
    rw [RingEquiv.symm_apply_eq]
    simp [e1, charHom_single]
  show e2 ((Ideal.quotEquivOfEq h) (e1.symm ((χ t : Kˣ) : K))) = _
  rw [h1]
  simp [e2, charHom_single]

theorem intCast_eq_ite (b : ℤ) : ((b : ℤ) : K) = if Even b then 0 else 1 := by
  rcases Int.even_or_odd' b with ⟨k, hk | hk⟩
  · subst hk
    have : Even (2 * k) := even_two_mul k
    rw [if_pos this, Int.cast_mul]
    simp [CharTwo.two_eq_zero]
  · subst hk
    have : ¬ Even (2 * k + 1) := by simpa using Int.not_even_two_mul_add_one k
    rw [if_neg this, Int.cast_add, Int.cast_mul]
    simp [CharTwo.two_eq_zero]

theorem charHom_eq_sum (χ : T →* Kˣ) (x : MonoidAlgebra ℤ T) :
    charHom χ x = ∑ t ∈ x.coeff.support.filter (fun t => ¬ Even (x.coeff t)),
      ((χ t : Kˣ) : K) := by
  classical
  rw [Finset.sum_filter]
  show (MonoidAlgebra.lift ℤ K T ((Units.coeHom K).comp χ)) x = _
  rw [MonoidAlgebra.lift_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [zsmul_eq_mul, intCast_eq_ite]
  by_cases h : Even (x.coeff t)
  · simp [h]
  · simp [h]

theorem exists_finset_char_sum [Finite ι] (χ : ι → T →* Kˣ)
    (hsurj : ∀ i, Function.Surjective (χ i))
    (hne : ∀ i j, i ≠ j → ∀ σ : K ≃+* K, ∃ t, σ ((χ i t : Kˣ) : K) ≠ (χ j t : Kˣ))
    (b : ι → K) : ∃ S : Finset T, ∀ i, ∑ t ∈ S, ((χ i t : Kˣ) : K) = b i := by
  classical
  have hmax : ∀ i, (RingHom.ker (charHom (χ i))).IsMaximal := fun i =>
    RingHom.ker_isMaximal_of_surjective _ (charHom_surjective _ (hsurj i))
  have hcop : Pairwise (Function.onFun IsCoprime fun i => RingHom.ker (charHom (χ i))) := by
    intro i j hij
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
    refine (hmax i).coprime_of_ne (hmax j) fun h => ?_
    obtain ⟨σ, hσ⟩ := exists_ringEquiv_of_ker_eq (χ i) (χ j) (hsurj i) (hsurj j) h
    obtain ⟨t, ht⟩ := hne i j hij σ
    exact ht (hσ t)
  choose r hr using fun i => charHom_surjective (χ i) (hsurj i) (b i)
  obtain ⟨x, hx⟩ := Ideal.exists_forall_sub_mem_ideal hcop r
  have hρ : ∀ i, charHom (χ i) x = b i := fun i => by
    have h1 := (RingHom.mem_ker).1 (hx i)
    rw [map_sub, hr i, sub_eq_zero] at h1
    exact h1
  refine ⟨x.coeff.support.filter fun t => ¬ Even (x.coeff t), fun i => ?_⟩
  rw [← hρ i, charHom_eq_sum]

section Layer

variable [Fintype ι] [DecidableEq ι]

@[expose] def coordSub (K : Type) [Field K] (A : Finset ι) : AddSubgroup (ι → K) where
  carrier := {c | ∀ i, i ∉ A → c i = 0}
  add_mem' := fun {a b} ha hb i hi => by simp [ha i hi, hb i hi]
  zero_mem' := fun i _ => rfl
  neg_mem' := fun {a} ha i hi => by simp [ha i hi]

open _root_.Classical in
theorem eq_coordSub (χ : ι → T →* Kˣ) (hsurj : ∀ i, Function.Surjective (χ i))
    (hne : ∀ i j, i ≠ j → ∀ σ : K ≃+* K, ∃ t, σ ((χ i t : Kˣ) : K) ≠ (χ j t : Kˣ))
    (S : AddSubgroup (ι → K))
    (hS : ∀ t : T, ∀ c ∈ S, (fun i => ((χ i t : Kˣ) : K) * c i) ∈ S) :
    S = coordSub K (Finset.univ.filter fun i => ∃ c ∈ S, c i ≠ 0) := by
  classical
  ext c
  constructor
  · intro hc i hi
    by_contra hci
    exact hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, c, hc, hci⟩)
  · intro hc
    have hsingle : ∀ i, (∃ c' ∈ S, c' i ≠ 0) → ∀ y : K, Pi.single i y ∈ S := by
      intro i ⟨c', hc'S, hc'i⟩ y
      obtain ⟨F, hF⟩ := exists_finset_char_sum χ hsurj hne (Pi.single i (1 : K))
      have hproj : Pi.single i (c' i) ∈ S := by
        have hmem : (∑ t ∈ F, fun j => ((χ j t : Kˣ) : K) * c' j) ∈ S :=
          AddSubgroup.sum_mem _ fun t _ => hS t c' hc'S
        convert hmem using 1
        funext j
        rw [Finset.sum_apply]
        simp only [← Finset.sum_mul, hF j]
        by_cases hj : j = i
        · subst hj; simp
        · simp [Pi.single_apply, hj]
      by_cases hy : y = 0
      · simp [hy]
      · obtain ⟨t, ht⟩ := hsurj i (Units.mk0 (y / c' i) (div_ne_zero hy hc'i))
        have h2 := hS t _ hproj
        convert h2 using 1
        funext j
        by_cases hj : j = i
        · subst hj
          simp only [Pi.single_eq_same, ht, Units.val_mk0]
          field_simp
        · simp [Pi.single_apply, hj]
    have : c = ∑ i, Pi.single i (c i) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [this]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    by_cases hci : c i = 0
    · simp [hci]
    · have hiA : i ∈ Finset.univ.filter fun i => ∃ c ∈ S, c i ≠ 0 := by
        by_contra hi
        exact hci (hc i hi)
      obtain ⟨-, c', hc'S, hc'i⟩ := Finset.mem_filter.1 hiA
      exact hsingle i ⟨c', hc'S, hc'i⟩ (c i)

theorem card_coordSub [Finite K] (A : Finset ι) :
    Nat.card (coordSub K A) = Nat.card K ^ A.card := by
  classical
  have e : coordSub K A ≃ (A → K) :=
    { toFun := fun c i => c.1 i
      invFun := fun f => ⟨fun i => if h : i ∈ A then f ⟨i, h⟩ else 0, fun i hi => by simp [hi]⟩
      left_inv := fun c => by
        apply Subtype.ext
        funext i
        by_cases h : i ∈ A
        · simp [h]
        · simp [h, c.2 i h]
      right_inv := fun f => by
        funext i
        simp [i.2] }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := A), Fintype.card_coe]

end Layer

end CFSG.RankThree.GF2n.Smith81.S81Z
