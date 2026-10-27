module

public import CFSG.Quasithin.EmptyFaithful.SzC4ChiApi
public import CFSG.Quasithin.EmptyFaithful.SzC4ChiGrpSq

public section

namespace CFSG.Quasithin.SzC4

@[expose] def restrictEquiv {M M' : Type} [Group M] [Group M'] (e : M ≃* M') (H : Subgroup M)
    (H' : Subgroup M') (h : ∀ x, e x ∈ H' ↔ x ∈ H) : H ≃* H' where
  toFun x := ⟨e x, (h x).2 x.2⟩
  invFun y := ⟨e.symm y, (h _).1 (by simp)⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := by ext; simp

@[simp] theorem restrictEquiv_apply {M M' : Type} [Group M] [Group M'] (e : M ≃* M')
    (H : Subgroup M) (H' : Subgroup M') (h : ∀ x, e x ∈ H' ↔ x ∈ H) (x : H) :
    ((restrictEquiv e H H' h x : H') : M') = e x := rfl

theorem sq_equiv_iff {M M' : Type} [Group M] [Group M'] (e : M ≃* M') (x : M) :
    e x ∈ sq M' ↔ x ∈ sq M := by
  rw [← sq_map_eq (e : M →* M') e.surjective]
  exact Subgroup.mem_map_iff_mem e.injective

@[expose] def sqQuotAut {M : Type} [Group M] (φ : MulAut M) : MulAut (M ⧸ sq M) :=
  quotAut (sq M) φ (sq_invariant φ)

@[expose] def sqRestrictAut {M : Type} [Group M] (φ : MulAut M) : MulAut (sq M) :=
  restrictAut φ (sq M) (sq_invariant φ)

open scoped Classical in
@[expose] noncomputable def chi (D : DeltaAPI) (M : Type) [Group M] [Finite M] (φ : MulAut M) :
    ℤ :=
  if _h : IsPGroup 2 M ∧ φ ^ 7 = 1 ∧ Nontrivial M then
    D.delta (M ⧸ sq M) (sqQuotAut φ) + chi D (sq M) (sqRestrictAut φ)
  else 0
termination_by Nat.card M
decreasing_by
  have : Nontrivial M := _h.2.2
  exact sq_lt_of_isPGroup _h.1

theorem chi_eq_zero_of_not (D : DeltaAPI) {M : Type} [Group M] [Finite M] (φ : MulAut M)
    (h : ¬(IsPGroup 2 M ∧ φ ^ 7 = 1 ∧ Nontrivial M)) : chi D M φ = 0 := by
  rw [chi, dite_eq_right h]

theorem chi_eq_of (D : DeltaAPI) {M : Type} [Group M] [Finite M] [Nontrivial M] (φ : MulAut M)
    (h2 : IsPGroup 2 M) (h7 : φ ^ 7 = 1) :
    chi D M φ = D.delta (M ⧸ sq M) (sqQuotAut φ) + chi D (sq M) (sqRestrictAut φ) := by
  rw [chi, dite_eq_left ⟨h2, h7, inferInstance⟩]

theorem chi_of_subsingleton (D : DeltaAPI) {M : Type} [Group M] [Finite M] [Subsingleton M]
    (φ : MulAut M) : chi D M φ = 0 :=
  chi_eq_zero_of_not D φ fun h => not_nontrivial_iff_subsingleton.2 ‹_› h.2.2

theorem delta_of_subsingleton (D : DeltaAPI) {A : Type} [Group A] [Finite A] [Subsingleton A]
    (φ : MulAut A) : D.delta A φ = 0 := by
  have h1 : φ = 1 := by ext x; exact Subsingleton.elim _ _
  rw [h1]
  exact D.delta_one A fun x => Subsingleton.elim _ _

theorem chi_unfold (D : DeltaAPI) {M : Type} [Group M] [Finite M] (φ : MulAut M)
    (h2 : IsPGroup 2 M) (h7 : φ ^ 7 = 1) :
    chi D M φ = D.delta (M ⧸ sq M) (sqQuotAut φ) + chi D (sq M) (sqRestrictAut φ) := by
  by_cases hM : Nontrivial M
  · exact chi_eq_of D φ h2 h7
  · rw [not_nontrivial_iff_subsingleton] at hM
    have hq : Subsingleton (M ⧸ sq M) := QuotientGroup.mk_surjective.subsingleton
    have hs : Subsingleton (sq M) := inferInstance
    rw [chi_of_subsingleton, delta_of_subsingleton, chi_of_subsingleton, add_zero]

theorem chi_one (D : DeltaAPI) (M : Type) [Group M] [Finite M] : chi D M 1 = 0 := by
  suffices H : ∀ (n : ℕ) (M : Type) [Group M] [Finite M], Nat.card M = n → chi D M 1 = 0 from
    H _ M rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M _ _ hn
    by_cases hc : IsPGroup 2 M ∧ (1 : MulAut M) ^ 7 = 1 ∧ Nontrivial M
    · obtain ⟨h2, h7, hnt⟩ := hc
      have e1 : sqQuotAut (1 : MulAut M) = 1 := by
        ext x
        induction x using QuotientGroup.induction_on with
        | H m => rfl
      have e2 : sqRestrictAut (1 : MulAut M) = 1 := by ext x; rfl
      rw [chi_eq_of D 1 h2 h7, e1, e2, D.delta_one _ quotient_sq_exp,
        ih (Nat.card (sq M)) (lt_of_lt_of_eq (sq_lt_of_isPGroup h2) hn) (sq M) rfl, add_zero]
    · exact chi_eq_zero_of_not D 1 hc

theorem chi_congr (D : DeltaAPI) {M M' : Type} [Group M] [Group M'] [Finite M] [Finite M']
    (e : M ≃* M') (φ : MulAut M) (φ' : MulAut M') (h : ∀ x : M, e (φ x) = φ' (e x)) :
    chi D M' φ' = chi D M φ := by
  suffices H : ∀ (n : ℕ) (M M' : Type) [Group M] [Group M'] [Finite M] [Finite M'],
      Nat.card M = n → ∀ (e : M ≃* M') (φ : MulAut M) (φ' : MulAut M'),
      (∀ x : M, e (φ x) = φ' (e x)) → chi D M' φ' = chi D M φ from H _ M M' rfl e φ φ' h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M M' _ _ _ _ hn e φ φ' h
    by_cases hc : IsPGroup 2 M ∧ φ ^ 7 = 1 ∧ Nontrivial M
    · obtain ⟨h2, h7, hnt⟩ := hc
      have h2' : IsPGroup 2 M' := h2.of_equiv e
      have h7' : φ' ^ 7 = 1 :=
        pow_eq_one_of_surjective (e : M →* M') e.surjective φ φ' (fun x => (h x).symm) 7 h7
      have hnt' : Nontrivial M' := e.toEquiv.nontrivial_congr.1 hnt
      rw [chi_eq_of D φ h2 h7, chi_eq_of D φ' h2' h7']
      have c1 : D.delta (M' ⧸ sq M') (sqQuotAut φ') = D.delta (M ⧸ sq M) (sqQuotAut φ) := by
        refine D.delta_congr quotient_sq_exp
          (QuotientGroup.congr (sq M) (sq M') e (sq_map_eq (e : M →* M') e.surjective)) _ _ ?_
        intro x
        induction x using QuotientGroup.induction_on with
        | H m => exact congrArg QuotientGroup.mk (h m)
      have c2 : chi D (sq M') (sqRestrictAut φ') = chi D (sq M) (sqRestrictAut φ) := by
        refine ih (Nat.card (sq M)) (lt_of_lt_of_eq (sq_lt_of_isPGroup h2) hn) (sq M) (sq M') rfl
          (restrictEquiv e (sq M) (sq M') (sq_equiv_iff e)) _ _ ?_
        intro x
        ext
        exact h x
      rw [c1, c2]
    · have hc' : ¬(IsPGroup 2 M' ∧ φ' ^ 7 = 1 ∧ Nontrivial M') := by
        rintro ⟨h2', h7', hnt'⟩
        refine hc ⟨h2'.of_equiv e.symm, ?_, e.toEquiv.nontrivial_congr.2 hnt'⟩
        exact pow_eq_one_of_injective (e : M →* M') e.injective φ φ' (fun x => (h x).symm) 7 h7'
      rw [chi_eq_zero_of_not D φ' hc', chi_eq_zero_of_not D φ hc]

theorem isPGroup_two_of_isExpTwo {M : Type} [Group M] (hM : IsExpTwo M) : IsPGroup 2 M :=
  fun g => ⟨1, by rw [pow_one, pow_two]; exact hM g⟩

theorem chi_of_isExpTwo (D : DeltaAPI) (M : Type) [Group M] [Finite M] (hM : IsExpTwo M)
    (φ : MulAut M) (h7 : φ ^ 7 = 1) : chi D M φ = D.delta M φ := by
  have hb : sq M = ⊥ := le_bot_iff.1 ((Subgroup.closure_le ⊥).2 (by
    rintro _ ⟨y, rfl⟩
    simp [hM y]))
  have hz : ∀ z ∈ sq M, z = 1 := fun z hz => by
    rw [hb] at hz
    exact Subgroup.mem_bot.1 hz
  have hs : Subsingleton (sq M) := ⟨fun x y => Subtype.ext ((hz x x.2).trans (hz y y.2).symm)⟩
  rw [chi_unfold D φ (isPGroup_two_of_isExpTwo hM) h7, chi_of_subsingleton, add_zero]
  have hinj : Function.Injective (QuotientGroup.mk' (sq M)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hb]
  exact D.delta_congr hM
    (MulEquiv.ofBijective (QuotientGroup.mk' (sq M)) ⟨hinj, QuotientGroup.mk'_surjective _⟩)
    φ _ (fun x => rfl)

end CFSG.Quasithin.SzC4
