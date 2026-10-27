module

public import CFSG.RankThree.Classical.SteinbergBJCharacterSpaces
public import CFSG.LieType.BorelTits.FormFlag

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof

open CFSG.RankThree.Classical CFSG.LieType.BorelTits Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable {Γ : Type*} [CommGroup Γ] [Fintype Γ] {ρ : Γ →* Module.End K V} {ζ : K}

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem form_eq_zero_of_mem_charSpace (F : ReflForm K V) (hζ : IsPrimitiveRoot ζ 3)
    (hσζ : F.σ ζ = ζ) (hρ : ∀ g u v, F.β (ρ g u) (ρ g v) = F.β u v)
    {χ ψ : Additive Γ →+ ZMod 3} (h : χ + ψ ≠ 0) {v w : V} (hv : v ∈ charSpace ρ ζ χ)
    (hw : w ∈ charSpace ρ ζ ψ) : F.β v w = 0 := by
  obtain ⟨g, hg⟩ : ∃ g : Γ, (χ + ψ) (Additive.ofMul g) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h (AddMonoidHom.ext fun x => hcon (Additive.toMul x))
  have h1 : ζ ^ ((χ + ψ) (Additive.ofMul g)).val ≠ 1 := fun h1 =>
    hg ((root_pow_val_eq_one_iff hζ _).mp h1)
  have key : F.β v w = ζ ^ ((χ + ψ) (Additive.ofMul g)).val * F.β v w := by
    conv_lhs => rw [← hρ g v w, (mem_charSpace.mp hv) g, (mem_charSpace.mp hw) g]
    rw [F.smul_left, F.smul_right, map_pow, hσζ, ← mul_assoc,
      ← root_pow_val_add hζ.pow_eq_one, AddMonoidHom.add_apply]
  have : (ζ ^ ((χ + ψ) (Additive.ofMul g)).val - 1) * F.β v w = 0 := by
    rw [sub_mul, ← key, one_mul, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h1)

theorem form_eq_zero_of_forall_charSpace [Fintype (Additive Γ →+ ZMod 3)] (F : ReflForm K V)
    (hζ : IsPrimitiveRoot ζ 3) (hexp : ∀ g : Γ, g ^ 3 = 1) (hΓ : (Fintype.card Γ : K) ≠ 0)
    {v : V} (h : ∀ ψ : Additive Γ →+ ZMod 3, ∀ w ∈ charSpace ρ ζ ψ, F.β w v = 0) (w : V) :
    F.β w v = 0 := by
  have hw := eq_sum_charIdem_apply (ρ := ρ) Nat.prime_three hζ hexp hΓ w
  have key : ∀ s : Finset (Additive Γ →+ ZMod 3),
      F.β (∑ χ ∈ s, charIdem ρ ζ χ w) v = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, F.β_zero_left]
    | insert χ s hχ ih =>
      rw [Finset.sum_insert hχ, F.add_left, ih, add_zero]
      exact h χ _ (charIdem_apply_mem hζ.pow_eq_one χ w)
  rw [hw]
  exact key Finset.univ

theorem charSpace_inf_perp_neg [Fintype (Additive Γ →+ ZMod 3)] (F : ReflForm K V)
    (hζ : IsPrimitiveRoot ζ 3) (hσζ : F.σ ζ = ζ) (hρ : ∀ g u v, F.β (ρ g u) (ρ g v) = F.β u v)
    (hexp : ∀ g : Γ, g ^ 3 = 1) (hΓ : (Fintype.card Γ : K) ≠ 0) (χ : Additive Γ →+ ZMod 3) :
    charSpace ρ ζ χ ⊓ F.perp (charSpace ρ ζ (-χ)) = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨hv, hvp⟩
  rw [Submodule.mem_bot]
  have hall : ∀ w, F.β w v = 0 := form_eq_zero_of_forall_charSpace F hζ hexp hΓ fun ψ w hw => by
    by_cases hψ : ψ = -χ
    · subst hψ
      exact hvp w hw
    · exact form_eq_zero_of_mem_charSpace F hζ hσζ hρ
        (fun h => hψ (eq_neg_of_add_eq_zero_left h)) hw hv
  exact F.nondeg v fun w => F.refl _ _ (hall w)

theorem finrank_charSpace_le_neg' [FiniteDimensional K V] [Fintype (Additive Γ →+ ZMod 3)]
    (F : ReflForm K V) (hζ : IsPrimitiveRoot ζ 3) (hσζ : F.σ ζ = ζ)
    (hρ : ∀ g u v, F.β (ρ g u) (ρ g v) = F.β u v) (hexp : ∀ g : Γ, g ^ 3 = 1)
    (hΓ : (Fintype.card Γ : K) ≠ 0) (χ : Additive Γ →+ ZMod 3) :
    finrank K (charSpace ρ ζ χ) ≤ finrank K (charSpace ρ ζ (-χ)) := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (charSpace ρ ζ χ)
    (F.perp (charSpace ρ ζ (-χ)))
  rw [charSpace_inf_perp_neg F hζ hσζ hρ hexp hΓ χ, finrank_bot, add_zero] at h1
  have h2 := F.finrank_perp (charSpace ρ ζ (-χ))
  have h3 := Submodule.finrank_le (charSpace ρ ζ χ ⊔ F.perp (charSpace ρ ζ (-χ)))
  omega

theorem finrank_charSpace_neg' [FiniteDimensional K V] [Fintype (Additive Γ →+ ZMod 3)]
    (F : ReflForm K V) (hζ : IsPrimitiveRoot ζ 3) (hσζ : F.σ ζ = ζ)
    (hρ : ∀ g u v, F.β (ρ g u) (ρ g v) = F.β u v) (hexp : ∀ g : Γ, g ^ 3 = 1)
    (hΓ : (Fintype.card Γ : K) ≠ 0) (χ : Additive Γ →+ ZMod 3) :
    finrank K (charSpace ρ ζ (-χ)) = finrank K (charSpace ρ ζ χ) := by
  refine le_antisymm ?_ (finrank_charSpace_le_neg' F hζ hσζ hρ hexp hΓ χ)
  have := finrank_charSpace_le_neg' F hζ hσζ hρ hexp hΓ (-χ)
  rwa [neg_neg] at this

omit [Fintype Γ] in
theorem three_nsmul_char (χ : Additive Γ →+ ZMod 3) : (3 : ℕ) • χ = 0 := by
  refine AddMonoidHom.ext fun x => ?_
  rw [AddMonoidHom.nsmul_apply, AddMonoidHom.zero_apply, nsmul_eq_mul,
    show ((3 : ℕ) : ZMod 3) = 0 from ZMod.natCast_self 3, zero_mul]

omit [Fintype Γ] in
theorem neg_ne_self_of_ne_zero {χ : Additive Γ →+ ZMod 3} (hχ : χ ≠ 0) : -χ ≠ χ := by
  intro h
  apply hχ
  have h2 : χ + χ = 0 := by
    nth_rewrite 1 [← h]
    exact neg_add_cancel χ
  have h3 : (3 : ℕ) • χ = χ + χ + χ := by
    rw [succ_nsmul, two_nsmul]
  rw [three_nsmul_char, h2, zero_add] at h3
  exact h3.symm

theorem exists_two_supported [Fintype (Additive Γ →+ ZMod 3)] (hζ : IsPrimitiveRoot ζ 3)
    (hexp : ∀ g : Γ, g ^ 3 = 1) (hΓ : (Fintype.card Γ : K) ≠ 0) (hcard : Nat.card Γ = 9)
    (hfaith : ∀ g, ρ g = 1 → g = 1) :
    ∃ χ₁ χ₂ : Additive Γ →+ ZMod 3, χ₁ ≠ 0 ∧ charSpace ρ ζ χ₁ ≠ ⊥ ∧ χ₂ ≠ 0 ∧
      charSpace ρ ζ χ₂ ≠ ⊥ ∧ χ₂ ≠ χ₁ ∧ χ₂ ≠ -χ₁ := by
  have hcl := closure_support_charSpace_eq_top (ρ := ρ) Nat.prime_three hζ hexp hΓ hfaith
  set S := {χ : Additive Γ →+ ZMod 3 | χ ≠ 0 ∧ charSpace ρ ζ χ ≠ ⊥} with hS
  have hcardD : Nat.card (Additive Γ →+ ZMod 3) = 9 := by
    rw [natCard_char Nat.prime_three hexp, hcard]
  obtain ⟨χ₁, hχ₁⟩ : S.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, AddSubgroup.closure_empty] at hcl
    have := congrArg (fun H : AddSubgroup (Additive Γ →+ ZMod 3) => Nat.card H) hcl
    simp only [AddSubgroup.card_bot, AddSubgroup.card_top, hcardD] at this
    norm_num at this
  obtain ⟨χ₂, hχ₂, hχ₂m⟩ : ∃ χ₂ ∈ S, χ₂ ∉ AddSubgroup.zmultiples χ₁ := by
    by_contra hall
    push Not at hall
    have hle : AddSubgroup.closure S ≤ AddSubgroup.zmultiples χ₁ :=
      (AddSubgroup.closure_le _).mpr hall
    rw [hcl] at hle
    have h1 := AddSubgroup.card_le_of_le hle
    rw [AddSubgroup.card_top, hcardD, Nat.card_zmultiples] at h1
    have h3 : addOrderOf χ₁ ∣ 3 := addOrderOf_dvd_of_nsmul_eq_zero (three_nsmul_char χ₁)
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  refine ⟨χ₁, χ₂, hχ₁.1, hχ₁.2, hχ₂.1, hχ₂.2, fun h => hχ₂m ?_, fun h => hχ₂m ?_⟩
  · rw [h]
    exact AddSubgroup.mem_zmultiples χ₁
  · rw [h]
    exact neg_mem (AddSubgroup.mem_zmultiples χ₁)

theorem weights_dim_four_five [FiniteDimensional K V] [Fintype (Additive Γ →+ ZMod 3)]
    [DecidableEq (Additive Γ →+ ZMod 3)] (F : ReflForm K V) (hζ : IsPrimitiveRoot ζ 3)
    (hσζ : F.σ ζ = ζ) (hρ : ∀ g u v, F.β (ρ g u) (ρ g v) = F.β u v)
    (hexp : ∀ g : Γ, g ^ 3 = 1) (hΓ : (Fintype.card Γ : K) ≠ 0) (hcard : Nat.card Γ = 9)
    (hfaith : ∀ g, ρ g = 1 → g = 1) (hdim : finrank K V = 4 ∨ finrank K V = 5) :
    (∀ χ : Additive Γ →+ ZMod 3, finrank K (charSpace ρ ζ χ) ≤ 1) ∧
      finrank K (charSpace ρ ζ (0 : Additive Γ →+ ZMod 3)) + 4 = finrank K V := by
  obtain ⟨χ₁, χ₂, h1, h1', h2, h2', h21, h21'⟩ :=
    exists_two_supported hζ hexp hΓ hcard hfaith (ρ := ρ)
  set d : (Additive Γ →+ ZMod 3) → ℕ := fun χ => finrank K (charSpace ρ ζ χ) with hd
  have hsum : ∑ χ, d χ = finrank K V := sum_finrank_charSpace Nat.prime_three hζ hexp hΓ
  have hneg : ∀ χ, d (-χ) = d χ := fun χ => finrank_charSpace_neg' F hζ hσζ hρ hexp hΓ χ
  have hpos : ∀ χ, charSpace ρ ζ χ ≠ ⊥ → 1 ≤ d χ := fun χ hχ => by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    exact hχ (Submodule.finrank_eq_zero.mp h0)
  have hd1 : 1 ≤ d χ₁ := hpos χ₁ h1'
  have hd2 : 1 ≤ d χ₂ := hpos χ₂ h2'
  have n11 : χ₁ ≠ -χ₁ := (neg_ne_self_of_ne_zero h1).symm
  have n22 : χ₂ ≠ -χ₂ := (neg_ne_self_of_ne_zero h2).symm
  have n3 : -χ₂ ≠ χ₁ := fun h => h21' (by rw [← h, neg_neg])
  have n4 : -χ₂ ≠ -χ₁ := fun h => h21 (neg_injective h)
  set S4 : Finset (Additive Γ →+ ZMod 3) := {χ₁, -χ₁, χ₂, -χ₂} with hS4
  have hS4sum : ∑ χ ∈ S4, d χ = d χ₁ + d (-χ₁) + (d χ₂ + d (-χ₂)) := by
    rw [hS4, Finset.sum_insert (by simp [n11, Ne.symm h21, Ne.symm n3]),
      Finset.sum_insert (by simp [Ne.symm h21', Ne.symm n4]),
      Finset.sum_pair n22]
    ring
  have hsplit := Finset.sum_add_sum_compl S4 d
  rw [hsum, hS4sum, hneg, hneg] at hsplit
  have hmemS4 : ∀ χ, χ ∈ S4 ↔ χ = χ₁ ∨ χ = -χ₁ ∨ χ = χ₂ ∨ χ = -χ₂ := fun χ => by
    simp [hS4]
  have hnegmem : ∀ χ, χ ∈ S4 → -χ ∈ S4 := fun χ hχ => by
    rw [hmemS4] at hχ ⊢
    rcases hχ with rfl | rfl | rfl | rfl <;> simp
  have h0S4 : (0 : Additive Γ →+ ZMod 3) ∉ S4 := by
    rw [hmemS4]
    rintro (h | h | h | h)
    · exact h1 h.symm
    · exact h1 (neg_eq_zero.mp h.symm)
    · exact h2 h.symm
    · exact h2 (neg_eq_zero.mp h.symm)
  have hout : ∀ χ ∉ S4, χ ≠ 0 → d χ = 0 := by
    intro χ hχ hχ0
    by_contra hne
    have hnχ : -χ ∉ S4 := fun h => hχ (by simpa using hnegmem _ h)
    have hle : d χ + d (-χ) ≤ ∑ ψ ∈ S4ᶜ, d ψ := by
      rw [← Finset.sum_pair (neg_ne_self_of_ne_zero hχ0).symm]
      exact Finset.sum_le_sum_of_subset (by
        intro ψ hψ
        rw [Finset.mem_insert, Finset.mem_singleton] at hψ
        rw [Finset.mem_compl]
        rcases hψ with rfl | rfl
        · exact hχ
        · exact hnχ)
    rw [hneg] at hle
    omega
  have hcompl : ∑ ψ ∈ S4ᶜ, d ψ = d 0 := by
    refine Finset.sum_eq_single 0 (fun χ hχ hχ0 => hout χ (Finset.mem_compl.mp hχ) hχ0) ?_
    intro h
    exact absurd (Finset.mem_compl.mpr h0S4) h
  rw [hcompl] at hsplit
  have hvals : d χ₁ = 1 ∧ d χ₂ = 1 ∧ d 0 + 4 = finrank K V := by
    rcases hdim with h | h <;> omega
  refine ⟨fun χ => ?_, hvals.2.2⟩
  by_cases hχ : χ ∈ S4
  · rw [hmemS4] at hχ
    rcases hχ with rfl | rfl | rfl | rfl
    · exact hvals.1.le
    · exact (hneg _).trans hvals.1 |>.le
    · exact hvals.2.1.le
    · exact (hneg _).trans hvals.2.1 |>.le
  · by_cases hχ0 : χ = 0
    · rw [hχ0]
      show d 0 ≤ 1
      have := hvals.2.2
      rcases hdim with h | h <;> omega
    · show d χ ≤ 1
      rw [hout χ hχ hχ0]
      exact Nat.zero_le 1

theorem eq_one_of_commute_of_pow [FiniteDimensional K V] [Fintype (Additive Γ →+ ZMod 3)]
    [Fact (Nat.Prime 2)] [CharP K 2] (hζ : IsPrimitiveRoot ζ 3) (hexp : ∀ g : Γ, g ^ 3 = 1)
    (hΓ : (Fintype.card Γ : K) ≠ 0)
    (hle : ∀ χ : Additive Γ →+ ZMod 3, finrank K (charSpace ρ ζ χ) ≤ 1)
    {u : Module.End K V} {k : ℕ} (hu : u ^ 2 ^ k = 1) (hcomm : ∀ g, u * ρ g = ρ g * u) :
    u = 1 := by
  have hχ : ∀ χ : Additive Γ →+ ZMod 3, ∀ v ∈ charSpace ρ ζ χ, u v = v := by
    intro χ v hv
    have huv : u v ∈ charSpace ρ ζ χ := by
      rw [mem_charSpace] at hv ⊢
      intro g
      rw [← Module.End.mul_apply, ← hcomm g, Module.End.mul_apply, hv g, map_smul]
    by_cases hv0 : v = 0
    · rw [hv0, map_zero]
    · have hspan : charSpace ρ ζ χ = K ∙ v := by
        symm
        apply Submodule.eq_of_le_of_finrank_le
        · exact (Submodule.span_singleton_le_iff_mem v _).mpr hv
        · rw [finrank_span_singleton hv0]
          exact hle χ
      have huv' : u v ∈ K ∙ v := hspan ▸ huv
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp huv'
      have hpow : ∀ j : ℕ, (u ^ j) v = c ^ j • v := by
        intro j
        induction j with
        | zero => simp
        | succ j ih =>
          rw [pow_succ', Module.End.mul_apply, ih, map_smul, ← hc, smul_smul, pow_succ',
            mul_comm]
      have h1 := hpow (2 ^ k)
      rw [hu, Module.End.one_apply] at h1
      have hc1 : c ^ 2 ^ k = 1 := by
        have h2 : (c ^ 2 ^ k - 1) • v = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
        exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hv0)
      have hc1' : c = 1 := by
        have h3 : (c - 1) ^ 2 ^ k = 0 := by rw [sub_pow_char_pow, hc1, one_pow, sub_self]
        exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero h3)
      rw [← hc, hc1', one_smul]
  ext v
  rw [Module.End.one_apply]
  conv_lhs => rw [eq_sum_charIdem_apply (ρ := ρ) Nat.prime_three hζ hexp hΓ v]
  rw [map_sum]
  conv_rhs => rw [eq_sum_charIdem_apply (ρ := ρ) Nat.prime_three hζ hexp hΓ v]
  exact Finset.sum_congr rfl fun χ _ => hχ χ _ (charIdem_apply_mem hζ.pow_eq_one χ v)

end CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof
