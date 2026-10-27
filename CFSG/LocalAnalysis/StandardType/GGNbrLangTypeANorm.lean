module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangNorm
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism

public section

namespace CFSG.StandardType

namespace NbrLangTypeA

theorem prod_range_pow_eq_of_mem_zpowers {Γ M : Type*} [Group Γ] [CommMonoid M] {p : ℕ}
    (hp : p.Prime) {σ τ : Γ} (hσ : orderOf σ = p) (hτ : orderOf τ = p)
    (hστ : σ ∈ Subgroup.zpowers τ) (f : Γ → M) :
    ∏ i ∈ Finset.range p, f (σ ^ i) = ∏ i ∈ Finset.range p, f (τ ^ i) := by
  have hτfin : IsOfFinOrder τ := orderOf_pos_iff.mp (by rw [hτ]; exact hp.pos)
  obtain ⟨c, rfl⟩ : ∃ c : ℕ, τ ^ c = σ := (hτfin.mem_powers_iff_mem_zpowers).mpr hστ
  have hτp : τ ^ p = 1 := hτ ▸ pow_orderOf_eq_one τ
  have hpc : ¬ p ∣ c := by
    rintro ⟨c', rfl⟩
    rw [pow_mul, hτp, one_pow, orderOf_one] at hσ
    exact hp.one_lt.ne hσ
  have hcop : Nat.gcd p c = 1 := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpc
  have hinj : Set.InjOn (fun i => c * i % p) (Finset.range p : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have h1 : c * a ≡ c * b [MOD p] := hab
    have h2 := Nat.ModEq.cancel_left_of_coprime hcop h1
    rwa [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2
  have himg : (Finset.range p).image (fun i => c * i % p) = Finset.range p := by
    apply Finset.eq_of_subset_of_card_le
    · intro b hb
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hb
      exact Finset.mem_range.mpr (Nat.mod_lt _ hp.pos)
    · rw [Finset.card_image_of_injOn hinj]
  conv_rhs => rw [← himg]
  rw [Finset.prod_image hinj]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← pow_mul, show c * a % p = c * a % orderOf τ by rw [hτ], pow_mod_orderOf]

theorem frob_pow_apply {F : Type*} [Field F] {ℓ : ℕ} {φ : F ≃+* F} (hφ : ∀ a, φ a = a ^ ℓ)
    (g : ℕ) (a : F) : (φ ^ g) a = a ^ ℓ ^ g := by
  induction g generalizing a with
  | zero => simp
  | succ g ih =>
    rw [pow_succ]
    change (φ ^ g) (φ a) = _
    rw [hφ, ih, ← pow_mul, ← pow_succ']

@[expose] def fixingSubgroup {F : Type*} [Field F] (t : F) : Subgroup (F ≃+* F) where
  carrier := {g | g t = t}
  one_mem' := rfl
  mul_mem' := by
    intro a b ha hb
    change a (b t) = t
    rw [show b t = t from hb]
    exact ha
  inv_mem' := by
    intro a ha
    change a.symm t = t
    rw [RingEquiv.symm_apply_eq]
    exact ha.symm

theorem exists_prod_pow_eq {F : Type*} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    {σ : F ≃+* F} (hσ : orderOf σ = p) {t : F} (ht : σ t = t) (ht0 : t ≠ 0) :
    ∃ s : F, s ≠ 0 ∧ ∏ i ∈ Finset.range p, (σ ^ i) s = t := by
  classical
  have := Fintype.ofFinite F
  have hℓp : (ringChar F).Prime := CharP.char_is_prime F (ringChar F)
  obtain ⟨n, -, hn⟩ := FiniteField.card F (ringChar F)
  have hcard : Nat.card F = ringChar F ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  obtain ⟨φ, hφ, hφo, hφtop, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓp
      n.pos hcard
  have hφfin : IsOfFinOrder φ := orderOf_pos_iff.mp (by rw [hφo]; exact n.pos)
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, φ ^ k = σ :=
    hφfin.mem_powers_iff_mem_zpowers.mpr (hφtop ▸ Subgroup.mem_top σ)
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_one] at hσ
    exact hp.one_lt.ne hσ
  have hord : orderOf (φ ^ k) = (n : ℕ) / Nat.gcd n k := by rw [orderOf_pow' φ hk0, hφo]
  have hgpos : 0 < Nat.gcd (n : ℕ) k := Nat.gcd_pos_of_pos_left _ n.pos
  have hgn : Nat.gcd (n : ℕ) k ∣ n := Nat.gcd_dvd_left _ _
  have hng : (n : ℕ) = p * Nat.gcd n k := by
    have h1 : (n : ℕ) / Nat.gcd n k = p := hord.symm.trans hσ
    rw [← h1, Nat.div_mul_cancel hgn]
  set g := Nat.gcd (n : ℕ) k with hg
  set τ := φ ^ g with hτdef
  have hτo : orderOf τ = p := by
    rw [hτdef, orderOf_pow' φ hgpos.ne', hφo, Nat.gcd_eq_right hgn, hng,
      Nat.mul_div_cancel _ hgpos]
  have hστ : φ ^ k ∈ Subgroup.zpowers τ := by
    obtain ⟨k', hk'⟩ := Nat.gcd_dvd_right (n : ℕ) k
    have h1 : φ ^ k = τ ^ k' := by rw [hτdef, ← pow_mul, ← hk']
    rw [h1]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers τ) k'
  have : Finite (F ≃+* F) := Finite.of_injective _ DFunLike.coe_injective
  have hτσ : τ ∈ Subgroup.zpowers (φ ^ k) := by
    have hle : Subgroup.zpowers (φ ^ k) ≤ Subgroup.zpowers τ :=
      (Subgroup.zpowers_le).mpr hστ
    have heq : Subgroup.zpowers (φ ^ k) = Subgroup.zpowers τ := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hτo, hσ]
    rw [heq]
    exact Subgroup.mem_zpowers τ
  have hτt : τ t = t := ((Subgroup.zpowers_le).mpr ht : Subgroup.zpowers (φ ^ k) ≤
    fixingSubgroup t) hτσ
  have hτa : ∀ a : F, τ a = a ^ ringChar F ^ g := frob_pow_apply hφ g
  set q₀ := ringChar F ^ g with hq₀
  let β : MulAut Fˣ := Units.mapEquiv τ.toMulEquiv
  have hβ : ∀ u : Fˣ, β u = u ^ q₀ := fun u => Units.ext (by
    change τ (u : F) = ((u ^ q₀ : Fˣ) : F)
    rw [hτa, Units.val_pow_eq_pow_val])
  have hcardU : Nat.card Fˣ = q₀ ^ p - 1 := by
    rw [Nat.card_units, hcard, hng, mul_comm, pow_mul]
  have hβt : β (Units.mk0 t ht0) = Units.mk0 t ht0 := Units.ext (by
    change τ t = t
    exact hτt)
  obtain ⟨s, hs⟩ := NbrLang.norm_surjective_of_isCyclic hcardU hβ _ hβt
  refine ⟨s, s.ne_zero, ?_⟩
  rw [prod_range_pow_eq_of_mem_zpowers hp hσ hτo hστ (fun γ => γ (s : F))]
  have h1 := congrArg (fun u : Fˣ => (u : F)) hs
  simp only [Units.coe_prod, Units.val_mk0] at h1
  rw [← h1]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [NbrLang.pow_apply_eq_pow hβ, Units.val_pow_eq_pow_val, frob_pow_apply hτa]

end NbrLangTypeA

end CFSG.StandardType

end
