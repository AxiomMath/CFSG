module

public import CFSG.Walter.Ree.Thompson1.Eigen
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.Walter.Ree.Thompson1

open Finset

variable {K : Type*} [Field K] [Fintype K]

theorem exists_addEquiv_of_exponent_three [CharP K 3] {A : Type*} [CommGroup A] [Finite A]
    (h3 : ∀ a : A, a ^ 3 = 1) (hcard : Nat.card A = Fintype.card K) :
    Nonempty (Additive A ≃+ K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : Module (ZMod 3) (Additive A) := AddCommGroup.zmodModule (n := 3) fun x => by
    have := h3 x.toMul
    exact toMul_eq_one.mp (by rw [toMul_nsmul]; exact this)
  let _ : Algebra (ZMod 3) K := ZMod.algebra K 3
  have hA := FiniteField.pow_finrank_eq_natCard 3 (Additive A)
  have hK := FiniteField.pow_finrank_eq_natCard 3 K
  have hfr : Module.finrank (ZMod 3) (Additive A) = Module.finrank (ZMod 3) K := by
    apply Nat.pow_right_injective (by norm_num : 2 ≤ 3)
    simp only
    rw [hA, hK, Nat.card_eq_fintype_card (α := K), ← hcard]
    exact Nat.card_congr Additive.toMul
  exact ⟨(LinearEquiv.ofFinrankEq _ _ hfr).toAddEquiv⟩

variable {N : Type*} [Group N]

theorem surjective_of_card [Finite N] {S T : Subgroup N} (hTS : T ≤ S) (θ : N → K)
    (hadd : ∀ x ∈ S, ∀ y ∈ S, θ (x * y) = θ x + θ y) (hker : ∀ x ∈ S, θ x = 0 ↔ x ∈ T)
    (hcard : Nat.card S = Nat.card T * Fintype.card K) : ∀ a : K, ∃ x ∈ S, θ x = a := by
  classical
  have h1 : θ 1 = 0 := (hker 1 S.one_mem).2 T.one_mem
  let f : S →* Multiplicative K :=
    { toFun := fun x => Multiplicative.ofAdd (θ x.1)
      map_one' := by simp [h1]
      map_mul' := fun x y => by simp [hadd x.1 x.2 y.1 y.2] }
  have hker' : f.ker = T.subgroupOf S := by
    ext x
    simp [f, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hker x.1 x.2]
  have hcard' : Nat.card f.range = Fintype.card K := by
    have e1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hker',
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTS).toEquiv, hcard] at e1
    have hT0 : 0 < Nat.card T := Nat.card_pos
    rw [mul_comm] at e1
    exact (Nat.eq_of_mul_eq_mul_right hT0 e1).symm
  have htop : f.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hcard', Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card]
  intro a
  obtain ⟨x, hx⟩ := (MonoidHom.range_eq_top.1 htop) (Multiplicative.ofAdd a)
  exact ⟨x.1, x.2, by simpa [f] using hx⟩

section Layer

variable [Finite N] {R S T : Subgroup N} (hTS : T ≤ S)
  (hS : ∀ r ∈ R, ∀ x ∈ S, r⁻¹ * x * r ∈ S) (hT : ∀ r ∈ R, ∀ x ∈ T, r⁻¹ * x * r ∈ T)
  {θ : N → K} (hadd : ∀ x ∈ S, ∀ y ∈ S, θ (x * y) = θ x + θ y)
  (hker : ∀ x ∈ S, θ x = 0 ↔ x ∈ T)
include hTS hS hT hadd hker

omit [Fintype K] [Finite N] hTS hS hT in
theorem coord_inv {x : N} (hx : x ∈ S) : θ x⁻¹ = -θ x := by
  have h1 := hadd x hx x⁻¹ (S.inv_mem hx)
  rw [mul_inv_cancel, (hker 1 S.one_mem).2 T.one_mem] at h1
  linear_combination -h1

omit [Fintype K] [Finite N] in
theorem coord_conj_congr {r x y : N} (hr : r ∈ R) (hx : x ∈ S) (hy : y ∈ S) (hxy : θ x = θ y) :
    θ (r⁻¹ * x * r) = θ (r⁻¹ * y * r) := by
  have h1 : y⁻¹ * x ∈ T := (hker _ (S.mul_mem (S.inv_mem hy) hx)).1 (by
    rw [hadd _ (S.inv_mem hy) _ hx, coord_inv hadd hker hy, hxy, neg_add_cancel])
  have h2 : r⁻¹ * (y⁻¹ * x) * r ∈ T := hT r hr _ h1
  have e : r⁻¹ * x * r = (r⁻¹ * y * r) * (r⁻¹ * (y⁻¹ * x) * r) := by group
  rw [e, hadd _ (hS r hr y hy) _ (hS r hr _ (S.mul_mem (S.inv_mem hy) hx)),
    (hker _ (hTS h2)).2 h2, add_zero]

theorem irreducible_of_fixed (hRcard : Nat.card R = Fintype.card K - 1)
    (hfix : ∀ r ∈ R, r ≠ 1 → ∀ x ∈ S, θ (r⁻¹ * x * r) = θ x → x ∈ T)
    (hsurj : ∀ a : K, ∃ x ∈ S, θ x = a) (H : AddSubgroup K)
    (hH : ∀ r ∈ R, ∀ x ∈ S, θ x ∈ H → θ (r⁻¹ * x * r) ∈ H) : H = ⊥ ∨ H = ⊤ := by
  classical
  by_cases hbot : H = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨a, haH⟩, ha0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero.1 hbot)
  have ha0' : a ≠ 0 := fun h => ha0 (Subtype.ext h)
  obtain ⟨x, hxS, rfl⟩ := hsurj a
  have hxT : x ∉ T := fun h => ha0' ((hker x hxS).2 h)
  have hne : ∀ r : R, θ (r.1⁻¹ * x * r.1) ≠ 0 := by
    intro r h0'
    apply hxT
    have hT' := (hker _ (hS r.1 r.2 x hxS)).1 h0'
    have := hT r.1⁻¹ (R.inv_mem r.2) _ hT'
    simpa [mul_assoc] using this
  let F : Option R → H := fun o => match o with
    | none => 0
    | some r => ⟨θ (r.1⁻¹ * x * r.1), hH r.1 r.2 x hxS haH⟩
  have hF : Function.Injective F := by
    rintro (_ | r) (_ | r') hrr
    · rfl
    · exact absurd (congrArg Subtype.val hrr).symm (hne r')
    · exact absurd (congrArg Subtype.val hrr) (hne r)
    have e1 : θ (r.1⁻¹ * x * r.1) = θ (r'.1⁻¹ * x * r'.1) := congrArg Subtype.val hrr
    set g := r.1 * r'.1⁻¹ with hg
    have hgR : g ∈ R := R.mul_mem r.2 (R.inv_mem r'.2)
    have e2 := coord_conj_congr hTS hS hT hadd hker (R.inv_mem r'.2) (hS _ r.2 x hxS)
      (hS _ r'.2 x hxS) e1
    have e3 : θ (g⁻¹ * x * g) = θ x := by
      rw [show g⁻¹ * x * g = r'.1⁻¹⁻¹ * (r.1⁻¹ * x * r.1) * r'.1⁻¹ by rw [hg]; group, e2]
      congr 1
      group
    by_contra hne'
    have hg1 : g ≠ 1 := fun h => hne' (congrArg some (Subtype.ext (by
      rw [hg, mul_inv_eq_one] at h; exact h)))
    exact hxT (hfix g hgR hg1 x hxS e3)
  have hc := Nat.card_le_card_of_injective F hF
  rw [Finite.card_option, hRcard] at hc
  have hH1 : 0 < Nat.card H := Nat.card_pos
  have hK1 : 0 < Fintype.card K := Fintype.card_pos
  have hle : Fintype.card K ≤ Nat.card H := by omega
  apply AddSubgroup.eq_top_of_card_eq
  exact le_antisymm (AddSubgroup.card_le_card_addGroup H) (by rwa [Nat.card_eq_fintype_card])

theorem irreducible_of_fixed₂ {m : ℕ} (hKm : Fintype.card K = 3 ^ m)
    (hRcard : Nat.card R = Fintype.card K - 1) {J : N} (hJ : J ∈ R)
    (hinv : ∀ r ∈ R, r ^ 2 = 1 → r = 1 ∨ r = J)
    (hfix : ∀ r ∈ R, r ^ 2 ≠ 1 → ∀ x ∈ S, θ (r⁻¹ * x * r) = θ x → x ∈ T)
    (hsurj : ∀ a : K, ∃ x ∈ S, θ x = a) (H : AddSubgroup K)
    (hH : ∀ r ∈ R, ∀ x ∈ S, θ x ∈ H → θ (r⁻¹ * x * r) ∈ H) : H = ⊥ ∨ H = ⊤ := by
  classical
  let _ : Fintype R := Fintype.ofFinite R
  by_cases hbot : H = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨a, haH⟩, ha0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero.1 hbot)
  have ha0' : a ≠ 0 := fun h => ha0 (Subtype.ext h)
  obtain ⟨x, hxS, rfl⟩ := hsurj a
  have hxT : x ∉ T := fun h => ha0' ((hker x hxS).2 h)
  have hne : ∀ r : R, θ (r.1⁻¹ * x * r.1) ≠ 0 := by
    intro r h0'
    apply hxT
    have hT' := (hker _ (hS r.1 r.2 x hxS)).1 h0'
    have := hT r.1⁻¹ (R.inv_mem r.2) _ hT'
    simpa [mul_assoc] using this
  let F : R → H := fun r => ⟨θ (r.1⁻¹ * x * r.1), hH r.1 r.2 x hxS haH⟩
  have hfib : ∀ r r' : R, F r = F r' → r = r' ∨ r = ⟨J, hJ⟩ * r' := by
    intro r r' hrr
    have e1 : θ (r.1⁻¹ * x * r.1) = θ (r'.1⁻¹ * x * r'.1) := congrArg Subtype.val hrr
    set g := r.1 * r'.1⁻¹ with hg
    have hgR : g ∈ R := R.mul_mem r.2 (R.inv_mem r'.2)
    have e2 := coord_conj_congr hTS hS hT hadd hker (R.inv_mem r'.2) (hS _ r.2 x hxS)
      (hS _ r'.2 x hxS) e1
    have e3 : θ (g⁻¹ * x * g) = θ x := by
      rw [show g⁻¹ * x * g = r'.1⁻¹⁻¹ * (r.1⁻¹ * x * r.1) * r'.1⁻¹ by rw [hg]; group, e2]
      congr 1
      group
    by_cases hg2 : g ^ 2 = 1
    · rcases hinv g hgR hg2 with h1 | h1
      · left
        exact Subtype.ext (by rw [hg, mul_inv_eq_one] at h1; exact h1)
      · right
        exact Subtype.ext (by
          show r.1 = J * r'.1
          rw [← h1, hg]; group)
    · exact absurd (hfix g hgR hg2 x hxS e3) hxT
  have hcard1 : Fintype.card R ≤ 2 * (Finset.univ.image F).card := by
    apply Finset.card_le_mul_card_image
    intro b hb
    obtain ⟨r₀, -, rfl⟩ := Finset.mem_image.1 hb
    calc (Finset.univ.filter fun r => F r = F r₀).card ≤ ({r₀, ⟨J, hJ⟩ * r₀} : Finset R).card := by
          apply Finset.card_le_card
          intro r hr
          rw [Finset.mem_filter] at hr
          rcases hfib r r₀ hr.2 with h | h <;> simp [h]
      _ ≤ 2 := Finset.card_le_two
  have hcard2 : (Finset.univ.image F).card ≤ Fintype.card H - 1 := by
    have hsub : Finset.univ.image F ⊆ Finset.univ.erase 0 := by
      intro v hv
      obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hv
      refine Finset.mem_erase.2 ⟨fun h => hne r (congrArg Subtype.val h), Finset.mem_univ _⟩
    have := Finset.card_le_card hsub
    rwa [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at this
  rw [← Nat.card_eq_fintype_card, hRcard] at hcard1
  have hdvd : Nat.card H ∣ 3 ^ m := by
    rw [← hKm, ← Nat.card_eq_fintype_card]
    exact AddSubgroup.card_addSubgroup_dvd_card H
  obtain ⟨j, hj, hjH⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hHc : Nat.card H = Fintype.card H := Nat.card_eq_fintype_card
  have hm3 : 3 ^ m ≤ 2 * 3 ^ j + 1 := by
    have : 1 ≤ Fintype.card H := Fintype.card_pos
    rw [hKm] at hcard1
    rw [← hjH, hHc]
    omega
  have hjm : j = m := by
    by_contra hjm
    have hj' : j + 1 ≤ m := lt_of_le_of_ne hj hjm
    have : 3 ^ (j + 1) ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hj'
    rw [pow_succ] at this
    have h1 : 1 ≤ 3 ^ j := Nat.one_le_pow _ _ (by norm_num)
    omega
  apply AddSubgroup.eq_top_of_card_eq
  rw [hjH, hjm, ← hKm, Nat.card_eq_fintype_card]

theorem exists_eigen_layer [IsCyclic R] (hRcard : Nat.card R = Fintype.card K - 1)
    (hRcomm : ∀ r ∈ R, ∀ r' ∈ R, r * r' = r' * r) (hsurj : ∀ a : K, ∃ x ∈ S, θ x = a)
    (hirr : ∀ H : AddSubgroup K, (∀ r ∈ R, ∀ x ∈ S, θ x ∈ H → θ (r⁻¹ * x * r) ∈ H) →
      H = ⊥ ∨ H = ⊤) :
    ∃ ℓ : N → K, (∀ x ∈ S, ∀ y ∈ S, ℓ (x * y) = ℓ x + ℓ y) ∧ (∀ x ∈ S, ℓ x = 0 ↔ x ∈ T) ∧
      (∀ a : K, ∃ x ∈ S, ℓ x = a) ∧
        ∃ ρ : R →* Kˣ, ∀ r : R, ∀ x ∈ S, ℓ (r.1⁻¹ * x * r.1) = ρ r * ℓ x := by
  choose sec hsecS hsec using hsurj
  let A : R → K → K := fun r a => θ (r.1⁻¹ * sec a * r.1)
  have hAθ : ∀ (r : R) (x : N), x ∈ S → A r (θ x) = θ (r.1⁻¹ * x * r.1) := fun r x hx =>
    coord_conj_congr hTS hS hT hadd hker r.2 (hsecS _) hx (hsec _)
  have hAadd : ∀ r a b, A r (a + b) = A r a + A r b := by
    intro r a b
    have hab : a + b = θ (sec a * sec b) := by
      rw [hadd _ (hsecS a) _ (hsecS b), hsec, hsec]
    rw [hab, hAθ r _ (S.mul_mem (hsecS a) (hsecS b)),
      show r.1⁻¹ * (sec a * sec b) * r.1 = (r.1⁻¹ * sec a * r.1) * (r.1⁻¹ * sec b * r.1) by group,
      hadd _ (hS _ r.2 _ (hsecS a)) _ (hS _ r.2 _ (hsecS b))]
  have hAmul : ∀ r r' a, A (r * r') a = A r (A r' a) := by
    intro r r' a
    obtain ⟨x, hx, rfl⟩ : ∃ x ∈ S, θ x = a := ⟨sec a, hsecS a, hsec a⟩
    rw [hAθ _ _ hx, hAθ _ _ hx, hAθ _ _ (hS _ r'.2 _ hx)]
    congr 1
    have hc : r.1 * r'.1 = r'.1 * r.1 := hRcomm _ r.2 _ r'.2
    calc (r * r').1⁻¹ * x * (r * r').1 = (r'.1 * r.1)⁻¹ * x * (r'.1 * r.1) := by
          rw [Subgroup.coe_mul, hc]
      _ = r.1⁻¹ * (r'.1⁻¹ * x * r'.1) * r.1 := by group
  have hAone : ∀ a, A 1 a = a := fun a => by simp [A, hsec]
  obtain ⟨φ, hφadd, hφbij, ρ, hρ⟩ := exists_eigen_coord hRcard A hAadd hAmul hAone
    fun H hH => hirr H fun r hr x hx hxH => by
      rw [← hAθ ⟨r, hr⟩ x hx]
      exact hH ⟨r, hr⟩ _ hxH
  have hφ0 : ∀ a, φ a = 0 ↔ a = 0 := fun a => by
    have h0 : φ 0 = 0 := by
      have := hφadd 0 0
      rw [add_zero] at this
      linear_combination -this
    exact ⟨fun h => hφbij.1 (h.trans h0.symm), fun h => by rw [h, h0]⟩
  refine ⟨fun x => φ (θ x), fun x hx y hy => by simp only [hadd x hx y hy, hφadd],
    fun x hx => by simp only [hφ0, hker x hx], fun a => ?_, ρ, fun r x hx => ?_⟩
  · obtain ⟨b, rfl⟩ := hφbij.2 a
    exact ⟨sec b, hsecS b, by show φ (θ (sec b)) = φ b; rw [hsec]⟩
  · simp only [← hAθ r x hx, hρ]

end Layer

end CFSG.Walter.Ree.Thompson1
