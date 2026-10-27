module

public import CFSG.Quasithin.H13.KG14726LTools

public section

namespace CFSG.Quasithin.H13.KG14726

open Subgroup
open scoped Pointwise

variable {X : Type} [Group X]

theorem kg115Excluded_of_simple [IsSimpleGroup X] (h : center X = ⊥ → KG115Excluded X) :
    KG115Excluded X := by
  intro A B l hA hBA hBi hB hF1
  refine h ?_ A B l hA hBA hBi hB hF1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with hc | hc
  · exact hc
  · exfalso
    obtain ⟨_, ⟨y, rfl⟩, hy3, -⟩ := hF1
    have h1 : MulAut.conj y = 1 := by
      rw [← MonoidHom.mem_ker, ker_conj_eq_center, hc]
      exact mem_top y
    rw [h1, orderOf_one] at hy3
    exact absurd hy3 (by norm_num)

theorem exists_conj_of_sylow [Finite X] {S S₀ : Subgroup X} (hS : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.index) (hS₀ : IsPGroup 2 S₀) (hS₀i : ¬ 2 ∣ S₀.index) :
    ∃ g : X, ∀ x : X, x ∈ S ↔ g⁻¹ * x * g ∈ S₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X (hS₀.toSylow hS₀i) (hS.toSylow hSi)
  have hSg : S = MulAut.conj g • S₀ := by
    have := congrArg (fun Q : Sylow 2 X => (Q : Subgroup X)) hg
    simpa [Sylow.coe_subgroup_smul] using this.symm
  refine ⟨g, fun x => ?_⟩
  rw [hSg, mem_pointwise_smul_iff_inv_smul_mem]
  simp [mul_assoc]

theorem forall_center_of_conj [Finite X] {S₀ : Subgroup X} (hS₀ : IsPGroup 2 S₀)
    (hS₀i : ¬ 2 ∣ S₀.index) {Q : X → Prop} (hQ : ∀ g u : X, Q u → Q (g * u * g⁻¹))
    (h : ∀ u ∈ S₀, (∀ s ∈ S₀, s * u = u * s) → u ≠ 1 → Q u) :
    ∀ S : Subgroup X, IsPGroup 2 S → ¬ 2 ∣ S.index → ∀ l ∈ S, (∀ s ∈ S, s * l = l * s) →
      l ≠ 1 → Q l := by
  intro S hS hSi l hl hlc hl1
  obtain ⟨g, hg⟩ := exists_conj_of_sylow hS hSi hS₀ hS₀i
  have hu : g⁻¹ * l * g ∈ S₀ := (hg l).mp hl
  have huc : ∀ s ∈ S₀, s * (g⁻¹ * l * g) = g⁻¹ * l * g * s := by
    intro s hs
    have hs' : g * s * g⁻¹ ∈ S := (hg _).mpr (by rwa [show g⁻¹ * (g * s * g⁻¹) * g = s by group])
    have h1 := hlc _ hs'
    calc s * (g⁻¹ * l * g) = g⁻¹ * ((g * s * g⁻¹) * l) * g := by group
      _ = g⁻¹ * (l * (g * s * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * l * g * s := by group
  have hu1 : g⁻¹ * l * g ≠ 1 := by
    intro h1
    apply hl1
    calc l = g * (g⁻¹ * l * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have := hQ g _ (h _ hu huc hu1)
  rwa [show g * (g⁻¹ * l * g) * g⁻¹ = l by group] at this

theorem sylowTwoNoThree_of_conj [Finite X] {S₀ : Subgroup X} (hS₀ : IsPGroup 2 S₀)
    (hS₀i : ¬ 2 ∣ S₀.index) (h : ∀ y : X, orderOf y = 3 → ¬ ∀ s ∈ S₀, s * y = y * s) :
    SylowTwoNoThree X := by
  intro S hS hSi y hy hyS
  obtain ⟨g, hg⟩ := exists_conj_of_sylow hS₀ hS₀i hS hSi
  refine h (g * y * g⁻¹) (by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]; exact hy)
    fun s hs => ?_
  have h1 := hyS _ ((hg s).mp hs)
  calc s * (g * y * g⁻¹) = g * ((g⁻¹ * s * g) * y) * g⁻¹ := by group
    _ = g * (y * (g⁻¹ * s * g)) * g⁻¹ := by rw [h1]
    _ = g * y * g⁻¹ * s := by group

theorem prime_conj {u : X} (g : X)
    (h : ∃ ℓ : X, ℓ * u = u * ℓ ∧ ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ orderOf ℓ = p) :
    ∃ ℓ : X, ℓ * (g * u * g⁻¹) = g * u * g⁻¹ * ℓ ∧ ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ orderOf ℓ = p := by
  obtain ⟨ℓ, hℓ, p, hp, hp5, hℓp⟩ := h
  refine ⟨g * ℓ * g⁻¹, ?_, p, hp, hp5, by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hℓp]⟩
  calc g * ℓ * g⁻¹ * (g * u * g⁻¹) = g * (ℓ * u) * g⁻¹ := by group
    _ = g * (u * ℓ) * g⁻¹ := by rw [hℓ]
    _ = g * u * g⁻¹ * (g * ℓ * g⁻¹) := by group

theorem kg115Excluded_of_prime_conj [Finite X] [IsSimpleGroup X] {S₀ : Subgroup X}
    (hS₀ : IsPGroup 2 S₀) (hS₀i : ¬ 2 ∣ S₀.index)
    (h3 : ∀ y : X, orderOf y = 3 → ¬ ∀ s ∈ S₀, s * y = y * s)
    (h : ∀ u ∈ S₀, (∀ s ∈ S₀, s * u = u * s) → u ≠ 1 →
      ∃ ℓ : X, ℓ * u = u * ℓ ∧ ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ orderOf ℓ = p) :
    KG115Excluded X :=
  kg115Excluded_of_simple fun hc => kg115Excluded_of_at hc (sylowTwoNoThree_of_conj hS₀ hS₀i h3)
    fun S hS hSi l hl hlc hl1 => kg115At_of_prime
      (forall_center_of_conj hS₀ hS₀i (fun g _ hu => prime_conj g hu) h S hS hSi l hl hlc hl1)

theorem kg115Excluded_of_involution [Finite X] [IsSimpleGroup X] (h2 : 2 ∣ Nat.card X)
    (h : ∀ t y : X, orderOf t = 2 → y * t = t * y → orderOf y ≠ 3) : KG115Excluded X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine kg115Excluded_of_simple fun hc => kg115Excluded_of_at hc ?_ ?_
  ·
    intro S hS hSi y hy hyS
    have h2S : 2 ∣ Nat.card S := by
      have h1 := S.card_mul_index
      exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hSi).dvd_of_dvd_mul_right
        (h1 ▸ h2)
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2S
    exact h t y (by rw [Subgroup.orderOf_coe]; exact ht) (hyS t t.2).symm hy
  ·
    intro S hS hSi l hl _ hl1
    refine kg115At_of_noThree fun y hy => ?_
    obtain ⟨k, hk⟩ := hS ⟨l, hl⟩
    have hlk : l ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hlk)
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hm
      exact hl1 hm
    have h2l : 2 ∣ orderOf l := by
      rw [hm]
      exact dvd_pow_self 2 hm0
    have ht : orderOf (l ^ (orderOf l / 2)) = 2 :=
      orderOf_pow_orderOf_div (orderOf_pos l).ne' h2l
    exact h _ y ht ((Commute.pow_right (hy : Commute y l) _).eq)

end CFSG.Quasithin.H13.KG14726

end
