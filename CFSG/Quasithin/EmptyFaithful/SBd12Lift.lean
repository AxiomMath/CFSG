module

public import CFSG.Quasithin.EmptyFaithful.SBd11Syl

public section

namespace CFSG.Quasithin.SBd12


open CFSG.Quasithin.SBd11

variable {X : Type*} [Group X] [Finite X]

theorem exists_normal_three_of_normalizing (P : Sylow 3 X) (h9 : 9 ∣ Nat.card P)
    {A : Subgroup X} (hA : IsPGroup 2 A) (hAN : A ≤ Subgroup.normalizer (P : Set X))
    (hcard : Nat.card X ∣ 8 * Nat.card A * Nat.card P) :
    ∃ R : Subgroup X, R ≠ ⊥ ∧ R.Normal ∧ IsPGroup 3 R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hWN : (P : Subgroup X) ⊔ A ≤ Subgroup.normalizer (P : Set X) :=
    sup_le Subgroup.le_normalizer hAN
  have hcop : Nat.Coprime (Nat.card P) (Nat.card A) :=
    IsPGroup.coprime_card_of_ne 3 2 (by norm_num) (P : Subgroup X) A P.isPGroup' hA
  have hdvdW : Nat.card P * Nat.card A ∣ Nat.card ((P : Subgroup X) ⊔ A : Subgroup X) :=
    hcop.mul_dvd_of_dvd_of_dvd (Subgroup.card_dvd_of_le le_sup_left)
      (Subgroup.card_dvd_of_le le_sup_right)
  have hidx : ((P : Subgroup X) ⊔ A).index ∣ 8 := by
    have h1 := Subgroup.card_mul_index ((P : Subgroup X) ⊔ A)
    have hpos : 0 < Nat.card P * Nat.card A := Nat.mul_pos Nat.card_pos Nat.card_pos
    have h2 : (Nat.card P * Nat.card A) * ((P : Subgroup X) ⊔ A).index ∣
        (Nat.card P * Nat.card A) * 8 := by
      calc (Nat.card P * Nat.card A) * ((P : Subgroup X) ⊔ A).index
          ∣ Nat.card ((P : Subgroup X) ⊔ A : Subgroup X) * ((P : Subgroup X) ⊔ A).index :=
            Nat.mul_dvd_mul_right hdvdW _
        _ = Nat.card X := h1
        _ ∣ 8 * Nat.card A * Nat.card P := hcard
        _ = (Nat.card P * Nat.card A) * 8 := by ring
    exact Nat.dvd_of_mul_dvd_mul_left hpos h2
  exact exists_normal_three_of_index P h9 hWN hidx

omit [Finite X] in
theorem le_normalizer_of_commute {P A : Subgroup X} (h : ∀ a ∈ A, ∀ x ∈ P, a * x = x * a) :
    A ≤ Subgroup.normalizer (P : Set X) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro n
  have hconj : ∀ z ∈ A, ∀ x ∈ P, z * x * z⁻¹ = x := fun z hz x hx => by
    rw [h z hz x hx]
    group
  constructor
  · intro hn
    rw [hconj a ha n hn]
    exact hn
  · intro hn
    have h2 := hconj a⁻¹ (A.inv_mem ha) _ hn
    have h3 : a⁻¹ * (a * n * a⁻¹) * a⁻¹⁻¹ = n := by group
    rw [h3] at h2
    rw [h2]
    exact hn

theorem mem_normalizer_of_map_mem_normalizer {Y Z : Type*} [Group Y] [Finite Y] [Group Z]
    (ψ : Y →* Z) (hK2 : IsPGroup 2 ψ.ker) (hKc : ∀ k ∈ ψ.ker, ∀ y : Y, k * y = y * k)
    (P : Sylow 3 Y) {w : Y}
    (hw : ψ w ∈ Subgroup.normalizer (((P : Subgroup Y).map ψ : Subgroup Z) : Set Z)) :
    w ∈ Subgroup.normalizer ((P : Subgroup Y) : Set Y) := by
  have hconj : ∀ p ∈ (P : Subgroup Y), w * p * w⁻¹ ∈ (P : Subgroup Y) := by
    intro p hp
    have h1 : ψ (w * p * w⁻¹) ∈ (P : Subgroup Y).map ψ := by
      have := (Subgroup.mem_normalizer_iff.1 hw (ψ p)).1 (Subgroup.mem_map_of_mem ψ hp)
      simpa [map_mul, map_inv] using this
    obtain ⟨p', hp', hp'e⟩ := Subgroup.mem_map.1 h1
    have hkK : p'⁻¹ * (w * p * w⁻¹) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hp'e, inv_mul_cancel]
    obtain ⟨a, ha⟩ := P.isPGroup' ⟨p, hp⟩
    obtain ⟨a', ha'⟩ := P.isPGroup' ⟨p', hp'⟩
    have hpa : p ^ (3 ^ (a + a')) = 1 := by
      have := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rw [pow_add, pow_mul, this, one_pow]
    have hp'a : p' ^ (3 ^ (a + a')) = 1 := by
      have := congrArg Subtype.val ha'
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rw [add_comm, pow_add, pow_mul, this, one_pow]
    set k := p'⁻¹ * (w * p * w⁻¹) with hk
    have hwp : w * p * w⁻¹ = p' * k := by rw [hk]; group
    have hcomm : Commute p' k := (hKc k hkK p').symm
    have hkN : k ^ (3 ^ (a + a')) = 1 := by
      have h2 : (w * p * w⁻¹) ^ (3 ^ (a + a')) = 1 := by
        rw [conj_pow, hpa]
        group
      rw [hwp, hcomm.mul_pow, hp'a, one_mul] at h2
      exact h2
    obtain ⟨m, hm⟩ := hK2 ⟨k, hkK⟩
    have hk2m : k ^ (2 ^ m) = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    have hk1 : k = 1 := by
      have hd1 : orderOf k ∣ 3 ^ (a + a') := orderOf_dvd_of_pow_eq_one hkN
      have hd2 : orderOf k ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hk2m
      have hcop : Nat.Coprime (3 ^ (a + a')) (2 ^ m) :=
        Nat.Coprime.pow _ _ (by norm_num)
      have : orderOf k = 1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
      exact orderOf_eq_one_iff.1 this
    rw [hwp, hk1, mul_one]
    exact hp'
  have hinj : Function.Injective
      (fun x : (P : Subgroup Y) => (⟨w * x * w⁻¹, hconj x x.2⟩ : (P : Subgroup Y))) := by
    intro a b hab
    have := congrArg Subtype.val hab
    simp only [mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  have hsurj := Finite.injective_iff_surjective.mp hinj
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hconj x, fun hx => ?_⟩
  obtain ⟨a, ha⟩ := hsurj ⟨w * x * w⁻¹, hx⟩
  have := congrArg Subtype.val ha
  simp only [mul_left_inj, mul_right_inj] at this
  rw [← this]
  exact a.2

end CFSG.Quasithin.SBd12
