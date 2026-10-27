module

public import CFSG.RankThree.PartTwo.Census.DoubleCoverLift

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

namespace TransitiveLift

open scoped commutatorElement IsMulCommutative
open CFSG.RankThree.PartOne.CentralCoverThree

variable {X J : Type*} [Group X] [Group J] {φ : J →* X}

section CommGroup

variable {C : Type*} [CommGroup C]

theorem mul_eq_sq_of_eq (s b c₁ c₂ c₃ : C) (h : s * c₃ ^ 2 = s * c₁ ^ 2 * (s * c₂ ^ 2) * b) :
    s * b = (c₃ * (c₁ * c₂)⁻¹) ^ 2 := by
  have h2 : s * c₃ ^ 2 = s * (s * b * (c₁ * c₂) ^ 2) := by
    rw [h, mul_pow]
    ac_rfl
  rw [mul_pow, inv_pow, eq_mul_inv_iff_mul_eq, mul_left_cancel h2]

theorem eq_sq_of_mul_eq (s b₁ b₂ d₁ d₂ d₃ : C) (h₁ : s * b₁ = d₁ ^ 2) (h₂ : s * b₂ = d₂ ^ 2)
    (h₃ : s * (b₁ * b₂) = d₃ ^ 2) : s = (d₁ * d₂ * d₃⁻¹) ^ 2 := by
  rw [mul_pow, mul_pow, inv_pow, ← h₁, ← h₂, ← h₃, eq_mul_inv_iff_mul_eq]
  ac_rfl

end CommGroup

section Lifts

variable (hker : φ.ker ≤ Subgroup.center J)
include hker

theorem commute_of_map_eq_one {k : J} (hk : φ k = 1) (y : J) : Commute y k :=
  Subgroup.mem_center_iff.mp (hker hk) y

theorem mul_sq_eq {x y : J} (h : φ ⁅y, x⁆ = 1) : (x * y) ^ 2 = x ^ 2 * y ^ 2 * ⁅y, x⁆ := by
  have hc := commute_of_map_eq_one hker h
  have e : y * x = ⁅y, x⁆ * x * y := by rw [commutatorElement_def]; group
  calc (x * y) ^ 2 = x * (y * x) * y := by rw [sq]; group
    _ = x * (⁅y, x⁆ * x * y) * y := by rw [e]
    _ = (x * ⁅y, x⁆) * x * y * y := by group
    _ = (⁅y, x⁆ * x) * x * y * y := by rw [(hc x).eq]
    _ = ⁅y, x⁆ * (x ^ 2 * y ^ 2) := by rw [sq, sq]; group
    _ = x ^ 2 * y ^ 2 * ⁅y, x⁆ := ((hc _).eq).symm

theorem exists_sq_eq_of_conj (hφ : Function.Surjective φ) {x y : J} {g : X}
    (hx2 : φ x ^ 2 = 1) (hg : g * φ x * g⁻¹ = φ y) :
    ∃ c : J, φ c = 1 ∧ y ^ 2 = x ^ 2 * c ^ 2 := by
  obtain ⟨g', rfl⟩ := hφ g
  set c := (g' * x * g'⁻¹)⁻¹ * y with hcdef
  have hc : φ c = 1 := by
    rw [hcdef, map_mul, map_inv, map_mul, map_mul, map_inv, hg, inv_mul_cancel]
  refine ⟨c, hc, ?_⟩
  have hx : φ (x ^ 2) = 1 := by rw [map_pow, hx2]
  have hy : y = g' * x * g'⁻¹ * c := by rw [hcdef, mul_inv_cancel_left]
  rw [hy, (commute_of_map_eq_one hker hc _).mul_pow, conj_pow,
    (commute_of_map_eq_one hker hx g').eq, mul_inv_cancel_right]

theorem commute_of_map_eq_commutatorElement {y y' p q : J} (hp : Commute (φ y) (φ p))
    (hq : Commute (φ y) (φ q)) (hy' : φ y' = φ ⁅p, q⁆) : y * y' = y' * y := by
  have h1 : φ (y * p * y⁻¹) = φ p := by
    rw [map_mul, map_mul, map_inv, hp.eq, mul_inv_cancel_right]
  have h2 : φ (y * q * y⁻¹) = φ q := by
    rw [map_mul, map_mul, map_inv, hq.eq, mul_inv_cancel_right]
  have hc : y * ⁅p, q⁆ * y⁻¹ = ⁅p, q⁆ := by
    rw [conjugate_commutatorElement]
    exact commutator_eq_of_map_eq hker h1 h2
  have hk : φ (⁅p, q⁆⁻¹ * y') = 1 := by rw [map_mul, map_inv, hy', inv_mul_cancel]
  have hcomm : Commute y ⁅p, q⁆ := mul_inv_eq_iff_eq_mul.mp hc
  have h3 := (hcomm.mul_right (commute_of_map_eq_one hker hk y)).eq
  rwa [mul_inv_cancel_left] at h3

end Lifts

section Triple

theorem exists_mem_notMem {E : Subgroup X} (T : Finset X) (hT : T.card < Nat.card E) :
    ∃ x ∈ E, x ∉ T := by
  by_contra h
  push Not at h
  have hsub : (E : Set X) ⊆ (T : Set X) := fun x hx => h x hx
  have hle : Nat.card (E : Set X) ≤ Nat.card (T : Set X) := Nat.card_mono T.finite_toSet hsub
  have h1 : Nat.card (T : Set X) = T.card := Nat.card_eq_finsetCard T
  have h2 : Nat.card (E : Set X) = Nat.card E := rfl
  omega

theorem exists_triple {E : Subgroup X} (hE2 : ∀ x ∈ E, x ^ 2 = 1) (hE8 : 8 ≤ Nat.card E) :
    ∃ a ∈ E, ∃ b ∈ E, ∃ c ∈ E, a ≠ 1 ∧ b ≠ 1 ∧ c ≠ 1 ∧ a * b ≠ 1 ∧ a * c ≠ 1 ∧ b * c ≠ 1 ∧
      a * (b * c) ≠ 1 := by
  classical
  have hinv : ∀ x ∈ E, x⁻¹ = x := fun x hx =>
    DoubleCoverLift.inv_eq_self_of_sq_eq_one hE2 hx
  obtain ⟨a, ha, ha1⟩ := exists_mem_notMem (E := E) {1} (by simp; omega)
  obtain ⟨b, hb, hb1⟩ := exists_mem_notMem (E := E) {1, a} (by
    have := Finset.card_le_two (a := (1 : X)) (b := a); omega)
  obtain ⟨c, hc, hc1⟩ := exists_mem_notMem (E := E) {1, a, b, a * b} (by
    have := Finset.card_le_four (a := (1 : X)) (b := a) (c := b) (d := a * b); omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha1 hb1 hc1
  have hab : b * a = a * b := DoubleCoverLift.mul_comm_of_sq_eq_one hE2 hb ha
  refine ⟨a, ha, b, hb, c, hc, ha1, hb1.1, hc1.1, fun h => hb1.2 ?_, fun h => hc1.2.1 ?_,
    fun h => hc1.2.2.1 ?_, fun h => hc1.2.2.2 ?_⟩
  · rw [eq_inv_of_mul_eq_one_right h, hinv a ha]
  · rw [eq_inv_of_mul_eq_one_right h, hinv a ha]
  · rw [eq_inv_of_mul_eq_one_right h, hinv b hb]
  · have h' : a * b * c = 1 := by rw [mul_assoc]; exact h
    rw [eq_inv_of_mul_eq_one_right h', mul_inv_rev, hinv a ha, hinv b hb, hab]

end Triple

section Transitive

variable (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center J) {E : Subgroup X}
  (hE2 : ∀ x ∈ E, x ^ 2 = 1) (hE8 : 8 ≤ Nat.card E) {e₀ : X}
  (htr : ∀ x ∈ E, x ≠ 1 → ∃ g : X, g * e₀ * g⁻¹ = x)
include hφ hker hE2 hE8 htr

omit hE8 in
theorem exists_sq_eq_mul_sq {e : J} (he : φ e = e₀) {y : J} (hy : φ y ∈ E) (hy1 : φ y ≠ 1) :
    ∃ c : J, φ c = 1 ∧ y ^ 2 = e ^ 2 * c ^ 2 := by
  obtain ⟨g, hg⟩ := htr _ hy hy1
  have he2 : φ e ^ 2 = 1 := by
    rw [he]
    have h := hE2 _ hy
    rw [← hg, conj_pow] at h
    rwa [mul_inv_eq_one, mul_eq_left] at h
  exact exists_sq_eq_of_conj hker hφ he2 (by rw [he]; exact hg)

omit hφ hker hE8 in
theorem map_sq_eq_one {e : J} (he : φ e = e₀) {x : X} (hx : x ∈ E) (hx1 : x ≠ 1) :
    φ (e ^ 2) = 1 := by
  obtain ⟨g, hg⟩ := htr _ hx hx1
  have h := hE2 _ hx
  rw [← hg, conj_pow] at h
  rw [map_pow, he]
  rwa [mul_inv_eq_one, mul_eq_left] at h

omit hE8 in
theorem exists_mul_commutator_eq_sq {e : J} (he : φ e = e₀) {y y' : J} (hy : φ y ∈ E)
    (hy' : φ y' ∈ E) (hy1 : φ y ≠ 1) (hy1' : φ y' ≠ 1) (hyy : φ y * φ y' ≠ 1) :
    ∃ c : J, φ c = 1 ∧ e ^ 2 * ⁅y', y⁆ = c ^ 2 := by
  have hB : φ ⁅y', y⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact DoubleCoverLift.mul_comm_of_sq_eq_one hE2 hy' hy
  obtain ⟨c₁, hc₁, h₁⟩ := exists_sq_eq_mul_sq hφ hker hE2 htr he hy hy1
  obtain ⟨c₂, hc₂, h₂⟩ := exists_sq_eq_mul_sq hφ hker hE2 htr he hy' hy1'
  obtain ⟨c₃, hc₃, h₃⟩ := exists_sq_eq_mul_sq hφ hker hE2 htr he (y := y * y')
    (by rw [map_mul]; exact E.mul_mem hy hy') (by rwa [map_mul])
  have hsq := mul_sq_eq hker hB
  rw [h₁, h₂, h₃] at hsq
  have hE : ∀ k : J, φ k = 1 → k ∈ Subgroup.center J := fun k hk => hker hk
  have he' := map_sq_eq_one hE2 htr he hy hy1
  set S : Subgroup.center J := ⟨e ^ 2, hE _ he'⟩
  set C₁ : Subgroup.center J := ⟨c₁, hE _ hc₁⟩
  set C₂ : Subgroup.center J := ⟨c₂, hE _ hc₂⟩
  set C₃ : Subgroup.center J := ⟨c₃, hE _ hc₃⟩
  set BB : Subgroup.center J := ⟨⁅y', y⁆, hE _ hB⟩
  have key := mul_eq_sq_of_eq S BB C₁ C₂ C₃ (Subtype.ext hsq)
  refine ⟨c₃ * (c₁ * c₂)⁻¹, ?_, congrArg Subtype.val key⟩
  rw [map_mul, map_inv, map_mul, hc₁, hc₂, hc₃]
  group

theorem exists_sq_eq_sq_lift {e : J} (he : φ e = e₀) : ∃ c : J, φ c = 1 ∧ e ^ 2 = c ^ 2 := by
  obtain ⟨a, ha, b, hb, c, hc, ha1, hb1, hc1, hab, hac, hbc, habc⟩ := exists_triple hE2 hE8
  obtain ⟨a', rfl⟩ := hφ a
  obtain ⟨b', rfl⟩ := hφ b
  obtain ⟨c', rfl⟩ := hφ c
  have hE : ∀ k : J, φ k = 1 → k ∈ Subgroup.center J := fun k hk => hker hk
  have hB : ∀ {x y : J}, φ x ∈ E → φ y ∈ E → φ ⁅y, x⁆ = 1 := fun hx hy => by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact DoubleCoverLift.mul_comm_of_sq_eq_one hE2 hy hx
  have hbc' : φ (b' * c') ∈ E := by rw [map_mul]; exact E.mul_mem hb hc
  obtain ⟨d₁, hd₁, h₁⟩ := exists_mul_commutator_eq_sq hφ hker hE2 htr he ha hb ha1 hb1 hab
  obtain ⟨d₂, hd₂, h₂⟩ := exists_mul_commutator_eq_sq hφ hker hE2 htr he ha hc ha1 hc1 hac
  obtain ⟨d₃, hd₃, h₃⟩ := exists_mul_commutator_eq_sq hφ hker hE2 htr he ha hbc' ha1
    (by rwa [map_mul]) (by rwa [map_mul])
  rw [commutator_mul_left_of_central (hE _ (hB ha hc))] at h₃
  have he' := map_sq_eq_one hE2 htr he ha ha1
  set S : Subgroup.center J := ⟨e ^ 2, hE _ he'⟩
  set B₁ : Subgroup.center J := ⟨⁅b', a'⁆, hE _ (hB ha hb)⟩
  set B₂ : Subgroup.center J := ⟨⁅c', a'⁆, hE _ (hB ha hc)⟩
  set D₁ : Subgroup.center J := ⟨d₁, hE _ hd₁⟩
  set D₂ : Subgroup.center J := ⟨d₂, hE _ hd₂⟩
  set D₃ : Subgroup.center J := ⟨d₃, hE _ hd₃⟩
  have key := eq_sq_of_mul_eq S B₁ B₂ D₁ D₂ D₃ (Subtype.ext h₁) (Subtype.ext h₂)
    (Subtype.ext h₃)
  refine ⟨d₁ * d₂ * d₃⁻¹, ?_, congrArg Subtype.val key⟩
  rw [map_mul, map_mul, map_inv, hd₁, hd₂, hd₃]
  group

theorem exists_sq_eq_sq {y : J} (hy : φ y ∈ E) : ∃ c : J, φ c = 1 ∧ y ^ 2 = c ^ 2 := by
  by_cases hy1 : φ y = 1
  · exact ⟨y, hy1, rfl⟩
  obtain ⟨e, he⟩ := hφ e₀
  obtain ⟨c₀, hc₀, h₀⟩ := exists_sq_eq_sq_lift hφ hker hE2 hE8 htr he
  obtain ⟨c, hc, h⟩ := exists_sq_eq_mul_sq hφ hker hE2 htr he hy hy1
  refine ⟨c₀ * c, by rw [map_mul, hc₀, hc, one_mul], ?_⟩
  rw [h, h₀, (commute_of_map_eq_one hker hc c₀).mul_pow]

theorem exists_commutator_eq_sq {y y' : J} (hy : φ y ∈ E) (hy' : φ y' ∈ E) :
    ∃ c : J, φ c = 1 ∧ ⁅y, y'⁆ = c ^ 2 := by
  by_cases hy1 : φ y = 1
  · exact ⟨1, map_one φ, by
      rw [one_pow, commutatorElement_eq_one_iff_mul_comm]
      exact ((commute_of_map_eq_one hker hy1 y').eq).symm⟩
  by_cases hy1' : φ y' = 1
  · exact ⟨1, map_one φ, by
      rw [one_pow, commutatorElement_eq_one_iff_mul_comm]
      exact (commute_of_map_eq_one hker hy1' y).eq⟩
  by_cases hyy : φ y' * φ y = 1
  · refine ⟨1, map_one φ, ?_⟩
    rw [one_pow, commutatorElement_eq_one_iff_mul_comm]
    have hk : φ (y' * y) = 1 := by rw [map_mul, hyy]
    have hc := (commute_of_map_eq_one hker hk y).eq
    calc y * y' = y * (y' * y) * y⁻¹ := by group
      _ = y' * y * y * y⁻¹ := by rw [hc]
      _ = y' * y := by group
  obtain ⟨e, he⟩ := hφ e₀
  obtain ⟨c₀, hc₀, h₀⟩ := exists_sq_eq_sq_lift hφ hker hE2 hE8 htr he
  obtain ⟨c, hc, h⟩ := exists_mul_commutator_eq_sq hφ hker hE2 htr he hy' hy hy1' hy1 hyy
  refine ⟨c₀⁻¹ * c, by rw [map_mul, map_inv, hc₀, hc, inv_one, one_mul], ?_⟩
  rw [h₀] at h
  rw [(commute_of_map_eq_one hker hc c₀⁻¹).mul_pow, ← h, inv_pow, inv_mul_cancel_left]

end Transitive

section Isotropic

variable (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center J) {W : Subgroup X}
  (hW : ∀ y y' : J, φ y ∈ W → φ y' ∈ W → y * y' = y' * y)
  (hsq : ∀ y : J, φ y ∈ W → ∃ c : J, φ c = 1 ∧ y ^ 2 = c ^ 2)
include hW

@[expose] def involutionLift : Subgroup J where
  carrier := {y | φ y ∈ W ∧ y ^ 2 = 1}
  mul_mem' {y y'} hy hy' := ⟨by rw [map_mul]; exact W.mul_mem hy.1 hy'.1, by
    rw [(Commute.mul_pow (hW y y' hy.1 hy'.1)), hy.2, hy'.2, one_mul]⟩
  one_mem' := ⟨by rw [map_one]; exact W.one_mem, one_pow 2⟩
  inv_mem' {y} hy := ⟨by rw [map_inv]; exact W.inv_mem hy.1, by rw [inv_pow, hy.2, inv_one]⟩

theorem mem_involutionLift {y : J} : y ∈ involutionLift hW ↔ φ y ∈ W ∧ y ^ 2 = 1 :=
  Iff.rfl

theorem isElementaryAbelian_involutionLift :
    CFSG.IsElementaryAbelian 2 (involutionLift hW) where
  toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hW _ _ a.2.1 b.2.1)⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => Subtype.ext a.2.2

include hφ hker hsq in
theorem card_involutionLift [Finite J] :
    Nat.card (involutionLift hW) = Nat.card W * Nat.card {c : J // φ c = 1 ∧ c ^ 2 = 1} := by
  set A := involutionLift hW
  let f : A →* W := (φ.comp A.subtype).codRestrict W fun y => y.2.1
  have hf : Function.Surjective f := by
    rintro ⟨w, hw⟩
    obtain ⟨y, rfl⟩ := hφ w
    obtain ⟨c, hc, hyc⟩ := hsq y hw
    have hcc := commute_of_map_eq_one hker hc
    refine ⟨⟨y * c⁻¹, ?_, ?_⟩, ?_⟩
    · rw [map_mul, map_inv, hc, inv_one, mul_one]; exact hw
    · rw [((hcc y).inv_right).mul_pow, hyc, inv_pow, mul_inv_cancel]
    · apply Subtype.ext
      change φ (y * c⁻¹) = φ y
      rw [map_mul, map_inv, hc, inv_one, mul_one]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv] at h1
  rw [h1]
  congr 1
  refine Nat.card_congr
    { toFun := fun y => ⟨((y : A) : J), ?_, (y : A).2.2⟩
      invFun := fun c => ⟨⟨c.1, ?_, c.2.2⟩, ?_⟩
      left_inv := fun y => rfl
      right_inv := fun c => rfl }
  · have h := y.2
    rw [MonoidHom.mem_ker] at h
    exact congrArg Subtype.val h
  · rw [c.2.1]; exact W.one_mem
  · rw [MonoidHom.mem_ker]
    exact Subtype.ext c.2.1

include hφ hker hsq in
theorem exists_isElementaryAbelian_card [Finite J] :
    ∃ A : Subgroup J, CFSG.IsElementaryAbelian 2 A ∧
      Nat.card A = Nat.card W * Nat.card {c : J // φ c = 1 ∧ c ^ 2 = 1} :=
  ⟨involutionLift hW, isElementaryAbelian_involutionLift hW,
    card_involutionLift hφ hker hW hsq⟩

end Isotropic

theorem le_pRank_of_card [Finite J] {A : Subgroup J} (hA : CFSG.IsElementaryAbelian 2 A)
    {k : ℕ} (hk : 2 ^ k ≤ Nat.card A) : k ≤ CFSG.pRank 2 J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hA
  obtain ⟨r, hr⟩ := (CFSG.IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hkr : k ≤ r := (Nat.pow_le_pow_iff_right (by norm_num)).mp (hr ▸ hk)
  exact hkr.trans (DoubleCoverLift.le_pRank_two_of_card A hA hr)

end TransitiveLift

end CFSG.RankThree.PartTwo.Sec4.Census
