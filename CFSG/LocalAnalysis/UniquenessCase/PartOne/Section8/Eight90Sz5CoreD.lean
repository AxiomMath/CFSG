module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Sz5SzFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Sz5Weights
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Sz5Struct
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Sz5Lift
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Sz5Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Sz5

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

theorem isPGroup_two_zpowers_of_sq {D : Type} [Group D] (z : D) (h : z ^ 2 = 1) :
    IsPGroup 2 (Subgroup.zpowers z) := by
  intro g
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp g.2
  refine ⟨1, Subtype.ext ?_⟩
  calc ((g ^ 2 ^ 1 : ↥(Subgroup.zpowers z)) : D) = (g : D) ^ 2 := rfl
    _ = (z ^ i) ^ 2 := by rw [hi]
    _ = (z ^ 2) ^ i := by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    _ = 1 := by rw [h, one_zpow]

theorem sq_eq_one_of_mem_zpowers {D : Type} [Group D] (z : D) (h : z ^ 2 = 1) :
    ∀ a ∈ Subgroup.zpowers z, a ^ 2 = 1 := by
  intro a ha
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

theorem weights_numerics {a c : ℕ} (hc : 1 ≤ c) (h : a + 3 * c ≤ 4) : c = 1 ∧ a ≤ 1 := by
  omega

theorem fixBound_mono {F K V : Type} [Field F] [Group K] [AddCommGroup V] [Module F V]
    {ρ : K →* (V ≃ₗ[F] V)} {r s : ℕ} (h : FixBound ρ r) (hrs : r ≤ s) : FixBound ρ s :=
  fun t ht h2 => (h t ht h2).trans hrs

theorem negOne_mul_comm {F V : Type} [Field F] [AddCommGroup V] [Module F V] (g : V ≃ₗ[F] V) :
    negOne F V * g = g * negOne F V := by
  apply LinearEquiv.ext
  intro v
  show negOne F V (g v) = g (negOne F V v)
  simp [negOne_apply]

theorem exists_ne_one_of_card_eq_eight {D : Type} [Group D] (E : Subgroup D)
    (h : Nat.card E = 8) : ∃ z ∈ E, z ≠ 1 := by
  by_contra hcon
  have hcon' : ∀ z ∈ E, z = 1 := fun z hz => by_contra fun h' => hcon ⟨z, hz, h'⟩
  have : Nat.card E = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun x y => Subtype.ext ((hcon' x x.2).trans (hcon' y y.2).symm)⟩, ⟨1⟩⟩
  omega

theorem weights_of_frobenius {D : Type} [Group D] {F : Type} [Field F] {V : Type}
    [AddCommGroup V] [Module F V] [Module.Finite F V] (hF : ringChar F ≠ 2)
    (ρ : D →* (V ≃ₗ[F] V))
    (hρ : Function.Injective ρ) (E : Subgroup D) (y : D) (hE8 : Nat.card E = 8)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE2 : ∀ a ∈ E, a ^ 2 = 1)
    (hy7 : orderOf y = 7) (hyE : ∀ e ∈ E, y * e * y⁻¹ ∈ E)
    (hyf : ∀ e ∈ E, y * e * y⁻¹ = e → e = 1) :
    (∀ a ∈ E.map ρ, ∀ b ∈ E.map ρ, a * b = b * a) ∧ (∀ a ∈ E.map ρ, a ^ 2 = 1) ∧
    ∃ a c : ℕ, 1 ≤ c ∧ Module.finrank F V = a + 7 * c ∧
      Module.finrank F (wt (E.map ρ) 1) = a ∧
      (∀ χ : ↥(E.map ρ) →* Fˣ, χ ≠ 1 →
        Module.finrank F (wt (E.map ρ) χ) = c) ∧
      (∀ b ∈ E, b ≠ 1 → Module.finrank F (fixSpaceOf (ρ b)) = a + 3 * c ∧
        Module.finrank F (fixSpaceOf (negOne F V * ρ b)) = 4 * c) := by
  have hE8' : Nat.card (E.map ρ) = 8 := by
    rw [Subgroup.card_map_of_injective hρ, hE8]
  have hEc' : ∀ a ∈ E.map ρ, ∀ b ∈ E.map ρ, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hEc a ha b hb]
  have hE2' : ∀ a ∈ E.map ρ, a ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE2 a ha, map_one]
  have hy7' : orderOf (ρ y) = 7 := by rw [orderOf_injective ρ hρ y, hy7]
  have hyE' : ∀ e ∈ E.map ρ, ρ y * e * (ρ y)⁻¹ ∈ E.map ρ := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨y * a * y⁻¹, hyE a ha, by simp⟩
  have hyf' : ∀ e ∈ E.map ρ, ρ y * e * (ρ y)⁻¹ = e → e = 1 := by
    rintro _ ⟨a, ha, rfl⟩ h
    have : ρ (y * a * y⁻¹) = ρ a := by simpa using h
    rw [hyf a ha (hρ this), map_one]
  obtain ⟨a, c, hc, hdim, hwt1, hwtc, hfixE⟩ :=
    sz5e1_weights_count hF (E.map ρ) (ρ y) hE8' hEc' hE2' hy7' hyE' hyf'
  refine ⟨hEc', hE2', a, c, hc, hdim, hwt1, hwtc, ?_⟩
  intro b hb hb1
  exact hfixE (ρ b) ⟨b, hb, rfl⟩ (fun h => hb1 (hρ (by simpa using h)))

theorem sz5e1_core_D1 {D : Type} [Group D] [Finite D] (hD : IsSz D 3) {F : Type} [Field F]
    {V : Type} [AddCommGroup V] [Module F V] [Module.Finite F V] (hF : ringChar F ≠ 2)
    (ρ : D →* (V ≃ₗ[F] V)) (hρ : Function.Injective ρ) (hfix : FixBound ρ 4) : False := by
  obtain ⟨S, Z, y, hZS, hZc, hZ8, hZ2, ⟨s, hs, t, ht, hst⟩, hy7, hyZ, hyf⟩ :=
    sz5e1_sz8_frobenius hD
  have hZcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb => hZc a ha b (hZS hb)
  obtain ⟨hEc, hE2, a, c, hc, -, hwt1, hwtc, hfixE⟩ :=
    weights_of_frobenius hF ρ hρ Z y hZ8 hZcomm hZ2 hy7 hyZ hyf
  obtain ⟨z, hz, hz1⟩ := exists_ne_one_of_card_eq_eight Z hZ8
  have hz4 := hfix z hz1 (isPGroup_two_zpowers_of_sq z (hZ2 z hz))
  have hρz := (hfixE z hz hz1).1
  have hnum : a + 3 * c ≤ 4 := by
    have : Module.finrank F (fixSpaceOf (ρ z)) ≤ 4 := hz4
    omega
  obtain ⟨hc1, ha1⟩ := weights_numerics hc hnum
  have hwt : ∀ χ : ↥(Z.map ρ) →* Fˣ, Module.finrank F (wt (Z.map ρ) χ) ≤ 1 := by
    intro χ
    by_cases hχ : χ = 1
    · rw [hχ, hwt1]; exact ha1
    · rw [hwtc χ hχ, hc1]
  obtain ⟨-, hcentr⟩ := sz5e1_weights_forms hF (Z.map ρ) hEc hE2 hwt
  apply hst
  apply hρ
  rw [map_mul, map_mul]
  apply hcentr
  · rintro _ ⟨z', hz', rfl⟩
    rw [← map_mul, ← map_mul, hZc z' hz' s hs]
  · rintro _ ⟨z', hz', rfl⟩
    rw [← map_mul, ← map_mul, hZc z' hz' t ht]

theorem comm_of_forall_sq {D : Type} [Group D] (E : Subgroup D) (h2 : ∀ a ∈ E, a ^ 2 = 1) :
    ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
  intro a ha b hb
  have h1 : (a * b) ^ 2 = 1 := h2 _ (E.mul_mem ha hb)
  have h3 : a ^ 2 = 1 := h2 a ha
  have h4 : b ^ 2 = 1 := h2 b hb
  have ha' : a⁻¹ = a := by
    have : a * a = 1 := by rw [← pow_two]; exact h3
    exact inv_eq_of_mul_eq_one_right this
  have hb' : b⁻¹ = b := by
    have : b * b = 1 := by rw [← pow_two]; exact h4
    exact inv_eq_of_mul_eq_one_right this
  have hab : (a * b)⁻¹ = a * b := by
    have : a * b * (a * b) = 1 := by rw [← pow_two]; exact h1
    exact inv_eq_of_mul_eq_one_right this
  calc a * b = (a * b)⁻¹ := hab.symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [ha', hb']

theorem sq_eq_one_of_card_le_two {D : Type} [Group D] [Finite D] (E : Subgroup D)
    (hE : Nat.card E ≤ 2) : ∀ a ∈ E, a ^ 2 = 1 := by
  intro a ha
  have hpos : 0 < Nat.card E := Nat.card_pos
  have hpow : (⟨a, ha⟩ : E) ^ Nat.card E = 1 := pow_card_eq_one'
  have : Nat.card E = 1 ∨ Nat.card E = 2 := by omega
  rcases this with h | h
  · rw [h, pow_one] at hpow
    have : a = 1 := congrArg Subtype.val hpow
    rw [this, one_pow]
  · rw [h] at hpow
    exact congrArg Subtype.val hpow

theorem normal_zpowers_of_central {D : Type} [Group D] (p : D) (hp : ∀ d : D, p * d = d * p) :
    (Subgroup.zpowers p).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  have hc : Commute g p := (hp g).symm
  rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
  exact (Subgroup.zpowers p).zpow_mem (Subgroup.mem_zpowers p) k

theorem exists_involution_of_pGroup {D : Type} [Group D] [Finite D] (P : Subgroup D)
    (hP : IsPGroup 2 P) (hne : P ≠ ⊥) : ∃ z ∈ P, z ≠ 1 ∧ z ^ 2 = 1 := by
  have hcard : 2 ∣ Nat.card P := by
    rcases hP.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq P h) hne
    · exact h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) 2 hcard
  refine ⟨(x : D), x.2, ?_, ?_⟩
  · intro h1
    have h3 : orderOf (x : D) = 1 := by rw [h1]; exact orderOf_one
    rw [Subgroup.orderOf_coe, hx] at h3
    omega
  · have h3 : (x : D) ^ orderOf (x : D) = 1 := pow_orderOf_eq_one _
    rwa [Subgroup.orderOf_coe, hx] at h3

theorem sz5e1_P_central {D : Type} [Group D] [Finite D] (P : Subgroup D) [P.Normal]
    (hD : SzSetup D P) {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    [Module.Finite F V] (hF : ringChar F ≠ 2) (ρ : D →* (V ≃ₗ[F] V)) (hρ : Function.Injective ρ)
    (hirr : IsIrreducibleRep ρ) (hdim : Module.finrank F V ≤ 12) :
    ∀ p ∈ P, ∀ d : D, p * d = d * p := by
  have hS1' : ∀ E : Subgroup D, E.Normal → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      (∀ a ∈ E, a ^ 2 = 1) → ∀ e ∈ E, ρ e = 1 ∨ ρ e = negOne F V := by
    intro E hE hc h2
    have := hE
    exact sz5e1_normal_elem_scalar P hD hF ρ hirr hdim E hc h2
  have hsimple : IsSimpleGroup (D ⧸ P) := hD.simple
  have : Nontrivial D := (QuotientGroup.mk'_surjective P).nontrivial
  have : Nontrivial V := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    have : Subsingleton (V ≃ₗ[F] V) :=
      ⟨fun f g => LinearEquiv.ext fun v => Subsingleton.elim _ _⟩
    exact not_subsingleton D (hρ.subsingleton)
  refine sz5e1_P_central_of_bounds P hD ?_ ?_
  · intro E hE hc h2
    have := hE
    classical
    let f : E → Fin 2 := fun e => if ρ e = 1 then 0 else 1
    have hf : Function.Injective f := by
      intro e₁ e₂ h
      have h₁ := hS1' E hE hc h2 e₁ e₁.2
      have h₂ := hS1' E hE hc h2 e₂ e₂.2
      apply Subtype.ext
      apply hρ
      by_cases hc1 : ρ e₁ = 1 <;> by_cases hc2 : ρ e₂ = 1
      · rw [hc1, hc2]
      · simp [f, hc1, hc2] at h
      · simp [f, hc1, hc2] at h
      · rw [h₁.resolve_left hc1, h₂.resolve_left hc2]
    calc Nat.card E ≤ Nat.card (Fin 2) := Nat.card_le_card_of_injective f hf
      _ = 2 := by simp
  · intro Q hQP hQ hcomm
    have := hQ
    set E : Subgroup D := ⁅Q, Q⁆ with hE
    have hEn : E.Normal := Subgroup.commutator_normal Q Q
    have h2 : ∀ a ∈ E, a ^ 2 = 1 := sq_eq_one_of_card_le_two E hcomm
    have hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := comm_of_forall_sq E h2
    have hscal := hS1' E hEn hc h2
    have hh := sz5e1_heisenberg (Q := ↥Q) (ρ.comp Q.subtype)
      (hρ.comp Subtype.val_injective) (by
        intro x y
        have hmem : ⁅(x : D), (y : D)⁆ ∈ E := Subgroup.commutator_mem_commutator x.2 y.2
        simpa [commutatorElement_def] using hscal _ hmem)
    calc (Subgroup.center ↥Q).index ≤ (Module.finrank F V) ^ 2 := hh
      _ ≤ 12 ^ 2 := Nat.pow_le_pow_left hdim 2
      _ = 144 := by norm_num

private theorem core_D_data {D : Type} [Group D] [Finite D] (P : Subgroup D) [P.Normal]
    (hD : SzSetup D P) {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    [Module.Finite F V] (hF : ringChar F ≠ 2) (ρ : D →* (V ≃ₗ[F] V)) (hρ : Function.Injective ρ)
    (hirr : IsIrreducibleRep ρ) (hdim : Module.finrank F V ≤ 12) {r : ℕ}
    (hfix : FixBound ρ r) (hP : P ≠ ⊥) :
    ∃ (E : Subgroup (V ≃ₗ[F] V)) (a c : ℕ), (∀ e ∈ E, ∃ d : D, ρ d = e) ∧
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x ^ 2 = 1) ∧ 1 ≤ c ∧
      a + 3 * c ≤ r ∧ 4 * c ≤ r ∧ Module.finrank F (wt E 1) = a ∧
      ∀ χ : ↥E →* Fˣ, χ ≠ 1 → Module.finrank F (wt E χ) = c := by
  have hPc := sz5e1_P_central P hD hF ρ hρ hirr hdim
  have hneg : ∀ z ∈ P, z ≠ 1 → z ^ 2 = 1 → ρ z = negOne F V := by
    intro z hz hz1 hz2
    have := normal_zpowers_of_central z (fun d => hPc z hz d)
    have hzc : ∀ a ∈ Subgroup.zpowers z, ∀ b ∈ Subgroup.zpowers z, a * b = b * a := by
      intro a ha b hb
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_zpow_self z i j).eq
    rcases sz5e1_normal_elem_scalar P hD hF ρ hirr hdim (Subgroup.zpowers z) hzc
      (sq_eq_one_of_mem_zpowers z hz2) z (Subgroup.mem_zpowers z) with h | h
    · exact absurd (hρ (by rw [h, map_one])) hz1
    · exact h
  have hΩ : ∀ p ∈ P, ∀ q ∈ P, p ^ 2 = 1 → q ^ 2 = 1 → p = 1 ∨ q = 1 ∨ p = q := by
    intro p hp q hq hp2 hq2
    by_cases h1 : p = 1
    · exact Or.inl h1
    by_cases h2 : q = 1
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (hρ ((hneg p hp h1 hp2).trans (hneg q hq h2 hq2).symm)))
  obtain ⟨S, Z, yb, hZS, hZc, hZ8, hZ2, -, hy7, hyZ, hyf⟩ := sz5e1_sz8_frobenius hD.2.2
  have hZcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb => hZc a ha b (hZS hb)
  obtain ⟨E, y, hE8, hEc, hE2, hEP, -, hy7', hyE, hyf'⟩ :=
    sz5e1_lift P hPc hD.2.1 hΩ Z hZ8 hZcomm hZ2 yb hy7 hyZ hyf
  obtain ⟨hEc', hE2', a, c, hc, -, hwt1, hwtc, hfixE⟩ :=
    weights_of_frobenius hF ρ hρ E y hE8 hEc hE2 hy7' hyE hyf'
  obtain ⟨b, hbE, hb1⟩ := exists_ne_one_of_card_eq_eight E hE8
  obtain ⟨z, hzP, hz1, hz2⟩ := exists_involution_of_pGroup P hD.2.1 hP
  have hρz := hneg z hzP hz1 hz2
  have hb2 := hE2 b hbE
  have h1 : a + 3 * c ≤ r := by
    have h' : Module.finrank F (fixSpaceOf (ρ b)) ≤ r :=
      hfix b hb1 (isPGroup_two_zpowers_of_sq b hb2)
    rw [(hfixE b hbE hb1).1] at h'
    exact h'
  have hbz1 : b * z ≠ 1 := by
    intro h
    have hbP : b ∈ P := by
      have : b = z⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this]
      exact P.inv_mem hzP
    have hmem : b ∈ E ⊓ P := ⟨hbE, hbP⟩
    rw [hEP] at hmem
    exact hb1 hmem
  have hbz2 : (b * z) ^ 2 = 1 := by
    have hcomm : Commute b z := (hPc z hzP b).symm
    rw [hcomm.mul_pow, hb2, hz2, one_mul]
  have h2 : 4 * c ≤ r := by
    have h' : Module.finrank F (fixSpaceOf (ρ (b * z))) ≤ r :=
      hfix (b * z) hbz1 (isPGroup_two_zpowers_of_sq _ hbz2)
    rw [map_mul, hρz, ← negOne_mul_comm, (hfixE b hbE hb1).2] at h'
    exact h'
  exact ⟨E.map ρ, a, c, fun e he => by obtain ⟨d, -, rfl⟩ := he; exact ⟨d, rfl⟩, hEc', hE2', hc,
    h1, h2, hwt1, hwtc⟩

theorem sz5e1_core_D2 {D : Type} [Group D] [Finite D] (P : Subgroup D) [P.Normal]
    (hD : SzSetup D P) {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    [Module.Finite F V] (hF : ringChar F ≠ 2) (ρ : D →* (V ≃ₗ[F] V)) (hρ : Function.Injective ρ)
    (hirr : IsIrreducibleRep ρ) (hdim : Module.finrank F V ≤ 12) (hfix : FixBound ρ 4) :
    NoInvariantAlt ρ := by
  by_cases hP : P = ⊥
  · exfalso
    subst hP
    exact sz5e1_core_D1 (isSz_of_mulEquiv QuotientGroup.quotientBot hD.2.2) hF ρ hρ hfix
  · obtain ⟨E, a, c, hEρ, hEc, hE2, hc, h1, h2, hwt1, hwtc⟩ :=
      core_D_data P hD hF ρ hρ hirr hdim hfix hP
    have hwt : ∀ χ : ↥E →* Fˣ, Module.finrank F (wt E χ) ≤ 1 := by
      intro χ
      by_cases hχ : χ = 1
      · rw [hχ, hwt1]; omega
      · rw [hwtc χ hχ]; omega
    obtain ⟨hform, -⟩ := sz5e1_weights_forms hF E hEc hE2 hwt
    intro f hf hinv
    apply hform f hf
    intro e he v w
    obtain ⟨d, rfl⟩ := hEρ e he
    exact hinv d v w

theorem sz5e1_core_D3 {D : Type} [Group D] [Finite D] (P : Subgroup D) [P.Normal]
    (hD : SzSetup D P) {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    [Module.Finite F V] (hF : ringChar F ≠ 2) (ρ : D →* (V ≃ₗ[F] V)) (hρ : Function.Injective ρ)
    (hirr : IsIrreducibleRep ρ) (hdim : Module.finrank F V ≤ 12) (hfix : FixBound ρ 3) :
    False := by
  by_cases hP : P = ⊥
  · subst hP
    exact sz5e1_core_D1 (isSz_of_mulEquiv QuotientGroup.quotientBot hD.2.2) hF ρ hρ
      (fixBound_mono hfix (by norm_num))
  · obtain ⟨E, a, c, -, -, -, hc, -, h2, -, -⟩ := core_D_data P hD hF ρ hρ hirr hdim hfix hP
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Sz5
