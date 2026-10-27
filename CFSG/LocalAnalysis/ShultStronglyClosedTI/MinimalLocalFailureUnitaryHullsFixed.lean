module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureChainInterface
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PairInvolutionFixedFieldOrbit
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairModelAlignment

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryHulls

open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.ShultStronglyClosedTI.ProperPairModel
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type} [Group G]

theorem card_rightFixedSet_conj (H : Subgroup G) (u g : G) :
    Nat.card (rightFixedSet H (g⁻¹ * u * g)) = Nat.card (rightFixedSet H u) := by
  have h₁ : ∀ ω ∈ rightFixedSet H u, rightCosetTranslate H ω g ∈ rightFixedSet H (g⁻¹ * u * g) :=
    fun ω hω => by
      change rightCosetTranslate H (rightCosetTranslate H ω g) (g⁻¹ * u * g) = _
      rw [rightCosetTranslate_mul, show g * (g⁻¹ * u * g) = u * g by group,
        ← rightCosetTranslate_mul, hω]
  have h₂ : ∀ ω ∈ rightFixedSet H (g⁻¹ * u * g), rightCosetTranslate H ω g⁻¹ ∈ rightFixedSet H u :=
    fun ω hω => by
      change rightCosetTranslate H (rightCosetTranslate H ω g⁻¹) u = _
      change rightCosetTranslate H ω (g⁻¹ * u * g) = ω at hω
      rw [rightCosetTranslate_mul, show g⁻¹ * u = g⁻¹ * u * g * g⁻¹ by group,
        ← rightCosetTranslate_mul, hω]
  refine (Nat.card_congr
    { toFun := fun ω => ⟨rightCosetTranslate H ω g, h₁ ω ω.2⟩
      invFun := fun ω => ⟨rightCosetTranslate H ω g⁻¹, h₂ ω ω.2⟩
      left_inv := fun ω => Subtype.ext ?_
      right_inv := fun ω => Subtype.ext ?_ }).symm
  · change rightCosetTranslate H (rightCosetTranslate H ω g) g⁻¹ = ω
    rw [rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one]
  · change rightCosetTranslate H (rightCosetTranslate H ω g⁻¹) g = ω
    rw [rightCosetTranslate_mul, inv_mul_cancel, rightCosetTranslate_one]

theorem exists_fixed_of_not_dvd [Finite G] {H A : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hA : IsPGroup p A) {Δ : Set (rightCosetSpace H)}
    (hstable : ∀ a ∈ A, ∀ ω ∈ Δ, rightCosetTranslate H ω a ∈ Δ) (hpΔ : ¬ p ∣ Nat.card Δ) :
    ∃ ω ∈ Δ, ∀ a ∈ A, rightCosetTranslate H ω a = ω := by
  let act : MulAction A Δ :=
    { smul := fun a ω => ⟨rightCosetTranslate H ω (a : G)⁻¹, hstable _ (A.inv_mem a.2) _ ω.2⟩
      one_smul := fun ω => Subtype.ext (by
        change rightCosetTranslate H ω ((1 : A) : G)⁻¹ = ω
        rw [Subgroup.coe_one, inv_one, rightCosetTranslate_one])
      mul_smul := fun a b ω => Subtype.ext (by
        change rightCosetTranslate H ω ((a * b : A) : G)⁻¹ =
          rightCosetTranslate H (rightCosetTranslate H ω (b : G)⁻¹) (a : G)⁻¹
        rw [rightCosetTranslate_mul, Subgroup.coe_mul, mul_inv_rev]) }
  obtain ⟨ω, hω⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card Δ hpΔ
  refine ⟨ω, ω.2, fun a ha => ?_⟩
  have h := congrArg Subtype.val (hω (⟨a, ha⟩ : A)⁻¹)
  change rightCosetTranslate H ω (((⟨a, ha⟩ : A)⁻¹ : A) : G)⁻¹ = ω at h
  simpa only [Subgroup.coe_inv, inv_inv] using h

theorem exists_conj_fixed [Finite G] {A : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hA : IsPGroup p A) {S : Set G} (hS : ∀ a ∈ A, ∀ r ∈ S, a⁻¹ * r * a ∈ S)
    (hpS : ¬ p ∣ Nat.card S) : ∃ r ∈ S, ∀ a ∈ A, a⁻¹ * r * a = r := by
  let act : MulAction A S :=
    { smul := fun a r => ⟨(a : G) * r * (a : G)⁻¹, by
        simpa only [inv_inv] using hS (a : G)⁻¹ (A.inv_mem a.2) r r.2⟩
      one_smul := fun r => Subtype.ext (by
        change ((1 : A) : G) * r * ((1 : A) : G)⁻¹ = r
        simp)
      mul_smul := fun a b r => Subtype.ext (by
        change ((a * b : A) : G) * r * ((a * b : A) : G)⁻¹ =
          (a : G) * ((b : G) * r * (b : G)⁻¹) * (a : G)⁻¹
        simp only [Subgroup.coe_mul]
        group) }
  obtain ⟨r, hr⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card S hpS
  refine ⟨r, r.2, fun a ha => ?_⟩
  have h := congrArg Subtype.val (hr (⟨a, ha⟩ : A)⁻¹)
  change (((⟨a, ha⟩ : A)⁻¹ : A) : G) * r * (((⟨a, ha⟩ : A)⁻¹ : A) : G)⁻¹ = r at h
  simpa only [Subgroup.coe_inv, inv_inv] using h

theorem card_fixed_ge [Finite G] {H Q A : Subgroup G} {z u : G}
    (hdatum : InvolutionPointLocalEmbedding H z)
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z)
    (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hA : IsPGroup p A) (hAH : A ≤ H)
    (hAQ : ∀ a ∈ A, ∀ e ∈ Q, a * e = e * a) (hAu : ∀ a ∈ A, a * u = u * a)
    (huH : u ∈ H) (hQu : ∀ e ∈ Q, e * u = u * e)
    (hΔ : ∀ e ∈ Q, u * e ∈ involutionPointClass u)
    {f : ℕ} (hq : Nat.card Q = 2 ^ f)
    (hfix : Nat.card (rightFixedSet H u) = Nat.card Q ^ 3 + 1) :
    Nat.card Q ^ 2 + 1 ≤
      Nat.card {ω : rightCosetSpace H | ∀ a ∈ A, rightCosetTranslate H ω a = ω} := by
  set α := rightCosetMk H 1
  have hQH : Q ≤ H := point_subgroup_le hdatum.distinguished_mem hQclass
  have hfreeQ : ∀ e ∈ Q, e ≠ 1 → ∀ ω, rightCosetTranslate H ω e = ω → ω = α := by
    intro e he he1 ω hω
    exact class_fixed_unique hdatum (point_subgroup_class hdatum hQclass ⟨he, he1⟩) hω
      ((translate_base_iff H e).mpr (hQH he))
  have hαH : ∀ g ∈ H, ∀ ω, rightCosetTranslate H ω g = α → ω = α := by
    intro g hg ω hω
    have h := congrArg (fun γ => rightCosetTranslate H γ g⁻¹) hω
    simp only [rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one] at h
    rw [h]
    exact (translate_base_iff H _).mpr (H.inv_mem hg)
  let X : Q → Set (rightCosetSpace H) :=
    fun e => {ω | rightCosetTranslate H ω (u * e) = ω ∧ ω ≠ α}
  have hXcard : ∀ e : Q, Nat.card (X e) = Nat.card Q ^ 3 := by
    intro e
    obtain ⟨g, hg⟩ := hΔ e e.2
    have hcard := card_rightFixedSet_conj H u g
    rw [show g⁻¹ * u * g = u * e from hg, hfix] at hcard
    have hα : α ∈ rightFixedSet H (u * e) :=
      (translate_base_iff H _).mpr (H.mul_mem huH (hQH e.2))
    have hXe : X e = rightFixedSet H (u * e) \ {α} := by
      ext ω
      simp only [X, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff, rightFixedSet]
    rw [hXe, Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem hα, ← Nat.card_coe_set_eq,
      hcard, Nat.add_sub_cancel]
  have hcomm : ∀ e e' : Q, (e' : G) * (u * e) = u * e * e' := fun e e' => by
    rw [← mul_assoc, hQu _ e'.2, mul_assoc, hQab _ e'.2 _ e.2, ← mul_assoc]
  have hXstable : ∀ e : Q, ∀ a ∈ A, ∀ ω ∈ X e, rightCosetTranslate H ω a ∈ X e := by
    rintro e a ha ω ⟨hω, hωα⟩
    refine ⟨?_, fun h => hωα (hαH a (hAH ha) ω h)⟩
    rw [rightCosetTranslate_mul, show a * (u * e) = u * e * a by
      rw [← mul_assoc, hAu a ha, mul_assoc, hAQ a ha _ e.2, ← mul_assoc], ← rightCosetTranslate_mul,
      hω]
  have hp : ¬ p ∣ Nat.card Q ^ 3 := by
    rw [hq, ← pow_mul]
    intro hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow hdvd))
  have hex : ∀ e : Q, ∃ ω ∈ X e, ∀ a ∈ A, rightCosetTranslate H ω a = ω :=
    fun e => exists_fixed_of_not_dvd hA (hXstable e) (by rw [hXcard e]; exact hp)
  choose γ hγX hγA using hex
  have hFfix : ∀ x : Q × Q, ∀ a ∈ A,
      rightCosetTranslate H (rightCosetTranslate H (γ x.1) x.2) a =
        rightCosetTranslate H (γ x.1) x.2 := by
    intro x a ha
    rw [rightCosetTranslate_mul, ← hAQ a ha _ x.2.2, ← rightCosetTranslate_mul, hγA x.1 a ha]
  let F : Q × Q → {ω : rightCosetSpace H | ∀ a ∈ A, rightCosetTranslate H ω a = ω} :=
    fun x => ⟨rightCosetTranslate H (γ x.1) x.2, hFfix x⟩
  have hFα : ∀ x : Q × Q, rightCosetTranslate H (γ x.1) x.2 ≠ α :=
    fun x h => (hγX x.1).2 (hαH _ (hQH x.2.2) _ h)
  have hfixe : ∀ x : Q × Q, rightCosetTranslate H (rightCosetTranslate H (γ x.1) x.2)
      (u * x.1) = rightCosetTranslate H (γ x.1) x.2 := by
    intro x
    rw [rightCosetTranslate_mul, hcomm, ← rightCosetTranslate_mul, (hγX x.1).1]
  have hFinj : Function.Injective F := by
    rintro ⟨e₁, e₁'⟩ ⟨e₂, e₂'⟩ hF
    have hω : rightCosetTranslate H (γ e₁) e₁' = rightCosetTranslate H (γ e₂) e₂' :=
      congrArg Subtype.val hF
    have he : e₁ = e₂ := by
      by_contra hne
      set ω := rightCosetTranslate H (γ e₁) e₁' with hωdef
      have h1 : rightCosetTranslate H ω (u * e₁) = ω := hfixe (e₁, e₁')
      have h2 : rightCosetTranslate H ω (u * e₂) = ω := by
        rw [hω]
        exact hfixe (e₂, e₂')
      have h1' : rightCosetTranslate H ω (u * e₁)⁻¹ = ω := by
        conv_lhs => rw [← h1]
        rw [rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one]
      have hprod : rightCosetTranslate H ω ((e₁ : G)⁻¹ * e₂) = ω := by
        rw [show (e₁ : G)⁻¹ * e₂ = (u * e₁)⁻¹ * (u * e₂) by group, ← rightCosetTranslate_mul,
          h1', h2]
      have hne' : (e₁ : G)⁻¹ * e₂ ≠ 1 := fun h1 => hne (Subtype.ext (by
        rw [← inv_mul_eq_one]; exact h1))
      exact hFα (e₁, e₁') (hfreeQ _ (Q.mul_mem (Q.inv_mem e₁.2) e₂.2) hne' _ hprod)
    subst he
    have he' : (e₁' : G) * (e₂' : G)⁻¹ = 1 := by
      by_contra hne
      apply (hγX e₁).2
      refine hfreeQ _ (Q.mul_mem e₁'.2 (Q.inv_mem e₂'.2)) hne _ ?_
      rw [← rightCosetTranslate_mul, hω, rightCosetTranslate_mul, mul_inv_cancel,
        rightCosetTranslate_one]
    exact Prod.ext rfl (Subtype.ext (mul_inv_eq_one.mp he'))
  have hαfix : α ∈ {ω : rightCosetSpace H | ∀ a ∈ A, rightCosetTranslate H ω a = ω} :=
    fun a ha => (translate_base_iff H a).mpr (hAH ha)
  let F' : Option (Q × Q) → {ω : rightCosetSpace H | ∀ a ∈ A, rightCosetTranslate H ω a = ω} :=
    fun o => o.elim ⟨α, hαfix⟩ F
  have hF'inj : Function.Injective F' := by
    rintro (_ | x) (_ | y) h
    · rfl
    · exact absurd (congrArg Subtype.val h).symm (hFα y)
    · exact absurd (congrArg Subtype.val h) (hFα x)
    · exact congrArg some (hFinj h)
  have hle := Nat.card_le_card_of_injective F' hF'inj
  rwa [Finite.card_option, Nat.card_prod, ← pow_two] at hle

theorem fixed_mem_centralizer_orbit [Finite G] {H Q A : Subgroup G} {z : G}
    (hdatum : InvolutionPointLocalEmbedding H z)
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z)
    {p : ℕ} [Fact p.Prime] (hA : IsPGroup p A) (hpq : ¬ p ∣ Nat.card Q - 1)
    (hDY : involutionPointClass z ∩ (Subgroup.centralizer (A : Set G) : Set G) =
      conjugacyWithin (Subgroup.centralizer (A : Set G)) z)
    {γ : rightCosetSpace H} (hγ : ∀ a ∈ A, rightCosetTranslate H γ a = γ) :
    ∃ y ∈ Subgroup.centralizer (A : Set G), rightCosetTranslate H (rightCosetMk H 1) y = γ := by
  obtain ⟨g, rfl⟩ := exists_rightCosetMk γ
  let S : Set G := {r | r ∈ involutionPointClass z ∧
    rightCosetTranslate H (rightCosetMk H g) r = rightCosetMk H g}
  have hS : ∀ a ∈ A, ∀ r ∈ S, a⁻¹ * r * a ∈ S := by
    rintro a ha r ⟨hrD, hr⟩
    refine ⟨conj_mem_pointClass hrD a, ?_⟩
    have ha' : rightCosetTranslate H (rightCosetMk H g) a⁻¹ = rightCosetMk H g := by
      conv_lhs => rw [← hγ a ha]
      rw [rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one]
    rw [← rightCosetTranslate_mul, ← rightCosetTranslate_mul, ha', hr, hγ a ha]
  have hScard : Nat.card S = Nat.card Q - 1 := by
    rw [← card_diff_one Q, ← class_inter_point hdatum hQclass]
    refine Nat.card_congr
      { toFun := fun r => ⟨g * r * g⁻¹, by simpa only [inv_inv] using conj_mem_pointClass r.2.1 g⁻¹,
          (translate_mk_fixed_iff H g r).mp r.2.2⟩
        invFun := fun s => ⟨g⁻¹ * s * g, conj_mem_pointClass s.2.1 g,
          (translate_mk_fixed_iff H g _).mpr (by
            rw [show g * (g⁻¹ * (s : G) * g) * g⁻¹ = s by group]
            exact s.2.2)⟩
        left_inv := fun r => Subtype.ext (by simp only; group)
        right_inv := fun s => Subtype.ext (by simp only; group) }
  obtain ⟨r, ⟨hrD, hrγ⟩, hrA⟩ := exists_conj_fixed hA hS (by rw [hScard]; exact hpq)
  have hrY : r ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h := hrA a ha
    calc a * r = a * (a⁻¹ * r * a) := by rw [h]
      _ = r * a := by group
  have hrc : r ∈ conjugacyWithin (Subgroup.centralizer (A : Set G)) z := by
    rw [← hDY]
    exact ⟨hrD, hrY⟩
  obtain ⟨y, rfl⟩ := hrc
  refine ⟨y, y.2, class_fixed_unique hdatum hrD ?_ hrγ⟩
  rw [translate_base_mk, translate_mk_fixed_iff, show (y : G) * ((y : G)⁻¹ * z * y) * (y : G)⁻¹ =
    z by group]
  exact hdatum.distinguished_mem

end CFSG.ShultStronglyClosedTI.UnitaryHulls
