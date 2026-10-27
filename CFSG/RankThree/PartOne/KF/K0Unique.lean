module

public import CFSG.RankThree.PartOne.KF.K0SL2
public import CFSG.RankThree.PartOne.KF.K0SU3Root
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartOne.KFK0

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open scoped commutatorElement

theorem le_of_perfect_of_map_center_eq {M₀ : Type} [Group M₀] {A B : Subgroup M₀} (hB : ⁅B, B⁆ = B)
    (h : A.map (QuotientGroup.mk' (Subgroup.center M₀)) =
      B.map (QuotientGroup.mk' (Subgroup.center M₀))) : B ≤ A := by
  have hBle : B ≤ A ⊔ Subgroup.center M₀ := by
    intro b hb
    have : QuotientGroup.mk' (Subgroup.center M₀) b ∈
        A.map (QuotientGroup.mk' (Subgroup.center M₀)) := by
      rw [h]
      exact ⟨b, hb, rfl⟩
    obtain ⟨a, ha, hab⟩ := this
    have hz : a⁻¹ * b ∈ Subgroup.center M₀ := QuotientGroup.eq.1 hab
    have : b = a * (a⁻¹ * b) := by group
    rw [this]
    exact Subgroup.mul_mem_sup ha hz
  have hdec : ∀ g ∈ A ⊔ Subgroup.center M₀, ∃ a ∈ A, ∃ z ∈ Subgroup.center M₀, a * z = g := by
    intro g hg
    have := Subgroup.mul_normal A (Subgroup.center M₀)
    rw [← SetLike.mem_coe, this] at hg
    exact hg
  have hcen : ∀ z ∈ Subgroup.center M₀, ∀ g : M₀, ⁅z, g⁆ = 1 ∧ ⁅g, z⁆ = 1 := by
    intro z hz g
    exact ⟨commutatorElement_eq_one_iff_mul_comm.2 ((Subgroup.mem_center_iff.1 hz g).symm),
      commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hz g)⟩
  have hcomm : ∀ g₁ ∈ B, ∀ g₂ ∈ B, ⁅g₁, g₂⁆ ∈ A := by
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨a₁, ha₁, z₁, hz₁, rfl⟩ := hdec g₁ (hBle hg₁)
    obtain ⟨a₂, ha₂, z₂, hz₂, rfl⟩ := hdec g₂ (hBle hg₂)
    have e : ⁅a₁ * z₁, a₂ * z₂⁆ = ⁅a₁, a₂⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul, (hcen z₁ hz₁ _).1,
        commutatorElement_mul_right_eq_mul_conj, (hcen z₂ hz₂ _).2]
      group
    rw [e, commutatorElement_def]
    exact A.mul_mem (A.mul_mem (A.mul_mem ha₁ ha₂) (A.inv_mem ha₁)) (A.inv_mem ha₂)
  have : B = ⁅B, B⁆ := hB.symm
  rw [this]
  exact Subgroup.commutator_le.2 hcomm

theorem eq_of_perfect_of_map_center_eq {M₀ : Type} [Group M₀] {A B : Subgroup M₀} (hA : ⁅A, A⁆ = A)
    (hB : ⁅B, B⁆ = B) (h : A.map (QuotientGroup.mk' (Subgroup.center M₀)) =
      B.map (QuotientGroup.mk' (Subgroup.center M₀))) : A = B :=
  le_antisymm (le_of_perfect_of_map_center_eq hA h.symm) (le_of_perfect_of_map_center_eq hB h)

theorem exists_primitiveRoot_of_dvd {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card F - 1) : ∃ ζ : F, IsPrimitiveRoot ζ p := by
  classical
  have := Fact.mk hp
  have : Fintype F := Fintype.ofFinite F
  have hcard : Nat.card Fˣ = Nat.card F - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (hcard ▸ hdvd)
  exact ⟨(x : F), IsPrimitiveRoot.iff_orderOf.2 (by rw [orderOf_units, hx])⟩

section Lift

variable {K : Type} [Field K] {σ : K ≃+* K}

@[expose] def IsImg {M : Type} [Group M] (π : ↥(SU σ 3) →* M) (R : Subgroup M) (a : Fin 3 → K) : Prop :=
  ∀ r : M, r ∈ R ↔ ∃ x ∈ Qset σ a, π x = r

theorem IsImg.unique {M : Type} [Group M] {π : ↥(SU σ 3) →* M} {R R' : Subgroup M} {a : Fin 3 → K}
    (h : IsImg π R a) (h' : IsImg π R' a) : R = R' := by
  ext r
  rw [h r, h' r]

theorem normalized_of_image [CharP K 2] {M : Type} [Group M] (π : ↥(SU σ 3) →* M)
    (hker : ∀ z, π z = 1 → z ^ 3 = 1 ∧ ∀ g, g * z = z * g) {R : Subgroup M} {g : ↥(SU σ 3)}
    (hR : IsImg π R (smat g *ᵥ e0)) {u : ↥(SU σ 3)} (hnorm : ∀ r ∈ R, π u * r * (π u)⁻¹ ∈ R)
    {x' : ↥(SU σ 3)} (hx' : x' ∈ Qset σ (smat g *ᵥ e0)) : u * x' * u⁻¹ ∈ Qset σ (smat g *ᵥ e0) := by
  have hr : π x' ∈ R := (hR _).2 ⟨x', hx', rfl⟩
  obtain ⟨x₁, hx₁, hx₁π⟩ := (hR _).1 (hnorm _ hr)
  set z := x₁⁻¹ * (u * x' * u⁻¹) with hz
  have hπz : π z = 1 := by
    rw [hz, map_mul, map_inv, hx₁π, map_mul, map_mul, map_inv, inv_mul_cancel]
  obtain ⟨hz3, hzc⟩ := hker z hπz
  have hw : u * x' * u⁻¹ = x₁ * z := by rw [hz]; group
  have hw2 : (u * x' * u⁻¹) ^ 2 = 1 := by
    rw [conj_pow, sq_eq_one_of_mem_Qset g hx']
    group
  have hx₁2 : x₁ ^ 2 = 1 := sq_eq_one_of_mem_Qset g hx₁
  have hz2 : z ^ 2 = 1 := by
    have : (x₁ * z) ^ 2 = x₁ ^ 2 * z ^ 2 := by
      rw [sq, sq, sq, mul_assoc, ← mul_assoc z x₁ z, ← hzc x₁, mul_assoc, ← mul_assoc]
    rw [← hw, hw2, hx₁2, one_mul] at this
    exact this.symm
  have hz1 : z = 1 := by
    calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
      _ = 1 := by rw [hz3, hz2]; group
  rw [hw, hz1, mul_one]
  exact hx₁

end Lift

section Roots

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

theorem roots_of_SL2 (hK : Nat.card K = (2 ^ f) ^ 2) (hf1 : 1 ≤ f) {M₀ M : Type} [Group M₀] [Group M]
    (κ : M₀ →* M) (π : ↥(SU (unitaryInvolution K 2 f) 3) →* M) (hπ : Function.Surjective π)
    (hker : ∀ z, π z = 1 → z ^ 3 = 1 ∧ ∀ g, g * z = z * g) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ f - 1) {u₀ : M₀} {B : Subgroup M₀} {F₁ : Type} [Field F₁] [Finite F₁] [CharP F₁ 2]
    (hF₁ : Nat.card F₁ = 2 ^ f) (ψ : SpecialLinearGroup (Fin 2) F₁ ≃* B)
    (hinj : ∀ x ∈ B, κ x = 1 → x = 1) (hu₀B : u₀ ∈ B) (hu₀ : u₀ ^ p = 1) (hu₀1 : κ u₀ ≠ 1)
    {u : ↥(SU (unitaryInvolution K 2 f) 3)} (hπu : π u = κ u₀) {v w : Fin 3 → K}
    (hvw : ∀ y : Fin 3 → K, y ≠ 0 → hf (unitaryInvolution K 2 f) y y = 0 →
      ∀ x' ∈ Qset (unitaryInvolution K 2 f) y, x' ≠ 1 →
        u * x' * u⁻¹ ∈ Qset (unitaryInvolution K 2 f) y →
          Qset (unitaryInvolution K 2 f) y = Qset (unitaryInvolution K 2 f) v ∨
            Qset (unitaryInvolution K 2 f) y = Qset (unitaryInvolution K 2 f) w) :
    ∃ R₁ R₂ : Subgroup M, R₁ ⊔ R₂ = B.map κ ∧ R₁ ≠ R₂ ∧
      ((IsImg π R₁ v ∧ IsImg π R₂ w) ∨ (IsImg π R₁ w ∧ IsImg π R₂ v)) := by
  classical
  have : Finite M := Finite.of_surjective π hπ
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨ζ₁, hζ₁⟩ := exists_primitiveRoot_of_dvd hp (by rw [hF₁]; exact hpq)
  set u₀' : ↥B := ⟨u₀, hu₀B⟩ with hu₀'
  have hu₀'p : u₀' ^ p = 1 := Subtype.ext (by simpa using hu₀)
  have hu₀'1 : u₀' ≠ 1 := fun h => hu₀1 (by
    have := congrArg Subtype.val h
    simp only [hu₀', OneMemClass.coe_one] at this
    rw [this, map_one])
  obtain ⟨R₁, R₂, hc1, hc2, hex1, hex2, hn1, hn2, hne, hsup⟩ :=
    exists_two_roots ψ hp.pos hpodd hζ₁ hu₀'p hu₀'1
  set κB : ↥B →* M := κ.comp B.subtype with hκB
  have hκBinj : Function.Injective κB :=
    (injective_iff_map_eq_one κB).2 fun a ha => Subtype.ext (hinj a a.2 ha)
  have key : ∀ R : Subgroup ↥B, Nat.card R = Nat.card F₁ → (∀ x ∈ R, x ^ 2 = 1) →
      (∀ x ∈ R, u₀' * x * u₀'⁻¹ ∈ R) → IsImg π (R.map κB) v ∨ IsImg π (R.map κB) w := by
    intro R hRc hR2 hRn
    have hcard : Nat.card (R.map κB) = 2 ^ f := by
      rw [Subgroup.card_map_of_injective hκBinj, hRc, hF₁]
    have hexp : ∀ r ∈ R.map κB, r ^ 2 = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hR2 x hx, map_one]
    obtain ⟨g, hg⟩ := exists_Rbar_eq_image hK hf1 π hπ (fun z hz => (hker z hz).1) hcard hexp
    have hnorm : ∀ r ∈ R.map κB, π u * r * (π u)⁻¹ ∈ R.map κB := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨u₀' * x * u₀'⁻¹, hRn x hx, ?_⟩
      rw [hπu, map_mul, map_mul, map_inv]
      rfl
    have hnt : Nontrivial ↥(R.map κB) :=
      Finite.one_lt_card_iff_nontrivial.1 (by rw [hcard]; exact Nat.one_lt_two_pow (by omega))
    obtain ⟨⟨r, hr⟩, hr1⟩ := exists_ne (1 : ↥(R.map κB))
    have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
    obtain ⟨x', hx'Q, hx'r⟩ := (hg r).1 hr
    have hx'1 : x' ≠ 1 := fun h => hr1' (by rw [← hx'r, h, map_one])
    have hux := normalized_of_image π hker hg hnorm hx'Q
    rcases hvw _ (smat_mulVec_e0_ne_zero g) (hf_smat_mulVec_e0 g) x' hx'Q hx'1 hux with h | h
    · left
      intro r'
      rw [hg r', h]
    · right
      intro r'
      rw [hg r', h]
  have h1 := key R₁ hc1 hex1 hn1
  have h2 := key R₂ hc2 hex2 hn2
  have hne' : R₁.map κB ≠ R₂.map κB := fun h => hne (Subgroup.map_injective hκBinj h)
  refine ⟨R₁.map κB, R₂.map κB, ?_, hne', ?_⟩
  · rw [← Subgroup.map_sup, hsup, Subgroup.map_top]
    ext r
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  · rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (h1.unique h2) hne'
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (h1.unique h2) hne'

theorem subgroups_SL2_unique (hK : Nat.card K = (2 ^ f) ^ 2) (hf1 : 1 ≤ f) {M₀ M : Type} [Group M₀]
    [Group M] (κ : M₀ →* M) (π : ↥(SU (unitaryInvolution K 2 f) 3) →* M)
    (hπ : Function.Surjective π) (hker : ∀ z, π z = 1 → z ^ 3 = 1 ∧ ∀ g, g * z = z * g)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f - 1) {u₀ : M₀} (hu₀ : u₀ ^ p = 1)
    (hu₀1 : κ u₀ ≠ 1) {B B' : Subgroup M₀} {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁]
    [Finite F₂] [CharP F₁ 2] [CharP F₂ 2] (hF₁ : Nat.card F₁ = 2 ^ f) (hF₂ : Nat.card F₂ = 2 ^ f)
    (ψ : SpecialLinearGroup (Fin 2) F₁ ≃* B) (ψ' : SpecialLinearGroup (Fin 2) F₂ ≃* B')
    (hinj : ∀ x ∈ B, κ x = 1 → x = 1) (hinj' : ∀ x ∈ B', κ x = 1 → x = 1) (hu₀B : u₀ ∈ B)
    (hu₀B' : u₀ ∈ B') : B.map κ = B'.map κ := by
  classical
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨g, hg⟩ := hπ (κ u₀)
  have hgp : g ^ (3 * p) = 1 := by
    have h1 : π (g ^ p) = 1 := by rw [map_pow, hg, ← map_pow, hu₀, map_one]
    have := (hker _ h1).1
    rwa [← pow_mul, mul_comm] at this
  have hcop : Nat.Coprime 3 p := (Nat.coprime_primes (by norm_num) hp).2 (by omega)
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega)
  set u : ↥(SU (unitaryInvolution K 2 f) 3) := g ^ (3 * m) with hu
  have hup : u ^ p = 1 := by
    rw [hu, ← pow_mul, show 3 * m * p = 3 * p * m by ring, pow_mul, hgp, one_pow]
  have hπu : π u = κ u₀ := by
    rw [hu, map_pow, hg, ← map_pow]
    congr 1
    have h3m : 3 * m = p * (3 * m / p) + 1 := by
      have := Nat.div_add_mod (3 * m) p
      omega
    rw [h3m, pow_add, pow_mul, hu₀, one_pow, one_mul, pow_one]
  have hu1 : u ≠ 1 := fun h => hu₀1 (by rw [← hπu, h, map_one])
  have hdvd : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpq.trans (by simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (2 ^ f) 1 2)
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd hp hdvd
  obtain ⟨v, w, hvw⟩ := core_Qset hK hp.pos hpodd hζ hpq hup hu1
  obtain ⟨R₁, R₂, hs, -, hR⟩ :=
    roots_of_SL2 hK hf1 κ π hπ hker hp hp5 hpq hF₁ ψ hinj hu₀B hu₀ hu₀1 hπu hvw
  obtain ⟨R₁', R₂', hs', -, hR'⟩ :=
    roots_of_SL2 hK hf1 κ π hπ hker hp hp5 hpq hF₂ ψ' hinj' hu₀B' hu₀ hu₀1 hπu hvw
  rw [← hs, ← hs']
  rcases hR with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases hR' with ⟨b1, b2⟩ | ⟨b1, b2⟩
  · rw [a1.unique b1, a2.unique b2]
  · rw [a1.unique b2, a2.unique b1, sup_comm]
  · rw [a1.unique b2, a2.unique b1, sup_comm]
  · rw [a1.unique b1, a2.unique b2]

end Roots

end CFSG.RankThree.PartOne.KFK0
