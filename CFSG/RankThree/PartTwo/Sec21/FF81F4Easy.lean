
module

public import CFSG.RankThree.PartTwo.Sec21.FF81F4Trans
public import CFSG.Monster.B.GSide.HSylowBetaF4
public import CFSG.LieType.Simplicity.TitsSimple
public import CFSG.Adapters.TauCetiExceptional.BridgeTransport
public import CFSG.RankThree.PartTwo.Sec21.FF81F4GraphBase

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.F4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
  CFSG.RankThree.PartTwo.Sec21.FF79.L41 CFSG.RankThree.PartTwo.Sec21.FF81
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

abbrev F42C : Type := adjointGroup ReeTag.F4.tag (ZMod 2)

theorem exists_model_zmod {X : Type} [Group X] {Y : Subgroup X}
    (h : ChevalleyExceptionalModel (↥Y) .F4 2 1) : Nonempty (↥Y ≃* F42C) := by
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := f4_exists_model h
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  exact ⟨e.trans (CFSG.TauCetiBridge.adjointGroupCongr
    (ZMod.ringEquivOfPrime K Nat.prime_two hF).symm)⟩

section Clauses

variable {X : Type} [Group X] {Y : Subgroup X}

theorem clause_center (e : ↥Y ≃* F42C) : ∀ z ∈ Y, (∀ y ∈ Y, z * y = y * z) → z = 1 := by
  intro z hz hc
  have h1 : e ⟨z, hz⟩ = 1 := by
    apply f4_center_trivial
    intro w
    apply e.symm.injective
    apply Subtype.ext
    simp only [map_mul, MulEquiv.symm_apply_apply, Subgroup.coe_mul]
    exact hc _ (e.symm w).2
  have : (⟨z, hz⟩ : ↥Y) = 1 := e.injective (h1.trans (map_one e).symm)
  exact congrArg Subtype.val this

theorem aut_mul_conj {G : Type*} [Group G] (φ : MulAut G) (c : G) :
    φ * MulAut.conj c = MulAut.conj (φ c) * φ := by
  ext x
  simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem indAut_congr' (e : ↥Y ≃* F42C) {a b : X} (h : a = b) (ha : a ∈ Nor Y) (hb : b ∈ Nor Y) :
    indAut e ha = indAut e hb := by
  subst h
  rfl

theorem clause_outer_one (e : ↥Y ≃* F42C) [Finite X] {g : X} (hg : g ∈ Nor Y)
    (hout : ¬ ∃ y ∈ Y, ∀ x ∈ Y, g * x * g⁻¹ = y * x * y⁻¹) :
    ∃ y ∈ Y, ∀ x ∈ Y, (g * y) ^ 2 * x = x * (g * y) ^ 2 := by
  have hαo := (indAut_not_inner_iff e hg).2 hout
  obtain ⟨hord, hNF, -⟩ := even_F4_exact_automorphism_normal_form (f := 1) le_rfl (ZMod 2)
    (by rw [Nat.card_zmod]; norm_num)
  set φ := ReeTag.F4.finiteExceptionalAut (ZMod 2) with hφ
  have hφ2 : φ * φ = 1 := by
    have := pow_orderOf_eq_one φ
    rw [hord, show 2 * 1 = 2 from rfl, pow_two] at this
    exact this
  obtain ⟨⟨g0, k⟩, hgk, -⟩ := hNF (indAut e hg)
  have hk : (k : ℕ) = 1 := by
    have hk2 : (k : ℕ) < 2 := by simpa using k.2
    by_contra hne
    have h0 : (k : ℕ) = 0 := by omega
    rw [h0, pow_zero, mul_one] at hgk
    exact hαo ⟨g0, hgk.symm⟩
  rw [hk, pow_one] at hgk
  set c : F42C := φ g0⁻¹ with hc
  have hφc : φ c = g0⁻¹ := by
    have : (φ * φ) g0⁻¹ = g0⁻¹ := by rw [hφ2]; rfl
    simpa [MulAut.mul_apply, hc] using this
  have hcy : e ⟨ιY e c, ιY_mem e c⟩ = c := by
    have : (⟨ιY e c, ιY_mem e c⟩ : ↥Y) = e.symm c := rfl
    rw [this, MulEquiv.apply_symm_apply]
  set y : X := ιY e c with hy
  have hyY : y ∈ Y := ιY_mem e c
  have hyN : y ∈ Nor Y := Subgroup.le_normalizer hyY
  have hgyN : g * y ∈ Nor Y := mul_mem hg hyN
  have hind : indAut e hgyN = φ := by
    rw [indAut_mul e hg hyN hgyN, indAut_of_mem e hyY hyN, hcy, hgk, mul_assoc, aut_mul_conj φ c,
      hφc]
    rw [← mul_assoc, ← map_mul]
    simp
  have hsqN : (g * y) ^ 2 ∈ Nor Y := pow_mem hgyN 2
  have hsq : indAut e hsqN = 1 := by
    have : (g * y) ^ 2 = (g * y) * (g * y) := pow_two _
    have h2 := indAut_mul e hgyN hgyN (mul_mem hgyN hgyN)
    rw [indAut_congr' e this hsqN (mul_mem hgyN hgyN), h2, hind, hφ2]
  refine ⟨y, hyY, fun x hx => ?_⟩
  have := (indAut_eq_one_iff e hsqN).1 hsq x hx
  calc (g * y) ^ 2 * x = (g * y) ^ 2 * x * ((g * y) ^ 2)⁻¹ * (g * y) ^ 2 := by group
    _ = x * (g * y) ^ 2 := by rw [this]

theorem card_F42C : Nat.card F42C = 2 ^ 24 * 197358525 :=
  CFSG.Monster.B.GSide.natCard_adjointGroup_F4_zmod_two

theorem factorization_two_card : (2 ^ 24 * 197358525 : ℕ).factorization 2 = 24 := by
  rw [Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem factorization_three_card : (2 ^ 24 * 197358525 : ℕ).factorization 3 = 6 := by
  have h : (2 ^ 24 * 197358525 : ℕ) = 2 ^ 24 * 3 ^ 6 * (5 ^ 2 * 7 ^ 2 * 13 * 17) := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_mul (by norm_num)
    (by norm_num), Finsupp.add_apply, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization_pow Nat.prime_three,
    Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (p := 3) (n := 5 ^ 2 * 7 ^ 2 * 13 * 17) (by norm_num)]
  simp

theorem card_Y [Finite X] (e : ↥Y ≃* F42C) : Nat.card ↥Y = 2 ^ 24 * 197358525 :=
  (Nat.card_congr e.toEquiv).trans card_F42C

theorem card_sylow_two [Finite X] (e : ↥Y ≃* F42C) {U : Subgroup X} (hU : IsSylowOf 2 U Y) :
    Nat.card ↥U = 2 ^ 24 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_card_p hU, card_Y e, factorization_two_card]

theorem card_sylow_three [Finite X] (e : ↥Y ≃* F42C) {Q : Subgroup X} (hQ : IsSylowOf 3 Q Y) :
    Nat.card ↥Q = 3 ^ 6 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [isSylowOf_card_p hQ, card_Y e, factorization_three_card]

theorem clause_Z_fusion [Finite X] (e : ↥Y ≃* F42C) :
    ∀ U : Subgroup X, IsSylowOf 2 U Y → ∀ z₁ ∈ U, ∀ z₂ ∈ U, (∀ u ∈ U, z₁ * u = u * z₁) →
      (∀ u ∈ U, z₂ * u = u * z₂) → (∃ y ∈ Y, y * z₁ * y⁻¹ = z₂) → z₁ = z₂ := by
  intro U hU z₁ hz₁ z₂ hz₂ hc₁ hc₂ ⟨y, hy, hyz⟩
  have hUY : U ≤ Y := hU.1
  have hcard : Nat.card ↥(U.subgroupOf Y) = 2 ^ 24 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUY).toEquiv).trans (card_sylow_two e hU)
  obtain ⟨-, -, -, hfus⟩ := CFSG.Monster.B.GSide.sylow_facts_of_mulEquiv_F4 e hcard
  have hmem : ∀ z (hz : z ∈ U), (∀ u ∈ U, z * u = u * z) →
      (⟨z, hUY hz⟩ : ↥Y) ∈ U.subgroupOf Y ⊓ Subgroup.centralizer (U.subgroupOf Y : Set ↥Y) := by
    intro z hz hc
    refine ⟨Subgroup.mem_subgroupOf.2 hz, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro p hp
    apply Subtype.ext
    exact (hc p (Subgroup.mem_subgroupOf.1 hp)).symm
  have h := hfus ⟨z₁, hUY hz₁⟩ (hmem z₁ hz₁ hc₁) ⟨y, hy⟩ (by
    have : (⟨y, hy⟩ : ↥Y) * ⟨z₁, hUY hz₁⟩ * ⟨y, hy⟩⁻¹ = ⟨z₂, hUY hz₂⟩ := Subtype.ext hyz
    rw [this]
    exact hmem z₂ hz₂ hc₂)
  have h' : (⟨y, hy⟩ : ↥Y) * ⟨z₁, hUY hz₁⟩ * ⟨y, hy⟩⁻¹ = ⟨z₂, hUY hz₂⟩ := Subtype.ext hyz
  rw [h'] at h
  exact (congrArg Subtype.val h).symm

theorem exists_inf_cen_eq [Finite X] (e : ↥Y ≃* F42C) {τ : X} (hτ2 : orderOf τ = 2)
    (hτN : τ ∈ Nor Y) (hout : ¬ ∃ y ∈ Y, ∀ x ∈ Y, τ * x * τ⁻¹ = y * x * y⁻¹) :
    ∃ ψ : MulAut F42C, Y ⊓ Cen τ = (reeFixed ReeTag.F4 (ZMod 2) 0).map (embedY e ψ) := by
  have hτ2' : τ ^ 2 = 1 := by rw [← hτ2]; exact pow_orderOf_eq_one τ
  have hα2 := indAut_sq e hτN hτ2'
  have hαo := (indAut_not_inner_iff e hτN).2 hout
  have hK : Nat.card (ZMod 2) = 2 := by simp
  haveI : CharP (ZMod 2) ReeTag.F4.prime := inferInstanceAs (CharP (ZMod 2) 2)
  obtain ⟨ψ, hψ⟩ := exists_fixSub_map_eq hK hα2 hαo
  exact ⟨ψ, inf_cen_eq_map e hτN ψ _ hψ⟩

theorem clause_O2 [Finite X] (e : ↥Y ≃* F42C) :
    ∀ τ : X, orderOf τ = 2 → τ ∈ Nor Y → (¬ ∃ y ∈ Y, ∀ x ∈ Y, τ * x * τ⁻¹ = y * x * y⁻¹) →
      ∀ R : Subgroup X, R ≤ Y ⊓ Cen τ → IsPGroup 2 R → Y ⊓ Cen τ ≤ Nor R → R = ⊥ := by
  intro τ hτ2 hτN hout R hR hRp hRN
  obtain ⟨ψ, hψ⟩ := exists_inf_cen_eq e hτ2 hτN hout
  have hK : Nat.card (ZMod 2) = 2 := by simp
  haveI : CharP (ZMod 2) ReeTag.F4.prime := inferInstanceAs (CharP (ZMod 2) 2)
  set ι' := embedY e ψ with hι'
  have hinj : Function.Injective ι' := embedY_injective e ψ
  set Γ := reeFixed ReeTag.F4 (ZMod 2) 0 with hΓ
  have hRΓ : ∀ r', ι' r' ∈ R → r' ∈ Γ := by
    intro r' hr'
    have := hR hr'
    rw [hψ] at this
    obtain ⟨γ, hγ, hγr⟩ := this
    rw [← hinj hγr]
    exact hγ
  set R' : Subgroup F42C := R.comap ι' with hR'
  have hR'p : IsPGroup 2 R' := hRp.comap_of_injective ι' hinj
  set N : Subgroup ↥Γ := R'.subgroupOf Γ with hN
  have hNp : IsPGroup 2 N := hR'p.comap_of_injective Γ.subtype Subtype.val_injective
  haveI hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : ι' (n : F42C) ∈ R := hn
    have hgH : ι' (g : F42C) ∈ Y ⊓ Cen τ := by
      rw [hψ]; exact ⟨g, g.2, rfl⟩
    have := (Subgroup.mem_normalizer_iff.1 (hRN hgH)) (ι' (n : F42C))
    show ι' ((g : F42C) * (n : F42C) * (g : F42C)⁻¹) ∈ R
    rw [map_mul, map_mul, map_inv]
    exact this.1 hn'
  rcases CFSG.LieType.Simplicity.eq_bot_or_sup_eq_top_of_card_eq_two hK N with hbot | htop
  · rw [eq_bot_iff]
    intro r hr
    have hrH := hR hr
    rw [hψ] at hrH
    obtain ⟨γ, hγ, rfl⟩ := hrH
    have : (⟨γ, hγ⟩ : ↥Γ) ∈ N := hr
    rw [hbot] at this
    have h1 : γ = 1 := congrArg Subtype.val (Subgroup.mem_bot.1 this)
    rw [h1, map_one]
    exact Subgroup.one_mem _
  · exfalso
    have hq := CFSG.LieType.Simplicity.isPGroup_quotient_of_sup_eq_top hK N htop
    obtain ⟨a, ha⟩ := hNp.exists_card_eq
    obtain ⟨b, hb⟩ := hq.exists_card_eq
    have hcard : Nat.card ↥Γ = 35942400 :=
      CFSG.RankThree.PartTwo.Census.Carrier.Tits.card_reeFixed hK
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hcard, hb, ha, ← pow_add] at h2
    have h3 : 3 ∣ 2 ^ (b + a) := by rw [← h2]; norm_num
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

end Clauses

end CFSG.RankThree.PartTwo.Sec21.FF81.F4
