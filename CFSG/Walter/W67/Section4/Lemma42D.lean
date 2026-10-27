module

import CFSG.Walter.W67.Section4.Lemma42C
import CFSG.Walter.W67.Section4.Lemma42B
import CFSG.Walter.W67.Section4.Prop43cA
import CFSG.Walter.W67.Section4.Basic
import CFSG.Walter.W67.Section4.Prop43ab
import CFSG.Walter.W67.W2Cor32A
public import CFSG.Walter.JRFacts
public import CFSG.Walter.ReeOrder.JT.Section2
public import CFSG.Walter.W67.Interface

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Std

variable (s : Std G) {T₂ : G}

theorem mem_A_sup_E_of_odd
    {t : G} (ht : t ∈ s.fr.T) (ht2 : orderOf t = 2) {b : G}
    (hbH : b ∈ s.H) (hbt : b ∈ Subgroup.centralizer ({t} : Set G)) (hodd : Odd (orderOf b)) :
    b ∈ s.fr.A t ⊔ s.fr.E := by
  have hJKE : Subgroup.zpowers s.J ⊓ (s.K ⊔ s.fr.E) = ⊥ :=
    disjoint_iff.mp s.fr.isInternalDirectProduct_H.2.1
  obtain ⟨j, hj, k, hk, e, he, rfl⟩ := s.fr.exists_decomp_H hbH
  have hkeH : k * e ∈ s.H := Subgroup.mul_mem _ (s.K_le_H hk) (s.fr.E_le_H he)
  have hkeKE : k * e ∈ s.K ⊔ s.fr.E :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right he)
  have hjc : Commute j (k * e) := by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hj
    exact Commute.zpow_left (Commute.symm (Commute.symm (s.commute_J hkeH).symm)) m
  have hj1 : j = 1 := by
    have hm := pow_orderOf_eq_one (j * k * e)
    generalize orderOf (j * k * e) = m at hm hodd
    rw [mul_assoc, hjc.mul_pow] at hm
    have hjm : j ^ m ∈ Subgroup.zpowers s.J ⊓ (s.K ⊔ s.fr.E) := by
      refine ⟨Subgroup.pow_mem _ hj _, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hm]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hkeKE _)
    rw [hJKE, Subgroup.mem_bot] at hjm
    rcases eq_one_or_eq_of_mem_zpowers s.orderOf_J hj with h | h
    · exact h
    · exfalso
      rw [h] at hjm
      have h2m := orderOf_dvd_of_pow_eq_one hjm
      rw [s.orderOf_J] at h2m
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2m)
  rw [hj1, one_mul] at hbt ⊢
  have het : e * t = t * e :=
    (Subgroup.mem_centralizer_iff.mp (s.fr.E_le_CS he) t (s.fr.T_le_S ht)).symm
  have hkt : k ∈ s.K ⊓ Subgroup.centralizer ({t} : Set G) := by
    refine ⟨hk, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hbt
    calc k * t = (k * e) * t * e⁻¹ := by rw [mul_assoc k e t, het]; group
      _ = t * (k * e) * e⁻¹ := by rw [h1]
      _ = t * k := by group
  rw [s.fr.K_inf_centralizer_eq ht ht2] at hkt
  have hEA : s.fr.E ≤ Subgroup.normalizer (s.fr.A t : Set G) := fun e he =>
    JT.mem_normalizer_of_conj_mem fun x hx => s.fr.E_conj_mem_A he hx ht
  have hAEodd : Odd (Nat.card (s.fr.A t ⊔ s.fr.E : Subgroup G)) := by
    have hc' := card_sup_mul_card_inf_of_le_normalizer hEA
    exact Odd.of_dvd_nat ((s.fr.odd_card_A t).mul s.fr.odd_card_E) (Dvd.intro _ hc')
  have hTN : s.fr.T ≤ Subgroup.normalizer ((s.fr.A t ⊔ s.fr.E : Subgroup G) : Set G) := by
    intro t' ht'
    refine mem_normalizer_sup (JT.mem_normalizer_of_conj_mem fun x hx =>
      s.fr.S_conj_mem_A (s.fr.T_le_S ht') hx ht) (JT.mem_normalizer_of_conj_mem fun e he => ?_)
    rw [Subgroup.mem_centralizer_iff.mp (s.fr.E_le_CS he) t' (s.fr.T_le_S ht'),
      mul_inv_cancel_right]
    exact he
  have hmem : k * e ∈ (s.fr.A t ⊔ s.fr.E) ⊔ s.fr.T := by
    have hk' : k ∈ (s.fr.A t ⊔ s.fr.E) ⊔ s.fr.T :=
      (sup_le le_sup_right (le_sup_left.trans le_sup_left) :
        s.fr.T ⊔ s.fr.A t ≤ (s.fr.A t ⊔ s.fr.E) ⊔ s.fr.T) hkt
    exact Subgroup.mul_mem _ hk' (Subgroup.mem_sup_left (Subgroup.mem_sup_right he))
  rw [hj1, one_mul] at hodd
  exact mem_of_odd_of_mem_sup s.fr.isPGroup_T hAEodd hTN hmem hodd

theorem commutator_mem_A {t τ : G} (ht : t ∈ s.fr.T) (hτ : τ ∈ (s.fr.S : Subgroup G)) {x : G}
    (hx : x ∈ s.fr.A t ⊔ s.fr.E) : τ * x * τ⁻¹ * x⁻¹ ∈ s.fr.A t := by
  have hEA : s.fr.E ≤ Subgroup.normalizer (s.fr.A t : Set G) := fun e he =>
    JT.mem_normalizer_of_conj_mem fun x hx => s.fr.E_conj_mem_A he hx ht
  obtain ⟨a, ha, e, he, rfl⟩ := (mem_sup_iff_of_le_normalizer hEA).mp hx
  have hτe : τ * e = e * τ := Subgroup.mem_centralizer_iff.mp (s.fr.E_le_CS he) τ hτ
  have heτ : e * τ⁻¹ = τ⁻¹ * e := by
    calc e * τ⁻¹ = τ⁻¹ * (τ * e) * τ⁻¹ := by group
      _ = τ⁻¹ * (e * τ) * τ⁻¹ := by rw [hτe]
      _ = τ⁻¹ * e := by group
  have h1 : τ * (a * e) * τ⁻¹ * (a * e)⁻¹ = (τ * a * τ⁻¹) * a⁻¹ := by
    calc τ * (a * e) * τ⁻¹ * (a * e)⁻¹ = τ * a * (e * τ⁻¹) * e⁻¹ * a⁻¹ := by group
      _ = τ * a * (τ⁻¹ * e) * e⁻¹ * a⁻¹ := by rw [heτ]
      _ = (τ * a * τ⁻¹) * a⁻¹ := by group
  rw [h1]
  exact Subgroup.mul_mem _ (s.fr.S_conj_mem_A hτ ha ht) (Subgroup.inv_mem _ ha)

theorem centralizer_inf_le
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2)
    {X : Subgroup G} (hAX : s.fr.A T₂ ≤ X) (hVX : s.fr.V T₂ ≤ X)
    (hX2 : (Nat.card X).factorization 2 = 2) {v₀ : G} (hv₀ : v₀ ∈ s.fr.V T₂) (hv₀1 : v₀ ≠ 1) :
    Subgroup.centralizer ({v₀} : Set G) ⊓ X ≤ Subgroup.centralizer (s.fr.V T₂ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVS := s.fr.V_le_S hT₂
  obtain ⟨c, hc, hcv⟩ := s.fr.exists_conj_of_cover s.hidx (hVS hv₀) hv₀1
  have hcS : c ∈ Subgroup.normalizer ((s.fr.S : Subgroup G) : Set G) := hc.1
  set φ := (MulAut.conj c).toMonoidHom with hφ
  have hφapp : ∀ x, φ x = c * x * c⁻¹ := fun x => rfl
  have hφinj : Function.Injective φ := (MulAut.conj c).injective
  set Y := (Subgroup.centralizer ({v₀} : Set G) ⊓ X).map φ with hY
  set V' := (s.fr.V T₂).map φ with hV'
  set B := (s.fr.A T₂).map φ with hB
  have hV'card : Nat.card V' = 4 := by
    rw [Subgroup.card_map_of_injective hφinj, s.fr.card_V hT₂ h2]
  have hVA := s.A_le_centralizer_V T₂
  have hVC : s.fr.V T₂ ≤ Subgroup.centralizer ({v₀} : Set G) := fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.mpr (s.fr.comm_of_mem_S (hVS hv) (hVS hv₀))
  have hAC : s.fr.A T₂ ≤ Subgroup.centralizer ({v₀} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hVA ha) v₀ hv₀).symm
  have hYH : Y ≤ s.H := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hφapp, ← hcv]
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hx.1
    calc c * x * c⁻¹ * (c * v₀ * c⁻¹) = c * (x * v₀) * c⁻¹ := by group
      _ = c * (v₀ * x) * c⁻¹ := by rw [h1]
      _ = c * v₀ * c⁻¹ * (c * x * c⁻¹) := by group
  have hV'S : V' ≤ (s.fr.S : Subgroup G) := by
    rintro _ ⟨v, hv, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hcS v).mp (hVS hv)
  have hJV' : s.J ∈ V' := ⟨v₀, hv₀, hcv⟩
  have hV'Y : V' ≤ Y := Subgroup.map_mono (le_inf hVC hVX)
  have hBY : B ≤ Y := Subgroup.map_mono (le_inf hAC hAX)
  have hBne : B ≠ ⊥ := by
    rw [hB, Ne, Subgroup.map_eq_bot_iff_of_injective _ hφinj]
    exact s.A_ne_bot hp hT₂ h2
  obtain ⟨t', ht'V, ht'T, ht'1⟩ : ∃ t' ∈ V', t' ∈ s.fr.T ∧ t' ≠ 1 := by
    obtain ⟨hc', -⟩ := card_sup_mul_card_inf_of_commute V' s.fr.T
      (fun x hx y hy => s.fr.comm_of_mem_S (hV'S hx) (s.fr.T_le_S hy))
    have hle : Nat.card (V' ⊔ s.fr.T : Subgroup G) ≤ 8 := by
      rw [← s.fr.card_S]
      exact Subgroup.card_le_of_le (sup_le hV'S s.fr.T_le_S)
    rw [hV'card, s.fr.card_T] at hc'
    have h1 : 1 < Nat.card (V' ⊓ s.fr.T : Subgroup G) := by
      by_contra hle1
      push Not at hle1
      have : Nat.card (V' ⊔ s.fr.T : Subgroup G) * Nat.card (V' ⊓ s.fr.T : Subgroup G) ≤ 8 :=
        calc _ ≤ 8 * 1 := Nat.mul_le_mul hle hle1
          _ = 8 := by norm_num
      omega
    have : Nontrivial (V' ⊓ s.fr.T : Subgroup G) := Finite.one_lt_card_iff_nontrivial.mp h1
    obtain ⟨⟨t', ht'⟩, ht'1⟩ := exists_ne (1 : (V' ⊓ s.fr.T : Subgroup G))
    exact ⟨t', ht'.1, ht'.2, fun h => ht'1 (Subtype.ext h)⟩
  have ht'2 : orderOf t' = 2 := orderOf_eq_prime
    (by rw [pow_two]; exact s.fr.mul_self_of_mem_S (s.fr.T_le_S ht'T)) ht'1
  have hVt' : s.fr.V t' = V' := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Frame.V, Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact hJV'
      · exact ht'V
    · rw [hV'card, s.fr.card_V ht'T ht'2]
  obtain ⟨v₁, hv₁, hv₁t⟩ := ht'V
  have hBprop : ∀ b ∈ B, b ∈ s.H ∧ b ∈ Subgroup.centralizer ({t'} : Set G) ∧
      Odd (orderOf b) := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨hYH (hBY ⟨a, ha, rfl⟩), ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff, ← hv₁t, hφapp, hφapp]
      have h1 := Subgroup.mem_centralizer_iff.mp (hVA ha) v₁ hv₁
      calc c * a * c⁻¹ * (c * v₁ * c⁻¹) = c * (a * v₁) * c⁻¹ := by group
        _ = c * (v₁ * a) * c⁻¹ := by rw [h1]
        _ = c * v₁ * c⁻¹ * (c * a * c⁻¹) := by group
    · rw [hφapp, orderOf_conj_mul]
      exact odd_orderOf_of_mem_oddPart ha
  have hBA' : B ≤ s.fr.A t' := by
    obtain ⟨τ, hτS, hτV⟩ := s.exists_mem_S_not_mem_V hT₂ h2
    set τ' := c * τ * c⁻¹ with hτ'
    have hτ'S : τ' ∈ (s.fr.S : Subgroup G) := (Subgroup.mem_normalizer_iff.mp hcS τ).mp hτS
    have hτ'inv : ∀ b ∈ B, τ' * b * τ'⁻¹ = b⁻¹ := by
      rintro _ ⟨a, ha, rfl⟩
      have h1 := s.fr.S_inv_A hT₂ h2 hτS hτV ha
      rw [hφapp, hτ']
      calc c * τ * c⁻¹ * (c * a * c⁻¹) * (c * τ * c⁻¹)⁻¹ = c * (τ * a * τ⁻¹) * c⁻¹ := by group
        _ = c * a⁻¹ * c⁻¹ := by rw [h1]
        _ = (c * a * c⁻¹)⁻¹ := by group
    intro b hb
    obtain ⟨hbH, -, hbodd⟩ := hBprop b hb
    obtain ⟨m, hm⟩ := hbodd
    set b₁ := b ^ (m + 1) with hb₁
    have hb₁B : b₁ ∈ B := Subgroup.pow_mem _ hb _
    have hb₁b : b₁ * b₁ = b := by
      rw [hb₁, ← pow_two, ← pow_mul, show (m + 1) * 2 = 2 * m + 1 + 1 by ring, pow_succ, ← hm,
        pow_orderOf_eq_one, one_mul]
    have hc1 : τ' * b₁⁻¹ * τ'⁻¹ * b₁⁻¹⁻¹ = b := by
      have : τ' * b₁⁻¹ * τ'⁻¹ = b₁ := by
        rw [show τ' * b₁⁻¹ * τ'⁻¹ = (τ' * b₁ * τ'⁻¹)⁻¹ by group, hτ'inv b₁ hb₁B, inv_inv]
      rw [this, inv_inv, hb₁b]
    obtain ⟨hH1, hC1, hO1⟩ := hBprop b₁⁻¹ (Subgroup.inv_mem _ hb₁B)
    rw [← hc1]
    exact s.commutator_mem_A ht'T hτ'S (s.mem_A_sup_E_of_odd ht'T ht'2 hH1 hC1 hO1)
  have hY2 : (Nat.card Y).factorization 2 = 2 := by
    rw [Subgroup.card_map_of_injective hφinj]
    exact factorization_two_of_le (le_inf hVC hVX) inf_le_right (s.fr.card_V hT₂ h2) hX2
  have hYC := s.le_centralizer_of_le_H hp ht'T ht'2 hYH (hV'Y hJV')
    (hV'Y ⟨v₁, hv₁, hv₁t⟩) hY2 hBY hBA' hBne
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hφx : φ x ∈ Y := ⟨x, hx, rfl⟩
  have hφv : φ v ∈ V' := ⟨v, hv, rfl⟩
  have hY' : φ x ∈ Subgroup.centralizer (s.fr.V t' : Set G) := by
    rw [s.fr.centralizer_V]
    exact ⟨hYH hφx, hYC hφx⟩
  rw [hVt'] at hY'
  have h1 := Subgroup.mem_centralizer_iff.mp hY' (φ v) hφv
  rw [hφapp, hφapp] at h1
  have h2' := congrArg (fun z => c⁻¹ * z * c) h1
  simp only [mul_assoc, inv_mul_cancel_left] at h2'
  simpa [mul_assoc] using h2'

theorem oddPart_le_centralizer
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2)
    {X : Subgroup G} (hAX : s.fr.A T₂ ≤ X) (hVX : s.fr.V T₂ ≤ X)
    (hX2 : (Nat.card X).factorization 2 = 2) :
    ∀ o ∈ CFSG.pPrimeCore 2 X, (o : G) ∈ Subgroup.centralizer (s.fr.V T₂ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Vx := (s.fr.V T₂).subgroupOf X with hVx
  have eV : Vx ≃* s.fr.V T₂ := Subgroup.subgroupOfEquivOfLe hVX
  have hVK := s.fr.isKleinFour_V hT₂ h2
  have hVxK : IsKleinFour Vx :=
    ⟨by rw [Nat.card_congr eV.toEquiv, hVK.card_four],
      (Monoid.exponent_eq_of_mulEquiv eV).trans hVK.exponent_two⟩
  have hO : Odd (Nat.card (CFSG.pPrimeCore 2 X)) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))
  have hON : (CFSG.pPrimeCore 2 X).Normal := CFSG.pPrimeCore_normal (p := 2) (G := X)
  have hC : ∀ a ∈ Vx, a ≠ 1 → Subgroup.centralizer ({a} : Set X) ≤
      Subgroup.centralizer (Vx : Set X) := by
    intro a ha ha1 y hy
    have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have hyG : (y : G) ∈ Subgroup.centralizer ({(a : G)} : Set G) ⊓ X :=
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)), y.2⟩
    have h1 := s.centralizer_inf_le hp hT₂ h2 hAX hVX hX2 ha ha1' hyG
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp h1 v hv)
  have hle := le_centralizer_of_isKleinFour' hVxK hO hC
  intro o ho
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 := Subgroup.mem_centralizer_iff.mp (hle (show (⟨v, hVX hv⟩ : X) ∈ Vx from hv)) o ho
  exact (congrArg Subtype.val h1).symm

end Std

end CFSG.Walter.W67
