module

public import CFSG.RankThree.GF2n.Stroth80.Sec86IrredCentral
public import CFSG.RankThree.GF2n.Stroth80.Sec86SpOrder

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75
open scoped commutatorElement

theorem card_sup_mul_card_inf_of_conj_mem {G : Type} [Group G] [Finite G] (A B : Subgroup G)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have hAN : A ≤ Subgroup.normalizer (B : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hAB a ha h hh, fun hh => ?_⟩
    simpa [mul_assoc] using hAB a⁻¹ (A.inv_mem ha) _ hh
  have hrel : B.relIndex A = B.relIndex (A ⊔ B) := by
    letI := Subgroup.normal_subgroupOf_of_le_normalizer hAN
    letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAN
    exact Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient A B hAN).toEquiv
  have hC : B.relIndex (A ⊔ B) * Nat.card ↥B = Nat.card ↥(A ⊔ B) := by
    have h := Subgroup.relIndex_mul_card (H := B) (K := A ⊔ B)
    rwa [inf_of_le_left (le_sup_right : B ≤ A ⊔ B)] at h
  have hA : B.relIndex A * Nat.card ↥(B ⊓ A) = Nat.card ↥A :=
    Subgroup.relIndex_mul_card (H := B) (K := A)
  rw [inf_comm]
  rw [← hrel] at hC
  rw [← hC, ← hA]
  exact Nat.mul_right_comm _ _ _

theorem eq_sup_of_irred {G : Type} [Group G] [Finite G] {R N Z0 K : Subgroup G}
    (hirr : IsIrredModule R N Z0) (hNR : N ≤ R) (hR : R = K ⊔ N)
    (hKn : ∀ r ∈ R, conjSubgroup r K = K) (hNn : ∀ r ∈ R, conjSubgroup r N = N)
    (hZn : ∀ r ∈ R, conjSubgroup r Z0 = Z0)
    (hnc : ¬ ∀ r ∈ R, ∀ n ∈ N, ⁅n, r⁆ ∈ Z0) : N = (K ⊓ N) ⊔ Z0 := by
  have hKR : K ≤ R := hR ▸ le_sup_left
  obtain ⟨hcomm, -, hlt, hmin⟩ := hirr
  have hZN : Z0 ≤ N := hlt.le
  have hAN : (K ⊓ N) ⊔ Z0 ≤ N := sup_le inf_le_right hZN
  have hinv : ∀ r ∈ R, conjSubgroup r ((K ⊓ N) ⊔ Z0) = (K ⊓ N) ⊔ Z0 := by
    intro r hr
    have hK' : Subgroup.map (MulAut.conj r).toMonoidHom K = K := hKn r hr
    have hN' : Subgroup.map (MulAut.conj r).toMonoidHom N = N := hNn r hr
    have hZ' : Subgroup.map (MulAut.conj r).toMonoidHom Z0 = Z0 := hZn r hr
    unfold conjSubgroup
    rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ (MulAut.conj r).injective, hK', hN', hZ']
  rcases hmin ((K ⊓ N) ⊔ Z0) le_sup_right hAN hinv with hA | hA
  · exfalso
    apply hnc
    let C : Subgroup G :=
      { carrier := {r | r ∈ R ∧ ∀ n ∈ N, ⁅n, r⁆ ∈ Z0}
        mul_mem' := by
          rintro a b ⟨haR, ha⟩ ⟨hbR, hb⟩
          refine ⟨R.mul_mem haR hbR, fun n hn => ?_⟩
          have e : ⁅n, a * b⁆ = ⁅n, a⁆ * (a * ⁅n, b⁆ * a⁻¹) := by
            simp only [commutatorElement_def]; group
          rw [e]
          refine Z0.mul_mem (ha n hn) ?_
          have h1 : a * ⁅n, b⁆ * a⁻¹ ∈ conjSubgroup a Z0 := by
            rw [mem_conjSubgroup]
            have e2 : a⁻¹ * (a * ⁅n, b⁆ * a⁻¹) * a = ⁅n, b⁆ := by group
            rw [e2]
            exact hb n hn
          rwa [hZn a haR] at h1
        one_mem' := ⟨R.one_mem, fun n _ => by simpa [commutatorElement_def] using Z0.one_mem⟩
        inv_mem' := by
          rintro a ⟨haR, ha⟩
          refine ⟨R.inv_mem haR, fun n hn => ?_⟩
          have e : ⁅n, a⁻¹⁆ = a⁻¹ * (⁅n, a⁆)⁻¹ * a := by
            simp only [commutatorElement_def]; group
          rw [e]
          have h1 : a⁻¹ * (⁅n, a⁆)⁻¹ * a ∈ conjSubgroup a⁻¹ Z0 := by
            rw [mem_conjSubgroup]
            have e2 : a⁻¹⁻¹ * (a⁻¹ * (⁅n, a⁆)⁻¹ * a) * a⁻¹ = (⁅n, a⁆)⁻¹ := by group
            rw [e2]
            exact Z0.inv_mem (ha n hn)
          rwa [hZn a⁻¹ (R.inv_mem haR)] at h1 }
    have hKC : K ≤ C := by
      intro k hk
      refine ⟨hKR hk, fun n hn => ?_⟩
      have hnR : n ∈ R := hNR hn
      have h1 : n * k * n⁻¹ ∈ K := by
        have : n * k * n⁻¹ ∈ conjSubgroup n K := by
          rw [mem_conjSubgroup]
          have e : n⁻¹ * (n * k * n⁻¹) * n = k := by group
          rw [e]; exact hk
        rwa [hKn n hnR] at this
      have h2 : k * n⁻¹ * k⁻¹ ∈ N := by
        have : k * n⁻¹ * k⁻¹ ∈ conjSubgroup k N := by
          rw [mem_conjSubgroup]
          have e : k⁻¹ * (k * n⁻¹ * k⁻¹) * k = n⁻¹ := by group
          rw [e]; exact N.inv_mem hn
        rwa [hNn k (hKR hk)] at this
      have hmemK : ⁅n, k⁆ ∈ K := by
        have e : ⁅n, k⁆ = (n * k * n⁻¹) * k⁻¹ := by simp only [commutatorElement_def]
        rw [e]; exact K.mul_mem h1 (K.inv_mem hk)
      have hmemN : ⁅n, k⁆ ∈ N := by
        have e : ⁅n, k⁆ = n * (k * n⁻¹ * k⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]; exact N.mul_mem hn h2
      have : ⁅n, k⁆ ∈ (K ⊓ N) ⊔ Z0 := Subgroup.mem_sup_left ⟨hmemK, hmemN⟩
      rwa [hA] at this
    have hNC : N ≤ C := fun n' hn' => ⟨hNR hn', fun n hn => hcomm n hn n' hn'⟩
    have hRC : R ≤ C := hR ▸ sup_le hKC hNC
    exact fun r hr n hn => (hRC hr).2 n hn
  · exact hA.symm

theorem conjSubgroup_eq_of_conj_mem {G : Type} [Group G] [Finite G] {T : Subgroup G} {r : G}
    (h : ∀ k ∈ T, r * k * r⁻¹ ∈ T) : conjSubgroup r T = T := by
  have hle : conjSubgroup r T ≤ T := by
    intro x hx
    rw [mem_conjSubgroup] at hx
    have := h _ hx
    simpa [mul_assoc] using this
  exact Subgroup.eq_of_le_of_card_ge hle
    (CFSG.RankThree.GF2n.card_conjSubgroup r T).ge

theorem step86_core {G : Type} [Group G] [Finite G] {R N Z0 Q K : Subgroup G}
    {f m e kk o₁ o₂ : ℕ}
    (hQZ0 : Q ≤ Z0) (hZ0N : Z0 ≤ N) (hNR : N ≤ R) (hQK : Q ≤ K) (hR : R = K ⊔ N)
    (hKn : ∀ r ∈ R, conjSubgroup r K = K) (hNn : ∀ r ∈ R, conjSubgroup r N = N)
    (hZn : ∀ r ∈ R, conjSubgroup r Z0 = Z0) (hirr : IsIrredModule R N Z0)
    (hN2 : IsPGroup 2 ↥N) (hf : 2 ≤ f) (he : 1 ≤ e) (hQcard : Nat.card ↥Q = 2 ^ kk)
    (hNcard : Nat.card ↥N = Nat.card ↥Q * (2 ^ f) ^ (e + 1))
    (hZ0card : Nat.card ↥Z0 = Nat.card ↥Q * 2 ^ f)
    (hRcard : Nat.card ↥R = Nat.card ↥N * ((2 ^ f) ^ (m ^ 2) * o₁)) (ho₁ : Odd o₁)
    (hKdvd : Nat.card ↥K ∣ Nat.card ↥Q * ((2 ^ f) ^ 15 * o₂)) (ho₂ : Odd o₂)
    (hme : 15 < m ^ 2 + e) : False := by
  have hKR : K ≤ R := hR ▸ le_sup_left
  have hmem : ∀ (T : Subgroup G) (r : G), conjSubgroup r T = T → ∀ b ∈ T, r * b * r⁻¹ ∈ T := by
    intro T r h b hb
    have h1 : r * b * r⁻¹ ∈ conjSubgroup r T := by
      rw [mem_conjSubgroup]
      have e : r⁻¹ * (r * b * r⁻¹) * r = b := by group
      rw [e]
      exact hb
    rwa [h] at h1
  have hqge : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hQpos : 0 < Nat.card ↥Q := Nat.card_pos
  have hNpos : 0 < Nat.card ↥N := Nat.card_pos
  have hbig : 2 * Nat.card ↥Z0 < Nat.card ↥N := by
    rw [hZ0card, hNcard]
    have h1 : 2 * 2 ^ f < (2 ^ f) ^ (e + 1) := by
      calc 2 * 2 ^ f < 4 * 2 ^ f := by omega
        _ ≤ 2 ^ f * 2 ^ f := Nat.mul_le_mul_right _ hqge
        _ = (2 ^ f) ^ 2 := by ring
        _ ≤ (2 ^ f) ^ (e + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    calc 2 * (Nat.card ↥Q * 2 ^ f) = Nat.card ↥Q * (2 * 2 ^ f) := by ring
      _ < Nat.card ↥Q * (2 ^ f) ^ (e + 1) := Nat.mul_lt_mul_of_pos_left h1 hQpos
  have hnc := not_central_of_irred hirr hNR hZn hbig
  have hgen := eq_sup_of_irred hirr hNR hR hKn hNn hZn hnc
  have hKN : ∀ a ∈ K, ∀ b ∈ N, a * b * a⁻¹ ∈ N := fun a ha b hb => hmem N a (hNn a (hKR ha)) b hb
  have hprod := card_sup_mul_card_inf_of_conj_mem K N hKN
  rw [← hR] at hprod
  have hKeq : (2 ^ f) ^ (m ^ 2) * o₁ * Nat.card ↥(K ⊓ N) = Nat.card ↥K := by
    rw [hRcard] at hprod
    have h1 : Nat.card ↥N * ((2 ^ f) ^ (m ^ 2) * o₁ * Nat.card ↥(K ⊓ N)) =
        Nat.card ↥N * Nat.card ↥K := by
      calc Nat.card ↥N * ((2 ^ f) ^ (m ^ 2) * o₁ * Nat.card ↥(K ⊓ N))
          = Nat.card ↥N * ((2 ^ f) ^ (m ^ 2) * o₁) * Nat.card ↥(K ⊓ N) := by ring
        _ = Nat.card ↥K * Nat.card ↥N := hprod
        _ = Nat.card ↥N * Nat.card ↥K := by ring
    exact Nat.eq_of_mul_eq_mul_left hNpos h1
  obtain ⟨j, hj⟩ : ∃ j, Nat.card ↥(K ⊓ N) = 2 ^ j := (hN2.to_inf_right (H := K)).exists_card_eq
  have hlow : Nat.card ↥Q * (2 ^ f) ^ e ≤ Nat.card ↥(K ⊓ N) := by
    have hQKN : Q ≤ K ⊓ N := le_inf hQK (hQZ0.trans hZ0N)
    have hnormZ : ∀ a ∈ K ⊓ N, ∀ b ∈ Z0, a * b * a⁻¹ ∈ Z0 := fun a ha b hb =>
      hmem Z0 a (hZn a (hNR ha.2)) b hb
    have h1 := card_sup_mul_card_le_of_normalizes (K ⊓ N) Z0 Q hQKN hQZ0 hnormZ
    rw [← hgen, hNcard, hZ0card] at h1
    have h2 : (2 ^ f) ^ (e + 1) = (2 ^ f) ^ e * 2 ^ f := pow_succ _ _
    rw [h2] at h1
    have hpos : 0 < Nat.card ↥Q * 2 ^ f := Nat.mul_pos hQpos (by positivity)
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc Nat.card ↥Q * (2 ^ f) ^ e * (Nat.card ↥Q * 2 ^ f)
        = Nat.card ↥Q * ((2 ^ f) ^ e * 2 ^ f) * Nat.card ↥Q := by ring
      _ ≤ Nat.card ↥(K ⊓ N) * (Nat.card ↥Q * 2 ^ f) := h1
  have hpowm : (2 ^ f) ^ (m ^ 2) = 2 ^ (f * m ^ 2) := (pow_mul 2 f (m ^ 2)).symm
  have hpow15 : (2 ^ f) ^ 15 = 2 ^ (f * 15) := (pow_mul 2 f 15).symm
  have h2adic : 2 ^ (f * m ^ 2 + j) * o₁ = Nat.card ↥K * 2 ^ 0 := by
    rw [hj, hpowm] at hKeq
    calc 2 ^ (f * m ^ 2 + j) * o₁ = 2 ^ (f * m ^ 2) * o₁ * 2 ^ j := by ring
      _ = Nat.card ↥K := hKeq
      _ = Nat.card ↥K * 2 ^ 0 := by ring
  have hX : Nat.card ↥K ∣ 2 ^ (kk + f * 15) * o₂ := by
    have h1 : Nat.card ↥Q * ((2 ^ f) ^ 15 * o₂) = 2 ^ (kk + f * 15) * o₂ := by
      rw [hQcard, hpow15, pow_add]
      ring
    rwa [h1] at hKdvd
  have hineq := two_adic_ineq ho₁ ho₂ h2adic hX
  have hj2 : kk + f * e ≤ j := by
    have h3 : 2 ^ (kk + f * e) ≤ 2 ^ j := by
      calc 2 ^ (kk + f * e) = 2 ^ kk * (2 ^ f) ^ e := by rw [pow_add, pow_mul]
        _ = Nat.card ↥Q * (2 ^ f) ^ e := by rw [hQcard]
        _ ≤ 2 ^ j := hj ▸ hlow
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h3
  have h4 : f * (m ^ 2 + e) ≤ f * 15 := by nlinarith
  have h5 : m ^ 2 + e ≤ 15 := Nat.le_of_mul_le_mul_left h4 (by omega)
  omega

end CFSG.RankThree.GF2n.Stroth80
