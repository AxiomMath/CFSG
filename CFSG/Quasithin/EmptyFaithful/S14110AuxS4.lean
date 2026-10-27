module

public import CFSG.Quasithin.EmptyFaithful.S14110AuxA4

public section

namespace CFSG.Quasithin.S14110

open Subgroup

section SylowThree

private theorem card_sylow_three_of_card_twelve {K : Type*} [Group K] [Finite K]
    (hK : Nat.card K = 12) (P : Sylow 3 K) : Nat.card P = 3 := by
  rw [P.card_eq_multiplicity, hK]
  have h : Nat.factorization 12 3 = 1 := by norm_num [Nat.factorization]
  rw [h]
  norm_num

private theorem card_sylow_three_eq_one_or_four {K : Type*} [Group K] [Finite K]
    (hK : Nat.card K = 12) : Nat.card (Sylow 3 K) = 1 ∨ Nat.card (Sylow 3 K) = 4 := by
  obtain ⟨P⟩ : Nonempty (Sylow 3 K) := inferInstance
  have hidx : (P : Subgroup K).index = 4 := by
    have h := (P : Subgroup K).card_mul_index
    rw [card_sylow_three_of_card_twelve hK P, hK] at h
    omega
  have hdvd := P.card_dvd_index
  have hmod := card_sylow_modEq_one 3 K
  rw [hidx] at hdvd
  have hle : Nat.card (Sylow 3 K) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  unfold Nat.ModEq at hmod
  generalize Nat.card (Sylow 3 K) = n at *
  interval_cases n <;> omega

private theorem eq_one_of_forall_mem_normalizer_sylow_three {K : Type*} [Group K] [Finite K]
    (hK : Nat.card K = 12) (hn : Nat.card (Sylow 3 K) = 4) {y : K}
    (hy : ∀ P : Sylow 3 K, y ∈ normalizer (P : Set K)) : y = 1 := by
  have hP3 : ∀ P : Sylow 3 K, Nat.card P = 3 := card_sylow_three_of_card_twelve hK
  have hmem : ∀ P : Sylow 3 K, y ∈ (P : Subgroup K) := by
    intro P
    have hN : Nat.card (normalizer (P : Set K)) = 3 := by
      have h1 := (normalizer (P : Set K)).card_mul_index
      rw [← P.card_eq_index_normalizer, hn, hK] at h1
      omega
    have hle : (P : Subgroup K) ≤ normalizer (P : Set K) := le_normalizer
    have heq : (P : Subgroup K) = normalizer (P : Set K) :=
      eq_of_le_of_card_ge hle (by rw [hN, hP3 P])
    rw [heq]
    exact hy P
  obtain ⟨P, Q, hPQ⟩ : ∃ P Q : Sylow 3 K, P ≠ Q := by
    have h1 : 1 < Nat.card (Sylow 3 K) := by rw [hn]; norm_num
    have : Nontrivial (Sylow 3 K) := (Finite.one_lt_card_iff_nontrivial).1 h1
    exact exists_pair_ne _
  have hinf : (P : Subgroup K) ⊓ Q = ⊥ := by
    have hd : Nat.card ↥((P : Subgroup K) ⊓ Q) ∣ 3 := by
      have h1 := card_dvd_of_le (inf_le_left : (P : Subgroup K) ⊓ Q ≤ P)
      rwa [hP3 P] at h1
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h3
    · exact eq_bot_of_card_eq _ h1
    · exfalso
      apply hPQ
      have e1 : (P : Subgroup K) ⊓ Q = P :=
        eq_of_le_of_card_ge inf_le_left (by rw [h3, hP3 P])
      have e2 : (P : Subgroup K) ⊓ Q = Q :=
        eq_of_le_of_card_ge inf_le_right (by rw [h3, hP3 Q])
      exact Sylow.ext (e1.symm.trans e2)
  have hyPQ : y ∈ (P : Subgroup K) ⊓ Q := ⟨hmem P, hmem Q⟩
  rw [hinf] at hyPQ
  exact mem_bot.1 hyPQ

theorem A4Data.card_sylow_three_eq_four {G : Type*} [Group G] {X W : Subgroup G} {c : G}
    (h : A4Data X W c) : Nat.card (Sylow 3 ↥X) = 4 := by
  have hfin : Finite X := Nat.finite_of_card_ne_zero (by rw [h.card_X]; norm_num)
  rcases card_sylow_three_eq_one_or_four h.card_X with h1 | h4
  · exfalso
    have hsub : Subsingleton (Sylow 3 ↥X) := (Nat.card_eq_one_iff_unique.1 h1).1
    let cX : ↥X := ⟨c, h.mem_X⟩
    have hcP : IsPGroup 3 (zpowers cX) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, h.order_c, pow_one]
    obtain ⟨P, hcP'⟩ := hcP.exists_le_sylow
    have hcmem : cX ∈ (P : Subgroup ↥X) := hcP' (mem_zpowers cX)
    have hPn : (P : Subgroup ↥X).Normal := Sylow.normal_of_subsingleton P
    have hP3 : Nat.card P = 3 := card_sylow_three_of_card_twelve h.card_X P
    obtain ⟨w, hw, hw1⟩ := h.exists_ne_one_mem_W
    let wX : ↥X := ⟨w, h.le hw⟩
    have hy : cX * (wX * cX * wX⁻¹)⁻¹ ∈ (P : Subgroup ↥X) :=
      mul_mem hcmem (inv_mem (hPn.conj_mem cX hcmem wX))
    have hy3 : (cX * (wX * cX * wX⁻¹)⁻¹) ^ 3 = 1 := by
      have h1 : (⟨_, hy⟩ : (P : Subgroup ↥X)) ^ Nat.card (P : Subgroup ↥X) = 1 :=
        pow_card_eq_one'
      rw [hP3] at h1
      exact congrArg Subtype.val h1
    have hyG : (c * w * c⁻¹ * w⁻¹) ^ 3 = 1 := by
      have h2 := congrArg Subtype.val hy3
      simpa [cX, wX, mul_assoc] using h2
    have hyW : c * w * c⁻¹ * w⁻¹ ∈ W := mul_mem (h.conj_mem hw) (inv_mem hw)
    have hy2 : (c * w * c⁻¹ * w⁻¹) ^ 2 = 1 := h.sq_eq_one _ hyW
    have hy1 : c * w * c⁻¹ * w⁻¹ = 1 := by
      calc c * w * c⁻¹ * w⁻¹ = (c * w * c⁻¹ * w⁻¹) ^ 3 * ((c * w * c⁻¹ * w⁻¹) ^ 2)⁻¹ := by group
        _ = 1 := by rw [hyG, hy2]; simp
    exact h.fpf w hw hw1 (mul_inv_eq_one.1 hy1)
  · exact h4

end SylowThree

section Action

private noncomputable def sylowThreePerm {G : Type*} [Group G] (X H : Subgroup G)
    (hHn : H ≤ normalizer (X : Set G)) : ↥H →* Equiv.Perm (Sylow 3 ↥X) :=
  (MulAction.toPermHom (MulAut ↥X) (Sylow 3 ↥X)).comp
    ((normalizerMonoidHom X).comp (Subgroup.inclusion hHn))

private theorem sylowThreePerm_injective {G : Type*} [Group G] {X H : Subgroup G} [Finite ↥X]
    (hXH : X ≤ H) (hHn : H ≤ normalizer (X : Set G)) (hX12 : Nat.card X = 12)
    (hn : Nat.card (Sylow 3 ↥X) = 4) (hC : ∀ h ∈ H, (∀ x ∈ X, h * x = x * h) → h = 1) :
    Function.Injective (sylowThreePerm X H hHn) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  have hkc : ∀ x ∈ X, (k : G) * x = x * (k : G) := by
    intro x hx
    let x' : ↥H := ⟨x, hXH hx⟩
    let z : ↥H := k * x' * k⁻¹ * x'⁻¹
    have hzK : sylowThreePerm X H hHn z = 1 := by
      simp [z, hk]
    have hzX : (z : G) ∈ X := by
      have h1 : (k : G) * x * (k : G)⁻¹ ∈ X := (mem_normalizer_iff.1 (hHn k.2) x).1 hx
      exact mul_mem h1 (inv_mem hx)
    let y : ↥X := ⟨(z : G), hzX⟩
    have hyP : ∀ P : Sylow 3 ↥X, y ∈ normalizer (P : Set ↥X) := by
      intro P
      have e : normalizerMonoidHom X ⟨(z : G), hHn z.2⟩ = MulAut.conj y :=
        MulEquiv.ext fun x => Subtype.ext rfl
      have h1 : (normalizerMonoidHom X ⟨(z : G), hHn z.2⟩) • P = P :=
        DFunLike.congr_fun hzK P
      rw [e] at h1
      exact Sylow.smul_eq_iff_mem_normalizer.1 h1
    have hy1 : y = 1 := eq_one_of_forall_mem_normalizer_sylow_three hX12 hn hyP
    have hz1 : (k : G) * x * (k : G)⁻¹ * x⁻¹ = 1 := congrArg Subtype.val hy1
    have h2 : (k : G) * x * (k : G)⁻¹ = x := mul_inv_eq_one.1 hz1
    calc (k : G) * x = (k : G) * x * (k : G)⁻¹ * k := by group
      _ = x * k := by rw [h2]
  exact Subtype.ext (hC k k.2 hkc)

end Action

theorem nonempty_mulEquiv_perm_four {G : Type*} [Group G] [Finite G] {X W : Subgroup G} {c : G}
    (hX : A4Data X W c) {H : Subgroup G} (hXH : X ≤ H)
    (hnorm : ∀ h ∈ H, h ∈ normalizer (X : Set G))
    (hC : ∀ h ∈ H, (∀ x ∈ X, h * x = x * h) → h = 1)
    (hne : ∃ h ∈ H, h ∉ X) : Nonempty (H ≃* Equiv.Perm (Fin 4)) := by
  have hn : Nat.card (Sylow 3 ↥X) = 4 := hX.card_sylow_three_eq_four
  have hinj := sylowThreePerm_injective hXH hnorm hX.card_X hn hC
  have hperm : Nat.card (Equiv.Perm (Sylow 3 ↥X)) = 24 := by
    rw [Nat.card_perm, hn]
    rfl
  have hdvd : 12 ∣ Nat.card H := hX.card_X ▸ card_dvd_of_le hXH
  have hne12 : Nat.card H ≠ 12 := by
    intro h12
    obtain ⟨g, hgH, hgX⟩ := hne
    refine hgX ?_
    have hXH' : X = H := eq_of_le_of_card_ge hXH (by rw [h12, hX.card_X])
    exact hXH' ▸ hgH
  have hle : Nat.card H ≤ 24 := by
    have h1 := Nat.card_le_card_of_injective _ hinj
    rwa [hperm] at h1
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hH24 : Nat.card H = 24 := by omega
  have hbij : Function.Bijective (sylowThreePerm X H hnorm) :=
    hinj.bijective_of_nat_card_le (by rw [hH24, hperm])
  exact ⟨(MulEquiv.ofBijective _ hbij).trans (Finite.equivFinOfCardEq hn).permCongrHom⟩

end CFSG.Quasithin.S14110
