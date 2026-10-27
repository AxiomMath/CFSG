module

public import CFSG.GH74.Uniqueness.Section162Suzuki
public import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.Quasithin.F112Crit.APrime

open CFSG.GH74.Uniqueness.Bender

theorem suzuki_exists_closure_three_involutions
    {K : Type} [Group K] [Finite K] {n : ℕ} (h : BenderType K n 2 1) :
    ∃ s₁ s₂ s₃ : K, s₁ * s₁ = 1 ∧ s₁ ≠ 1 ∧ s₂ * s₂ = 1 ∧ s₂ ≠ 1 ∧ s₃ * s₃ = 1 ∧ s₃ ≠ 1 ∧
      Subgroup.closure ({s₁, s₂, s₃} : Set K) = ⊤ := by
  classical
  obtain ⟨Q⟩ := Sylow.nonempty (p := 2) (G := K)
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  obtain ⟨d₀, hd₀⟩ :=
    (Subgroup.isCyclic_iff_exists_zpowers_eq_top (cartan (Q : Subgroup K) t)).mp hc.isCyclic
  have hd₀D : d₀ ∈ cartan (Q : Subgroup K) t := by
    rw [← hd₀]
    exact Subgroup.mem_zpowers d₀
  have hd₀inv : t * d₀ * t = d₀⁻¹ := by
    have hmem : d₀ ∈ ⁅cartan (Q : Subgroup K) t, Subgroup.zpowers t⁆ := by
      rw [← hc.cartan_eq_commutator rfl]
      exact hd₀D
    exact (hc.mem_commutator_cartan_iff.mp hmem).2
  set s₃ : K := t * d₀ with hs₃
  have hs₃sq : s₃ * s₃ = 1 := by
    have h1 : s₃ * s₃ = (t * d₀ * t) * d₀ := by
      simp only [hs₃]
      group
    rw [h1, hd₀inv, inv_mul_cancel]
  have ht1 : t ≠ 1 := by
    intro h1
    exact hc.not_mem (by rw [h1]; exact (borel (Q : Subgroup K)).one_mem)
  have hs₃1 : s₃ ≠ 1 := by
    intro h1
    have htd : t * d₀ = 1 := h1
    have ht_inv_eq : t = d₀⁻¹ := eq_inv_of_mul_eq_one_left htd
    have htD : t ∈ cartan (Q : Subgroup K) t := by
      have h : d₀⁻¹ ∈ cartan (Q : Subgroup K) t := (cartan (Q : Subgroup K) t).inv_mem hd₀D
      rwa [← ht_inv_eq] at h
    exact hc.not_mem (cartan_le_borel (Q : Subgroup K) t htD)
  obtain ⟨z, hz, hz1⟩ := hc.exists_involution
  refine ⟨z, t, s₃, hc.center_sq z hz, hz1, hc.sq_eq_one, ht1, hs₃sq, hs₃1, ?_⟩
  set L : Subgroup K := Subgroup.closure ({z, t, s₃} : Set K) with hL
  have hd₀L : d₀ ∈ L := by
    have htL : t ∈ L := Subgroup.subset_closure (by simp)
    have hs₃L : s₃ ∈ L := Subgroup.subset_closure (by simp)
    have hdt : d₀ = t * s₃ := by
      simp only [hs₃]
      rw [← mul_assoc, hc.sq_eq_one, one_mul]
    rw [hdt]
    exact L.mul_mem htL hs₃L
  have hzt : Subgroup.closure ({z, t} : Set K) ≤ L := by
    rw [hL]
    apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  have hDle : cartan (Q : Subgroup K) t ≤ L := by
    rw [← hd₀]
    exact Subgroup.zpowers_le.mpr hd₀L
  have hcomm : ⁅cartan (Q : Subgroup K) t, Subgroup.zpowers t⁆ ≤ L := by
    rw [← hc.cartan_eq_commutator rfl]
    exact hDle
  have hsup : Subgroup.closure ({z, t} : Set K) ⊔
      ⁅cartan (Q : Subgroup K) t, Subgroup.zpowers t⁆ ≤ L := sup_le hzt hcomm
  have htop : Subgroup.closure ({z, t} : Set K) ⊔
      ⁅cartan (Q : Subgroup K) t, Subgroup.zpowers t⁆ = ⊤ :=
    h.lemma_3_2_h_suzuki Q hc.sq_eq_one hc.not_mem hz hz1
  apply top_le_iff.mp
  rw [← htop]
  exact hsup

theorem suzuki_exists_sup_conj_eq_top
    {K : Type} [Group K] [Finite K] {n : ℕ} (h : BenderType K n 2 1) (A : Subgroup K)
    (hA : ∀ x ∈ A, x * x = 1) (hcard : Nat.card A = 2 ^ n) :
    ∃ g : K, A ⊔ A.map (MulAut.conj g).toMonoidHom = ⊤ := by
  classical
  have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := n) hcard
  obtain ⟨Q, hAQ⟩ := IsPGroup.exists_le_sylow (G := K) (p := 2) hA2
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  have hAZ : A ≤ rootCenter (Q : Subgroup K) := hc.elemAbelian_le_rootCenter hAQ hA
  have hAeq : A = rootCenter (Q : Subgroup K) :=
    Subgroup.eq_of_le_of_card_ge hAZ (by rw [hc.card_center, ← hcard])
  have hsupA : A ⊔ Subgroup.zpowers t = ⊤ := by
    rw [hAeq]
    exact h.rootCenter_sup_zpowers_suzuki Q hc.sq_eq_one hc.not_mem
  have ht1 : t ≠ 1 := by
    intro h1
    exact hc.not_mem (by rw [h1]; exact (borel (Q : Subgroup K)).one_mem)
  have htord : orderOf t = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using hc.sq_eq_one) ht1
  have hzt : IsPGroup 2 (Subgroup.zpowers t) := by
    apply IsPGroup.of_card (n := 1)
    simp [Nat.card_zpowers, htord]
  obtain ⟨Q', hzQ'⟩ := IsPGroup.exists_le_sylow (G := K) (p := 2) hzt
  obtain ⟨_, hcQ'⟩ := h.exists_benderCore Q'
  have hztZ : Subgroup.zpowers t ≤ rootCenter (Q' : Subgroup K) :=
    BenderCore.elemAbelian_le_rootCenter hcQ' hzQ' (fun x hx => by
      rcases eq_one_or_eq_of_mem_zpowers hc.sq_eq_one hx with rfl | rfl
      · exact one_mul 1
      · exact hc.sq_eq_one)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q Q'
  have hmap : (Q : Subgroup K).map (MulAut.conj g).toMonoidHom = (Q' : Subgroup K) := by
    have hU : (Q : Subgroup K).map (MulAut.conj g).toMonoidHom =
        ((g • Q : Sylow 2 K) : Subgroup K) := by
      ext x
      rw [Subgroup.mem_map_equiv, Sylow.coe_subgroup_smul,
        Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      rfl
    rw [hU, hg]
  have hrc : rootCenter (Q' : Subgroup K) =
      (rootCenter (Q : Subgroup K)).map (MulAut.conj g).toMonoidHom := by
    rw [← hmap, rootCenter_map]
  have hztA : Subgroup.zpowers t ≤ A.map (MulAut.conj g).toMonoidHom := by
    rw [hAeq, ← hrc]
    exact hztZ
  refine ⟨g, ?_⟩
  apply top_le_iff.mp
  rw [← hsupA]
  exact sup_le le_sup_left (hztA.trans le_sup_right)

theorem suzuki_exists_prime_dvd_card
    {K : Type} [Group K] [Finite K] {n : ℕ} (h : BenderType K n 2 1) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ orderOf (2 : ZMod p) = 4 * n ∧ p ∣ Nat.card K := by
  obtain ⟨a, ha, hn⟩ : ∃ a, 1 ≤ a ∧ n = 2 * a + 1 := by
    rcases h.cases' with ⟨hi, -, -⟩ | ⟨-, -, a, ha, hn⟩ | ⟨hi, -, -⟩
    · omega
    · exact ⟨a, ha, hn⟩
    · omega
  have hn3 : 3 ≤ n := by omega
  obtain ⟨p, hpp⟩ :=
    CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 4 * n) (by omega) (by omega)
  have hp2 : p ≠ 2 := hpp.ne_two (by omega)
  have hord : orderOf (2 : ZMod p) = 4 * n := by
    have h1 : (2 : ZMod p) ^ (4 * n) = 1 :=
      (CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff _).mp hpp.dvd
    have hpos : 0 < orderOf (2 : ZMod p) :=
      orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨4 * n, by omega, h1⟩)
    have hle : orderOf (2 : ZMod p) ≤ 4 * n :=
      Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one h1)
    by_contra hne
    exact hpp.2.2 _ hpos (lt_of_le_of_ne hle hne)
      ((CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff _).mpr (pow_orderOf_eq_one _))
  have hp2n : p ∣ 2 ^ (2 * n) + 1 := by
    refine (hpp.dvd_add_one_iff (by omega) (2 * n)).mpr ⟨?_, ?_⟩
    · have h : 2 * (2 * n) = 4 * n := by ring
      rw [h]
    · intro hd
      have hle : 4 * n ≤ 2 * n := Nat.le_of_dvd (by omega) hd
      omega
  have hpeq : 2 ^ (2 * n) + 1 = (2 ^ n) ^ 2 + 1 := by
    rw [show 2 * n = n * 2 by omega, pow_mul]
  have hpcard : (2 ^ n) ^ 2 + 1 ∣ Nat.card K := by
    rw [h.card_eq]
    exact dvd_mul_right _ _
  exact ⟨p, hpp.prime, hp2, hord, (hpeq ▸ hp2n).trans hpcard⟩

end CFSG.Quasithin.F112Crit.APrime

end
