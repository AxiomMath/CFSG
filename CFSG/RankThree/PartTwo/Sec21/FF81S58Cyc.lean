module

public import CFSG.RankThree.PartTwo.Sec21.FF81S58Cen
public import CFSG.RankThree.PartTwo.Sec21.FF81S58Hom
import CFSG.RankThree.PartTwo.Sec21.FF81Sec32A
import CFSG.RankThree.PartTwo.Sec21.FF81Sec32
import CFSG.RankThree.PartTwo.Sec21.FF81Step0
import CFSG.RankThree.PartTwo.Sec21.FF81Prop51
import CFSG.RankThree.PartTwo.Sec21.FF81S0
public import CFSG.RankThree.PartTwo.Sec21.FF81J

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.S58

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ s₀ : G}
  {M : Subgroup G}

theorem cenS_M_le_L (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) (h526 : FF81Conc5_2_6 b b₁ b₂ b₃ s₀)
    (hM7 : FF81Conc5_7 b b₁ b₂ b₃ s₀ M) : CenS M ≤ L := by
  intro x hx
  have hB := h5.basis
  have h0 : Opp 3 (Cen b) = ⊥ := h526.1
  have hbM : b ∈ M := A₁_le_M h526 hM7 b_mem_A₁
  have ht₀M : t₀ ∈ M := t₀_mem_M h5 hM7
  have hxb : x ∈ Cen b :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hx b hbM).symm
  have hxt : t₀ * x * t₀⁻¹ = x := by
    rw [Subgroup.mem_centralizer_iff.mp hx t₀ ht₀M, mul_inv_cancel_right]
  obtain ⟨l, hl, hd⟩ := hB.hyp.exists_decomp hxb
  have hdb : l⁻¹ * x ∈ Subgroup.zpowers b := by
    rw [← hB.cen_inf_cenS_eq h0]; exact hd
  have hy3 : (l⁻¹ * x) ^ 3 = 1 := hB.hyp.cube_of_mem_zpowers hdb
  have hyinv : t₀ * (l⁻¹ * x) * t₀⁻¹ = (l⁻¹ * x)⁻¹ := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hdb
    rw [← hk, ← conj_zpow, h5.ht₀b, inv_zpow]
  have hy' : t₀ * (l⁻¹ * x) * t₀⁻¹ = l⁻¹ * x := by
    rw [show t₀ * (l⁻¹ * x) * t₀⁻¹ = (t₀ * l⁻¹ * t₀⁻¹) * (t₀ * x * t₀⁻¹) by group, hxt,
      conj_eq_of_mem_cenS h5.ht₀L (L.inv_mem hl)]
  have hy2 : (l⁻¹ * x) ^ 2 = 1 := by
    have : (l⁻¹ * x)⁻¹ = l⁻¹ * x := hyinv.symm.trans hy'
    rw [sq]
    exact mul_eq_one_iff_eq_inv.mpr this.symm
  have hy1 : l⁻¹ * x = 1 := by
    calc l⁻¹ * x = (l⁻¹ * x) ^ 3 * ((l⁻¹ * x) ^ 2)⁻¹ := by group
      _ = 1 := by rw [hy3, hy2]; simp
  have : x = l := by
    calc x = l * (l⁻¹ * x) := by group
      _ = l := by rw [hy1, mul_one]
  rw [this]
  exact hl

theorem ffCentCyclicSylow_M
    (hrk : ∀ E : Subgroup G, E ≤ L → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ 3 = 1) →
      Nat.card E ≤ 27)
    (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) (h526 : FF81Conc5_2_6 b b₁ b₂ b₃ s₀)
    (hM7 : FF81Conc5_7 b b₁ b₂ b₃ s₀ M) : FFCentCyclicSylow M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro P
  have hB := h5.basis
  have h0 : Opp 3 (Cen b) = ⊥ := h526.1
  have hCL : CenS M ≤ L := cenS_M_le_L h5 h526 hM7
  set P' : Subgroup G := (P : Subgroup ↥(CenS M)).map (CenS M).subtype with hP'def
  have hP'C : P' ≤ CenS M := Subgroup.map_subtype_le _
  have hP'3 : IsPGroup 3 P' := P.isPGroup'.map _
  have hP'L : P' ≤ L := hP'C.trans hCL
  have hAM : Subgroup.closure ({b, b₁, b₂ * b₃} : Set G) ≤ M := A₁_le_M h526 hM7
  have hAel := isElemAb_A₁ h5
  set A := Subgroup.closure ({b, b₁, b₂ * b₃} : Set G) with hAdef
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) hAel.2
  have hcomm : ∀ p ∈ P', ∀ a ∈ A, p * a = a * p := fun p hp a ha =>
    (Subgroup.mem_centralizer_iff.mp (hP'C hp) a (hAM ha)).symm
  have hinf : P' ⊓ A = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have : x ∈ M ⊓ CenS M := ⟨hAM hx.2, hP'C hx.1⟩
    rw [inf_cenS_self_of_model hM7.2.1] at this
    exact this
  have hnorm : P' ≤ Subgroup.normalizer (A : Set G) := fun p hp =>
    Subgroup.centralizer_le_normalizer (A : Set G) (Subgroup.mem_centralizer_iff.mpr fun a ha =>
      (hcomm p hp a ha).symm)
  have hQ3 : IsPGroup 3 ↥(P' ⊔ A) := IsPGroup.to_sup_of_normal_right' hP'3 hA3 hnorm
  have hQcard : Nat.card ↥(P' ⊔ A) = Nat.card P' * 27 := by
    have := card_sup_mul_card_inf P' A hnorm
    rw [hinf, Subgroup.card_bot, mul_one, hAel.2] at this
    rw [this]; norm_num
  have hAcen : A ≤ Cen b := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_isElemAb hAel a ha b b_mem_A₁)
  have hQC : P' ⊔ A ≤ Cen b := sup_le (hP'L.trans hB.hyp.hLC) hAcen
  have hQdvd : Nat.card ↥(P' ⊔ A) ∣ 3 * 1451520 := by
    rw [← card_cen_b hB h0]; exact Subgroup.card_dvd_of_le hQC
  obtain ⟨n, hn⟩ := hQ3.exists_card_eq
  have hn5 : n ≤ 5 := by
    by_contra hlt
    have h6 : 3 ^ 6 ∣ 3 ^ n := pow_dvd_pow 3 (by omega)
    rw [← hn] at h6
    have := h6.trans hQdvd
    norm_num at this
  have hP'9 : Nat.card P' ≤ 9 := by
    have h1 : 3 ^ n ≤ 3 ^ 5 := Nat.pow_le_pow_right (by norm_num) hn5
    rw [hn.symm, hQcard] at h1
    omega
  have hcardP : Nat.card ↥(P : Subgroup ↥(CenS M)) = Nat.card P' :=
    (Subgroup.card_map_of_injective (CenS M).subtype_injective).symm
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  by_contra hncyc
  have hk2 : k = 2 := by
    by_contra hne
    have hk3 : k ≤ 2 := by
      by_contra hlt
      have : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hk1 : k ≤ 1 := by omega
    apply hncyc
    refine isCyclic_of_card_dvd_prime (p := 3) ?_
    rw [hk]
    exact (pow_dvd_pow 3 hk1).trans (by simp)
  subst hk2
  have hPcomm : ∀ x y : ↥(P : Subgroup ↥(CenS M)), x * y = y * x :=
    IsPGroup.commutative_of_card_eq_prime_sq (p := 3) hk
  have hexp : ∀ x : ↥(P : Subgroup ↥(CenS M)), x ^ 3 = 1 := by
    intro x
    have hd : orderOf x ∣ 3 ^ 2 := hk ▸ orderOf_dvd_natCard x
    obtain ⟨i, hi, hx⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
    have hi2 : i ≠ 2 := by
      rintro rfl
      exact hncyc (isCyclic_of_orderOf_eq_card x (by rw [hx, hk]))
    have : orderOf x ∣ 3 := by
      rw [hx]
      interval_cases i
      · simp
      · simp
      · exact absurd rfl hi2
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have hP'comm : ∀ x ∈ P', ∀ y ∈ P', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have := congrArg (fun z : ↥(P : Subgroup ↥(CenS M)) => (((z : ↥(CenS M)) : G)))
      (hPcomm ⟨x, hx⟩ ⟨y, hy⟩)
    simpa using this
  have hP'exp : ∀ x ∈ P', x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have := congrArg (fun z : ↥(P : Subgroup ↥(CenS M)) => (((z : ↥(CenS M)) : G)))
      (hexp ⟨x, hx⟩)
    simpa using this
  have hAcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := comm_of_isElemAb hAel
  have hmulset := Subgroup.coe_mul_of_left_le_normalizer_right P' A hnorm
  have hQmem : ∀ x ∈ P' ⊔ A, ∃ p ∈ P', ∃ a ∈ A, x = p * a := by
    intro x hx
    have hx' : x ∈ (↑(P' ⊔ A) : Set G) := hx
    rw [hmulset] at hx'
    obtain ⟨p, hp, a, ha, hpa⟩ := Set.mem_mul.mp hx'
    exact ⟨p, hp, a, ha, hpa.symm⟩
  have hQcomm : ∀ x ∈ P' ⊔ A, ∀ y ∈ P' ⊔ A, x * y = y * x := by
    intro x hx y hy
    obtain ⟨p, hp, a, ha, rfl⟩ := hQmem x hx
    obtain ⟨p', hp', a', ha', rfl⟩ := hQmem y hy
    have e1 : p * a * (p' * a') = (p * p') * (a * a') := by
      calc p * a * (p' * a') = p * (a * p') * a' := by group
        _ = p * (p' * a) * a' := by rw [← hcomm p' hp' a ha]
        _ = (p * p') * (a * a') := by group
    have e2 : p' * a' * (p * a) = (p' * p) * (a' * a) := by
      calc p' * a' * (p * a) = p' * (a' * p) * a := by group
        _ = p' * (p * a') * a := by rw [← hcomm p hp a' ha']
        _ = (p' * p) * (a' * a) := by group
    rw [e1, e2, hP'comm p hp p' hp', hAcomm a ha a' ha']
  have hQexp : ∀ x ∈ P' ⊔ A, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨p, hp, a, ha, rfl⟩ := hQmem x hx
    rw [(show Commute p a from hcomm p hp a ha).mul_pow, hP'exp p hp,
      pow_three_eq_one_of_isElemAb hAel ha, one_mul]
  have := (hB.hyp.card_elem_le hrk hQC hQcomm hQexp).1
  rw [hQcard, ← hcardP, hk] at this
  norm_num at this

end CFSG.RankThree.PartTwo.Sec21.FF81.S58
