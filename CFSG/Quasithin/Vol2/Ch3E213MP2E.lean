module

public import CFSG.Quasithin.H13.QRCPairedDihedral

public section

namespace CFSG.Quasithin.Ch3E213M.P2

open Subgroup CFSG.ABGLocalTools CFSG.Quasithin.SteinbergBS

variable {A : Type*} [Group A] [Finite A]

theorem dihedral_pair {S B E₁ : Subgroup A} {e x₁ : A} {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hE₁z : E₁ = zpowers e) (hoe : orderOf e = 2) (hox : orderOf x₁ = ℓ)
    (hex : e * x₁ * e⁻¹ = x₁⁻¹) (hx₁B : x₁ ∉ B) (hE₁S : E₁ ≤ S) (hSB : S ≤ B) :
    x₁ ∈ E₁ ⊔ conjugate E₁ x₁ ∧
      Nonempty (↥(E₁ ⊔ conjugate E₁ x₁) ≃* DihedralGroup ℓ) ∧
      Nat.card ↥(E₁ ⊔ conjugate E₁ x₁) = 2 * ℓ ∧ B ⊓ (E₁ ⊔ conjugate E₁ x₁) = E₁ ∧
      S ⊓ (E₁ ⊔ conjugate E₁ x₁) = E₁ ∧
      IsSylowOf 2 (S ⊓ (E₁ ⊔ conjugate E₁ x₁)) (E₁ ⊔ conjugate E₁ x₁) ∧
      kerIn (B ⊓ (E₁ ⊔ conjugate E₁ x₁)) (E₁ ⊔ conjugate E₁ x₁) = ⊥ ∧
      inSubgroup (CFSG.pCore 2) (E₁ ⊔ conjugate E₁ x₁) = ⊥ ∧
      inSubgroup (CFSG.pCore 2) (B ⊓ (E₁ ⊔ conjugate E₁ x₁)) = S ⊓ (E₁ ⊔ conjugate E₁ x₁) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓodd : ℓ % 2 = 1 := Nat.odd_iff.1 (hℓ.odd_of_ne_two hℓ2)
  have heE : e ∈ E₁ := hE₁z ▸ mem_zpowers e
  have hee : e * e = 1 := by rw [← sq, ← hoe, pow_orderOf_eq_one]
  have he1' : e ≠ 1 := fun h => by rw [h, orderOf_one] at hoe; omega
  have hx₁ℓ : x₁ ^ ℓ = 1 := hox ▸ pow_orderOf_eq_one x₁
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
  have hex' : e * x₁⁻¹ * e⁻¹ = x₁ := by
    have h1 : e * x₁⁻¹ * e⁻¹ = (e * x₁ * e⁻¹)⁻¹ := by group
    rw [h1, hex, inv_inv]
  set L₁ := E₁ ⊔ conjugate E₁ x₁ with hL₁
  have hconj_e : x₁⁻¹ * e * x₁ ∈ conjugate E₁ x₁ := by
    rw [mem_conjugate_iff, show x₁ * (x₁⁻¹ * e * x₁) * x₁⁻¹ = e by group]
    exact heE
  have hx₁sq : e * (x₁⁻¹ * e * x₁) = x₁ ^ 2 := by
    calc e * (x₁⁻¹ * e * x₁) = (e * x₁⁻¹ * e⁻¹) * x₁ := by rw [heinv]; group
      _ = x₁ ^ 2 := by rw [hex', sq]
  have hx₁L : x₁ ∈ L₁ := by
    have h2 : x₁ ^ 2 ∈ L₁ := hx₁sq ▸ L₁.mul_mem (mem_sup_left heE) (mem_sup_right hconj_e)
    have h3 : x₁ = (x₁ ^ 2) ^ ((ℓ + 1) / 2) := by
      rw [← pow_mul, show 2 * ((ℓ + 1) / 2) = ℓ + 1 by omega, pow_succ, hx₁ℓ, one_mul]
    rw [h3]
    exact L₁.pow_mem h2 _
  have hinv : ∀ c ∈ zpowers x₁, e * c * e⁻¹ = c⁻¹ := by
    intro c hc
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hc
    have h1 : e * x₁ ^ j * e⁻¹ = (e * x₁ * e⁻¹) ^ j := by
      rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
    rw [h1, hex, inv_zpow]
  have heN : zpowers e ≤ normalizer ((zpowers x₁ : Subgroup A) : Set A) := by
    rw [zpowers_le]
    refine mem_normalizer_iff.2 fun y => ⟨fun hy => ?_, fun hy => ?_⟩
    · obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hy
      rw [hinv _ (zpow_mem (mem_zpowers x₁) j)]
      exact inv_mem (zpow_mem (mem_zpowers x₁) j)
    · obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hy
      have h1 : y = e⁻¹ * (e * y * e⁻¹) * e := by group
      have h3 : e⁻¹ * x₁ ^ j * e = e * x₁ ^ j * e⁻¹ := by rw [heinv]
      rw [h1, ← hj, h3, hinv _ (zpow_mem (mem_zpowers x₁) j)]
      exact inv_mem (zpow_mem (mem_zpowers x₁) j)
  have hLz : L₁ = zpowers x₁ ⊔ zpowers e := by
    apply le_antisymm
    · refine sup_le (by rw [hE₁z]; exact le_sup_right) fun y hy => ?_
      rw [mem_conjugate_iff] at hy
      have h1 : y = x₁⁻¹ * (x₁ * y * x₁⁻¹) * x₁ := by group
      rw [h1]
      exact mul_mem (mul_mem (mem_sup_left (inv_mem (mem_zpowers x₁)))
        (mem_sup_right (hE₁z ▸ hy))) (mem_sup_left (mem_zpowers x₁))
    · exact sup_le (zpowers_le.2 hx₁L) (zpowers_le.2 (mem_sup_left heE))
  have heC : e ∉ zpowers x₁ := by
    intro h
    have h1 := orderOf_dvd_of_mem_zpowers h
    rw [hoe, hox] at h1
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hℓ).1 h1).symm
  obtain ⟨φ⟩ := CFSG.Glauberman.Dickson.nonempty_sup_zpowers_mulEquiv_dihedral (zpowers x₁)
    inferInstance e heC hee hinv
  have hCℓ : Nat.card (zpowers x₁) = ℓ := by rw [Nat.card_zpowers, hox]
  rw [hCℓ] at φ
  have hD : Nonempty (L₁ ≃* DihedralGroup ℓ) := ⟨(MulEquiv.subgroupCongr hLz).trans φ⟩
  have hcardL : Nat.card L₁ = 2 * ℓ := by
    rw [Nat.card_congr ((MulEquiv.subgroupCongr hLz).trans φ).toEquiv, DihedralGroup.nat_card]
  have hE₁B : E₁ ≤ B := hE₁S.trans hSB
  have hBL : B ⊓ L₁ = E₁ := by
    refine le_antisymm (fun y hy => ?_) (le_inf hE₁B le_sup_left)
    obtain ⟨hyB, hyL⟩ := mem_inf.1 hy
    rw [hLz, ← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left (zpowers x₁) (zpowers e)
      heN] at hyL
    obtain ⟨c, hc, d, hd, rfl⟩ := hyL
    have hdE : d ∈ E₁ := hE₁z ▸ hd
    have hcB : c ∈ B := by
      have := B.mul_mem hyB (B.inv_mem (hE₁B hdE))
      rwa [mul_inv_cancel_right] at this
    have hc1 : c = 1 := by
      by_contra hc1
      apply hx₁B
      have h1 : zpowers c = zpowers x₁ := by
        refine eq_of_le_of_card_ge (zpowers_le.2 hc) ?_
        rw [Nat.card_zpowers, Nat.card_zpowers, hox]
        have h2 : orderOf c ∣ ℓ := hox ▸ orderOf_dvd_of_mem_zpowers hc
        rcases (Nat.dvd_prime hℓ).1 h2 with h | h
        · exact absurd (orderOf_eq_one_iff.1 h) hc1
        · rw [h]
      have h3 := mem_zpowers x₁
      rw [← h1] at h3
      exact (zpowers_le.2 hcB) h3
    show c * d ∈ E₁
    rw [hc1, one_mul]
    exact hdE
  have hSL : S ⊓ L₁ = E₁ :=
    le_antisymm (hBL ▸ inf_le_inf_right L₁ hSB) (le_inf hE₁S le_sup_left)
  have hE₁2 : Nat.card E₁ = 2 := by rw [hE₁z, Nat.card_zpowers, hoe]
  have hE₁2' : IsPGroup 2 E₁ := IsPGroup.of_card (n := 1) (by rw [hE₁2, pow_one])
  have hsyl : IsSylowOf 2 E₁ L₁ := by
    refine isSylowOf_iff.2 ⟨le_sup_left, hE₁2', ?_⟩
    have h1 := relIndex_mul_card E₁ L₁
    rw [inf_eq_left.2 (le_sup_left : E₁ ≤ L₁), hE₁2, hcardL] at h1
    have h2 : E₁.relIndex L₁ = ℓ := by omega
    rw [h2]
    exact fun h => hℓ2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hℓ).1 h).symm
  have hker : kerIn E₁ L₁ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [mem_bot]
    by_contra hy1
    have hyE : y ∈ E₁ := by simpa using hy 1 (one_mem L₁)
    have hye : y = e := H13.QRC.eq_of_mem_zpowers_of_orderOf_two hoe (hE₁z ▸ hyE) hy1
    have h1 : x₁ * y * x₁⁻¹ ∈ E₁ := hy x₁ hx₁L
    rw [hye] at h1
    have h2 : x₁ * e * x₁⁻¹ = e := by
      refine H13.QRC.eq_of_mem_zpowers_of_orderOf_two hoe (hE₁z ▸ h1) fun h => he1' ?_
      have h3 : e = x₁⁻¹ * (x₁ * e * x₁⁻¹) * x₁ := by group
      rw [h3, h, mul_one, inv_mul_cancel]
    have h4 : x₁ * e = e * x₁ := by
      calc x₁ * e = x₁ * e * x₁⁻¹ * x₁ := by group
        _ = e * x₁ := by rw [h2]
    have h5 : e * x₁ * e⁻¹ = x₁ := by rw [← h4, mul_inv_cancel_right]
    rw [hex] at h5
    have h6 : x₁ ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 1 [← h5]
      exact inv_mul_cancel x₁
    have h7 := orderOf_dvd_of_pow_eq_one h6
    rw [hox] at h7
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h7)
  refine ⟨hx₁L, hD, hcardL, hBL, hSL, hSL ▸ hsyl, hBL ▸ hker,
    H13.QRC.inSubgroup_pCore_eq_bot_of_kerIn hsyl le_rfl hker, ?_⟩
  rw [hBL, hSL]
  exact H13.QRC.inSubgroup_pCore_eq_of_isSylowOf hsyl le_rfl le_sup_left le_normalizer

end CFSG.Quasithin.Ch3E213M.P2
