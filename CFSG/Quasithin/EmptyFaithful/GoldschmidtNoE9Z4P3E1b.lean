module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P3E1
public import CFSG.Quasithin.EmptyFaithful.S146zRElem

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

namespace E9P2.E1

section Hat

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem qPi_eq_of_mem {G₁ : Subgroup G} {y z : G} (hy : y ∈ G₁) (hz : z ∈ G₁)
    (h : y⁻¹ * z ∈ pCoreOf 2 G₁) : qPi G₁ ⟨y, hy⟩ = qPi G₁ ⟨z, hz⟩ := by
  have h1 : qPi G₁ ((⟨y, hy⟩ : ↥G₁)⁻¹ * ⟨z, hz⟩) = 1 := (mk_eq_one_iff_mem_pCoreOf _).mpr h
  rwa [map_mul, map_inv, inv_mul_eq_one] at h1

theorem hat_sq_inverts {G₁ H : Subgroup G} (hHG : H ≤ G₁)
    (hn : G₁ ≤ Subgroup.normalizer (oTwoUpper H : Set G)) {σ : G} (hσ : σ ∈ H)
    (hinv : ∀ y ∈ oTwoUpper H, σ ^ 2 * y * (σ ^ 2)⁻¹ * y ∈ pCoreOf 2 H) {x : G}
    (hx : x ∈ oTwoUpper H) (hσG : σ ∈ G₁) (hxG : x ∈ G₁) :
    qPi G₁ ⟨σ, hσG⟩ ^ 2 * qPi G₁ ⟨x, hxG⟩ * (qPi G₁ ⟨σ, hσG⟩)⁻¹ ^ 2 = (qPi G₁ ⟨x, hxG⟩)⁻¹ := by
  have hσ2 : σ ^ 2 ∈ Subgroup.normalizer (H : Set G) := Subgroup.le_normalizer (H.pow_mem hσ 2)
  have hwK : σ ^ 2 * x * (σ ^ 2)⁻¹ * x ∈ oTwoUpper H :=
    (oTwoUpper H).mul_mem (conj_mem_oTwoUpper hσ2 hx) hx
  have hw : σ ^ 2 * x * (σ ^ 2)⁻¹ * x ∈ pCoreOf 2 G₁ :=
    inf_pCoreOf_le (oTwoUpper_le H) hHG hn ⟨hwK, hinv x hx⟩
  have h1 : qPi G₁ ((⟨σ, hσG⟩ : ↥G₁) ^ 2 * ⟨x, hxG⟩ * ((⟨σ, hσG⟩ : ↥G₁) ^ 2)⁻¹ * ⟨x, hxG⟩) = 1 :=
    (mk_eq_one_iff_mem_pCoreOf _).mpr hw
  rw [map_mul, map_mul, map_mul, map_inv, map_pow] at h1
  rw [inv_pow]
  exact eq_inv_of_mul_eq_one_left h1

theorem hat_conj_pow {G₁ H : Subgroup G} (hHG : H ≤ G₁)
    (hn : G₁ ≤ Subgroup.normalizer (oTwoUpper H : Set G)) {σ t : G} (hσ : σ ∈ H) {i : ℕ}
    (hq : t * (σ ^ i)⁻¹ ∈ pCoreOf 2 H) {x : G} (hx : x ∈ oTwoUpper H)
    (hσG : σ ∈ G₁) (htG : t ∈ G₁) (hxG : x ∈ G₁) :
    qPi G₁ ⟨t, htG⟩ * qPi G₁ ⟨x, hxG⟩ * (qPi G₁ ⟨t, htG⟩)⁻¹ =
      qPi G₁ ⟨σ, hσG⟩ ^ i * qPi G₁ ⟨x, hxG⟩ * (qPi G₁ ⟨σ, hσG⟩)⁻¹ ^ i := by
  set q : G := t * (σ ^ i)⁻¹ with hqdef
  set z : G := σ ^ i * x * (σ ^ i)⁻¹ with hz
  have hσi : σ ^ i ∈ Subgroup.normalizer (H : Set G) := Subgroup.le_normalizer (H.pow_mem hσ i)
  have hzK : z ∈ oTwoUpper H := conj_mem_oTwoUpper hσi hx
  have hzH : z ∈ H := oTwoUpper_le H hzK
  have hqH : q ∈ H := pCoreOf_le 2 H hq
  have hqK : q * z * q⁻¹ ∈ oTwoUpper H :=
    conj_mem_oTwoUpper (Subgroup.le_normalizer hqH) hzK
  have hqQ : z⁻¹ * q * z ∈ pCoreOf 2 H := by
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (H.inv_mem hzH)) q).mp hq
    simpa using this
  have hcomm : z⁻¹ * (t * x * t⁻¹) ∈ pCoreOf 2 G₁ := by
    have heq : z⁻¹ * (t * x * t⁻¹) = (z⁻¹ * q * z) * q⁻¹ := by
      have ht' : t = q * σ ^ i := by simp [hqdef]
      rw [ht', hz]
      group
    refine inf_pCoreOf_le (oTwoUpper_le H) hHG hn ⟨?_, ?_⟩
    · have : z⁻¹ * (t * x * t⁻¹) = z⁻¹ * (q * z * q⁻¹) := by
        have ht' : t = q * σ ^ i := by simp [hqdef]
        rw [ht', hz]
        group
      rw [this]
      exact (oTwoUpper H).mul_mem ((oTwoUpper H).inv_mem hzK) hqK
    · rw [heq]
      exact (pCoreOf 2 H).mul_mem hqQ ((pCoreOf 2 H).inv_mem hq)
  have hzG : z ∈ G₁ := hHG hzH
  have htxG : t * x * t⁻¹ ∈ G₁ := G₁.mul_mem (G₁.mul_mem htG hxG) (G₁.inv_mem htG)
  have h1 : qPi G₁ ⟨z, hzG⟩ = qPi G₁ ⟨t * x * t⁻¹, htxG⟩ := qPi_eq_of_mem hzG htxG hcomm
  have e1 : (⟨z, hzG⟩ : ↥G₁) = ⟨σ, hσG⟩ ^ i * ⟨x, hxG⟩ * (⟨σ, hσG⟩⁻¹) ^ i :=
    Subtype.ext (by simp [hz, inv_pow])
  have e2 : (⟨t * x * t⁻¹, htxG⟩ : ↥G₁) = ⟨t, htG⟩ * ⟨x, hxG⟩ * ⟨t, htG⟩⁻¹ := rfl
  rw [e1, e2, map_mul, map_mul, map_mul, map_mul, map_inv, map_pow, map_pow, map_inv] at h1
  exact h1.symm

theorem isElemAbelian_hat {G₁ P : Subgroup G} (hPG : P ≤ G₁) (hPel : IsElemAbelian 3 P)
    (hP9 : Nat.card P = 9) :
    IsElemAbelian 3 (imageOTwoQuot G₁ P) ∧ Nat.card (imageOTwoQuot G₁ P) = 9 := by
  obtain ⟨hE1, hE2⟩ := zm_isElemAbelian_subgroupOf hPG hPel
  obtain ⟨hEb, hEbc⟩ := isElemAbelian_map_quotient (CFSG.Open.pCore 2 ↥G₁)
    (CFSG.LieType.BorelTits.pCore_isPGroup 2) (by norm_num : (3 : ℕ) ≠ 2) hE1
  refine ⟨hEb, ?_⟩
  change Nat.card ↥((P.subgroupOf G₁).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥G₁))) = 9
  rw [hEbc, hE2, hP9]

omit [Finite G] in
theorem hat_K_eq {G₁ K P : Subgroup G} (hKG : K ≤ G₁) (hPK : P ≤ K)
    (h : ∀ k ∈ K, ∃ x ∈ P, x⁻¹ * k ∈ pCoreOf 2 G₁) :
    imageOTwoQuot G₁ K = imageOTwoQuot G₁ P := by
  refine le_antisymm (fun u hu => ?_) (q_image_mono hPK)
  obtain ⟨k, hkG, hkK, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
  obtain ⟨x, hxP, hxk⟩ := h k hkK
  have hxG : x ∈ G₁ := hKG (hPK hxP)
  have h1 : qPi G₁ ⟨x, hxG⟩ = qPi G₁ ⟨k, hkG⟩ := qPi_eq_of_mem hxG hkG hxk
  exact mem_imageOTwoQuot_iff.mpr ⟨x, hxG, hxP, h1⟩

omit [Finite G] in
theorem card_le_nine_of_pRank {X : Type*} [Group X] [Finite X]
    (h : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2) {E : Subgroup X} (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 9 := by
  have hp : IsPGroup 3 ↥E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hkle : k ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
    refine le_csSup ⟨Nat.card X, ?_⟩ ⟨E, le_top, hE, hk⟩
    rintro r ⟨B, -, -, hB⟩
    calc r ≤ 3 ^ r := (Nat.lt_pow_self (by norm_num)).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card X := Subgroup.card_le_card_group B
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (hkle.trans h)
    _ = 9 := by norm_num

end Hat

end E9P2.E1

end CFSG.Quasithin
