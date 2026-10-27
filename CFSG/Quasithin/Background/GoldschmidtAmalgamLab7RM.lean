module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab7RGrp
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL1Bound
public import CFSG.Quasithin.Background.GoldschmidtAmalgamNSetup

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmLab7

variable {D : Type*} [Group D]

theorem relIndex_sup_eq_of_le_normalizer'' {H N : Subgroup D}
    (h : H ≤ Subgroup.normalizer (N : Set D)) : N.relIndex (N ⊔ H) = N.relIndex H := by
  rw [sup_comm]
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H N h).toEquiv.symm

theorem inf_zpowers_eq_bot {Q : Subgroup D} (hQ : IsPGroup 2 Q) {y : D} (hy3 : orderOf y = 3) :
    Q ⊓ Subgroup.zpowers y = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk⟩ := hQ ⟨x, hx.1⟩
  have h1 : x ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have h2 : x ^ 3 = 1 := by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx.2
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hy3, pow_orderOf_eq_one,
      one_zpow]
  have h3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one h2
  have h4 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  have h5 : orderOf x ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd h3 h4
  have h6 : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
  rw [h6, Nat.dvd_one, orderOf_eq_one_iff] at h5
  exact h5


theorem le_normalizer_of_forall {Q M : Subgroup D}
    (hQ : ∀ t ∈ Q, ∀ m ∈ M, t * m * t⁻¹ ∈ M) : Q ≤ Subgroup.normalizer (M : Set D) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro m
  refine ⟨hQ t ht m, fun hm => ?_⟩
  have := hQ t⁻¹ (Q.inv_mem ht) _ hm
  simpa [mul_assoc] using this

variable [Finite D] {A B : Subgroup D}

section MH

variable (h : GoldHyp A B) (hne : pCoreOf 2 A ≠ pCoreOf 2 B)
  (hN : B ≤ Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D))
  {y : D} (hy : y ∈ B) (hy3 : orderOf y = 3)

omit h hne in
include hN hy hy3 in
theorem relIndex_inf_sup_zpowers :
    (pCoreOf 2 A ⊓ pCoreOf 2 B).relIndex
      ((pCoreOf 2 A ⊓ pCoreOf 2 B) ⊔ Subgroup.zpowers y) = 3 := by
  have hzN : Subgroup.zpowers y ≤
      Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D) :=
    Subgroup.zpowers_le.mpr (hN hy)
  have hR2 : IsPGroup 2 (pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) :=
    (pCoreOf_isPGroup 2 A : IsPGroup 2 (pCoreOf 2 A)).to_le inf_le_left
  rw [relIndex_sup_eq_of_le_normalizer'' hzN, ← Subgroup.inf_relIndex_right,
    inf_zpowers_eq_bot hR2 hy3, Subgroup.relIndex_bot_left, Nat.card_zpowers, hy3]

include h hne hN hy hy3

theorem pCoreOf_le_normalizer_sup :
    pCoreOf 2 A ≤ Subgroup.normalizer
      (((pCoreOf 2 A ⊓ pCoreOf 2 B) ⊔ Subgroup.zpowers y : Subgroup D) : Set D) := by
  set R : Subgroup D := pCoreOf 2 A ⊓ pCoreOf 2 B with hR
  set M : Subgroup D := R ⊔ Subgroup.zpowers y with hM
  refine le_normalizer_of_forall fun t ht m hm => ?_
  by_cases htR : t ∈ R
  · exact M.mul_mem (M.mul_mem (Subgroup.mem_sup_left htR) hm)
      (M.inv_mem (Subgroup.mem_sup_left htR))
  · have htB : t ∉ pCoreOf 2 B := fun hmem => htR ⟨ht, hmem⟩
    have htT : t ∈ A ⊓ B := h.pCoreOf_left_le ht
    have hg : t * y * t⁻¹ * y ∈ R := conj_inv_mem_inf h hne hN htT htB hy hy3
    have hty : t * y * t⁻¹ ∈ M := by
      have e : t * y * t⁻¹ = (t * y * t⁻¹ * y) * y⁻¹ := by group
      rw [e]
      exact M.mul_mem (Subgroup.mem_sup_left hg)
        (M.inv_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)))
    have htN : t ∈ Subgroup.normalizer (R : Set D) := hN htT.2
    have hle : M ≤ M.comap (MulAut.conj t).toMonoidHom := by
      refine sup_le (fun r hr => ?_) (Subgroup.zpowers_le.mpr ?_)
      · have : t * r * t⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp htN r).mp hr
        exact Subgroup.mem_sup_left this
      · exact hty
    exact hle hm

theorem sup_zpowers_inf_pCoreOf_left :
    ((pCoreOf 2 A ⊓ pCoreOf 2 B) ⊔ Subgroup.zpowers y) ⊓ pCoreOf 2 A =
      pCoreOf 2 A ⊓ pCoreOf 2 B := by
  set R : Subgroup D := pCoreOf 2 A ⊓ pCoreOf 2 B with hR
  set M : Subgroup D := R ⊔ Subgroup.zpowers y with hM
  have hRM : R ≤ M := le_sup_left
  refine le_antisymm ?_ (le_inf hRM inf_le_left)
  have hRX : R ≤ M ⊓ pCoreOf 2 A := le_inf hRM inf_le_left
  have h1 := Subgroup.relIndex_mul_relIndex R (M ⊓ pCoreOf 2 A) M hRX inf_le_left
  have h2 := Subgroup.relIndex_mul_relIndex R (M ⊓ pCoreOf 2 A) (pCoreOf 2 A) hRX inf_le_right
  rw [relIndex_inf_sup_zpowers hN hy hy3] at h1
  rw [relIndex_inf_pCoreOf_left' h hne] at h2
  have h3 : R.relIndex (M ⊓ pCoreOf 2 A) ∣ 3 := Dvd.intro _ h1
  have h4 : R.relIndex (M ⊓ pCoreOf 2 A) ∣ 2 := Dvd.intro _ h2
  have h5 : R.relIndex (M ⊓ pCoreOf 2 A) ∣ Nat.gcd 3 2 := Nat.dvd_gcd h3 h4
  have h6 : R.relIndex (M ⊓ pCoreOf 2 A) = 1 := by
    have : Nat.gcd 3 2 = 1 := by norm_num
    rw [this] at h5
    exact Nat.dvd_one.mp h5
  exact Subgroup.relIndex_eq_one.mp h6

omit hne hN hy3 in
theorem sup_zpowers_sup_le :
    ((pCoreOf 2 A ⊓ pCoreOf 2 B) ⊔ Subgroup.zpowers y) ⊔ pCoreOf 2 A ≤ B := by
  refine sup_le (sup_le (inf_le_right.trans (pCoreOf_le 2 B)) (Subgroup.zpowers_le.mpr hy)) ?_
  exact h.pCoreOf_left_le.trans inf_le_right

theorem relIndex_pCoreOf_sup :
    (pCoreOf 2 A).relIndex
      (((pCoreOf 2 A ⊓ pCoreOf 2 B) ⊔ Subgroup.zpowers y) ⊔ pCoreOf 2 A) = 3 := by
  set R : Subgroup D := pCoreOf 2 A ⊓ pCoreOf 2 B with hR
  set M : Subgroup D := R ⊔ Subgroup.zpowers y with hM
  have hQM := pCoreOf_le_normalizer_sup h hne hN hy hy3
  have hMH : M.relIndex (M ⊔ pCoreOf 2 A) = 2 := by
    rw [relIndex_sup_eq_of_le_normalizer'' hQM, ← Subgroup.inf_relIndex_right,
      sup_zpowers_inf_pCoreOf_left h hne hN hy hy3, relIndex_inf_pCoreOf_left' h hne]
  have hRM := relIndex_inf_sup_zpowers (A := A) hN hy hy3
  have hRH := Subgroup.relIndex_mul_relIndex R M (M ⊔ pCoreOf 2 A) le_sup_left le_sup_left
  have hRQ := Subgroup.relIndex_mul_relIndex R (pCoreOf 2 A) (M ⊔ pCoreOf 2 A) inf_le_left
    le_sup_right
  rw [hRM, hMH] at hRH
  rw [relIndex_inf_pCoreOf_left' h hne] at hRQ
  omega

omit hN in
theorem not_le_normalizer_sup :
    ¬ ((pCoreOf 2 A ⊓ pCoreOf 2 B) ⊔ Subgroup.zpowers y) ⊔ pCoreOf 2 A ≤
      Subgroup.normalizer (pCoreOf 2 A : Set D) := by
  intro hH
  have hyH : y ∈ ((pCoreOf 2 A ⊓ pCoreOf 2 B) ⊔ Subgroup.zpowers y) ⊔ pCoreOf 2 A :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  have hyN : y ∈ Subgroup.normalizer (pCoreOf 2 A : Set D) := hH hyH
  have hTN : A ⊓ B ≤ Subgroup.normalizer (pCoreOf 2 A : Set D) := h.T_le_normalizer_left
  have hBN : B ≤ Subgroup.normalizer (pCoreOf 2 A : Set D) := by
    have := GoldAmN.inf_sup_zpowers_eq_right_vTriple h.amalgam.toIsGoldschmidtVTriple hy hy3
    rw [← this]
    exact sup_le hTN (Subgroup.zpowers_le.mpr hyN)
  have hbot := h.eq_bot_of_normalizes (le_normalizer_pCoreOf 2 A) hBN h.pCoreOf_left_le
  have h2 := relIndex_inf_pCoreOf_left' h hne
  have h3 : (pCoreOf 2 A ⊓ pCoreOf 2 B).relIndex (pCoreOf 2 A) = 1 :=
    Subgroup.relIndex_eq_one.mpr (le_inf le_rfl (hbot.le.trans bot_le))
  omega

end MH

end GoldAmLab7

end F6

end CFSG.Quasithin
