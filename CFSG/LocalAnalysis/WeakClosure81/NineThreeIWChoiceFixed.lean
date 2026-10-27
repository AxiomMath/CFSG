module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeIWChoiceSetup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

theorem nine3_mem_zpowers_involution {u : G} (hu2 : u * u = 1) {s : G}
    (hs : s ∈ Subgroup.zpowers u) : s = 1 ∨ s = u := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs
  have hkmod : u ^ k = u ^ (k % 2) :=
    zpow_eq_zpow_emod' k (by simpa [pow_two] using hu2)
  rcases Int.emod_two_eq_zero_or_one k with hk0 | hk1
  · left
    rw [← hk, hkmod, hk0]
    simp
  · right
    rw [← hk, hkmod, hk1]
    norm_num

theorem nine3_eq_sup_inf_zpowers (hc : Nine3Choice V T A K S X p g x)
    {U : Subgroup G} (hU : U ∈ omegaIn V K (nineE V K)) {u : G}
    (huU : u ∈ U) (huR : u ∉ pCoreOf 2 K) :
    U = (U ⊓ pCoreOf 2 K) ⊔ Subgroup.zpowers u := by
  let H : Subgroup G := U ⊓ pCoreOf 2 K
  let J : Subgroup G := H ⊔ Subgroup.zpowers u
  have hrel : H.relIndex U = 2 := nine3_relIndex_of_mem_omega hc hU
  have hHJ : H ≤ J := le_sup_left
  have hJle : J ≤ U := sup_le inf_le_left (Subgroup.zpowers_le.mpr huU)
  have hne : J ≠ H := by
    intro hEq
    have huJ : u ∈ J := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
    rw [hEq] at huJ
    exact huR huJ.2
  have hmul := Subgroup.relIndex_mul_relIndex (H := H) (K := J) (L := U) hHJ hJle
  have hdvd : J.relIndex U ∣ 2 := ⟨H.relIndex J, by rw [mul_comm, hmul, hrel]⟩
  have hrelJ : J.relIndex U = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact h1
    · exfalso
      have hHJ1 : H.relIndex J = 1 := by
        rw [h2] at hmul
        omega
      have hJH : J ≤ H := Subgroup.relIndex_eq_one.mp hHJ1
      exact hne (le_antisymm hJH hHJ)
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hrelJ) hJle

theorem nine3_exists_inverted_P (hc : Nine3Choice V T A K S X p g x)
    (hI : Nine3IFacts V K S) :
    ∃ (a : G) (P : Subgroup G), a ∈ A ∧ a ∉ pCoreOf 2 K ∧ P ≤ K ∧
      Nat.card ↥P = p ∧ X ≤ pCoreOf 2 K ⊔ P ∧
      P ≤ Subgroup.closure ({a, x⁻¹ * a * x} : Set G) ∧
      ∀ y ∈ P, a⁻¹ * y * a = y⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime p) := ⟨hc.core.hyp.base.prime⟩
  obtain ⟨a, ha, haR⟩ := nine3_exists_a_not_mem_pCore hc
  have hxX : x ∈ X := hc.x_mem
  have hxK : x ∈ K := hc.core.hyp.base.sylowP.le hxX
  have hXcard : Nat.card X = p := hc.core.card
  have hxord : orderOf x = p := by
    rw [hc.x_gen, Nat.card_zpowers] at hXcard
    exact hXcard
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hxord
    exact hc.core.hyp.base.prime.ne_one hxord.symm
  set c : G := a * (x⁻¹ * a * x) with hcdef
  have hcK : c ∈ K := by
    have h := nine3_c_mem_sup hc ha hxX
    exact (sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
      hc.core.hyp.base.sylowP.le) h
  have hcnot : ∀ n : ℕ, c ^ 2 ^ n ≠ 1 :=
    nine3_c_pow_two_ne_one hc hI ha haR hxX hx1
  obtain ⟨y, hyz, hyord⟩ := nine3_exists_order_p hc hcK hcnot
  have hyK : y ∈ K := (Subgroup.zpowers_le.mpr hcK) hyz
  have hP_le_K : Subgroup.zpowers y ≤ K := Subgroup.zpowers_le.mpr hyK
  have hP_le_RX : Subgroup.zpowers y ≤ pCoreOf 2 K ⊔ X :=
    Subgroup.zpowers_le.mpr ((Subgroup.zpowers_le.mpr (nine3_c_mem_sup hc ha hxX)) hyz)
  have hRX : pCoreOf 2 K ⊓ X = ⊥ := by
    exact (IsPGroup.disjoint_of_ne 2 p (Ne.symm hc.core.hyp.base.odd)
      (pCoreOf 2 K) X
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
      hc.core.hyp.base.sylowP.isPGroup).eq_bot
  have hRP : pCoreOf 2 K ⊓ Subgroup.zpowers y = ⊥ := by
    exact (IsPGroup.disjoint_of_ne 2 p (Ne.symm hc.core.hyp.base.odd)
      (pCoreOf 2 K) (Subgroup.zpowers y)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
      (IsPGroup.of_card (by rw [Nat.card_zpowers, hyord, pow_one]))).eq_bot
  have hRXnorm : X ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    hc.core.hyp.base.sylowP.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
  have hRPnorm : Subgroup.zpowers y ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    hP_le_K.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
  have hcardRX : Nat.card ↥(pCoreOf 2 K ⊔ X) =
      Nat.card ↥(pCoreOf 2 K) * Nat.card ↥X :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (pCoreOf 2 K) X hRXnorm (disjoint_iff.mpr hRX)
  have hcardRP : Nat.card ↥(pCoreOf 2 K ⊔ Subgroup.zpowers y) =
      Nat.card ↥(pCoreOf 2 K) * Nat.card ↥(Subgroup.zpowers y) :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (pCoreOf 2 K) (Subgroup.zpowers y) hRPnorm (disjoint_iff.mpr hRP)
  have hsup_eq : pCoreOf 2 K ⊔ Subgroup.zpowers y = pCoreOf 2 K ⊔ X := by
    apply Subgroup.eq_of_le_of_card_ge (H := pCoreOf 2 K ⊔ Subgroup.zpowers y)
      (K := pCoreOf 2 K ⊔ X)
    · exact sup_le le_sup_left hP_le_RX
    · rw [hcardRX, hcardRP, Nat.card_zpowers, hyord, hXcard]
  have hac : a⁻¹ * c * a = c⁻¹ := by
    have ha2 : a * a = 1 := by
      have h := (isElemAbelian_of_mem_omegaSet hc.core.hyp7.1
        hc.core.A_mem_nineOmegaIn.1).2 a ha
      simpa [pow_two] using h
    have hb2 : (x⁻¹ * a * x) * (x⁻¹ * a * x) = 1 := by
      calc (x⁻¹ * a * x) * (x⁻¹ * a * x) = x⁻¹ * (a * a) * x := by group
        _ = 1 := by rw [ha2]; group
    rw [hcdef, mul_inv_rev, inv_eq_of_mul_eq_one_left hb2,
      inv_eq_of_mul_eq_one_left ha2]
    calc a * (a * (x⁻¹ * a * x)) * a =
        (a * a) * ((x⁻¹ * a * x) * a) := by group
      _ = (x⁻¹ * a * x) * a := by rw [ha2, one_mul]
  have hpow : ∀ k : ℤ, a⁻¹ * (c ^ k) * a = (c ^ k)⁻¹ := by
    intro k
    have h1 : (MulAut.conj a⁻¹).toMonoidHom (c ^ k) =
        ((MulAut.conj a⁻¹).toMonoidHom c) ^ k :=
      (MulAut.conj a⁻¹).toMonoidHom.map_zpow c k
    rw [show (MulAut.conj a⁻¹).toMonoidHom c = c⁻¹ by
      simpa [MulAut.conj_apply] using hac] at h1
    simpa [MulAut.conj_apply] using h1
  refine ⟨a, Subgroup.zpowers y, ha, haR, hP_le_K, ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_zpowers, hyord]
  · rw [hsup_eq]
    exact le_sup_right
  · have hc_cl : c ∈ Subgroup.closure ({a, x⁻¹ * a * x} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    exact (Subgroup.zpowers_le.mpr hyz).trans (Subgroup.zpowers_le.mpr hc_cl)
  · intro y' hy'
    have hy'c : y' ∈ Subgroup.zpowers c := (Subgroup.zpowers_le.mpr hyz) hy'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy'c
    rw [← hk]
    exact hpow k

end CFSG.LocalAnalysis.WeakClosure81
