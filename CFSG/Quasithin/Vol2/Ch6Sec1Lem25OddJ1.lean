module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25OddA
import CFSG.Walter.Models
import CFSG.Walter.J1Props.Aut

public section

namespace CFSG.Quasithin.H13.OddSyl

open CFSG.QuasithinUnique CFSG.Quasithin

theorem central_map {S M : Type} [Group S] [Group M] (φ : S ≃* M) {P : Subgroup S}
    {R : Subgroup M} (hPR : ∀ x, x ∈ R ↔ φ.symm x ∈ P) {g : S}
    (hg : g ∈ Subgroup.normalizer (P : Set S))
    (hc : ∀ y ∈ Subgroup.normalizer (P : Set S), g * y * g⁻¹ * y⁻¹ ∈ P) :
    φ g ∈ Subgroup.normalizer (R : Set M) ∧
      ∀ y ∈ Subgroup.normalizer (R : Set M), φ g * y * (φ g)⁻¹ * y⁻¹ ∈ R := by
  have hN : ∀ y, y ∈ Subgroup.normalizer (R : Set M) →
      φ.symm y ∈ Subgroup.normalizer (P : Set S) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff] at hy ⊢
    intro h
    have h1 := hy (φ h)
    rw [hPR, hPR] at h1
    simpa using h1
  have hgR : φ g ∈ Subgroup.normalizer (R : Set M) := by
    rw [Subgroup.mem_normalizer_iff] at hg ⊢
    intro h
    rw [hPR, hPR, hg (φ.symm h)]
    simp
  refine ⟨hgR, fun y hy => ?_⟩
  rw [hPR]
  simpa using hc _ (hN y hy)

open CFSG.Walter.J1Props CFSG.Walter.J1Recog CFSG.Open
open scoped Pointwise

private theorem walterJ1_eq_one_of_mem_S₀_zpowers {x : walterJ1} (h1 : x ∈ S₀)
    (h2 : x ∈ Subgroup.zpowers nJ) : x = 1 := by
  have h7 : orderOf nJ = 7 := orderOf_yJ (p := 7) (by norm_num)
  have ha : orderOf x ∣ 8 := card_S₀ ▸ Subgroup.orderOf_dvd_natCard _ h1
  have hb : orderOf x ∣ 7 := by
    have h := Subgroup.orderOf_dvd_natCard _ h2
    rwa [Nat.card_zpowers, h7] at h
  have h := Nat.dvd_gcd ha hb
  rw [show Nat.gcd 8 7 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at h
  exact h

private theorem walterJ1_eq_one_of_mem_S₀_of_odd {x : walterJ1} (hx : x ∈ S₀)
    (hodd : Odd (orderOf x)) : x = 1 := by
  have h8 : orderOf x ∣ 2 ^ 3 := by
    have h := Subgroup.orderOf_dvd_natCard _ hx
    rw [card_S₀] at h
    norm_num
    exact h
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h8
  rcases i with _ | i
  · rw [pow_zero] at hi
    exact orderOf_eq_one_iff.1 hi
  · exfalso
    obtain ⟨m, hm⟩ := hodd
    rw [hi, pow_succ] at hm
    omega

private theorem walterJ1_eq_one_of_central {g : walterJ1}
    (hg : g ∈ Subgroup.normalizer (S₀ : Set walterJ1)) (hodd : Odd (orderOf g))
    (hc : ∀ y ∈ Subgroup.normalizer (S₀ : Set walterJ1), g * y * g⁻¹ * y⁻¹ ∈ S₀) : g = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, hmn2, hm3, hmn4, -, -⟩ := rels_aut
  have h7 : orderOf nJ = 7 := orderOf_yJ (p := 7) (by norm_num)
  have h3 : orderOf mJ = 3 := orderOf_yJ (p := 3) (by norm_num)
  set N := Subgroup.normalizer (S₀ : Set walterJ1) with hNdef
  set K := (S₀ ⊔ Subgroup.zpowers nJ : Subgroup walterJ1) with hKdef
  have hN : Nat.card N = 168 := jankoHyp.card_normalizer_sylow sylowS₀ t_mem_sylowS₀
  have hKN : K ≤ N := sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr nJ_mem_normalizer)
  have hmK : Subgroup.zpowers mJ ≤ Subgroup.normalizer (K : Set walterJ1) :=
    Subgroup.zpowers_le.mpr mJ_mem_normalizer_K
  have hKm : Nat.card (K ⊔ Subgroup.zpowers mJ : Subgroup walterJ1) = 168 := by
    rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hmK, card_K,
      Nat.card_zpowers, h3]
    rw [Subgroup.disjoint_def]
    intro y hyK hym
    have h1 : orderOf y ∣ 56 := card_K ▸ Subgroup.orderOf_dvd_natCard _ hyK
    have h2 : orderOf y ∣ 3 := by
      have h := Subgroup.orderOf_dvd_natCard _ hym
      rwa [Nat.card_zpowers, h3] at h
    have h := Nat.dvd_gcd h1 h2
    rw [show Nat.gcd 56 3 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at h
    exact h
  have hNeq : K ⊔ Subgroup.zpowers mJ = N :=
    Subgroup.eq_of_le_of_card_ge (sup_le hKN (Subgroup.zpowers_le.mpr mJ_mem_normalizer))
      (by rw [hN, hKm])
  have hgKm : g ∈ (K : Set walterJ1) * (Subgroup.zpowers mJ : Set walterJ1) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hmK, hNeq]
    exact hg
  obtain ⟨k, hk, z, ⟨b, rfl⟩, rfl⟩ := Set.mem_mul.mp hgKm
  obtain ⟨s, hs, a, rfl⟩ := mem_K_iff.mp hk
  have hmod : mJ ^ (b % 3) = mJ ^ b := by
    have h := zpow_mod_orderOf mJ b
    rwa [h3, Nat.cast_ofNat] at h
  have hn7 : ∀ j : ℕ, 0 < j → j < 7 → nJ ^ j ∉ S₀ := by
    intro j hj0 hj7 hj
    have h1 := walterJ1_eq_one_of_mem_S₀_zpowers hj (Subgroup.pow_mem _ (Subgroup.mem_zpowers nJ) j)
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [h7] at h2
    have h3' := Nat.le_of_dvd hj0 h2
    omega
  have hb3 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
  rcases hb3 with hb | hb | hb
  ·
    have hgeq : s * nJ ^ a * mJ ^ b = s * nJ ^ a := by
      rw [← hmod, hb, zpow_zero, mul_one]
    rw [hgeq] at hodd hc ⊢
    have hB := hc mJ mJ_mem_normalizer
    have hs'' : mJ * s⁻¹ * mJ⁻¹ ∈ S₀ :=
      (Subgroup.mem_normalizer_iff.mp mJ_mem_normalizer s⁻¹).mp (S₀.inv_mem hs)
    have hconj : mJ * nJ ^ (-a) * mJ⁻¹ = (nJ ^ 4) ^ (-a) := by rw [← conj_zpow, hmn4]
    have hx : nJ ^ a * (nJ ^ 4) ^ (-a) ∈ S₀ := by
      have h := S₀.mul_mem (S₀.mul_mem (S₀.inv_mem hs) hB) (S₀.inv_mem hs'')
      have heq : s⁻¹ * (s * nJ ^ a * mJ * (s * nJ ^ a)⁻¹ * mJ⁻¹) * (mJ * s⁻¹ * mJ⁻¹)⁻¹ =
          nJ ^ a * (nJ ^ 4) ^ (-a) := by
        rw [← hconj]
        group
      rwa [heq] at h
    have hx1 := walterJ1_eq_one_of_mem_S₀_zpowers hx (Subgroup.mul_mem _
      (Subgroup.zpow_mem_zpowers nJ a)
      (Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers nJ) 4) (-a)))
    have hx2 : nJ ^ (a + 4 * -a) = 1 := by
      rw [zpow_add, zpow_mul, zpow_ofNat]
      exact hx1
    have h7a : ((orderOf nJ : ℕ) : ℤ) ∣ a := by
      have h := orderOf_dvd_iff_zpow_eq_one.mpr hx2
      rw [h7] at h ⊢
      push_cast at h ⊢
      omega
    rw [orderOf_dvd_iff_zpow_eq_one.mp h7a, mul_one] at hodd ⊢
    exact walterJ1_eq_one_of_mem_S₀_of_odd hs hodd
  ·
    exfalso
    have hgeq : s * nJ ^ a * mJ ^ b = s * nJ ^ a * mJ := by
      rw [← hmod, hb, zpow_one]
    rw [hgeq] at hc
    have hA := hc nJ nJ_mem_normalizer
    have hw : nJ ^ 4 * s⁻¹ * (nJ ^ 4)⁻¹ ∈ S₀ :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ nJ_mem_normalizer 4) s⁻¹).mp
        (S₀.inv_mem hs)
    apply hn7 3 (by norm_num) (by norm_num)
    have h := S₀.mul_mem (S₀.mul_mem (S₀.inv_mem hw) (S₀.inv_mem hs)) hA
    have heq : (nJ ^ 4 * s⁻¹ * (nJ ^ 4)⁻¹)⁻¹ * s⁻¹ *
        (s * nJ ^ a * mJ * nJ * (s * nJ ^ a * mJ)⁻¹ * nJ⁻¹) = nJ ^ 3 := by
      calc _ = nJ ^ 4 * s * (nJ ^ 4)⁻¹ * nJ ^ a * (mJ * nJ * mJ⁻¹) * nJ ^ (-a) * s⁻¹ *
            nJ⁻¹ := by group
        _ = nJ ^ 4 * s * (nJ ^ 4)⁻¹ * nJ ^ a * nJ ^ 4 * nJ ^ (-a) * s⁻¹ * nJ⁻¹ := by rw [hmn4]
        _ = nJ ^ 3 := by group
    rwa [heq] at h
  ·
    exfalso
    have hm2 : mJ ^ (2 : ℤ) = mJ⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← zpow_add_one, show (2 : ℤ) + 1 = 3 by norm_num, zpow_ofNat,
        hm3]
    have hgeq : s * nJ ^ a * mJ ^ b = s * nJ ^ a * mJ⁻¹ := by
      rw [← hmod, hb, hm2]
    rw [hgeq] at hc
    have hA := hc nJ nJ_mem_normalizer
    have hw : nJ ^ 2 * s⁻¹ * (nJ ^ 2)⁻¹ ∈ S₀ :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ nJ_mem_normalizer 2) s⁻¹).mp
        (S₀.inv_mem hs)
    apply hn7 1 (by norm_num) (by norm_num)
    have h := S₀.mul_mem (S₀.mul_mem (S₀.inv_mem hw) (S₀.inv_mem hs)) hA
    have heq : (nJ ^ 2 * s⁻¹ * (nJ ^ 2)⁻¹)⁻¹ * s⁻¹ *
        (s * nJ ^ a * mJ⁻¹ * nJ * (s * nJ ^ a * mJ⁻¹)⁻¹ * nJ⁻¹) = nJ ^ 1 := by
      calc _ = nJ ^ 2 * s * (nJ ^ 2)⁻¹ * nJ ^ a * (mJ⁻¹ * nJ * mJ) * nJ ^ (-a) * s⁻¹ *
            nJ⁻¹ := by group
        _ = nJ ^ 2 * s * (nJ ^ 2)⁻¹ * nJ ^ a * nJ ^ 2 * nJ ^ (-a) * s⁻¹ * nJ⁻¹ := by rw [hmn2]
        _ = nJ ^ 1 := by group
    rwa [heq] at h

private theorem walterJ1_eq_one_of_central_of_mulEquiv {S : Type}
    [Group S] (ψ : S ≃* walterJ1) {P : Subgroup S} (hP : IsSylowTwoOf P ⊤) {g : S}
    (hg : g ∈ Subgroup.normalizer (P : Set S)) (hodd : Odd (orderOf g))
    (hc : ∀ y ∈ Subgroup.normalizer (P : Set S), g * y * g⁻¹ * y⁻¹ ∈ P) : g = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := P.map ψ.toMonoidHom with hQ
  have hQp : IsPGroup 2 Q := hP.2.1.map _
  have hidx : ¬ 2 ∣ Q.index := by
    have hker : ψ.toMonoidHom.ker ≤ P := by
      rw [(MonoidHom.ker_eq_bot_iff _).mpr ψ.injective]
      exact bot_le
    rw [hQ, Subgroup.index_map_eq P (f := ψ.toMonoidHom) ψ.surjective hker,
      ← Subgroup.relIndex_top_right]
    exact hP.2.2
  obtain ⟨c, hc'⟩ := MulAction.exists_smul_eq walterJ1 (hQp.toSylow hidx) sylowS₀
  have hmem : ∀ x : walterJ1, x ∈ S₀ ↔ (ψ.trans (MulAut.conj c)).symm x ∈ P := by
    intro x
    have h1 : x ∈ ((c • hQp.toSylow hidx : Sylow 2 walterJ1) : Subgroup walterJ1) ↔ x ∈ S₀ := by
      rw [hc']
      exact Iff.rfl
    rw [← h1, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.conj_inv_apply, IsPGroup.toSylow_coe, hQ, Subgroup.mem_map_equiv]
    rfl
  obtain ⟨hN, hC⟩ := central_map (ψ.trans (MulAut.conj c)) hmem hg hc
  have h1 := walterJ1_eq_one_of_central hN (by rwa [MulEquiv.orderOf_eq]) hC
  exact (map_eq_one_iff _ (ψ.trans (MulAut.conj c)).injective).1 h1

theorem oddSylowJ1_holds : OddSylowJ1 := by
  intro S _ _ hS hna hJ P hP d r hr hr2 hd hdP hx hcent
  obtain ⟨e⟩ := hJ
  let ψ : S ≃* walterJ1 := e.trans CFSG.Walter.walterJ1EquivNative.symm
  have hinj := conj_injective hS hna
  have hinn : d ∈ innAut S := by
    obtain ⟨g, hg⟩ := J3_aut (MulAut.congr ψ d)
    refine ⟨ψ.symm g, MulEquiv.ext fun x => ?_⟩
    have h1 : ψ (d x) = g * ψ x * g⁻¹ := by
      have h := DFunLike.congr_fun hg (ψ x)
      simpa [MulAut.congr_apply] using h
    rw [MulAut.conj_apply]
    apply ψ.injective
    rw [h1]
    simp
  obtain ⟨g, hgN, rfl, hgo⟩ := exists_conj_of_mem_innAut hinj hd hdP hinn
  have hodd : Odd (orderOf g) := by
    rw [hgo]
    exact hr.odd_of_ne_two hr2
  have hg1 := walterJ1_eq_one_of_central_of_mulEquiv ψ hP hgN hodd fun y hy => by
    simpa [MulAut.conj_apply] using hcent y hy
  obtain ⟨x, -, hx⟩ := hx
  apply hx
  rw [hg1, map_one]
  rfl

end CFSG.Quasithin.H13.OddSyl
