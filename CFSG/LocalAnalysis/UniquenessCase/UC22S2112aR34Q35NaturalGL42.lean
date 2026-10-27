module

public import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35NaturalGL42Fix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural

variable {Γ : Type*} [Group Γ] [Finite Γ] {Z N : Subgroup Γ}

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩

private instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by decide⟩

private lemma orderOf_two_zmod_five : orderOf (2 : ZMod 5) = 4 :=
  (orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩

private lemma four_dvd_of_two_pow_modEq_one {j : ℕ} (h : 2 ^ j ≡ 1 [MOD 5]) : 4 ∣ j := by
  have hz : (2 : ZMod 5) ^ j = 1 := by
    have h' := (ZMod.natCast_eq_natCast_iff (2 ^ j) 1 5).mpr h
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using h'
  have hd := orderOf_dvd_of_pow_eq_one hz
  rwa [orderOf_two_zmod_five] at hd

private lemma le_of_pow_two_dvd_five_mul_pow {d k : ℕ} (h : 2 ^ d ∣ 5 * 2 ^ k) : d ≤ k := by
  have hcop : Nat.Coprime (2 ^ d) 5 :=
    Nat.Coprime.pow_left d (by norm_num : Nat.Coprime 2 5)
  have hdvd : 2 ^ d ∣ 2 ^ k := hcop.dvd_of_dvd_mul_left h
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdvd

private lemma isPGroup_two_N (hZ2 : IsPGroup 2 Z)
    (hcard : Nat.card N = 16 * Nat.card Z) : IsPGroup 2 N := by
  obtain ⟨a, ha⟩ := hZ2.exists_card_eq
  refine IsPGroup.of_card (p := 2) (n := a + 4) ?_
  calc Nat.card N = 16 * Nat.card Z := hcard
    _ = 16 * 2 ^ a := by rw [ha]
    _ = 2 ^ 4 * 2 ^ a := by norm_num
    _ = 2 ^ (4 + a) := by rw [pow_add]
    _ = 2 ^ (a + 4) := by congr 1; omega

private theorem card_sylow_five_eq_five [N.Normal] (hZN : Z ≤ N)
    (hZc : ∀ z ∈ Z, ∀ g : Γ, g * z = z * g) (hZ2 : IsPGroup 2 Z)
    (hcard : Nat.card N = 16 * Nat.card Z) (hsq : ∀ x ∈ N, x * x ∈ Z)
    (hker : ∀ g : Γ, (∀ x ∈ N, g * x * g⁻¹ * x⁻¹ ∈ Z) → g ∈ N)
    (h5 : 5 ∣ Nat.card Γ) (R : Sylow 5 Γ) : Nat.card (R : Subgroup Γ) = 5 := by
  have hdvd : Nat.card (R : Subgroup Γ) ∣ 5 :=
    card_dvd_five_of_isPGroup hZN hZc hZ2 hcard hsq hker R.isPGroup'
  have h5dvd : 5 ∣ Nat.card (R : Subgroup Γ) := Sylow.dvd_card_of_dvd_card R h5
  rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hdvd with h | h
  · rw [h] at h5dvd
    exact absurd h5dvd (by norm_num)
  · exact h

private theorem exists_index_eq_pow_two
    (hΓ : ∀ r : ℕ, r.Prime → r ∣ Nat.card Γ → r = 2 ∨ r = 5) (R : Sylow 5 Γ) :
    ∃ k : ℕ, (R : Subgroup Γ).index = 2 ^ k := by
  have hne : (R : Subgroup Γ).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  refine ⟨(R : Subgroup Γ).index.primeFactorsList.length,
    Nat.eq_prime_pow_of_unique_prime_dvd hne ?_⟩
  intro d hd hdvd
  have hdvdΓ : d ∣ Nat.card Γ := hdvd.trans (Subgroup.index_dvd_card _)
  rcases hΓ d hd hdvdΓ with rfl | rfl
  · rfl
  · exact absurd hdvd (Sylow.not_dvd_index R)



private theorem sylow_five_not_normal [N.Normal]
    (hker : ∀ g : Γ, (∀ x ∈ N, g * x * g⁻¹ * x⁻¹ ∈ Z) → g ∈ N)
    {R : Sylow 5 Γ} {c : Γ} (hR : (R : Subgroup Γ) = Subgroup.zpowers c)
    (hc : orderOf c = 5) (hN2 : IsPGroup 2 N)
    (hn5 : Nat.card (Sylow 5 Γ) = 1) : False := by
  have hindex : (Subgroup.normalizer (R : Set Γ)).index = 1 := by
    rw [← Sylow.card_eq_index_normalizer R]
    exact hn5
  have htop : Subgroup.normalizer (R : Set Γ) = ⊤ := Subgroup.index_eq_one.mp hindex
  have hRnormal : (R : Subgroup Γ).Normal := Subgroup.normalizer_eq_top_iff.mp htop
  have hcR : c ∈ (R : Subgroup Γ) := by
    rw [hR]
    exact Subgroup.mem_zpowers c
  have hinf : N ⊓ (R : Subgroup Γ) = ⊥ :=
    (IsPGroup.disjoint_of_ne 2 5 (by norm_num) N (R : Subgroup Γ) hN2 R.isPGroup').eq_bot
  have hcomm : ∀ x ∈ N, c * x = x * c := by
    intro x hx
    have hmemN : c * x * c⁻¹ * x⁻¹ ∈ N := by
      have h1 : c * x * c⁻¹ ∈ N := (inferInstance : N.Normal).conj_mem x hx c
      exact N.mul_mem h1 (N.inv_mem hx)
    have hmemR : c * x * c⁻¹ * x⁻¹ ∈ (R : Subgroup Γ) := by
      have h1 : x * c⁻¹ * x⁻¹ ∈ (R : Subgroup Γ) :=
        hRnormal.conj_mem c⁻¹ ((R : Subgroup Γ).inv_mem hcR) x
      have h2 : c * (x * c⁻¹ * x⁻¹) ∈ (R : Subgroup Γ) :=
        (R : Subgroup Γ).mul_mem hcR h1
      simpa only [mul_assoc] using h2
    have hbot : c * x * c⁻¹ * x⁻¹ ∈ (⊥ : Subgroup Γ) := by
      rw [← hinf]
      exact ⟨hmemN, hmemR⟩
    have h1 : c * x * c⁻¹ * x⁻¹ = 1 := Subgroup.mem_bot.mp hbot
    have h2 : (c * x) * (x * c)⁻¹ = 1 := by
      simpa only [mul_inv_rev, mul_assoc] using h1
    exact mul_inv_eq_one.mp h2
  have hcN : c ∈ N := hker c (fun x hx => by
    have h1 : c * x * c⁻¹ * x⁻¹ = 1 := by
      have h2 : (c * x) * (x * c)⁻¹ = 1 := mul_inv_eq_one.mpr (hcomm x hx)
      simpa only [mul_inv_rev, mul_assoc] using h2
    rw [h1]
    exact Z.one_mem)
  obtain ⟨m, hm⟩ := hN2.exists_orderOf_eq_pow (⟨c, hcN⟩ : N)
  have hord : orderOf (⟨c, hcN⟩ : N) = 5 := by
    rw [Subgroup.orderOf_mk, hc]
  have hdvd : 5 ∣ 2 ^ m := by
    rw [← hord, hm]
  have h25 : 5 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 5) hdvd
  norm_num at h25

private theorem card_centralizer_le [N.Normal] (hZN : Z ≤ N)
    (hZc : ∀ z ∈ Z, ∀ g : Γ, g * z = z * g) (hZ2 : IsPGroup 2 Z)
    (hcard : Nat.card N = 16 * Nat.card Z) (hsq : ∀ x ∈ N, x * x ∈ Z)
    (hker : ∀ g : Γ, (∀ x ∈ N, g * x * g⁻¹ * x⁻¹ ∈ Z) → g ∈ N)
    {c : Γ} (hc : orderOf c = 5) {k a : ℕ} (hk : Nat.card Γ = 5 * 2 ^ k)
    (ha : Nat.card Z = 2 ^ a) :
    Nat.card (Subgroup.centralizer ({c} : Set Γ)) ≤ 5 * 2 ^ a := by
  classical
  let C : Subgroup Γ := Subgroup.centralizer ({c} : Set Γ)
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := C)
  have hPZ : ((P : Subgroup C).map C.subtype) ≤ Z := by
    rintro _ ⟨p, hp, rfl⟩
    have hpC : (p : Γ) ∈ C := p.2
    have hpc : (p : Γ) * c = c * (p : Γ) := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp hpC
      simpa using h
    obtain ⟨m, hm⟩ := P.isPGroup' (⟨p, hp⟩ : P)
    have ht : ∃ m : ℕ, (p : Γ) ^ 2 ^ m = 1 :=
      ⟨m, by simpa using congrArg (fun x : P => (x : Γ)) hm⟩
    exact mem_of_commute_of_orderOf_five hZN hZc hZ2 hcard hsq hker hc ht hpc
  have hPcard : Nat.card (P : Subgroup C) ≤ 2 ^ a := by
    calc Nat.card (P : Subgroup C) = Nat.card ((P : Subgroup C).map C.subtype) :=
          (Subgroup.card_subtype C (P : Subgroup C)).symm
      _ ≤ Nat.card Z := Subgroup.card_le_of_le hPZ
      _ = 2 ^ a := ha
  have hm_dvd : (P : Subgroup C).index ∣ 5 * 2 ^ k := by
    have h1 : (P : Subgroup C).index ∣ Nat.card C := Subgroup.index_dvd_card _
    have h2 : Nat.card C ∣ Nat.card Γ := Subgroup.card_subgroup_dvd_card C
    have h3 : (P : Subgroup C).index ∣ Nat.card Γ := h1.trans h2
    rwa [hk] at h3
  have hm_odd : Odd (P : Subgroup C).index := by
    have h2 : ¬ 2 ∣ (P : Subgroup C).index := Sylow.not_dvd_index P
    have h2' : ¬ Even (P : Subgroup C).index := by rwa [even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mp h2'
  have hcop : Nat.Coprime (P : Subgroup C).index (2 ^ k) :=
    (Odd.coprime_two_right hm_odd).pow_right k
  have hm_dvd5 : (P : Subgroup C).index ∣ 5 :=
    hcop.dvd_of_dvd_mul_right hm_dvd
  have hm_le : (P : Subgroup C).index ≤ 5 := Nat.le_of_dvd (by norm_num) hm_dvd5
  calc Nat.card C = Nat.card (P : Subgroup C) * (P : Subgroup C).index :=
        (Subgroup.card_mul_index _).symm
    _ ≤ 2 ^ a * 5 := Nat.mul_le_mul hPcard hm_le
    _ = 5 * 2 ^ a := Nat.mul_comm _ _

private theorem card_normalizer_le {R : Sylow 5 Γ} {c : Γ}
    (hR : (R : Subgroup Γ) = Subgroup.zpowers c)
    (hRcard : Nat.card (R : Subgroup Γ) = 5) :
    Nat.card (Subgroup.normalizer (R : Set Γ)) ≤
      4 * Nat.card (Subgroup.centralizer ({c} : Set Γ)) := by
  classical
  let NΓR := Subgroup.normalizer (R : Set Γ)
  let C := Subgroup.centralizer ({c} : Set Γ)
  let φ : NΓR →* MulAut (R : Subgroup Γ) := (R : Subgroup Γ).normalizerMonoidHom
  have hCle : C ≤ Subgroup.centralizer ((R : Subgroup Γ) : Set Γ) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hgc : g * c = c * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hcz : c ∈ Subgroup.centralizer ({g} : Set Γ) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hgc.symm
    have hzp : Subgroup.zpowers c ≤ Subgroup.centralizer ({g} : Set Γ) :=
      Subgroup.zpowers_le.mpr hcz
    have hr' : r ∈ Subgroup.zpowers c := by rwa [hR] at hr
    exact Subgroup.mem_centralizer_singleton_iff.mp (hzp hr')
  have hCnorm : C ≤ NΓR := hCle.trans (Subgroup.centralizer_le_normalizer _)
  have hker : φ.ker = C.subgroupOf NΓR := by
    have hφ : φ = (R : Subgroup Γ).normalizerMonoidHom := rfl
    rw [hφ, Subgroup.normalizerMonoidHom_ker]
    congr 1
    rw [hR, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hcardker : Nat.card φ.ker = Nat.card C := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCnorm).toEquiv
  have hcyc : IsCyclic (R : Subgroup Γ) := by
    rw [hR]
    exact Subgroup.isCyclic_zpowers c
  have hMA : Nat.card (MulAut (R : Subgroup Γ)) = 4 := by
    rw [@IsCyclic.card_mulAut (R : Subgroup Γ) _ _ hcyc, hRcard,
      Nat.totient_prime (by decide : Nat.Prime 5)]
  have hrange : Nat.card φ.range ≤ 4 := by
    calc Nat.card φ.range ≤ Nat.card (MulAut (R : Subgroup Γ)) :=
          Subgroup.card_le_card_group φ.range
      _ = 4 := hMA
  calc Nat.card NΓR = Nat.card φ.ker * Nat.card φ.range :=
        (Subgroup.card_ker_mul_card_range φ).symm
    _ = Nat.card C * Nat.card φ.range := by rw [hcardker]
    _ ≤ Nat.card C * 4 := Nat.mul_le_mul_left _ hrange
    _ = 4 * Nat.card C := Nat.mul_comm _ _


open scoped IsMulCommutative in
private theorem exists_conj_sq_of_card_eq {R : Sylow 5 Γ} {c : Γ}
    (hR : (R : Subgroup Γ) = Subgroup.zpowers c)
    (hRcard : Nat.card (R : Subgroup Γ) = 5)
    (hN : Nat.card (Subgroup.normalizer (R : Set Γ)) =
      4 * Nat.card (Subgroup.centralizer ({c} : Set Γ))) :
    ∃ g : Γ, g * c * g⁻¹ = c ^ 2 := by
  classical
  let NΓR := Subgroup.normalizer (R : Set Γ)
  let C := Subgroup.centralizer ({c} : Set Γ)
  let φ : NΓR →* MulAut (R : Subgroup Γ) := (R : Subgroup Γ).normalizerMonoidHom
  have hCle : C ≤ Subgroup.centralizer ((R : Subgroup Γ) : Set Γ) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hgc : g * c = c * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hcz : c ∈ Subgroup.centralizer ({g} : Set Γ) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hgc.symm
    have hzp : Subgroup.zpowers c ≤ Subgroup.centralizer ({g} : Set Γ) :=
      Subgroup.zpowers_le.mpr hcz
    have hr' : r ∈ Subgroup.zpowers c := by rwa [hR] at hr
    exact Subgroup.mem_centralizer_singleton_iff.mp (hzp hr')
  have hCnorm : C ≤ NΓR := hCle.trans (Subgroup.centralizer_le_normalizer _)
  have hker : φ.ker = C.subgroupOf NΓR := by
    have hφ : φ = (R : Subgroup Γ).normalizerMonoidHom := rfl
    rw [hφ, Subgroup.normalizerMonoidHom_ker]
    congr 1
    rw [hR, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hcardker : Nat.card φ.ker = Nat.card C := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCnorm).toEquiv
  have hcyc : IsCyclic (R : Subgroup Γ) := by
    rw [hR]
    exact Subgroup.isCyclic_zpowers c
  have hRcomm : IsMulCommutative (R : Subgroup Γ) := by
    rw [hR]
    exact Subgroup.zpowers_isMulCommutative c
  have hMA : Nat.card (MulAut (R : Subgroup Γ)) = 4 := by
    rw [@IsCyclic.card_mulAut (R : Subgroup Γ) _ _ hcyc, hRcard,
      Nat.totient_prime (by decide : Nat.Prime 5)]
  have hrange4 : Nat.card φ.range = 4 := by
    have hN' : Nat.card NΓR = Nat.card φ.ker * Nat.card φ.range :=
      (Subgroup.card_ker_mul_card_range φ).symm
    rw [hcardker] at hN'
    have hEq : Nat.card C * Nat.card φ.range = Nat.card C * 4 := by
      rw [← hN', hN, Nat.mul_comm 4 (Nat.card C)]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hEq
  let sqEquiv : (R : Subgroup Γ) ≃ (R : Subgroup Γ) :=
    { toFun := fun x => x ^ 2
      invFun := fun x => x ^ 3
      left_inv := fun x => by
        change (x ^ 2) ^ 3 = x
        rw [← pow_mul]
        have hx5 : x ^ 5 = 1 := by
          have h := pow_card_eq_one' (x := x)
          rwa [hRcard] at h
        rw [show 2 * 3 = 5 + 1 by norm_num, pow_succ, hx5, one_mul]
      right_inv := fun x => by
        change (x ^ 3) ^ 2 = x
        rw [← pow_mul]
        have hx5 : x ^ 5 = 1 := by
          have h := pow_card_eq_one' (x := x)
          rwa [hRcard] at h
        rw [show 3 * 2 = 5 + 1 by norm_num, pow_succ, hx5, one_mul] }
  let sqAut : MulAut (R : Subgroup Γ) :=
    { toEquiv := sqEquiv
      map_mul' := fun x y => by
        change (x * y) ^ 2 = x ^ 2 * y ^ 2
        exact Commute.mul_pow
          ((IsMulCommutative.is_comm (M := (R : Subgroup Γ))).comm x y) 2 }
  have htop : φ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq (G := MulAut (R : Subgroup Γ))
    rw [hrange4, hMA]
  have hmem : sqAut ∈ φ.range := by
    rw [htop]
    exact Subgroup.mem_top sqAut
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hmem
  have hcR : c ∈ (R : Subgroup Γ) := by
    rw [hR]
    exact Subgroup.mem_zpowers c
  refine ⟨(g : Γ), ?_⟩
  have happ := Subgroup.normalizerMonoidHom_apply_apply_coe (R : Subgroup Γ) g ⟨c, hcR⟩
  rw [hg] at happ
  have hsq : ((sqAut ⟨c, hcR⟩ : R) : Γ) = c ^ 2 := by
    simp [sqAut, sqEquiv]
  rw [← hsq]
  exact happ.symm


private theorem common_bounds [N.Normal] (hZN : Z ≤ N)
    (hZc : ∀ z ∈ Z, ∀ g : Γ, g * z = z * g) (hZ2 : IsPGroup 2 Z)
    (hcard : Nat.card N = 16 * Nat.card Z) (hsq : ∀ x ∈ N, x * x ∈ Z)
    (hker : ∀ g : Γ, (∀ x ∈ N, g * x * g⁻¹ * x⁻¹ ∈ Z) → g ∈ N)
    (hΓ : ∀ r : ℕ, r.Prime → r ∣ Nat.card Γ → r = 2 ∨ r = 5) (h5 : 5 ∣ Nat.card Γ)
    (h16 : ¬ 16 * Nat.card N ∣ Nat.card Γ) :
    ∃ (R : Sylow 5 Γ) (c : Γ) (k a : ℕ),
      (R : Subgroup Γ) = Subgroup.zpowers c ∧ orderOf c = 5 ∧
      Nat.card Γ = 5 * 2 ^ k ∧ Nat.card Z = 2 ^ a ∧
      Nat.card (Sylow 5 Γ) = 16 ∧ k ≤ a + 6 ∧
      Nat.card (Subgroup.normalizer (R : Set Γ)) * 16 = Nat.card Γ ∧
      Nat.card (Subgroup.normalizer (R : Set Γ)) ≤
        4 * Nat.card (Subgroup.centralizer ({c} : Set Γ)) ∧
      Nat.card (Subgroup.centralizer ({c} : Set Γ)) ≤ 5 * 2 ^ a := by
  classical
  obtain ⟨R⟩ := Sylow.nonempty (p := 5) (G := Γ)
  have hRcard : Nat.card (R : Subgroup Γ) = 5 :=
    card_sylow_five_eq_five hZN hZc hZ2 hcard hsq hker h5 R
  have hcyc : IsCyclic (R : Subgroup Γ) := isCyclic_of_prime_card hRcard
  obtain ⟨cR, hcRord⟩ :=
    @IsCyclic.exists_ofOrder_eq_natCard (R : Subgroup Γ) _ hcyc
  let c : Γ := cR
  have hc : orderOf c = 5 := by
    dsimp [c]
    rw [Subgroup.orderOf_coe, hcRord, hRcard]
  have hcR : c ∈ (R : Subgroup Γ) := cR.2
  have hR : (R : Subgroup Γ) = Subgroup.zpowers c := by
    symm
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · exact Subgroup.zpowers_le.mpr hcR
    · rw [Nat.card_zpowers, hc, hRcard]
  obtain ⟨k, hkidx⟩ := exists_index_eq_pow_two hΓ R
  have hk : Nat.card Γ = 5 * 2 ^ k := by
    have h := Subgroup.card_mul_index (R : Subgroup Γ)
    rw [hRcard, hkidx] at h
    exact h.symm
  obtain ⟨a, ha⟩ := hZ2.exists_card_eq
  have hN2 : IsPGroup 2 N := isPGroup_two_N hZ2 hcard
  have h16' : ¬ 2 ^ (a + 8) ∣ 5 * 2 ^ k := by
    have hpow : 16 * Nat.card N = 2 ^ (a + 8) := by
      calc 16 * Nat.card N = 16 * (16 * Nat.card Z) := by rw [hcard]
        _ = 16 * (16 * 2 ^ a) := by rw [ha]
        _ = 2 ^ (a + 8) := by
          rw [show (16:ℕ) = 2 ^ 4 by norm_num]
          rw [← pow_add, ← pow_add]
          congr 1
          omega
    rw [hpow, hk] at h16
    exact h16
  have hk_le_a7 : k ≤ a + 7 := by
    by_contra h
    have hle : a + 8 ≤ k := by omega
    apply h16'
    exact (Nat.pow_dvd_pow 2 hle).trans (dvd_mul_left _ _)
  have hdvd : Nat.card (Sylow 5 Γ) ∣ 2 ^ k := by
    rw [← hkidx]
    exact Sylow.card_dvd_index R
  obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp hdvd
  have hmod : 2 ^ j ≡ 1 [MOD 5] := by
    have := card_sylow_modEq_one (p := 5) (G := Γ)
    rwa [hj] at this
  have h4j : 4 ∣ j := four_dvd_of_two_pow_modEq_one hmod
  have hjnz : j ≠ 0 := by
    intro hj0
    apply sylow_five_not_normal hker hR hc hN2
    rw [hj, hj0, pow_zero]
  have hj4 : 4 ≤ j := Nat.le_of_dvd (Nat.pos_of_ne_zero hjnz) h4j
  have hZnorm : Z ≤ Subgroup.normalizer (R : Set Γ) := by
    have hZcent : Z ≤ Subgroup.centralizer ((R : Subgroup Γ) : Set Γ) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro r _
      exact hZc z hz r
    exact hZcent.trans (Subgroup.centralizer_le_normalizer _)
  have hdisj : Disjoint (R : Subgroup Γ) Z :=
    (IsPGroup.disjoint_of_ne 2 5 (by norm_num) Z (R : Subgroup Γ) hZ2 R.isPGroup').symm
  have hZRcard : Nat.card ↥((R : Subgroup Γ) ⊔ Z) = 5 * 2 ^ a := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (A := (R : Subgroup Γ)) (B := Z) hZnorm hdisj, hRcard, ha]
  have hZRle : ((R : Subgroup Γ) ⊔ Z) ≤ Subgroup.normalizer (R : Set Γ) :=
    sup_le Subgroup.le_normalizer hZnorm
  have hn5_eq_index : Nat.card (Sylow 5 Γ) =
      (Subgroup.normalizer (R : Set Γ)).index := Sylow.card_eq_index_normalizer R
  have hNΓ_mul : Nat.card (Subgroup.normalizer (R : Set Γ)) *
      Nat.card (Sylow 5 Γ) = Nat.card Γ := by
    rw [hn5_eq_index, Subgroup.card_mul_index]
  have hbig : (5 * 2 ^ a) * 2 ^ j ≤ 5 * 2 ^ k := by
    calc (5 * 2 ^ a) * 2 ^ j
        = Nat.card ↥((R : Subgroup Γ) ⊔ Z) * Nat.card (Sylow 5 Γ) := by rw [hZRcard, hj]
      _ ≤ Nat.card (Subgroup.normalizer (R : Set Γ)) * Nat.card (Sylow 5 Γ) :=
          Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hZRle)
      _ = Nat.card Γ := hNΓ_mul
      _ = 5 * 2 ^ k := hk
  have hbig' : 2 ^ a * 2 ^ j ≤ 2 ^ k := by
    have h' := hbig
    rw [mul_assoc] at h'
    exact Nat.le_of_mul_le_mul_left h' (by norm_num)
  have haj : a + j ≤ k := by
    have h3 : 2 ^ (a + j) ≤ 2 ^ k := by
      rw [pow_add]
      exact hbig'
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h3
  have hj7 : j ≤ 7 := by omega
  have hj4' : j = 4 := by
    rcases h4j with ⟨t, ht⟩
    have ht1 : t = 1 := by omega
    omega
  have hn5 : Nat.card (Sylow 5 Γ) = 16 := by
    rw [hj, hj4']
    norm_num
  have hNle : Nat.card (Subgroup.normalizer (R : Set Γ)) ≤
      4 * Nat.card (Subgroup.centralizer ({c} : Set Γ)) := card_normalizer_le hR hRcard
  have hCle : Nat.card (Subgroup.centralizer ({c} : Set Γ)) ≤ 5 * 2 ^ a :=
    card_centralizer_le hZN hZc hZ2 hcard hsq hker hc hk ha
  have hN16 : Nat.card (Subgroup.normalizer (R : Set Γ)) * 16 = Nat.card Γ := by
    rw [← hn5]
    exact hNΓ_mul
  have hk_le : k ≤ a + 6 := by
    have hle1 : 5 * 2 ^ k ≤
        (4 * Nat.card (Subgroup.centralizer ({c} : Set Γ))) * 16 := by
      rw [← hk, ← hN16]
      exact Nat.mul_le_mul_right 16 hNle
    have hle2 : (4 * Nat.card (Subgroup.centralizer ({c} : Set Γ))) * 16 ≤
        5 * 2 ^ (a + 6) := by
      calc (4 * Nat.card (Subgroup.centralizer ({c} : Set Γ))) * 16 ≤
            (4 * (5 * 2 ^ a)) * 16 :=
            Nat.mul_le_mul_right 16 (Nat.mul_le_mul_left 4 hCle)
        _ = 5 * 2 ^ (a + 6) := by
            rw [show (2:ℕ) ^ (a + 6) = 2 ^ a * 2 ^ 6 by rw [pow_add]]
            ring
    have h5le : 5 * 2 ^ k ≤ 5 * 2 ^ (a + 6) := hle1.trans hle2
    have h3 : 2 ^ k ≤ 2 ^ (a + 6) := Nat.le_of_mul_le_mul_left h5le (by norm_num)
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h3
  exact ⟨R, c, k, a, hR, hc, hk, ha, hn5, hk_le, hN16, hNle, hCle⟩

theorem not_eight_mul_dvd_card [N.Normal] (hZN : Z ≤ N)
    (hZc : ∀ z ∈ Z, ∀ g : Γ, g * z = z * g) (hZ2 : IsPGroup 2 Z)
    (hcard : Nat.card N = 16 * Nat.card Z) (hsq : ∀ x ∈ N, x * x ∈ Z)
    (hker : ∀ g : Γ, (∀ x ∈ N, g * x * g⁻¹ * x⁻¹ ∈ Z) → g ∈ N)
    (hΓ : ∀ r : ℕ, r.Prime → r ∣ Nat.card Γ → r = 2 ∨ r = 5) (h5 : 5 ∣ Nat.card Γ)
    (h16 : ¬ 16 * Nat.card N ∣ Nat.card Γ) : ¬ 8 * Nat.card N ∣ Nat.card Γ := by
  obtain ⟨R, c, k, a, hR, hc, hk, ha, hn5, hk_le, hN16, hNle, hCle⟩ :=
    common_bounds hZN hZc hZ2 hcard hsq hker hΓ h5 h16
  intro h8
  have hpow : 8 * Nat.card N = 2 ^ (a + 7) := by
    calc 8 * Nat.card N = 8 * (16 * Nat.card Z) := by rw [hcard]
      _ = 8 * (16 * 2 ^ a) := by rw [ha]
      _ = 2 ^ (a + 7) := by
        rw [show (8:ℕ) = 2 ^ 3 by norm_num, show (16:ℕ) = 2 ^ 4 by norm_num]
        rw [← pow_add, ← pow_add]
        congr 1
        omega
  have h8' : 2 ^ (a + 7) ∣ 5 * 2 ^ k := by
    have h := h8
    rw [hk] at h
    rwa [← hpow]
  have hle : a + 7 ≤ k := le_of_pow_two_dvd_five_mul_pow h8'
  omega

theorem exists_conj_eq_sq [N.Normal] (hZN : Z ≤ N)
    (hZc : ∀ z ∈ Z, ∀ g : Γ, g * z = z * g) (hZ2 : IsPGroup 2 Z)
    (hcard : Nat.card N = 16 * Nat.card Z) (hsq : ∀ x ∈ N, x * x ∈ Z)
    (hker : ∀ g : Γ, (∀ x ∈ N, g * x * g⁻¹ * x⁻¹ ∈ Z) → g ∈ N)
    (hΓ : ∀ r : ℕ, r.Prime → r ∣ Nat.card Γ → r = 2 ∨ r = 5) (h5 : 5 ∣ Nat.card Γ)
    (h16 : ¬ 16 * Nat.card N ∣ Nat.card Γ) (h4 : 4 * Nat.card N ∣ Nat.card Γ) :
    ∃ c g : Γ, orderOf c = 5 ∧ g * c * g⁻¹ * (c ^ 2)⁻¹ ∈ N := by
  obtain ⟨R, c, k, a, hR, hc, hk, ha, hn5, hk_le, hN16, hNle, hCle⟩ :=
    common_bounds hZN hZc hZ2 hcard hsq hker hΓ h5 h16
  have hpow : 4 * Nat.card N = 2 ^ (a + 6) := by
    calc 4 * Nat.card N = 4 * (16 * Nat.card Z) := by rw [hcard]
      _ = 4 * (16 * 2 ^ a) := by rw [ha]
      _ = 2 ^ (a + 6) := by
        rw [show (4:ℕ) = 2 ^ 2 by norm_num, show (16:ℕ) = 2 ^ 4 by norm_num]
        rw [← pow_add, ← pow_add]
        congr 1
        omega
  have h4' : 2 ^ (a + 6) ∣ 5 * 2 ^ k := by
    have h := h4
    rw [hk] at h
    rwa [← hpow]
  have ha6 : a + 6 ≤ k := le_of_pow_two_dvd_five_mul_pow h4'
  have hkeq : k = a + 6 := le_antisymm hk_le ha6
  have hΓcard : Nat.card Γ = 5 * 2 ^ (a + 6) := by rw [hk, hkeq]
  have hNΓcard : Nat.card (Subgroup.normalizer (R : Set Γ)) = 5 * 2 ^ (a + 2) := by
    have h := hN16
    rw [hΓcard] at h
    have hpow16 : 5 * 2 ^ (a + 6) = (5 * 2 ^ (a + 2)) * 16 := by
      rw [show a + 6 = (a + 2) + 4 by omega, pow_add]
      norm_num
      ring
    rw [hpow16] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 16) h
  have hCcard : Nat.card (Subgroup.centralizer ({c} : Set Γ)) = 5 * 2 ^ a := by
    have hCge : 5 * 2 ^ a ≤ Nat.card (Subgroup.centralizer ({c} : Set Γ)) := by
      refine Nat.le_of_mul_le_mul_left ?_ (by norm_num : 0 < 4)
      calc 4 * (5 * 2 ^ a) = Nat.card (Subgroup.normalizer (R : Set Γ)) := by
            rw [hNΓcard]
            rw [pow_add]
            norm_num
            ring
        _ ≤ 4 * Nat.card (Subgroup.centralizer ({c} : Set Γ)) := hNle
    exact le_antisymm hCle hCge
  have hNΓ4 : Nat.card (Subgroup.normalizer (R : Set Γ)) =
      4 * Nat.card (Subgroup.centralizer ({c} : Set Γ)) := by
    rw [hNΓcard, hCcard]
    rw [pow_add]
    norm_num
    ring
  obtain ⟨g, hg⟩ := exists_conj_sq_of_card_eq hR (by rw [hR, Nat.card_zpowers, hc]) hNΓ4
  refine ⟨c, g, hc, ?_⟩
  rw [hg]
  simp

end CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural
