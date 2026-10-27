module

public import CFSG.Quasithin.H13.A6S13821y
public import CFSG.Quasithin.H13.A6S13821h

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem X13820_of_hat (hhat : IsHatA6 L) : S.X13820 = l1plus T L V := by
  rw [Setting4.X13820, if_pos hhat]

theorem X13820_of_not_hat (hhat : ¬ IsHatA6 L) : S.X13820 = S.L1 := by
  rw [Setting4.X13820, if_neg hhat]
  rfl

theorem plusData_X13820 : S14.PlusData S S.X13820 := by
  by_cases hhat : IsHatA6 L
  · rw [S.X13820_of_hat hhat]
    exact S14.plusData_l1plus S (S.hatL1Plus hhat)
  · rw [S.X13820_of_not_hat hhat]
    exact S14.plusData_L1 S hhat

theorem K4pre_le_pCoreOf {H : Subgroup G} (hH : H ∈ S.Hz)
    (hHX : H ≤ Subgroup.normalizer (S.X13820 : Set G)) :
    S14.K4pre S S.X13820 ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := S.X13820 with hXdef
  have P := S.plusData_X13820
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hXH : X ≤ H := P.le_L1.trans hL1H
  set N := S14.K4pre S X with hN
  have hNX : N ≤ X := inf_le_left
  have hN2 : IsPGroup 2 N := by
    rintro ⟨k, hk⟩
    obtain ⟨hkX, hkV, hkK⟩ := S14.mem_K4pre.mp hk
    have h2 : S.frame.ρ (⟨k, hkV⟩ ^ 2) = 1 := by
      rw [map_pow, sq]
      exact K4L_sq _ hkK
    have hkC : (k : G) ^ 2 ∈ Subgroup.centralizer (V : Set G) := by
      have := (S.rho_eq_one_iff _).1 h2
      simpa using this
    have hkO := P.cent ⟨X.pow_mem hkX 2, hkC⟩
    obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 L ⟨_, hkO⟩
    have hm' : (k ^ 2) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    refine ⟨m + 1, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [pow_succ', pow_mul, hm']
  have hXN : X ≤ Subgroup.normalizer (N : Set G) := by
    intro x hx
    have hxV : x ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le (S.L1_le_L (P.le_L1 hx))
    obtain ⟨h4, h5, hs⟩ := S.rho_L1 (g := ⟨x, hxV⟩) (P.le_L1 hx)
    have hconj := (a4At_all (S.frame.ρ ⟨x, hxV⟩) h4 h5 hs).2
    have key : ∀ y ∈ X, y ∈ Subgroup.normalizer (V : Set G) →
        ∀ k ∈ N, y * k * y⁻¹ ∈ N := by
      intro y hy hyV k hk
      obtain ⟨hkX, hkV, hkK⟩ := S14.mem_K4pre.mp hk
      obtain ⟨y4, y5, ys⟩ := S.rho_L1 (g := ⟨y, hyV⟩) (P.le_L1 hy)
      refine S14.mem_K4pre.mpr ⟨X.mul_mem (X.mul_mem hy hkX) (X.inv_mem hy),
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hyV hkV) (Subgroup.inv_mem _ hyV), ?_⟩
      have e : (⟨y * k * y⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hyV hkV)
          (Subgroup.inv_mem _ hyV)⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          ⟨y, hyV⟩ * ⟨k, hkV⟩ * ⟨y, hyV⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      exact (a4At_all _ y4 y5 ys).2 _ hkK
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨fun hk => key x hx hxV k hk, fun hk => ?_⟩
    have h1 := key x⁻¹ (X.inv_mem hx) (Subgroup.inv_mem _ hxV) _ hk
    rwa [show x⁻¹ * (x * k * x⁻¹) * x⁻¹⁻¹ = k by group] at h1
  have hNO : N ≤ pCoreOf 2 X := le_pCoreOf_of_le_normalizer 2 hNX hXN hN2
  have hchar : (CFSG.Open.pCore 2 ↥X).Characteristic := by
    infer_instance
  have hHO : H ≤ Subgroup.normalizer ((pCoreOf 2 X : Subgroup G) : Set G) :=
    hHX.trans (normalizer_le_normalizer_map_of_characteristic (CFSG.Open.pCore 2 ↥X))
  exact hNO.trans (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 X).trans hXH) hHO
    (pCoreOf_isPGroup 2 X))

theorem mem_pCoreOf_or_of_X {H : Subgroup G} (hH : H ∈ S.Hz)
    (hHX : H ≤ Subgroup.normalizer (S.X13820 : Set G)) {c : ↥(Subgroup.normalizer (V : Set G))}
    (hcX : (c : G) ∈ S.X13820) (hρc : S.frame.ρ c = swap 0 1 * swap 1 2)
    (hc3 : (c : G) ^ 3 = 1) {y : G} (hyX : y ∈ S.X13820) :
    y ∈ pCoreOf 2 H ∨ y * (c : G)⁻¹ ∈ pCoreOf 2 H ∨ y * (c : G) ∈ pCoreOf 2 H := by
  set X := S.X13820 with hXdef
  have P := S.plusData_X13820
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hXH : X ≤ H := P.le_L1.trans hL1H
  have hNQ := S.K4pre_le_pCoreOf hH hHX
  have hcH : (c : G) ∈ H := hXH hcX
  have hyV : y ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le (S.L1_le_L (P.le_L1 hyX))
  obtain ⟨y4, y5, ys⟩ := S.rho_L1 (g := ⟨y, hyV⟩) (P.le_L1 hyX)
  have hcV : ((c : G)) ∈ Subgroup.normalizer (V : Set G) := c.2
  rcases (a4At_all (S.frame.ρ ⟨y, hyV⟩) y4 y5 ys).1 with h1 | h1 | h1
  · exact Or.inl (hNQ (S14.mem_K4pre.mpr ⟨hyX, hyV, h1⟩))
  ·
    right; left
    have hm : (c : G) * c * y ∈ S14.K4pre S X := by
      refine S14.mem_K4pre.mpr ⟨X.mul_mem (X.mul_mem hcX hcX) hyX,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hcV hcV) hyV, ?_⟩
      have e : (⟨(c : G) * c * y, Subgroup.mul_mem _ (Subgroup.mul_mem _ hcV hcV) hyV⟩ :
          ↥(Subgroup.normalizer (V : Set G))) = c * c * ⟨y, hyV⟩ := rfl
      rw [e, map_mul, map_mul, hρc]
      exact h1
    have h2 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hcH) _).mp (hNQ hm)
    have e : y * (c : G)⁻¹ = (c : G) * ((c : G) * c * y) * (c : G)⁻¹ := by
      have hc3' : (c : G) * c * c = 1 := by rw [← pow_three', hc3]
      calc y * (c : G)⁻¹ = ((c : G) * c * c) * y * (c : G)⁻¹ := by rw [hc3', one_mul]
        _ = (c : G) * ((c : G) * c * y) * (c : G)⁻¹ := by group
    rw [e]
    exact h2
  ·
    right; right
    have hm : (c : G) * y ∈ S14.K4pre S X := by
      refine S14.mem_K4pre.mpr ⟨X.mul_mem hcX hyX, Subgroup.mul_mem _ hcV hyV, ?_⟩
      have e : (⟨(c : G) * y, Subgroup.mul_mem _ hcV hyV⟩ :
          ↥(Subgroup.normalizer (V : Set G))) = c * ⟨y, hyV⟩ := rfl
      rw [e, map_mul, hρc]
      exact h1
    have h2 := (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 H (H.inv_mem hcH)) _).mp (hNQ hm)
    have e : y * (c : G) = (c : G)⁻¹ * ((c : G) * y) * (c : G)⁻¹⁻¹ := by group
    rw [e]
    exact h2

theorem exists_c_13820a' (hS : S.Hyp138) {H : Subgroup G}
    (hH : H ∈ S.Hz) (hHX : H ≤ Subgroup.normalizer (S.X13820 : Set G)) :
    ∃ c ∈ S.X13820, c ^ 3 = 1 ∧
      (∀ u ∈ conjClosure S.V3 H, u * (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹) ∈ fsuV1 T V) ∧
      (∀ u ∈ conjClosure S.V3 H, c * u * c⁻¹ * u⁻¹ ∈ fsuV1 T V → u ∈ fsuV1 T V) ∧
      (∀ y ∈ S.X13820, y ∈ pCoreOf 2 H ∨ y * c⁻¹ ∈ pCoreOf 2 H ∨ y * c ∈ pCoreOf 2 H) ∧
      ∀ h ∈ H, h * c * h⁻¹ * c⁻¹ ∈ pCoreOf 2 H ∨ h * c * h⁻¹ * c ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := S.X13820 with hXdef
  have P := S.plusData_X13820
  have hF := (hS.hF H hH).toHypF91
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hXH : X ≤ H := P.le_L1.trans hL1H
  obtain ⟨x, hxX, hρx⟩ := P.three (swap 0 1 * swap 1 2) (by decide)
  have hx3C : ((x ^ 3 : ↥(Subgroup.normalizer (V : Set G))) : G) ∈
      Subgroup.centralizer (V : Set G) :=
    (S.rho_eq_one_iff _).1 (by rw [map_pow, hρx]; exact c012_facts.2.2)
  have hx3O := P.cent ⟨by simpa using X.pow_mem hxX 3, hx3C⟩
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨_, hx3O⟩
  have hk' : ((x : G) ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  set c : ↥(Subgroup.normalizer (V : Set G)) := x ^ 4 ^ k with hc
  have hcX : (c : G) ∈ X := by simpa [hc] using X.pow_mem hxX (4 ^ k)
  have hρc : S.frame.ρ c = swap 0 1 * swap 1 2 := by
    rw [hc, map_pow, hρx, pow_four_pow_of_cube c012_facts.2.2]
  have hc3 : (c : G) ^ 3 = 1 := by
    have e : (4 : ℕ) ^ k = 2 ^ k * 2 ^ k := by
      rw [← mul_pow]
      norm_num
    simp only [hc, SubgroupClass.coe_pow]
    rw [← pow_mul, mul_comm, pow_mul, e, pow_mul, hk', one_pow]
  have hcH : (c : G) ∈ H := hXH hcX
  have hcV3 : (c : G) ∈ Subgroup.normalizer (S.V3 : Set G) :=
    hF.L₁T_normalizes_Vp (Subgroup.mem_sup_left (P.le_L1 hcX))
  have htri := fun y (hy : y ∈ X) => S.mem_pCoreOf_or_of_X hH hHX hcX hρc hc3 hy
  have hconj : ∀ h ∈ H, h * (c : G) * h⁻¹ * (c : G)⁻¹ ∈ pCoreOf 2 H ∨
      h * (c : G) * h⁻¹ * (c : G) ∈ pCoreOf 2 H := by
    intro h hh
    set y := h * (c : G) * h⁻¹ with hy
    have hyX : y ∈ X := (Subgroup.mem_normalizer_iff.mp (hHX hh) _).mp hcX
    rcases htri y hyX with hyN | h1 | h1
    ·
      exfalso
      obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 H ⟨_, hyN⟩
      have hm' : y ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
      have hy3 : y ^ 3 = 1 := by rw [hy, conj_pow, hc3, mul_one, mul_inv_cancel]
      have h2 : orderOf y ∣ Nat.gcd 3 (2 ^ m) :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hy3) (orderOf_dvd_of_pow_eq_one hm')
      have h4 : Nat.gcd 3 (2 ^ m) = 1 := Nat.Coprime.pow_right _ (by decide : Nat.Coprime 3 2)
      rw [h4, Nat.dvd_one, orderOf_eq_one_iff, hy] at h2
      have hc1 : (c : G) = 1 := by
        have := congrArg (fun z => h⁻¹ * z * h) h2
        simpa [mul_assoc] using this
      have : c = 1 := Subtype.ext hc1
      rw [this, map_one] at hρc
      exact absurd hρc.symm (by decide)
    · exact Or.inl h1
    · exact Or.inr h1
  have hN := S.norm_mem_V1 hS hH hcH hc3 hρc hcV3 hconj
  exact ⟨c, hcX, hc3, hN, fun u hu hfix => S.mem_V1_of_fix hS hH hcH hN hu hfix, htri, hconj⟩

theorem exists_c_13820a (hS : S.Hyp138) {H : Subgroup G}
    (hH : H ∈ S.Hz) (hHX : H ≤ Subgroup.normalizer (S.X13820 : Set G)) :
    ∃ c ∈ S.X13820, c ^ 3 = 1 ∧
      (∀ u ∈ conjClosure S.V3 H, u * (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹) ∈ fsuV1 T V) ∧
      ∀ u ∈ conjClosure S.V3 H, c * u * c⁻¹ * u⁻¹ ∈ fsuV1 T V → u ∈ fsuV1 T V := by
  obtain ⟨c, hcX, hc3, hN, hfix, -, -⟩ := S.exists_c_13820a' hS hH hHX
  exact ⟨c, hcX, hc3, hN, hfix⟩

end Setting4

end CFSG.Quasithin.H13.A6
