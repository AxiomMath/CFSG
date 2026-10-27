module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss113Sec
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushNatMain
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModSecBase

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F53Mod Equiv

variable {G : Type} [Group G]

theorem pResidualOf_eq_oTwoRes [Finite G] (X : Subgroup G) :
    pResidualOf 2 X = oTwoRes X := by
  rw [← oTwoUpper_eq_pResidualOf]
  unfold oTwoRes oTwoUpper
  congr 1
  ext x
  constructor
  · rintro ⟨hx, ho⟩
    exact ⟨hx, orderOf x, ho, pow_orderOf_eq_one x⟩
  · rintro ⟨hx, m, hm, hxm⟩
    exact ⟨hx, Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hxm)⟩

theorem zZero_eq [Finite G] (X Z : Subgroup G) :
    zZero X Z = Z ⊓ Subgroup.centralizer (oTwoRes X : Set G) := by
  rw [zZero, pResidualOf_eq_oTwoRes]

theorem ker_le_cSecIn {X S Z : Subgroup G} [Finite G] (h : PushHyp X S Z) {H : Type*} [Group H]
    (θ : ↥X →* H) (hker : ∀ x : ↥X, θ x = 1 ↔ (x : G) ∈ pCoreOf 2 X) (K : Subgroup G) :
    θ.ker ≤ (cSecIn X K Z).subgroupOf X := fun x hx =>
  Subgroup.mem_subgroupOf.mpr (core_le_cSecIn h K ((hker x).mp hx))

theorem pow_conj_eq {x z k : G} (hxz : x * z * x⁻¹ = z * k) (hxk : x * k = k * x) (j : ℕ) :
    x ^ j * z * (x ^ j)⁻¹ = z * k ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hxk' : x * k ^ j * x⁻¹ = k ^ j := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (Commute.pow_right (show Commute x k from hxk) j).eq
    calc x ^ (j + 1) * z * (x ^ (j + 1))⁻¹
        = x * (x ^ j * z * (x ^ j)⁻¹) * x⁻¹ := by group
      _ = (x * z * x⁻¹) * (x * k ^ j * x⁻¹) := by rw [ih]; group
      _ = z * k ^ (j + 1) := by rw [hxz, hxk', pow_succ']; group

section Moved

variable [Finite G] {X S Z : Subgroup G} {H : Type*} [Group H]

omit [Finite G] in
theorem exists_moved (h : PushHyp X S Z) (θ : ↥X →* H)
    (hker : ∀ x : ↥X, θ x = 1 ↔ (x : G) ∈ pCoreOf 2 X) {d : G} (hdL : d ∈ oTwoRes X)
    (hdX : d ∈ X) (hodd : Odd (orderOf (θ ⟨d, hdX⟩))) (hne : θ ⟨d, hdX⟩ ≠ 1) :
    ∃ z ∈ Z, z⁻¹ * (d * z * d⁻¹) ∉ Z ⊓ Subgroup.centralizer (oTwoRes X : Set G) := by
  by_contra hall
  push Not at hall
  apply hne
  refine (hker _).mpr (h.mem_core_of_centralizes hdX ?_)
  refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
  set m := orderOf (θ ⟨d, hdX⟩) with hm
  have hdm : d ^ m ∈ pCoreOf 2 X := by
    have h1 : θ (⟨d, hdX⟩ ^ m) = 1 := by rw [map_pow, hm, pow_orderOf_eq_one]
    exact (hker _).mp h1
  have hdmz : d ^ m * z * (d ^ m)⁻¹ = z := by
    have := h.core_le_centralizer hdm z hz
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  set k := z⁻¹ * (d * z * d⁻¹) with hk
  have hkK := hall z hz
  have hdk : d * k = k * d := Subgroup.mem_centralizer_iff.mp hkK.2 d hdL
  have hdz : d * z * d⁻¹ = z * k := by rw [hk]; group
  have hpow := pow_conj_eq hdz hdk m
  rw [hdmz] at hpow
  have hk2 : k ^ 2 = 1 := h.elemAbelian.2 k hkK.1
  obtain ⟨r, hr⟩ := hodd
  have hkm : k ^ m = k := by rw [hr, pow_succ, pow_mul, hk2, one_pow, one_mul]
  rw [hkm] at hpow
  have hk1 : k = 1 := by
    have : z = z * k := hpow
    simpa using this.symm
  have : d * z * d⁻¹ = z := by rw [hdz, hk1, mul_one]
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this.symm

theorem exists_odd_elt (θ : ↥X →* H) (hθ : Function.Surjective θ) {c : H} :
    ∃ d : G, d ∈ oTwoRes X ∧ ∃ hd : d ∈ X, ∃ k : ℕ, θ ⟨d, hd⟩ = c ^ 2 ^ k := by
  obtain ⟨x, rfl⟩ := hθ c
  obtain ⟨k, hk⟩ := exists_pow_mem_pResidualOf X x.2
  refine ⟨(x : G) ^ 2 ^ k, by rwa [← pResidualOf_eq_oTwoRes], X.pow_mem x.2 _, k, ?_⟩
  have : (⟨(x : G) ^ 2 ^ k, X.pow_mem x.2 _⟩ : ↥X) = x ^ 2 ^ k := rfl
  rw [this, map_pow]

theorem odd_orderOf_pow_two_pow {c : H} (hc : Odd (orderOf c)) (k : ℕ) :
    Odd (orderOf (c ^ 2 ^ k)) ∧ (c ^ 2 ^ k = 1 → c = 1) := by
  refine ⟨Odd.of_dvd_nat hc (orderOf_pow_dvd _), fun h1 => ?_⟩
  have h2 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  have h3 : Nat.Coprime (orderOf c) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hc)
  have := Nat.Coprime.eq_one_of_dvd h3 h2
  exact orderOf_eq_one_iff.mp this

end Moved

section Model

variable [Finite G] {X S Z : Subgroup G} {n : ℕ} (θ : ↥X →* Perm (Fin n))
  (hθ : Function.Surjective θ)

theorem fixW_top_eq_bot (hZ : IsElemAbelian 2 Z) (hXN : X ≤ Subgroup.normalizer (Z : Set G))
    (hk : θ.ker ≤ (cSecIn X (Z ⊓ Subgroup.centralizer (oTwoRes X : Set G)) Z).subgroupOf X) :
    fixW (secModule (isSec_inf_centralizer_oTwoRes hZ hXN) θ hθ hk) ⊤ = ⊥ := by
  have hs := isSec_inf_centralizer_oTwoRes hZ hXN
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨z, rfl⟩ := hs.proj_surjective w
  refine (hs.proj_eq_one_iff z).mpr ?_
  refine mem_inf_centralizer_oTwoRes_of_forall hZ z.2 fun x hx => ?_
  have h1 := hw (θ ⟨x, hx⟩) (Subgroup.mem_top _)
  rw [secModule_act_proj hs θ hθ hk ⟨x, hx⟩ z] at h1
  exact (hs.proj_eq_proj_iff _ _).mp h1.symm

theorem index_fixW_secModule_le (hZ : IsElemAbelian 2 Z) (hXN : X ≤ Subgroup.normalizer (Z : Set G))
    (hk : θ.ker ≤ (cSecIn X (Z ⊓ Subgroup.centralizer (oTwoRes X : Set G)) Z).subgroupOf X)
    {A Q' : Subgroup G} (hAQ : ∀ y ∈ A, ∀ q ∈ Q', y * q = q * y) :
    (fixW (secModule (isSec_inf_centralizer_oTwoRes hZ hXN) θ hθ hk)
        ((A.subgroupOf X).map θ)).index ≤ (Z ⊓ Q').relIndex Z := by
  have hs := isSec_inf_centralizer_oTwoRes hZ hXN
  let P : Subgroup ↥Z := (Z ⊓ Q').subgroupOf Z
  have hPle : P.map hs.proj ≤ fixW (secModule hs θ hθ hk) ((A.subgroupOf X).map θ) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨a, ha, rfl⟩
    rw [secModule_act_proj hs θ hθ hk a x]
    congr 1
    apply Subtype.ext
    show (a : G) * x * (a : G)⁻¹ = x
    rw [mul_inv_eq_iff_eq_mul]
    exact hAQ a (Subgroup.mem_subgroupOf.mp ha) x (Subgroup.mem_inf.mp hx).2
  have h1 := Subgroup.index_dvd_of_le hPle
  have h2 : (P.map hs.proj).index ∣ P.index := Subgroup.index_map_dvd (H := P) hs.proj_surjective
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero) (h1.trans h2)

end Model

end CFSG.Quasithin.F53Push
