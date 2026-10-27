module

public import CFSG.Quasithin.H13.A6S13820Aut4

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

omit [Finite G] S in
theorem comm_mem_of_act20 {K : Subgroup G} {x : G} (hxN : x ∈ Subgroup.normalizer (K : Set G))
    (h : Aut20.act20 K ⟨x, hxN⟩ = 1) {k : G} (hk : k ∈ K) : x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  have h1 := congrArg (fun φ : MulAut (ModO2 K) => φ ((⟨k, hk⟩ : ↥K) : ModO2 K)) h
  simp only [Aut20.act20_mk, MulAut.one_apply] at h1
  have h2 := (QuotientGroup.eq (s := CFSG.pCore 2 ↥K)).1 h1.symm
  rw [← pCoreOf_subgroupOf_eq K] at h2
  have h3 : k⁻¹ * (x * k * x⁻¹) ∈ pCoreOf 2 K := by simpa using Subgroup.mem_subgroupOf.mp h2
  have e : x * k * x⁻¹ * k⁻¹ = k * (k⁻¹ * (x * k * x⁻¹)) * k⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 K hk) _).mp h3

theorem caseA20 {H K : Subgroup G} (hH : H ∈ S.Hz)
    (hK : K ∈ cComp H) (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hHe : H = K ⊔ (S.L1 ⊔ T))
    (hLT : S.L1 ⊔ T ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G)) {t : G}
    (htTL : t ∈ T ⊓ L) (htX : ∀ x ∈ S.X13820, t * x * t⁻¹ * x ∈ pCoreOf 2 S.X13820)
    (htN : t ∈ Subgroup.normalizer (K : Set G)) {u : G} (hu : u ∈ T ⊓ K)
    (hα : Aut20.act20 K ⟨t, htN⟩ = MulAut.conj (Aut20.mk20 K ⟨u, hu.2⟩)) :
    S.Case13820aHyp H K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have P := S.plusData_X13820
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hXN : S.X13820 ≤ Subgroup.normalizer (K : Set G) :=
    (P.le_L1.trans (le_sup_left.trans hH.1.1)).trans hKn
  have hcent := fun x (hx : x ∈ S.X13820) =>
    S.act20_X_eq_one20 hH hKH hKn hLT htX htN hu hα hx (hXN hx)
  have hcomm : ∀ x ∈ S.X13820, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K := fun x hx k hk =>
    comm_mem_of_act20 (hXN hx) (hcent x hx) hk
  have hO2KH : pCoreOf 2 K ≤ pCoreOf 2 H := A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK)
  have hO := S.pCoreOf_le_TK hH hKH hKn
  have hO2XT : pCoreOf 2 S.X13820 ≤ T := S.pCoreOf_le_T_of_le_normalizer20 P.T_le
  have hXK : ¬ S.X13820 ≤ K := by
    intro hXK
    obtain ⟨x, hx, hxodd, hx1⟩ := S.exists_odd_ne_one20
    have hxK := hXK hx
    set z := Aut20.mk20 K ⟨x, hxK⟩ with hz
    have hzc : z ∈ Subgroup.center (ModO2 K) := by
      apply Aut20.mem_center_of_conj_eq_one20
      rw [hz, ← Aut20.act20_of_mem hxK (hXN hx)]
      exact hcent x hx
    have hoTK : t * x * t⁻¹ * x ∈ T ⊓ K := ⟨hO2XT (htX x hx), hXK (pCoreOf_le 2 _ (htX x hx))⟩
    have htxK : t * x * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp htN x).mp hxK
    have hact : Aut20.act20 K ⟨t, htN⟩ z = Aut20.mk20 K ⟨t * x * t⁻¹, htxK⟩ :=
      Aut20.act20_mk K ⟨t, htN⟩ ⟨x, hxK⟩
    have hconj : Aut20.act20 K ⟨t, htN⟩ z = z := by
      rw [hα, MulAut.conj_apply, Subgroup.mem_center_iff.mp hzc, mul_inv_cancel_right]
    have h1 : Aut20.mk20 K ⟨t * x * t⁻¹, htxK⟩ = z := hact.symm.trans hconj
    have hz2 : z ^ 2 ∈ ((T ⊓ K).subgroupOf K).map (Aut20.mk20 K) := by
      have e : Aut20.mk20 K ⟨t * x * t⁻¹ * x, hoTK.2⟩ = Aut20.mk20 K ⟨t * x * t⁻¹, htxK⟩ * z := by
        rw [hz, ← map_mul]
        rfl
      have e2 : z ^ 2 = Aut20.mk20 K ⟨t * x * t⁻¹, htxK⟩ * z := by
        rw [sq]
        congr 1
        exact h1.symm
      rw [e2, ← e]
      exact (Aut20.mem_map_mk20 hO _).2 hoTK
    obtain ⟨c, hc⟩ := (Aut20.isSylowTwoOf_Sb20 (S.isSylowTwoOf_TK hH hKH hKn)).2.1 ⟨_, hz2⟩
    have hc' : (z ^ 2) ^ 2 ^ c = 1 := by simpa using congrArg Subtype.val hc
    have hzm : z ^ orderOf x = 1 := by
      rw [hz, ← map_pow]
      have : (⟨x, hxK⟩ : ↥K) ^ orderOf x = 1 := Subtype.ext (by simp [pow_orderOf_eq_one])
      rw [this, map_one]
    have hz21 : z ^ 2 = 1 :=
      Aut20.eq_one_of_two_odd20 hc' hxodd (by rw [← pow_mul, mul_comm, pow_mul, hzm, one_pow])
    have hz1 : z = 1 := Aut20.eq_one_of_two_odd20 (b := 1) (by simpa using hz21) hxodd hzm
    have hxO : x ∈ pCoreOf 2 K := by
      have h3 : (⟨x, hxK⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := (QuotientGroup.eq_one_iff _).1 hz1
      rw [← pCoreOf_subgroupOf_eq K] at h3
      exact Subgroup.mem_subgroupOf.mp h3
    obtain ⟨d, hd⟩ := pCoreOf_isPGroup 2 K ⟨x, hxO⟩
    have hd' : x ^ 2 ^ d = 1 := by simpa using congrArg Subtype.val hd
    exact hx1 (Aut20.eq_one_of_two_odd20 hd' hxodd (pow_orderOf_eq_one x))
  have hfwd : ∀ k ∈ K, ∀ y ∈ S.X13820, k * y * k⁻¹ ∈ S.X13820 := by
    intro k hk y hy
    have hy' : y ∈ oTwoUpper S.X13820 := by
      have := hy
      rw [P.eq] at this
      exact this
    clear hy
    induction hy' using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨hyX, hyodd⟩ := hy
      have hq : y⁻¹ * k * y * k⁻¹ ∈ pCoreOf 2 K := by
        have := hcomm _ (S.X13820.inv_mem hyX) k hk
        simpa using this
      obtain ⟨b, hb⟩ := pCoreOf_isPGroup 2 K ⟨_, hq⟩
      have hb' : (y⁻¹ * k * y * k⁻¹) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
      have e : k * y * k⁻¹ = y * (y⁻¹ * k * y * k⁻¹) := by group
      rw [e]
      refine Aut20.mul_mem_of_odd20 hyX (P.T_le (hO hq).1) hb' hyodd ?_
      rw [← e, conj_pow, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
    | one => simp
    | mul a b _ _ ha hb =>
      have e : k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) := by group
      rw [e]
      exact S.X13820.mul_mem ha hb
    | inv a _ ha =>
      have e : k * a⁻¹ * k⁻¹ = (k * a * k⁻¹)⁻¹ := by group
      rw [e]
      exact S.X13820.inv_mem ha
  have hKNX : K ≤ Subgroup.normalizer (S.X13820 : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hfwd k hk y, fun hy => ?_⟩
    have := hfwd k⁻¹ (K.inv_mem hk) _ hy
    simpa [mul_assoc] using this
  have hL1NX : S.L1 ≤ Subgroup.normalizer (S.X13820 : Set G) := by
    by_cases hhat : IsHatA6 L
    · rw [S.X13820_of_hat hhat]
      exact A5.le_normalizer_oTwoRes_of_le_normalizer
        (Aut20.le_normalizer_commutator_left20 S.L1 (T ⊓ L))
    · rw [S.X13820_of_not_hat hhat]
      exact Subgroup.le_normalizer
  have hHN : H ≤ Subgroup.normalizer (S.X13820 : Set G) := by
    rw [hHe]
    exact sup_le hKNX (sup_le hL1NX P.T_le)
  refine ⟨hXK, fun x hx k hk => hO2KH (hcomm x hx k hk), hHN, u⁻¹ * t,
    H.mul_mem (H.inv_mem (hKH hu.2)) (hTH htTL.1), fun k hk => ?_, fun x hx => ?_⟩
  ·
    have htk : t * k * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp htN k).mp hk
    have huk : u * k * u⁻¹ ∈ K := K.mul_mem (K.mul_mem hu.2 hk) (K.inv_mem hu.2)
    have h1 := congrArg (fun φ : MulAut (ModO2 K) => φ ((⟨k, hk⟩ : ↥K) : ModO2 K)) hα
    simp only [Aut20.act20_mk, MulAut.conj_apply] at h1
    have h2 : ((⟨t * k * t⁻¹, htk⟩ : ↥K) : ModO2 K) = ((⟨u * k * u⁻¹, huk⟩ : ↥K) : ModO2 K) := by
      rw [h1]
      rfl
    have h3 := (QuotientGroup.eq (s := CFSG.pCore 2 ↥K)).1 h2
    rw [← pCoreOf_subgroupOf_eq K] at h3
    have h4 : (t * k * t⁻¹)⁻¹ * (u * k * u⁻¹) ∈ pCoreOf 2 K := by
      simpa using Subgroup.mem_subgroupOf.mp h3
    have h5 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 K (K.inv_mem hu.2)) _).mp
      ((pCoreOf 2 K).inv_mem h4)
    have h6 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 K hk) _).mp h5
    have e : u⁻¹ * t * k * (u⁻¹ * t)⁻¹ * k⁻¹ =
        k * (u⁻¹ * ((t * k * t⁻¹)⁻¹ * (u * k * u⁻¹))⁻¹ * u⁻¹⁻¹) * k⁻¹ := by group
    rw [e]
    exact hO2KH h6
  ·
    have huX : u⁻¹ ∈ Subgroup.normalizer (S.X13820 : Set G) := Subgroup.inv_mem _ (P.T_le hu.1)
    have huO : u⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 S.X13820 : Set G) :=
      normalizer_le_normalizer_pCoreOf 2 _ huX
    have h1 : u⁻¹ * (t * x * t⁻¹ * x) * u⁻¹⁻¹ ∈ pCoreOf 2 S.X13820 :=
      (Subgroup.mem_normalizer_iff.mp huO _).mp (htX x hx)
    have h2 : u⁻¹ * x⁻¹ * u * x ∈ S.X13820 ⊓ pCoreOf 2 K := by
      refine ⟨?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp huX _).mp (S.X13820.inv_mem hx)
        simpa [mul_assoc] using S.X13820.mul_mem this hx
      · have := (pCoreOf 2 K).inv_mem (hcomm _ (S.X13820.inv_mem hx) _ (K.inv_mem hu.2))
        simpa [mul_assoc] using this
    have hle : S.X13820 ⊓ pCoreOf 2 K ≤ pCoreOf 2 S.X13820 := by
      refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
        ((pCoreOf_isPGroup 2 K).to_le inf_le_right)
      exact F7.le_normalizer_inf Subgroup.le_normalizer
        (hXN.trans (normalizer_le_normalizer_pCoreOf 2 K))
    have e : u⁻¹ * t * x * (u⁻¹ * t)⁻¹ * x =
        (u⁻¹ * (t * x * t⁻¹ * x) * u⁻¹⁻¹) * (u⁻¹ * x⁻¹ * u * x) := by group
    rw [e]
    exact (pCoreOf 2 S.X13820).mul_mem h1 (hle h2)

end Setting4

end CFSG.Quasithin.H13.A6
