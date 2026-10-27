module

public import CFSG.Quasithin.Vol2.Ch12Sec7Mod4D

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_thetaOf (M : Subgroup G) :
    M ≤ Subgroup.normalizer (thetaOf M : Set G) := by
  intro g hg
  apply normalizer_of_maps
  intro w hw
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    exact Subgroup.subset_closure ⟨M.mul_mem (M.mul_mem hg hx.1) (M.inv_mem hg),
      by rw [orderOf_conj']; exact hx.2⟩
  | one => simp
  | mul x y _ _ hx hy =>
    have := (thetaOf M).mul_mem hx hy
    simpa [mul_assoc] using this
  | inv x _ hx =>
    have := (thetaOf M).inv_mem hx
    simpa [mul_assoc] using this

theorem normalizer_le_normalizer_commutator (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer ((⁅H, H⁆ : Subgroup G) : Set G) := by
  intro g hg
  apply normalizer_of_maps
  intro w hw
  have hH : H.map (MulAut.conj g).toMonoidHom = H := by
    ext x
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    constructor
    · intro hx
      have := (Subgroup.mem_normalizer_iff.1 hg _).1 hx
      simpa [mul_assoc] using this
    · intro hx
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) _).1 hx
      simpa [mul_assoc] using this
  have hmap := Subgroup.map_commutator H H (MulAut.conj g).toMonoidHom
  rw [hH] at hmap
  rw [← hmap]
  exact ⟨w, hw, rfl⟩

variable {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [IsMulCommutative ↥V] in
theorem exists_lift_three {K : Subgroup G} (hKN : K ≤ Subgroup.normalizer (V : Set G))
    (hK2 : IsPGroup 2 ↥(K ⊓ Subgroup.centralizer (V : Set G))) {y : G} (hyK : y ∈ K)
    (hy3 : (conjAct V ⟨y, hKN hyK⟩) ^ 3 = 1) :
    ∃ y₁, ∃ hy₁ : y₁ ∈ K, y₁ ^ 3 = 1 ∧ ∃ e : ℕ,
      conjAct V ⟨y, hKN hyK⟩ = (conjAct V ⟨y₁, hKN hy₁⟩) ^ e := by
  have hn0 : orderOf y ≠ 0 := (isOfFinOrder_of_finite y).orderOf_pos.ne'
  obtain ⟨j, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  have hy₁K : y ^ 2 ^ j ∈ K := K.pow_mem hyK _
  have hy₁m : (y ^ 2 ^ j) ^ m = 1 := by rw [← pow_mul, ← hn, pow_orderOf_eq_one]
  have hconj : ∀ n : ℕ, conjAct V ⟨y ^ n, hKN (K.pow_mem hyK n)⟩ =
      (conjAct V ⟨y, hKN hyK⟩) ^ n := fun n => by
    rw [← map_pow]
    rfl
  have hc3 : (y ^ 2 ^ j) ^ 3 ∈ Subgroup.centralizer (V : Set G) := by
    have hN : (y ^ 2 ^ j) ^ 3 ∈ Subgroup.normalizer (V : Set G) := hKN (K.pow_mem hy₁K 3)
    have hpow : (⟨(y ^ 2 ^ j) ^ 3, hN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨y, hKN hyK⟩ ^ (3 * 2 ^ j) := Subtype.ext (by
      show (y ^ 2 ^ j) ^ 3 =
        ((⟨y, hKN hyK⟩ ^ (3 * 2 ^ j) : ↥(Subgroup.normalizer (V : Set G))) : G)
      rw [SubmonoidClass.coe_pow, ← pow_mul, Nat.mul_comm (2 ^ j) 3])
    rw [← conjAct_eq_one' hN, hpow, map_pow, pow_mul, hy3, one_pow]
  refine ⟨y ^ 2 ^ j, hy₁K, ?_, ?_⟩
  · have hmem : (y ^ 2 ^ j) ^ 3 ∈ K ⊓ Subgroup.centralizer (V : Set G) :=
      Subgroup.mem_inf.2 ⟨K.pow_mem hy₁K 3, hc3⟩
    obtain ⟨k, hk⟩ := hK2 ⟨_, hmem⟩
    have hk' : ((y ^ 2 ^ j) ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hm' : ((y ^ 2 ^ j) ^ 3) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hy₁m, one_pow]
    have hd : orderOf ((y ^ 2 ^ j) ^ 3) ∣ Nat.gcd (2 ^ k) m :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hm')
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hm))] at hd
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd)
  · have hodd : Odd (orderOf (conjAct V ⟨y, hKN hyK⟩)) :=
      Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hy3)
    obtain ⟨e, he⟩ := exists_pow_eq_self_of_coprime
      (Nat.Coprime.pow_left j (Nat.coprime_two_left.2 hodd))
    refine ⟨e, ?_⟩
    rw [hconj]
    exact he.symm

omit [IsMulCommutative ↥V] in
theorem isPGroup_inf_centralizer (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {K : Subgroup G}
    (hKL : K ≤ L) : IsPGroup 2 ↥(K ⊓ Subgroup.centralizer (V : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : K ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 L := by
    rw [← inf_centralizer_eq_of_1222 h1222 h]
    exact inf_le_inf_right _ hKL
  exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le hle

theorem Lt_eq_theta
    (h1222 : Stmt12_2_2) (h128 : Stmt12_2_8) (h : Hyp1271 G T L V) {C : Coding ↥V}
    (hC : IdentL C (autOn L V)) {t : G} (ht : t ∈ V) (h1 : C.cd ⟨t, ht⟩ = 1) :
    oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G)) =
      thetaOf (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G)) := by
  set K := L ⊓ Subgroup.centralizer ({t} : Set G) with hKd
  set M := Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G) with hMd
  have hKN := K_le_normalizer h t
  have hKM : K ≤ M := inf_le_inf_right _ Subgroup.le_normalizer
  have hK2 := isPGroup_inf_centralizer h1222 h (K := K) inf_le_left
  have hlift : ∀ {B : B6}, B ∈ stab1 → B.pow 3 = B6.id → ∃ n ∈ thetaOf M,
      ∃ hn : n ∈ K, C.cB (conjAct V ⟨n, hKN hn⟩) = B := by
    intro B hB hB3
    obtain ⟨a, rfl⟩ := hC.2 B (stab1_sub hB).1
    obtain ⟨y, hy, hyK, rfl⟩ := mem_autOn'.1 ((mem_autOn_K_iff hC ht h1 a).2 hB)
    have hy3 : (conjAct V ⟨y, hKN hyK⟩) ^ 3 = 1 := (C.pow_eq_one_iff _ 3).2 hB3
    obtain ⟨y₁, hy₁, hy₁3, e, he⟩ := exists_lift_three hKN hK2 hyK hy3
    have hθ : y₁ ∈ thetaOf M := by
      by_cases h1' : y₁ = 1
      · rw [h1']
        exact Subgroup.one_mem _
      · exact Subgroup.subset_closure ⟨hKM hy₁, orderOf_eq_prime hy₁3 h1'⟩
    refine ⟨y₁ ^ e, Subgroup.pow_mem _ hθ e, K.pow_mem hy₁ e, ?_⟩
    have e2 : conjAct V ⟨y₁ ^ e, hKN (K.pow_mem hy₁ e)⟩ = (conjAct V ⟨y₁, hKN hy₁⟩) ^ e := by
      rw [← map_pow]
      rfl
    rw [e2, ← he]
  apply le_antisymm
  · apply oTwoUpper_le_of_pow
    intro x hx
    have hg := (mem_autOn_K_iff hC ht h1 _).1 (conjAct_mem_autOn hx (hKN hx))
    obtain ⟨a, ha, b, hb, ha3, hb3, he⟩ := cert4_gen3 _ hg
    obtain ⟨n₁, hn₁θ, hn₁K, hn₁⟩ := hlift ha ha3
    obtain ⟨n₂, hn₂θ, hn₂K, hn₂⟩ := hlift hb hb3
    set n := n₁ * n₂ with hnd
    have hnK : n ∈ K := K.mul_mem hn₁K hn₂K
    have hc : n⁻¹ * x ∈ K ⊓ Subgroup.centralizer (V : Set G) := by
      refine Subgroup.mem_inf.2 ⟨K.mul_mem (K.inv_mem hnK) hx, ?_⟩
      have hN : n⁻¹ * x ∈ Subgroup.normalizer (V : Set G) := hKN (K.mul_mem (K.inv_mem hnK) hx)
      rw [← conjAct_eq_one' hN]
      have e1 : conjAct V ⟨n⁻¹ * x, hN⟩ = (conjAct V ⟨n, hKN hnK⟩)⁻¹ * conjAct V ⟨x, hKN hx⟩ := by
        rw [← map_inv, ← map_mul]
        rfl
      have e2 : conjAct V ⟨n, hKN hnK⟩ = conjAct V ⟨x, hKN hx⟩ := by
        apply C.cB_injective
        have e3 : conjAct V ⟨n, hKN hnK⟩ =
            conjAct V ⟨n₁, hKN hn₁K⟩ * conjAct V ⟨n₂, hKN hn₂K⟩ := by
          rw [← map_mul]
          rfl
        rw [e3, C.cB_mul, hn₁, hn₂, he]
      rw [e1, e2, inv_mul_cancel]
    have hcN : K ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (thetaOf M : Set G) :=
      (inf_le_left.trans hKM).trans (le_normalizer_thetaOf M)
    obtain ⟨k, hk⟩ := pow_mem_of_mul hK2 hcN (Subgroup.mul_mem _ hn₁θ hn₂θ) hc
    rw [mul_inv_cancel_left] at hk
    exact ⟨k, hk⟩
  · rw [thetaOf, Subgroup.closure_le]
    rintro x ⟨hxM, hx3⟩
    have hxL : x ∈ L := mem_L_of_orderOf_three h128 h hxM.1 hx3
    exact Subgroup.subset_closure ⟨⟨hxL, hxM.2⟩, by rw [hx3]; decide⟩

omit [Finite G] [IsMulCommutative ↥V] in
theorem commutator_le_self' (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.2 fun _ ha _ hb =>
    H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem Lt_perfect
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V))
    {t : G} (ht : t ∈ V) (h1 : C.cd ⟨t, ht⟩ = 1) :
    Group.IsPerfect ↥(oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G))) := by
  set K := L ⊓ Subgroup.centralizer ({t} : Set G) with hKd
  set Lt := oTwoUpper K with hLtd
  have hKN := K_le_normalizer h t
  have hK2 := isPGroup_inf_centralizer h1222 h (K := K) inf_le_left
  have hKD : K ≤ Subgroup.normalizer ((⁅Lt, Lt⁆ : Subgroup G) : Set G) :=
    (Subgroup.le_normalizer.trans (normalizer_le_normalizer_oTwoUpper K)).trans
      (normalizer_le_normalizer_commutator Lt)
  have hle : Lt ≤ ⁅Lt, Lt⁆ := by
    apply oTwoUpper_le_of_pow
    intro x hx
    have hg := (mem_autOn_K_iff hC ht h1 _).1 (conjAct_mem_autOn hx (hKN hx))
    obtain ⟨a, ha, b, hb, he⟩ := cert4_comm_all _ hg
    obtain ⟨y, hy, hyL, hya⟩ := exists_Lt_of_stab1 h hC ht h1 ha
    obtain ⟨w, hw, hwL, hwb⟩ := exists_Lt_of_stab1 h hC ht h1 hb
    have hnD : ⁅y, w⁆ ∈ ⁅Lt, Lt⁆ := Subgroup.commutator_mem_commutator hyL hwL
    have hnK : ⁅y, w⁆ ∈ K := oTwoUpper_le' K (commutator_le_self' Lt hnD)
    have hc : ⁅y, w⁆⁻¹ * x ∈ K ⊓ Subgroup.centralizer (V : Set G) := by
      refine Subgroup.mem_inf.2 ⟨K.mul_mem (K.inv_mem hnK) hx, ?_⟩
      have hN : ⁅y, w⁆⁻¹ * x ∈ Subgroup.normalizer (V : Set G) :=
        hKN (K.mul_mem (K.inv_mem hnK) hx)
      rw [← conjAct_eq_one' hN]
      have e1 : conjAct V ⟨⁅y, w⁆⁻¹ * x, hN⟩ =
          (conjAct V ⟨⁅y, w⁆, hKN hnK⟩)⁻¹ * conjAct V ⟨x, hKN hx⟩ := by
        rw [← map_inv, ← map_mul]
        rfl
      have e2 : conjAct V ⟨⁅y, w⁆, hKN hnK⟩ = conjAct V ⟨x, hKN hx⟩ := by
        apply C.cB_injective
        have e3 : conjAct V ⟨⁅y, w⁆, hKN hnK⟩ = conjAct V ⟨y, hy⟩ * conjAct V ⟨w, hw⟩ *
            (conjAct V ⟨y, hy⟩)⁻¹ * (conjAct V ⟨w, hw⟩)⁻¹ := by
          rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
          rfl
        rw [e3, C.cB_mul, C.cB_mul, C.cB_mul, hya, hwb, cB_inv_eq C (by rw [hya]; exact
          (stab1_sub ha).1), cB_inv_eq C (by rw [hwb]; exact (stab1_sub hb).1), hya, hwb, he]
      rw [e1, e2, inv_mul_cancel]
    have hcN : K ⊓ Subgroup.centralizer (V : Set G) ≤
        Subgroup.normalizer ((⁅Lt, Lt⁆ : Subgroup G) : Set G) :=
      inf_le_left.trans hKD
    obtain ⟨k, hk⟩ := pow_mem_of_mul hK2 hcN hnD hc
    rw [mul_inv_cancel_left] at hk
    exact ⟨k, hk⟩
  constructor
  apply Subgroup.map_injective (Subgroup.subtype_injective Lt)
  rw [Subgroup.map_subtype_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact le_antisymm (commutator_le_self' Lt) hle

end CFSG.Quasithin.H13.S127.Mod

end
