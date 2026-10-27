module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem4SixA
public import CFSG.Quasithin.Vol2.Ch1Inputs
public import CFSG.Quasithin.Background.A3Structure36AQuasi
public import CFSG.Quasithin.Vol2.Ch1Prop121

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem center_three_of_a36Conclusion624 {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q}
    (hL : A36Conclusion L) (hperf : commutator ↥L = ⊤) :
    ∀ z ∈ Subgroup.center ↥L, orderOf z = 3 → ∀ z' ∈ Subgroup.center ↥L, orderOf z' = 3 →
      z' ∈ Subgroup.zpowers z := by
  classical
  intro z hz hz3 z' hz' hz'3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3Z : 3 ∣ Nat.card (Subgroup.center ↥L) := by
    have h1 := orderOf_dvd_natCard (⟨z, hz⟩ : ↥(Subgroup.center ↥L))
    rwa [Subgroup.orderOf_mk, hz3] at h1
  rcases hL with ⟨-, hsimple, -⟩ | ⟨-, hc3, -⟩ | h3 | h4
  ·
    exfalso
    have hcen : Subgroup.center ↥L = ⊥ := by
      rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with h | h
      · exact h
      · exfalso
        have hcomm : commutator ↥L = ⊥ := by
          rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
          intro x _
          rw [Subgroup.mem_centralizer_iff]
          intro y _
          have hy : y ∈ Subgroup.center ↥L := h ▸ Subgroup.mem_top y
          exact (Subgroup.mem_center_iff.mp hy x).symm
        rw [hperf] at hcomm
        exact top_ne_bot hcomm
    rw [hcen, Subgroup.card_bot] at h3Z
    omega
  ·
    have hzc : Subgroup.zpowers z ≤ Subgroup.center ↥L := Subgroup.zpowers_le.mpr hz
    have hcard : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hz3]
    have heq : Subgroup.zpowers z = Subgroup.center ↥L :=
      Subgroup.eq_of_le_of_card_ge hzc (by rw [hc3, hcard])
    rw [heq]
    exact hz'
  ·
    exfalso
    obtain ⟨p, hp, hp3, -, ⟨e⟩, -⟩ := h3
    have : NeZero p := ⟨hp.ne_zero⟩
    have hF : Nat.card (CFSG.fittingSubgroup ↥L) = p ^ 2 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
      simp [Fintype.card_multiplicative, ZMod.card]
    have hZF := Subgroup.card_dvd_of_le (A36A.center_le_fittingSubgroup (X := ↥L))
    rw [hF] at hZF
    have h3p : 3 ∣ p ^ 2 := h3Z.trans hZF
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3p)
    omega
  ·
    exfalso
    obtain ⟨-, -, -, hprimes⟩ := h4
    have hZF := Subgroup.card_dvd_of_le (A36A.center_le_fittingSubgroup (X := ↥L))
    have h := hprimes 3 Nat.prime_three (h3Z.trans hZF)
    omega

theorem commutator_eq_top_of_perfect624 {X : Type*} [Group X] {K : Subgroup X}
    (hKp : ⁅K, K⁆ = K) : commutator ↥K = ⊤ := by
  apply Subgroup.map_injective K.subtype_injective
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    hKp]

theorem exists_noncentral_three_of_cComp624 {G : Type} [Group G] [Finite G] (h36 : A36ForSQTK)
    (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    {H J : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hJ : J ∈ cComp H) (h3 : 3 ∣ Nat.card J) :
    ∃ x ∈ J, orderOf x = 3 ∧ ∃ k ∈ J, x * k * x⁻¹ * k⁻¹ ∉ pCoreOf 2 H := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.pCore 2 ↥H with hP
  have : P.Normal := CFSG.pCore_normal
  set φ := QuotientGroup.mk' P with hφ
  have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective P
  have hker : Group.IsSolvable φ.ker := by
    rw [hφ, QuotientGroup.ker_mk']
    exact isSolvable_pCore_two_group ↥H
  set J₁ := J.subgroupOf H with hJ₁
  have hJ₁c : J₁ ∈ cComp (⊤ : Subgroup ↥H) := subgroupOf_mem_cComp hJ
  set Jb := J₁.map φ with hJb
  have hJbc : Jb ∈ cComp (⊤ : Subgroup (↥H ⧸ P)) := map_mem_cComp_top φ hφs hker hJ₁c
  have hSQ := sqtkHyp_quotient_of_pCoreOf_ne_bot hK hs hnab hH
  have h36' := (h36 _ hSQ Jb hJbc).1
  have hperf : commutator ↥Jb = ⊤ := commutator_eq_top_of_perfect624 (perfect_of_mem_cComp hJbc)
  have hP2 : IsPGroup 2 P := CFSG.pCore_isPGroup
  have h3b : 3 ∣ Nat.card Jb := by
    have hmul := Subgroup.card_ker_mul_card_range (φ.comp J₁.subtype)
    have hrange : (φ.comp J₁.subtype).range = Jb := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hrange] at hmul
    have hJ₁card : Nat.card J₁ = Nat.card J :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_of_mem_cComp hJ)).toEquiv
    have hker2 : IsPGroup 2 (φ.comp J₁.subtype).ker := by
      intro x
      have hx : ((x : ↥J₁) : ↥H) ∈ P := (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp x.2)
      obtain ⟨c, hc⟩ := hP2 ⟨_, hx⟩
      exact ⟨c, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hc))⟩
    obtain ⟨a, ha⟩ := hker2.exists_card_eq
    rw [ha, hJ₁card] at hmul
    rw [← hmul] at h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
    · exfalso
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
      omega
    · exact h
  obtain ⟨xb, hxb3, hxbc⟩ := exists_noncentral_order_three624 hperf h3b
    (center_three_of_a36Conclusion624 h36' hperf)
  have hkb : ∃ kb : ↥Jb, xb * kb ≠ kb * xb := by
    by_contra hcon
    push Not at hcon
    exact hxbc (Subgroup.mem_center_iff.mpr fun g => (hcon g).symm)
  obtain ⟨kb, hkb⟩ := hkb
  obtain ⟨j₁, hj₁J, hj₁⟩ := xb.2
  obtain ⟨k₁, hk₁J, hk₁⟩ := kb.2
  obtain ⟨e, m, hm3, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos j₁).ne' 3
    (by norm_num)
  set y₁ := j₁ ^ m with hy₁
  have hxm : (xb : ↥H ⧸ P) ^ m = (xb : ↥H ⧸ P) ^ (m % 3) := by
    rw [← pow_mod_orderOf, Subgroup.orderOf_coe, hxb3]
  have hxb1 : (xb : ↥H ⧸ P) ≠ 1 := by
    intro h1
    have : xb = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hxb3
    omega
  have hφy : φ y₁ = (xb : ↥H ⧸ P) ^ m := by rw [hy₁, map_pow, hj₁]
  have hx3 : (xb : ↥H ⧸ P) ^ 3 = 1 := by
    have : xb ^ 3 = 1 := by rw [← hxb3]; exact pow_orderOf_eq_one xb
    simpa using congrArg Subtype.val this
  have hm3' : m % 3 = 1 ∨ m % 3 = 2 := by omega
  have hnc : (xb : ↥H ⧸ P) ^ m * kb ≠ kb * (xb : ↥H ⧸ P) ^ m := by
    intro hc
    apply hkb
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hxm] at hc
    rcases hm3' with h | h
    · rw [h, pow_one] at hc
      exact hc
    · rw [h] at hc
      have hinv : (xb : ↥H ⧸ P) ^ 2 = (xb : ↥H ⧸ P)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_succ, hx3]
      rw [hinv] at hc
      calc (xb : ↥H ⧸ P) * kb = (xb : ↥H ⧸ P) * (kb * (xb : ↥H ⧸ P)⁻¹) * (xb : ↥H ⧸ P) := by
            group
        _ = (xb : ↥H ⧸ P) * ((xb : ↥H ⧸ P)⁻¹ * kb) * (xb : ↥H ⧸ P) := by rw [hc]
        _ = kb * (xb : ↥H ⧸ P) := by group
  have hy3e : y₁ ^ 3 ^ e = 1 := by
    rw [hy₁, ← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  have hyP : y₁ ^ 3 ∈ P := by
    have h1 : φ (y₁ ^ 3) = 1 := by
      rw [map_pow, hφy, ← pow_mul, mul_comm, pow_mul, hx3, one_pow]
    rwa [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hy3 : y₁ ^ 3 = 1 := by
    obtain ⟨c, hc⟩ := hP2 ⟨_, hyP⟩
    have h2 : (y₁ ^ 3) ^ 2 ^ c = 1 := by simpa using congrArg Subtype.val hc
    have h3' : (y₁ ^ 3) ^ 3 ^ e = 1 := by rw [← pow_mul, mul_comm, pow_mul, hy3e, one_pow]
    have hcop : Nat.Coprime (2 ^ c) (3 ^ e) := Nat.Coprime.pow c e (by norm_num)
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3')
    rw [hcop.gcd_eq_one] at hd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  have hy1 : y₁ ≠ 1 := by
    intro h1
    apply hxb1
    have h2 := hφy
    rw [h1, map_one, hxm] at h2
    rcases hm3' with h | h
    · rw [h, pow_one] at h2
      exact h2.symm
    · rw [h] at h2
      calc (xb : ↥H ⧸ P) = (xb : ↥H ⧸ P) ^ 3 * ((xb : ↥H ⧸ P) ^ 2)⁻¹ := by group
        _ = 1 := by rw [hx3, ← h2]; group
  have hyo : orderOf y₁ = 3 := orderOf_eq_prime hy3 hy1
  refine ⟨(y₁ : G), ?_, by rw [Subgroup.orderOf_coe, hyo], (k₁ : G), hk₁J, fun hmem => ?_⟩
  · exact Subgroup.mem_subgroupOf.mp (J₁.pow_mem hj₁J m)
  · apply hnc
    have hP' : (y₁ * k₁ * y₁⁻¹ * k₁⁻¹ : ↥H) ∈ P := by
      have hmap : P.map H.subtype = pCoreOf 2 H := by
        rw [hP]
        rfl
      rw [← hmap] at hmem
      obtain ⟨w, hw, hwe⟩ := hmem
      have : w = y₁ * k₁ * y₁⁻¹ * k₁⁻¹ := Subtype.ext (by simpa using hwe)
      rw [← this]
      exact hw
    have h1 : φ (y₁ * k₁ * y₁⁻¹ * k₁⁻¹) = 1 := by
      rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hP'
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hφy, hk₁] at h1
    calc (xb : ↥H ⧸ P) ^ m * kb = ((xb : ↥H ⧸ P) ^ m * kb * ((xb : ↥H ⧸ P) ^ m)⁻¹ *
          (kb : ↥H ⧸ P)⁻¹) * (kb * (xb : ↥H ⧸ P) ^ m) := by group
      _ = kb * (xb : ↥H ⧸ P) ^ m := by rw [h1, one_mul]

end CFSG.Quasithin.H13
