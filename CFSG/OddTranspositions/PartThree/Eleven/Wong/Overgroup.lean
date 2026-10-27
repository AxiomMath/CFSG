module

public import CFSG.Timmesfeld.Basic

public section

namespace CFSG.OddTranspositions.PartThree.Wong

theorem eq_top_of_involution_classes {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    {t u : G} (htH : t ∈ H) (huH : u ∈ H) (ht : orderOf t = 2) (hu : orderOf u = 2)
    (htu : ¬ IsConj t u) (hC : ∀ a ∈ H, orderOf a = 2 → Subgroup.centralizer {a} ≤ H)
    (hcl : ∀ a ∈ H, orderOf a = 2 →
      (∃ h ∈ H, h⁻¹ * t * h = a) ∨ (∃ h ∈ H, h⁻¹ * u * h = a)) :
    H = ⊤ := by
  classical
  have hAllInv : ∀ x : G, orderOf x = 2 → x ∈ H := by
    intro x hx2
    by_contra hxH
    obtain ⟨y, hyH, hy2, hxy⟩ : ∃ y ∈ H, orderOf y = 2 ∧ ¬ IsConj x y := by
      by_cases hconj : IsConj t x
      · refine ⟨u, huH, hu, ?_⟩
        rintro hxu
        exact htu (hconj.trans hxu)
      · refine ⟨t, htH, ht, ?_⟩
        rintro hxt
        exact hconj hxt.symm
    have hx2' : x * x = 1 := by rw [← pow_two, ← hx2, pow_orderOf_eq_one]
    have hy2' : y * y = 1 := by rw [← pow_two, ← hy2, pow_orderOf_eq_one]
    by_cases hodd : Odd (orderOf (x * y))
    ·
      obtain ⟨g, -, hg⟩ := CFSG.Timmesfeld.exists_conj_of_odd_orderOf_mul hx2' hy2' hodd
      exact hxy (isConj_iff.mpr ⟨g, hg⟩)
    ·
      have heven : Even (orderOf (x * y)) := Nat.not_odd_iff_even.mp hodd
      obtain ⟨k, hk⟩ := heven
      have hk2 : orderOf (x * y) = 2 * k := by omega
      have hk_pos : 0 < k := by
        have := orderOf_pos (x * y)
        omega
      set z : G := (x * y) ^ k with hz_def
      have hz2 : z * z = 1 := by
        rw [hz_def, ← pow_two, ← pow_mul, mul_comm k 2, ← hk2, pow_orderOf_eq_one]
      have hz_ne_one : z ≠ 1 := by
        intro hz1
        rw [hz_def] at hz1
        have hdvd : orderOf (x * y) ∣ k := orderOf_dvd_iff_pow_eq_one.mpr hz1
        rw [hk2] at hdvd
        have hle : 2 * k ≤ k := Nat.le_of_dvd hk_pos hdvd
        omega
      have hz_order : orderOf z = 2 := by
        have hz2' : z ^ 2 = 1 := by rw [pow_two]; exact hz2
        have hdiv : orderOf z ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hz2'
        rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h1 | h2
        · exact absurd (orderOf_eq_one_iff.mp h1) hz_ne_one
        · exact h2
      have hconj_x : x * (x * y) * x⁻¹ = (x * y)⁻¹ := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hx2', inv_eq_of_mul_eq_one_right hy2']
        calc x * (x * y) * x = (x * x) * y * x := by group
          _ = 1 * y * x := by rw [hx2']
          _ = y * x := by group
      have hconj_y : y * (x * y) * y⁻¹ = (x * y)⁻¹ := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hx2', inv_eq_of_mul_eq_one_right hy2']
        calc y * (x * y) * y = y * x * (y * y) := by group
          _ = y * x * 1 := by rw [hy2']
          _ = y * x := by group
      have hz_inv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
      have hxz_conj : x * z * x⁻¹ = z := by
        calc x * z * x⁻¹ = x * (x * y) ^ k * x⁻¹ := by rw [hz_def]
          _ = (x * (x * y) * x⁻¹) ^ k := (conj_pow (a := x) (b := x * y) (i := k)).symm
          _ = ((x * y)⁻¹) ^ k := by rw [hconj_x]
          _ = ((x * y) ^ k)⁻¹ := by rw [inv_pow]
          _ = z⁻¹ := by rw [← hz_def]
          _ = z := hz_inv
      have hyz_conj : y * z * y⁻¹ = z := by
        calc y * z * y⁻¹ = y * (x * y) ^ k * y⁻¹ := by rw [hz_def]
          _ = (y * (x * y) * y⁻¹) ^ k := (conj_pow (a := y) (b := x * y) (i := k)).symm
          _ = ((x * y)⁻¹) ^ k := by rw [hconj_y]
          _ = ((x * y) ^ k)⁻¹ := by rw [inv_pow]
          _ = z⁻¹ := by rw [← hz_def]
          _ = z := hz_inv
      have hxz : x * z = z * x := by
        calc x * z = x * z * x⁻¹ * x := by group
          _ = z * x := by rw [hxz_conj]
      have hyz : y * z = z * y := by
        calc y * z = y * z * y⁻¹ * y := by group
          _ = z * y := by rw [hyz_conj]
      have hzH : z ∈ H := by
        apply hC y hyH hy2
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        subst hw
        exact hyz
      have hxH' : x ∈ H := by
        apply hC z hzH hz_order
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        subst hw
        exact hxz.symm
      exact hxH hxH'
  set C : Subgroup G := Subgroup.centralizer ({t} : Set G) with hC_def
  have hCle : C ≤ H := by
    rw [hC_def]
    exact hC t htH ht
  have hCsub : C.subgroupOf H = Subgroup.centralizer ({⟨t, htH⟩} : Set H) := by
    ext h
    rw [Subgroup.mem_subgroupOf, hC_def]
    constructor
    · intro hh
      rw [Subgroup.mem_centralizer_iff] at hh
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      apply Subtype.ext
      simpa only [Subgroup.coe_mul] using hh t (by simp)
    · intro hh
      rw [Subgroup.mem_centralizer_iff] at hh
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      simpa only [Subgroup.coe_mul] using congrArg Subtype.val (hh ⟨t, htH⟩ (by simp))
  have hset : (conjugatesOf t : Set G) = Subtype.val '' (conjugatesOf (⟨t, htH⟩ : H)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨g, hg⟩ := isConj_iff.mp hx
      have hx2 : orderOf x = 2 := by
        rw [← ht]
        exact (SemiconjBy.orderOf_eq g (by
          change g * t = x * g
          rw [← hg]
          group)).symm
      have hxH : x ∈ H := hAllInv x hx2
      refine ⟨⟨x, hxH⟩, ?_, rfl⟩
      rcases hcl x hxH hx2 with ⟨h, hhH, hh⟩ | ⟨h, hhH, hh⟩
      · refine isConj_iff.mpr ⟨⟨h⁻¹, H.inv_mem hhH⟩, ?_⟩
        apply Subtype.ext
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] using hh
      · exfalso
        have hu_x : IsConj u x := isConj_iff.mpr ⟨h⁻¹, by rw [inv_inv]; exact hh⟩
        exact htu (hx.trans hu_x.symm)
    · rintro ⟨h, hh, hx⟩
      obtain ⟨k, hk⟩ := isConj_iff.mp hh
      rw [← hx]
      exact isConj_iff.mpr ⟨(k : G), by
        have := congrArg Subtype.val hk
        simpa using this⟩
  have hclass : (conjugatesOf t).ncard = (conjugatesOf (⟨t, htH⟩ : H)).ncard := by
    rw [hset, Set.ncard_image_of_injective _ Subtype.coe_injective]
  have hGsize : (conjugatesOf t).ncard = C.index := by
    rw [hC_def]
    exact (Subgroup.index_centralizer_eq_ncard t).symm
  have hHsize : (conjugatesOf (⟨t, htH⟩ : H)).ncard = C.relIndex H := by
    rw [← Subgroup.index_centralizer_eq_ncard (⟨t, htH⟩ : H)]
    change (Subgroup.centralizer ({⟨t, htH⟩} : Set H)).index = (C.subgroupOf H).index
    rw [hCsub]
  have hrel : C.relIndex H = C.index := by
    calc C.relIndex H = (conjugatesOf (⟨t, htH⟩ : H)).ncard := hHsize.symm
      _ = (conjugatesOf t).ncard := hclass.symm
      _ = C.index := hGsize
  have hrel_ne : C.relIndex H ≠ 0 := by
    have : (C.subgroupOf H).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact this
  have hidx : H.index = 1 := by
    refine Nat.mul_left_cancel (Nat.pos_of_ne_zero hrel_ne) ?_
    rw [mul_one]
    calc C.relIndex H * H.index = C.index := Subgroup.relIndex_mul_index hCle
      _ = C.relIndex H := hrel.symm
  exact Subgroup.index_eq_one.mp hidx

end CFSG.OddTranspositions.PartThree.Wong
