module

public import CFSG.RankThree.GF2n.Stroth78.Sec2Fifteen

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem eq_one_or_eq_of_mem_zpowers_of_sq_eq_one {P : Type*} [Group P] {a u : P}
    (ha : a ^ 2 = 1) (hu : u ∈ Subgroup.zpowers a) : u = 1 ∨ u = a := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [← hk, zpow_mul]
    simp [ha]
  · right
    rw [← hk, zpow_add, zpow_mul]
    simp [ha]

theorem mul_comm_of_mem_zpowers {P : Type*} [Group P] {a u v : P}
    (hu : u ∈ Subgroup.zpowers a) (hv : v ∈ Subgroup.zpowers a) : u * v = v * u := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  exact zpow_mul_comm a m n

theorem exists_commutator_eq_of_mul_not_mem_center {P : Type*} [Group P] [Finite P]
    {a b z : P} (ha2 : a ^ 2 = 1)
    (hderiv : _root_.commutator P ≤ Subgroup.zpowers a)
    (hcent : _root_.commutator P ≤ Subgroup.center P)
    (hb : b ∉ Subgroup.center P) (hz : z ∉ Subgroup.center P)
    (hbz : b * z ∉ Subgroup.center P) :
    ∃ l : P, ⁅l, z⁆ = 1 ∧ ⁅l, b⁆ = a := by
  classical
  have ha1 : a ≠ 1 := by
    intro ha
    apply hb
    rw [Subgroup.mem_center_iff]
    intro g
    have hmem : ⁅g, b⁆ ∈ Subgroup.zpowers a :=
      hderiv (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top b))
    rw [ha, Subgroup.zpowers_one_eq_bot] at hmem
    have h1 : ⁅g, b⁆ = 1 := by simpa using hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hcard_a : Nat.card (Subgroup.zpowers a) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha2 ha1]
  let fb : P →* Subgroup.zpowers a :=
    { toFun := fun x =>
        ⟨⁅x, b⁆,
          hderiv (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top b))⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        have hmem_x : ⁅x, b⁆ ∈ Subgroup.zpowers a :=
          hderiv (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top b))
        have hmem_y : ⁅y, b⁆ ∈ Subgroup.zpowers a :=
          hderiv (Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top b))
        have hyc : x * ⁅y, b⁆ * x⁻¹ = ⁅y, b⁆ := by
          have hc := Subgroup.mem_center_iff.mp
            (hcent (Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top b))) x
          rw [hc, mul_assoc, mul_inv_cancel, mul_one]
        have hmul : ⁅x * y, b⁆ = ⁅x, b⁆ * ⁅y, b⁆ := by
          rw [commutatorElement_mul_left_eq_conj_mul, hyc]
          exact mul_comm_of_mem_zpowers hmem_y hmem_x
        exact Subtype.ext hmul }
  let fz : P →* Subgroup.zpowers a :=
    { toFun := fun x =>
        ⟨⁅x, z⁆,
          hderiv (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top z))⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        have hmem_x : ⁅x, z⁆ ∈ Subgroup.zpowers a :=
          hderiv (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top z))
        have hmem_y : ⁅y, z⁆ ∈ Subgroup.zpowers a :=
          hderiv (Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top z))
        have hyc : x * ⁅y, z⁆ * x⁻¹ = ⁅y, z⁆ := by
          have hc := Subgroup.mem_center_iff.mp
            (hcent (Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top z))) x
          rw [hc, mul_assoc, mul_inv_cancel, mul_one]
        have hmul : ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
          rw [commutatorElement_mul_left_eq_conj_mul, hyc]
          exact mul_comm_of_mem_zpowers hmem_y hmem_x
        exact Subtype.ext hmul }
  have hker_b : fb.ker = Subgroup.centralizer ({b} : Set P) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val h)
    · intro h
      apply Subtype.ext
      exact commutatorElement_eq_one_iff_mul_comm.mpr h
  have hker_z : fz.ker = Subgroup.centralizer ({z} : Set P) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val h)
    · intro h
      apply Subtype.ext
      exact commutatorElement_eq_one_iff_mul_comm.mpr h
  have hsurj_b : Function.Surjective fb := by
    intro u
    obtain ⟨y, hy⟩ : ∃ y, ⁅y, b⁆ ≠ 1 := by
      by_contra h
      push Not at h
      apply hb
      rw [Subgroup.mem_center_iff]
      intro g
      exact commutatorElement_eq_one_iff_mul_comm.mp (h g)
    have hmem_y : ⁅y, b⁆ ∈ Subgroup.zpowers a :=
      hderiv (Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top b))
    have hfby : fb y = ⟨a, Subgroup.mem_zpowers a⟩ := by
      apply Subtype.ext
      rcases eq_one_or_eq_of_mem_zpowers_of_sq_eq_one ha2 hmem_y with h1 | h1
      · exact absurd h1 hy
      · exact h1
    have hu : (u : P) ∈ Subgroup.zpowers a := u.2
    rcases eq_one_or_eq_of_mem_zpowers_of_sq_eq_one ha2 hu with h1 | h1
    · refine ⟨1, ?_⟩
      rw [map_one]
      exact Subtype.ext h1.symm
    · refine ⟨y, ?_⟩
      rw [hfby]
      exact Subtype.ext h1.symm
  have hsurj_z : Function.Surjective fz := by
    intro u
    obtain ⟨y, hy⟩ : ∃ y, ⁅y, z⁆ ≠ 1 := by
      by_contra h
      push Not at h
      apply hz
      rw [Subgroup.mem_center_iff]
      intro g
      exact commutatorElement_eq_one_iff_mul_comm.mp (h g)
    have hmem_y : ⁅y, z⁆ ∈ Subgroup.zpowers a :=
      hderiv (Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top z))
    have hfzy : fz y = ⟨a, Subgroup.mem_zpowers a⟩ := by
      apply Subtype.ext
      rcases eq_one_or_eq_of_mem_zpowers_of_sq_eq_one ha2 hmem_y with h1 | h1
      · exact absurd h1 hy
      · exact h1
    have hu : (u : P) ∈ Subgroup.zpowers a := u.2
    rcases eq_one_or_eq_of_mem_zpowers_of_sq_eq_one ha2 hu with h1 | h1
    · refine ⟨1, ?_⟩
      rw [map_one]
      exact Subtype.ext h1.symm
    · refine ⟨y, ?_⟩
      rw [hfzy]
      exact Subtype.ext h1.symm
  have hidx_b : fb.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj_b,
      Subgroup.card_top, hcard_a]
  have hidx_z : fz.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj_z,
      Subgroup.card_top, hcard_a]
  by_contra hno
  have hKle : fz.ker ≤ fb.ker := by
    intro x hx
    rw [hker_z, Subgroup.mem_centralizer_singleton_iff] at hx
    rw [hker_b, Subgroup.mem_centralizer_singleton_iff]
    by_contra hxb
    apply hno
    have hmem : ⁅x, b⁆ ∈ Subgroup.zpowers a :=
      hderiv (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top b))
    have hne : ⁅x, b⁆ ≠ 1 := fun h1 =>
      hxb (commutatorElement_eq_one_iff_mul_comm.mp h1)
    rcases eq_one_or_eq_of_mem_zpowers_of_sq_eq_one ha2 hmem with h1 | h1
    · exact absurd h1 hne
    · exact ⟨x, commutatorElement_eq_one_iff_mul_comm.mpr hx, h1⟩
  have hcard_ker : Nat.card fz.ker = Nat.card fb.ker := by
    have h1 := Subgroup.card_mul_index fz.ker
    have h2 := Subgroup.card_mul_index fb.ker
    rw [hidx_z] at h1
    rw [hidx_b] at h2
    have h : Nat.card fz.ker * 2 = Nat.card fb.ker * 2 := h1.trans h2.symm
    exact Nat.mul_right_cancel (by norm_num) h
  have hKeq : fz.ker = fb.ker :=
    Subgroup.eq_of_le_of_card_ge hKle (le_of_eq hcard_ker.symm)
  obtain ⟨y, hy⟩ : ∃ y, ⁅y, b⁆ ≠ 1 := by
    by_contra h
    push Not at h
    apply hb
    rw [Subgroup.mem_center_iff]
    intro g
    exact commutatorElement_eq_one_iff_mul_comm.mp (h g)
  have hmem_y : ⁅y, b⁆ ∈ Subgroup.zpowers a :=
    hderiv (Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top b))
  have hfby : fb y = ⟨a, Subgroup.mem_zpowers a⟩ := by
    apply Subtype.ext
    rcases eq_one_or_eq_of_mem_zpowers_of_sq_eq_one ha2 hmem_y with h1 | h1
    · exact absurd h1 hy
    · exact h1
  have hy_notmem_b : y ∉ fb.ker := by
    rw [MonoidHom.mem_ker]
    exact fun h1 => hy (congrArg Subtype.val h1)
  have hy_notmem_z : y ∉ fz.ker := by
    simpa [hKeq] using hy_notmem_b
  have hmem_yz : ⁅y, z⁆ ∈ Subgroup.zpowers a :=
    hderiv (Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top z))
  have hfzy : fz y = ⟨a, Subgroup.mem_zpowers a⟩ := by
    apply Subtype.ext
    have hne : ⁅y, z⁆ ≠ 1 := fun h1 => hy_notmem_z (by
      rw [MonoidHom.mem_ker]
      exact Subtype.ext h1)
    rcases eq_one_or_eq_of_mem_zpowers_of_sq_eq_one ha2 hmem_yz with h1 | h1
    · exact absurd h1 hne
    · exact h1
  have hfun : fb = fz := by
    ext x
    by_cases hx : x ∈ fb.ker
    · have hx' : x ∈ fz.ker := by simpa [hKeq] using hx
      rw [MonoidHom.mem_ker] at hx hx'
      rw [hx, hx']
    · have hx' : x ∉ fz.ker := by simpa [hKeq] using hx
      have hmem_xb : ⁅x, b⁆ ∈ Subgroup.zpowers a :=
        hderiv (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top b))
      have hmem_xz : ⁅x, z⁆ ∈ Subgroup.zpowers a :=
        hderiv (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top z))
      have hfxb : fb x = ⟨a, Subgroup.mem_zpowers a⟩ := by
        apply Subtype.ext
        have hne : ⁅x, b⁆ ≠ 1 := fun h1 => hx (by
          rw [MonoidHom.mem_ker]
          exact Subtype.ext h1)
        rcases eq_one_or_eq_of_mem_zpowers_of_sq_eq_one ha2 hmem_xb with h1 | h1
        · exact absurd h1 hne
        · exact h1
      have hfxz : fz x = ⟨a, Subgroup.mem_zpowers a⟩ := by
        apply Subtype.ext
        have hne : ⁅x, z⁆ ≠ 1 := fun h1 => hx' (by
          rw [MonoidHom.mem_ker]
          exact Subtype.ext h1)
        rcases eq_one_or_eq_of_mem_zpowers_of_sq_eq_one ha2 hmem_xz with h1 | h1
        · exact absurd h1 hne
        · exact h1
      rw [hfxb, hfxz]
  have hcomm_same : ∀ x : P, ⁅x, b⁆ = ⁅x, z⁆ := by
    intro x
    have hx : fb x = fz x := congrArg (fun f : P →* Subgroup.zpowers a => f x) hfun
    exact congrArg (fun u : Subgroup.zpowers a => (u : P)) hx
  apply hbz
  rw [Subgroup.mem_center_iff]
  intro x
  rw [← commutatorElement_eq_one_iff_mul_comm]
  have hcent_xz : ⁅x, z⁆ ∈ Subgroup.center P :=
    hcent (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top z))
  have hconj : b * ⁅x, z⁆ * b⁻¹ = ⁅x, z⁆ := by
    have hc := Subgroup.mem_center_iff.mp hcent_xz b
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  rw [commutatorElement_mul_right_eq_mul_conj]
  have hconj' : ⁅x, b⁆ * b * ⁅x, z⁆ * b⁻¹ = ⁅x, b⁆ * ⁅x, z⁆ := by
    calc
      ⁅x, b⁆ * b * ⁅x, z⁆ * b⁻¹ = ⁅x, b⁆ * (b * ⁅x, z⁆ * b⁻¹) := by group
      _ = ⁅x, b⁆ * ⁅x, z⁆ := by rw [hconj]
  rw [hconj', ← hcomm_same x]
  have hmem_xb : ⁅x, b⁆ ∈ Subgroup.zpowers a :=
    hderiv (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top b))
  rcases eq_one_or_eq_of_mem_zpowers_of_sq_eq_one ha2 hmem_xb with h1 | h1
  · rw [h1, one_mul]
  · rw [h1, ← pow_two, ha2]

theorem exists_lbar_conjQbar_sub_eq
    (S : Setting z E F) {a b : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a) (hza : z ∈ QaOf a)
    (hbQ : b ∈ Q z) (hbQa : b ∈ QaOf a)
    (hb_not : Additive.ofMul (mkQbar S ⟨b, hbQ⟩) ∉
      Submodule.span (ZMod 2) {Additive.ofMul (mkQbar S ⟨a, haQ⟩)}) :
    ∃ h : ↥(H z), (QuotientGroup.mk h : Hbar z) ∈ Lbar S a ∧
      conjQbar S h (Additive.ofMul (mkQbar S ⟨b, hbQ⟩)) -
        Additive.ofMul (mkQbar S ⟨b, hbQ⟩) = Additive.ofMul (mkQbar S ⟨a, haQ⟩) := by
  classical
  by_cases haZ : a ∈ ZQ z
  ·
    refine ⟨1, one_mem_Lbar S a, ?_⟩
    have hva : Additive.ofMul (mkQbar S ⟨a, haQ⟩) = 0 := by
      have h1 : (mkQbar S ⟨a, haQ⟩ : QbarOf S) = 1 := by
        rw [← MonoidHom.mem_ker]
        rw [show (mkQbar S).ker = (ZQ z).subgroupOf (Q z) from QuotientGroup.ker_mk' _]
        exact Subgroup.mem_subgroupOf.mpr haZ
      rw [h1]
      rfl
    rw [hva, conjQbar_one]
    simp
  ·
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    have ha2 : a ^ 2 = 1 := sq_eq_one_of_isConj S hconj
    have hzaZ : z ∉ centerIn (QaOf a) :=
      z_not_mem_centerIn_Qa S haQ hconj haZ hza
    have hderiv : ⁅QaOf a, QaOf a⁆ = Subgroup.zpowers a :=
      commutator_QaOf_eq_zpowers S hg
    have ha_mem : a ∈ QaOf a := mem_QaOf_self a
    have ha_center : (⟨a, ha_mem⟩ : ↥(QaOf a)) ∈ Subgroup.center ↥(QaOf a) := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp
        (fStar_le (Subgroup.centralizer ({a} : Set G)) x.2) a (Set.mem_singleton a)).symm
    have hbZa : b ∉ centerIn (QaOf a) := by
      intro hbZ
      have hmem : b ∈ Q z ⊓ centerIn (QaOf a) := Subgroup.mem_inf.mpr ⟨hbQ, hbZ⟩
      have hsup := centerIn_QaOf_inf_Q_le_sup_zpowers_ZQ S haQ hzaZ hmem
      exact hb_not (mkQbar_mem_span_of_mem_sup_zpowers_ZQ S haQ hconj hsup hbQ)
    have hbzZa : b * z ∉ centerIn (QaOf a) := by
      intro hbzZ
      have hbzQ : b * z ∈ Q z := (Q z).mul_mem hbQ (z_mem_Q S)
      have hmem : b * z ∈ Q z ⊓ centerIn (QaOf a) := Subgroup.mem_inf.mpr ⟨hbzQ, hbzZ⟩
      have hsup := centerIn_QaOf_inf_Q_le_sup_zpowers_ZQ S haQ hzaZ hmem
      have hzsup : z ∈ Subgroup.zpowers a ⊔ ZQ z :=
        Subgroup.mem_sup_right (z_mem_ZQ S)
      have hbsup : b ∈ Subgroup.zpowers a ⊔ ZQ z := by
        have h : (b * z) * z⁻¹ ∈ Subgroup.zpowers a ⊔ ZQ z :=
          (Subgroup.zpowers a ⊔ ZQ z).mul_mem hsup
            ((Subgroup.zpowers a ⊔ ZQ z).inv_mem hzsup)
        simpa using h
      exact hb_not (mkQbar_mem_span_of_mem_sup_zpowers_ZQ S haQ hconj hbsup hbQ)
    have hderivP : _root_.commutator ↥(QaOf a) ≤
        Subgroup.zpowers (⟨a, ha_mem⟩ : ↥(QaOf a)) := by
      intro c hc
      rw [Subgroup.mem_zpowers_iff]
      have hcG : ((c : ↥(QaOf a)) : G) ∈ ⁅QaOf a, QaOf a⁆ := by
        have hmap := Subgroup.map_subtype_commutator (QaOf a)
        rw [← hmap]
        exact Subgroup.mem_map_of_mem (QaOf a).subtype hc
      rw [hderiv] at hcG
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcG
      exact ⟨k, Subtype.ext hk⟩
    have hcentP : _root_.commutator ↥(QaOf a) ≤ Subgroup.center ↥(QaOf a) :=
      hderivP.trans (Subgroup.zpowers_le.mpr ha_center)
    have hb_centerP : (⟨b, hbQa⟩ : ↥(QaOf a)) ∉ Subgroup.center ↥(QaOf a) := by
      intro h
      apply hbZa
      rw [centerIn_eq_map_center]
      exact Subgroup.mem_map.mpr ⟨⟨b, hbQa⟩, h, rfl⟩
    have hz_centerP : (⟨z, hza⟩ : ↥(QaOf a)) ∉ Subgroup.center ↥(QaOf a) := by
      intro h
      apply hzaZ
      rw [centerIn_eq_map_center]
      exact Subgroup.mem_map.mpr ⟨⟨z, hza⟩, h, rfl⟩
    have hbz_centerP : (⟨b, hbQa⟩ : ↥(QaOf a)) * ⟨z, hza⟩ ∉
        Subgroup.center ↥(QaOf a) := by
      intro h
      apply hbzZa
      rw [centerIn_eq_map_center]
      exact Subgroup.mem_map.mpr ⟨⟨b, hbQa⟩ * ⟨z, hza⟩, h, rfl⟩
    obtain ⟨l, hlz, hlb⟩ :=
      exists_commutator_eq_of_mul_not_mem_center
        (a := (⟨a, ha_mem⟩ : ↥(QaOf a))) (b := (⟨b, hbQa⟩ : ↥(QaOf a)))
        (z := (⟨z, hza⟩ : ↥(QaOf a)))
        (by exact Subtype.ext ha2)
        hderivP hcentP hb_centerP hz_centerP hbz_centerP
    have hlzG : ⁅(l : G), z⁆ = 1 := by
      have h := congrArg (QaOf a).subtype hlz
      rw [map_commutatorElement] at h
      simpa using h
    have hlbG : ⁅(l : G), b⁆ = a := by
      have h := congrArg (QaOf a).subtype hlb
      rw [map_commutatorElement] at h
      simpa using h
    have hlH : (l : G) ∈ H z := by
      rw [H, Subgroup.mem_centralizer_iff]
      intro t ht
      rw [Set.mem_singleton_iff] at ht
      subst t
      exact (commutatorElement_eq_one_iff_mul_comm.mp hlzG).symm
    let hH : ↥(H z) := ⟨l, hlH⟩
    have hlbar : (QuotientGroup.mk hH : Hbar z) ∈ Lbar S a := by
      rw [← map_L0_eq_Lbar S a]
      refine Subgroup.mem_map.mpr ⟨hH, ?_, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_inf.mpr ⟨l.2, hlH⟩
    refine ⟨hH, hlbar, ?_⟩
    have hconjQ : conjAutQ S hH ⟨b, hbQ⟩ = ⟨a * b, (Q z).mul_mem haQ hbQ⟩ := by
      apply Subtype.ext
      rw [conjAutQ_apply]
      change (l : G) * b * (l : G)⁻¹ = a * b
      have hcomm : (l : G) * b * (l : G)⁻¹ * b⁻¹ = a := by
        simpa [commutatorElement_def] using hlbG
      calc
        (l : G) * b * (l : G)⁻¹ = ((l : G) * b * (l : G)⁻¹ * b⁻¹) * b := by group
        _ = a * b := by rw [hcomm]
    have hclass : (QuotientGroup.mk (conjAutQ S hH ⟨b, hbQ⟩) : QbarOf S) =
        QuotientGroup.mk (⟨a, haQ⟩ : ↥(Q z)) *
          QuotientGroup.mk (⟨b, hbQ⟩ : ↥(Q z)) := by
      rw [hconjQ]
      have hprod : (⟨a * b, (Q z).mul_mem haQ hbQ⟩ : ↥(Q z)) =
          ⟨a, haQ⟩ * ⟨b, hbQ⟩ := Subtype.ext rfl
      rw [hprod]
      simpa only [mkQbar, QuotientGroup.mk'_apply] using
        (map_mul (mkQbar S) (⟨a, haQ⟩ : ↥(Q z)) (⟨b, hbQ⟩ : ↥(Q z)))
    simp only [mkQbar, QuotientGroup.mk'_apply]
    calc
      conjQbar S hH (Additive.ofMul (QuotientGroup.mk (⟨b, hbQ⟩ : ↥(Q z)))) -
          Additive.ofMul (QuotientGroup.mk (⟨b, hbQ⟩ : ↥(Q z)))
          = Additive.ofMul (QuotientGroup.mk (⟨a, haQ⟩ : ↥(Q z)) *
              QuotientGroup.mk (⟨b, hbQ⟩ : ↥(Q z))) -
              Additive.ofMul (QuotientGroup.mk (⟨b, hbQ⟩ : ↥(Q z))) := by
            rw [conjQbar_apply_mk, hclass]
      _ = (Additive.ofMul (QuotientGroup.mk (⟨a, haQ⟩ : ↥(Q z))) +
            Additive.ofMul (QuotientGroup.mk (⟨b, hbQ⟩ : ↥(Q z)))) -
            Additive.ofMul (QuotientGroup.mk (⟨b, hbQ⟩ : ↥(Q z))) := by
            rw [ofMul_mul]
      _ = Additive.ofMul (QuotientGroup.mk (⟨a, haQ⟩ : ↥(Q z))) := by abel

theorem exists_lbar_apply_sub_eq
    (S : Setting z E F) {a b : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a) (hza : z ∈ QaOf a)
    (hbQ : b ∈ Q z) (hbQa : b ∈ QaOf a)
    (hb_not : Additive.ofMul (mkQbar S ⟨b, hbQ⟩) ∉
      Submodule.span (ZMod 2) {Additive.ofMul (mkQbar S ⟨a, haQ⟩)}) :
    ∃ l ∈ Lbar S a,
      ((rhoBar S l : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
        (Additive.ofMul (mkQbar S ⟨b, hbQ⟩)) -
        Additive.ofMul (mkQbar S ⟨b, hbQ⟩) = Additive.ofMul (mkQbar S ⟨a, haQ⟩) := by
  obtain ⟨h, hh, hconv⟩ :=
    exists_lbar_conjQbar_sub_eq S haQ hconj hza hbQ hbQa hb_not
  refine ⟨QuotientGroup.mk h, hh, ?_⟩
  rw [rhoBar_apply_mk, rho_apply_mk]
  exact hconv

end CFSG.RankThree.GF2n.Stroth78
