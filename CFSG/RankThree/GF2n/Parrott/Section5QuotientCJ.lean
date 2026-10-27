module

public import CFSG.RankThree.GF2n.Parrott.Section5QuotientC

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z z₁ : G}

omit [Finite G] in
private theorem ker_quotMk_eq (z₁ : G) :
    (quotMk z₁).ker =
      (Subgroup.zpowers z₁).subgroupOf (Subgroup.centralizer ({z₁} : Set G)) := by
  ext x
  rw [MonoidHom.mem_ker, quotMk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf]

omit [Finite G] in
private theorem comm_mem_zpowers_of_quotMk_commute
    {x : ↥(Subgroup.centralizer ({z₁} : Set G))} {j : G}
    (hjC : j ∈ Subgroup.centralizer ({z₁} : Set G))
    (h1 : quotMk z₁ ⟨j, hjC⟩ * quotMk z₁ x = quotMk z₁ x * quotMk z₁ ⟨j, hjC⟩) :
    (x : G)⁻¹ * j⁻¹ * (x : G) * j ∈ Subgroup.zpowers z₁ := by
  rw [← map_mul, ← map_mul] at h1
  have h2 : quotMk z₁ ((⟨j, hjC⟩ * x)⁻¹ * (x * ⟨j, hjC⟩)) = 1 := by
    rw [map_mul, map_inv, h1]
    simp
  have h3 : (((⟨j, hjC⟩ * x)⁻¹ * (x * ⟨j, hjC⟩) :
      ↥(Subgroup.centralizer ({z₁} : Set G))) : G) ∈ Subgroup.zpowers z₁ :=
    Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h2)
  have e : (((⟨j, hjC⟩ * x)⁻¹ * (x * ⟨j, hjC⟩) :
      ↥(Subgroup.centralizer ({z₁} : Set G))) : G) =
      (x : G)⁻¹ * j⁻¹ * (x : G) * j := by
    show ((j : G) * (x : G))⁻¹ * ((x : G) * j) = _
    group
  rwa [e] at h3

omit [Finite G] in
private theorem mul_mul_inv_eq_mul_of_mem_zpowers_of_mem_centralizer {x j : G}
    (hx : x ∈ Subgroup.centralizer ({z₁} : Set G))
    (hc : x⁻¹ * j⁻¹ * x * j ∈ Subgroup.zpowers z₁) :
    x * j * x⁻¹ = j * (x⁻¹ * j⁻¹ * x * j) := by
  have hzx : Subgroup.zpowers z₁ ≤ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hx).symm)
  have hxc : (x⁻¹ * j⁻¹ * x * j) * x = x * (x⁻¹ * j⁻¹ * x * j) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hzx hc)
  have e1 : x * (x⁻¹ * j⁻¹ * x * j) * x⁻¹ = j⁻¹ * x * j * x⁻¹ := by group
  have e2 : x * (x⁻¹ * j⁻¹ * x * j) * x⁻¹ = (x⁻¹ * j⁻¹ * x * j) := by
    rw [hxc.symm]
    group
  have e3 : j⁻¹ * x * j * x⁻¹ = x⁻¹ * j⁻¹ * x * j := by rw [← e1, e2]
  calc x * j * x⁻¹ = j * (j⁻¹ * x * j * x⁻¹) := by group
    _ = j * (x⁻¹ * j⁻¹ * x * j) := by rw [e3]

theorem card_J_quotW_of_ne (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z))
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) :
    Nat.card (J (quotW hzC)) = 2 ^ 9 := by
  have hJC : J z ≤ Subgroup.centralizer ({z₁} : Set G) :=
    fun x hx => (J_le_inf_centralizer_z1 hz₁ hx).2
  rw [J_quotW_eq_of_ne h hZ hz₁ hz₁z hz₁2 hzC,
    ← Subgroup.relIndex_ker ((J z).subgroupOf (Subgroup.centralizer ({z₁} : Set G)))
      (quotMk z₁), ker_quotMk_eq]
  have h1 := Subgroup.relIndex_mul_card
    ((Subgroup.zpowers z₁).subgroupOf (Subgroup.centralizer ({z₁} : Set G)))
    ((J z).subgroupOf (Subgroup.centralizer ({z₁} : Set G)))
  have hle : (Subgroup.zpowers z₁).subgroupOf (Subgroup.centralizer ({z₁} : Set G)) ≤
      (J z).subgroupOf (Subgroup.centralizer ({z₁} : Set G)) :=
    fun x hx => Subgroup.mem_subgroupOf.mpr
      (zpowers_le_J_of_mem_centerIn hz₁ (Subgroup.mem_subgroupOf.mp hx))
  have hz₁C : z₁ ∈ Subgroup.centralizer ({z₁} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hcard2 : Nat.card ((Subgroup.zpowers z₁).subgroupOf
      (Subgroup.centralizer ({z₁} : Set G))) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.zpowers_le.mpr hz₁C)).toEquiv, Nat.card_zpowers, hz₁2]
  have hcardJ : Nat.card ((J z).subgroupOf (Subgroup.centralizer ({z₁} : Set G))) = 2 ^ 10 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJC).toEquiv, card_J h]
  rw [inf_eq_left.mpr hle, hcard2, hcardJ] at h1
  omega

theorem commutator_J_quotW_of_ne (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) :
    ⁅J (quotW hzC), J (quotW hzC)⁆ = Subgroup.zpowers (quotW hzC) := by
  have hJC : J z ≤ Subgroup.centralizer ({z₁} : Set G) :=
    fun x hx => (J_le_inf_centralizer_z1 hz₁ hx).2
  rw [J_quotW_eq_of_ne h hZ hz₁ hz₁z hz₁2 hzC, ← Subgroup.map_commutator]
  have h1 : ⁅(J z).subgroupOf (Subgroup.centralizer ({z₁} : Set G)),
      (J z).subgroupOf (Subgroup.centralizer ({z₁} : Set G))⁆ =
      Subgroup.zpowers (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({z₁} : Set G))) := by
    apply Subgroup.map_injective (Subgroup.centralizer ({z₁} : Set G)).subtype_injective
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers, Subgroup.map_subgroupOf_eq_of_le hJC]
    have hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z := h.2.2.1
    rw [hcomm]
    rfl
  rw [h1, MonoidHom.map_zpowers]
  rfl

theorem centerIn_J_quotW_of_ne (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z))
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) :
    centerIn (J (quotW hzC)) = Subgroup.zpowers (quotW hzC) := by
  have hJC : J z ≤ Subgroup.centralizer ({z₁} : Set G) :=
    fun x hx => (J_le_inf_centralizer_z1 hz₁ hx).2
  apply le_antisymm
  · rintro y ⟨hyJ, hyC⟩
    obtain ⟨x, hxJ, rfl⟩ := (mem_J_quotW_iff_of_ne h hZ hz₁ hz₁z hz₁2 hzC y).mp hyJ
    have hxZ : (x : G) ∈ centerIn (J z) := by
      refine ⟨hxJ, ?_⟩
      show (x : G) ∈ Subgroup.centralizer ((J z : Subgroup G) : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have hjw : quotMk z₁ ⟨j, hJC hj⟩ ∈ J (quotW hzC) :=
        (mem_J_quotW_iff_of_ne h hZ hz₁ hz₁z hz₁2 hzC _).mpr ⟨⟨j, hJC hj⟩, hj, rfl⟩
      have h3 := comm_mem_zpowers_of_quotMk_commute (x := x) (j := j) (hJC hj)
        (Subgroup.mem_centralizer_iff.mp hyC _ hjw)
      have h4 : (x : G)⁻¹ * j⁻¹ * (x : G) * j ∈ Subgroup.zpowers z := by
        have h5 : (x : G)⁻¹ * j⁻¹ * (x : G) * j = ⁅(x : G)⁻¹, j⁻¹⁆ := by
          rw [commutatorElement_def]
          group
        rw [h5]
        have h6 : ⁅(x : G)⁻¹, j⁻¹⁆ ∈ ⁅J z, J z⁆ :=
          Subgroup.commutator_mem_commutator ((J z).inv_mem hxJ) ((J z).inv_mem hj)
        have hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z := h.2.2.1
        rwa [hcomm] at h6
      have h8 : (x : G)⁻¹ * j⁻¹ * (x : G) * j = 1 := by
        have h9 : (x : G)⁻¹ * j⁻¹ * (x : G) * j ∈
            Subgroup.zpowers z ⊓ Subgroup.zpowers z₁ := Subgroup.mem_inf.mpr ⟨h4, h3⟩
        rw [zpowers_inf_zpowers_eq_bot_of_orderOf_eq_two h.1 hz₁z hz₁2,
          Subgroup.mem_bot] at h9
        exact h9
      have e : j * (x : G) * ((x : G)⁻¹ * j⁻¹ * (x : G) * j) = (x : G) * j := by group
      rw [h8, mul_one] at e
      exact e
    have hz₁C : z₁ ∈ Subgroup.centralizer ({z₁} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have hk : quotMk z₁ ⟨z₁, hz₁C⟩ = 1 := by
      show QuotientGroup.mk (⟨z₁, hz₁C⟩ : ↥(Subgroup.centralizer ({z₁} : Set G))) = 1
      rw [QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers z₁)
    rcases (mem_centerIn_J_iff h hz₁ hz₁z hz₁2).mp hxZ with h1 | h1 | h1 | h1
    · have hx1 : x = 1 := Subtype.ext h1
      rw [hx1, map_one]
      exact Subgroup.one_mem _
    · have hxz : x = ⟨z, hzC⟩ := Subtype.ext h1
      rw [hxz]
      exact Subgroup.mem_zpowers _
    · have hxz₁ : x = ⟨z₁, hz₁C⟩ := Subtype.ext h1
      rw [hxz₁, hk]
      exact Subgroup.one_mem _
    · have hxzz : x = ⟨z, hzC⟩ * ⟨z₁, hz₁C⟩ := Subtype.ext h1
      rw [hxzz, map_mul, hk, mul_one]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    refine ⟨?_, ?_⟩
    · exact (mem_J_quotW_iff_of_ne h hZ hz₁ hz₁z hz₁2 hzC _).mpr
        ⟨⟨z, hzC⟩, z_mem_J h, rfl⟩
    · show quotW hzC ∈
        Subgroup.centralizer ((J (quotW hzC) : Subgroup (QuotC z₁)) : Set (QuotC z₁))
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨x, hxJ, rfl⟩ := (mem_J_quotW_iff_of_ne h hZ hz₁ hz₁z hz₁2 hzC y).mp hy
      change quotMk z₁ x * quotMk z₁ ⟨z, hzC⟩ = quotMk z₁ ⟨z, hzC⟩ * quotMk z₁ x
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp (z_centralizes_J h) (x : G) hxJ

theorem isExtraspecial2_J_quotW_of_ne (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) :
    IsExtraspecial2 (J (quotW hzC)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (pCore_isPGroup (p := 2) (G := ↥(H (quotW hzC)))).map (H (quotW hzC)).subtype
  · rw [← CFSG.centerIn_eq_map_center, commutator_J_quotW_of_ne h hZ hz₁ hz₁z hz₁2 hzC,
      centerIn_J_quotW_of_ne h hZ hz₁ hz₁z hz₁2 hzC]
  · rw [commutator_J_quotW_of_ne h hZ hz₁ hz₁z hz₁2 hzC, Nat.card_zpowers,
      orderOf_quotW h hz₁z hz₁2 hzC]

theorem centralizer_J_quotW_le_of_ne (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) :
    H (quotW hzC) ⊓
      Subgroup.centralizer ((J (quotW hzC) : Subgroup (QuotC z₁)) : Set (QuotC z₁)) ≤
      J (quotW hzC) := by
  have hJC : J z ≤ Subgroup.centralizer ({z₁} : Set G) :=
    fun x hx => (J_le_inf_centralizer_z1 hz₁ hx).2
  rintro y ⟨hyH, hyC⟩
  obtain ⟨x, hx⟩ := quotHH₁_surjective h hZ hz₁ hz₁z hz₁2 hzC ⟨y, hyH⟩
  have hxincl : (Subgroup.inclusion inf_le_right x : ↥(Subgroup.centralizer ({z₁} : Set G))) =
      ⟨(x : G), x.2.2⟩ := Subtype.ext rfl
  have hxy : quotMk z₁ ⟨(x : G), x.2.2⟩ = y := by
    have h := congrArg Subtype.val hx
    simpa [quotHH₁, quotH₁, hxincl] using h
  let xH : ↥(H z) := ⟨(x : G), x.2.1⟩
  have hxJ : (x : G) ∈ J z := by
    have hZx : conjZ z xH = 1 := by
      apply MulEquiv.ext
      intro c
      apply Subtype.ext
      rw [conjZ_apply_coe]
      show (xH : G) * (c : G) * (xH : G)⁻¹ = (c : G)
      have hc := (mem_centerIn_J_iff h hz₁ hz₁z hz₁2).mp c.2
      have hxz : (xH : G) * z = z * (xH : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp x.2.1
      have hxz₁ : (xH : G) * z₁ = z₁ * (xH : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp x.2.2
      rcases hc with h1 | h1 | h1 | h1
      · rw [h1, mul_one, mul_inv_cancel]
      · rw [h1, hxz, mul_inv_cancel_right]
      · rw [h1, hxz₁, mul_inv_cancel_right]
      · rw [h1]
        calc (xH : G) * (z * z₁) * (xH : G)⁻¹ =
            ((xH : G) * z * (xH : G)⁻¹) * ((xH : G) * z₁ * (xH : G)⁻¹) := by group
          _ = z * z₁ := by rw [hxz, hxz₁]; group
    have hVx : conjV h xH = 1 := by
      apply MulEquiv.ext
      intro v
      obtain ⟨j, rfl⟩ := QuotientV.pi_surjective z v
      rw [conjV_pi_conj h xH j.2, MulAut.one_apply]
      have hjw : quotMk z₁ ⟨(j : G), hJC j.2⟩ ∈ J (quotW hzC) :=
        (mem_J_quotW_iff_of_ne h hZ hz₁ hz₁z hz₁2 hzC _).mpr
          ⟨⟨(j : G), hJC j.2⟩, j.2, rfl⟩
      have hc := comm_mem_zpowers_of_quotMk_commute (x := ⟨(x : G), x.2.2⟩) (j := (j : G))
        (hJC j.2) (by rw [hxy]; exact Subgroup.mem_centralizer_iff.mp hyC _ hjw)
      have he := mul_mul_inv_eq_mul_of_mem_zpowers_of_mem_centralizer (x := (x : G))
        (j := (j : G)) x.2.2 hc
      have hcZ : (x : G)⁻¹ * (j : G)⁻¹ * (x : G) * (j : G) ∈ centerIn (J z) :=
        (Subgroup.zpowers_le.mpr hz₁) hc
      have hcJ : (x : G)⁻¹ * (j : G)⁻¹ * (x : G) * (j : G) ∈ J z := hcZ.1
      have e : (⟨(xH : G) * (j : G) * (xH : G)⁻¹, H_conj_mem_J xH j.2⟩ : J z) =
          ⟨(j : G) * ((x : G)⁻¹ * (j : G)⁻¹ * (x : G) * (j : G)),
            (J z).mul_mem j.2 hcJ⟩ := Subtype.ext he
      rw [e]
      have h2 := pi_mk_mul_J (z := z) (j : G)
        ((x : G)⁻¹ * (j : G)⁻¹ * (x : G) * (j : G)) j.2 hcJ
      rw [h2, (pi_eq_one_iff_mem_centerIn hcJ).mpr hcZ, mul_one]
    exact mem_J_of_conjZ_eq_one_of_conjV_eq_one h (x := xH) hZx hVx
  exact (mem_J_quotW_iff_of_ne h hZ hz₁ hz₁z hz₁2 hzC y).mpr
    ⟨⟨(x : G), x.2.2⟩, hxJ, hxy⟩

end CFSG.RankThree.GF2n.Parrott
