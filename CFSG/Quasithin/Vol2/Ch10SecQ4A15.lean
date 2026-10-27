module

public import CFSG.Quasithin.Background.A3Structure36AQuasi
public import CFSG.Quasithin.Vol2.Ch10SecQ4A12
public import CFSG.Quasithin.Vol2.Ch10SecQ4A3
public import CFSG.Quasithin.Vol2.Ch10SecQ4A4

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C1

theorem normal_le_center_or_eq_top' {Y : Type*} [Group Y] (hq : CFSG.IsQuasisimple Y)
    (N : Subgroup Y) [N.Normal] : N ≤ Subgroup.center Y ∨ N = ⊤ := by
  let π := QuotientGroup.mk' (Subgroup.center Y)
  have := hq.2.1
  have hnormal : (N.map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  rcases hnormal.eq_bot_or_eq_top with hbot | htop
  · left
    have hk : N ≤ π.ker := N.map_eq_bot_iff.mp hbot
    simpa only [π, QuotientGroup.ker_mk'] using hk
  · right
    have hsup : N ⊔ Subgroup.center Y = ⊤ := by
      have hcomap := Subgroup.comap_map_eq π N
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
      exact hcomap.symm
    have hder : commutator Y ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    rw [eq_top_iff]
    calc (⊤ : Subgroup Y) = commutator Y := hq.1.commutator_eq_top.symm
      _ ≤ N := hder

variable {G : Type} [Group G] [Finite G] {K J : Subgroup G}

theorem map_centralizer_le_center (hK : IsShort2 K) (hKJ : K ≤ J)
    (hQK : pCoreOf 2 J ≤ Subgroup.normalizer (K : Set G))
    (hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)) :
    ((J ⊓ Subgroup.centralizer (conjClosure (blockU K) J : Set G)).subgroupOf J).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥J)) ≤ Subgroup.center _ := by
  set W := conjClosure (blockU K) J
  have hJW : J ≤ Subgroup.normalizer (W : Set G) := le_normalizer_conjClosure _ J
  have hNn : ((J ⊓ Subgroup.centralizer (W : Set G)).subgroupOf J).Normal := by
    refine normal_subgroupOf fun j hj => Subgroup.mem_normalizer_iff.mpr fun x => ?_
    constructor
    · rintro ⟨hx, hxc⟩
      refine ⟨J.mul_mem (J.mul_mem hj hx) (J.inv_mem hj), Subgroup.mem_centralizer_iff.mpr
        fun w hw => ?_⟩
      have hw' : j⁻¹ * w * j⁻¹⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hJW (J.inv_mem hj)) w).mp hw
      have := Subgroup.mem_centralizer_iff.mp hxc _ hw'
      rw [inv_inv] at this
      calc w * (j * x * j⁻¹) = j * ((j⁻¹ * w * j) * x) * j⁻¹ := by group
        _ = j * (x * (j⁻¹ * w * j)) * j⁻¹ := by rw [this]
        _ = j * x * j⁻¹ * w := by group
    · rintro ⟨hx, hxc⟩
      have hx' : x = j⁻¹ * (j * x * j⁻¹) * j := by group
      refine ⟨by rw [hx']; exact J.mul_mem (J.mul_mem (J.inv_mem hj) hx) hj,
        Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
      have hw' : j * w * j⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hJW hj) w).mp hw
      have := Subgroup.mem_centralizer_iff.mp hxc _ hw'
      calc w * x = j⁻¹ * ((j * w * j⁻¹) * (j * x * j⁻¹)) * j := by group
        _ = j⁻¹ * ((j * x * j⁻¹) * (j * w * j⁻¹)) * j := by rw [this]
        _ = x * w := by group
  have hmn := hNn.map (QuotientGroup.mk' (CFSG.pCore 2 ↥J)) (QuotientGroup.mk'_surjective _)
  rcases @normal_le_center_or_eq_top' _ _ hq _ hmn with h | h
  · exact h
  · exfalso
    apply hK.2.2.2.2.1.ne
    refine le_antisymm inf_le_left fun u hu => ⟨hu, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro k hk
    obtain ⟨n, hnN, hn⟩ : QuotientGroup.mk (⟨k, hKJ hk⟩ : ↥J) ∈
        ((J ⊓ Subgroup.centralizer (W : Set G)).subgroupOf J).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥J)) := h ▸ Subgroup.mem_top _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at hn
    have hq' : (n : G)⁻¹ * k ∈ pCoreOf 2 J := mem_blockQ_of_mem_pCore hn
    have hk' : k = n * ((n : G)⁻¹ * k) := by group
    have huW : u ∈ W := le_conjClosure _ J hu
    have h1 : ((n : G)⁻¹ * k) * u = u * ((n : G)⁻¹ * k) :=
      (commute_blockU_of_pCoreOf hK hKJ hQK hq' u hu).symm
    have h2 : (n : G) * u = u * n := (Subgroup.mem_centralizer_iff.mp hnN.2 u huW).symm
    rw [hk', mul_assoc, h1, ← mul_assoc, h2, mul_assoc]

theorem center_le_pCoreOf (hK : IsShort2 K) (hKJ : K ≤ J)
    (hQK : pCoreOf 2 J ≤ Subgroup.normalizer (K : Set G)) (hUQ : blockU K ≤ pCoreOf 2 J)
    (hZ : blockZ K = ⊥) (hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J))
    (hO : CFSG.pCore 2 (↥J ⧸ CFSG.pCore 2 ↥J) = ⊥) :
    K ⊓ Subgroup.centralizer (K : Set G) ≤ pCoreOf 2 J := by
  intro z hz
  have hzW : z ∈ J ⊓ Subgroup.centralizer (conjClosure (blockU K) J : Set G) :=
    ⟨hKJ hz.1, Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (commute_of_mem_center hK hKJ hQK hUQ hZ hz.1 hz.2 hw).symm⟩
  have hc := map_centralizer_le_center hK hKJ hQK hq ⟨⟨z, hKJ hz.1⟩, hzW, rfl⟩
  have hodd := A36A.odd_card_center hO
  have hQ2 : IsPGroup 2 (blockQ K) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 K
  obtain ⟨n, hn⟩ := hQ2 ⟨z, inf_centralizer_le_blockQ hK hz⟩
  have hzn : z ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  set y : ↥J ⧸ CFSG.pCore 2 ↥J := QuotientGroup.mk' (CFSG.pCore 2 ↥J) ⟨z, hKJ hz.1⟩ with hy
  have hy1 : orderOf y ∣ 2 ^ n := by
    apply orderOf_dvd_of_pow_eq_one
    rw [hy, ← map_pow]
    have : (⟨z, hKJ hz.1⟩ : ↥J) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hzn)
    rw [this, map_one]
  have hy2 : orderOf y ∣ Nat.card (Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J)) := by
    have := orderOf_dvd_natCard (⟨y, hc⟩ : ↥(Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J)))
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime (2 ^ n) (Nat.card (Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J))) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hodd)
  have hy3 : orderOf y = 1 := Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd hy1 hy2)
  rw [orderOf_eq_one_iff, hy, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy3
  exact mem_blockQ_of_mem_pCore hy3

omit [Finite G] in
theorem isAlt_range (hKJ : K ≤ J) (h5 : IsAltType K 5) (hQQ : blockQ K ≤ pCoreOf 2 J) :
    IsAlt 5 ↥(fK hKJ).range := by
  obtain ⟨α, hα, hαk, -⟩ := h5
  have hker : (fK hKJ).rangeRestrict.ker = α.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h
      have h' : fK hKJ x = 1 := by simpa using congrArg Subtype.val h
      rw [← MonoidHom.mem_ker, hαk]
      exact mem_pCore_of_mem_blockQ (fK_ker_le hKJ x h')
    · intro h
      rw [← MonoidHom.mem_ker, hαk] at h
      apply Subtype.ext
      simpa using (fK_eq_one_iff hKJ x).mpr (hQQ (mem_blockQ_of_mem_pCore h))
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective _
    (fK hKJ).rangeRestrict_surjective).symm.trans (QuotientGroup.quotientMulEquivOfEq hker)).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)⟩

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4
