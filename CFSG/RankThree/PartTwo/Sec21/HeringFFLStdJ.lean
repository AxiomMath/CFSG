module

public import CFSG.RankThree.PartTwo.Sec21.HeringFFPaperReduce
public import CFSG.RankThree.PartTwo.Sec21.HeringFFLTransfer
public import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

private theorem comm_of_isPGroup_of_cyclic_sylow {H : Type} [Group H] [Finite H]
    (hS : ∀ P : Sylow 3 H, IsCyclic ↥(P : Subgroup H)) {R : Subgroup H} (hR : IsPGroup 3 R)
    {r s : H} (hr : r ∈ R) (hs : s ∈ R) : r * s = s * r := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hRP⟩ := hR.exists_le_sylow
  haveI := hS P
  exact congrArg Subtype.val
    ((inferInstance : IsMulCommutative ↥(P : Subgroup H)).is_comm.comm ⟨r, hRP hr⟩ ⟨s, hRP hs⟩)

private theorem mem_zpowers_of_cyclic_sylow {H : Type} [Group H] [Finite H]
    (hS : ∀ P : Sylow 3 H, IsCyclic ↥(P : Subgroup H)) {u v : H} (hu3 : u ^ 3 = 1)
    (hu1 : u ≠ 1) (hv3 : v ^ 3 = 1) (hv1 : v ≠ 1) (huv : Commute u v) :
    u ∈ Subgroup.zpowers v := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hou : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hov : orderOf v = 3 := orderOf_eq_prime hv3 hv1
  have hzu : IsPGroup 3 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hou, pow_one])
  have hzv : IsPGroup 3 (Subgroup.zpowers v) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hov, pow_one])
  have hle : Subgroup.zpowers u ≤
      Subgroup.normalizer ((Subgroup.zpowers v : Subgroup H) : Set H) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    rintro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact huv.symm.zpow_left k
  obtain ⟨P, hP⟩ := (IsPGroup.to_sup_of_normal_right' hzu hzv hle).exists_le_sylow
  haveI := hS P
  have hmu : u ∈ (P : Subgroup H) := hP (Subgroup.mem_sup_left (Subgroup.mem_zpowers u))
  have hmv : v ∈ (P : Subgroup H) := hP (Subgroup.mem_sup_right (Subgroup.mem_zpowers v))
  have hu' : orderOf (⟨u, hmu⟩ : (P : Subgroup H)) = 3 := by
    rw [Subgroup.orderOf_mk, hou]
  have hv' : orderOf (⟨v, hmv⟩ : (P : Subgroup H)) = 3 := by
    rw [Subgroup.orderOf_mk, hov]
  have heq : Subgroup.zpowers (⟨u, hmu⟩ : (P : Subgroup H)) =
      Subgroup.zpowers (⟨v, hmv⟩ : (P : Subgroup H)) :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr (by rw [Nat.card_zpowers, Nat.card_zpowers, hu', hv'])
  have hmem : (⟨u, hmu⟩ : (P : Subgroup H)) ∈
      Subgroup.zpowers (⟨v, hmv⟩ : (P : Subgroup H)) := by
    rw [← heq]
    exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem ffStandardJL5_of_cyc (hcyc : FFCentCyclic) : FFStandardJL5 := by
  intro G _ _ A a X hpt h5 hXq hN
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAab := hpt.mem_S.1.1
  have ha3 : a ^ 3 = 1 := hAab.2 a hpt.mem
  have ha1 : a ≠ 1 := hpt.ne_one
  have hXC : X ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hpt.mem_theta
  have hcyc' := hcyc G A a X hpt (Or.inr (Or.inl h5)) hXq hN
  have hXnorm : (X.subgroupOf (Subgroup.centralizer ({a} : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXC).mpr hN
  have hXcomp : CFSG.IsComponent (X.subgroupOf (Subgroup.centralizer ({a} : Set G))) :=
    ⟨CFSG.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hXC) hXq,
      hXnorm.isSubnormal⟩
  unfold FFStandardJ
  set Cc : Subgroup G := Subgroup.centralizer ({a} : Set G)
  set D : Subgroup G := Subgroup.centralizer (X : Set G)
  refine ⟨hXC, hXcomp, fun K hK h3K => ?_⟩
  rcases CFSG.LocalCores.distinct_components_commute hK hXcomp with h | hcomm
  · exact h
  exfalso
  have hcomm' : ∀ k ∈ K, ∀ y ∈ X.subgroupOf Cc, y * k = k * y := fun k hk y hy =>
    Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hk) y hy
  have hKD : ∀ k ∈ K, ((k : ↥Cc) : G) ∈ D := by
    intro k hk
    refine Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_)
    have hy' : (⟨y, hXC hy⟩ : ↥Cc) ∈ X.subgroupOf Cc := Subgroup.mem_subgroupOf.mpr hy
    exact congrArg Subtype.val (hcomm' k hk ⟨y, hXC hy⟩ hy')
  obtain ⟨xK, hxK⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 3 h3K
  set x : G := ((xK : ↥Cc) : G) with hxdef
  have hxD : x ∈ D := hKD xK.1 xK.2
  have hxa : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.mp xK.1.2
  have hx3 : x ^ 3 = 1 := by
    have h := pow_orderOf_eq_one xK
    rw [hxK] at h
    simpa [hxdef] using congrArg (fun z : ↥K => ((z : ↥Cc) : G)) h
  have hx1 : x ≠ 1 := by
    intro h
    have h' : xK = 1 := Subtype.ext (Subtype.ext (by simpa [hxdef] using h))
    rw [h', orderOf_one] at hxK
    norm_num at hxK
  have haCc : a ∈ Cc := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have haD : a ∈ D := by
    refine Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hXC hy)
  have hcommA : Commute (⟨a, haD⟩ : ↥D) (⟨x, hxD⟩ : ↥D) := by
    show (⟨a, haD⟩ : ↥D) * ⟨x, hxD⟩ = ⟨x, hxD⟩ * ⟨a, haD⟩
    exact Subtype.ext hxa.symm
  have hu3 : (⟨a, haD⟩ : ↥D) ^ 3 = 1 := Subtype.ext (by simpa using ha3)
  have hu1 : (⟨a, haD⟩ : ↥D) ≠ 1 := fun h => ha1 (by simpa using congrArg Subtype.val h)
  have hv3 : (⟨x, hxD⟩ : ↥D) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have hv1 : (⟨x, hxD⟩ : ↥D) ≠ 1 := fun h => hx1 (by simpa using congrArg Subtype.val h)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (mem_zpowers_of_cyclic_sylow hcyc' hu3 hu1 hv3 hv1 hcommA)
  have hxk : x ^ k = a := by simpa using congrArg Subtype.val hk
  have haK : (⟨a, haCc⟩ : ↥Cc) ∈ K := by
    have he : (⟨a, haCc⟩ : ↥Cc) = (xK : ↥Cc) ^ k :=
      Subtype.ext (by simpa [hxdef] using hxk.symm)
    rw [he]
    exact zpow_mem xK.2 k
  have haK3 : (⟨⟨a, haCc⟩, haK⟩ : ↥K) ^ 3 = 1 :=
    Subtype.ext (Subtype.ext (by simpa using ha3))
  have haK1 : (⟨⟨a, haCc⟩, haK⟩ : ↥K) ≠ 1 := fun h =>
    ha1 (by simpa using congrArg (fun z : ↥K => ((z : ↥Cc) : G)) h)
  have haKc : (⟨⟨a, haCc⟩, haK⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp g.1.2
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥K) := inferInstance
  have hPab : ∀ y ∈ (P : Subgroup ↥K), ∀ z ∈ (P : Subgroup ↥K), y * z = z * y := by
    let φ : ↥K →* ↥D := (Cc.subtype.comp K.subtype).codRestrict D (fun k => hKD k.1 k.2)
    have hφ : Function.Injective φ := fun u v huv =>
      Subtype.ext (Subtype.ext (congrArg (fun z : ↥D => (z : G)) huv))
    have hR : IsPGroup 3 ((P : Subgroup ↥K).map φ) := P.isPGroup'.map φ
    intro y hy z hz
    apply hφ
    rw [map_mul, map_mul]
    exact comm_of_isPGroup_of_cyclic_sylow hcyc' hR (Subgroup.mem_map_of_mem φ hy)
      (Subgroup.mem_map_of_mem φ hz)
  have hz1 := eq_one_of_mem_center_of_abelian_sylow hK.1.1 P hPab haKc haK3
  exact haK1 hz1

end CFSG.RankThree.PartTwo.Sec21
