module

public import CFSG.RankThree.PartTwo.KFacts.K72Lift
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.RankThree.PartTwo.Sec11.Notation
public import CFSG.RankThree.PartTwo.Sec6.Item612Basic

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem not_three_dvd_card_inSubgroup_theta (L : Subgroup G) :
    ¬ 3 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) L) := by
  rw [inSubgroup, Subgroup.card_map_of_injective L.subtype_injective]
  exact (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1

theorem exists_lift_of_fixed {L : Subgroup G} {x : G} (hxN : x ∈ Subgroup.normalizer (L : Set G))
    (hx3 : x ^ 3 = 1) (y : L)
    (hy : Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)
      (y : L ⧸ aschbacherSolvableCore 3 L) = (y : L ⧸ aschbacherSolvableCore 3 L)) :
    ∃ z : L, (z : L ⧸ aschbacherSolvableCore 3 L) = (y : L ⧸ aschbacherSolvableCore 3 L) ∧
      x * (z : G) = (z : G) * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ' := inSubgroup (aschbacherSolvableCore 3) L with hθ'
  have hθ3 := not_three_dvd_card_inSubgroup_theta L
  have hθL : θ' ≤ L := Subgroup.map_subtype_le _
  have hX3 : IsPGroup 3 (Subgroup.zpowers x) := by
    intro g
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    rw [pow_one, Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hx3, one_zpow, Subgroup.coe_one]
  have hxθ : x ∈ Subgroup.normalizer (θ' : Set G) := Sec6.normalizer_le_normalizer_theta L hxN
  have hXθ : Subgroup.zpowers x ≤ Subgroup.normalizer (θ' : Set G) :=
    Subgroup.zpowers_le.mpr hxθ
  rw [Sec4.thetaQuotMulAut_mk, QuotientGroup.eq] at hy
  obtain ⟨s', hs', hs'eq⟩ : (x * (y : G)⁻¹ * x⁻¹ * (y : G)) ∈ θ' := by
    refine ⟨_, hy, ?_⟩
    rw [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
    change (x * (y : G) * x⁻¹)⁻¹ * (y : G) = _
    group
  set s := x * (y : G)⁻¹ * x⁻¹ * (y : G) with hs
  have hsθ : s ∈ θ' := ⟨s', hs', hs'eq⟩
  have hyx : (y : G)⁻¹ * x * (y : G) = s⁻¹ * x := by rw [hs]; group
  have hconj : ∀ z ∈ Subgroup.zpowers x, (y : G)⁻¹ * z * ((y : G)⁻¹)⁻¹ ∈
      Subgroup.zpowers x ⊔ θ' := by
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← conj_zpow, inv_inv, hyx]
    refine Subgroup.zpow_mem _ ?_ k
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.inv_mem _ hsθ))
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
  obtain ⟨t, ht, htN, -⟩ := KFacts.exists_mul_mem_normalizer hX3 hθ3 hXθ hconj
  set w := t * (y : G)⁻¹ with hw
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp
    ((Subgroup.mem_normalizer_iff.mp htN x).mp (Subgroup.mem_zpowers x))
  have hwx : w * x * w⁻¹ * x⁻¹ ∈ θ' := by
    have h1 : w * x * w⁻¹ * x⁻¹ = t * (s⁻¹ * (x * t⁻¹ * x⁻¹)) := by
      rw [hw, show t * (y : G)⁻¹ * x * (t * (y : G)⁻¹)⁻¹ * x⁻¹ =
        t * ((y : G)⁻¹ * x * (y : G)) * t⁻¹ * x⁻¹ by group, hyx]
      group
    rw [h1]
    exact Subgroup.mul_mem _ ht (Subgroup.mul_mem _ (Subgroup.inv_mem _ hsθ)
      ((Subgroup.mem_normalizer_iff.mp hxθ _).mp (Subgroup.inv_mem _ ht)))
  have hm1 : x ^ m * x⁻¹ = 1 := by
    have h2 : x ^ m * x⁻¹ ∈ Subgroup.zpowers x ⊓ θ' := by
      refine ⟨Subgroup.mul_mem _ (Subgroup.zpow_mem_zpowers x m)
        (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)), ?_⟩
      rw [hm]
      exact hwx
    rw [KFacts.inf_eq_bot_of_coprime hX3 hθ3, Subgroup.mem_bot] at h2
    exact h2
  have hwxc : w * x = x * w := by
    have h3 : w * x * w⁻¹ = x := by rw [← hm]; exact mul_inv_eq_one.mp hm1
    calc w * x = w * x * w⁻¹ * w := by group
      _ = x * w := by rw [h3]
  have hzL : w⁻¹ ∈ L := by
    rw [hw, mul_inv_rev, inv_inv]
    exact L.mul_mem y.2 (L.inv_mem (hθL ht))
  refine ⟨⟨w⁻¹, hzL⟩, ?_, ?_⟩
  · rw [QuotientGroup.eq]
    obtain ⟨t', ht', ht'eq⟩ := ht
    have : (⟨w⁻¹, hzL⟩ : L)⁻¹ * y = t' := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      change (w⁻¹)⁻¹ * (y : G) = L.subtype t'
      rw [ht'eq, inv_inv, hw]
      group)
    rw [this]
    exact ht'
  · show x * w⁻¹ = w⁻¹ * x
    calc x * w⁻¹ = w⁻¹ * (w * x) * w⁻¹ := by group
      _ = w⁻¹ * (x * w) * w⁻¹ := by rw [hwxc]
      _ = w⁻¹ * x := by group

theorem eq_bot_of_normal_solvable_of_isQuasisimple {Q : Type*} [Group Q] (hQ : IsQuasisimple Q)
    (hZ : Subgroup.center Q = ⊥) (N : Subgroup Q) [N.Normal] (hN : Group.IsSolvable N) :
    N = ⊥ := by
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hQ N with h | h
  · rwa [hZ, le_bot_iff] at h
  · exfalso
    obtain ⟨-, hsimple, a, b, hab⟩ := hQ
    have hQs : Group.IsSolvable Q := by
      have e : N ≃* Q := (MulEquiv.subgroupCongr h).trans Subgroup.topEquiv
      exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
    have : Group.IsSolvable (Q ⧸ Subgroup.center Q) := inferInstance
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr this a b)

@[expose] noncomputable def cMap (L : Subgroup G) (x : G) :
    (L ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) →* L ⧸ aschbacherSolvableCore 3 L :=
  (QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp (Subgroup.inclusion inf_le_left)

omit [Finite G] in
theorem sec11K_le (L : Subgroup G) (x : G) : sec11K L x ≤ L :=
  (Subgroup.map_subtype_le _).trans inf_le_left

@[expose] noncomputable def kMap (L : Subgroup G) (x : G) :
    (sec11K L x : Subgroup G) →* L ⧸ aschbacherSolvableCore 3 L :=
  (QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp (Subgroup.inclusion (sec11K_le L x))

theorem range_cMap {L : Subgroup G} {x : G} (hxN : x ∈ Subgroup.normalizer (L : Set G))
    (hx3 : x ^ 3 = 1) : (cMap L x).range =
      (Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
        (MonoidHom.id _) := by
  ext q
  constructor
  · rintro ⟨m, rfl⟩
    change Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)
      ((Subgroup.inclusion inf_le_left m : L) : L ⧸ aschbacherSolvableCore 3 L) = _
    rw [Sec4.thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    change x * (m : G) * x⁻¹ = (m : G)
    rw [← (Subgroup.mem_centralizer_singleton_iff.mp m.2.2), mul_inv_cancel_right]
  · intro hq
    induction q using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨z, hz, hzx⟩ := exists_lift_of_fixed hxN hx3 y hq
      refine ⟨⟨z, z.2, Subgroup.mem_centralizer_singleton_iff.mpr hzx.symm⟩, ?_⟩
      exact hz

omit [Finite G] in
theorem range_kMap (L : Subgroup G) (x : G) :
    (kMap L x).range = (perfectResidual ↥(L ⊓ Subgroup.centralizer ({x} : Set G))).map
      (cMap L x) := by
  ext q
  constructor
  · rintro ⟨⟨k, p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨_, p, hp, rfl⟩, rfl⟩

theorem range_kMap_eq {L : Subgroup G} {x : G} (hxN : x ∈ Subgroup.normalizer (L : Set G))
    (hx3 : x ^ 3 = 1)
    (hperf : Group.IsPerfect
      ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L)))) :
    (kMap L x).range = (cMap L x).range := by
  rw [range_kMap, (CFSG.perfect_residual_transport (cMap L x)).1]
  rw [← range_cMap hxN hx3] at hperf
  exact inSubgroup_perfectResidual_of_isPerfect hperf

omit [Finite G] in
@[expose] def sectionCentralizerSubgroup (A X Y : Subgroup G)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hAY : A ≤ Subgroup.normalizer (Y : Set G)) :
    Subgroup G where
  carrier := Late.sectionCentralizer A X Y
  mul_mem' := by
    rintro z₁ z₂ ⟨h₁A, h₁⟩ ⟨h₂A, h₂⟩
    refine ⟨A.mul_mem h₁A h₂A, fun y hy => ?_⟩
    have e : z₁ * z₂ * y * (z₁ * z₂)⁻¹ * y⁻¹ =
        z₁ * (z₂ * y * z₂⁻¹ * y⁻¹) * z₁⁻¹ * (z₁ * y * z₁⁻¹ * y⁻¹) := by group
    rw [e]
    exact Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAY h₁A) _).mp (h₂ y hy)) (h₁ y hy)
  one_mem' := ⟨A.one_mem, fun y _ => by simp⟩
  inv_mem' := by
    rintro z ⟨hzA, hz⟩
    refine ⟨A.inv_mem hzA, fun y hy => ?_⟩
    have hy' : z⁻¹ * y * z⁻¹⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hAX (A.inv_mem hzA)) y).mp hy
    have h1 := Y.inv_mem (hz _ hy')
    have e : (z * (z⁻¹ * y * z⁻¹⁻¹) * z⁻¹ * (z⁻¹ * y * z⁻¹⁻¹)⁻¹)⁻¹ = z⁻¹ * y * z⁻¹⁻¹ * y⁻¹ := by
      group
    rwa [e] at h1

omit [Finite G] in
theorem mem_sectionCentralizerSubgroup {A X Y : Subgroup G}
    {hAX : A ≤ Subgroup.normalizer (X : Set G)} {hAY : A ≤ Subgroup.normalizer (Y : Set G)}
    {z : G} : z ∈ sectionCentralizerSubgroup A X Y hAX hAY ↔ z ∈ Late.sectionCentralizer A X Y :=
  Iff.rfl

omit [Finite G] in
theorem kMap_eq_one_iff {L : Subgroup G} {x : G} (k : sec11K L x) :
    kMap L x k = 1 ↔ (k : G) ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  rw [kMap, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨_, h, rfl⟩
  · rintro ⟨t, ht, hteq⟩
    have : Subgroup.inclusion (sec11K_le L x) k = t := Subtype.ext hteq.symm
    rw [this]
    exact ht

theorem mem_sec11K_of_pow_eq_one {L : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1)
    (hperf : Group.IsPerfect
      ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))))
    {m : G} (hm : m ∈ L ⊓ Subgroup.centralizer ({x} : Set G)) {k : ℕ} (hk : m ^ 3 ^ k = 1) :
    m ∈ sec11K L x := by
  set M := L ⊓ Subgroup.centralizer ({x} : Set G) with hM
  set P := perfectResidual ↥M with hP
  have h1 : cMap L x ⟨m, hm⟩ ∈ P.map (cMap L x) := by
    rw [← range_kMap, range_kMap_eq hxN hx3 hperf]
    exact ⟨_, rfl⟩
  obtain ⟨p, hp, hpm⟩ := h1
  set q := QuotientGroup.mk' P with hq
  have hqp : q p = 1 := by
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hp
  have hqm : q ⟨m, hm⟩ = q (p⁻¹ * ⟨m, hm⟩) := by
    rw [map_mul, map_inv, hqp, inv_one, one_mul]
  have hker : cMap L x (p⁻¹ * ⟨m, hm⟩) = 1 := by
    rw [map_mul, map_inv, hpm, inv_mul_cancel]
  have hθ : ((p⁻¹ * ⟨m, hm⟩ : M) : G) ∈ inSubgroup (aschbacherSolvableCore 3) L := by
    rw [cMap, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hker
    exact ⟨_, hker, rfl⟩
  have h2 : orderOf (q ⟨m, hm⟩) ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) L) := by
    rw [hqm]
    refine (orderOf_map_dvd q _).trans ?_
    rw [← Subgroup.orderOf_coe]
    exact Subgroup.orderOf_dvd_natCard _ hθ
  have h3 : orderOf (q ⟨m, hm⟩) ∣ 3 ^ k := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← map_pow, show (⟨m, hm⟩ : M) ^ 3 ^ k = 1 from Subtype.ext (by simpa using hk), map_one]
  have hcop : Nat.Coprime (3 ^ k) (Nat.card (inSubgroup (aschbacherSolvableCore 3) L)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (not_three_dvd_card_inSubgroup_theta L))
  have h4 := Nat.eq_one_of_dvd_coprimes hcop h3 h2
  rw [orderOf_eq_one_iff, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h4
  exact ⟨_, h4, rfl⟩

theorem le_ker_kMap_of_normal_solvable {L : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1)
    (hQ : IsQuasisimple ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
      (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))))
    (hZ : Subgroup.center ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
      (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))) = ⊥)
    (N : Subgroup (sec11K L x)) [N.Normal] (hNs : Group.IsSolvable N) : N ≤ (kMap L x).ker := by
  set F := (Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
    (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L)) with hF
  have hrange : (kMap L x).range = F := by
    rw [range_kMap_eq hxN hx3 hQ.1, range_cMap hxN hx3]
  have hmem : ∀ k, kMap L x k ∈ F := fun k => hrange ▸ ⟨k, rfl⟩
  set ψ : sec11K L x →* F := (kMap L x).codRestrict F hmem with hψ
  have hψs : Function.Surjective ψ := by
    rintro ⟨f, hf⟩
    rw [← hrange] at hf
    obtain ⟨k, hk⟩ := hf
    exact ⟨k, Subtype.ext hk⟩
  have hMn : (N.map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψs
  have hMs : Group.IsSolvable (N.map ψ) :=
    Group.isSolvable_of_surjective (ψ.subgroupMap_surjective N)
  have hbot := eq_bot_of_normal_solvable_of_isQuasisimple hQ hZ (N.map ψ) hMs
  intro k hk
  have h1 : ψ k ∈ N.map ψ := ⟨k, hk, rfl⟩
  rw [hbot, Subgroup.mem_bot] at h1
  rw [MonoidHom.mem_ker]
  exact congrArg Subtype.val h1

theorem isSolvable_inSubgroup_theta (Y : Subgroup G) :
    Group.IsSolvable (inSubgroup (aschbacherSolvableCore 3) Y) := by
  have := (solvable_prime_complement_core_characterization (H := Y) Nat.prime_three).1
  exact Group.isSolvable_of_surjective ((Y.subtype).subgroupMap_surjective _)

theorem eq_one_of_mem_inSubgroup_theta {L : Subgroup G} {z : G}
    (hz : z ∈ inSubgroup (aschbacherSolvableCore 3) L) (hz3 : z ^ 3 = 1) : z = 1 := by
  have h1 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
  have h2 := Subgroup.orderOf_dvd_natCard _ hz
  have hcop : Nat.Coprime 3 (Nat.card (inSubgroup (aschbacherSolvableCore 3) L)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (not_three_dvd_card_inSubgroup_theta L)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem mem_theta_of_mem_sectionCentralizer_of_le {L Y A : Subgroup G} {x z : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1)
    (hQ : IsQuasisimple ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
      (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))))
    (hZ : Subgroup.center ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
      (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))) = ⊥)
    (hKY : sec11K L x ≤ Y) (hzK : z ∈ Subgroup.normalizer (sec11K L x : Set G))
    (hz : z ∈ Late.sectionCentralizer A Y (inSubgroup (aschbacherSolvableCore 3) Y)) :
    ∀ k ∈ sec11K L x, z * k * z⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  set θY := inSubgroup (aschbacherSolvableCore 3) Y with hθY
  set N₀ : Subgroup (sec11K L x) := θY.subgroupOf (sec11K L x) with hN₀
  have hN₀n : N₀.Normal := by
    constructor
    intro n hn k
    rw [hN₀, Subgroup.mem_subgroupOf] at hn ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta Y (hKY k.2)) _).mp hn
  have hN₀s : Group.IsSolvable N₀ := by
    have := isSolvable_inSubgroup_theta Y
    set f : N₀ →* θY :=
      ((sec11K L x).subtype.comp N₀.subtype).codRestrict θY fun n => n.2 with hf
    have hfinj : Function.Injective f := fun a b hab => by
      have h := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h)
    exact Group.isSolvable_of_isSolvable_injective hfinj
  have hle := le_ker_kMap_of_normal_solvable hxN hx3 hQ hZ N₀ hN₀s
  intro k hk
  have hzk : z * k * z⁻¹ * k⁻¹ ∈ sec11K L x :=
    (sec11K L x).mul_mem ((Subgroup.mem_normalizer_iff.mp hzK k).mp hk)
      ((sec11K L x).inv_mem hk)
  have hmem : (⟨_, hzk⟩ : sec11K L x) ∈ N₀ := by
    rw [hN₀, Subgroup.mem_subgroupOf]
    exact hz.2 k (hKY hk)
  have := (kMap_eq_one_iff _).mp (hle hmem)
  exact this

theorem eq_one_of_forall_mem_theta {L : Subgroup G} {x z : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1)
    (hQ : IsQuasisimple ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
      (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))))
    (hZ : Subgroup.center ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
      (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))) = ⊥)
    (hzK : z ∈ sec11K L x) (hz3 : z ^ 3 = 1)
    (hz : ∀ k ∈ sec11K L x, z * k * z⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L) :
    z = 1 := by
  set F := (Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
    (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L)) with hF
  have hrange : (kMap L x).range = F := by
    rw [range_kMap_eq hxN hx3 hQ.1, range_cMap hxN hx3]
  have hmem : ∀ k, kMap L x k ∈ F := fun k => hrange ▸ ⟨k, rfl⟩
  have hcen : (⟨kMap L x ⟨z, hzK⟩, hmem _⟩ : F) ∈ Subgroup.center F := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨f, hf⟩
    rw [← hrange] at hf
    obtain ⟨k, rfl⟩ := hf
    apply Subtype.ext
    have h1 := (kMap_eq_one_iff (⟨z * k * z⁻¹ * k⁻¹, (sec11K L x).mul_mem
      ((sec11K L x).mul_mem ((sec11K L x).mul_mem hzK k.2) ((sec11K L x).inv_mem hzK))
      ((sec11K L x).inv_mem k.2)⟩ : sec11K L x)).mpr (hz k k.2)
    have e : (⟨z * k * z⁻¹ * k⁻¹, (sec11K L x).mul_mem
      ((sec11K L x).mul_mem ((sec11K L x).mul_mem hzK k.2) ((sec11K L x).inv_mem hzK))
      ((sec11K L x).inv_mem k.2)⟩ : sec11K L x) = ⟨z, hzK⟩ * k * ⟨z, hzK⟩⁻¹ * k⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    show kMap L x k * kMap L x ⟨z, hzK⟩ = kMap L x ⟨z, hzK⟩ * kMap L x k
    calc kMap L x k * kMap L x ⟨z, hzK⟩ = (kMap L x ⟨z, hzK⟩ * kMap L x k *
          (kMap L x ⟨z, hzK⟩)⁻¹ * (kMap L x k)⁻¹)⁻¹ * (kMap L x ⟨z, hzK⟩ * kMap L x k) := by
          group
      _ = kMap L x ⟨z, hzK⟩ * kMap L x k := by rw [h1, inv_one, one_mul]
  rw [hZ, Subgroup.mem_bot] at hcen
  have h2 : kMap L x ⟨z, hzK⟩ = 1 := congrArg Subtype.val hcen
  rw [kMap_eq_one_iff] at h2
  exact eq_one_of_mem_inSubgroup_theta h2 hz3

end CFSG.RankThree.PartTwo.Sec11
