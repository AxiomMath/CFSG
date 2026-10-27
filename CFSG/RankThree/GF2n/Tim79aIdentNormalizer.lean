module

public import CFSG.RankThree.GF2n.Tim79aIdentCore
public import CFSG.StronglyEmbedded.BenderCentre

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

namespace MinCex

variable {M V Q P H : Subgroup G} [Finite G]

theorem mem_normalizer_Vy_of_tilde (hc : MinCex M V Q P H) (hd : Sec23Data V H)
    {b : Xbar V H}
    (hb : projZ V H b ∈ Subgroup.normalizer (VZ V H : Set (XbarZ V H))) :
    b ∈ Subgroup.normalizer (Vy V H : Set (Xbar V H)) := by
  rw [mem_normalizer_iff_conjSubgroup_eq]
  have hle : conjSubgroup b (Vy V H) ≤ Vy V H := by
    intro v' hv'
    have hv : b⁻¹ * v' * b ∈ Vy V H := mem_conjSubgroup.mp hv'
    set v := b⁻¹ * v' * b with hvdef
    have hv'eq : v' = b * v * b⁻¹ := by rw [hvdef]; group
    by_cases hv1 : v = 1
    · rw [hv'eq, hv1]
      simp
    have hvD : v ∈ Dy V H := hc.barOf_V_subset_dbarOf (Subgroup.mem_subgroupOf.mp hv)
      (fun h => hv1 (Subtype.ext h))
    have hv'D : v' ∈ Dy V H := by
      rw [hv'eq]
      exact conj_mem_Dy hd hvD b
    have hmem : projZ V H v' ∈ VZ V H := by
      have h1 : projZ V H v ∈ VZ V H := ⟨v, hv, rfl⟩
      have h2 := (Subgroup.mem_normalizer_iff.mp hb (projZ V H v)).mp h1
      rw [hv'eq, map_mul, map_mul, map_inv]
      exact h2
    obtain ⟨u, hu, huv⟩ := hmem
    have hz : u⁻¹ * v' ∈ Subgroup.center (Xbar V H) := by
      have h1 : projZ V H (u⁻¹ * v') = 1 := by
        rw [map_mul, map_inv, huv]
        group
      exact (QuotientGroup.eq_one_iff _).mp h1
    by_cases hu1 : u = 1
    · exfalso
      rw [hu1, inv_one, one_mul] at hz
      exact hd.noncentral v' hv'D hz
    have huD : u ∈ Dy V H := hc.barOf_V_subset_dbarOf (Subgroup.mem_subgroupOf.mp hu)
      (fun h => hu1 (Subtype.ext h))
    have hz1 : u⁻¹ * v' = 1 :=
      noCentralTwist hd _ hz u huD (by rwa [mul_inv_cancel_left])
    have : v' = u := by
      rw [inv_mul_eq_one] at hz1
      exact hz1.symm
    rw [this]
    exact hu
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm.symm
  rw [card_conjSubgroup]


end MinCex

@[expose] def Rbar (V H P : Subgroup G) : Subgroup (Xbar V H) :=
  (barOf V H P).subgroupOf (barOf V H (xOf V H))

@[expose] def Rtilde (V H P : Subgroup G) : Subgroup (XbarZ V H) :=
  (Rbar V H P).map (projZ V H)

theorem mem_Rbar {V H P : Subgroup G} {r : Xbar V H} :
    r ∈ Rbar V H P ↔ (r : Hbar V H) ∈ barOf V H P := Subgroup.mem_subgroupOf

namespace MinCex

variable {M V Q P H : Subgroup G} [Finite G]

theorem Vy_le_Rbar (hc : MinCex M V Q P H) : Vy V H ≤ Rbar V H P := fun v hv =>
  mem_Rbar.mpr (barOf_mono hc.V_le_P (Subgroup.mem_subgroupOf.mp hv))

theorem isPGroup_Rbar (hc : MinCex M V Q P H) : IsPGroup 2 (Rbar V H P) := by
  intro r
  obtain ⟨p, hp, hpr⟩ := mem_barOf_iff.mp (mem_Rbar.mp r.2)
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hc.isPGroup_P ⟨(p : G), hp⟩
  refine ⟨k, ?_⟩
  have h0 : (⟨(p : G), hp⟩ : P) ^ 2 ^ k = 1 := by
    rw [← hk]
    exact pow_orderOf_eq_one _
  have h1 : (p : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val h0
  have h2 : p ^ 2 ^ k = 1 := Subtype.ext (by simpa using h1)
  apply Subtype.ext
  apply Subtype.ext
  simp only [Subgroup.coe_pow, OneMemClass.coe_one]
  rw [← hpr, ← map_pow, h2, map_one]

theorem commutator_mem_Rbar (hc : MinCex M V Q P H) {b : Xbar V H}
    (hb : b ∈ Subgroup.normalizer (Vy V H : Set (Xbar V H))) {p : Hbar V H}
    (hp : p ∈ barOf V H P) :
    ∃ r ∈ Rbar V H P, (r : Hbar V H) = (b : Hbar V H) * p * (b : Hbar V H)⁻¹ * p⁻¹ := by
  haveI := normal_barOf_xOf V H
  have hbN : (b : Hbar V H) ∈ Subgroup.normalizer (barOf V H V : Set (Hbar V H)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxX : x ∈ barOf V H (xOf V H) := barOf_V_le V H hx
      have := (Subgroup.mem_normalizer_iff.mp hb ⟨x, hxX⟩).mp (Subgroup.mem_subgroupOf.mpr hx)
      exact Subgroup.mem_subgroupOf.mp this
    · intro hx
      have hxX' : (b : Hbar V H) * x * (b : Hbar V H)⁻¹ ∈ barOf V H (xOf V H) :=
        barOf_V_le V H hx
      have hxX : x ∈ barOf V H (xOf V H) := by
        have h1 : (b : Hbar V H)⁻¹ * ((b : Hbar V H) * x * (b : Hbar V H)⁻¹) * (b : Hbar V H) ∈
            barOf V H (xOf V H) :=
          (barOf V H (xOf V H)).mul_mem ((barOf V H (xOf V H)).mul_mem
            ((barOf V H (xOf V H)).inv_mem b.2) hxX') b.2
        simpa [mul_assoc] using h1
      have := (Subgroup.mem_normalizer_iff.mpr (fun y => (Subgroup.mem_normalizer_iff.mp hb y)))
      have h2 := (Subgroup.mem_normalizer_iff.mp hb ⟨x, hxX⟩).mpr (Subgroup.mem_subgroupOf.mpr hx)
      exact Subgroup.mem_subgroupOf.mp h2
  rw [hc.normalizer_barOf_V] at hbN
  obtain ⟨m, hmN, hmb⟩ := mem_barOf_iff.mp hbN
  have hmP : (m : G) ∈ Subgroup.normalizer (P : Set G) :=
    hc.M_le_normalizer_P (hc.normalizer_eq ▸ hmN)
  obtain ⟨p', hp', hpp⟩ := mem_barOf_iff.mp hp
  have hxX : (b : Hbar V H) * p * (b : Hbar V H)⁻¹ * p⁻¹ ∈ barOf V H (xOf V H) := by
    have h1 : p * (b : Hbar V H)⁻¹ * p⁻¹ ∈ barOf V H (xOf V H) :=
      Subgroup.Normal.conj_mem inferInstance _ ((barOf V H (xOf V H)).inv_mem b.2) p
    have := (barOf V H (xOf V H)).mul_mem b.2 h1
    simpa [mul_assoc] using this
  have hxP : (b : Hbar V H) * p * (b : Hbar V H)⁻¹ * p⁻¹ ∈ barOf V H P := by
    refine mem_barOf_iff.mpr ⟨m * p' * m⁻¹ * p'⁻¹, ?_, ?_⟩
    · have h1 : (m : G) * p' * (m : G)⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hmP p').mp hp'
      simpa using P.mul_mem h1 (P.inv_mem hp')
    · simp only [map_mul, map_inv, hmb, hpp]
  exact ⟨⟨_, hxX⟩, mem_Rbar.mpr hxP, rfl⟩

end MinCex

theorem mem_normalizer_of_map_mem_normalizer {Y K : Type*} [Group Y] [Group K] [Finite Y]
    (π : Y →* K) (hker : π.ker ≤ Subgroup.center Y) (S : Sylow 2 Y) {y : Y}
    (hy : π y ∈ Subgroup.normalizer (((S : Subgroup Y).map π : Subgroup K) : Set K)) :
    y ∈ Subgroup.normalizer ((S : Subgroup Y) : Set Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSS : conjSubgroup y (S : Subgroup Y) ≤ (S : Subgroup Y) := by
    intro s' hs'
    have hs₀ : y⁻¹ * s' * y ∈ (S : Subgroup Y) := mem_conjSubgroup.mp hs'
    have hπ : π s' ∈ (S : Subgroup Y).map π := by
      have h1 : π (y⁻¹ * s' * y) ∈ (S : Subgroup Y).map π := ⟨_, hs₀, rfl⟩
      have h2 := (Subgroup.mem_normalizer_iff.mp hy (π (y⁻¹ * s' * y))).mp h1
      have e : π y * π (y⁻¹ * s' * y) * (π y)⁻¹ = π s' := by
        rw [map_mul, map_mul, map_inv]
        group
      rwa [e] at h2
    obtain ⟨s, hs, hss'⟩ := hπ
    set k := s⁻¹ * s' with hk
    have hkker : k ∈ π.ker := by
      rw [MonoidHom.mem_ker, hk, map_mul, map_inv, hss']
      group
    have hkc : k ∈ Subgroup.center Y := hker hkker
    have hSy : IsPGroup 2 ↥(conjSubgroup y (S : Subgroup Y)) :=
      (S : Sylow 2 Y).isPGroup'.of_equiv ((S : Subgroup Y).equivMapOfInjective
        (MulAut.conj y).toMonoidHom (MulAut.conj y).injective)
    obtain ⟨a, ha⟩ := hSy ⟨s', hs'⟩
    obtain ⟨b, hb⟩ := (S : Sylow 2 Y).isPGroup' ⟨s, hs⟩
    have ha' : s' ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    have hb' : s ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    have hs'N : s' ^ 2 ^ (a + b) = 1 := by rw [pow_add, pow_mul, ha', one_pow]
    have hsN : s ^ 2 ^ (a + b) = 1 := by
      rw [add_comm, pow_add, pow_mul, hb', one_pow]
    have hs'eq : s' = s * k := by rw [hk]; group
    have hcomm : Commute s k := Subgroup.mem_center_iff.mp hkc s
    have hkN : k ^ 2 ^ (a + b) = 1 := by
      have h1 : s' ^ 2 ^ (a + b) = s ^ 2 ^ (a + b) * k ^ 2 ^ (a + b) := by
        rw [hs'eq]
        exact hcomm.mul_pow _
      rw [hs'N, hsN, one_mul] at h1
      exact h1.symm
    have hz2 : IsPGroup 2 ↥(Subgroup.zpowers k) := by
      rintro ⟨x, hx⟩
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      refine ⟨a + b, Subtype.ext ?_⟩
      simp only [Subgroup.coe_pow, OneMemClass.coe_one]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hkN, one_zpow]
    have hsup : IsPGroup 2 ↥(Subgroup.zpowers k ⊔ (S : Subgroup Y)) :=
      IsPGroup.to_sup_of_normal_right' hz2 (S : Sylow 2 Y).isPGroup' (by
        rw [Subgroup.zpowers_le]
        exact Subgroup.center_le_normalizer ((S : Subgroup Y) : Set Y) hkc)
    have hkS : k ∈ (S : Subgroup Y) := by
      have := (S : Sylow 2 Y).is_maximal' hsup le_sup_right
      rw [← this]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers k)
    rw [hs'eq]
    exact (S : Subgroup Y).mul_mem hs hkS
  have heq : conjSubgroup y (S : Subgroup Y) = (S : Subgroup Y) :=
    Subgroup.eq_of_le_of_card_ge hSS (by rw [card_conjSubgroup])
  exact mem_normalizer_iff_conjSubgroup_eq.mpr heq

end CFSG.RankThree.GF2n.Tim79a

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.BenderSuzuki
open CFSG.StronglyEmbedded.BenderCentre
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter)
open scoped commutatorElement

variable {G : Type} [Group G]

theorem preimOf_mono {V H : Subgroup G} {S T : Subgroup (Hbar V H)} (h : S ≤ T) :
    preimOf V H S ≤ preimOf V H T := fun g hg => by
  obtain ⟨x, rfl, hx⟩ := mem_preimOf.mp hg
  exact mem_preimOf.mpr ⟨x, rfl, h hx⟩

namespace MinCex

variable {M V Q P H : Subgroup G} [Finite G]

theorem VZ_le_Rtilde (hc : MinCex M V Q P H) : VZ V H ≤ Rtilde V H P :=
  Subgroup.map_mono hc.Vy_le_Rbar

theorem isPGroup_Rtilde (hc : MinCex M V Q P H) : IsPGroup 2 (Rtilde V H P) :=
  (hc.isPGroup_Rbar).of_surjective ((projZ V H).subgroupMap (Rbar V H P))
    (MonoidHom.subgroupMap_surjective _ _)

theorem VZ_sq (hc : MinCex M V Q P H) {x : XbarZ V H} (hx : x ∈ VZ V H) : x * x = 1 := by
  have := hc.isElemAbelian_Vtilde.2 x hx
  rwa [pow_two] at this

theorem le_sylow_of_isPGroup (hc : MinCex M V Q P H) (hd : Sec23Data V H)
    (hBG : IsBenderGroup (XbarZ V H)) {S : Sylow 2 (XbarZ V H)}
    (hVS : VZ V H ≤ sylowCenter (S : Subgroup (XbarZ V H))) {T : Subgroup (XbarZ V H)}
    (hT : IsPGroup 2 T) (hVT : VZ V H ≤ T) : T ≤ (S : Subgroup (XbarZ V H)) := by
  obtain ⟨S', hTS'⟩ := IsPGroup.exists_le_sylow hT
  have hVS' : VZ V H ≤ sylowCenter (S' : Subgroup (XbarZ V H)) :=
    le_sylowCenter_of_sq_eq_one hBG (fun x hx => hTS' (hVT hx)) fun x hx => hc.VZ_sq hx
  have := sylow_eq_of_le_sylowCenter hBG (hc.Vtilde_ne_bot hd) hVS' hVS
  rw [← this]
  exact hTS'

@[expose] def Ugrp (V H P : Subgroup G) : Subgroup G :=
  preimOf V H ((Rbar V H P).map (barOf V H (xOf V H)).subtype)

theorem wOf_le_Ugrp (V H P : Subgroup G) : wOf V H ≤ Ugrp V H P := wOf_le_preimOf _ _ _

theorem barOf_Ugrp (V H P : Subgroup G) :
    barOf V H (Ugrp V H P) = (Rbar V H P).map (barOf V H (xOf V H)).subtype :=
  barOf_preimOf _ _ _

theorem exists_mul_of_mem_Ugrp {u : G} (hu : u ∈ Ugrp V H P) :
    ∃ p ∈ P, ∃ w ∈ wOf V H, u = p * w := by
  obtain ⟨h, rfl, hh⟩ := mem_preimOf.mp hu
  obtain ⟨r, hr, hrh⟩ := Subgroup.mem_map.mp hh
  obtain ⟨p, hp, hpr⟩ := mem_barOf_iff.mp (mem_Rbar.mp hr)
  have h1 : piBar V H (p⁻¹ * h) = 1 := by
    rw [map_mul, map_inv, hpr]
    simp only [Subgroup.coe_subtype] at hrh
    rw [hrh]
    group
  have h2 : ((p⁻¹ * h : ↥H) : G) ∈ wOf V H := (piBar_eq_one_iff _).1 h1
  refine ⟨(p : G), hp, _, h2, ?_⟩
  simp

theorem Ugrp_centralizes (hc : MinCex M V Q P H) {x u : G} (hx : x ∈ V ⊓ wOf V H)
    (hu : u ∈ Ugrp V H P) : x * u = u * x := by
  obtain ⟨p, hp, w, hw, rfl⟩ := exists_mul_of_mem_Ugrp hu
  have h1 : x * p = p * x := hc.commute_of_mem_P hp hx.1
  have h2 : x * w = w * x := hc.wOf_isElemAbelian.comm hx.2 hw
  calc x * (p * w) = (x * p) * w := by group
    _ = p * (x * w) := by rw [h1]; group
    _ = p * (w * x) := by rw [h2]
    _ = p * w * x := by group


end MinCex

end CFSG.RankThree.GF2n.Tim79a

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.BenderSuzuki
open CFSG.StronglyEmbedded.BenderCentre
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter)
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_normalizer_preimOf_of_mem_normalizer {V H : Subgroup G} (hVH : V ≤ H)
    {T : Subgroup (Hbar V H)} {x : ↥(xOf V H)}
    (hx : (xToXbar hVH x : Hbar V H) ∈ Subgroup.normalizer (T : Set (Hbar V H))) :
    (x : G) ∈ Subgroup.normalizer ((preimOf V H T : Subgroup G) : Set G) := by
  have key : ∀ (x : ↥(xOf V H)),
      (xToXbar hVH x : Hbar V H) ∈ Subgroup.normalizer (T : Set (Hbar V H)) →
      ∀ g ∈ preimOf V H T, (x : G) * g * (x : G)⁻¹ ∈ preimOf V H T := by
    intro x hb g hg
    obtain ⟨h, rfl, hh⟩ := mem_preimOf.mp hg
    set xH : ↥H := Subgroup.inclusion (xOf_le_H hVH) x with hxH
    refine mem_preimOf.mpr ⟨xH * h * xH⁻¹, by simp [hxH], ?_⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp hb (piBar V H h)).mp hh
    simpa [coe_xToXbar, hxH] using h1
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => key x hx g hg, fun hg => ?_⟩
  have hx' : (xToXbar hVH x⁻¹ : Hbar V H) ∈ Subgroup.normalizer (T : Set (Hbar V H)) := by
    rw [map_inv]
    exact Subgroup.inv_mem _ hx
  have := key x⁻¹ hx' _ hg
  simpa [mul_assoc] using this


theorem mem_normalizer_VZ_of_le_sylowCenter {V H : Subgroup G}
    {S : Subgroup (XbarZ V H)} (hVS : VZ V H ≤ sylowCenter S) {s : XbarZ V H} (hs : s ∈ S) :
    s ∈ Subgroup.normalizer (VZ V H : Set (XbarZ V H)) := by
  refine Subgroup.centralizer_le_normalizer _ ?_
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact ((mem_sylowCenter.mp (hVS hh)).2 s hs).symm

theorem isPGroup_map_subtype {V H : Subgroup G} (Sb : Sylow 2 (Xbar V H)) :
    IsPGroup 2 ((Sb : Subgroup (Xbar V H)).map (barOf V H (xOf V H)).subtype) := by
  intro y
  obtain ⟨y', hy', hyy⟩ := Subgroup.mem_map.mp y.2
  obtain ⟨k, hk⟩ := Sb.isPGroup' ⟨y', hy'⟩
  refine ⟨k, Subtype.ext ?_⟩
  have := congrArg (fun z : Sb => ((z : Xbar V H) : Hbar V H)) hk
  simp only [Subgroup.coe_pow, OneMemClass.coe_one] at this ⊢
  rw [← hyy]
  simpa using this

theorem mem_normalizer_map_subtype {V H : Subgroup G} {Sb : Subgroup (Xbar V H)}
    {b : Xbar V H} (hb : b ∈ Subgroup.normalizer (Sb : Set (Xbar V H))) :
    (b : Hbar V H) ∈
      Subgroup.normalizer ((Sb.map (barOf V H (xOf V H)).subtype : Subgroup (Hbar V H)) :
        Set (Hbar V H)) := by
  have key : ∀ b : Xbar V H, b ∈ Subgroup.normalizer (Sb : Set (Xbar V H)) →
      ∀ y ∈ Sb.map (barOf V H (xOf V H)).subtype, (b : Hbar V H) * y * (b : Hbar V H)⁻¹ ∈
        Sb.map (barOf V H (xOf V H)).subtype := by
    intro b hb y hy
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_map.mpr ⟨b * y' * b⁻¹, (Subgroup.mem_normalizer_iff.mp hb y').mp hy',
      rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => key b hb y hy, fun hy => ?_⟩
  have := key b⁻¹ (Subgroup.inv_mem _ hb) _ hy
  simpa [mul_assoc] using this

namespace MinCex

variable {M V Q P H : Subgroup G} [Finite G]

theorem xToZ_mem_normalizer_of_isPGroup (hc : MinCex M V Q P H) {T : Subgroup (Hbar V H)}
    (hT : IsPGroup 2 T) (hCV : wOf V H ⊓ Subgroup.centralizer (preimOf V H T : Set G) ≤ V)
    {x : ↥(xOf V H)}
    (hx : (xToXbar hc.V_le_H x : Hbar V H) ∈ Subgroup.normalizer (T : Set (Hbar V H))) :
    xToZ hc.V_le_H x ∈ Subgroup.normalizer (VZ V H : Set (XbarZ V H)) := by
  have hVH : V ≤ H := hc.V_le_H
  have hW : wOf V H ≠ ⊥ := fun h => hc.V_inf_wOf_ne_bot (by rw [h, inf_bot_eq])
  have hxN := mem_normalizer_preimOf_of_mem_normalizer hVH hx
  have hT2 : IsPGroup 2 (preimOf V H T) := by
    refine isPGroup_preimOf (fun s hs => ?_)
      (CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hc.wOf_isElemAbelian)
    obtain ⟨k, hk⟩ := hT ⟨s, hs⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hxV : (x : G) ∈ Subgroup.normalizer (V : Set G) :=
    normalizer_mem_of_centralizer_le hc.ti hW (preimOf_le_H _ _ _) hT2 hCV
      (xOf_le_H hVH x.2) hxN
  rw [mem_normalizer_iff_conjSubgroup_eq, ← imgZ_conj hVH x,
    mem_normalizer_iff_conjSubgroup_eq.mp hxV]
  rfl

theorem exists_sylow_over (hc : MinCex M V Q P H) (hd : Sec23Data V H)
    (hBG : IsBenderGroup (XbarZ V H)) {S : Sylow 2 (XbarZ V H)}
    (hVS : VZ V H ≤ sylowCenter (S : Subgroup (XbarZ V H))) :
    ∃ Sb : Sylow 2 (Xbar V H), Rbar V H P ≤ (Sb : Subgroup (Xbar V H)) ∧
      (Sb : Subgroup (Xbar V H)).map (projZ V H) = (S : Subgroup (XbarZ V H)) := by
  obtain ⟨Sb, hRSb⟩ := IsPGroup.exists_le_sylow hc.isPGroup_Rbar
  refine ⟨Sb, hRSb, ?_⟩
  set Ssyl : Sylow 2 (XbarZ V H) := Sb.mapSurjective (QuotientGroup.mk'_surjective _) with hSsyl
  have hSs : (Ssyl : Subgroup (XbarZ V H)) = (Sb : Subgroup (Xbar V H)).map (projZ V H) :=
    Sylow.coe_mapSurjective _ _
  have hVSs : VZ V H ≤ sylowCenter (Ssyl : Subgroup (XbarZ V H)) :=
    le_sylowCenter_of_sq_eq_one hBG (fun x hx => by
      rw [hSs]
      exact Subgroup.map_mono hRSb (hc.VZ_le_Rtilde hx)) fun x hx => hc.VZ_sq hx
  have hSsS : Ssyl = S := sylow_eq_of_le_sylowCenter hBG (hc.Vtilde_ne_bot hd) hVSs hVS
  rw [← hSs, hSsS]

end MinCex

end CFSG.RankThree.GF2n.Tim79a
