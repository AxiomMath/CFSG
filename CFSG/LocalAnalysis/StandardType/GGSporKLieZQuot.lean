module

public import CFSG.LocalAnalysis.StandardType.GGSporKLieZDefs
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
import CFSG.LocalAnalysis.ComponentInitial.CentralQuotientComponentLift
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.Open CFSG.Assembly Matrix

private lemma l937z_q_lift_order {G : Type} [Group G] (Z : Subgroup G) [Z.Normal]
    (hZ : Nat.Coprime 14 (Nat.card Z)) {xbar : G ⧸ Z} (hxbar : orderOf xbar = 7) :
    ∃ x : G, orderOf x = 7 ∧ QuotientGroup.mk' Z x = xbar := by
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective Z xbar
  have hcop : Nat.Coprime 7 (Nat.card Z) := hZ.coprime_dvd_left (by norm_num)
  let u : (ZMod 7)ˣ := ZMod.unitOfCoprime (Nat.card Z) hcop.symm
  let s : ℕ := ((u⁻¹ : (ZMod 7)ˣ) : ZMod 7).val
  have hs : Nat.card Z * s ≡ 1 [MOD 7] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    rw [Nat.cast_mul]
    rw [show ((s : ℕ) : ZMod 7) = ((u⁻¹ : (ZMod 7)ˣ) : ZMod 7) from
      ZMod.natCast_zmod_val ((u⁻¹ : (ZMod 7)ˣ) : ZMod 7)]
    have hu : (u : ZMod 7) = ((Nat.card Z : ℕ) : ZMod 7) :=
      ZMod.coe_unitOfCoprime (Nat.card Z) hcop.symm
    rw [← hu]
    exact congrArg (fun w : (ZMod 7)ˣ => (w : ZMod 7)) (mul_inv_cancel u)
  have hz : y ^ 7 ∈ Z := by
    apply (QuotientGroup.eq_one_iff (y ^ 7)).mp
    change QuotientGroup.mk' Z (y ^ 7) = 1
    rw [map_pow, hy, ← hxbar, pow_orderOf_eq_one]
  have hzpow : (y ^ 7) ^ Nat.card Z = 1 := by
    have h1 : (⟨y ^ 7, hz⟩ : Z) ^ Nat.card Z = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_natCard (⟨y ^ 7, hz⟩ : Z))
    have h2 : ((⟨y ^ 7, hz⟩ : Z) : G) ^ Nat.card Z = 1 := by
      rw [← Subgroup.coe_pow]
      exact congrArg (fun z : ↥Z => (z : G)) h1
    simpa using h2
  have hfin : IsOfFinOrder xbar := isOfFinOrder_iff_pow_eq_one.mpr
    ⟨7, by norm_num, by simpa [hxbar] using pow_orderOf_eq_one xbar⟩
  have hxbar_pow : xbar ^ (Nat.card Z * s) = xbar := by
    have h : xbar ^ (Nat.card Z * s) = xbar ^ 1 := by
      rw [hfin.pow_eq_pow_iff_modEq, hxbar]
      exact hs
    rwa [pow_one] at h
  refine ⟨y ^ (Nat.card Z * s), ?_, ?_⟩
  · haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hpow : (y ^ (Nat.card Z * s)) ^ 7 = 1 := by
      calc (y ^ (Nat.card Z * s)) ^ 7 = y ^ (Nat.card Z * s * 7) := by rw [← pow_mul]
        _ = y ^ (7 * (Nat.card Z * s)) := by rw [mul_comm]
        _ = (y ^ 7) ^ (Nat.card Z * s) := by rw [pow_mul]
        _ = ((y ^ 7) ^ Nat.card Z) ^ s := by rw [pow_mul]
        _ = 1 := by rw [hzpow, one_pow]
    have hne : y ^ (Nat.card Z * s) ≠ 1 := by
      intro h1
      have hx1 : xbar = 1 := by
        have h2 : xbar ^ (Nat.card Z * s) = 1 := by
          rw [← hy, ← map_pow, h1, map_one]
        rwa [hxbar_pow] at h2
      rw [hx1, orderOf_one] at hxbar
      norm_num at hxbar
    exact orderOf_eq_prime hpow hne
  · rw [map_pow, hy, hxbar_pow]

private lemma l937z_q_centralizer {G : Type} [Group G] (Z : Subgroup G) [Z.Normal]
    (hZc : Z ≤ Subgroup.center G) (hZ7 : Nat.Coprime 7 (Nat.card Z)) {x : G}
    (hx : orderOf x = 7) :
    Subgroup.centralizer ({QuotientGroup.mk' Z x} : Set (G ⧸ Z)) =
      (Subgroup.centralizer ({x} : Set G)).map (QuotientGroup.mk' Z) := by
  have hx7 : x ^ 7 = 1 := by rw [← hx, pow_orderOf_eq_one]
  ext q
  constructor
  · intro hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z q
    rw [Subgroup.mem_map]
    refine ⟨g, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hq ⊢
    have hq' : QuotientGroup.mk' Z g * QuotientGroup.mk' Z x =
        QuotientGroup.mk' Z x * QuotientGroup.mk' Z g := hq
    have hz : g * x * g⁻¹ * x⁻¹ ∈ Z := by
      apply (QuotientGroup.eq_one_iff (g * x * g⁻¹ * x⁻¹)).mp
      change QuotientGroup.mk' Z (g * x * g⁻¹ * x⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hq']
      group
    have hzx : g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x := by group
    have hz7 : (g * x * g⁻¹ * x⁻¹) ^ 7 = 1 := by
      have h1 : ((g * x * g⁻¹ * x⁻¹) * x) ^ 7 = 1 := by
        rw [← hzx, conj_pow, hx7]
        group
      have hcomm : Commute (g * x * g⁻¹ * x⁻¹) x :=
        (Subgroup.mem_center_iff.mp (hZc hz) x).symm
      rw [hcomm.mul_pow, hx7, mul_one] at h1
      exact h1
    have hz1 : g * x * g⁻¹ * x⁻¹ = 1 := by
      have hdvd7 : orderOf (g * x * g⁻¹ * x⁻¹) ∣ 7 :=
        orderOf_dvd_iff_pow_eq_one.mpr hz7
      have hdvdZ : orderOf (g * x * g⁻¹ * x⁻¹) ∣ Nat.card Z := by
        have h := orderOf_dvd_natCard (⟨g * x * g⁻¹ * x⁻¹, hz⟩ : Z)
        rwa [Subgroup.orderOf_mk] at h
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hZ7 hdvd7 hdvdZ)
    have hgx : g * x * g⁻¹ = x := by rw [hzx, hz1, one_mul]
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [hgx]
  · intro hq
    rw [Subgroup.mem_map] at hq
    obtain ⟨k, hk, rfl⟩ := hq
    rw [Subgroup.mem_centralizer_singleton_iff] at hk ⊢
    rw [← map_mul, ← map_mul, hk]

private lemma l937z_q_card_center_eq {G : Type} [Group G] (K : Subgroup G) :
    Nat.card (Subgroup.center ↥K) = Nat.card ↥(K ⊓ Subgroup.centralizer (K : Set G)) := by
  have hmap : (Subgroup.center ↥K).map K.subtype = K ⊓ Subgroup.centralizer (K : Set G) := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨c.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro y hy
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hc) ⟨y, hy⟩)
    · rintro ⟨hxK, hxcent⟩
      refine ⟨⟨x, hxK⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxcent (y : G) y.2)
  rw [← hmap]
  exact Nat.card_congr
    ((Subgroup.center ↥K).equivMapOfInjective K.subtype K.subtype_injective).toEquiv

private lemma l937z_q_card_center_map {G : Type} [Group G] {D : Subgroup G}
    (L : Subgroup ↥D) :
    Nat.card (Subgroup.center ↥(L.map D.subtype)) = Nat.card (Subgroup.center ↥L) :=
  (Nat.card_congr
    (Subgroup.centerCongr (L.equivMapOfInjective D.subtype D.subtype_injective)).toEquiv).symm

private lemma l937z_q_center_dvd {A B : Type} [Group A] [Group B] [Group.IsPerfect A]
    (φ : A →* B) (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center A) :
    Nat.card (Subgroup.center B) ∣ Nat.card (Subgroup.center A) := by
  have hmap : (Subgroup.center A).map φ = Subgroup.center B :=
    CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel φ hφ hker
  rw [← hmap]
  exact Subgroup.card_map_dvd (Subgroup.center A) φ

theorem lieZRow_quotient_of_central {G : Type} [Group G] [Finite G] (Z : Subgroup G) [Z.Normal]
    (hZc : Z ≤ Subgroup.center G) (hZ : Nat.Coprime 14 (Nat.card Z)) (h : LieZRow G) :
    LieZRow (G ⧸ Z) := by
  intro xbar hxbar Jbar hJbar
  obtain ⟨x, hx, hxmk⟩ := l937z_q_lift_order Z hZ hxbar
  rw [← hxmk] at hJbar
  have hZ7 : Nat.Coprime 7 (Nat.card Z) := hZ.coprime_dvd_left (by norm_num)
  have hcent : Subgroup.centralizer ({QuotientGroup.mk' Z x} : Set (G ⧸ Z)) =
      (Subgroup.centralizer ({x} : Set G)).map (QuotientGroup.mk' Z) :=
    l937z_q_centralizer Z hZc hZ7 hx
  let D : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let Dbar : Subgroup (G ⧸ Z) := Subgroup.centralizer ({QuotientGroup.mk' Z x} : Set (G ⧸ Z))
  have hJle : Jbar ≤ Dbar := hJbar.1
  let M : Subgroup ↥Dbar := Jbar.subgroupOf Dbar
  have hMsub : M.IsSubnormal := CFSG.Assembly.IsSubnormal.subgroupOf hJbar.2.1
  have hJq : CFSG.Open.IsQuasisimple ↥Jbar := hJbar.2.2
  have hMq : CFSG.Open.IsQuasisimple ↥M :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (Subgroup.subgroupOfEquivOfLe hJle) hJq
  haveI hMperf : Group.IsPerfect ↥M := ⟨hMq.1⟩
  let f : ↥D →* ↥Dbar :=
    CFSG.LocalAnalysis.ComponentInitial.CentralQuotientLift.centralizerProj Z x
  have hfker : f.ker ≤ Subgroup.center ↥D :=
    CFSG.LocalAnalysis.ComponentInitial.CentralQuotientLift.centralizerProj_ker_le_center hZc x
  have hfsurj : Function.Surjective f := by
    intro y
    have hy : (y : G ⧸ Z) ∈
        (Subgroup.centralizer ({x} : Set G)).map (QuotientGroup.mk' Z) := by
      rw [← hcent]
      exact y.2
    obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.mp hy
    refine ⟨⟨g, hg⟩, Subtype.ext ?_⟩
    change QuotientGroup.mk' Z g = (y : G ⧸ Z)
    exact hgy
  let L : Subgroup ↥D := CFSG.ComponentClassification.CatalogueBCentralQuotient.derivedPreimage f M
  have hLmap : L.map f = M :=
    CFSG.ComponentClassification.CatalogueBCentralQuotient.derivedPreimage_map f hfsurj M
  have hLperf : Group.IsPerfect ↥L :=
    CFSG.ComponentClassification.CatalogueBCentralQuotient.derivedPreimage_perfect
      f hfsurj hfker M
  have hLsub : L.IsSubnormal :=
    CFSG.ComponentClassification.CatalogueBCentralQuotient.derivedPreimage_subnormal f M hMsub
  let ψ : ↥L →* ↥M :=
    (f.domRestrict L).codRestrict M (fun l => by
      have hl : f l ∈ L.map f := Subgroup.mem_map_of_mem f l.2
      rwa [hLmap] at hl)
  have hψsurj : Function.Surjective ψ := by
    intro m
    have hm : (m : ↥Dbar) ∈ L.map f := by rw [hLmap]; exact m.2
    obtain ⟨l, hl, hlm⟩ := Subgroup.mem_map.mp hm
    refine ⟨⟨l, hl⟩, Subtype.ext ?_⟩
    change f l = (m : ↥Dbar)
    exact hlm
  have hψker : ψ.ker ≤ Subgroup.center ↥L := by
    intro l hl
    have hfl : f (l : ↥D) = 1 := by
      have h1 : ψ l = 1 := MonoidHom.mem_ker.mp hl
      have h2 : (ψ l : ↥Dbar) = (1 : ↥Dbar) :=
        congrArg (fun m : ↥M => (m : ↥Dbar)) h1
      have hval : (ψ l : ↥Dbar) = f (l : ↥D) := rfl
      rwa [hval] at h2
    have hcentD : (l : ↥D) ∈ Subgroup.center ↥D := hfker (MonoidHom.mem_ker.mpr hfl)
    refine Subgroup.mem_center_iff.mpr ?_
    intro m
    exact Subtype.ext ((Subgroup.mem_center_iff.mp hcentD) (m : ↥D))
  have hLq : CFSG.Open.IsQuasisimple ↥L :=
    CFSG.ComponentClassification.CentralExtensions.quasisimple_of_surjective hMq ψ hψsurj hψker
  let J : Subgroup G := L.map D.subtype
  have hJleD : J ≤ D := by
    rw [Subgroup.map_le_iff_le_comap]
    intro l _
    exact l.2
  have hJsub : CFSG.Assembly.IsSubnormal J D := by
    have h1 : CFSG.Assembly.IsSubnormal L ⊤ := CFSG.Assembly.IsSubnormal.of_mathlib hLsub
    have h2 := h1.map D.subtype
    rwa [Subgroup.map_top, Subgroup.range_subtype] at h2
  have hJq : CFSG.Assembly.IsQuasisimple ↥J :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (L.equivMapOfInjective D.subtype D.subtype_injective).symm hLq
  have hOddJ : Odd (Nat.card ↥(J ⊓ Subgroup.centralizer (J : Set G))) :=
    h x hx J ⟨hJleD, hJsub, hJq⟩
  have hcenterM : Nat.card (Subgroup.center ↥M) ∣ Nat.card (Subgroup.center ↥L) :=
    l937z_q_center_dvd ψ hψsurj hψker
  have hcenterJbar : Nat.card (Subgroup.center ↥Jbar) = Nat.card (Subgroup.center ↥M) := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hJle]
    exact l937z_q_card_center_map (D := Dbar) (Jbar.subgroupOf Dbar)
  have hcenterJ : Nat.card (Subgroup.center ↥J) = Nat.card (Subgroup.center ↥L) :=
    l937z_q_card_center_map (D := D) L
  have hcJbar : Nat.card ↥(Jbar ⊓ Subgroup.centralizer (Jbar : Set (G ⧸ Z))) =
      Nat.card (Subgroup.center ↥Jbar) := (l937z_q_card_center_eq Jbar).symm
  have hcJ : Nat.card ↥(J ⊓ Subgroup.centralizer (J : Set G)) =
      Nat.card (Subgroup.center ↥J) := (l937z_q_card_center_eq J).symm
  have hdvd : Nat.card ↥(Jbar ⊓ Subgroup.centralizer (Jbar : Set (G ⧸ Z))) ∣
      Nat.card ↥(J ⊓ Subgroup.centralizer (J : Set G)) := by
    rw [hcJbar, hcJ, hcenterJbar, hcenterJ]
    exact hcenterM
  exact Odd.of_dvd_nat hOddJ hdvd

theorem lieZRow_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    (H : Subgroup (GL ι K)) (hZ : Nat.Coprime 14 (Nat.card ↥((StatedScalars ι K).subgroupOf H)))
    (h : LieZRow ↥H) : LieZRow (StatedProj H) := by
  have hZc : (StatedScalars ι K).subgroupOf H ≤ Subgroup.center ↥H := by
    intro x hx
    have hxS : ((x : ↥H) : GL ι K) ∈ StatedScalars ι K := Subgroup.mem_subgroupOf.mp hx
    have hx' : ((x : ↥H) : GL ι K) ∈ Subgroup.center (GL ι K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact hxS
    rw [Subgroup.mem_center_iff] at hx' ⊢
    intro y
    apply Subtype.ext
    exact hx' (y : GL ι K)
  exact lieZRow_quotient_of_central ((StatedScalars ι K).subgroupOf H) hZc hZ h

theorem card_statedScalars_subgroupOf_dvd {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] (H : Subgroup (GL ι K)) :
    Nat.card ↥((StatedScalars ι K).subgroupOf H) ∣ Nat.card K - 1 := by
  have h1 : Nat.card ↥((StatedScalars ι K).subgroupOf H) ∣ Nat.card ↥(StatedScalars ι K) :=
    Subgroup.card_comap_dvd_of_injective (StatedScalars ι K) H.subtype H.subtype_injective
  have h2 : Nat.card ↥(StatedScalars ι K) ∣ Nat.card Kˣ := by
    rw [StatedScalars]
    exact Subgroup.card_range_dvd (Matrix.GeneralLinearGroup.scalar ι)
  have h3 : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
  exact h1.trans (h3 ▸ h2)

end CFSG.StandardType.SporadicShape
