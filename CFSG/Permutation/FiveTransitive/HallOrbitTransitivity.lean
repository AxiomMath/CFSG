module

public import CFSG.Permutation.FiveTransitive.HallExceptionalCalculation
public import CFSG.Permutation.FiveTransitive.HallVFourOrbits

public section

namespace CFSG

namespace FiveTransitive.Research.HallOrbitTransitivity

open MulAction Subgroup

private theorem exists_zpowers_conjugator_of_involutions_odd_product
    {G : Type} [Group G]
    (u v : G) (huTwo : u ^ 2 = 1) (hvTwo : v ^ 2 = 1)
    (huNe : u ≠ 1) (hvNe : v ≠ 1)
    (hodd : Odd (orderOf (v * u))) :
    ∃ k : G, k ∈ Subgroup.zpowers (v * u) ∧ k * u * k⁻¹ = v := by
  classical
  let r : G := v * u
  let Z : Subgroup G := Subgroup.zpowers r
  let rZ : Z := ⟨r, Subgroup.mem_zpowers r⟩
  have hZOdd : Odd (Nat.card Z) := by
    change Odd (Nat.card (Subgroup.zpowers r))
    rw [Nat.card_zpowers]
    simpa only [r] using hodd
  have hcoprime : (Nat.card Z).Coprime 2 :=
    Nat.coprime_two_right.mpr hZOdd
  obtain ⟨kZ, hkZ⟩ :=
    (Nat.Coprime.pow_left_bijective (G := Z) hcoprime).2 rZ
  let k : G := kZ
  have hkSq : k ^ 2 = r := congrArg Subtype.val hkZ
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp kZ.prop
  have hnG : r ^ n = k := by simpa only [k] using hn
  have huOrder : orderOf u = 2 := orderOf_eq_prime huTwo huNe
  have hvOrder : orderOf v = 2 := orderOf_eq_prime hvTwo hvNe
  have huInv : u⁻¹ = u := inv_eq_self_of_orderOf_eq_two huOrder
  have hvInv : v⁻¹ = v := inv_eq_self_of_orderOf_eq_two hvOrder
  have huu : u * u = 1 := by simpa [pow_two] using huTwo
  have hur : u * r * u⁻¹ = r⁻¹ := by
    dsimp only [r]
    rw [mul_inv_rev, huInv, hvInv]
    calc
      u * (v * u) * u = u * v * (u * u) := by group
      _ = u * v := by rw [huu, mul_one]
  have huk : u * k * u⁻¹ = k⁻¹ := by
    calc
      u * k * u⁻¹ = u * (r ^ n) * u⁻¹ := by rw [hnG]
      _ = (MulAut.conj u) (r ^ n) := by rw [MulAut.conj_apply]
      _ = ((MulAut.conj u) r) ^ n := map_zpow (MulAut.conj u) r n
      _ = (u * r * u⁻¹) ^ n := by rw [MulAut.conj_apply]
      _ = (r⁻¹) ^ n := by rw [hur]
      _ = (r ^ n)⁻¹ := inv_zpow r n
      _ = k⁻¹ := by rw [hnG]
  have huk' : u * k * u = k⁻¹ := by simpa only [huInv] using huk
  have hukInv : u * k⁻¹ * u = k := by
    have h := congrArg Inv.inv huk'
    have h' : u * (k⁻¹ * u) = k := by
      simpa only [mul_inv_rev, inv_inv, huInv] using h
    exact (mul_assoc u k⁻¹ u).trans h'
  have huKInv : u * k⁻¹ = k * u := by
    calc
      u * k⁻¹ = (u * k⁻¹ * u) * u := by
        rw [mul_assoc, huu, mul_one]
      _ = k * u := by rw [hukInv]
  refine ⟨k, ?_, ?_⟩
  · simpa only [k, Z, r] using kZ.prop
  · calc
      k * u * k⁻¹ = k * (u * k⁻¹) := by rw [mul_assoc]
      _ = k * (k * u) := by rw [huKInv]
      _ = (k ^ 2) * u := by rw [pow_two, mul_assoc]
      _ = r * u := by rw [hkSq]
      _ = (v * u) * u := rfl
      _ = v := by rw [mul_assoc, huu, mul_one]

theorem quarter_reflection_sq
    {G : Type} [Group G]
    (a b u : G) (haTwo : a ^ 2 = 1) (hbTwo : b ^ 2 = 1)
    (hab : Commute a b) (huSq : u ^ 2 = a)
    (hub : u * b = (a * b) * u) :
    (b * u) ^ 2 = 1 := by
  calc
    (b * u) ^ 2 = (b * u) * (b * u) := by rw [pow_two]
    _ = b * (u * b) * u := by group
    _ = b * ((a * b) * u) * u := by rw [hub]
    _ = (b * (a * b)) * (u * u) := by group
    _ = (b * (a * b)) * (u ^ 2) := by rw [pow_two]
    _ = a * a := by
      rw [huSq]
      congr 1
      calc
        b * (a * b) = a * (b * b) := by
          rw [← mul_assoc, hab.eq.symm, mul_assoc]
        _ = a := by rw [← pow_two, hbTwo, mul_one]
    _ = 1 := by simpa [pow_two] using haTwo

theorem quarter_reflection_commute_first
    {G : Type} [Group G]
    (a b u : G) (hab : Commute a b) (hua : u * a = a * u) :
    Commute (b * u) a := by
  rw [Commute]
  calc
    (b * u) * a = b * (u * a) := by rw [mul_assoc]
    _ = b * (a * u) := by rw [hua]
    _ = (a * b) * u := by rw [← mul_assoc, hab.eq.symm]
    _ = a * (b * u) := by rw [mul_assoc]

theorem quarter_reflection_intertwines_second
    {G : Type} [Group G]
    (a b u : G) (hbTwo : b ^ 2 = 1) (hab : Commute a b)
    (hub : u * b = (a * b) * u) :
    (b * u) * b = (a * b) * (b * u) := by
  calc
    (b * u) * b = b * (u * b) := by rw [mul_assoc]
    _ = b * ((a * b) * u) := by rw [hub]
    _ = (b * (a * b)) * u := by rw [← mul_assoc]
    _ = ((a * b) * b) * u := by
      congr 1
      rw [← mul_assoc, hab.eq.symm, mul_assoc]
    _ = (a * b) * (b * u) := by rw [mul_assoc]

private theorem reflection_product_centralizes
    {G : Type} [Group G]
    (a b v w : G)
    (hva : Commute v a) (hwa : Commute w a)
    (hvb : v * b = (a * b) * v)
    (hwb : w * b = (a * b) * w)
    (haTwo : a ^ 2 = 1) :
    Commute (w * v) a ∧ Commute (w * v) b := by
  constructor
  · exact hwa.mul_left hva
  · rw [Commute]
    have hwc : w * (a * b) = b * w := by
      calc
        w * (a * b) = (w * a) * b := by rw [mul_assoc]
        _ = (a * w) * b := by rw [hwa.eq]
        _ = a * (w * b) := by rw [mul_assoc]
        _ = a * ((a * b) * w) := by rw [hwb]
        _ = (a * a) * b * w := by group
        _ = b * w := by rw [← pow_two, haTwo, one_mul]
    calc
      (w * v) * b = w * (v * b) := by rw [mul_assoc]
      _ = w * ((a * b) * v) := by rw [hvb]
      _ = (w * (a * b)) * v := by rw [← mul_assoc]
      _ = (b * w) * v := by rw [hwc]
      _ = b * (w * v) := by rw [mul_assoc]

@[expose] def exceptionalSet
    {G X : Type} [Group G] [MulAction G X] (a b : G) : Set X :=
  (MulAction.fixedBy X a ∪ MulAction.fixedBy X b) ∪
    MulAction.fixedBy X (a * b)

def hallCentralizer
    {G X : Type} [Group G] [MulAction G X] (a b : G) : Subgroup G :=
  fixingSubgroup G (exceptionalSet (X := X) a b) ⊓
    Subgroup.centralizer ({a, b} : Set G)

theorem mem_hallCentralizer_iff
    {G X : Type} [Group G] [MulAction G X] (a b z : G) :
    z ∈ hallCentralizer (X := X) a b ↔
      (∀ x ∈ exceptionalSet (X := X) a b, z • x = x) ∧
      Commute z a ∧ Commute z b := by
  rw [hallCentralizer, Subgroup.mem_inf, mem_fixingSubgroup_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hfix, hcomm⟩
    refine ⟨hfix, ?_, ?_⟩
    · exact (show a * z = z * a from hcomm a (by simp)).symm
    · exact (show b * z = z * b from hcomm b (by simp)).symm
  · rintro ⟨hfix, hza, hzb⟩
    refine ⟨hfix, ?_⟩
    intro g hg
    rcases hg with rfl | rfl
    · exact hza.eq.symm
    · exact hzb.eq.symm

theorem hallCentralizer_le_stabilizer
    {G X : Type} [Group G] [MulAction G X]
    (e : Fin 4 ↪ X) (a b : G)
    (he : ∀ i, e i ∈ exceptionalSet (X := X) a b) :
    hallCentralizer (X := X) a b ≤ MulAction.stabilizer G e := by
  intro z hz
  rw [MulAction.mem_stabilizer_iff]
  apply Function.Embedding.ext
  intro i
  exact (mem_hallCentralizer_iff a b z).mp hz |>.1 (e i) (he i)

theorem hallCentralizer_card_odd
    {G X : Type} [Group G] [Finite G] [MulAction G X]
    (e : Fin 4 ↪ X) (a b : G)
    (he : ∀ i, e i ∈ exceptionalSet (X := X) a b)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e))) :
    Odd (Nat.card (hallCentralizer (X := X) a b)) := by
  apply hodd.of_dvd_nat
  exact Subgroup.card_dvd_of_le (hallCentralizer_le_stabilizer e a b he)

structure HallReflectionAt
    {G X : Type} [Group G] [MulAction G X]
    (E : Set X) (sigma : X → X) (a b : G) (x : X) (v : G) : Prop where
  sq : v ^ 2 = 1
  ne_one : v ≠ 1
  commute_first : Commute v a
  intertwines_second : v * b = (a * b) * v
  fixes_point : v • x = x
  fixes_first_translate : v • (a • x) = a • x
  fixed_regular : ∀ z : X, z ∉ E → v • z = z → z = x ∨ z = a • x
  on_exceptional : ∀ z ∈ E, v • z = sigma z

theorem exists_hallCentralizer_maps_regular_orbit
    {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (a b : G) (haTwo : a ^ 2 = 1)
    (E : Set X) (hE : E = exceptionalSet (X := X) a b)
    (sigma : X → X) (hsigmaE : Set.MapsTo sigma E E)
    (hsigmaSq : ∀ z ∈ E, sigma (sigma z) = z)
    (hoddC : Odd (Nat.card (hallCentralizer (X := X) a b)))
    (x y : X) (hx : x ∉ E) (hy : y ∉ E)
    (vx vy : G)
    (hvx : HallReflectionAt E sigma a b x vx)
    (hvy : HallReflectionAt E sigma a b y vy) :
    ∃ k : hallCentralizer (X := X) a b,
      (k : G) • x = y ∨ (k : G) • x = a • y := by
  let r : G := vy * vx
  have hrFix : ∀ z ∈ E, r • z = z := by
    intro z hz
    calc
      r • z = vy • (vx • z) := by
        change (vy * vx) • z = vy • (vx • z)
        rw [mul_smul]
      _ = vy • sigma z := by rw [hvx.on_exceptional z hz]
      _ = sigma (sigma z) := hvy.on_exceptional (sigma z) (hsigmaE hz)
      _ = z := hsigmaSq z hz
  have hrComm := reflection_product_centralizes a b vx vy
    hvx.commute_first hvy.commute_first
    hvx.intertwines_second hvy.intertwines_second haTwo
  have hrC : r ∈ hallCentralizer (X := X) a b := by
    rw [mem_hallCentralizer_iff]
    refine ⟨?_, hrComm.1, hrComm.2⟩
    intro z hz
    apply hrFix z
    rwa [hE]
  have hrOdd : Odd (orderOf r) := by
    apply hoddC.of_dvd_nat
    exact (hallCentralizer (X := X) a b).orderOf_dvd_natCard hrC
  obtain ⟨k, hkPow, hkConj⟩ :=
    exists_zpowers_conjugator_of_involutions_odd_product
      vx vy hvx.sq hvy.sq hvx.ne_one hvy.ne_one hrOdd
  have hkC : k ∈ hallCentralizer (X := X) a b :=
    (Subgroup.zpowers_le_of_mem hrC) hkPow
  let kC : hallCentralizer (X := X) a b := ⟨k, hkC⟩
  have hkFixE : ∀ z ∈ E, k • z = z := by
    intro z hz
    exact (mem_hallCentralizer_iff a b k).mp hkC |>.1 z (by rwa [← hE])
  have hkxNotE : k • x ∉ E := by
    intro hkxE
    have hkFix := hkFixE (k • x) hkxE
    have heq : k • x = k • (k • x) := by rw [hkFix]
    have hxEq : x = k • x := (MulAction.injective k) heq
    apply hx
    rw [hxEq]
    exact hkxE
  have hvykx : vy • (k • x) = k • x := by
    calc
      vy • (k • x) = (k * vx * k⁻¹) • (k • x) := by rw [hkConj]
      _ = k • (vx • x) := by
        rw [mul_smul, mul_smul, inv_smul_smul]
      _ = k • x := by rw [hvx.fixes_point]
  have hcases := hvy.fixed_regular (k • x) hkxNotE hvykx
  exact ⟨kC, by simpa only [kC] using hcases⟩

theorem hallCentralizer_smul_eq_self_of_mem_fourSet
    {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (a b : G) (haTwo : a ^ 2 = 1) (hbTwo : b ^ 2 = 1)
    (hab : Commute a b)
    (hoddC : Odd (Nat.card (hallCentralizer (X := X) a b)))
    (x : X) (hx : x ∉ exceptionalSet (X := X) a b)
    (k : hallCentralizer (X := X) a b)
    (hk : (k : G) • x ∈
      ({x, a • x, b • x, (a * b) • x} : Set X)) :
    (k : G) • x = x := by
  have hxa : a • x ≠ x := by
    intro h
    apply hx
    simp [exceptionalSet, h]
  have hxb : b • x ≠ x := by
    intro h
    apply hx
    simp [exceptionalSet, h]
  have hxc : (a * b) • x ≠ x := by
    intro h
    apply hx
    simp [exceptionalSet, h]
  have hka : Commute (k : G) a :=
    (mem_hallCentralizer_iff a b (k : G)).mp k.prop |>.2.1
  have hkb : Commute (k : G) b :=
    (mem_hallCentralizer_iff a b (k : G)).mp k.prop |>.2.2
  have hkc : Commute (k : G) (a * b) := hka.mul_right hkb
  have horderOdd : Odd (orderOf (k : G)) := by
    apply hoddC.of_dvd_nat
    simpa only [Subgroup.orderOf_coe] using
      (orderOf_dvd_natCard k)
  have hnotTwo : ¬2 ∣ orderOf (k : G) := horderOdd.not_two_dvd_nat
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
  rcases hk with hk | hk | hk | hk
  · exact hk
  · exfalso
    apply hnotTwo
    apply Research.HallExceptionalCalculation.two_dvd_orderOf_of_smul_swap
      (k : G) x (a • x) hxa.symm hk
    calc
      (k : G) • (a • x) = a • ((k : G) • x) := by
        rw [← mul_smul, ← mul_smul, hka.eq]
      _ = a • (a • x) := by rw [hk]
      _ = x := by rw [← mul_smul, ← pow_two, haTwo, one_smul]
  · exfalso
    apply hnotTwo
    apply Research.HallExceptionalCalculation.two_dvd_orderOf_of_smul_swap
      (k : G) x (b • x) hxb.symm hk
    calc
      (k : G) • (b • x) = b • ((k : G) • x) := by
        rw [← mul_smul, ← mul_smul, hkb.eq]
      _ = b • (b • x) := by rw [hk]
      _ = x := by rw [← mul_smul, ← pow_two, hbTwo, one_smul]
  · have hcTwo : (a * b) ^ 2 = 1 :=
      Research.HallVFourOrbits.product_involution_sq
        a b haTwo hbTwo hab
    exfalso
    apply hnotTwo
    apply Research.HallExceptionalCalculation.two_dvd_orderOf_of_smul_swap
      (k : G) x ((a * b) • x) hxc.symm hk
    calc
      (k : G) • ((a * b) • x) =
          (a * b) • ((k : G) • x) := by
        rw [← mul_smul, ← mul_smul, hkc.eq]
      _ = (a * b) • ((a * b) • x) := by rw [hk]
      _ = x := by rw [← mul_smul, ← pow_two, hcTwo, one_smul]

theorem exists_sylow_element_moves_of_prime_dvd_orbit
    {G X : Type} [Group G] [Finite G] [MulAction G X]
    {p : ℕ} [Fact p.Prime]
    (C : Subgroup G) (P : Sylow p C) (x : X)
    (hdvd : p ∣ (MulAction.orbit C x).ncard) :
    ∃ u : P, ((u : P) : C) • x ≠ x := by
  by_contra hnone
  push_neg at hnone
  have hle : (P : Subgroup C) ≤ MulAction.stabilizer C x := by
    intro u hu
    change (u : C) • x = x
    exact hnone ⟨u, hu⟩
  have hindexDvd : p ∣ (MulAction.stabilizer C x).index := by
    rw [MulAction.index_stabilizer]
    exact hdvd
  apply P.not_dvd_index
  rw [← Subgroup.relIndex_mul_index hle]
  exact dvd_mul_of_dvd_right hindexDvd _

end FiveTransitive.Research.HallOrbitTransitivity

end CFSG
