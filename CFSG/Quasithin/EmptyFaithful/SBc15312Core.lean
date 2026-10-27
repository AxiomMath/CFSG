module

public import CFSG.Quasithin.EmptyFaithful.S153I37
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc

section Theta

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G}

structure Setup12 (A L : Subgroup G) : Prop where
  normalizes : A ≤ Subgroup.normalizer (L : Set G)
  centerless : ∀ y ∈ L, (∀ l ∈ L, l * y * l⁻¹ * y⁻¹ ∈ pCoreOf 2 L) → y ∈ pCoreOf 2 L
  inner : InducesInnerModO2153 A L

omit [Finite G] in
theorem mem_pCore_iff' (x : ↥L) : x ∈ CFSG.Open.pCore 2 ↥L ↔ (x : G) ∈ pCoreOf 2 L :=
  (CFSG.mem_openPCoreOf_iff_open x).symm

omit [Finite G] in
private theorem conj_mem (h : Setup12 A L) (y : ↥A) (z : ↥L) : (y : G) * z * (y : G)⁻¹ ∈ L :=
  (Subgroup.mem_normalizer_iff.mp (h.normalizes y.2) z).mp z.2

private def cj (h : Setup12 A L) (y : ↥A) (z : ↥L) : ↥L := ⟨(y : G) * z * (y : G)⁻¹, conj_mem h y z⟩

omit [Finite G] in
private theorem exists_act (h : Setup12 A L) (y : ↥A) :
    ∃ m : OTwoQuot L, ∀ z : ↥L,
      (QuotientGroup.mk (cj h y z) : OTwoQuot L) = m * QuotientGroup.mk z * m⁻¹ := by
  obtain ⟨l, hl, hl'⟩ := h.inner y y.2
  refine ⟨QuotientGroup.mk ⟨l, hl⟩, fun z => ?_⟩
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    QuotientGroup.eq_iff_div_mem, mem_pCore_iff']
  simpa [cj, div_eq_mul_inv, mul_assoc] using hl' z z.2

omit [Finite G] in
private theorem centerless_quot (h : Setup12 A L) (w : OTwoQuot L)
    (hw : ∀ q : OTwoQuot L, q * w = w * q) : w = 1 := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
  have hmem : (y : G) ∈ pCoreOf 2 L := by
    refine h.centerless y y.2 (fun l hl => ?_)
    have h0 := hw (QuotientGroup.mk ⟨l, hl⟩)
    have h1 : (QuotientGroup.mk (⟨l, hl⟩ * y * ⟨l, hl⟩⁻¹ * y⁻¹ : ↥L) : OTwoQuot L) = 1 := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [h0]
      group
    exact (mem_pCore_iff' _).mp ((QuotientGroup.eq_one_iff _).mp h1)
  exact (QuotientGroup.eq_one_iff _).mpr ((mem_pCore_iff' y).mpr hmem)

private noncomputable def theta (h : Setup12 A L) (y : ↥A) : OTwoQuot L :=
  Classical.choose (exists_act h y)

omit [Finite G] in
private theorem theta_spec (h : Setup12 A L) (y : ↥A) (z : ↥L) :
    (QuotientGroup.mk (cj h y z) : OTwoQuot L) = theta h y * QuotientGroup.mk z * (theta h y)⁻¹ :=
  Classical.choose_spec (exists_act h y) z

omit [Finite G] in
private theorem theta_unique (h : Setup12 A L) (y : ↥A) (m : OTwoQuot L)
    (hm : ∀ z : ↥L, (QuotientGroup.mk (cj h y z) : OTwoQuot L) = m * QuotientGroup.mk z * m⁻¹) :
    m = theta h y := by
  have key : (theta h y)⁻¹ * m = 1 := by
    apply centerless_quot h
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    have e1 := theta_spec h y z
    have e2 := hm z
    rw [e1] at e2
    calc (QuotientGroup.mk z : OTwoQuot L) * ((theta h y)⁻¹ * m)
        = (theta h y)⁻¹ * (theta h y * QuotientGroup.mk z * (theta h y)⁻¹) * m := by group
      _ = (theta h y)⁻¹ * (m * QuotientGroup.mk z * m⁻¹) * m := by rw [e2]
      _ = (theta h y)⁻¹ * m * QuotientGroup.mk z := by group
  exact (inv_mul_eq_one.mp key).symm

omit [Finite G] in
private theorem theta_mul (h : Setup12 A L) (y y' : ↥A) :
    theta h (y * y') = theta h y * theta h y' := by
  symm
  apply theta_unique h (y * y')
  intro z
  have e : cj h (y * y') z = cj h y (cj h y' z) := by
    apply Subtype.ext
    simp [cj, mul_assoc]
  rw [e, theta_spec h y (cj h y' z), theta_spec h y' z]
  group

private noncomputable def thetaHom (h : Setup12 A L) : ↥A →* OTwoQuot L :=
  MonoidHom.mk' (theta h) (theta_mul h)

omit [Finite G] in
private theorem theta_of_mem (h : Setup12 A L) (y : ↥A) (hyL : (y : G) ∈ L) :
    theta h y = QuotientGroup.mk (⟨(y : G), hyL⟩ : ↥L) := by
  symm
  apply theta_unique h y
  intro z
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  rfl

omit [Finite G] in
private theorem theta_eq_one_iff (h : Setup12 A L) (y : ↥A) :
    theta h y = 1 ↔ ∀ z ∈ L, z * (y : G) * z⁻¹ * (y : G)⁻¹ ∈ pCoreOf 2 L := by
  constructor
  · intro h1 z hz
    have e := theta_spec h y ⟨z, hz⟩
    rw [h1] at e
    simp only [inv_one, one_mul, mul_one] at e
    have e' : (y : G) * z * (y : G)⁻¹ * z⁻¹ ∈ pCoreOf 2 L := by
      have := (QuotientGroup.eq_iff_div_mem.mp e)
      rw [mem_pCore_iff'] at this
      simpa [cj, div_eq_mul_inv] using this
    have := (pCoreOf 2 L).inv_mem e'
    simpa [mul_assoc] using this
  · intro hz
    symm
    apply theta_unique h y
    intro z
    simp only [inv_one, one_mul, mul_one]
    rw [QuotientGroup.eq_iff_div_mem, mem_pCore_iff']
    have := (pCoreOf 2 L).inv_mem (hz z z.2)
    simpa [cj, div_eq_mul_inv, mul_assoc] using this

structure Core12 (A L : Subgroup G) : Prop extends Setup12 A L where
  exp3 : ∀ y ∈ A, Odd (orderOf y) → y ^ 3 = 1
  rankL : CFSG.Open.pRank 3 L = 1
  three_dvd : 3 ∣ Nat.card ↥(A ⊓ L)

omit [Finite G] in
private theorem isPGroup_three_zpowers {y : G} (hy : y ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers y) := by
  intro g
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
  refine ⟨1, Subtype.ext ?_⟩
  show ((g : G)) ^ 3 ^ 1 = 1
  rw [← hn, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]

private theorem pRank_quot_le_one (hL : CFSG.Open.pRank 3 L = 1) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (OTwoQuot L)) ≤ 1 := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnd : ¬ 3 ∣ Nat.card (CFSG.Open.pCore 2 ↥L) := by
    intro hd
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥L) 2).exists_card_eq
    rw [hk] at hd
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow hd)) (by norm_num)
  have h1 := CFSG.SectionRank.pRank_quotient_eq (p := 3) (CFSG.Open.pCore 2 ↥L) hnd
  have h2 := pRank_top_subtype (p := 3) L
  rw [h1, h2, hL]

private theorem mem_zpowers_of_commute {X : Type} [Group X] [Finite X]
    (hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 1) {a b : X} (ha1 : a ≠ 1) (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1) (hab : a * b = b * a) : b ∈ Subgroup.zpowers a := by
  by_contra hb'
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hao : orderOf a = 3 := orderOf_eq_prime ha ha1
  have hb1 : b ≠ 1 := fun h => hb' (h ▸ Subgroup.one_mem _)
  have hbo : orderOf b = 3 := orderOf_eq_prime hb hb1
  have hE : IsElemAbelian 3 (Subgroup.zpowers a) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow]
  have hcomm : ∀ e ∈ Subgroup.zpowers a, Commute e b := by
    intro e he
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact (Commute.zpow_left (show Commute a b from hab) n)
  obtain ⟨hE2, hc2⟩ := exists_elemAbelian_sup_zpowers hE hbo hcomm hb'
  have hcard : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, hao]
  have h2 := CFSG.Quasithin.le_pRank Nat.prime_three
    (le_top : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ ⊤) hE2 (k := 2)
    (by rw [hc2, hcard]; norm_num)
  omega

section Decomp

omit [Finite G] in
private theorem A_le_normalizer_inf (h : Setup12 A L) :
    A ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := fun _ hg =>
  Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, h.normalizes hg⟩

private theorem mem_K_iff {c : G} :
    c ∈ centralizerSection A L (pCoreOf 2 L) ↔
      c ∈ A ∧ ∀ z ∈ L, z * c * z⁻¹ * c⁻¹ ∈ pCoreOf 2 L :=
  mem_centralizerSection_iff_of_le (pCoreOf_le 2 L)

theorem exists_decomp (h : Core12 A L) {y : G} (hyA : y ∈ A) (hy : Odd (orderOf y)) :
    ∃ a ∈ A ⊓ L, ∃ c ∈ centralizerSection A L (pCoreOf 2 L),
      Odd (orderOf a) ∧ Odd (orderOf c) ∧ y = a * c := by
  have hy3 : y ^ 3 = 1 := h.exp3 y hyA hy
  have hP3 := isPGroup_three_zpowers hy3
  have hPN : Subgroup.zpowers y ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le.mpr hyA).trans (A_le_normalizer_inf h.toSetup12)
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hxAL, hxo, hxC⟩ := exists_orderOf_eq_of_isPGroup_normalizer hP3 hPN h.three_dvd
  have hxy : y * x = x * y := Subgroup.mem_centralizer_iff.mp hxC y (Subgroup.mem_zpowers y)
  have hx3 : x ^ 3 = 1 := hxo ▸ pow_orderOf_eq_one x
  set Y : ↥A := ⟨y, hyA⟩ with hY
  set X : ↥A := ⟨x, hxAL.1⟩ with hX
  have hθX : theta h.toSetup12 X = QuotientGroup.mk (⟨x, hxAL.2⟩ : ↥L) :=
    theta_of_mem h.toSetup12 X hxAL.2
  have hx1 : (QuotientGroup.mk (⟨x, hxAL.2⟩ : ↥L) : OTwoQuot L) ≠ 1 := by
    intro h1
    have hmem : x ∈ pCoreOf 2 L := (mem_pCore_iff' _).mp ((QuotientGroup.eq_one_iff _).mp h1)
    obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 L ⟨x, hmem⟩
    have h2 : x ^ 2 ^ j = 1 := congrArg Subtype.val hj
    have hd1 : orderOf x ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one h2
    rw [hxo] at hd1
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow hd1)
    omega
  have hθX3 : (QuotientGroup.mk (⟨x, hxAL.2⟩ : ↥L) : OTwoQuot L) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨x, hxAL.2⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, QuotientGroup.mk_one]
  have hY3 : Y ^ 3 = 1 := Subtype.ext (by simpa using hy3)
  have hθY3 : theta h.toSetup12 Y ^ 3 = 1 := by
    have : thetaHom h.toSetup12 (Y ^ 3) = 1 := by rw [hY3, map_one]
    rwa [map_pow] at this
  have hcomm : (QuotientGroup.mk (⟨x, hxAL.2⟩ : ↥L) : OTwoQuot L) * theta h.toSetup12 Y =
      theta h.toSetup12 Y * QuotientGroup.mk (⟨x, hxAL.2⟩ : ↥L) := by
    rw [← hθX]
    have hXY : X * Y = Y * X := Subtype.ext (by simpa using hxy.symm)
    have := congrArg (thetaHom h.toSetup12) hXY
    rw [map_mul, map_mul] at this
    exact this
  have hmem := mem_zpowers_of_commute (pRank_quot_le_one h.rankL) hx1 hθX3 hθY3 hcomm
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hxk : x ^ k ∈ A ⊓ L := Subgroup.zpow_mem _ hxAL k
  have hxk3 : (x ^ k) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  have hcomm' : Commute (x ^ k) y := (Commute.zpow_left (show Commute x y from hxy.symm) k)
  refine ⟨x ^ k, hxk, (x ^ k)⁻¹ * y, ?_, ?_, ?_, by group⟩
  · rw [mem_K_iff]
    refine ⟨A.mul_mem (A.inv_mem hxk.1) hyA, ?_⟩
    have h1 : theta h.toSetup12 (⟨(x ^ k)⁻¹ * y, A.mul_mem (A.inv_mem hxk.1) hyA⟩ : ↥A) = 1 := by
      have e : (⟨(x ^ k)⁻¹ * y, A.mul_mem (A.inv_mem hxk.1) hyA⟩ : ↥A) = (X ^ k)⁻¹ * Y :=
        Subtype.ext (by simp [hX, hY])
      have : thetaHom h.toSetup12 ((X ^ k)⁻¹ * Y) = 1 := by
        rw [map_mul, map_inv, map_zpow]
        change (theta h.toSetup12 X ^ k)⁻¹ * theta h.toSetup12 Y = 1
        rw [hθX, hk]
        exact inv_mul_cancel _
      rw [e]
      exact this
    exact (theta_eq_one_iff h.toSetup12 _).mp h1
  · exact Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hxk3)
  · have hc3 : ((x ^ k)⁻¹ * y) ^ 3 = 1 := by
      rw [(hcomm'.inv_left).mul_pow, inv_pow, hxk3, hy3]
      simp
    exact Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hc3)

end Decomp

section Orders

omit [Finite G] in
private theorem exists_elemAbelian_nine [Finite G] (hexp : ∀ y ∈ A, Odd (orderOf y) → y ^ 3 = 1)
    {H : Subgroup G} (hHA : H ≤ A) (h9 : 9 ∣ Nat.card H) :
    ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥H) 3 (n := 2) (by simpa using h9)
  have hcard : Nat.card (K.map H.subtype) = 9 := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hK]
    norm_num
  refine ⟨K.map H.subtype, Subgroup.map_subtype_le K, ⟨?_, ?_⟩, hcard⟩
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := ↥(K.map H.subtype))
      (by rw [hcard]; norm_num)
  · intro x hx
    have hxA : x ∈ A := hHA (Subgroup.map_subtype_le K hx)
    have hd : orderOf x ∣ 9 := by
      have := orderOf_dvd_natCard (⟨x, hx⟩ : ↥(K.map H.subtype))
      rwa [Subgroup.orderOf_mk x hx, hcard] at this
    exact hexp x hxA (Odd.of_dvd_nat (by decide : Odd 9) hd)

private theorem not_nine_dvd_of_le_L (h : Core12 A L) {H : Subgroup G} (hHA : H ≤ A)
    (hHL : H ≤ L) : ¬ 9 ∣ Nat.card H := by
  intro h9
  obtain ⟨E, hEH, hE, hEc⟩ := exists_elemAbelian_nine h.exp3 hHA h9
  have := CFSG.Quasithin.le_pRank Nat.prime_three (hEH.trans hHL) hE (k := 2)
    (by rw [hEc]; norm_num)
  have h1 := h.rankL
  omega

private theorem mem_pCore_of_mem_K (h : Setup12 A L) {x : G} (hxL : x ∈ L)
    (hxK : x ∈ centralizerSection A L (pCoreOf 2 L)) : x ∈ pCoreOf 2 L := by
  refine h.centerless x hxL (fun l hl => ?_)
  exact ((mem_K_iff).mp hxK).2 l hl

private theorem orderOf_three_not_mem_pCore {x : G} (hxo : orderOf x = 3) : x ∉ pCoreOf 2 L := by
  intro hmem
  obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 L ⟨x, hmem⟩
  have h2 : x ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hd1 : orderOf x ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one h2
  rw [hxo] at hd1
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow hd1)
  omega

private theorem not_nine_dvd_of_le_K (h : Core12 A L) (hrankA : CFSG.Open.pRank 3 A = 2)
    {H : Subgroup G} (hHK : H ≤ centralizerSection A L (pCoreOf 2 L)) : ¬ 9 ∣ Nat.card H := by
  intro h9
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHA : H ≤ A := hHK.trans (centralizerSection_le_left _ _ _)
  obtain ⟨E, hEH, hE, hEc⟩ := exists_elemAbelian_nine h.exp3 hHA h9
  have hEN : E ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) :=
    (hEH.trans hHA).trans (A_le_normalizer_inf h.toSetup12)
  obtain ⟨x, hxAL, hxo, hxC⟩ := exists_orderOf_eq_of_isPGroup_normalizer
    (isPGroup_of_isElemAbelian hE) hEN h.three_dvd
  have hxE : x ∉ E := by
    intro hxE
    exact orderOf_three_not_mem_pCore hxo (mem_pCore_of_mem_K h.toSetup12 hxAL.2 (hHK (hEH hxE)))
  obtain ⟨hE2, hc2⟩ := exists_elemAbelian_sup_zpowers hE hxo
    (fun e he => Subgroup.mem_centralizer_iff.mp hxC e he) hxE
  have hle : E ⊔ Subgroup.zpowers x ≤ A :=
    sup_le (hEH.trans hHA) (Subgroup.zpowers_le.mpr hxAL.1)
  have h3 := CFSG.Quasithin.le_pRank Nat.prime_three hle hE2 (k := 3)
    (by rw [hc2, hEc]; norm_num)
  omega

end Orders

section Final

omit [Finite G] in
private theorem exists_orderOf_three_of_ne_bot (hexp : ∀ y ∈ A, Odd (orderOf y) → y ^ 3 = 1)
    {X : Subgroup G} (hXA : X ≤ A) (hne : oTwoUpper X ≠ ⊥) :
    ∃ x ∈ X, orderOf x = 3 := by
  by_contra hno
  push Not at hno
  apply hne
  rw [eq_bot_iff, oTwoUpper, Subgroup.closure_le]
  rintro x ⟨hxX, hxo⟩
  rw [SetLike.mem_coe, Subgroup.mem_bot]
  by_contra hx1
  have hx3 : x ^ 3 = 1 := hexp x (hXA hxX) hxo
  exact hno x hxX (orderOf_eq_prime hx3 hx1)

omit [Finite G] in
theorem three_dvd_card_oTwoUpper (hexp : ∀ y ∈ A, Odd (orderOf y) → y ^ 3 = 1)
    {X : Subgroup G} (hXA : X ≤ A) (hne : oTwoUpper X ≠ ⊥) : 3 ∣ Nat.card ↥(oTwoUpper X) := by
  obtain ⟨x, hxX, hxo⟩ := exists_orderOf_three_of_ne_bot hexp hXA hne
  have hxo' : Odd (orderOf x) := by rw [hxo]; decide
  have hx : x ∈ oTwoUpper X := mem_oTwoUpper_of_odd hxX hxo'
  have := orderOf_dvd_natCard (⟨x, hx⟩ : ↥(oTwoUpper X))
  rwa [Subgroup.orderOf_mk x hx, hxo] at this

private theorem A_eq_sup (h : Core12 A L) (hAO : oTwoUpper A = A) :
    A = oTwoUpper (A ⊓ L) ⊔ oTwoUpper (centralizerSection A L (pCoreOf 2 L)) := by
  apply le_antisymm
  · calc A = oTwoUpper A := hAO.symm
      _ ≤ _ := by
        rw [oTwoUpper, Subgroup.closure_le]
        rintro y ⟨hyA, hy⟩
        obtain ⟨a, ha, c, hc, hao, hco, rfl⟩ := exists_decomp h hyA hy
        exact Subgroup.mul_mem_sup (mem_oTwoUpper_of_odd ha hao) (mem_oTwoUpper_of_odd hc hco)
  · exact sup_le ((oTwoUpper_le _).trans inf_le_left)
      ((oTwoUpper_le _).trans (centralizerSection_le_left _ _ _))

private theorem padicValNat_YL (h : Core12 A L) (hne : oTwoUpper (A ⊓ L) ≠ ⊥) :
    padicValNat 3 (Nat.card ↥(oTwoUpper (A ⊓ L))) = 1 := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYLA : oTwoUpper (A ⊓ L) ≤ A ⊓ L := oTwoUpper_le _
  have hpos : 0 < Nat.card ↥(oTwoUpper (A ⊓ L)) := Nat.card_pos
  have h3 := three_dvd_card_oTwoUpper h.exp3 (inf_le_left : A ⊓ L ≤ A) hne
  have h9 : ¬ 9 ∣ Nat.card ↥(oTwoUpper (A ⊓ L)) :=
    not_nine_dvd_of_le_L h (hYLA.trans inf_le_left) (hYLA.trans inf_le_right)
  have h1 : 1 ≤ padicValNat 3 (Nat.card ↥(oTwoUpper (A ⊓ L))) :=
    one_le_padicValNat_of_dvd hpos.ne' h3
  have h2 : ¬ 2 ≤ padicValNat 3 (Nat.card ↥(oTwoUpper (A ⊓ L))) := fun h2 =>
    h9 (by simpa using (padicValNat_dvd_iff_le hpos.ne').mpr h2)
  omega

omit [Finite G] in
private theorem card_sup_le_of_commute {Q : Type*} [Group Q] [Finite Q] {X C : Subgroup Q}
    (hcomm : ∀ u ∈ X, ∀ v ∈ C, u * v = v * u) :
    Nat.card ↥(X ⊔ C) ≤ Nat.card ↥X * Nat.card ↥C := by
  have hc : ∀ (x : X) (y : C), Commute (X.subtype x) (C.subtype y) := fun x y => hcomm x x.2 y y.2
  let f : X × C →* Q := MonoidHom.noncommCoprod X.subtype C.subtype hc
  have hrange : f.range = X ⊔ C := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  calc Nat.card ↥(X ⊔ C) = Nat.card f.range := by rw [hrange]
    _ ≤ Nat.card (X × C) := Nat.card_le_card_of_surjective _ f.rangeRestrict_surjective
    _ = Nat.card ↥X * Nat.card ↥C := Nat.card_prod _ _

omit [Finite G] in
private theorem card_range_le_three {H Q : Type*} [Group H] [Finite H] [Group Q] [Finite Q]
    (hQ : ∀ q : Q, q ^ 3 = 1) (f : H →* Q) (hH : padicValNat 3 (Nat.card H) ≤ 1) :
    Nat.card f.range ≤ 3 := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 ↥f.range := fun g => ⟨1, Subtype.ext (by simpa using hQ g)⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hd : 3 ^ k ∣ Nat.card H := hk ▸ Subgroup.card_range_dvd f
  have hk1 : k ≤ 1 :=
    ((padicValNat_dvd_iff_le (Nat.card_pos (α := H)).ne').mp hd).trans hH
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
    _ = 3 := by norm_num

private theorem exists_Q_bounds (h : Core12 A L) (hAO : oTwoUpper A = A)
    (hQ : ∀ q : OTwoQuot A, q ^ 3 = 1) :
    ∃ a c : ℕ, Nat.card (OTwoQuot A) ≤ a * c ∧
      (padicValNat 3 (Nat.card ↥(oTwoUpper (A ⊓ L))) ≤ 1 → a ≤ 3) ∧
      (padicValNat 3 (Nat.card ↥(oTwoUpper (centralizerSection A L (pCoreOf 2 L)))) ≤ 1 → c ≤ 3) ∧
      (∃ k : ℕ, c = 3 ^ k) ∧ c ∣ Nat.card ↥(oTwoUpper (centralizerSection A L (pCoreOf 2 L))) := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K : Subgroup G := centralizerSection A L (pCoreOf 2 L) with hK
  set YL : Subgroup G := oTwoUpper (A ⊓ L) with hYL
  set YC : Subgroup G := oTwoUpper K with hYC
  have hYLAL : YL ≤ A ⊓ L := oTwoUpper_le _
  have hYCK : YC ≤ K := oTwoUpper_le _
  have hYLA : YL ≤ A := hYLAL.trans inf_le_left
  have hYCA : YC ≤ A := hYCK.trans (centralizerSection_le_left _ _ _)
  let π : ↥A →* OTwoQuot A := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥A)
  let fL : ↥(YL.subgroupOf A) →* OTwoQuot A := π.comp (YL.subgroupOf A).subtype
  let fC : ↥(YC.subgroupOf A) →* OTwoQuot A := π.comp (YC.subgroupOf A).subtype
  have hcardL : Nat.card ↥(YL.subgroupOf A) = Nat.card ↥YL :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYLA).toEquiv
  have hcardC : Nat.card ↥(YC.subgroupOf A) = Nat.card ↥YC :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYCA).toEquiv
  have hsup : fL.range ⊔ fC.range = ⊤ := by
    have h1 : fL.range = (YL.subgroupOf A).map π := by
      show (π.comp (YL.subgroupOf A).subtype).range = _
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have h2 : fC.range = (YC.subgroupOf A).map π := by
      show (π.comp (YC.subgroupOf A).subtype).range = _
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [h1, h2, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hYLA hYCA, ← A_eq_sup h hAO,
      Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hcomm : ∀ u ∈ fL.range, ∀ v ∈ fC.range, u * v = v * u := by
    rintro _ ⟨a', rfl⟩ _ ⟨b', rfl⟩
    have haL : ((a' : ↥(YL.subgroupOf A)) : G) ∈ L := (hYLAL (Subgroup.mem_subgroupOf.mp a'.2)).2
    have hbK : ((b' : ↥(YC.subgroupOf A)) : G) ∈ K := hYCK (Subgroup.mem_subgroupOf.mp b'.2)
    set a : G := ((a' : ↥(YL.subgroupOf A)) : G)
    set b : G := ((b' : ↥(YC.subgroupOf A)) : G)
    have haA : a ∈ A := hYLA (Subgroup.mem_subgroupOf.mp a'.2)
    have hbA : b ∈ A := hYCA (Subgroup.mem_subgroupOf.mp b'.2)
    have hcommL : a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 L := ((mem_K_iff).mp hbK).2 a haL
    have hcommA : a * b * a⁻¹ * b⁻¹ ∈ A :=
      A.mul_mem (A.mul_mem (A.mul_mem haA hbA) (A.inv_mem haA)) (A.inv_mem hbA)
    have hle : pCoreOf 2 L ⊓ A ≤ pCoreOf 2 A :=
      le_pCoreOf_of_le_normalizer 2 inf_le_right
        (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨normalizer_le_normalizer_pCoreOf 2 L (h.normalizes hg), Subgroup.le_normalizer hg⟩)
        ((pCoreOf_isPGroup 2 L).to_le inf_le_left)
    have hmem : a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 A := hle ⟨hcommL, hcommA⟩
    set a'' : ↥A := ⟨a, haA⟩
    set b'' : ↥A := ⟨b, hbA⟩
    have hmem' : (a'' * b'' * a''⁻¹ * b''⁻¹ : ↥A) ∈ CFSG.Open.pCore 2 ↥A :=
      (mem_pCore_iff' (L := A) _).mpr hmem
    have h1 : π (a'' * b'' * a''⁻¹ * b''⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hmem'
    have h2 : π a'' * π b'' * (π a'')⁻¹ * (π b'')⁻¹ = 1 := by
      simpa [map_mul, map_inv] using h1
    show π a'' * π b'' = π b'' * π a''
    calc π a'' * π b'' = (π a'' * π b'' * (π a'')⁻¹ * (π b'')⁻¹) * (π b'' * π a'') := by group
      _ = π b'' * π a'' := by rw [h2, one_mul]
  refine ⟨Nat.card fL.range, Nat.card fC.range, ?_, ?_, ?_, ?_, ?_⟩
  · have := card_sup_le_of_commute hcomm
    rwa [hsup, Subgroup.card_top] at this
  · intro hle
    exact card_range_le_three hQ fL (by rw [hcardL]; exact hle)
  · intro hle
    exact card_range_le_three hQ fC (by rw [hcardC]; exact hle)
  · have hP : IsPGroup 3 ↥fC.range := fun g => ⟨1, Subtype.ext (by simpa using hQ g)⟩
    exact hP.exists_card_eq
  · rw [← hcardC]
    exact Subgroup.card_range_dvd fC

omit [Finite G] in
theorem exp_three_of_struct (hstruct : IsElemAbelianOfRank 3 2 (OTwoQuot A) ∨ IsPOnePlusTwo 3 (OTwoQuot A)) :
    ∀ q : OTwoQuot A, q ^ 3 = 1 := by
  rcases hstruct with hE | ⟨-, -, hexp⟩
  · obtain ⟨e⟩ := hE
    intro q
    apply e.injective
    rw [map_pow, map_one]
    apply Multiplicative.toAdd.injective
    funext i
    have h1 : ∀ a : ZMod 3, 3 • a = 0 := by decide
    simpa [toAdd_pow] using h1 (Multiplicative.toAdd (e q) i)
  · exact hexp

omit [Finite G] in
private theorem card_Q_ge_nine
    (hstruct : IsElemAbelianOfRank 3 2 (OTwoQuot A) ∨ IsPOnePlusTwo 3 (OTwoQuot A)) :
    9 ≤ Nat.card (OTwoQuot A) := by
  rcases hstruct with hE | ⟨-, hcard, -⟩
  · obtain ⟨e⟩ := hE
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card]
  · rw [hcard]
    norm_num

theorem core15312Two (h : Core12 A L) (hAO : oTwoUpper A = A) (hrankA : CFSG.Open.pRank 3 A = 2)
    (hne : oTwoUpper (A ⊓ L) ≠ ⊥)
    (hstruct : IsElemAbelianOfRank 3 2 (OTwoQuot A) ∨ IsPOnePlusTwo 3 (OTwoQuot A)) :
    A = oTwoUpper (A ⊓ L) ⊔ oTwoUpper (centralizerSection A L (pCoreOf 2 L)) ∧
      padicValNat 3 (Nat.card ↥(oTwoUpper (A ⊓ L))) = 1 ∧
      padicValNat 3 (Nat.card ↥(oTwoUpper (centralizerSection A L (pCoreOf 2 L)))) = 1 ∧
      IsElemAbelianOfRank 3 2 (OTwoQuot A) := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ := exp_three_of_struct hstruct
  have hYL := padicValNat_YL h hne
  obtain ⟨a, c, hQac, ha, hc, ⟨k, hck⟩, hcdvd⟩ := exists_Q_bounds h hAO hQ
  have ha3 : a ≤ 3 := ha hYL.le
  have hYCpos : 0 < Nat.card ↥(oTwoUpper (centralizerSection A L (pCoreOf 2 L))) := Nat.card_pos
  have h9 : ¬ 9 ∣ Nat.card ↥(oTwoUpper (centralizerSection A L (pCoreOf 2 L))) := not_nine_dvd_of_le_K h hrankA (oTwoUpper_le _)
  have hYCle : padicValNat 3 (Nat.card ↥(oTwoUpper (centralizerSection A L (pCoreOf 2 L)))) ≤ 1 := by
    by_contra hcon
    exact h9 (by simpa using (padicValNat_dvd_iff_le hYCpos.ne').mpr (by omega : 2 ≤ padicValNat 3 (Nat.card ↥(oTwoUpper (centralizerSection A L (pCoreOf 2 L))))))
  have hc3 : c ≤ 3 := hc hYCle
  have hQ9 := card_Q_ge_nine hstruct
  have hcge : 3 ≤ c := by
    by_contra hlt
    push Not at hlt
    have : a * c ≤ 3 * 2 := Nat.mul_le_mul ha3 (by omega)
    omega
  have hk1 : k ≠ 0 := by
    rintro rfl
    simp at hck
    omega
  have h3 : 3 ∣ Nat.card ↥(oTwoUpper (centralizerSection A L (pCoreOf 2 L))) := by
    have : 3 ∣ c := by rw [hck]; exact dvd_pow_self 3 hk1
    exact this.trans hcdvd
  have hYC1 : padicValNat 3 (Nat.card ↥(oTwoUpper (centralizerSection A L (pCoreOf 2 L)))) = 1 := by
    have : 1 ≤ padicValNat 3 (Nat.card ↥(oTwoUpper (centralizerSection A L (pCoreOf 2 L)))) := one_le_padicValNat_of_dvd hYCpos.ne' h3
    omega
  refine ⟨A_eq_sup h hAO, hYL, hYC1, ?_⟩
  rcases hstruct with hE | ⟨-, hcard, -⟩
  · exact hE
  · exfalso
    have h99 : Nat.card (OTwoQuot A) ≤ 9 :=
      hQac.trans (by calc a * c ≤ 3 * 3 := Nat.mul_le_mul ha3 hc3
        _ = 9 := rfl)
    rw [hcard] at h99
    norm_num at h99

end Final

end Theta

end SBc

end CFSG.Quasithin
