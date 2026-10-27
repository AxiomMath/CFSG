module

public import CFSG.RankThree.PartTwo.KFacts.L34Sylow
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLinearPointKernelCentralizer
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch1EightFourInit
public import CFSG.Quasithin.Vol2.Ch5Statements

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace L34

theorem exists_elemAbelian_nine_of_isPSL {X : Type} [Group X] (h : IsPSL 3 2 2 X) :
    ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  have hk : Nat.card F = 4 := by rw [hF]; norm_num
  let e' : X ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F :=
    e.trans (QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 F).symm
  set E₀ := CFSG.RankThree.PartTwo.KFacts.L34.eZero F with hE₀
  refine ⟨E₀.map e'.symm.toMonoidHom, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp b.2
    apply Subtype.ext
    change (a : X) * b = b * a
    rw [← hxa, ← hyb, ← map_mul, ← map_mul,
      CFSG.RankThree.PartTwo.KFacts.L34.commute_of_mem_eZero hk hx hy]
  · obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, CFSG.RankThree.PartTwo.KFacts.L34.pow_three_of_mem_eZero hk hy, map_one]
  · rw [Subgroup.card_map_of_injective e'.symm.injective]
    exact CFSG.RankThree.PartTwo.KFacts.L34.card_eZero hk

variable {G : Type} [Group G] [Finite G]

theorem exists_elemAbelian_of_quot {K : Subgroup G} {E₁ : Subgroup (O2Q K)}
    (hE₁ : IsElemAbelian 3 E₁) {r : ℕ} (hr : Nat.card E₁ = 3 ^ r) :
    ∃ E : Subgroup G, E ≤ K ∧ IsElemAbelian 3 E ∧ ∃ s, r ≤ s ∧ Nat.card E = 3 ^ s := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥K) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).exists_card_eq
    rw [hk]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    norm_num at this
  have h1 : r ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (O2Q K)) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top hE₁ hr
  rw [CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥K) hN] at h1
  obtain ⟨E₀, -, hE₀, hc⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num)
    (⊤ : Subgroup ↥K)
  refine ⟨E₀.map K.subtype, Subgroup.map_subtype_le E₀,
    CFSG.SectionRank.isElemAbelian_map hE₀ K.subtype, CFSG.Open.pRank 3 (⊤ : Subgroup ↥K), h1, ?_⟩
  rw [Subgroup.card_map_of_injective K.subtype_injective, hc]

omit [Finite G] in
theorem mem_pCoreOf_iff_pCore {K : Subgroup G} (x : ↥K) :
    (x : G) ∈ pCoreOf 2 K ↔ x ∈ CFSG.pCore 2 ↥K := CFSG.mem_openPCoreOf_iff x

omit [Finite G] in
theorem pow_comm_mem {K O : Subgroup G} {c : G} (hcO : c ∈ Subgroup.normalizer (O : Set G))
    (hcc : ∀ x ∈ K, c * x * c⁻¹ * x⁻¹ ∈ O) (m : ℕ) :
    ∀ x ∈ K, c ^ m * x * (c ^ m)⁻¹ * x⁻¹ ∈ O := by
  induction m with
  | zero =>
    intro x _
    rw [pow_zero, one_mul, inv_one, mul_one, mul_inv_cancel]
    exact O.one_mem
  | succ m ih =>
    intro x hx
    have h3 : c * (c ^ m * x * (c ^ m)⁻¹ * x⁻¹) * c⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp hcO _).mp (ih x hx)
    have e : c ^ (m + 1) * x * (c ^ (m + 1))⁻¹ * x⁻¹ =
        (c * (c ^ m * x * (c ^ m)⁻¹ * x⁻¹) * c⁻¹) * (c * x * c⁻¹ * x⁻¹) := by group
    rw [e]
    exact O.mul_mem h3 (hcc x hx)

omit [Finite G] in
theorem mem_pCoreOf_of_centralizes {K : Subgroup G} (hK : IsPSL 3 2 2 (O2Q K)) {t : G}
    (htK : t ∈ K) (htc : ∀ x ∈ K, t * x * t⁻¹ * x⁻¹ ∈ pCoreOf 2 K) : t ∈ pCoreOf 2 K := by
  have hS : IsSimpleGroup (O2Q K) := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2 hK).2
  have hnab : ∃ a b : O2Q K, a * b ≠ b * a :=
    Vol2Native.A312L.Seven.nonabelian_of_card_not_prime (by
      rw [Ch1Four.card_of_isPSL_three_four hK]; norm_num)
  set τ := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hτ
  have hz : τ ⟨t, htK⟩ ∈ Subgroup.center (O2Q K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) y
    have h1 : ((⟨t, htK⟩ : ↥K) * ⟨k, hk⟩ * (⟨t, htK⟩ : ↥K)⁻¹ * (⟨k, hk⟩ : ↥K)⁻¹ : ↥K) ∈
        CFSG.pCore 2 ↥K := (mem_pCoreOf_iff_pCore _).mp (htc k hk)
    have h2 : τ ((⟨t, htK⟩ : ↥K) * ⟨k, hk⟩ * (⟨t, htK⟩ : ↥K)⁻¹ * (⟨k, hk⟩ : ↥K)⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr h1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    calc τ ⟨k, hk⟩ * τ ⟨t, htK⟩ = (τ ⟨t, htK⟩ * τ ⟨k, hk⟩ * (τ ⟨t, htK⟩)⁻¹ * (τ ⟨k, hk⟩)⁻¹)⁻¹ *
          (τ ⟨t, htK⟩ * τ ⟨k, hk⟩) := by group
      _ = τ ⟨t, htK⟩ * τ ⟨k, hk⟩ := by rw [h2, inv_one, one_mul]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (O2Q K)) with h | h
  · rw [h, Subgroup.mem_bot] at hz
    exact (mem_pCoreOf_iff_pCore ⟨t, htK⟩).mpr ((QuotientGroup.eq_one_iff _).mp hz)
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center (O2Q K) := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem three_le_pRank_of_centralizes {K : Subgroup G} (hK : IsPSL 3 2 2 (O2Q K)) {c : G}
    (hcN : c ∈ Subgroup.normalizer (K : Set G)) (hc3 : c ^ 3 ∈ pCoreOf 2 K) (hcK : c ∉ K)
    (hcc : ∀ x ∈ K, c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 K) :
    3 ≤ CFSG.Open.pRank 3 (K ⊔ Subgroup.zpowers c) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E₁, hE₁, hc9⟩ := exists_elemAbelian_nine_of_isPSL hK
  obtain ⟨E, hEK, hE, s, hs, hEc⟩ :=
    exists_elemAbelian_of_quot hE₁ (r := 2) (by rw [hc9]; norm_num)
  set O := pCoreOf 2 K with hO
  set X := K ⊔ Subgroup.zpowers c with hX
  have hKX : K ≤ X := le_sup_left
  have hcX : c ∈ X := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hOK : O ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hXN : X ≤ Subgroup.normalizer (O : Set G) := by
    refine sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K) ?_
    rw [Subgroup.zpowers_le]
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K hcN
  set N : Subgroup ↥X := O.subgroupOf X with hNdef
  have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer (hOK.trans hKX)).mpr hXN
  have hN3 : ¬ 3 ∣ Nat.card N := by
    have h1 : Nat.card N = Nat.card O := Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (hOK.trans hKX)).toEquiv
    obtain ⟨k, hk⟩ := hO2.exists_card_eq
    rw [h1, hk]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    norm_num at this
  set π := QuotientGroup.mk' N with hπ
  set Eb := (E.subgroupOf X).map π with hEb
  set cb : ↥X ⧸ N := π ⟨c, hcX⟩ with hcb
  have hπ1 : ∀ x : ↥X, π x = 1 ↔ (x : G) ∈ O := by
    intro x
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hEO : ∀ e ∈ E, e ∈ O → e = 1 := by
    intro e he heO
    obtain ⟨k, hk⟩ := hO2 ⟨e, heO⟩
    have h1 : e ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h3 : e ^ 3 = 1 := hE.2 e he
    have h4 : orderOf e ∣ Nat.gcd (2 ^ k) 3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1)
      (orderOf_dvd_of_pow_eq_one h3)
    have h5 : Nat.gcd (2 ^ k) 3 = 1 :=
      Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)
    rw [h5, Nat.dvd_one, orderOf_eq_one_iff] at h4
    exact h4
  have hEbc : Nat.card Eb = 3 ^ s := by
    have hinj : Set.InjOn π ((E.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
      intro x hx y hy hxy
      have hx' : (x : G) ∈ E := Subgroup.mem_subgroupOf.mp hx
      have hy' : (y : G) ∈ E := Subgroup.mem_subgroupOf.mp hy
      have h1 : π (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
      rw [hπ1] at h1
      have h3 : (x : G)⁻¹ * (y : G) ∈ E := E.mul_mem (E.inv_mem hx') hy'
      have h4 := hEO _ h3 h1
      exact Subtype.ext (inv_mul_eq_one.mp h4)
    have h := Nat.card_image_of_injOn hinj
    rw [← Subgroup.coe_map] at h
    rw [hEb]
    refine h.trans ?_
    rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hEK.trans hKX)).toEquiv
  have hcbE : ∀ y ∈ Eb, cb * y = y * cb := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hxK : ((x : ↥X) : G) ∈ K := hEK (Subgroup.mem_subgroupOf.mp hx)
    have h1 : π (⟨c, hcX⟩ * x * (⟨c, hcX⟩ : ↥X)⁻¹ * x⁻¹) = 1 := by
      rw [hπ1]
      exact hcc _ hxK
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    rw [← hcb] at h1
    calc cb * π x = (cb * π x * cb⁻¹ * (π x)⁻¹) * π x * cb := by group
      _ = π x * cb := by rw [h1, one_mul]
  have hcb3 : cb ^ 3 = 1 := by
    rw [hcb, ← map_pow, hπ1, Subgroup.coe_pow]
    exact hc3
  have hcbE' : cb ∉ Eb := by
    intro hm
    obtain ⟨x, hx, hxc⟩ := Subgroup.mem_map.mp hm
    have h1 : π (x⁻¹ * ⟨c, hcX⟩) = 1 := by
      rw [map_mul, map_inv, hxc, ← hcb, inv_mul_cancel]
    rw [hπ1] at h1
    have hxK : ((x : ↥X) : G) ∈ K := hEK (Subgroup.mem_subgroupOf.mp hx)
    apply hcK
    have h3 : ((x : ↥X) : G)⁻¹ * c ∈ K := hOK h1
    have h4 := K.mul_mem hxK h3
    simpa using h4
  set Q := Eb ⊔ Subgroup.zpowers cb with hQ
  have hEbab : Eb ≤ Subgroup.centralizer (Eb : Set (↥X ⧸ N)) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    have hxE := Subgroup.mem_subgroupOf.mp hx
    have hwE := Subgroup.mem_subgroupOf.mp hw
    have h1 : ((w : ↥X) : G) * (x : ↥X) = (x : ↥X) * (w : ↥X) := by
      have := hE.1
      exact congrArg Subtype.val (mul_comm' (⟨_, hwE⟩ : ↥E) ⟨_, hxE⟩)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h1
  have hzc : Subgroup.zpowers cb ≤ Subgroup.centralizer (Eb : Set (↥X ⧸ N)) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro z hz
    exact (hcbE z hz).symm
  have hzz : Subgroup.zpowers cb ≤ Subgroup.centralizer (Subgroup.zpowers cb : Set (↥X ⧸ N)) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((Commute.refl cb).zpow_left k).eq
  have hEz : Eb ≤ Subgroup.centralizer (Subgroup.zpowers cb : Set (↥X ⧸ N)) :=
    Subgroup.le_centralizer_iff.mp hzc
  have hQE : Q ≤ Subgroup.centralizer (Eb : Set (↥X ⧸ N)) := sup_le hEbab hzc
  have hQZ : Q ≤ Subgroup.centralizer (Subgroup.zpowers cb : Set (↥X ⧸ N)) := sup_le hEz hzz
  have hQC : Q ≤ Subgroup.centralizer (Q : Set (↥X ⧸ N)) :=
    sup_le (Subgroup.le_centralizer_iff.mp hQE) (Subgroup.le_centralizer_iff.mp hQZ)
  have hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (hQC hy) x hx
  let P : Subgroup (↥X ⧸ N) :=
    { carrier := {x | x ∈ Q ∧ x ^ 3 = 1}
      mul_mem' := fun {a b} ha hb => ⟨Q.mul_mem ha.1 hb.1, by
        rw [(Commute.mul_pow (hQab a ha.1 b hb.1) 3), ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨Q.one_mem, one_pow 3⟩
      inv_mem' := fun {a} ha => ⟨Q.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hEP : Eb ≤ P := by
    intro y hy
    refine ⟨Subgroup.mem_sup_left hy, ?_⟩
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_pow]
    have hwE := Subgroup.mem_subgroupOf.mp hw
    have h1 : w ^ 3 = 1 := Subtype.ext (by simpa using hE.2 _ hwE)
    rw [h1, map_one]
  have hcP : Subgroup.zpowers cb ≤ P := by
    rw [Subgroup.zpowers_le]
    exact ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers cb), hcb3⟩
  have hQ3 : ∀ x ∈ Q, x ^ 3 = 1 := fun x hx => (sup_le hEP hcP hx).2
  have hcb1 : cb ≠ 1 := fun h => hcbE' (h ▸ Eb.one_mem)
  have hcbo : orderOf cb = 3 := orderOf_eq_prime hcb3 hcb1
  have hcbN : Subgroup.zpowers cb ≤ Subgroup.normalizer (Eb : Set (↥X ⧸ N)) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hcbE y hy, mul_inv_cancel_right]
      exact hy
    · intro hy
      have h1 : cb * y * cb⁻¹ = y := by
        have h3 := hcbE _ hy
        calc cb * y * cb⁻¹ = cb⁻¹ * (cb * (cb * y * cb⁻¹)) := by group
          _ = cb⁻¹ * (cb * y * cb⁻¹ * cb) := by rw [h3]
          _ = y := by group
      rw [← h1]
      exact hy
  have hinf : Eb ⊓ Subgroup.zpowers cb = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxE, hxc⟩
    rw [Subgroup.mem_bot]
    by_contra hx1
    have hxo : orderOf x = 3 := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxc
      refine orderOf_eq_prime ?_ hx1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hcb3, one_zpow]
    have hle : Subgroup.zpowers x ≤ Subgroup.zpowers cb := Subgroup.zpowers_le.mpr hxc
    have heq : Subgroup.zpowers x = Subgroup.zpowers cb :=
      Subgroup.eq_of_le_of_card_ge hle
        (le_of_eq (by rw [Nat.card_zpowers, Nat.card_zpowers, hxo, hcbo]))
    apply hcbE'
    have : cb ∈ Subgroup.zpowers x := heq ▸ Subgroup.mem_zpowers cb
    exact (Subgroup.zpowers_le.mpr hxE) this
  have hQc : Nat.card Q = 3 ^ (s + 1) := by
    have h1 := CFSG.ShultStronglyClosedTI.LinearChain.card_sup_mul_card_inf_of_le_normalizer hcbN
    rw [hinf, Subgroup.card_bot, mul_one, hEbc, Nat.card_zpowers, hcbo] at h1
    rw [hQ, h1, pow_succ]
  have hQe : IsElemAbelian 3 Q :=
    ⟨⟨⟨fun a b => Subtype.ext (hQab a a.2 b b.2)⟩⟩, hQ3⟩
  have h1 : s + 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (↥X ⧸ N)) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top hQe hQc
  rw [CFSG.SectionRank.pRank_quotient_eq N hN3,
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup X] at h1
  omega

end L34

end CFSG.Quasithin.H13.Ch9
