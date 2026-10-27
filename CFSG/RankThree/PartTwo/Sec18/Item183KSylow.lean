module

public import CFSG.RankThree.PartTwo.Sec18.Item183KStatements
public import CFSG.RankThree.PartTwo.Sec18.Item183KSL
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Source.GammaTwoSubgroups
import CFSG.RankThree.PartTwo.Sec18.Transport

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G] {A M K S : Subgroup G} {c : G}

namespace Hyp183

variable (h : Hyp183 G A M c K)
include h

theorem le_normalizer : A ≤ Subgroup.normalizer (K : Set G) :=
  fun a ha => (h.inducesInnerMod a ha).1

theorem sup_le_normalizer : A ⊔ K ≤ Subgroup.normalizer (K : Set G) :=
  sup_le h.le_normalizer Subgroup.le_normalizer

theorem isE27 : IsE27 A :=
  isE27_of_mem_partTwoE h.mem_partTwoE

theorem le_centralizer : K ≤ Subgroup.centralizer ({c} : Set G) :=
  Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt

theorem pow_three {a : G} (ha : a ∈ A) : a ^ 3 = 1 :=
  h.isE27.1.2 a ha

theorem commute {a b : G} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a :=
  congrArg Subtype.val (h.isE27.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem mem_of_commute {x : G} (hx : x ^ 3 = 1) (hxA : ∀ a ∈ A, a * x = x * a) : x ∈ A := by
  have hFE := (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
  have hAF : A ∈ partTwoF G := hFE ▸ h.mem_partTwoE
  have hab : CFSG.Assembly.IsElemAbelian 3 (A ⊔ Subgroup.zpowers x) := by
    refine Sec13.isElemAbelian_sup h.isE27.1 (Sec13.isElemAbelian_zpowers hx) fun a ha y hy => ?_
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (show Commute a x from hxA a ha) i).eq
  have heq := hAF.2.1 _ hab le_sup_left
  exact heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

theorem mem_C_iff {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Sec4.thetaQuotCentralizer K ↔ ∀ y ∈ K, g * y * g⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
  obtain ⟨e⟩ := h.quotient_iso
  exact Item183K.mem_thetaQuotCentralizer_iff_of_SL34 e hg

theorem c_mem_C : c ∈ Sec4.thetaQuotCentralizer K := by
  refine (h.mem_C_iff (h.le_normalizer h.mem_A)).mpr fun y hy => ?_
  have hyc : c * y = y * c := (Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hy)).symm
  rw [hyc, mul_inv_cancel_right, mul_inv_cancel]
  exact Subgroup.one_mem _

theorem sectionCentralizer_eq {E : Subgroup G} (hE : E ≤ Subgroup.normalizer (K : Set G)) :
    sectionCentralizer E K (CFSG.Open.pCoreOf 2 K) =
      ((E ⊓ Sec4.thetaQuotCentralizer K : Subgroup G) : Set G) := by
  obtain ⟨e⟩ := h.quotient_iso
  exact Item183K.sectionCentralizer_eq_of_SL34 e hE

theorem commutator_mem_C {a b x y : G} (ha : a ∈ A) (hb : b ∈ A) (hx : x ∈ K) (hy : y ∈ K)
    (hxa : x⁻¹ * a ∈ Sec4.thetaQuotCentralizer K)
    (hyb : y⁻¹ * b ∈ Sec4.thetaQuotCentralizer K) :
    x * y * x⁻¹ * y⁻¹ ∈ Sec4.thetaQuotCentralizer K := by
  set C := Sec4.thetaQuotCentralizer K with hC
  set s := x⁻¹ * a with hs
  set t := y⁻¹ * b with ht
  have haN := h.le_normalizer ha
  have hbN := h.le_normalizer hb
  have hxs : x = a * s⁻¹ := by rw [hs]; group
  have hyt : y = b * t⁻¹ := by rw [ht]; group
  have hab := h.commute ha hb
  have hu : (y * x)⁻¹ * (x * y) ∈ C := by
    have e1 : x * y = a * b * ((b⁻¹ * s⁻¹ * b) * t⁻¹) := by rw [hxs, hyt]; group
    have e2 : y * x = a * b * ((a⁻¹ * t⁻¹ * a) * s⁻¹) := by
      rw [hxs, hyt, hab]
      group
    have e3 : (y * x)⁻¹ * (x * y) = (s * (a⁻¹ * t * a)) * ((b⁻¹ * s⁻¹ * b) * t⁻¹) := by
      rw [e1, e2]
      group
    rw [e3]
    have h1 : a⁻¹ * t * a ∈ C := by
      have := Sec12.conj_mem_thetaQuotCentralizer (inv_mem haN) hyb
      simpa using this
    have h2 : b⁻¹ * s⁻¹ * b ∈ C := by
      have := Sec12.conj_mem_thetaQuotCentralizer (inv_mem hbN) (inv_mem hxa)
      simpa using this
    exact mul_mem (mul_mem hxa h1) (mul_mem h2 (inv_mem hyb))
  have hyxN : y * x ∈ Subgroup.normalizer (K : Set G) :=
    mul_mem (Subgroup.le_normalizer hy) (Subgroup.le_normalizer hx)
  have h1 := Sec12.conj_mem_thetaQuotCentralizer hyxN hu
  have e : y * x * ((y * x)⁻¹ * (x * y)) * (y * x)⁻¹ = x * y * x⁻¹ * y⁻¹ := by group
  rwa [e] at h1

theorem false_of_isE27_le {B : Subgroup G} (hB : IsE27 B) (hBK : B ≤ K) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := h.quotient_iso
  set π := QuotientGroup.mk' (CFSG.pCore 2 K) with hπ
  have hBR : B ⊓ CFSG.Open.pCoreOf 2 K = ⊥ := Source.inf_eq_bot_of_isPGroup (by norm_num)
    hB.isPGroup (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have hinj : Set.InjOn π (B.subgroupOf K) := by
    intro u hu v hv huv
    have h1 := (Item183K.mk_eq_mk_iff u.2 v.2).mp huv
    have h2 : (u : G) * (v : G)⁻¹ ∈ B :=
      B.mul_mem (Subgroup.mem_subgroupOf.mp hu) (B.inv_mem (Subgroup.mem_subgroupOf.mp hv))
    have h3 : (u : G) * (v : G)⁻¹ ∈ B ⊓ CFSG.Open.pCoreOf 2 K := ⟨h2, h1⟩
    rw [hBR, Subgroup.mem_bot, mul_inv_eq_one] at h3
    exact Subtype.ext h3
  have hB' := isE27_subgroupOf hB hBK
  have hcard : Nat.card ((B.subgroupOf K).map π) = 27 := by
    rw [Sec13.card_map_eq_of_injOn π hinj, hB'.2]
  exact Item183K.card_ne_of_SL34 e (Sec13.isElemAbelian_map hB'.1 π) hcard

end Hyp183

structure SylowS (A K S : Subgroup G) : Prop where
  le : A ≤ S
  le_sup : S ≤ A ⊔ K
  isPGroup : IsPGroup 3 S
  isSylowOf_inf : IsSylowOf 3 (S ⊓ K) K

namespace Item183K

theorem exists_sylowS (h : Hyp183 G A M c K) : ∃ S : Subgroup G, SylowS A K S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : IsPGroup 3 (A.subgroupOf (A ⊔ K)) := h.isE27.isPGroup.comap_subtype
  obtain ⟨Q, hQ⟩ := hA3.exists_le_sylow
  set S := (Q : Subgroup ↥(A ⊔ K)).map (A ⊔ K).subtype with hS
  have hSyl : IsSylowOf 3 S (A ⊔ K) := ⟨Q, rfl⟩
  refine ⟨S, ⟨fun a ha => ⟨⟨a, Subgroup.mem_sup_left ha⟩,
    hQ (Subgroup.mem_subgroupOf.mpr ha), rfl⟩, hSyl.le, hSyl.isPGroup, ?_⟩⟩
  exact hSyl.inf_of_le_normalizer le_sup_right h.sup_le_normalizer

variable (h : Hyp183 G A M c K) (hS : SylowS A K S)
include h hS

theorem le_normalizer_S : S ≤ Subgroup.normalizer (K : Set G) :=
  hS.le_sup.trans h.sup_le_normalizer

omit h in
theorem inf_pCoreOf_eq_bot : S ⊓ CFSG.Open.pCoreOf 2 K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact Source.inf_eq_bot_of_isPGroup (by norm_num) hS.isPGroup
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)

omit h in
theorem eq_one_of_mem {x : G} (hxS : x ∈ S) (hxR : x ∈ CFSG.Open.pCoreOf 2 K) : x = 1 := by
  have hx : x ∈ S ⊓ CFSG.Open.pCoreOf 2 K := ⟨hxS, hxR⟩
  rwa [inf_pCoreOf_eq_bot hS, Subgroup.mem_bot] at hx

theorem commute_of_mem_C {s x : G} (hsS : s ∈ S) (hsC : s ∈ Sec4.thetaQuotCentralizer K)
    (hx : x ∈ S ⊓ K) : s * x = x * s := by
  have h1 := (h.mem_C_iff (le_normalizer_S h hS hsS)).mp hsC x hx.2
  have h2 : s * x * s⁻¹ * x⁻¹ ∈ S :=
    S.mul_mem (S.mul_mem (S.mul_mem hsS hx.1) (S.inv_mem hsS)) (S.inv_mem hx.1)
  have h3 := eq_one_of_mem hS h2 h1
  calc s * x = s * x * s⁻¹ * x⁻¹ * (x * s) := by group
    _ = x * s := by rw [h3, one_mul]

omit [Finite G] h in
theorem exists_sylow_K : ∃ Q : Sylow 3 K, (Q : Subgroup K) = (S ⊓ K).subgroupOf K :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  hS.isSylowOf_inf.exists_sylow_eq_subgroupOf

omit h in
theorem injOn_mk : Set.InjOn (QuotientGroup.mk' (CFSG.pCore 2 K)) ((S ⊓ K).subgroupOf K) := by
  intro u hu v hv huv
  have h1 := (Item183K.mk_eq_mk_iff u.2 v.2).mp huv
  have h2 : (u : G) * (v : G)⁻¹ ∈ S :=
    S.mul_mem (Subgroup.mem_subgroupOf.mp hu).1 (S.inv_mem (Subgroup.mem_subgroupOf.mp hv).1)
  have h3 := eq_one_of_mem hS h2 h1
  rw [mul_inv_eq_one] at h3
  exact Subtype.ext h3

theorem pow_three_of_mem_inf {x : G} (hx : x ∈ S ⊓ K) : x ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := h.quotient_iso
  set π := QuotientGroup.mk' (CFSG.pCore 2 K) with hπ
  have hP : IsPGroup 3 (((S ⊓ K).subgroupOf K).map π) :=
    ((hS.isPGroup.to_le inf_le_left).comap_subtype).map π
  have h1 := Item183K.pow_three_eq_one_of_SL34 e hP
    (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hx : (⟨x, hx.2⟩ : K) ∈ _))
  rw [← map_pow] at h1
  have h2 : π (⟨x, hx.2⟩ ^ 3) = π ⟨1, K.one_mem⟩ := by rw [h1]; rfl
  have h3 := (Item183K.mk_eq_mk_iff (K.pow_mem hx.2 3) K.one_mem).mp h2
  rw [inv_one, mul_one] at h3
  exact eq_one_of_mem hS (S.pow_mem hx.1 3) h3

theorem card_inf : Nat.card (S ⊓ K : Subgroup G) = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := h.quotient_iso
  obtain ⟨Q, hQ⟩ := exists_sylow_K hS
  set π := QuotientGroup.mk' (CFSG.pCore 2 K) with hπ
  set P := Q.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 K)) with hP
  have h1 := Item183K.card_sylow_of_SL34 e P
  rw [hP, Sylow.coe_mapSurjective, hQ, Sec13.card_map_eq_of_injOn π (injOn_mk hS)] at h1
  rw [← h1]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm

theorem card_inf_C_le :
    Nat.card (S ⊓ K ⊓ Sec4.thetaQuotCentralizer K : Subgroup G) ≤ 3 := by
  obtain ⟨e⟩ := h.quotient_iso
  set π := QuotientGroup.mk' (CFSG.pCore 2 K) with hπ
  set T := S ⊓ K ⊓ Sec4.thetaQuotCentralizer K with hT
  have hTK : T ≤ K := inf_le_left.trans inf_le_right
  have hinj : Set.InjOn π (T.subgroupOf K) := (injOn_mk hS).mono fun u hu =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hu).1
  have hle : (T.subgroupOf K).map π ≤ Subgroup.center (K ⧸ CFSG.pCore 2 K) := by
    rintro _ ⟨t, ht, rfl⟩
    have ht' : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) q
    have h1 := (h.mem_C_iff (Subgroup.le_normalizer t.2)).mp ht'.2 y y.2
    have h2 : π (t * y * t⁻¹ * y⁻¹) = π 1 :=
      (Item183K.mk_eq_mk_iff (K.mul_mem (K.mul_mem (K.mul_mem t.2 y.2) (K.inv_mem t.2))
        (K.inv_mem y.2)) K.one_mem).mpr (by rw [inv_one, mul_one]; exact h1)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_one] at h2
    calc π y * π t = (π t * π y * (π t)⁻¹ * (π y)⁻¹)⁻¹ * (π t * π y) := by group
      _ = π t * π y := by rw [h2, inv_one, one_mul]
  have h1 := Subgroup.card_le_of_le hle
  rw [Sec13.card_map_eq_of_injOn π hinj, Item183K.card_center_of_SL34 e] at h1
  rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv]

theorem exists_mem_inf_C :
    ∃ z ∈ S ⊓ K, z ∈ Sec4.thetaQuotCentralizer K ∧ z ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := h.quotient_iso
  obtain ⟨Q, hQ⟩ := exists_sylow_K hS
  set π := QuotientGroup.mk' (CFSG.pCore 2 K) with hπ
  set P := Q.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 K)) with hP
  have hZ3 := Item183K.card_center_of_SL34 e
  have hZp : IsPGroup 3 (Subgroup.center (K ⧸ CFSG.pCore 2 K)) :=
    IsPGroup.of_card (n := 1) (by rw [hZ3, pow_one])
  have hZP : Subgroup.center (K ⧸ CFSG.pCore 2 K) ≤ P := hZp.le_sylow_of_normal P
  have hne : Subgroup.center (K ⧸ CFSG.pCore 2 K) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hZ3
    norm_num at hZ3
  obtain ⟨⟨zb, hzb⟩, hzb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hzbP : zb ∈ (P : Subgroup (K ⧸ CFSG.pCore 2 K)) := hZP hzb
  rw [hP, Sylow.coe_mapSurjective] at hzbP
  obtain ⟨q, hq, rfl⟩ := hzbP
  rw [hQ] at hq
  have hqS : (q : G) ∈ S ⊓ K := Subgroup.mem_subgroupOf.mp hq
  refine ⟨q, hqS, (h.mem_C_iff (Subgroup.le_normalizer q.2)).mpr fun y hy => ?_, ?_⟩
  · have hc : π q * π ⟨y, hy⟩ = π ⟨y, hy⟩ * π q := (Subgroup.mem_center_iff.mp hzb _).symm
    have h1 : π (q * ⟨y, hy⟩ * q⁻¹ * (⟨y, hy⟩ : K)⁻¹) = π 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_one, hc]
      group
    have h2 := (Item183K.mk_eq_mk_iff (K.mul_mem (K.mul_mem (K.mul_mem q.2 hy) (K.inv_mem q.2))
      (K.inv_mem hy)) K.one_mem).mp h1
    rwa [inv_one, mul_one] at h2
  · intro hq1
    apply hzb1
    apply Subtype.ext
    have : q = 1 := Subtype.ext hq1
    show (QuotientGroup.mk' (CFSG.pCore 2 K)) q = (1 : K ⧸ CFSG.pCore 2 K)
    rw [this, map_one]

omit hS in
theorem actsLike_pow {a k : G} (ha : a ∈ A) (hk : k ∈ K)
    (hak : ∀ y ∈ K, a * y * a⁻¹ * (k * y * k⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 K) (n : ℕ) :
    ∀ y ∈ K, a ^ n * y * (a ^ n)⁻¹ * (k ^ n * y * (k ^ n)⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
  have haN : a ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K (h.le_normalizer ha)
  have haK : a ∈ Subgroup.normalizer (K : Set G) := h.le_normalizer ha
  induction n with
  | zero =>
    intro y _
    simp
  | succ n ih =>
    intro y hy
    have hw : a ^ n * y * (a ^ n)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (pow_mem haK n) y).mp hy
    have hw' : k ^ n * y * (k ^ n)⁻¹ ∈ K := K.mul_mem (K.mul_mem (K.pow_mem hk n) hy)
      (K.inv_mem (K.pow_mem hk n))
    have h1 := (Subgroup.mem_normalizer_iff.mp haN _).mp (ih y hy)
    have h2 := hak _ hw'
    have e : a ^ (n + 1) * y * (a ^ (n + 1))⁻¹ * (k ^ (n + 1) * y * (k ^ (n + 1))⁻¹)⁻¹ =
        (a * (a ^ n * y * (a ^ n)⁻¹ * (k ^ n * y * (k ^ n)⁻¹)⁻¹) * a⁻¹) *
          (a * (k ^ n * y * (k ^ n)⁻¹) * a⁻¹ * (k * (k ^ n * y * (k ^ n)⁻¹) * k⁻¹)⁻¹) := by
      rw [pow_succ', pow_succ']
      group
    rw [e]
    exact Subgroup.mul_mem _ h1 h2

theorem exists_actsLike {a : G} (ha : a ∈ A) :
    ∃ x ∈ S ⊓ K, x⁻¹ * a ∈ Sec4.thetaQuotCentralizer K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := h.quotient_iso
  obtain ⟨-, k, hk, hak⟩ := h.inducesInnerMod a ha
  obtain ⟨Q, hQ⟩ := exists_sylow_K hS
  set π := QuotientGroup.mk' (CFSG.pCore 2 K) with hπ
  set P := Q.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 K)) with hP
  have hPeq : (P : Subgroup (K ⧸ CFSG.pCore 2 K)) = ((S ⊓ K).subgroupOf K).map π := by
    rw [hP, Sylow.coe_mapSurjective, hQ]
  have haK := h.le_normalizer ha
  have haS := hS.le ha
  set kb := π ⟨k, hk⟩ with hkb
  have hconj : ∀ y (hy : y ∈ K), π ⟨a * y * a⁻¹, (Subgroup.mem_normalizer_iff.mp haK y).mp hy⟩ =
      kb * π ⟨y, hy⟩ * kb⁻¹ := by
    intro y hy
    have h1 := (Item183K.mk_eq_mk_iff ((Subgroup.mem_normalizer_iff.mp haK y).mp hy)
      (K.mul_mem (K.mul_mem hk hy) (K.inv_mem hk))).mpr (hak y hy)
    rw [h1, hkb, ← map_mul, ← map_inv, ← map_mul]
    rfl
  have hkN : kb ∈ Subgroup.normalizer ((P : Subgroup (K ⧸ CFSG.pCore 2 K)) : Set _) := by
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    have hn' : n ∈ (P : Subgroup (K ⧸ CFSG.pCore 2 K)) := hn
    rw [hPeq] at hn' ⊢
    obtain ⟨y, hy, rfl⟩ := hn'
    have hy' : (y : G) ∈ S ⊓ K := Subgroup.mem_subgroupOf.mp hy
    rw [← hconj y y.2]
    refine Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩)
    · exact S.mul_mem (S.mul_mem haS hy'.1) (S.inv_mem haS)
    · exact (Subgroup.mem_normalizer_iff.mp haK y).mp y.2
  have hk3 : kb ^ 3 ∈ Subgroup.center (K ⧸ CFSG.pCore 2 K) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) q
    have h1 := actsLike_pow h ha hk hak 3 y hy
    rw [h.pow_three ha, inv_one, one_mul, mul_one] at h1
    have h2 := (Item183K.mk_eq_mk_iff hy (K.mul_mem (K.mul_mem (K.pow_mem hk 3) hy)
      (K.inv_mem (K.pow_mem hk 3)))).mpr h1
    have h3 : kb ^ 3 * π ⟨y, hy⟩ * (kb ^ 3)⁻¹ = π ⟨y, hy⟩ := by
      rw [hkb, ← map_pow, ← map_mul, ← map_inv, ← map_mul, h2]
      exact congrArg π (Subtype.ext (by simp))
    calc π ⟨y, hy⟩ * kb ^ 3 = kb ^ 3 * π ⟨y, hy⟩ * (kb ^ 3)⁻¹ * kb ^ 3 := by rw [h3]
      _ = kb ^ 3 * π ⟨y, hy⟩ := by group
  have hk9 : kb ^ 9 = 1 := by
    have h1 : (⟨kb ^ 3, hk3⟩ : Subgroup.center (K ⧸ CFSG.pCore 2 K)) ^
        Nat.card (Subgroup.center (K ⧸ CFSG.pCore 2 K)) = 1 := pow_card_eq_one'
    rw [Item183K.card_center_of_SL34 e] at h1
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2
    rw [← pow_mul] at h2
    exact h2
  have hkp : IsPGroup 3 (Subgroup.zpowers kb) := by
    intro g
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨2, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      show (3 : ℕ) ^ 2 = 9 by norm_num, hk9, one_zpow]
  have hsup := IsPGroup.to_sup_of_normal_right' hkp P.isPGroup' (Subgroup.zpowers_le.mpr hkN)
  have heq := P.is_maximal' hsup le_sup_right
  have hkP : kb ∈ (P : Subgroup (K ⧸ CFSG.pCore 2 K)) := by
    rw [← heq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers kb)
  rw [hPeq] at hkP
  obtain ⟨x, hx, hxk⟩ := hkP
  have hx' : (x : G) ∈ S ⊓ K := Subgroup.mem_subgroupOf.mp hx
  refine ⟨x, hx', (h.mem_C_iff (mul_mem (inv_mem (Subgroup.le_normalizer x.2)) haK)).mpr
    fun y hy => ?_⟩
  have hz : (x : G)⁻¹ * a * y * ((x : G)⁻¹ * a)⁻¹ ∈ K := by
    have h1 : a * y * a⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp haK y).mp hy
    have e : (x : G)⁻¹ * a * y * ((x : G)⁻¹ * a)⁻¹ = (x : G)⁻¹ * (a * y * a⁻¹) * x := by group
    rw [e]
    exact K.mul_mem (K.mul_mem (K.inv_mem x.2) h1) x.2
  have h1 : π ⟨(x : G)⁻¹ * a * y * ((x : G)⁻¹ * a)⁻¹, hz⟩ = π ⟨y, hy⟩ := by
    have e : (⟨(x : G)⁻¹ * a * y * ((x : G)⁻¹ * a)⁻¹, hz⟩ : K) =
        x⁻¹ * ⟨a * y * a⁻¹, (Subgroup.mem_normalizer_iff.mp haK y).mp hy⟩ * x := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e, map_mul, map_mul, hconj y hy, map_inv, hxk]
    group
  have h2 := (Item183K.mk_eq_mk_iff hz hy).mp h1
  exact h2

end Item183K

end CFSG.RankThree.PartTwo.Sec18
