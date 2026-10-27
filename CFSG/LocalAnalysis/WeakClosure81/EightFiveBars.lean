module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveBridge
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenW3
public import CFSG.LocalAnalysis.WeakClosure81.SevenKFactsBar

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

section Transport

variable {G : Type*} [Group G]

theorem pCoreOf_subgroupOf_map {N M : Subgroup G} (hNM : N ≤ M) :
    (pCoreOf 2 (N.subgroupOf M)).map M.subtype = pCoreOf 2 N := by
  set e := Subgroup.subgroupOfEquivOfLe hNM
  have hcomp : M.subtype.comp (N.subgroupOf M).subtype = N.subtype.comp e.toMonoidHom := by
    ext x
    rfl
  rw [CFSG.Open.pCoreOf, CFSG.Open.pCoreOf, Subgroup.map_map, hcomp, ← Subgroup.map_map,
    CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e]

theorem pCoreOf_subgroupOf {N M : Subgroup G} (hNM : N ≤ M) :
    pCoreOf 2 (N.subgroupOf M) = (pCoreOf 2 N).subgroupOf M := by
  rw [← pCoreOf_subgroupOf_map hNM]
  exact (Subgroup.comap_map_eq_self_of_injective M.subtype_injective _).symm

theorem hasQuotShape_of_subgroupOf {K H : Subgroup G} (hKH : K ≤ H) {N : Set G} {N' : Set ↥H}
    (hN : ∀ x : ↥H, x ∈ N' ↔ (x : G) ∈ N) {P : ∀ (X : Type) [Group X], Prop}
    (h : HasQuotShape (K.subgroupOf H) N' P) : HasQuotShape K N P := by
  obtain ⟨X, _, φ, hφs, hφk, hP⟩ := h
  refine ⟨X, inferInstance,
    φ.comp (Subgroup.subgroupOfEquivOfLe hKH).symm.toMonoidHom, ?_, ?_, hP⟩
  · exact hφs.comp (Subgroup.subgroupOfEquivOfLe hKH).symm.surjective
  · intro k
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hφk, hN]
    rfl

theorem mem_centerPre_subgroupOf_iff {K H N : Subgroup G} (hKH : K ≤ H) (x : ↥H) :
    x ∈ centerPre (K.subgroupOf H) ((N.subgroupOf H : Subgroup ↥H) : Set ↥H) ↔
      (x : G) ∈ centerPre K (N : Set G) := by
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨Subgroup.mem_subgroupOf.mp hx, fun z hz => ?_⟩
    exact Subgroup.mem_subgroupOf.mp (h ⟨z, hKH hz⟩ (Subgroup.mem_subgroupOf.mpr hz))
  · rintro ⟨hx, h⟩
    refine ⟨Subgroup.mem_subgroupOf.mpr hx, fun y hy => ?_⟩
    exact Subgroup.mem_subgroupOf.mpr (h (y : G) (Subgroup.mem_subgroupOf.mp hy))

theorem hasQuotShape_centerPre_pCoreOf_of_subgroupOf {K H : Subgroup G} (hKH : K ≤ H)
    {P : ∀ (X : Type) [Group X], Prop}
    (h : HasQuotShape (K.subgroupOf H)
      (centerPre (K.subgroupOf H) ((pCoreOf 2 (K.subgroupOf H) : Subgroup ↥H) : Set ↥H)) P) :
    HasQuotShape K (centerPre K ((pCoreOf 2 K : Subgroup G) : Set G)) P := by
  refine hasQuotShape_of_subgroupOf hKH (fun x => ?_) h
  rw [pCoreOf_subgroupOf hKH]
  exact mem_centerPre_subgroupOf_iff hKH x

end Transport

section Commutators

variable {G : Type} [Group G] [Finite G]

private def commSub (K J : Subgroup G) (hJ : K ≤ Subgroup.normalizer (J : Set G)) (r : G) :
    Subgroup G where
  carrier := {x | x ∈ K ∧ r * x * r⁻¹ * x⁻¹ ∈ J}
  mul_mem' := by
    rintro x y ⟨hx, hxJ⟩ ⟨hy, hyJ⟩
    refine ⟨K.mul_mem hx hy, ?_⟩
    have h1 : x * (r * y * r⁻¹ * y⁻¹) * x⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hJ hx) _).mp hyJ
    have e : r * (x * y) * r⁻¹ * (x * y)⁻¹ =
        (r * x * r⁻¹ * x⁻¹) * (x * (r * y * r⁻¹ * y⁻¹) * x⁻¹) := by group
    rw [e]
    exact J.mul_mem hxJ h1
  one_mem' := ⟨K.one_mem, by simp⟩
  inv_mem' := by
    rintro x ⟨hx, hxJ⟩
    refine ⟨K.inv_mem hx, ?_⟩
    have h0 : x * r * x⁻¹ * r⁻¹ ∈ J := by
      have := J.inv_mem hxJ
      rwa [show (r * x * r⁻¹ * x⁻¹)⁻¹ = x * r * x⁻¹ * r⁻¹ by group] at this
    have h1 : x⁻¹ * (x * r * x⁻¹ * r⁻¹) * x⁻¹⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hJ (K.inv_mem hx)) _).mp h0
    have e : r * x⁻¹ * r⁻¹ * x⁻¹⁻¹ = x⁻¹ * (x * r * x⁻¹ * r⁻¹) * x⁻¹⁻¹ := by group
    rw [e]
    exact h1

theorem forall_comm_mem_pCoreOf_of_forall_gen {V H : Subgroup G} {r : G}
    (hgen : ∀ k ∈ conjClosure V H, ∀ u ∈ conjSubgroup V k,
      r * u * r⁻¹ * u⁻¹ ∈ pCoreOf 2 (kGenIn V H)) :
    ∀ x ∈ kGenIn V H, r * x * r⁻¹ * x⁻¹ ∈ pCoreOf 2 (kGenIn V H) := by
  have hJ := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (kGenIn V H)
  have hle : kGenIn V H ≤ commSub (kGenIn V H) (pCoreOf 2 (kGenIn V H)) hJ r :=
    iSup₂_le fun k hk u hu => ⟨conjSubgroup_le_kGenIn hk hu, hgen k hk u hu⟩
  exact fun x hx => (hle hx).2

theorem mem_pCoreOf_of_comm_mem_of_pow_mem {K : Subgroup G} {c : G} (hcK : c ∈ K)
    (hcz : ∀ x ∈ K, c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 K) {n : ℕ} (hn : c ^ 2 ^ n ∈ pCoreOf 2 K) :
    c ∈ pCoreOf 2 K := by
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  have hφ : IsBarMap K (pCoreOf 2 K) (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) :=
    isBarMap_mk_pCore K
  set φ : ↥K →* ↥K ⧸ CFSG.pCore 2 ↥K := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hφdef
  set ĉ : ↥K := ⟨c, hcK⟩ with hĉ
  set z := φ ĉ with hz
  have hzc : z ∈ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨ŷ, rfl⟩ := hφ.surjective y
    have h1 : φ (ĉ * ŷ * ĉ⁻¹ * ŷ⁻¹) = 1 := by
      refine (hφ.ker_iff _).mpr ?_
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hcz (ŷ : G) ŷ.2
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)).symm
  have hzp : z ^ 2 ^ n = 1 := by
    rw [hz, ← map_pow]
    refine (hφ.ker_iff _).mpr ?_
    simpa only [Subgroup.coe_pow] using hn
  have hP2 : IsPGroup 2 (Subgroup.zpowers z) := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hzp)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hm])
  have hnorm : (Subgroup.zpowers z).Normal := by
    refine ⟨fun m hm g => ?_⟩
    have hm' := (Subgroup.zpowers_le.mpr hzc) hm
    rw [Subgroup.mem_center_iff] at hm'
    rw [show g * m * g⁻¹ = m by rw [hm' g, mul_inv_cancel_right]]
    exact hm
  have hle := CFSG.LieType.BorelTits.le_pCore 2 hnorm hP2
  have hz1 : z ∈ CFSG.pCore 2 (↥K ⧸ CFSG.pCore 2 ↥K) := hle (Subgroup.mem_zpowers z)
  rw [pCore_eq_bot_of_isBarMap hφ, Subgroup.mem_bot] at hz1
  exact (hφ.ker_iff ĉ).mp hz1

theorem isElemAbelian_conjClosure_of_comm {D H : Subgroup G} (hsq : ∀ z ∈ D, z * z = 1)
    (hcomm : ∀ x ∈ H, ∀ z ∈ D, ∀ y ∈ H, ∀ z' ∈ D,
      (x * z * x⁻¹) * (y * z' * y⁻¹) = (y * z' * y⁻¹) * (x * z * x⁻¹)) :
    IsElemAbelian 2 (conjClosure D H) := by
  have hS : ({w | ∃ x ∈ H, ∃ z ∈ D, x * z * x⁻¹ = w} : Set G).Pairwise Commute := by
    rintro _ ⟨x, hx, z, hz, rfl⟩ _ ⟨y, hy, z', hz', rfl⟩ -
    exact hcomm x hx z hz y hy z' hz'
  have hmc := Subgroup.isMulCommutative_closure hS
  refine ⟨hmc, fun w hw => ?_⟩
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨x, hx, z, hz, rfl⟩ := hw
    have : (x * z * x⁻¹) * (x * z * x⁻¹) = 1 := by
      calc (x * z * x⁻¹) * (x * z * x⁻¹) = x * (z * z) * x⁻¹ := by group
        _ = 1 := by rw [hsq z hz]; group
    simpa [pow_two] using this
  | one => simp
  | mul a b ha hb iha ihb =>
    have hc : a * b = b * a := congrArg Subtype.val (hmc.is_comm.comm (⟨a, ha⟩ : Subgroup.closure
      ({w | ∃ x ∈ H, ∃ z ∈ D, x * z * x⁻¹ = w} : Set G)) ⟨b, hb⟩)
    rw [(Commute.mul_pow (show Commute a b from hc)) 2, iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

end Commutators

variable {G : Type} [Group G] [Finite G] {V H T : Subgroup G}

namespace Hyp83

theorem pCoreOf_kGenIn_le_centralizer_eSub (h : Hyp83 V H T) :
    pCoreOf 2 (kGenIn V H) ≤ Subgroup.centralizer (eSub V H T : Set G) := fun x hx =>
  Subgroup.le_centralizer_iff.mp (eSub_centralizes_pCoreOf h.elemAbelian h.isCalH h.sylow)
    (pCoreOf_kGenIn_le h.le_H hx)

theorem conj_mem_centralizer_eSub (h : Hyp83 V H T) {g x : G} (hg : g ∈ H)
    (hx : x ∈ Subgroup.centralizer (eSub V H T : Set G)) :
    g * x * g⁻¹ ∈ Subgroup.centralizer (eSub V H T : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have hE := (Subgroup.normal_subgroupOf_iff h.eSub_le_H).mp h.eSub_subgroupOf_normal
  have he' : g⁻¹ * e * g ∈ eSub V H T := by
    simpa using hE e g⁻¹ he (H.inv_mem hg)
  have hc : (g⁻¹ * e * g) * x = x * (g⁻¹ * e * g) := Subgroup.mem_centralizer_iff.mp hx _ he'
  calc e * (g * x * g⁻¹) = g * ((g⁻¹ * e * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * e * g)) * g⁻¹ := by rw [hc]
    _ = g * x * g⁻¹ * e := by group

theorem mem_normalizer_conjSubgroup_of_mem_centralizer (h : Hyp83 V H T) {k : G} (hk : k ∈ H)
    {r : G} (hr : r ∈ Subgroup.centralizer (eSub V H T : Set G)) :
    r ∈ Subgroup.normalizer (conjSubgroup V k : Set G) := by
  obtain ⟨w₀, hw₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.inf_eSub_ne_bot
  have hwV : (w₀ : G) ∈ V := (Subgroup.mem_inf.mp w₀.2).1
  have hwE : (w₀ : G) ∈ eSub V H T := (Subgroup.mem_inf.mp w₀.2).2
  have hw1 : (w₀ : G) ≠ 1 := fun h' => hw₀ (Subtype.ext h')
  have hE := (Subgroup.normal_subgroupOf_iff h.eSub_le_H).mp h.eSub_subgroupOf_normal
  have hwU : k⁻¹ * (w₀ : G) * k ∈ conjSubgroup V k := by
    rw [mem_conjSubgroup_iff]
    simpa [mul_assoc] using hwV
  have hwE' : k⁻¹ * (w₀ : G) * k ∈ eSub V H T := by
    simpa using hE (w₀ : G) k⁻¹ hwE (H.inv_mem hk)
  have hw1' : k⁻¹ * (w₀ : G) * k ≠ 1 := by
    intro h'
    apply hw1
    simpa [mul_assoc] using congrArg (fun x => k * x * k⁻¹) h'
  have hrw : r ∈ Subgroup.centralizer ({k⁻¹ * (w₀ : G) * k} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hwE') hr
  exact centralizer_le_normalizer_conj h.isTI k hwU hw1' hrw

theorem commute_of_mem_centralizer_of_mem_conjSubgroup (h : Hyp83 V H T) {x y a b : G}
    (hx : x ∈ H) (hy : y ∈ H) (ha : a ∈ Subgroup.centralizer (eSub V H T : Set G))
    (hb : b ∈ Subgroup.centralizer (eSub V H T : Set G)) (haV : a ∈ conjSubgroup V x)
    (hbV : b ∈ conjSubgroup V y) : a * b = b * a := by
  have hNa := h.mem_normalizer_conjSubgroup_of_mem_centralizer hy ha
  have hNb := h.mem_normalizer_conjSubgroup_of_mem_centralizer hx hb
  have h1 : a * b * a⁻¹ ∈ conjSubgroup V y := (Subgroup.mem_normalizer_iff.mp hNa b).mp hbV
  have h2 : b * a * b⁻¹ ∈ conjSubgroup V x := (Subgroup.mem_normalizer_iff.mp hNb a).mp haV
  have hcy : a * b * a⁻¹ * b⁻¹ ∈ conjSubgroup V y :=
    (conjSubgroup V y).mul_mem h1 ((conjSubgroup V y).inv_mem hbV)
  have hcx : a * b * a⁻¹ * b⁻¹ ∈ conjSubgroup V x := by
    have := (conjSubgroup V x).inv_mem ((conjSubgroup V x).mul_mem h2
      ((conjSubgroup V x).inv_mem haV))
    rwa [show (b * a * b⁻¹ * a⁻¹)⁻¹ = a * b * a⁻¹ * b⁻¹ by group] at this
  rcases inf_conjSubgroup_eq_bot_or_eq h.isTI x y with hbot | heq
  · have hc1 : a * b * a⁻¹ * b⁻¹ = 1 := by
      have hmem : a * b * a⁻¹ * b⁻¹ ∈ conjSubgroup V x ⊓ conjSubgroup V y := ⟨hcx, hcy⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hc1)
  · have hbx : b ∈ conjSubgroup V x := heq ▸ hbV
    have hab := (isElemAbelian_conjSubgroup' h.elemAbelian x).1
    exact congrArg Subtype.val (hab.is_comm.comm (⟨a, haV⟩ : conjSubgroup V x) ⟨b, hbx⟩)

theorem inf_centralizer_eSub_le_pCoreOf (h : Hyp83 V H T) (hKT : H = kGenIn V H ⊔ T) :
    V ⊓ Subgroup.centralizer (eSub V H T : Set G) ≤ pCoreOf 2 (kGenIn V H) := by
  set D := V ⊓ Subgroup.centralizer (eSub V H T : Set G) with hD
  have hgen : ∀ x ∈ H, ∀ z ∈ D, x * z * x⁻¹ ∈ Subgroup.centralizer (eSub V H T : Set G) ∧
      x * z * x⁻¹ ∈ conjSubgroup V x⁻¹ := by
    intro x hx z hz
    refine ⟨h.conj_mem_centralizer_eSub hx (Subgroup.mem_inf.mp hz).2, ?_⟩
    rw [mem_conjSubgroup_iff]
    simpa [mul_assoc] using (Subgroup.mem_inf.mp hz).1
  have hN : IsElemAbelian 2 (conjClosure D H) := by
    refine isElemAbelian_conjClosure_of_comm (fun z hz => ?_) ?_
    · have := h.elemAbelian.2 z (Subgroup.mem_inf.mp hz).1
      simpa [pow_two] using this
    · intro x hx z hz y hy z' hz'
      exact h.commute_of_mem_centralizer_of_mem_conjSubgroup (H.inv_mem hx) (H.inv_mem hy)
        (hgen x hx z hz).1 (hgen y hy z' hz').1 (hgen x hx z hz).2 (hgen y hy z' hz').2
  have hnorm := h.le_normalizer_kGenIn_of_eq_sup hKT
  have hNK : conjClosure D H ≤ kGenIn V H := conjClosure_le fun x hx z hz =>
    (Subgroup.mem_normalizer_iff.mp (hnorm hx) z).mp (le_kGenIn_self V H (Subgroup.mem_inf.mp hz).1)
  have hKN : kGenIn V H ≤ Subgroup.normalizer (conjClosure D H : Set G) := fun k hk =>
    le_normalizer_conjClosure D H (kGenIn_le_H h.le_H hk)
  exact (le_conjClosure D H).trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNK hKN
    (CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hN))

theorem inf_centralizer_eSub_eq (h : Hyp83 V H T) (hKT : H = kGenIn V H ⊔ T) :
    V ⊓ Subgroup.centralizer (eSub V H T : Set G) = V ⊓ pCoreOf 2 (kGenIn V H) :=
  le_antisymm (le_inf inf_le_left (h.inf_centralizer_eSub_le_pCoreOf hKT))
    (inf_le_inf_left V h.pCoreOf_kGenIn_le_centralizer_eSub)

theorem comm_mem_pCoreOf_of_mem_inf_centralizer (h : Hyp83 V H T) (hKT : H = kGenIn V H ⊔ T)
    {r : G} (hrC : r ∈ Subgroup.centralizer (eSub V H T : Set G)) :
    ∀ x ∈ kGenIn V H, r * x * r⁻¹ * x⁻¹ ∈ pCoreOf 2 (kGenIn V H) := by
  refine forall_comm_mem_pCoreOf_of_forall_gen fun k hk u hu => ?_
  have hkK : k ∈ kGenIn V H := (h.conjClosure_eq_kGenIn hKT) ▸ hk
  have hkH : k ∈ H := conjClosure_le_of_le_H h.le_H hk
  have huK : u ∈ kGenIn V H := conjSubgroup_le_kGenIn hk hu
  have huH : u ∈ H := kGenIn_le_H h.le_H huK
  have hrN := h.mem_normalizer_conjSubgroup_of_mem_centralizer hkH hrC
  have h1 : r * u * r⁻¹ ∈ conjSubgroup V k := (Subgroup.mem_normalizer_iff.mp hrN u).mp hu
  have h2 : r * u * r⁻¹ * u⁻¹ ∈ conjSubgroup V k :=
    (conjSubgroup V k).mul_mem h1 ((conjSubgroup V k).inv_mem hu)
  have h3 : r * u * r⁻¹ * u⁻¹ ∈ Subgroup.centralizer (eSub V H T : Set G) := by
    have h4 := h.conj_mem_centralizer_eSub huH ((Subgroup.centralizer (eSub V H T : Set G)).inv_mem
      hrC)
    simpa [mul_assoc] using (Subgroup.centralizer (eSub V H T : Set G)).mul_mem hrC h4
  have h5 : k * (r * u * r⁻¹ * u⁻¹) * k⁻¹ ∈
      V ⊓ Subgroup.centralizer (eSub V H T : Set G) :=
    ⟨mem_conjSubgroup_iff.mp h2, h.conj_mem_centralizer_eSub hkH h3⟩
  have h6 := h.inf_centralizer_eSub_le_pCoreOf hKT h5
  have h7 := (Subgroup.mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (kGenIn V H)
      ((kGenIn V H).inv_mem hkK)) _).mp h6
  simpa [mul_assoc] using h7

theorem mem_pCoreOf_of_mem_inf_centralizer_of_pow (h : Hyp83 V H T) (hKT : H = kGenIn V H ⊔ T)
    {r : G} (hrK : r ∈ kGenIn V H) (hrC : r ∈ Subgroup.centralizer (eSub V H T : Set G))
    {n : ℕ} (hn : r ^ 2 ^ n ∈ pCoreOf 2 (kGenIn V H)) : r ∈ pCoreOf 2 (kGenIn V H) :=
  mem_pCoreOf_of_comm_mem_of_pow_mem hrK (h.comm_mem_pCoreOf_of_mem_inf_centralizer hKT hrC) hn

theorem comm_mem_pCoreOf_of_mem_centerPre (h : Hyp83 V H T) (hKT : H = kGenIn V H ⊔ T) {k : G}
    (hk : k ∈ centerPre (kGenIn V H) (eCentSet V H T)) :
    ∀ x ∈ kGenIn V H, k * x * k⁻¹ * x⁻¹ ∈ pCoreOf 2 (kGenIn V H) := by
  obtain ⟨hkK, hkc⟩ := hk
  refine forall_comm_mem_pCoreOf_of_forall_gen fun m hm u hu => ?_
  have huK : u ∈ kGenIn V H := conjSubgroup_le_kGenIn hm hu
  have hcK : k * u * k⁻¹ * u⁻¹ ∈ kGenIn V H :=
    (kGenIn V H).mul_mem ((kGenIn V H).mul_mem ((kGenIn V H).mul_mem hkK huK)
      ((kGenIn V H).inv_mem hkK)) ((kGenIn V H).inv_mem huK)
  have hcC : k * u * k⁻¹ * u⁻¹ ∈ Subgroup.centralizer (eSub V H T : Set G) := hkc u huK
  have hcz := h.comm_mem_pCoreOf_of_mem_inf_centralizer hKT hcC
  have hu2 : u * u = 1 := by
    have := (isElemAbelian_conjSubgroup' h.elemAbelian m).2 u hu
    simpa [pow_two] using this
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hcomm : u * (k * u * k⁻¹ * u⁻¹) * u⁻¹ * (k * u * k⁻¹ * u⁻¹)⁻¹ ∈
      pCoreOf 2 (kGenIn V H) := by
    have := (pCoreOf 2 (kGenIn V H)).inv_mem (hcz u huK)
    rwa [show (k * u * k⁻¹ * u⁻¹ * u * (k * u * k⁻¹ * u⁻¹)⁻¹ * u⁻¹)⁻¹ =
      u * (k * u * k⁻¹ * u⁻¹) * u⁻¹ * (k * u * k⁻¹ * u⁻¹)⁻¹ by group] at this
  have hsq : (k * u * k⁻¹ * u⁻¹) * (k * u * k⁻¹ * u⁻¹) ∈ pCoreOf 2 (kGenIn V H) := by
    have e : u * (k * u * k⁻¹ * u⁻¹) * u⁻¹ * (k * u * k⁻¹ * u⁻¹)⁻¹ =
        ((k * u * k⁻¹ * u⁻¹) * (k * u * k⁻¹ * u⁻¹))⁻¹ := by
      rw [hui]
      calc u * (k * u * k⁻¹ * u) * u * (k * u * k⁻¹ * u)⁻¹
          = u * k * u * k⁻¹ * (u * u) * (k * u * k⁻¹ * u)⁻¹ := by group
        _ = ((k * u * k⁻¹ * u) * (k * u * k⁻¹ * u))⁻¹ := by
          rw [hu2, mul_one]
          simp only [mul_inv_rev, hui, inv_inv]
          group
    rw [e] at hcomm
    simpa using (pCoreOf 2 (kGenIn V H)).inv_mem hcomm
  exact mem_pCoreOf_of_comm_mem_of_pow_mem hcK hcz (n := 1) (by simpa [pow_two] using hsq)

theorem centerPre_eCentSet_eq (h : Hyp83 V H T) (hKT : H = kGenIn V H ⊔ T) :
    centerPre (kGenIn V H) (eCentSet V H T) =
      centerPre (kGenIn V H) ((pCoreOf 2 (kGenIn V H) : Subgroup G) : Set G) := by
  ext k
  constructor
  · intro hk
    exact ⟨hk.1, h.comm_mem_pCoreOf_of_mem_centerPre hKT hk⟩
  · rintro ⟨hkK, hk⟩
    exact ⟨hkK, fun x hx => h.pCoreOf_kGenIn_le_centralizer_eSub (hk x hx)⟩

theorem kBarCenterShape_iff (h : Hyp83 V H T) (hKT : H = kGenIn V H ⊔ T)
    {P : ∀ (X : Type) [Group X], Prop} :
    KBarCenterShape V H T P ↔
      HasQuotShape (kGenIn V H) (centerPre (kGenIn V H)
        ((pCoreOf 2 (kGenIn V H) : Subgroup G) : Set G)) P := by
  unfold KBarCenterShape
  rw [centerPre_eCentSet_eq h hKT]

theorem card_barSub_eq_two_pow_rankBarV (h : Hyp83 V H T) (hKT : H = kGenIn V H ⊔ T) {X : Type}
    [Group X] {φ : ↥(kGenIn V H) →* X}
    (hφ : IsBarMap (kGenIn V H) (pCoreOf 2 (kGenIn V H)) φ) :
    Nat.card (barSub (kGenIn V H) φ V) = 2 ^ rankBarV V H T := by
  rw [card_barSub_eq_relIndex_of_isBarMap (le_kGenIn_self V H)
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _) hφ]
  unfold rankBarV
  rw [← E3.relIndex_eq_two_pow (CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian h.elemAbelian),
    h.inf_centralizer_eSub_eq hKT, inf_comm, Subgroup.inf_relIndex_right]

theorem kBarCenterShape_of_ambient (h : Hyp83 V H T) (hKT : H = kGenIn V H ⊔ T)
    {P : ∀ (X : Type) [Group X], Prop}
    (hP : HasQuotShape
      (kSub (V.subgroupOf H) (⊤ : Subgroup ↥H)
        (eSub (V.subgroupOf H) (⊤ : Subgroup ↥H) (T.subgroupOf H)))
      (centerPre
        (kSub (V.subgroupOf H) (⊤ : Subgroup ↥H)
          (eSub (V.subgroupOf H) (⊤ : Subgroup ↥H) (T.subgroupOf H)))
        ((pCoreOf 2 (kSub (V.subgroupOf H) (⊤ : Subgroup ↥H)
          (eSub (V.subgroupOf H) (⊤ : Subgroup ↥H) (T.subgroupOf H))) : Subgroup ↥H) :
          Set ↥H)) P) :
    KBarCenterShape V H T P := by
  rw [kBarCenterShape_iff h hKT]
  rw [AmbientH.kSub_eq_kGenIn h hKT] at hP
  exact hasQuotShape_centerPre_pCoreOf_of_subgroupOf (kGenIn_le_H h.le_H) hP

end Hyp83

end CFSG.LocalAnalysis.WeakClosure81
