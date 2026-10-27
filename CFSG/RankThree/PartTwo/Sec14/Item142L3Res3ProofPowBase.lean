module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofTypesBase
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic

public section

namespace CFSG.RankThree.PartTwo.Sec14.L3PGLPow

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS Item148PtRes2 Res5Types
open CFSG.RankThree.PartTwo.Sec14.L3PGL (sigmaOf)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure Pow142 (A : Subgroup G) (c : G) (L : Subgroup G) : Prop where
  std : Sec14Std G A c L
  eq_k : k142 A (lB A) c = L ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
    pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))
  le_k : ∀ V ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
    (piCompl 3), V ≤ k142 A (lB A) c

namespace Pow142

variable {A L : Subgroup G} {c : G} (d : Pow142 A c L)
include d

theorem l_le : L ≤ k142 A (lB A) c := by
  rw [d.eq_k]
  exact le_sup_left.trans le_sup_left

theorem o'_le : pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ≤
    k142 A (lB A) c := by
  rw [d.eq_k]
  exact le_sup_right.trans le_sup_left

theorem o''_le : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤ k142 A (lB A) c := by
  rw [d.eq_k]
  exact le_sup_right

theorem k_le_centralizer : k142 A (lB A) c ≤ Subgroup.centralizer ({c} : Set G) := by
  have hD := d.std.toSec13Data
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hD.commute hx hy
  have hRc := le_centralizer_of_mem_invariantPiSubgroups hD.mem_A hD.orderOf_eq
    (sup_mem_invariantPiSubgroups hD.mem_A hAab)
  rw [d.eq_k, sup_assoc]
  exact sup_le hD.le_centralizer hRc

theorem k_le_normalizer : k142 A (lB A) c ≤ Subgroup.normalizer (L : Set G) := by
  have hD := d.std.toSec13Data
  have h3L : 3 ∣ Nat.card L :=
    three_dvd_card_of_types148 (d.std.chosen136.2 c hD.zpowers_mem_omegaA L hD.mem_lA).1
  exact d.k_le_centralizer.trans (centralizer_le_normalizer_of_three_dvd d.std h3L)

theorem theta_le : inSubgroup (aschbacherSolvableCore 3) L ≤ pPrimeCoreOf 3 (k142 A (lB A) c) := by
  have : (aschbacherSolvableCore 3 ↥L).Characteristic :=
    Sec4.aschbacherSolvableCore_characteristic _
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  refine le_pPrimeCoreOf ((Subgroup.map_subtype_le _).trans d.l_le)
    (d.k_le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)) ?_
  rw [inSubgroup, Subgroup.card_map_of_injective L.subtype_injective]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3

theorem l_le_kA : L ≤ kA142 A (lB A) c := d.l_le.trans le_sup_left

theorem o'_le_pCore : pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ≤
    pPrimeCoreOf 3 (k142 A (lB A) c) :=
  le_pPrimeCoreOf d.o'_le ((delta_le _).trans (le_normalizer_pPrimeCoreOf 3 _))
    (coprime_card_pPrimeCoreOf 3 _)

theorem o''_le_normalizer : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
    Subgroup.normalizer ((L ⊔ pPrimeCoreOf 3 (k142 A (lB A) c) : Subgroup G) : Set G) :=
  le_normalizer_sup (d.o''_le.trans d.k_le_normalizer)
    (d.o''_le.trans (le_normalizer_pPrimeCoreOf 3 _))

theorem eq_sup_o'' : k142 A (lB A) c = L ⊔ pPrimeCoreOf 3 (k142 A (lB A) c) ⊔
    pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
  refine le_antisymm ?_ (sup_le (sup_le d.l_le (pPrimeCoreOf_le 3 _)) d.o''_le)
  conv_lhs => rw [d.eq_k]
  exact sup_le_sup_right (sup_le_sup_left d.o'_le_pCore L) _


theorem zpow_eq_one_of_mem {i : ℤ} (hci : c ^ i ∈ k142 A (lB A) c) : c ^ i = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := d.std.toSec13Data
  set K := k142 A (lB A) c with hKdef
  set OK := pPrimeCoreOf 3 K with hOK
  set R := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hR
  set M := L ⊔ OK with hM
  have hOK3 : ¬ 3 ∣ Nat.card OK :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 K)
  have hR3 : ¬ 3 ∣ Nat.card R :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  have hc3 : c ^ 3 = 1 := ((orderOf_eq_iff (by norm_num)).mp hD.orderOf_eq).1
  have hci3 : (c ^ i) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3, one_zpow]
  have hx : c ^ i ∈ (M : Set G) * (R : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left M R d.o''_le_normalizer, hM, hR,
      ← d.eq_sup_o'']
    exact hci
  obtain ⟨m, hm, r, hr, hmr⟩ := hx
  have hrc : Commute r (c ^ i) := by
    have hrA : r ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ hr
    exact Commute.zpow_right (Subgroup.mem_centralizer_iff.mp hrA c hD.mem_A).symm i
  set n := orderOf r with hn
  have hn3 : ¬ 3 ∣ n := fun h3 => hR3 (h3.trans (Subgroup.orderOf_dvd_natCard R hr))
  have hm' : m = c ^ i * r⁻¹ := by
    rw [← hmr]
    group
  have hmn : m ^ n = (c ^ i) ^ n := by
    rw [hm', (hrc.symm.inv_right).mul_pow, inv_pow, hn, pow_orderOf_eq_one, inv_one, mul_one]
  have hcM : c ^ i ∈ M := by
    have h1 : (c ^ i) ^ n ∈ M := hmn ▸ pow_mem hm n
    have hcop : Nat.Coprime n 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hn3).symm
    obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by norm_num : 1 < 3)
    have e : c ^ i = ((c ^ i) ^ n) ^ k := by
      rw [← pow_mul, ← Nat.div_add_mod (n * k) 3, hk, pow_add, pow_mul, hci3, one_pow, one_mul,
        pow_one]
    rw [e]
    exact pow_mem h1 k
  have hLOK : L ≤ Subgroup.normalizer (OK : Set G) :=
    d.l_le.trans (le_normalizer_pPrimeCoreOf 3 K)
  have hOKc : OK ≤ Subgroup.centralizer ({c} : Set G) :=
    (pPrimeCoreOf_le 3 K).trans d.k_le_centralizer
  have hx' : c ^ i ∈ (L : Set G) * (OK : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right L OK hLOK]
    exact hcM
  obtain ⟨l, hl, o, ho, hlo⟩ := hx'
  have hl' : (⟨l, hl⟩ : ↥L) ∈ (OK ⊔ Subgroup.zpowers c).subgroupOf L := by
    rw [Subgroup.mem_subgroupOf]
    change l ∈ OK ⊔ Subgroup.zpowers c
    rw [show l = c ^ i * o⁻¹ by rw [← hlo]; group]
    exact mul_mem (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers c i))
      (Subgroup.mem_sup_left (inv_mem ho))
  have hlθ := inf_le_theta Sec13.sporadicModels131 d.std hOK3 hLOK hOKc hl'
  have hlOK : l ∈ OK := d.theta_le ⟨⟨l, hl⟩, hlθ, rfl⟩
  have hcOK : c ^ i ∈ OK := hlo ▸ mul_mem hlOK ho
  by_contra hne
  have ho3 : orderOf (c ^ i) = 3 := orderOf_eq_prime hci3 hne
  exact hOK3 (ho3 ▸ Subgroup.orderOf_dvd_natCard OK hcOK)

theorem mem_pCore_of_mem {k : G} (hk : k ∈ k142 A (lB A) c)
    (hker : k ∈ pPrimeCoreOf 3 (k142 A (lB A) c) ⊔ Subgroup.zpowers c) :
    k ∈ pPrimeCoreOf 3 (k142 A (lB A) c) := by
  set K := k142 A (lB A) c with hKdef
  set OK := pPrimeCoreOf 3 K with hOK
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (OK : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun o ho => ?_
    have hoc : Commute o c :=
      Subgroup.mem_centralizer_singleton_iff.mp ((pPrimeCoreOf_le 3 K).trans
        d.k_le_centralizer ho)
    rw [hoc.symm.eq, mul_inv_cancel_right]
    exact ho
  have hx : k ∈ (OK : Set G) * (Subgroup.zpowers c : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left OK _ hcN]
    exact hker
  obtain ⟨o, ho, z, hz, rfl⟩ := hx
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hzK : c ^ i ∈ K := by
    rw [show c ^ i = o⁻¹ * (o * c ^ i) by group]
    exact mul_mem (inv_mem (pPrimeCoreOf_le 3 K ho)) hk
  rw [d.zpow_eq_one_of_mem hzK]
  simpa using ho

end Pow142

namespace Pow142

variable {A L : Subgroup G} {c : G} (d : Pow142 A c L)
include d

variable [(ker142 A (lB A) c).Normal]

theorem ker_toKα : (toKα d.l_le_kA).ker = aschbacherSolvableCore 3 ↥L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO3 : ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 (k142 A (lB A) c)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  ext l
  rw [MonoidHom.mem_ker, toKα, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, ker142, Subgroup.mem_subgroupOf]
  change (l : G) ∈ pPrimeCoreOf 3 (k142 A (lB A) c) ⊔ Subgroup.zpowers c ↔ _
  constructor
  · intro hl
    exact inf_le_theta Sec13.sporadicModels131 d.std hO3
      (d.l_le.trans (le_normalizer_pPrimeCoreOf 3 _))
      ((pPrimeCoreOf_le 3 _).trans d.k_le_centralizer) (Subgroup.mem_subgroupOf.mpr hl)
  · intro hl
    exact Subgroup.mem_sup_left (d.theta_le ⟨l, hl, rfl⟩)

@[expose] noncomputable def lbarEquiv :
    (↥L ⧸ aschbacherSolvableCore 3 ↥L) ≃* ↥(img142 A (lB A) c L) :=
  (QuotientGroup.quotientMulEquivOfEq d.ker_toKα).symm.trans
    ((QuotientGroup.quotientKerEquivRange (toKα d.l_le_kA)).trans
      (MulEquiv.subgroupCongr (range_toKα d.l_le_kA)))

theorem lbarEquiv_mk (l : ↥L) :
    ((d.lbarEquiv (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) l) :
        ↥(img142 A (lB A) c L)) : ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c) =
      QuotientGroup.mk' (ker142 A (lB A) c) (Subgroup.inclusion d.l_le_kA l) :=
  rfl

theorem lbarEquiv_act {a : G} (ha : a ∈ A) (haN : a ∈ Subgroup.normalizer (L : Set G))
    (z : ↥L ⧸ aschbacherSolvableCore 3 ↥L) :
    ((d.lbarEquiv (sigmaOf L haN z) : ↥(img142 A (lB A) c L)) :
        ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c) =
      alpha142 A (lB A) c a ha * (d.lbarEquiv z : ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c) *
        (alpha142 A (lB A) c a ha)⁻¹ := by
  induction z using QuotientGroup.induction_on with
  | H l =>
    have e1 : sigmaOf L haN (l : ↥L ⧸ aschbacherSolvableCore 3 ↥L) =
        QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) (L.normalizerMonoidHom ⟨a, haN⟩ l) :=
      Sec4.thetaQuotMulAut_mk _ l
    have e2 : (l : ↥L ⧸ aschbacherSolvableCore 3 ↥L) =
        QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) l := rfl
    rw [e1, d.lbarEquiv_mk, e2, d.lbarEquiv_mk, alpha142, ← map_inv, ← map_mul, ← map_mul]
    congr 1

theorem sigmaOf_eq_one_of_alpha {a : G} (ha : a ∈ A) (haN : a ∈ Subgroup.normalizer (L : Set G))
    (h1 : alpha142 A (lB A) c a ha = 1) : sigmaOf L haN = 1 := by
  ext z
  apply d.lbarEquiv.injective
  apply Subtype.ext
  rw [d.lbarEquiv_act ha haN, h1, one_mul, inv_one, mul_one, MulAut.one_apply]

end Pow142

end CFSG.RankThree.PartTwo.Sec14.L3PGLPow
