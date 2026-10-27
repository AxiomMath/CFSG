module

import CFSG.RankThree.PartTwo.Sec18.SylowFiveOmega
import CFSG.RankThree.PartTwo.Sec13.Item13Plane
import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolCenterNormal
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open scoped commutatorElement

namespace SylowFive

variable {G : Type} [Group G]

abbrev qOf (P B : Subgroup G) : Subgroup G := P ⊓ Subgroup.centralizer (B : Set G)

theorem mem_qOf_iff {P B : Subgroup G} {x : G} :
    x ∈ qOf P B ↔ x ∈ P ∧ ∀ b ∈ B, b * x = x * b := by
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]

theorem conj_mul_inv_mem {X N : Subgroup G} {x₁ p : G} (hX : CFSG.Assembly.IsElemAbelian 3 X)
    (hXeq : X = Subgroup.zpowers x₁ ⊔ N) (hpX : p ∈ Subgroup.normalizer (X : Set G))
    (hpN : p ∈ Subgroup.normalizer (N : Set G)) {k : ℕ} (hp : p ^ 3 ^ k = 1) {x : G}
    (hx : x ∈ X) : p * x * p⁻¹ * x⁻¹ ∈ N := by
  have hNX : N ≤ X := hXeq ▸ le_sup_right
  have hx₁ : x₁ ∈ X := hXeq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers x₁)
  have hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hX.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hconj : ∀ g ∈ Subgroup.normalizer (N : Set G), ∀ n ∈ N, g * n * g⁻¹ ∈ N :=
    fun g hg n hn => (Subgroup.mem_normalizer_iff.mp hg n).mp hn
  let T : Subgroup G :=
    { carrier := {g | g ∈ Subgroup.normalizer (N : Set G) ∧ g * x₁ * g⁻¹ * x₁⁻¹ ∈ N}
      mul_mem' := by
        rintro g h ⟨hg, hgx⟩ ⟨hh, hhx⟩
        refine ⟨Subgroup.mul_mem _ hg hh, ?_⟩
        have e : g * h * x₁ * (g * h)⁻¹ * x₁⁻¹ =
            g * (h * x₁ * h⁻¹ * x₁⁻¹) * g⁻¹ * (g * x₁ * g⁻¹ * x₁⁻¹) := by group
        rw [e]
        exact N.mul_mem (hconj g hg _ hhx) hgx
      one_mem' := ⟨Subgroup.one_mem _, by simp⟩
      inv_mem' := by
        rintro g ⟨hg, hgx⟩
        refine ⟨Subgroup.inv_mem _ hg, ?_⟩
        have e : g⁻¹ * x₁ * g⁻¹⁻¹ * x₁⁻¹ = g⁻¹ * (g * x₁ * g⁻¹ * x₁⁻¹)⁻¹ * g⁻¹⁻¹ := by group
        rw [e]
        exact hconj _ (Subgroup.inv_mem _ hg) _ (N.inv_mem hgx) }
  have hpT : p ∈ T := by
    have hpx : p * x₁ * p⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hpX x₁).mp hx₁
    obtain ⟨i, hi, n, hn, he⟩ := Sec13.exists_pow_mul_of_mem hX hx₁ hXeq hpx
    have hnX : n ∈ X := hNX hn
    interval_cases i
    ·
      rw [pow_zero, one_mul] at he
      have hx₁N : x₁ ∈ N := (Subgroup.mem_normalizer_iff.mp hpN x₁).mpr (he ▸ hn)
      exact ⟨hpN, by rw [he]; exact N.mul_mem hn (N.inv_mem hx₁N)⟩
    · refine ⟨hpN, ?_⟩
      rw [he, pow_one, hcomm x₁ hx₁ n hnX, mul_inv_cancel_right]
      exact hn
    ·
      have hp2 : p ^ 2 ∈ T := by
        refine ⟨Subgroup.pow_mem _ hpN 2, ?_⟩
        have hn' : p * n * p⁻¹ ∈ N := hconj p hpN n hn
        have hx₁3 : x₁ ^ 3 = 1 := hX.2 x₁ hx₁
        have hn2 : n * x₁ ^ 2 = x₁ ^ 2 * n := hcomm n hnX _ (Subgroup.pow_mem _ hx₁ 2)
        have e1 : p ^ 2 * x₁ * (p ^ 2)⁻¹ = p * (p * x₁ * p⁻¹) * p⁻¹ := by
          rw [pow_two, mul_inv_rev]; simp only [mul_assoc]
        have e2 : p * (x₁ ^ 2 * n) * p⁻¹ = (p * x₁ * p⁻¹) * (p * x₁ * p⁻¹) * (p * n * p⁻¹) := by
          simp only [pow_two, mul_assoc, inv_mul_cancel_left]
        set m := n * n * (p * n * p⁻¹) with hm
        have hmN : m ∈ N := N.mul_mem (N.mul_mem hn hn) hn'
        have e3 : (x₁ ^ 2 * n) * (x₁ ^ 2 * n) * (p * n * p⁻¹) * x₁⁻¹ =
            x₁ ^ 3 * (x₁ * m * x₁⁻¹) := by
          calc (x₁ ^ 2 * n) * (x₁ ^ 2 * n) * (p * n * p⁻¹) * x₁⁻¹ =
              x₁ ^ 2 * (n * x₁ ^ 2) * n * (p * n * p⁻¹) * x₁⁻¹ := by group
            _ = x₁ ^ 2 * (x₁ ^ 2 * n) * n * (p * n * p⁻¹) * x₁⁻¹ := by rw [hn2]
            _ = x₁ ^ 3 * (x₁ * m * x₁⁻¹) := by rw [hm]; group
        rw [e1, he, e2, he, e3, hx₁3, one_mul, hcomm x₁ hx₁ m (hNX hmN),
          mul_inv_cancel_right]
        exact hmN
      obtain ⟨m, hm⟩ : Odd (3 ^ k) := Odd.pow (by decide)
      have e : p = (p ^ 2) ^ (m + 1) := by
        rw [← pow_mul, show 2 * (m + 1) = 3 ^ k + 1 by omega, pow_succ, hp, one_mul]
      rw [e]
      exact T.pow_mem hp2 _
  let S : Subgroup G :=
    { carrier := {y | y ∈ X ∧ p * y * p⁻¹ * y⁻¹ ∈ N}
      mul_mem' := by
        rintro y z ⟨hy, hyN⟩ ⟨hz, hzN⟩
        refine ⟨X.mul_mem hy hz, ?_⟩
        have e : p * (y * z) * p⁻¹ * (y * z)⁻¹ =
            (p * y * p⁻¹ * y⁻¹) * (y * (p * z * p⁻¹ * z⁻¹) * y⁻¹) := by group
        rw [e, hcomm y hy _ (hNX hzN), mul_inv_cancel_right]
        exact N.mul_mem hyN hzN
      one_mem' := ⟨X.one_mem, by simp⟩
      inv_mem' := by
        rintro y ⟨hy, hyN⟩
        refine ⟨X.inv_mem hy, ?_⟩
        have e : p * y⁻¹ * p⁻¹ * y⁻¹⁻¹ = y⁻¹ * (p * y * p⁻¹ * y⁻¹)⁻¹ * y := by group
        rw [e, hcomm y⁻¹ (X.inv_mem hy) _ (hNX (N.inv_mem hyN)), inv_mul_cancel_right]
        exact N.inv_mem hyN }
  have hXS : X ≤ S := by
    conv_lhs => rw [hXeq]
    refine sup_le (Subgroup.zpowers_le.mpr ⟨hx₁, hpT.2⟩) fun n hn => ⟨hNX hn, ?_⟩
    exact N.mul_mem (hconj p hpN n hn) (N.inv_mem hn)
  exact (hXS hx).2

structure CaseTwo (P A B : Subgroup G) (c : G) : Prop where
  isPGroup : IsPGroup 3 P
  isElemAbelian : CFSG.Assembly.IsElemAbelian 3 A
  card_eq : Nat.card A = 27
  le : B ≤ A
  card_plane : Nat.card B = 9
  eq_sup : A = Subgroup.zpowers c ⊔ B
  not_mem : c ∉ B
  le_sylow : A ≤ P
  le_normalizer : P ≤ Subgroup.normalizer (A : Set G)
  le_normalizer_plane : P ≤ Subgroup.normalizer (B : Set G)
  mem_of_commute : ∀ x ∈ P, (∀ a ∈ A, x * a = a * x) → x ∈ A
  exists_conj_eq : ∀ b ∈ B, ∃ x ∈ qOf P B, x * c * x⁻¹ = b * c
  card_le : ∀ E : Subgroup G, E ≤ P → CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 27
  not_le_normalizer : ∀ B₀ : Subgroup G, B₀ ≤ B → Nat.card B₀ = 3 →
    ¬ Subgroup.normalizer ((qOf P B : Subgroup G) : Set G) ≤ Subgroup.normalizer (B₀ : Set G)

structure Flag (P B : Subgroup G) (b₀ b₁ : G) : Prop where
  mem_zero : b₀ ∈ B
  ne_one : b₀ ≠ 1
  commute : ∀ x ∈ P, x * b₀ = b₀ * x
  mem_one : b₁ ∈ B
  not_mem : b₁ ∉ Subgroup.zpowers b₀

namespace Flag

variable {P B : Subgroup G} {b₀ b₁ : G}

theorem zpowers_le (hF : Flag P B b₀ b₁) : Subgroup.zpowers b₀ ≤ B :=
  Subgroup.zpowers_le.mpr hF.mem_zero

theorem le_centralizer (hF : Flag P B b₀ b₁) :
    P ≤ Subgroup.centralizer (Subgroup.zpowers b₀ : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  exact (Commute.zpow_left (hF.commute x hx).symm k).eq

theorem commute_of_mem (hF : Flag P B b₀ b₁) {x z : G} (hx : x ∈ P)
    (hz : z ∈ Subgroup.zpowers b₀) : x * z = z * x :=
  ((Subgroup.mem_centralizer_iff.mp (hF.le_centralizer hx)) z hz).symm

end Flag

theorem commutator_pow_mul_of {t a d z : G} (hta : t * a * t⁻¹ = d * a) (hda : d * a = a * d)
    (htz : t * z = z * t) (i : ℕ) : ⁅t, a ^ i * z⁆ = d ^ i := by
  have e : t * (a ^ i * z) * t⁻¹ = (t * a * t⁻¹) ^ i * (t * z * t⁻¹) := by
    rw [conj_pow]; simp only [mul_assoc, inv_mul_cancel_left]
  rw [commutatorElement_def, e, hta, htz, mul_inv_cancel_right, Commute.mul_pow hda i, mul_inv_rev]
  simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

theorem eq_one_of_pow_three_of_pow_two {g : G} (h3 : g ^ 3 = 1) (h2 : g ^ 2 = 1) : g = 1 := by
  rw [pow_succ, h2, one_mul] at h3
  exact h3

namespace CaseTwo

variable {P A B : Subgroup G} {c : G} (hS : CaseTwo P A B c)
include hS

theorem mem : c ∈ A := hS.eq_sup ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers c)

theorem comm {a b : G} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a :=
  congrArg Subtype.val (hS.isElemAbelian.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem pow_three {a : G} (ha : a ∈ A) : a ^ 3 = 1 := hS.isElemAbelian.2 a ha

theorem pow_three_of_mem_plane {b : G} (hb : b ∈ B) : b ^ 3 = 1 := hS.pow_three (hS.le hb)

theorem le_qOf : A ≤ qOf P B :=
  le_inf hS.le_sylow fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb =>
    hS.comm (hS.le hb) ha

theorem plane_le : B ≤ P := hS.le.trans hS.le_sylow

theorem exists_pow_eq {x : G} (hx : x ∈ P) : ∃ k : ℕ, x ^ 3 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hS.isPGroup ⟨x, hx⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem conj_mem_plane {x b : G} (hx : x ∈ P) (hb : b ∈ B) : x * b * x⁻¹ ∈ B :=
  (Subgroup.mem_normalizer_iff.mp (hS.le_normalizer_plane hx) b).mp hb

theorem commute_of_mem_qOf {x b : G} (hx : x ∈ qOf P B) (hb : b ∈ B) : x * b = b * x :=
  ((mem_qOf_iff.mp hx).2 b hb).symm

theorem commutator_mem {x : G} (hx : x ∈ P) : ⁅x, c⁆ ∈ B := by
  obtain ⟨k, hk⟩ := hS.exists_pow_eq hx
  rw [commutatorElement_def]
  exact conj_mul_inv_mem hS.isElemAbelian hS.eq_sup (hS.le_normalizer hx)
    (hS.le_normalizer_plane hx) hk hS.mem

theorem commutator_mul {x y : G} (hx : x ∈ qOf P B) (hy : y ∈ P) :
    ⁅x * y, c⁆ = ⁅x, c⁆ * ⁅y, c⁆ := by
  have hyc := hS.commutator_mem hy
  have e : ⁅x * y, c⁆ = x * ⁅y, c⁆ * x⁻¹ * ⁅x, c⁆ := by
    simp only [commutatorElement_def]; group
  rw [e, hS.commute_of_mem_qOf hx hyc, mul_inv_cancel_right]
  exact hS.comm (hS.le hyc) (hS.le (hS.commutator_mem hx.1))

theorem mem_of_commute_plane {x : G} (hx : x ∈ P) (hxc : x * c = c * x)
    (hxB : ∀ b ∈ B, x * b = b * x) : x ∈ A := by
  refine hS.mem_of_commute x hx fun a ha => ?_
  have hle : A ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [hS.eq_sup]
    refine sup_le ?_ fun b hb => ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact hxc.symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hxB b hb).symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle ha)).symm

theorem commutator_eq_one_iff {x : G} (hx : x ∈ qOf P B) : ⁅x, c⁆ = 1 ↔ x ∈ A := by
  constructor
  · intro h
    refine hS.mem_of_commute_plane hx.1 ?_ fun b hb => hS.commute_of_mem_qOf hx hb
    rwa [commutatorElement_eq_one_iff_mul_comm] at h
  · intro h
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact hS.comm h hS.mem

@[expose] def deltaG : qOf P B →* G where
  toFun x := ⁅(x : G), c⁆
  map_one' := by simp
  map_mul' x y := by
    simp only [Subgroup.coe_mul]
    exact hS.commutator_mul x.2 y.2.1

theorem deltaG_apply (x : qOf P B) : hS.deltaG x = ⁅(x : G), c⁆ := rfl

def dImage (U : Subgroup G) : Subgroup G := (U.subgroupOf (qOf P B)).map hS.deltaG

theorem mem_dImage {U : Subgroup G} {y : G} :
    y ∈ hS.dImage U ↔ ∃ x ∈ U, x ∈ qOf P B ∧ ⁅x, c⁆ = y := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, x.2, rfl⟩
  · rintro ⟨x, hxU, hxQ, rfl⟩
    exact ⟨⟨x, hxQ⟩, Subgroup.mem_subgroupOf.mpr hxU, rfl⟩

theorem dImage_le_plane (U : Subgroup G) : hS.dImage U ≤ B := by
  intro y hy
  obtain ⟨x, -, hxQ, rfl⟩ := hS.mem_dImage.mp hy
  exact hS.commutator_mem hxQ.1

theorem dImage_mono {U V : Subgroup G} (h : U ≤ V) : hS.dImage U ≤ hS.dImage V := by
  intro y hy
  obtain ⟨x, hxU, hxQ, rfl⟩ := hS.mem_dImage.mp hy
  exact hS.mem_dImage.mpr ⟨x, h hxU, hxQ, rfl⟩

theorem card_eq_of_le_qOf [Finite G] {U : Subgroup G} (hUQ : U ≤ qOf P B) :
    Nat.card U = Nat.card (U ⊓ A : Subgroup G) * Nat.card (hS.dImage U) := by
  set f : U →* G := hS.deltaG.comp (Subgroup.inclusion hUQ) with hf
  have hker : f.ker.map U.subtype = U ⊓ A := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, (hS.commutator_eq_one_iff (hUQ x.2)).mp hx⟩
    · rintro ⟨hyU, hyA⟩
      exact ⟨⟨y, hyU⟩, (hS.commutator_eq_one_iff (hUQ hyU)).mpr hyA, rfl⟩
  have hrange : f.range = hS.dImage U := by
    ext y
    rw [hS.mem_dImage]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, hUQ x.2, rfl⟩
    · rintro ⟨x, hxU, -, rfl⟩
      exact ⟨⟨x, hxU⟩, rfl⟩
  rw [← Subgroup.card_ker_mul_card_range f, hrange, ← hker,
    Subgroup.card_map_of_injective U.subtype_injective]

theorem card_inf_qOf [Finite G] (U : Subgroup G) :
    Nat.card (U ⊓ qOf P B : Subgroup G) =
      Nat.card (U ⊓ A : Subgroup G) * Nat.card (hS.dImage U) := by
  have h := hS.card_eq_of_le_qOf (U := U ⊓ qOf P B) inf_le_right
  have h1 : (U ⊓ qOf P B) ⊓ A = U ⊓ A := by
    rw [inf_assoc, inf_eq_right.mpr hS.le_qOf]
  have h2 : hS.dImage (U ⊓ qOf P B) = hS.dImage U := by
    refine le_antisymm (hS.dImage_mono inf_le_left) fun y hy => ?_
    obtain ⟨x, hxU, hxQ, rfl⟩ := hS.mem_dImage.mp hy
    exact hS.mem_dImage.mpr ⟨x, ⟨hxU, hxQ⟩, hxQ, rfl⟩
  rwa [h1, h2] at h

theorem dImage_qOf : hS.dImage (qOf P B) = B := by
  refine le_antisymm (hS.dImage_le_plane _) fun b hb => ?_
  obtain ⟨x, hxQ, hx⟩ := hS.exists_conj_eq b hb
  refine hS.mem_dImage.mpr ⟨x, hxQ, hxQ, ?_⟩
  rw [commutatorElement_def, hx, mul_inv_cancel_right]

theorem exists_commutator_eq {b : G} (hb : b ∈ B) : ∃ x ∈ qOf P B, ⁅x, c⁆ = b := by
  obtain ⟨x, -, hxQ, hx⟩ := hS.mem_dImage.mp (hS.dImage_qOf.ge hb)
  exact ⟨x, hxQ, hx⟩

theorem card_qOf [Finite G] : Nat.card (qOf P B) = 243 := by
  have h := hS.card_eq_of_le_qOf (le_refl (qOf P B))
  rw [inf_eq_right.mpr hS.le_qOf, hS.dImage_qOf, hS.card_eq, hS.card_plane] at h
  exact h

theorem commutator_pow_mul {t b : G} (ht : t ∈ qOf P B) (hb : b ∈ B) (i : ℕ) :
    ⁅t, c ^ i * b⁆ = ⁅t, c⁆ ^ i := by
  refine commutator_pow_mul_of ?_ (hS.comm (hS.le (hS.commutator_mem ht.1)) hS.mem)
    (hS.commute_of_mem_qOf ht hb) i
  rw [commutatorElement_def, inv_mul_cancel_right]

theorem commutator_pow {t : G} (ht : t ∈ qOf P B) (n : ℕ) : ⁅t ^ n, c⁆ = ⁅t, c⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, hS.commutator_mul ((qOf P B).pow_mem ht n) ht.1, ih, pow_succ]

theorem commutator_conj {y q : G} (hy : y ∈ P) (hq : q ∈ qOf P B) :
    ⁅y * q * y⁻¹, c⁆ = y * ⁅q, c⁆ * y⁻¹ := by
  set β := ⁅y⁻¹, c⁆ with hβ
  set d := ⁅q, c⁆ with hd
  have hβB : β ∈ B := hS.commutator_mem (P.inv_mem hy)
  have hdB : d ∈ B := hS.commutator_mem hq.1
  have e1 : y⁻¹ * c * y = β * c := by
    rw [hβ, commutatorElement_def, inv_inv, inv_mul_cancel_right]
  have e2 : q * β = β * q := hS.commute_of_mem_qOf hq hβB
  have e3 : q * c * q⁻¹ = d * c := by rw [hd, commutatorElement_def, inv_mul_cancel_right]
  have e4 : β * d = d * β := hS.comm (hS.le hβB) (hS.le hdB)
  calc ⁅y * q * y⁻¹, c⁆ = y * q * (y⁻¹ * c * y) * q⁻¹ * y⁻¹ * c⁻¹ := by
        rw [commutatorElement_def]; group
    _ = y * (q * β) * c * q⁻¹ * y⁻¹ * c⁻¹ := by rw [e1]; group
    _ = y * β * (q * c * q⁻¹) * y⁻¹ * c⁻¹ := by rw [e2]; group
    _ = y * (β * d) * c * y⁻¹ * c⁻¹ := by rw [e3]; group
    _ = y * d * y⁻¹ * (y * (β * c) * y⁻¹) * c⁻¹ := by rw [e4]; group
    _ = y * d * y⁻¹ := by rw [← e1]; group

theorem conj_mem_qOf {y q : G} (hy : y ∈ P) (hq : q ∈ qOf P B) : y * q * y⁻¹ ∈ qOf P B := by
  refine mem_qOf_iff.mpr ⟨P.mul_mem (P.mul_mem hy hq.1) (P.inv_mem hy), fun b hb => ?_⟩
  have hb' : y⁻¹ * b * y ∈ B := by
    have h := hS.conj_mem_plane (P.inv_mem hy) hb
    rwa [inv_inv] at h
  have e := hS.commute_of_mem_qOf hq hb'
  calc b * (y * q * y⁻¹) = y * ((y⁻¹ * b * y) * q) * y⁻¹ := by group
    _ = y * (q * (y⁻¹ * b * y)) * y⁻¹ := by rw [e]
    _ = y * q * y⁻¹ * b := by group

theorem commutator_inv {q : G} (hq : q ∈ qOf P B) : ⁅q⁻¹, c⁆ = ⁅q, c⁆⁻¹ := by
  have h := hS.commutator_mul hq ((qOf P B).inv_mem hq).1
  rw [mul_inv_cancel, commutatorElement_one_left] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem commutator_commutator {y q : G} (hy : y ∈ P) (hq : q ∈ qOf P B) :
    ⁅⁅y, q⁆, c⁆ = ⁅y, ⁅q, c⁆⁆ := by
  have h1 := hS.conj_mem_qOf hy hq
  have hqi : q⁻¹ ∈ qOf P B := (qOf P B).inv_mem hq
  rw [commutatorElement_def y q, hS.commutator_mul h1 hqi.1, hS.commutator_conj hy hq,
    hS.commutator_inv hq, commutatorElement_def y]

theorem commutator_mem_qOf_of_mem_qOf {y q : G} (hy : y ∈ P) (hq : q ∈ qOf P B) :
    ⁅y, q⁆ ∈ qOf P B := by
  rw [commutatorElement_def]
  exact (qOf P B).mul_mem (hS.conj_mem_qOf hy hq) ((qOf P B).inv_mem hq)

theorem pow_three_mem_plane {t : G} (ht : t ∈ qOf P B) : t ^ 3 ∈ B := by
  have ht3Q : t ^ 3 ∈ qOf P B := (qOf P B).pow_mem ht 3
  have ht3A : t ^ 3 ∈ A := by
    refine (hS.commutator_eq_one_iff ht3Q).mp ?_
    rw [hS.commutator_pow ht, hS.pow_three_of_mem_plane (hS.commutator_mem ht.1)]
  by_cases hd : ⁅t, c⁆ = 1
  · rw [hS.pow_three ((hS.commutator_eq_one_iff ht).mp hd)]
    exact B.one_mem
  obtain ⟨i, hi, b, hb, he⟩ := Sec13.exists_pow_mul_of_mem hS.isElemAbelian hS.mem hS.eq_sup ht3A
  have h1 : ⁅t, c ^ i * b⁆ = 1 := by
    rw [← he, commutatorElement_eq_one_iff_mul_comm]
    exact (Commute.self_pow t 3).eq
  rw [hS.commutator_pow_mul ht hb] at h1
  interval_cases i
  · rw [he, pow_zero, one_mul]
    exact hb
  · exact absurd (by simpa using h1) hd
  · exact absurd (eq_one_of_pow_three_of_pow_two
      (hS.pow_three_of_mem_plane (hS.commutator_mem ht.1)) h1) hd

variable [Finite G]

theorem exists_flag : ∃ b₀ b₁ : G, Flag P B b₀ b₁ := by
  have : (B.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hS.plane_le).mpr hS.le_normalizer_plane
  have hne : B.subgroupOf P ≠ ⊥ := by
    intro h
    have hB : B = ⊥ := by
      rw [eq_bot_iff]
      intro b hb
      have hb' : (⟨b, hS.plane_le hb⟩ : P) ∈ B.subgroupOf P := hb
      rw [h, Subgroup.mem_bot] at hb'
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hb')
    have h9 := hS.card_plane
    rw [hB, Subgroup.card_bot] at h9
    norm_num at h9
  obtain ⟨z, hzB, hz1, hzZ⟩ :=
    Sec11.Item1119Sym.exists_ne_one_mem_center_of_normal P hS.isPGroup (B.subgroupOf P) hne
  have hb₀B : (z : G) ∈ B := hzB
  have hb₀1 : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hb₀3 : orderOf (z : G) = 3 := orderOf_eq_prime (hS.pow_three_of_mem_plane hb₀B) hb₀1
  obtain ⟨b₁, hb₁B, hb₁Z⟩ : ∃ b₁ ∈ B, b₁ ∉ Subgroup.zpowers (z : G) := by
    by_contra hall
    push Not at hall
    have h := Subgroup.card_le_of_le (H := B) (K := Subgroup.zpowers (z : G)) hall
    rw [Nat.card_zpowers, hb₀3, hS.card_plane] at h
    norm_num at h
  refine ⟨z, b₁, hb₀B, hb₀1, fun x hx => ?_, hb₁B, hb₁Z⟩
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzZ ⟨x, hx⟩)

variable {b₀ b₁ : G}

theorem orderOf_flag (hF : Flag P B b₀ b₁) : orderOf b₀ = 3 :=
  orderOf_eq_prime (hS.pow_three_of_mem_plane hF.mem_zero) hF.ne_one

theorem isElemAbelian_plane : CFSG.Assembly.IsElemAbelian 3 B :=
  CFSG.Open.IsElemAbelian.mono hS.isElemAbelian hS.le

theorem plane_eq_sup (hF : Flag P B b₀ b₁) :
    B = Subgroup.zpowers b₁ ⊔ Subgroup.zpowers b₀ := by
  have hle : Subgroup.zpowers b₁ ⊔ Subgroup.zpowers b₀ ≤ B :=
    sup_le (Subgroup.zpowers_le.mpr hF.mem_one) hF.zpowers_le
  have hb₁1 : b₁ ≠ 1 := fun h => hF.not_mem (h ▸ Subgroup.one_mem _)
  have hn : Subgroup.zpowers b₁ ≤ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) :=
    (Subgroup.zpowers_le.mpr (hS.plane_le hF.mem_one)).trans
      (hF.le_centralizer.trans (Subgroup.centralizer_le_normalizer _))
  have h1 := Sec6.card_sup_mul_card_inf hn
  rw [zpowers_inf_eq_bot (hS.pow_three_of_mem_plane hF.mem_one) hF.not_mem, Subgroup.card_bot,
    mul_one, Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime
      (hS.pow_three_of_mem_plane hF.mem_one) hb₁1, hS.orderOf_flag hF] at h1
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h1, hS.card_plane])).symm

theorem commutator_mem_zpowers (hF : Flag P B b₀ b₁) {x b : G} (hx : x ∈ P) (hb : b ∈ B) :
    ⁅x, b⁆ ∈ Subgroup.zpowers b₀ := by
  obtain ⟨k, hk⟩ := hS.exists_pow_eq hx
  rw [commutatorElement_def]
  exact conj_mul_inv_mem hS.isElemAbelian_plane (hS.plane_eq_sup hF) (hS.le_normalizer_plane hx)
    (Subgroup.centralizer_le_normalizer _ (hF.le_centralizer hx)) hk hb

@[expose] def chi (hF : Flag P B b₀ b₁) : P →* G where
  toFun x := ⁅(x : G), b₁⁆
  map_one' := by simp
  map_mul' x y := by
    simp only [Subgroup.coe_mul]
    have hy' := hS.commutator_mem_zpowers hF y.2 hF.mem_one
    have hx' := hS.commutator_mem_zpowers hF x.2 hF.mem_one
    have e : ⁅(x : G) * y, b₁⁆ = x * ⁅(y : G), b₁⁆ * (x : G)⁻¹ * ⁅(x : G), b₁⁆ := by
      simp only [commutatorElement_def]; group
    rw [e, hF.commute_of_mem x.2 hy', mul_inv_cancel_right]
    exact hS.comm (hS.le (hF.zpowers_le hy')) (hS.le (hF.zpowers_le hx'))

theorem chi_apply (hF : Flag P B b₀ b₁) (x : P) : hS.chi hF x = ⁅(x : G), b₁⁆ := rfl

theorem mem_qOf_iff_commutator (hF : Flag P B b₀ b₁) {x : G} (hx : x ∈ P) :
    x ∈ qOf P B ↔ ⁅x, b₁⁆ = 1 := by
  rw [commutatorElement_eq_one_iff_mul_comm]
  constructor
  · intro h
    exact hS.commute_of_mem_qOf h hF.mem_one
  · intro h
    refine mem_qOf_iff.mpr ⟨hx, fun b hb => ?_⟩
    have hle : B ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [hS.plane_eq_sup hF]
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact h.symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (hF.commute x hx).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hb)

theorem card_le_three_mul (hF : Flag P B b₀ b₁) {U : Subgroup G} (hU : U ≤ P) :
    Nat.card U ≤ 3 * Nat.card (U ⊓ qOf P B : Subgroup G) := by
  set f : U →* G := (hS.chi hF).comp (Subgroup.inclusion hU) with hf
  have hker : f.ker.map U.subtype = U ⊓ qOf P B := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, (hS.mem_qOf_iff_commutator hF (hU x.2)).mpr hx⟩
    · rintro ⟨hyU, hyQ⟩
      exact ⟨⟨y, hyU⟩, (hS.mem_qOf_iff_commutator hF (hU hyU)).mp hyQ, rfl⟩
  have hrange : f.range ≤ Subgroup.zpowers b₀ := by
    rintro _ ⟨x, rfl⟩
    exact hS.commutator_mem_zpowers hF (hU x.2) hF.mem_one
  have h3 : Nat.card f.range ≤ 3 := by
    calc Nat.card f.range ≤ Nat.card (Subgroup.zpowers b₀) := Subgroup.card_le_of_le hrange
      _ = 3 := by rw [Nat.card_zpowers, hS.orderOf_flag hF]
  rw [← Subgroup.card_ker_mul_card_range f, ← hker,
    Subgroup.card_map_of_injective U.subtype_injective, mul_comm]
  exact Nat.mul_le_mul_right _ h3

theorem commutator_mem_qOf (hF : Flag P B b₀ b₁) {x y : G} (hx : x ∈ P) (hy : y ∈ P) :
    ⁅x, y⁆ ∈ qOf P B := by
  have hxy : ⁅x, y⁆ ∈ P := by
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem hx hy) (P.inv_mem hx)) (P.inv_mem hy)
  refine (hS.mem_qOf_iff_commutator hF hxy).mpr ?_
  have h := map_commutatorElement (hS.chi hF) ⟨x, hx⟩ ⟨y, hy⟩
  have hc : ⁅hS.chi hF ⟨x, hx⟩, hS.chi hF ⟨y, hy⟩⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact hS.comm (hS.le (hF.zpowers_le (hS.commutator_mem_zpowers hF hx hF.mem_one)))
      (hS.le (hF.zpowers_le (hS.commutator_mem_zpowers hF hy hF.mem_one)))
  rw [hc] at h
  exact h

theorem pow_three_mem_qOf (hF : Flag P B b₀ b₁) {x : G} (hx : x ∈ P) : x ^ 3 ∈ qOf P B := by
  refine (hS.mem_qOf_iff_commutator hF (P.pow_mem hx 3)).mpr ?_
  have h := map_pow (hS.chi hF) ⟨x, hx⟩ 3
  simp only [hS.chi_apply, SubmonoidClass.coe_pow] at h
  rw [h, hS.pow_three_of_mem_plane (hF.zpowers_le (hS.commutator_mem_zpowers hF hx hF.mem_one))]

theorem pow_three_mem (hF : Flag P B b₀ b₁) {x : G} (hx : x ∈ P) : x ^ 3 ∈ A := by
  set z := ⁅x, c⁆ with hz
  have hzB : z ∈ B := hS.commutator_mem hx
  set β := ⁅x, z⁆ with hβ
  have hβZ : β ∈ Subgroup.zpowers b₀ := hS.commutator_mem_zpowers hF hx hzB
  have hβB : β ∈ B := hF.zpowers_le hβZ
  have hzc : x * c * x⁻¹ = z * c := by rw [hz, commutatorElement_def, inv_mul_cancel_right]
  have hβz : x * z * x⁻¹ = β * z := by rw [hβ, commutatorElement_def, inv_mul_cancel_right]
  have hxβ : x * β * x⁻¹ = β := by rw [hF.commute_of_mem hx hβZ, mul_inv_cancel_right]
  have hzβ : z * β = β * z := hS.comm (hS.le hzB) (hS.le hβB)
  have cm : ∀ a b : G, x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := fun a b => by group
  have e : x ^ 3 * c * (x ^ 3)⁻¹ = x * (x * (x * c * x⁻¹) * x⁻¹) * x⁻¹ := by
    rw [_root_.pow_three, mul_inv_rev, mul_inv_rev]; simp only [mul_assoc]
  have hc : x ^ 3 * c * (x ^ 3)⁻¹ = c := by
    calc x ^ 3 * c * (x ^ 3)⁻¹ = x * (x * (x * c * x⁻¹) * x⁻¹) * x⁻¹ := e
      _ = x * (x * (z * c) * x⁻¹) * x⁻¹ := by rw [hzc]
      _ = x * ((x * z * x⁻¹) * (x * c * x⁻¹)) * x⁻¹ := by rw [cm z c]
      _ = x * ((β * z) * (z * c)) * x⁻¹ := by rw [hβz, hzc]
      _ = ((x * β * x⁻¹) * (x * z * x⁻¹)) * ((x * z * x⁻¹) * (x * c * x⁻¹)) := by
        rw [cm (β * z) (z * c), cm β z, cm z c]
      _ = (β * (β * z)) * ((β * z) * (z * c)) := by rw [hxβ, hβz, hzc]
      _ = β * β * (z * β) * z * z * c := by simp only [mul_assoc]
      _ = β * β * (β * z) * z * z * c := by rw [hzβ]
      _ = β ^ 3 * z ^ 3 * c := by rw [_root_.pow_three, _root_.pow_three]; simp only [mul_assoc]
      _ = c := by rw [hS.pow_three_of_mem_plane hβB, hS.pow_three_of_mem_plane hzB, one_mul,
          one_mul]
  have hQ := hS.pow_three_mem_qOf hF hx
  refine hS.mem_of_commute_plane hQ.1 ?_ fun b hb => hS.commute_of_mem_qOf hQ hb
  calc x ^ 3 * c = x ^ 3 * c * (x ^ 3)⁻¹ * x ^ 3 := by group
    _ = c * x ^ 3 := by rw [hc]

end CaseTwo

end SylowFive

end CFSG.RankThree.PartTwo.Sec18
