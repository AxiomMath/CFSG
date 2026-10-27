module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs
import CFSG.RankThree.PartTwo.KFacts.K71SU3TwoFree
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.LowTwoRank (StatedSU)
open Matrix

namespace Res417Six

theorem exists_nonscalar_of_injective {N : Type*} [Group N] {K : Type} [Field K]
    (ι : N →* GL (Fin 3) K) (hι : Function.Injective ι) (F : Subgroup N) [Finite F]
    (hF3 : ∀ x ∈ F, x ^ 3 = 1) (hF : 3 < Nat.card F) :
    ∃ x ∈ F, ∀ c : K, ((ι x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ c • 1 := by
  classical
  by_contra hall
  push Not at hall
  choose c hc using hall
  have hc3 : ∀ x (hx : x ∈ F), c x hx ∈ Polynomial.nthRoots 3 (1 : K) := by
    intro x hx
    rw [Polynomial.mem_nthRoots (by norm_num)]
    have h1 : ((ι x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, hF3 x hx, map_one, Units.val_one]
    rw [hc x hx, smul_pow, one_pow] at h1
    have h2 := congrFun (congrFun h1 0) 0
    simpa using h2
  let φ : F → (Polynomial.nthRoots 3 (1 : K)).toFinset := fun x =>
    ⟨c x x.2, Multiset.mem_toFinset.mpr (hc3 x x.2)⟩
  have hφ : Function.Injective φ := by
    intro x y hxy
    have hxy' : c x x.2 = c y y.2 := congrArg Subtype.val hxy
    apply Subtype.ext
    apply hι
    apply Units.ext
    rw [hc x x.2, hc y y.2, hxy']
  have h1 := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_eq_finsetCard] at h1
  have h2 := (Multiset.toFinset_card_le (Polynomial.nthRoots 3 (1 : K))).trans
    (Polynomial.card_nthRoots 3 (1 : K))
  omega

theorem mem_of_coprime_index {H : Type*} [Group H] {P : Subgroup H} [P.Normal]
    (hP : Nat.Coprime 3 P.index) {x : H} (hx : x ^ 3 = 1) : x ∈ P := by
  have hidx := P.pow_index_mem x
  have hgcd := Nat.gcd_eq_gcd_ab 3 P.index
  rw [hP, Nat.cast_one] at hgcd
  have hx' : x = (x ^ 3) ^ Nat.gcdA 3 P.index * (x ^ P.index) ^ Nat.gcdB 3 P.index := by
    calc x = x ^ (1 : ℤ) := (_root_.zpow_one x).symm
      _ = x ^ (((3 : ℕ) : ℤ) * Nat.gcdA 3 P.index + (P.index : ℤ) * Nat.gcdB 3 P.index) := by
          rw [← hgcd]
      _ = (x ^ 3) ^ Nat.gcdA 3 P.index * (x ^ P.index) ^ Nat.gcdB 3 P.index := by
          rw [_root_.zpow_add, _root_.zpow_mul, _root_.zpow_mul, _root_.zpow_natCast,
            _root_.zpow_natCast]
  rw [hx', hx, _root_.one_zpow, one_mul]
  exact P.zpow_mem hidx _

theorem le_centralizer_of_unitary {Γ : Type*} [Group Γ] [Finite Γ] {F T : Subgroup Γ}
    (hF : CFSG.Assembly.IsElemAbelian 3 F) (hF9 : 9 ≤ Nat.card F) (hT : IsPGroup 2 T)
    (hFT : F ≤ Subgroup.normalizer (T : Set Γ))
    (h : ∀ e ∈ F, e ≠ 1 → ∃ N : Subgroup Γ,
      Subgroup.centralizer ({e} : Set Γ) ≤ Subgroup.normalizer (N : Set Γ) ∧ F ≤ N ∧
      ∃ (f : ℕ) (K : Type) (_ : Field K) (ι : N →* GL (Fin 3) K), Function.Injective ι ∧
        PiField false 2 f K ∧ ModThree false (2 ^ f) ∧ ∀ x, ι x ∈ StatedSU 3 (2 ^ f) K) :
    T ≤ Subgroup.centralizer (F : Set Γ) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime 3 (Nat.card T) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := T)).mp hT
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three hF (by norm_num; exact hF9) hFT
    hcop fun e heF he1 => ?_
  obtain ⟨N, hCN, hFN, f, K, _, ι, hι, hK, hq, hιSU⟩ := h e heF he1
  have hFC : F ≤ Subgroup.centralizer ({e} : Set Γ) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hFcomm r hr e heF)
  set S : Subgroup Γ := T ⊓ Subgroup.centralizer ({e} : Set Γ) with hS
  set Y : Subgroup Γ := Subgroup.closure
    {c | ∃ r ∈ F, ∃ w ∈ S, c = r * w * r⁻¹ * w⁻¹} with hY
  have hrw : ∀ r ∈ F, ∀ w ∈ S, r * w * r⁻¹ * w⁻¹ ∈ T ⊓ N := by
    intro r hr w hw
    refine ⟨T.mul_mem ((Subgroup.mem_normalizer_iff.mp (hFT hr) w).mp hw.1) (T.inv_mem hw.1), ?_⟩
    have h1 : w * r⁻¹ * w⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hCN hw.2) r⁻¹).mp (N.inv_mem (hFN hr))
    have : r * w * r⁻¹ * w⁻¹ = r * (w * r⁻¹ * w⁻¹) := by group
    rw [this]
    exact N.mul_mem (hFN hr) h1
  have hYTN : Y ≤ T ⊓ N := by
    rw [hY, Subgroup.closure_le]
    rintro _ ⟨r, hr, w, hw, rfl⟩
    exact hrw r hr w hw
  have : Finite (F.subgroupOf N) := inferInstance
  have hF3 : ∀ x ∈ F.subgroupOf N, x ^ 3 = 1 := fun x hx =>
    Subtype.ext (by rw [Subgroup.coe_pow, hF.2 _ (Subgroup.mem_subgroupOf.mp hx), N.coe_one])
  have hFcard : 3 < Nat.card (F.subgroupOf N) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFN).toEquiv]
    omega
  obtain ⟨x₀, hx₀F, hx₀s⟩ := exists_nonscalar_of_injective ι hι (F.subgroupOf N) hF3 hFcard
  have hx₀F' : (x₀ : Γ) ∈ F := Subgroup.mem_subgroupOf.mp hx₀F
  have hx₀Y : ∀ y ∈ Y, (x₀ : Γ) * y * (x₀ : Γ)⁻¹ ∈ Y := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem c hc =>
      obtain ⟨r, hr, w, hw, rfl⟩ := hc
      have hw' : (x₀ : Γ) * w * (x₀ : Γ)⁻¹ ∈ S :=
        ⟨(Subgroup.mem_normalizer_iff.mp (hFT hx₀F') w).mp hw.1,
          (Subgroup.mem_normalizer_iff.mp
            (Subgroup.le_normalizer (hFC hx₀F')) w).mp hw.2⟩
      have hr' : (x₀ : Γ) * r * (x₀ : Γ)⁻¹ = r := by
        rw [hFcomm _ hx₀F' r hr, mul_assoc, mul_inv_cancel, mul_one]
      have : (x₀ : Γ) * (r * w * r⁻¹ * w⁻¹) * (x₀ : Γ)⁻¹ =
          r * ((x₀ : Γ) * w * (x₀ : Γ)⁻¹) * r⁻¹ * ((x₀ : Γ) * w * (x₀ : Γ)⁻¹)⁻¹ := by
        conv_rhs => rw [← hr']
        group
      rw [this]
      exact Subgroup.subset_closure ⟨r, hr, _, hw', rfl⟩
    | one => simp [Y.one_mem]
    | mul a b _ _ ha hb =>
      have : (x₀ : Γ) * (a * b) * (x₀ : Γ)⁻¹ =
          ((x₀ : Γ) * a * (x₀ : Γ)⁻¹) * ((x₀ : Γ) * b * (x₀ : Γ)⁻¹) := by group
      rw [this]
      exact Y.mul_mem ha hb
    | inv a _ ha =>
      have : (x₀ : Γ) * a⁻¹ * (x₀ : Γ)⁻¹ = ((x₀ : Γ) * a * (x₀ : Γ)⁻¹)⁻¹ := by group
      rw [this]
      exact Y.inv_mem ha
  set X : Subgroup (GL (Fin 3) K) := (Y.subgroupOf N).map ι with hX
  have hXu : X ≤ glPi false 3 (2 ^ f) K := by
    rintro _ ⟨y, -, rfl⟩
    have hy := hιSU y
    simp only [glPi, Bool.cond_false]
    rw [CFSG.Assembly.LowTwoRank.StatedSU] at hy
    exact Subgroup.closure_mono (fun A hA => hA.2) hy
  have hX2 : IsPGroup 2 X := by
    have hY2 : IsPGroup 2 (Y.subgroupOf N) := by
      have hYT : IsPGroup 2 ((Y.subgroupOf N).map N.subtype) := by
        rw [Subgroup.map_subgroupOf_eq_of_le (hYTN.trans inf_le_right)]
        exact hT.to_le (hYTN.trans inf_le_left)
      exact hYT.of_equiv ((Y.subgroupOf N).equivMapOfInjective _ N.subtype_injective).symm
    exact hY2.map ι
  have hXv : ∀ z ∈ X, ι x₀ * z * (ι x₀)⁻¹ ∈ X := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨x₀ * y * x₀⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
    simpa using hx₀Y _ (Subgroup.mem_subgroupOf.mp hy)
  have hv3 : ι x₀ ^ 3 = 1 := by rw [← map_pow, hF3 _ hx₀F, map_one]
  have hX1 := eq_bot_of_normalizes hK hq (hιSU x₀) hv3 hx₀s hXu hX2 hXv
  have hY1 : ∀ y ∈ Y, y = 1 := by
    intro y hy
    have hyN : y ∈ N := (hYTN hy).2
    have h1 : ι ⟨y, hyN⟩ ∈ X := ⟨⟨y, hyN⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    rw [hX1, Subgroup.mem_bot, ← map_one ι] at h1
    exact congrArg Subtype.val (hι h1)
  rintro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have h1 := hY1 _ (Subgroup.subset_closure ⟨r, hr, w, hw, rfl⟩)
  have key : r * w = (r * w * r⁻¹ * w⁻¹) * (w * r) := by group
  rw [key, h1, one_mul]

end Res417Six

end CFSG.RankThree.PartTwo.Sec4
