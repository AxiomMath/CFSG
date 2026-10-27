module

public import CFSG.Assembly.Defs
public import CFSG.RankThree.PartTwo.ClassTwoEightActionInverting
public import CFSG.RankThree.PartTwo.Sec3.MinimalCommutatorTwoGroup
import CFSG.RankThree.Coprime.InvolutionFixedRankBound
import CFSG.RankThree.GroupTheory.SteinbergBMClassTwoExtraspecialAction
import CFSG.Assembly.OrderReductions.FrattiniElementary
import CFSG.LinearAlgebra.OddSolvableUnitary.CommutatorForm
import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.LocalAnalysis.SignalizerFunctor.Maximality

public section

namespace CFSG.RankThree.PartTwo.Sec3

open Subgroup
open scoped commutatorElement

theorem false_of_elemAbelian_action {p q : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hq : q.Prime)
    (hq3 : 3 < q) {D : Type*} [Group D] [Finite D] (hD : IsPGroup p D)
    (hexp : ∀ x : D, x ^ p = 1) (hclass : commutator D ≤ Subgroup.center D)
    {A : Type*} [CommGroup A] [Finite A] [Nontrivial A] (hA2 : ∀ a : A, a ^ 2 = 1)
    (ρ : A →* MulAut D) (hρ : Function.Injective ρ)
    (hfix : ∀ a : A, a ≠ 1 → CFSG.pRank p (fixedSubgroupOf (ρ a)) ≤ 2)
    (γ : MulAut A) (hγq : γ ^ q = 1) (hγfix : ∀ a, γ a = a → a = 1)
    (β : MulAut D) (hβ : ∀ a, β * ρ a * β⁻¹ = ρ (γ a)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact q.Prime := ⟨hq⟩
  have hA2g : IsPGroup 2 A := fun a => ⟨1, by rw [pow_one]; exact hA2 a⟩
  obtain ⟨n, hn⟩ := hA2g.exists_card_eq
  have hn3 : n ≤ 3 := by
    let _ : MulDistribMulAction A D := MulDistribMulAction.compHom D ρ
    have : FaithfulSMul A D := ⟨fun {a b} h => hρ (MulEquiv.ext h)⟩
    let _ : Module (ZMod 2) (Additive A) := AddCommGroup.zmodModule fun x => by
      change Additive.ofMul (Additive.toMul x ^ 2) = Additive.ofMul 1
      rw [hA2]
    have hlcs : (⊤ : Subgroup D).lowerCentralSeries 2 = ⊥ := by
      change ⁅⁅(⊤ : Subgroup D), ⊤⁆, ⊤⁆ = ⊥
      rw [commutator_eq_bot_iff_le_centralizer, coe_top, centralizer_univ]
      exact hclass
    have h := (CFSG.RankThree.Coprime.class_two_involution_fixed_rank_bound
      (hp.out.odd_of_ne_two hp2) hD (Monoid.exponent_dvd_of_forall_pow_eq_one hexp) hlcs n 2 hn
      (fun a ha => by
        have heq : CFSG.fixedPointSubgroup (zpowers a) D = fixedSubgroupOf (ρ a) := by
          ext x
          rw [mem_fixedSubgroupOf]
          constructor
          · intro h
            exact h ⟨a, mem_zpowers a⟩
          · intro h
            rintro ⟨b, hb⟩
            obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
            change (ρ (a ^ k)) x = x
            rw [map_zpow]
            exact zpow_apply_eq_self_of_apply_eq_self h k
        rw [heq]
        exact hfix a ha)).1
    omega
  have hmod : Nat.card A ≡ 1 [MOD q] := by
    let Γ := zpowers γ
    have hΓ : IsPGroup q Γ := fun g => ⟨1, by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp g.2
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hk, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, hγq, one_zpow, Subgroup.coe_one]⟩
    have h := hΓ.card_modEq_card_fixedPoints A
    have hfp : Nat.card (MulAction.fixedPoints Γ A) = 1 := by
      rw [Nat.card_eq_one_iff_exists]
      refine ⟨⟨1, fun g => map_one (g : MulAut A)⟩, fun ⟨a, ha⟩ => Subtype.ext ?_⟩
      exact hγfix a (ha ⟨γ, mem_zpowers γ⟩)
    rwa [hfp] at h
  have hq1 : q ∣ 2 ^ n - 1 := by
    rw [hn] at hmod
    exact (Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).mp hmod.symm
  interval_cases n
  · rw [pow_zero] at hn
    exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne' hn
  · norm_num at hq1
    exact hq.one_lt.ne' hq1
  · norm_num at hq1
    have := Nat.le_of_dvd (by norm_num) hq1
    omega
  · obtain ⟨-, ⟨a₀, ha₀, -⟩, hlast⟩ := class_two_eight_action_inverting_quotient hp2 hD hexp
      hclass hA2 (by rw [hn]; norm_num) ρ hρ hfix
    exact ha₀.1 (hγfix a₀ (hlast a₀ ha₀ β γ hβ).1)

theorem eq_five_of_extraspecial_action {p q : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hq : q.Prime) (hq3 : 3 < q) {D : Type*} [Group D] [Finite D] (hD : IsPGroup p D)
    (hexp : ∀ x : D, x ^ p = 1) (hclass : commutator D ≤ Subgroup.center D)
    {S : Type*} [Group S] [Finite S] {n : ℕ} (hS : IsExtraspecialPGroup 2 S)
    (hcard : Nat.card S = 2 ^ (1 + 2 * n)) (hn : 1 ≤ n) {z : S}
    (hz : Subgroup.center S = zpowers z) (ρ : S →* MulAut D) (hρ : Function.Injective ρ)
    (hfix : ∀ s : S, s ≠ 1 → CFSG.pRank p (fixedSubgroupOf (ρ s)) ≤ 2)
    (γ : MulAut S) (hγq : γ ^ q = 1)
    (hγfix : ∀ s, γ s * s⁻¹ ∈ Subgroup.center S → s ∈ Subgroup.center S) : q = 5 := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have hbound := CFSG.RankThree.GroupTheory.SteinbergBM.class_two_extraspecial_action_bound hp2
    hD hexp hclass hS hcard hz ρ hρ (fun s hs => (hfix s hs).trans (by norm_num))
  have hn2 : n ≤ 2 := by
    by_contra h
    have hn3 : n = 3 := by have := hbound.1; omega
    obtain ⟨s, hs, hs2⟩ :=
      CFSG.RankThree.GroupTheory.SteinbergBM.exists_noncentral_involution hS hcard (by omega) hz
    have h3 := hbound.2.1 hn3 s hs hs2
    have hs1 : s ≠ 1 := fun h1 => hs (h1 ▸ one_mem _)
    have := hfix s hs1
    omega
  let ψ := CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (Subgroup.center S)
  have hψ : ∀ s : S, ψ γ (s : S ⧸ Subgroup.center S) = ((γ s : S) : S ⧸ Subgroup.center S) :=
    fun s => CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism_apply _ γ s
  let Γ := zpowers (ψ γ)
  have hΓ : IsPGroup q Γ := fun g => ⟨1, by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp g.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hk, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, ← map_pow, hγq, map_one, one_zpow, Subgroup.coe_one]⟩
  have h := hΓ.card_modEq_card_fixedPoints (S ⧸ Subgroup.center S)
  have hfp : Nat.card (MulAction.fixedPoints Γ (S ⧸ Subgroup.center S)) = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨1, fun g => map_one (g : MulAut (S ⧸ Subgroup.center S))⟩, fun ⟨c, hc⟩ =>
      Subtype.ext ?_⟩
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective c
    have h1 := hc ⟨ψ γ, mem_zpowers _⟩
    change ψ γ (s : S ⧸ Subgroup.center S) = (s : S ⧸ Subgroup.center S) at h1
    rw [hψ, QuotientGroup.eq] at h1
    change (s : S ⧸ Subgroup.center S) = 1
    rw [QuotientGroup.eq_one_iff]
    apply hγfix
    have h2 : γ s * s⁻¹ = s * ((γ s)⁻¹ * s)⁻¹ * s⁻¹ := by group
    rw [h2]
    exact Subgroup.Normal.conj_mem inferInstance _ (inv_mem h1) s
  rw [hfp] at h
  have hZ2 : Nat.card (Subgroup.center S) = 2 := hS.2.2.2
  have hquot : Nat.card (S ⧸ Subgroup.center S) = 2 ^ (2 * n) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center S)
    rw [hcard, hZ2, pow_add, pow_one] at h1
    omega
  rw [hquot] at h
  have hq1 : q ∣ 2 ^ (2 * n) - 1 := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp h.symm
  interval_cases n
  · norm_num at hq1
    have := Nat.le_of_dvd (by norm_num) hq1
    omega
  · norm_num at hq1
    have h15 : q ∣ 3 * 5 := by norm_num; exact hq1
    rcases (Nat.Prime.dvd_mul hq).mp h15 with h3 | h5
    · have := Nat.le_of_dvd (by norm_num) h3
      omega
    · exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h5

section Conj

variable {G : Type*} [Group G]

@[expose] noncomputable def conjAction (D U : Subgroup G) (h : U ≤ normalizer (D : Set G)) :
    U →* MulAut D :=
  D.normalizerMonoidHom.comp (inclusion h)

theorem conjAction_apply_coe (D U : Subgroup G) (h : U ≤ normalizer (D : Set G)) (u : U)
    (d : D) : ((conjAction D U h u d : D) : G) = (u : G) * d * (u : G)⁻¹ :=
  normalizerMonoidHom_apply_apply_coe _ _ _

theorem mem_ker_conjAction {D U : Subgroup G} {h : U ≤ normalizer (D : Set G)} {u : U} :
    u ∈ (conjAction D U h).ker ↔ (u : G) ∈ centralizer (D : Set G) := by
  rw [MonoidHom.mem_ker, mem_centralizer_iff]
  constructor
  · intro hu d hd
    have := congrArg (fun σ : MulAut D => ((σ ⟨d, hd⟩ : D) : G)) hu
    simp only [conjAction_apply_coe, MulAut.one_apply] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  · intro hu
    apply MulEquiv.ext
    intro d
    apply Subtype.ext
    rw [conjAction_apply_coe, MulAut.one_apply, ← hu d d.2, mul_inv_cancel_right]

theorem mem_fixedSubgroupOf_conjAction {D U : Subgroup G} {h : U ≤ normalizer (D : Set G)}
    {u : U} {d : D} : d ∈ fixedSubgroupOf (conjAction D U h u) ↔ (u : G) * d = d * u := by
  rw [mem_fixedSubgroupOf, Subtype.ext_iff, conjAction_apply_coe, mul_inv_eq_iff_eq_mul]

theorem conjAction_conj {D U : Subgroup G} (h : U ≤ normalizer (D : Set G)) {x : G}
    (hxD : x ∈ normalizer (D : Set G)) (u : U) (hu : x * u * x⁻¹ ∈ U) :
    conjAction D U h ⟨x * u * x⁻¹, hu⟩ =
      D.normalizerMonoidHom ⟨x, hxD⟩ * conjAction D U h u *
        (D.normalizerMonoidHom ⟨x, hxD⟩)⁻¹ := by
  apply MulEquiv.ext
  intro d
  apply Subtype.ext
  rw [MulAut.mul_apply, MulAut.mul_apply, conjAction_apply_coe,
    normalizerMonoidHom_apply_apply_coe, conjAction_apply_coe, ← map_inv,
    normalizerMonoidHom_apply_apply_coe]
  simp only [InvMemClass.coe_inv]
  group

theorem pRank_fixedSubgroupOf_le [Finite G] {p : ℕ} (hp : 1 < p) {P D U : Subgroup G}
    (hDP : D ≤ P) {h : U ≤ normalizer (D : Set G)} (u : U) :
    CFSG.pRank p (fixedSubgroupOf (conjAction D U h u)) ≤
      CFSG.Assembly.pRank p (P ⊓ centralizer ({(u : G)} : Set G)) := by
  let f : fixedSubgroupOf (conjAction D U h u) →* G :=
    D.subtype.comp (fixedSubgroupOf (conjAction D U h u)).subtype
  have hf : Function.Injective f := fun a b hab => Subtype.ext (Subtype.ext hab)
  have hmap : (⊤ : Subgroup (fixedSubgroupOf (conjAction D U h u))).map f ≤
      P ⊓ centralizer ({(u : G)} : Set G) := by
    rintro _ ⟨y, -, rfl⟩
    have hy := mem_fixedSubgroupOf_conjAction.mp y.2
    exact mem_inf.mpr ⟨hDP (y : D).2, mem_centralizer_singleton_iff.mpr hy.symm⟩
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact (CFSG.SectionRank.pRank_le_map hp f hf ⊤).trans (CFSG.SectionRank.pRank_mono hp hmap)

end Conj

section Cases

variable {G : Type*} [Group G] [Finite G]

theorem mem_normalizer_centralizer {D : Subgroup G} {x : G} (hx : x ∈ normalizer (D : Set G)) :
    x ∈ normalizer (centralizer (D : Set G) : Set G) := by
  apply mem_normalizer_of_forall_conj_mem
  intro c hc
  rw [mem_centralizer_iff] at hc ⊢
  intro d hd
  have hd' : x⁻¹ * d * x ∈ D := by
    have := (mem_normalizer_iff.mp (inv_mem hx) d).mp hd
    rwa [inv_inv] at this
  have h := hc _ hd'
  calc d * (x * c * x⁻¹) = x * ((x⁻¹ * d * x) * c) * x⁻¹ := by group
    _ = x * (c * (x⁻¹ * d * x)) * x⁻¹ := by rw [h]
    _ = x * c * x⁻¹ * d := by group

@[expose] noncomputable def conjQuot {D U : Subgroup G} (h : U ≤ normalizer (D : Set G)) {x : G}
    (hxD : x ∈ normalizer (D : Set G)) (hxU : x ∈ normalizer (U : Set G)) :
    MulAut (U ⧸ (conjAction D U h).ker) :=
  QuotientGroup.congr _ _ (U.normalizerMonoidHom ⟨x, hxU⟩) (by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      apply mem_ker_conjAction.mpr
      have hv' : (v : G) ∈ centralizer (D : Set G) := mem_ker_conjAction.mp hv
      change ((U.normalizerMonoidHom ⟨x, hxU⟩ v : U) : G) ∈ _
      rw [normalizerMonoidHom_apply_apply_coe]
      exact (mem_normalizer_iff.mp (mem_normalizer_centralizer hxD) _).mp hv'
    · intro hu
      refine ⟨(U.normalizerMonoidHom ⟨x, hxU⟩)⁻¹ u, ?_, ?_⟩
      · apply mem_ker_conjAction.mpr
        have hu' : (u : G) ∈ centralizer (D : Set G) := mem_ker_conjAction.mp hu
        rw [← map_inv, normalizerMonoidHom_apply_apply_coe]
        have hx' : (⟨x, hxU⟩ : normalizer (U : Set G))⁻¹.1 ∈ normalizer
            (centralizer (D : Set G) : Set G) := mem_normalizer_centralizer (inv_mem hxD)
        exact (mem_normalizer_iff.mp hx' _).mp hu'
      · show (U.normalizerMonoidHom ⟨x, hxU⟩) ((U.normalizerMonoidHom ⟨x, hxU⟩)⁻¹ u) = u
        exact MulAut.apply_inv_self _ _ _)

omit [Finite G] in
theorem commutator_le_center_of_forall {D : Subgroup G}
    (hDcl : ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ⁅a, b⁆ * c = c * ⁅a, b⁆) :
    commutator D ≤ Subgroup.center D := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [Subgroup.mem_center_iff]
  intro c
  apply Subtype.ext
  have hcoe : ((⁅a, b⁆ : D) : G) = ⁅(a : G), (b : G)⁆ := by simp [commutatorElement_def]
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hcoe]
  exact (hDcl a a.2 b b.2 c c.2).symm

theorem conjQuot_pow_mk {D U : Subgroup G} (h : U ≤ normalizer (D : Set G)) {x : G}
    (hxD : x ∈ normalizer (D : Set G)) (hxU : x ∈ normalizer (U : Set G)) (k : ℕ) (u : U) :
    (conjQuot h hxD hxU ^ k) (u : U ⧸ (conjAction D U h).ker) =
      ((U.normalizerMonoidHom ⟨x, hxU⟩ ^ k) u : U) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, ih, pow_succ', MulAut.mul_apply]
    exact QuotientGroup.congr_mk _ _ _ _ _

theorem conjQuot_pow_eq_one {D U : Subgroup G} (h : U ≤ normalizer (D : Set G)) {x : G}
    (hxD : x ∈ normalizer (D : Set G)) (hxU : x ∈ normalizer (U : Set G)) {q : ℕ}
    (hxq : x ^ q = 1) : conjQuot h hxD hxU ^ q = 1 := by
  have hθ : U.normalizerMonoidHom ⟨x, hxU⟩ ^ q = 1 := by
    rw [← map_pow]
    have : (⟨x, hxU⟩ : normalizer (U : Set G)) ^ q = 1 := Subtype.ext (by simp [hxq])
    rw [this, map_one]
  apply MulEquiv.ext
  intro a
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective a
  rw [conjQuot_pow_mk, hθ, MulAut.one_apply, MulAut.one_apply]

theorem conjQuot_mk {D U : Subgroup G} (h : U ≤ normalizer (D : Set G)) {x : G}
    (hxD : x ∈ normalizer (D : Set G)) (hxU : x ∈ normalizer (U : Set G)) (u : U) :
    ∃ hu : x * u * x⁻¹ ∈ U, conjQuot h hxD hxU (u : U ⧸ (conjAction D U h).ker) =
      ((⟨x * u * x⁻¹, hu⟩ : U) : U ⧸ (conjAction D U h).ker) := by
  have hu : x * u * x⁻¹ ∈ U := (mem_normalizer_iff.mp hxU u).mp u.2
  refine ⟨hu, ?_⟩
  rw [conjQuot, QuotientGroup.congr_mk]
  congr 1

theorem conj_kerLift_eq {D U : Subgroup G} (h : U ≤ normalizer (D : Set G)) {x : G}
    (hxD : x ∈ normalizer (D : Set G)) (hxU : x ∈ normalizer (U : Set G))
    (a : U ⧸ (conjAction D U h).ker) :
    D.normalizerMonoidHom ⟨x, hxD⟩ * QuotientGroup.kerLift (conjAction D U h) a *
        (D.normalizerMonoidHom ⟨x, hxD⟩)⁻¹ =
      QuotientGroup.kerLift (conjAction D U h) (conjQuot h hxD hxU a) := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨hu, he⟩ := conjQuot_mk h hxD hxU u
  rw [he, QuotientGroup.kerLift_mk, QuotientGroup.kerLift_mk, conjAction_conj h hxD u hu]

omit [Finite G] in
theorem conj_mul_inv_mem_of {N : Subgroup G} {u y : G} (hu : u ∈ normalizer (N : Set G))
    (h : y⁻¹ * u ∈ N) : y * u⁻¹ ∈ N := by
  have h1 := (mem_normalizer_iff.mp hu _).mp (inv_mem h)
  have : u * (y⁻¹ * u)⁻¹ * u⁻¹ = y * u⁻¹ := by group
  rwa [this] at h1

theorem false_of_elemAbelian_section {p q : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hq : q.Prime) (hq3 : 3 < q) {P D U : Subgroup G} (hP : IsPGroup p P) (hDP : D ≤ P)
    (hDexp : ∀ d ∈ D, d ^ p = 1) (hDcl : ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ⁅a, b⁆ * c = c * ⁅a, b⁆)
    (hUD : U ≤ normalizer (D : Set G)) {x : G} (hxD : x ∈ normalizer (D : Set G))
    (hxU : x ∈ normalizer (U : Set G)) (hxq : x ^ q = 1)
    (hcomm : ∀ a ∈ U, ∀ b ∈ U, ⁅a, b⁆ ∈ centralizer (D : Set G))
    (hsq : ∀ a ∈ U, a ^ 2 ∈ centralizer (D : Set G))
    (hne : ∃ u ∈ U, u ∉ centralizer (D : Set G))
    (hfpf : ∀ u ∈ U, x * u * x⁻¹ * u⁻¹ ∈ centralizer (D : Set G) →
      u ∈ centralizer (D : Set G))
    (hfix : ∀ u ∈ U, u ∉ centralizer (D : Set G) →
      CFSG.Assembly.pRank p (P ⊓ centralizer ({u} : Set G)) ≤ 2) : False := by
  classical
  set φ := conjAction D U hUD with hφ
  have hcommQ : ∀ a b : U ⧸ φ.ker, a * b = b * a := by
    intro a b
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_ker_conjAction]
    have : (((u * v)⁻¹ * (v * u) : U) : G) = ⁅((v : U) : G)⁻¹, ((u : U) : G)⁻¹⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [this]
    exact hcomm _ (inv_mem v.2) _ (inv_mem u.2)
  let _ : CommGroup (U ⧸ φ.ker) := { (inferInstance : Group (U ⧸ φ.ker)) with mul_comm := hcommQ }
  have hsqQ : ∀ a : U ⧸ φ.ker, a ^ 2 = 1 := by
    intro a
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective a
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_ker_conjAction, Subgroup.coe_pow]
    exact hsq _ u.2
  obtain ⟨u₀, hu₀, hu₀C⟩ := hne
  have : Nontrivial (U ⧸ φ.ker) := ⟨⟨((⟨u₀, hu₀⟩ : U) : U ⧸ φ.ker), 1, fun h => hu₀C
    (mem_ker_conjAction.mp ((QuotientGroup.eq_one_iff _).mp h))⟩⟩
  let ρ : U ⧸ φ.ker →* MulAut D := QuotientGroup.kerLift φ
  have hρ : Function.Injective ρ := QuotientGroup.kerLift_injective φ
  have hfixQ : ∀ a : U ⧸ φ.ker, a ≠ 1 → CFSG.pRank p (fixedSubgroupOf (ρ a)) ≤ 2 := by
    intro a ha
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective a
    have hu : (u : G) ∉ centralizer (D : Set G) := fun h =>
      ha ((QuotientGroup.eq_one_iff u).mpr (mem_ker_conjAction.mpr h))
    change CFSG.pRank p (fixedSubgroupOf (QuotientGroup.kerLift φ (u : U ⧸ φ.ker))) ≤ 2
    rw [QuotientGroup.kerLift_mk]
    exact (pRank_fixedSubgroupOf_le hp.out.one_lt hDP u).trans (hfix u u.2 hu)
  let γ : MulAut (U ⧸ φ.ker) := conjQuot hUD hxD hxU
  have hγfix : ∀ a, γ a = a → a = 1 := by
    intro a ha
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨hu, he⟩ := conjQuot_mk hUD hxD hxU u
    change conjQuot hUD hxD hxU (u : U ⧸ φ.ker) = _ at ha
    rw [he, QuotientGroup.eq, mem_ker_conjAction] at ha
    have h1 : x * u * x⁻¹ * (u : G)⁻¹ ∈ centralizer (D : Set G) := by
      have := conj_mul_inv_mem_of (N := centralizer (D : Set G))
        (mem_normalizer_centralizer (hUD u.2)) (y := x * u * x⁻¹) (by simpa using ha)
      simpa [mul_assoc] using this
    exact (QuotientGroup.eq_one_iff u).mpr (mem_ker_conjAction.mpr (hfpf u u.2 h1))
  have hDp : IsPGroup p D := hP.to_le hDP
  have hDexp' : ∀ d : D, d ^ p = 1 := fun d =>
    Subtype.ext (by rw [Subgroup.coe_pow, hDexp d d.2, Subgroup.coe_one])
  exact false_of_elemAbelian_action hp2 hq hq3 hDp hDexp' (commutator_le_center_of_forall hDcl)
    hsqQ ρ hρ hfixQ γ (conjQuot_pow_eq_one hUD hxD hxU hxq) hγfix _
    (conj_kerLift_eq hUD hxD hxU)

theorem eq_five_of_extraspecial_section {p q : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hq : q.Prime) (hq3 : 3 < q) {P D U Z : Subgroup G} (hP : IsPGroup p P) (hDP : D ≤ P)
    (hDexp : ∀ d ∈ D, d ^ p = 1) (hDcl : ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ⁅a, b⁆ * c = c * ⁅a, b⁆)
    (hUD : U ≤ normalizer (D : Set G)) {x : G} (hxD : x ∈ normalizer (D : Set G))
    (hxU : x ∈ normalizer (U : Set G)) (hxq : x ^ q = 1) (hU2 : IsPGroup 2 U)
    (hZU : Z ≤ U) (hZc : ∀ z ∈ Z, ∀ v ∈ U, z * v = v * z) (hUUZ : ⁅U, U⁆ = Z)
    (hsqZ : ∀ u ∈ U, u ^ 2 ∈ Z) (hUZ : U ≠ Z) (hKZ : U ⊓ centralizer (D : Set G) ≤ Z)
    (hK2 : Nat.card Z = 2 * Nat.card ↥(U ⊓ centralizer (D : Set G)))
    (hcen : ∀ u ∈ U, (∀ v ∈ U, ⁅u, v⁆ ∈ centralizer (D : Set G)) → u ∈ Z)
    (hfpf : ∀ u ∈ U, x * u * x⁻¹ * u⁻¹ ∈ Z → u ∈ Z)
    (hfix : ∀ u ∈ U, u ∉ centralizer (D : Set G) →
      CFSG.Assembly.pRank p (P ⊓ centralizer ({u} : Set G)) ≤ 2) : q = 5 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := conjAction D U hUD with hφ
  set K := φ.ker with hK
  set S := U ⧸ K
  set π := QuotientGroup.mk' K with hπ
  set Z' := Z.subgroupOf U with hZ'
  have hmemK : ∀ u : U, u ∈ K ↔ (u : G) ∈ centralizer (D : Set G) := fun u => mem_ker_conjAction
  have hKZ' : K ≤ Z' := fun u hu => hKZ ⟨u.2, (hmemK u).mp hu⟩
  have hmemZ : ∀ w : U, π w ∈ Z'.map π → w ∈ Z' := by
    intro w ⟨z, hz, hzw⟩
    have h1 : z⁻¹ * w ∈ K := by
      rw [← QuotientGroup.eq]
      exact hzw
    have := Z'.mul_mem hz (hKZ' h1)
    rwa [mul_inv_cancel_left] at this
  have hS2 : IsPGroup 2 S := (hU2.to_quotient K)
  have hZS : Subgroup.center S = Z'.map π := by
    apply le_antisymm
    · intro s hs
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective K s
      refine ⟨u, ?_, rfl⟩
      show (u : G) ∈ Z
      apply hcen u u.2
      intro v hv
      have h1 := Subgroup.mem_center_iff.mp hs (π ⟨v, hv⟩)
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq, hmemK] at h1
      have : (((⟨v, hv⟩ * u : U)⁻¹ * (u * ⟨v, hv⟩) : U) : G) = ⁅(u : G)⁻¹, v⁻¹⁆ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
        group
      rw [this] at h1
      have h2 := (mem_normalizer_iff.mp
        (mem_normalizer_centralizer (hUD (mul_mem u.2 hv))) _).mp h1
      rwa [show (u : G) * v * ⁅(u : G)⁻¹, v⁻¹⁆ * ((u : G) * v)⁻¹ = ⁅(u : G), v⁆ by
        simp only [commutatorElement_def]; group] at h2
    · rintro _ ⟨z, hz, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective K s
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext ((hZc z hz v v.2).symm)
  have hcomU : commutator U = Z' := by
    apply map_injective U.subtype_injective
    rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype, hUUZ,
      subgroupOf_map_subtype, inf_of_le_left hZU]
  have hcomS : commutator S = Z'.map π := by
    rw [← hcomU, _root_.commutator_def, _root_.commutator_def, map_commutator,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective K)]
  have hfrS : frattini S = Z'.map π := by
    have : Fact (IsPGroup 2 S) := ⟨hS2⟩
    apply le_antisymm
    · rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2), closure_le]
      rintro s (hs | ⟨t, rfl⟩)
      · rw [← hcomS]
        exact hs
      · obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective K t
        refine ⟨u ^ 2, ?_, by rw [map_pow]⟩
        show ((u ^ 2 : U) : G) ∈ Z
        rw [Subgroup.coe_pow]
        exact hsqZ _ u.2
    · rw [← hcomS]
      exact CFSG.OrderReductions.FrattiniElementary.commutator_le_frattini 2 hS2
  have hcardZS : Nat.card (Subgroup.center S) = 2 := by
    rw [hZS, ← relIndex_ker, QuotientGroup.ker_mk']
    have h := relIndex_mul_card (H := K) (K := Z')
    rw [inf_of_le_left hKZ'] at h
    have hZ'c : Nat.card Z' = Nat.card Z := Nat.card_congr (subgroupOfEquivOfLe hZU).toEquiv
    have hKc : Nat.card K = Nat.card ↥(U ⊓ centralizer (D : Set G)) := by
      refine Nat.card_congr ?_
      exact
        { toFun := fun k => ⟨(k : U), (k : U).2, (hmemK k).mp k.2⟩
          invFun := fun g => ⟨⟨g, g.2.1⟩, (hmemK _).mpr g.2.2⟩
          left_inv := fun k => rfl
          right_inv := fun g => rfl }
    rw [hZ'c, hK2, hKc] at h
    have hpos : 0 < Nat.card ↥(U ⊓ centralizer (D : Set G)) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h
  have hZcom : Subgroup.center S = commutator S := hZS.trans hcomS.symm
  have hSx : IsExtraspecialPGroup 2 S :=
    ⟨hS2, hZcom.symm, hfrS.trans hZS.symm, hcardZS⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Nat.card S = 2 ^ (1 + 2 * n) := by
    obtain ⟨ε⟩ := CFSG.OddSolvableUnitary.nonempty_center_mulEquiv hcardZS
    let _ : Module (ZMod 2) (Additive (Abelianization S)) := AddCommGroup.zmodModule fun v => by
      obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
      change Additive.ofMul ((Abelianization.of t) ^ 2) = Additive.ofMul 1
      congr 1
      rw [← map_pow, ← MonoidHom.mem_ker, Abelianization.ker_of, hcomS]
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective K t
      refine ⟨u ^ 2, ?_, by rw [map_pow]⟩
      show ((u ^ 2 : U) : G) ∈ Z
      rw [Subgroup.coe_pow]
      exact hsqZ _ u.2
    obtain ⟨B, hBa, hBn, -⟩ := CFSG.OddSolvableUnitary.exists_commForm hZcom ε
    have : Finite (Additive (Abelianization S)) :=
      Finite.of_surjective (fun x : S => Additive.ofMul (Abelianization.of x))
        fun v => QuotientGroup.mk_surjective (Additive.toMul v)
    have : Module.Finite (ZMod 2) (Additive (Abelianization S)) := Module.Finite.of_finite
    obtain ⟨a, ha⟩ := LinearMap.BilinForm.IsAlt.even_finrank (K := ZMod 2) hBa hBn
    refine ⟨a, ?_⟩
    rw [CFSG.OddSolvableUnitary.card_eq_card_abelianization_mul hZcom hcardZS]
    change Nat.card (Additive (Abelianization S)) * 2 = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, ha, ← two_mul, pow_add,
      pow_one, mul_comm]
  have hn1 : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    rw [hn0, mul_zero, add_zero, pow_one] at hn
    have htop : Subgroup.center S = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (hcardZS.trans hn.symm)
    apply hUZ
    refine le_antisymm (fun u hu => ?_) hZU
    have h := hmemZ ⟨u, hu⟩ (by rw [← hZS, htop]; exact mem_top _)
    exact h
  obtain ⟨z, hz⟩ : ∃ z : S, Subgroup.center S = zpowers z := by
    have : IsCyclic (Subgroup.center S) := isCyclic_of_prime_card hcardZS
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Subgroup.center S)
    refine ⟨g, le_antisymm (fun s hs => ?_) (zpowers_le.mpr g.2)⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hg ⟨s, hs⟩)
    exact mem_zpowers_iff.mpr ⟨k, by
      have := congrArg Subtype.val hk
      simpa using this⟩
  let ρ : S →* MulAut D := QuotientGroup.kerLift φ
  have hρ : Function.Injective ρ := QuotientGroup.kerLift_injective φ
  have hfixS : ∀ s : S, s ≠ 1 → CFSG.pRank p (fixedSubgroupOf (ρ s)) ≤ 2 := by
    intro s hs
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective s
    have hu : (u : G) ∉ centralizer (D : Set G) := fun h =>
      hs ((QuotientGroup.eq_one_iff u).mpr (mem_ker_conjAction.mpr h))
    change CFSG.pRank p (fixedSubgroupOf (QuotientGroup.kerLift φ (u : U ⧸ φ.ker))) ≤ 2
    rw [QuotientGroup.kerLift_mk]
    exact (pRank_fixedSubgroupOf_le hp.out.one_lt hDP u).trans (hfix u u.2 hu)
  let γ : MulAut S := conjQuot hUD hxD hxU
  have hγfix : ∀ s, γ s * s⁻¹ ∈ Subgroup.center S → s ∈ Subgroup.center S := by
    intro s hs
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective s
    obtain ⟨hu, he⟩ := conjQuot_mk hUD hxD hxU u
    change conjQuot hUD hxD hxU (u : U ⧸ φ.ker) * _ ∈ _ at hs
    rw [he, hZS, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul] at hs
    have h1 := hmemZ _ hs
    rw [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    have h2 := hfpf u u.2 h1
    rw [hZS]
    exact ⟨u, h2, rfl⟩
  have hDp : IsPGroup p D := hP.to_le hDP
  have hDexp' : ∀ d : D, d ^ p = 1 := fun d =>
    Subtype.ext (by rw [Subgroup.coe_pow, hDexp d d.2, Subgroup.coe_one])
  exact eq_five_of_extraspecial_action hp2 hq hq3 hDp hDexp' (commutator_le_center_of_forall hDcl)
    hSx hn hn1 hz ρ hρ hfixS γ (conjQuot_pow_eq_one hUD hxD hxU hxq) hγfix

theorem mem_normalizer_inf {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) :=
  mem_normalizer_of_forall_conj_mem fun _ hc =>
    ⟨(mem_normalizer_iff.mp hA _).mp hc.1, (mem_normalizer_iff.mp hB _).mp hc.2⟩

theorem mem_normalizer_of_forall_commute {B : Subgroup G} {g : G}
    (h : ∀ b ∈ B, g * b = b * g) : g ∈ normalizer (B : Set G) :=
  mem_normalizer_of_forall_conj_mem fun b hb => by rw [h b hb, mul_inv_cancel_right]; exact hb

theorem exists_critical_subgroup {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {P U : Subgroup G}
    (hP : IsPGroup p P) (hU : IsPGroup 2 U) (hUP : U ≤ normalizer (P : Set G))
    (hfaith : U ⊓ centralizer (P : Set G) = ⊥) (hU1 : U ≠ ⊥) :
    ∃ D : Subgroup G, D ≤ P ∧ normalizer (P : Set G) ≤ normalizer (D : Set G) ∧
      (∀ d ∈ D, d ^ p = 1) ∧ (∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ⁅a, b⁆ * c = c * ⁅a, b⁆) ∧
      U ⊓ centralizer (D : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial P := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply hU1
    rw [eq_bot_iff, ← hfaith]
    intro u hu
    refine ⟨hu, mem_centralizer_iff.mpr fun g hg => ?_⟩
    have : (⟨g, hg⟩ : P) = 1 := Subsingleton.elim _ _
    have hg1 : g = 1 := congrArg Subtype.val this
    rw [hg1, one_mul, mul_one]
  obtain ⟨D', hD'char, -, hD'comm, hD'exp, hD'fix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hp2 hP
  refine ⟨D'.map P.subtype, map_subtype_le D', ?_, ?_, ?_, ?_⟩
  · intro g hg
    apply mem_normalizer_of_forall_conj_mem
    rintro _ ⟨d, hd, rfl⟩
    have h := Subgroup.characteristic_iff_map_eq.mp hD'char (P.normalizerMonoidHom ⟨g, hg⟩)
    have hσd : P.normalizerMonoidHom ⟨g, hg⟩ d ∈ D' := by
      rw [← h]
      exact mem_map_of_mem _ hd
    exact ⟨_, hσd, normalizerMonoidHom_apply_apply_coe _ _ _⟩
  · rintro _ ⟨d, hd, rfl⟩
    rw [← map_pow, hD'exp d hd, map_one]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
    have h := hD'comm (commutator_mem_commutator ha (mem_top b))
    have h2 := mem_centralizer_iff.mp h.2 c hc
    have h3 : ((c * ⁅a, b⁆ : P) : G) = ((⁅a, b⁆ * c : P) : G) := congrArg Subtype.val h2
    simp only [Subgroup.coe_mul, commutatorElement_def, Subgroup.coe_inv] at h3
    simp only [Subgroup.coe_subtype, commutatorElement_def]
    exact h3.symm
  · rw [eq_bot_iff]
    rintro u ⟨hu, huc⟩
    rw [mem_bot]
    have hσfix : P.normalizerMonoidHom ⟨u, hUP hu⟩ ∈ fixingSubgroup (MulAut P) (D' : Set P) := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      apply Subtype.ext
      change ((P.normalizerMonoidHom ⟨u, hUP hu⟩ y : P) : G) = y
      rw [normalizerMonoidHom_apply_apply_coe]
      have := mem_centralizer_iff.mp huc (y : G) ⟨y, hy, rfl⟩
      rw [← this, mul_inv_cancel_right]
    obtain ⟨k, hk⟩ := hD'fix ⟨_, hσfix⟩
    have hσk : P.normalizerMonoidHom ⟨u, hUP hu⟩ ^ p ^ k = 1 := by
      have := congrArg Subtype.val hk
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    obtain ⟨m, hm⟩ := hU ⟨u, hu⟩
    have hσm : P.normalizerMonoidHom ⟨u, hUP hu⟩ ^ 2 ^ m = 1 := by
      rw [← map_pow]
      have : (⟨u, hUP hu⟩ : normalizer (P : Set G)) ^ 2 ^ m = 1 := by
        apply Subtype.ext
        have := congrArg Subtype.val hm
        simpa using this
      rw [this, map_one]
    have hdvd : orderOf (P.normalizerMonoidHom ⟨u, hUP hu⟩) ∣ Nat.gcd (p ^ k) (2 ^ m) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hσk) (orderOf_dvd_of_pow_eq_one hσm)
    have hcop : Nat.Coprime (p ^ k) (2 ^ m) :=
      Nat.Coprime.pow k m ((Nat.coprime_primes hp.out Nat.prime_two).mpr hp2)
    rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
    have hcP : u ∈ centralizer (P : Set G) := by
      rw [mem_centralizer_iff]
      intro g hg
      have := congrArg (fun τ : MulAut P => ((τ ⟨g, hg⟩ : P) : G)) hdvd
      simp only [MulAut.one_apply] at this
      rw [normalizerMonoidHom_apply_apply_coe, mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    have : u ∈ U ⊓ centralizer (P : Set G) := ⟨hu, hcP⟩
    rwa [hfaith, mem_bot] at this

end Cases

theorem rank3II_3_6 {G : Type*} [Group G] [Finite G] {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : q.Prime) (hq3 : 3 < q) {P U X : Subgroup G} (hP : IsPGroup p P) (hU : IsPGroup 2 U)
    (hXq : Nat.card X = q) (hUX : ⁅U, X⁆ = U)
    (hU1 : U ≠ ⊥) (hUP : U ≤ normalizer (P : Set G)) (hXP : X ≤ normalizer (P : Set G))
    (hfaith : U ⊓ centralizer (P : Set G) = ⊥)
    (hfix : ∀ u ∈ U, u ≠ 1 → CFSG.Assembly.pRank p (P ⊓ centralizer ({u} : Set G)) ≤ 2) :
    q = 5 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq2 : q ≠ 2 := by omega
  have hX : IsPGroup q X := IsPGroup.of_card (n := 1) (by rw [hXq, pow_one])
  obtain ⟨x, hXx⟩ : ∃ x : G, X = zpowers x := by
    have : IsCyclic X := isCyclic_of_prime_card hXq
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := X)
    refine ⟨g, le_antisymm (fun y hy => ?_) (zpowers_le.mpr g.2)⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hg ⟨y, hy⟩)
    exact mem_zpowers_iff.mpr ⟨k, by
      have := congrArg Subtype.val hk
      simpa using this⟩
  have hxX : x ∈ X := hXx ▸ mem_zpowers x
  have hxq : x ^ q = 1 := by
    have h := pow_card_eq_one' (G := X) (x := ⟨x, hxX⟩)
    rw [hXq] at h
    have := congrArg Subtype.val h
    simpa using this
  obtain ⟨U₀, ⟨hU₀U, hU₀X, hU₀1⟩, hU₀min⟩ := (wellFounded_lt (α := Subgroup G)).has_min
    {V | V ≤ U ∧ ⁅V, X⁆ = V ∧ V ≠ ⊥} ⟨U, le_rfl, hUX, hU1⟩
  have hmin : ∀ V ≤ U₀, ⁅V, X⁆ = V → V ≠ ⊥ → V = U₀ := fun V hV hVX hV1 =>
    by_contra fun hne => hU₀min V ⟨hV.trans hU₀U, hVX, hV1⟩ (lt_of_le_of_ne hV hne)
  have hU₀2 : IsPGroup 2 U₀ := hU.to_le hU₀U
  have hXU₀ : X ≤ normalizer (U₀ : Set G) := by
    rw [← hU₀X]
    exact normalizer_commutator_ge_right U₀ X
  obtain ⟨D, hDP, hND, hDexp, hDcl, hDfaith⟩ := exists_critical_subgroup hp2 hP hU hUP hfaith hU1
  have hU₀D : U₀ ≤ normalizer (D : Set G) := (hU₀U.trans hUP).trans hND
  have hxD : x ∈ normalizer (D : Set G) := hND (hXP hxX)
  have hxU₀ : x ∈ normalizer (U₀ : Set G) := hXU₀ hxX
  have hfaith₀ : ∀ u ∈ U₀, u ∈ centralizer (D : Set G) → u = 1 := fun u hu hc => by
    have : u ∈ U ⊓ centralizer (D : Set G) := ⟨hU₀U hu, hc⟩
    rwa [hDfaith, mem_bot] at this
  have hfix₀ : ∀ D₀ : Subgroup G, ∀ u ∈ U₀, u ∉ centralizer (D₀ : Set G) →
      CFSG.Assembly.pRank p (P ⊓ centralizer ({u} : Set G)) ≤ 2 := fun D₀ u hu hc =>
    hfix u (hU₀U hu) (fun h => hc (h ▸ one_mem _))
  have hfpf : ∀ u ∈ U₀, x * u * x⁻¹ * u⁻¹ ∈ squares U₀ → u ∈ squares U₀ := fun u hu h =>
    mem_squares_of_conj_mul_inv_mem hq hq2 hXx hXq hU₀2 hXU₀ hU₀X hu h
  by_cases hab : ∀ a ∈ U₀, ∀ b ∈ U₀, a * b = b * a
  ·
    exfalso
    have hsq1 : ∀ u ∈ U₀, u ^ 2 = 1 := fun u hu =>
      sq_eq_one_of_commute hq hq2 hX hU₀2 hXU₀ hU₀X hU₀1 hmin hab hu
    have hF : squares U₀ = ⊥ := by
      rw [eq_bot_iff, squares, closure_le]
      rintro _ ⟨w, hw, rfl⟩
      rw [hsq1 w hw]
      exact one_mem _
    refine false_of_elemAbelian_section hp2 hq hq3 hP hDP hDexp hDcl hU₀D hxD hxU₀ hxq ?_ ?_ ?_
      ?_ (hfix₀ D)
    · intro a ha b hb
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hab a ha b hb)]
      exact one_mem _
    · intro a ha
      rw [hsq1 a ha]
      exact one_mem _
    · by_contra h
      push Not at h
      apply hU₀1
      rw [eq_bot_iff]
      intro u hu
      rw [mem_bot]
      exact hfaith₀ u hu (h u hu)
    · intro u hu hc
      have hw : x * u * x⁻¹ * u⁻¹ ∈ U₀ :=
        mul_mem ((mem_normalizer_iff.mp hxU₀ u).mp hu) (inv_mem hu)
      have h2 := hfpf u hu (by rw [hfaith₀ _ hw hc]; exact one_mem _)
      rw [hF, mem_bot] at h2
      rw [h2]
      exact one_mem _
  ·
    set Z := squares U₀ with hZdef
    have hZU₀ : Z ≤ U₀ := squares_le U₀
    have hZc : ∀ z ∈ Z, ∀ v ∈ U₀, z * v = v * z := fun z hz v hv =>
      squares_commute hq hq2 hX hU₀2 hXU₀ hU₀X hU₀1 hmin hz hv
    have hUUZ : ⁅U₀, U₀⁆ = Z := commutator_eq_squares hq hq2 hX hU₀2 hXU₀ hU₀X hU₀1 hmin
    have hZ2 : ∀ z ∈ Z, z ^ 2 = 1 := fun z hz =>
      sq_eq_one_of_mem_squares hq hq2 hX hU₀2 hXU₀ hU₀X hU₀1 hmin hz
    have hZne : Z ≠ U₀ := squares_ne hU₀2 hU₀1
    have hxZ : ∀ z ∈ Z, x * z * x⁻¹ = z := fun z hz =>
      conj_eq_of_mem_squares hq hq2 hX hU₀2 hXU₀ hU₀1 hmin hxX hz
    have hZbot : Z ≠ ⊥ := fun h => hab fun a ha b hb => by
      have : ⁅a, b⁆ ∈ ⁅U₀, U₀⁆ := commutator_mem_commutator ha hb
      rwa [hUUZ, h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    obtain ⟨r, hr⟩ := (hU₀2.to_le hZU₀).exists_card_eq
    have hr1 : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with h | h
      · rw [h, pow_zero, card_eq_one] at hr
        exact absurd hr hZbot
      · exact h
    have hZel : CFSG.Open.IsElemAbelian 2 Z :=
      ⟨⟨⟨fun a b => Subtype.ext (hZc a a.2 b (hZU₀ b.2))⟩⟩, hZ2⟩
    have hcopD : Nat.Coprime 2 (Nat.card D) := by
      obtain ⟨k, hk⟩ := (hP.to_le hDP).exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm)
    have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2
      (r - 1) Nat.prime_two Z D hZel (by rw [hr, show r - 1 + 1 = r by omega])
      (hZU₀.trans hU₀D) hcopD
    obtain ⟨Z₀, ⟨hZ₀Z, hZ₀card⟩, hZ₀act⟩ : ∃ Z₀ ∈ CFSG.Open.signalizerFunctorEk 2 (r - 1) Z,
        ¬ U₀ ≤ centralizer ((D ⊓ centralizer (Z₀ : Set G) : Subgroup G) : Set G) := by
      by_contra h
      push Not at h
      apply hU₀1
      have hle : D ≤ centralizer (U₀ : Set G) := by
        rw [← hgen]
        exact iSup₂_le fun Z₀ hZ₀ => (le_centralizer_iff.mp (h Z₀ hZ₀))
      rw [eq_bot_iff]
      intro u hu
      rw [mem_bot]
      exact hfaith₀ u hu (le_centralizer_iff.mp hle hu)
    set D₀ := D ⊓ centralizer (Z₀ : Set G) with hD₀
    have hD₀P : D₀ ≤ P := inf_le_left.trans hDP
    have hU₀D₀ : U₀ ≤ normalizer (D₀ : Set G) := fun u hu =>
      mem_normalizer_inf (hU₀D hu) (mem_normalizer_centralizer (mem_normalizer_of_forall_commute
        fun z hz => (hZc z (hZ₀Z hz) u hu).symm))
    have hxD₀ : x ∈ normalizer (D₀ : Set G) :=
      mem_normalizer_inf hxD (mem_normalizer_centralizer (mem_normalizer_of_forall_commute
        fun z hz => by
          have := hxZ z (hZ₀Z hz)
          calc x * z = x * z * x⁻¹ * x := by group
            _ = z * x := by rw [this]))
    set K := U₀ ⊓ centralizer (D₀ : Set G) with hKdef
    have hKne : K ≠ U₀ := fun h => hZ₀act (h ▸ inf_le_right)
    have hXK : X ≤ normalizer (K : Set G) := by
      intro y hy
      have hyZ₀ : ∀ z ∈ Z₀, y * z = z * y := fun z hz => by
        have := conj_eq_of_mem_squares hq hq2 hX hU₀2 hXU₀ hU₀1 hmin hy (hZ₀Z hz)
        calc y * z = y * z * y⁻¹ * y := by group
          _ = z * y := by rw [this]
      exact mem_normalizer_inf (hXU₀ hy) (mem_normalizer_centralizer (mem_normalizer_inf
        (hND (hXP hy)) (mem_normalizer_centralizer (mem_normalizer_of_forall_commute hyZ₀))))
    have hKX := commutator_eq_bot_of_ne hq hq2 hX hU₀2 hmin inf_le_left hXK hKne
    have hKZ : K ≤ Z := fun k hk => hfpf k hk.1 (by
      have : ⁅k, x⁆ ∈ ⁅K, X⁆ := commutator_mem_commutator hk hxX
      rw [hKX, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      rw [← this, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _)
    have hZ₀K : Z₀ ≤ K := fun z hz => ⟨hZU₀ (hZ₀Z hz), mem_centralizer_iff.mpr fun d hd =>
      (mem_centralizer_iff.mp hd.2 z hz).symm⟩
    have hKcard : Nat.card K = 2 ^ (r - 1) ∨ Nat.card K = 2 ^ r := by
      have h1 : Nat.card Z₀ ∣ Nat.card K := card_dvd_of_le hZ₀K
      have h2 : Nat.card K ∣ Nat.card Z := card_dvd_of_le hKZ
      rw [hZ₀card] at h1
      rw [hr] at h2
      obtain ⟨j, hj, hjK⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
      rw [hjK] at h1
      have : r - 1 ≤ j := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1
      rcases (show j = r - 1 ∨ j = r by omega) with h | h
      · left
        rw [hjK, h]
      · right
        rw [hjK, h]
    rcases hKcard with hK1 | hK2
    ·
      have hKZ₀ : K = Z₀ := (eq_of_le_of_card_ge hZ₀K (by rw [hK1, hZ₀card])).symm
      have hZ₀ne : Z₀ ≠ Z := fun h => by
        have := congrArg (fun H : Subgroup G => Nat.card H) h
        simp only [hZ₀card, hr] at this
        have := Nat.pow_right_injective (le_refl 2) this
        omega
      refine eq_five_of_extraspecial_section hp2 hq hq3 hP hD₀P (fun d hd => hDexp d hd.1)
        (fun a ha b hb c hc => hDcl a ha.1 b hb.1 c hc.1) hU₀D₀ hxD₀ hxU₀ hxq hU₀2 hZU₀ hZc hUUZ
        (fun u hu => sq_mem_squares hu) hZne.symm hKZ ?_ ?_ hfpf (hfix₀ D₀)
      · rw [hr, hK1, ← pow_succ']
        congr 1
        omega
      · intro u hu hc
        apply mem_squares_of_commutator_mem hq hq2 hXx hXq hX hU₀2 hXU₀ hU₀X hU₀1 hmin hZ₀Z hZ₀ne
          hu
        intro v hv
        have : ⁅u, v⁆ ∈ K :=
          ⟨le_normalizer_iff_commutator_le_left.mp le_normalizer
            (commutator_mem_commutator hu hv), hc v hv⟩
        rwa [hKZ₀] at this
    ·
      exfalso
      have hKZeq : K = Z := eq_of_le_of_card_ge hKZ (by rw [hK2, hr])
      refine false_of_elemAbelian_section hp2 hq hq3 hP hD₀P (fun d hd => hDexp d hd.1)
        (fun a ha b hb c hc => hDcl a ha.1 b hb.1 c hc.1) hU₀D₀ hxD₀ hxU₀ hxq ?_ ?_ ?_ ?_
        (hfix₀ D₀)
      · intro a ha b hb
        have : ⁅a, b⁆ ∈ K := by
          rw [hKZeq, ← hUUZ]
          exact commutator_mem_commutator ha hb
        exact this.2
      · intro a ha
        have : a ^ 2 ∈ K := by
          rw [hKZeq]
          exact sq_mem_squares ha
        exact this.2
      · by_contra h
        push Not at h
        exact hZ₀act fun u hu => h u hu
      · intro u hu hc
        have hw : x * u * x⁻¹ * u⁻¹ ∈ K := Subgroup.mem_inf.mpr
          ⟨mul_mem ((mem_normalizer_iff.mp hxU₀ u).mp hu) (inv_mem hu), hc⟩
        rw [hKZeq] at hw
        have := hfpf u hu hw
        rw [← hKZeq] at this
        exact this.2

end CFSG.RankThree.PartTwo.Sec3
