module

import CFSG.RankThree.PartTwo.Sec21.Item21Res8ProofFusion
import CFSG.RankThree.PartTwo.Sec13.Item134Dichotomy
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec12.KS128NotHJSLTools
import CFSG.Timmesfeld.Orders.Exceptional
import CFSG.RankThree.PartTwo.Sec21.Item2113Res3ProofRankTools
import CFSG.RankThree.PartTwo.Sec21.Item2130Res3ProofTypes
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.RankThree.PartOne.S11d.Common
import CFSG.RankThree.PartOne.S11c.HNAlternating
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.Sporadic.He.Simple
public import CFSG.RankThree.PartTwo.Sec21.Item2110Res3ProofAL
public import CFSG.RankThree.PartTwo.Sec21.Item229Orders

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint

@[expose] def Item2110JONHJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → IsList218 L → Nonempty (lBar L ≃* NativeSporadic.J2) →
    ∀ d ∈ A, d ≠ 1 → IsCentral218 L d →
      ∀ J ∈ thetaComponentsAt 3 d, iOf218 L d ≤ J →
        Sec4.IsTripleCover (lBar (iOf218 L d)) (alternatingGroup (Fin 6)) →
        ¬ Sec4.IsTripleCover (lBar J) NativeSporadic.ON

namespace Item21Res8Proof

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem lBar_sporadic_of_A6 {L : Subgroup G} {d : G}
    (hdI : d ∈ iOf218 L d) (hdc : ∀ x ∈ iOf218 L d, x * d = d * x) (hd3 : d ^ 3 = 1)
    (hd1 : d ≠ 1)
    (h : (Nonempty (L ≃* NativeSporadic.He) ∧
            Sec4.IsTripleCover (iOf218 L d) (alternatingGroup (Fin 7))) ∨
          ((Nonempty (lBar L ≃* NativeSporadic.M24) ∨ Nonempty (lBar L ≃* NativeSporadic.J2) ∨
              Nonempty (lBar L ≃* NativeSporadic.Ru)) ∧
            Sec4.IsTripleCover (lBar (iOf218 L d)) (alternatingGroup (Fin 6))) ∨
          (Nonempty (L ≃* NativeSporadic.J4) ∧
            Nat.card (Subgroup.center (iOf218 L d)) = 6 ∧
            Nonempty (iOf218 L d ⧸ Subgroup.center (iOf218 L d) ≃* NativeSporadic.M22)) ∨
          (∃ n : ℕ, 0 < n ∧ Even n ∧
            (ChevalleyExceptionalModel (lBar L) .G2 2 n ∨
              ChevalleyExceptionalModel (lBar L) .trialityD4 2 n) ∧
            Nonempty (lBar (iOf218 L d) ≃* SL3 n)))
    (hA6 : Sec4.IsTripleCover (lBar (iOf218 L d)) (alternatingGroup (Fin 6))) :
    Nonempty (lBar L ≃* NativeSporadic.M24) ∨ Nonempty (lBar L ≃* NativeSporadic.J2) ∨
      Nonempty (lBar L ≃* NativeSporadic.Ru) := by
  have h1080 : Nat.card (lBar (iOf218 L d)) = 1080 := Sec13.card_eq_of_isTripleCover_six hA6
  have hIp := Item2113Res3Proof.isPerfect_iOf218 L d
  rcases h with ⟨-, hcard, ⟨e⟩⟩ | ⟨hL, -⟩ | ⟨-, hcard, ⟨e⟩⟩ | ⟨n, hn, hev, -, ⟨e⟩⟩
  · exfalso
    have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
    obtain ⟨s, m, hs3, hs1, hm⟩ := Item2113Res3Proof.alternating_seven_real
    obtain ⟨hq, -⟩ := Item2113Res3Proof.isQuasisimple_and_exists_of_real hIp e hs3 hs1 hm
    have hT := Item2110Res3Proof.isTripleCover_lBar_of hq (by rw [hcard]; norm_num) e hdI hdc
      hd3 hd1
    have h1 := Item2113Proof.card_of_isTripleCover hT
    rw [h1080, PartOne.HNRed.card_alternatingGroup_fin 7 (by norm_num)] at h1
    norm_num [Nat.factorial] at h1
  · exact hL
  · exfalso
    have : IsSimpleGroup NativeSporadic.M22 := CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
    obtain ⟨s, -, m, hs, -, -, hm⟩ := Native.m22_witness
    have hs3 : s ^ 3 = 1 := hs ▸ pow_orderOf_eq_one s
    have hs1 : s ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hs; norm_num at hs
    obtain ⟨hq, -⟩ := Item2113Res3Proof.isQuasisimple_and_exists_of_real hIp e hs3 hs1 hm
    have hT := Item2110Res3Proof.isTripleCover_lBar_of hq (by simp [hcard]) e hdI hdc hd3 hd1
    have h1 := Item2113Proof.card_of_isTripleCover hT
    rw [h1080, KFacts.KS14.card_nativeM22] at h1
    norm_num at h1
  · exact absurd (Item2130Res3Proof.isSLThreePiAt_of_SL3 hn hev e)
      (Sec13.not_isSLThreePiAt_two_pow h1080 hn)


theorem exists_conj_of_gl {A L : Subgroup G} {c d : G} (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (hcA : c ∈ A) (hLc : L ≤ centralizer ({c} : Set G))
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) (hAcL : zpowers c ⊔ (A ⊓ L) = A)
    (hdA : d ∈ A) (hdL : d ∈ L) (hd1 : d ≠ 1)
    (hGL : Nonempty (starOf A L ≃* GL (Fin 2) (ZMod 3))) :
    ∃ a ∈ A ⊓ L, a ∉ zpowers d ∧ ∃ g ∈ L,
      (zpowers a).map (MulAut.conj g).toMonoidHom = zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  push Not at hcon
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hfix : ∀ n ∈ L, n ∈ normalizer (A : Set G) → n * d * n⁻¹ ∈ zpowers d := by
    intro n hnL hnA
    by_contra hnd
    have ha : n * d * n⁻¹ ∈ A ⊓ L :=
      ⟨(mem_normalizer_iff.mp hnA d).mp hdA, L.mul_mem (L.mul_mem hnL hdL) (L.inv_mem hnL)⟩
    apply hcon _ ha hnd n⁻¹ (L.inv_mem hnL)
    rw [MonoidHom.map_zpowers]
    congr 1
    simp [mul_assoc]
  obtain ⟨b, hbAL, hbd⟩ : ∃ b ∈ A ⊓ L, b ∉ zpowers d := by
    by_contra hne
    push Not at hne
    have := card_le_of_le (show A ⊓ L ≤ zpowers d from hne)
    rw [h9, Sec13.card_zpowers_of_pow_three hd3 hd1] at this
    omega
  have hb3 : b ^ 3 = 1 := hAe.2 b hbAL.1
  have hb1 : b ≠ 1 := fun h => hbd (h ▸ one_mem _)
  have hbdc : ∀ x ∈ zpowers b, ∀ y ∈ zpowers d, x * y = y * x := fun x hx y hy =>
    hcomm x (zpowers_le.mpr hbAL.1 hx) y (zpowers_le.mpr hdA hy)
  have hY : zpowers b ⊔ zpowers d = A ⊓ L := by
    have hle : zpowers b ⊔ zpowers d ≤ A ⊓ L :=
      sup_le (zpowers_le.mpr hbAL) (zpowers_le.mpr ⟨hdA, hdL⟩)
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hbdc
    rw [Sec13.zpowers_inf_eq_bot hb3 hbd, card_bot, mul_one,
      Sec13.card_zpowers_of_pow_three hb3 hb1, Sec13.card_zpowers_of_pow_three hd3 hd1] at hcard
    exact eq_of_le_of_card_ge hle (by rw [h9, hcard])
  have hmem : ∀ φ ∈ starOf A L, ∃ n : normalizer (A : Set G), (n : G) ∈ L ∧
      φ = A.normalizerMonoidHom n := by
    rintro φ ⟨n, hn, rfl⟩
    exact ⟨n, mem_subgroupOf.mp hn, rfl⟩
  set d₀ : A := ⟨d, hdA⟩ with hd₀
  set b₀ : A := ⟨b, hbAL.1⟩ with hb₀
  have h1 : ∀ φ : starOf A L, (φ : MulAut A) d₀ ∈ zpowers d₀ := by
    intro φ
    obtain ⟨n, hnL, hφ⟩ := hmem φ φ.2
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hfix n hnL n.2)
    refine mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
    rw [hφ, normalizerMonoidHom_apply_apply_coe, coe_zpow, ← hk]
  have h2 : ∀ φ : starOf A L, (φ : MulAut A) b₀ ∈ (A ⊓ L).subgroupOf A := by
    intro φ
    obtain ⟨n, hnL, hφ⟩ := hmem φ φ.2
    rw [mem_subgroupOf, hφ, normalizerMonoidHom_apply_apply_coe]
    exact ⟨(mem_normalizer_iff.mp n.2 b).mp hbAL.1,
      L.mul_mem (L.mul_mem hnL hbAL.2) (L.inv_mem hnL)⟩
  let F : starOf A L → zpowers d₀ × (A ⊓ L).subgroupOf A :=
    fun φ => (⟨(φ : MulAut A) d₀, h1 φ⟩, ⟨(φ : MulAut A) b₀, h2 φ⟩)
  have hinj : Function.Injective F := by
    intro φ ψ hφψ
    have hd' : (φ : MulAut A) d₀ = (ψ : MulAut A) d₀ := congrArg (fun p => (p.1 : A)) hφψ
    have hb' : (φ : MulAut A) b₀ = (ψ : MulAut A) b₀ := congrArg (fun p => (p.2 : A)) hφψ
    have hc' : ∀ χ : starOf A L, (χ : MulAut A) ⟨c, hcA⟩ = ⟨c, hcA⟩ := by
      intro χ
      obtain ⟨n, hnL, hχ⟩ := hmem χ χ.2
      apply Subtype.ext
      rw [hχ, normalizerMonoidHom_apply_apply_coe]
      show (n : G) * c * (n : G)⁻¹ = c
      rw [mem_centralizer_singleton_iff.mp (hLc hnL), mul_inv_cancel_right]
    set Eq : Subgroup G := (MonoidHom.eqLocus (φ : MulAut A).toMonoidHom
      (ψ : MulAut A).toMonoidHom).map A.subtype with hEq
    have hmemEq : ∀ x (hx : x ∈ A), (φ : MulAut A) ⟨x, hx⟩ = (ψ : MulAut A) ⟨x, hx⟩ →
        x ∈ Eq := fun x hx h => ⟨⟨x, hx⟩, h, rfl⟩
    have hAEq : A ≤ Eq := by
      rw [← hAcL, ← hY]
      refine sup_le (zpowers_le.mpr (hmemEq c hcA ((hc' φ).trans (hc' ψ).symm)))
        (sup_le (zpowers_le.mpr (hmemEq b hbAL.1 hb')) (zpowers_le.mpr (hmemEq d hdA hd')))
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    obtain ⟨y, hy, hyx⟩ := hAEq x.2
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact hy
  have hle := Nat.card_le_card_of_injective F hinj
  rw [Nat.card_prod, Nat.card_zpowers, orderOf_eq_prime (Subtype.ext hd3 : d₀ ^ 3 = 1)
      (fun h => hd1 (congrArg Subtype.val h)),
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : A ⊓ L ≤ A)).toEquiv, h9] at hle
  obtain ⟨e⟩ := hGL
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field] at hle
  simp [ZMod.card] at hle


theorem false_of_ne_of_maximal {A J K : Subgroup G} {d y₀ : G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (hmax : ∀ E : Subgroup G, CFSG.Assembly.IsElemAbelian 3 E → A ≤ E → E = A)
    (hAJ : A ≤ J) (hJ : J ∈ thetaComponentsAt 3 d) (hK : K ∈ thetaComponentsAt 3 d)
    (hne : J ≠ K) (hAN : A ≤ normalizer (K : Set G)) (hZ : center (lBar K) = ⊥)
    (hy₀ : y₀ ∈ K) (hy₀3 : y₀ ^ 3 = 1) (hy₀1 : y₀ ≠ 1) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := aschbacherSolvableCore 3 ↥K with hNdef
  set π := QuotientGroup.mk' N with hπ
  obtain ⟨-, -, hN3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := K) Nat.prime_three
  have hKd : K ≤ centralizer ({d} : Set G) := Sec6.le_centralizer_of_mem_thetaComponentsAt hK
  have htriv : ∀ a ∈ A, ∀ l ∈ K,
      a * l * a⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) K := by
    intro a ha l hl
    have h1 := PartOne.S11d.commutator_mem_theta_of_ne Nat.prime_three hJ hK hne a (hAJ ha) l hl
    have h2 : a * l * a⁻¹ * l⁻¹ ∈ K :=
      K.mul_mem ((mem_normalizer_iff.mp (hAN ha) l).mp hl) (K.inv_mem hl)
    exact Item2110Res3Proof.inSubgroup_theta_inf_le hKd ⟨h1, h2⟩
  let α : A →* MulAut K := K.normalizerMonoidHom.comp (inclusion hAN)
  have hα : ∀ (a : A) (z : K), ((α a z : K) : G) = a * z * (a : G)⁻¹ := fun a z =>
    normalizerMonoidHom_apply_apply_coe K _ z
  have hαN : ∀ a : A, ∀ n ∈ N, α a n ∈ N := by
    intro a n hn
    show (α a) n ∈ aschbacherSolvableCore 3 K
    rw [← Sec4.map_aschbacherSolvableCore (α a)]
    exact mem_map_of_mem _ hn
  have hfix : ∀ (a : A) (z : K), π (α a z) = π z := by
    intro a z
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    obtain ⟨t, ht, hte⟩ := htriv a a.2 (z⁻¹ : K) (K.inv_mem z.2)
    have : (α a z)⁻¹ * z = t := by
      apply Subtype.ext
      have hte' : (t : G) = a * ((z⁻¹ : K) : G) * (a : G)⁻¹ * ((z⁻¹ : K) : G)⁻¹ := hte
      rw [hte', coe_mul, coe_inv, hα, coe_inv, inv_inv]
      group
    rw [this]
    exact ht
  set x := π ⟨y₀, hy₀⟩ with hxdef
  have hx3 : x ^ 3 = 1 := by
    rw [hxdef, ← map_pow]
    have : (⟨y₀, hy₀⟩ : K) ^ 3 = 1 := Subtype.ext (by simpa using hy₀3)
    rw [this, map_one]
  have hx1 : x ≠ 1 := by
    intro h1
    rw [hxdef, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have := Sec13.eq_one_of_pow_three_pow_of_not_dvd hN3 h1 (k := 1)
      (Subtype.ext (by simpa using hy₀3))
    exact hy₀1 (congrArg Subtype.val this)
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 3 hA3 α N hαN hN3
  have hxmem : x ∈ {q : K ⧸ N | ∀ a : A,
      CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hαN a q = q} := by
    intro a
    exact hfix a ⟨y₀, hy₀⟩
  rw [hlift] at hxmem
  obtain ⟨x₁, hx₁, hx₁x⟩ := hxmem
  obtain ⟨e, m, hm3, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x₁).ne' 3 (by norm_num)
  set y : K := x₁ ^ m with hy
  have hx₁A : ∀ a ∈ A, a * (x₁ : G) = x₁ * a := by
    intro a ha
    have h1 : (a : G) * x₁ * a⁻¹ = x₁ := by
      rw [← hα ⟨a, ha⟩ x₁]
      exact congrArg Subtype.val (hx₁ ⟨a, ha⟩)
    calc a * (x₁ : G) = a * x₁ * a⁻¹ * a := by group
      _ = x₁ * a := by rw [h1]
  have hyA : ∀ a ∈ A, a * (y : G) = (y : G) * a := by
    intro a ha
    rw [hy, coe_pow]
    exact ((Commute.pow_right (hx₁A a ha) m)).eq
  have hy3e : y ^ 3 ^ e = 1 := by
    rw [hy, ← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  have hπy : π y = x ^ m := by
    rw [hy, map_pow]
    exact congrArg (· ^ m) hx₁x
  have hy3 : y ^ 3 = 1 := by
    have hmemN : y ^ 3 ∈ N := by
      have h1 : π (y ^ 3) = 1 := by
        rw [map_pow, hπy, ← pow_mul, mul_comm, pow_mul, hx3, one_pow]
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Sec13.eq_one_of_pow_three_pow_of_not_dvd hN3 hmemN (k := e)
      (by rw [← pow_mul, mul_comm, pow_mul, hy3e, one_pow])
  have hxm : x = (x ^ m) ^ m := by
    have hmm : m * m % 3 = 1 := by
      have : m % 3 = 1 ∨ m % 3 = 2 := by omega
      rcases this with h | h <;> simp [Nat.mul_mod, h]
    rw [← pow_mul, ← Nat.mod_add_div (m * m) 3, hmm, pow_add, pow_mul, hx3, one_pow, mul_one,
      pow_one]
  have hπy1 : π y ≠ 1 := by
    intro h1
    apply hx1
    rw [hxm, ← hπy, h1, one_pow]
  have hyA' : (y : G) ∉ A := by
    intro hyA'
    apply hπy1
    have hcen : π y ∈ center (lBar K) := by
      rw [mem_center_iff]
      intro q
      obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective N q
      have h1 := hfix ⟨y, hyA'⟩ z
      have h2 : α ⟨y, hyA'⟩ z = y * z * y⁻¹ := Subtype.ext (by rw [hα]; rfl)
      rw [h2, map_mul, map_mul, map_inv] at h1
      calc QuotientGroup.mk' N z * π y = π y * QuotientGroup.mk' N z * (π y)⁻¹ * π y := by
            rw [h1]
        _ = π y * QuotientGroup.mk' N z := by group
    rw [hZ, mem_bot] at hcen
    exact hcen
  have hy3' : (y : G) ^ 3 = 1 := by rw [← coe_pow, hy3, coe_one]
  have hE := Sec13.isElemAbelian_sup hAe (Sec13.isElemAbelian_zpowers hy3')
    (fun a ha z hz => by
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hz
      exact (Commute.zpow_right (hyA a ha) n).eq)
  apply hyA'
  rw [← hmax _ hE le_sup_left]
  exact mem_sup_right (mem_zpowers _)

theorem isE27_zpowers_sup {c d a : G} (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1) (ha3 : a ^ 3 = 1)
    (hd1 : d ≠ 1) (ha1 : a ≠ 1) (had : a ∉ zpowers d) (hcd : c * d = d * c)
    (hca : c * a = a * c) (hda : d * a = a * d) (hc : c ∉ zpowers d ⊔ zpowers a) :
    Late.IsE27 (zpowers c ⊔ (zpowers d ⊔ zpowers a)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdac : ∀ x ∈ zpowers a, ∀ y ∈ zpowers d, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact ((Commute.zpow_zpow (show Commute a d from hda.symm) i j)).eq
  have hY9 : Nat.card (zpowers d ⊔ zpowers a : Subgroup G) = 9 := by
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hdac
    rw [Sec13.zpowers_inf_eq_bot ha3 had, card_bot, mul_one,
      Sec13.card_zpowers_of_pow_three ha3 ha1, Sec13.card_zpowers_of_pow_three hd3 hd1,
      sup_comm] at hcard
    exact hcard
  have hYe : CFSG.Assembly.IsElemAbelian 3 (zpowers d ⊔ zpowers a) :=
    Sec13.isElemAbelian_sup (Sec13.isElemAbelian_zpowers hd3) (Sec13.isElemAbelian_zpowers ha3)
      (fun x hx y hy => (hdac y hy x hx).symm)
  have hcY : ∀ y ∈ zpowers d ⊔ zpowers a, c * y = y * c := by
    intro y hy
    have hle : zpowers d ⊔ zpowers a ≤ centralizer ({c} : Set G) := by
      refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
      · exact mem_centralizer_singleton_iff.mpr hcd.symm
      · exact mem_centralizer_singleton_iff.mpr hca.symm
    exact (mem_centralizer_singleton_iff.mp (hle hy)).symm
  obtain ⟨hE, h27⟩ := Sec13.isElemAbelian_zpowers_sup_of_card_nine hc3 hc le_rfl hY9
    (fun s hs => hYe.2 s hs) hcY
  exact ⟨hE, h27⟩


section Certs


omit [Finite G] in
theorem not_list_of_sporadic
    {L : Subgroup G}
    (hMR : Nonempty (lBar L ≃* NativeSporadic.M24) ∨ Nonempty (lBar L ≃* NativeSporadic.Ru)) :
    (¬ ∃ n : ℕ, 0 < n ∧ Even n ∧ (ChevalleyExceptionalModel (lBar L) .G2 2 n ∨
        ChevalleyExceptionalModel (lBar L) .trialityD4 2 n)) ∧
      ¬ Nonempty (lBar L ≃* NativeSporadic.J2) := by
  have hc : Nat.card (lBar L) = 2 ^ 10 * 239085 ∨ Nat.card (lBar L) = 2 ^ 14 * 8906625 := by
    rcases hMR with e | e
    · left
      rw [Nat.card_congr e.some.toEquiv, Sporadic.Mathieu.card_M24]
      norm_num
    · right
      rw [Nat.card_congr e.some.toEquiv, Sporadic.Ru.card_Ru]
      norm_num
  have hv : padicValNat 2 (Nat.card (lBar L)) = 10 ∨ padicValNat 2 (Nat.card (lBar L)) = 14 := by
    rcases hc with h | h
    · left
      rw [h]
      exact padicValNat_two_pow_mul_odd (by decide)
    · right
      rw [h]
      exact padicValNat_two_pow_mul_odd (by decide)
  refine ⟨?_, ?_⟩
  · rintro ⟨n, hn, -, hG2 | hD4⟩
    · have hcG : Nat.card (lBar L) = CFSG.Open.ordG2 (2 ^ n) :=
        Timmesfeld.card_chevalleyExceptionalModel_two hG2
      have h1 := Item218Proof.padicValNat_ordG2 hn
      rw [← hcG] at h1
      omega
    · have hcD : Nat.card (lBar L) = CFSG.Open.ordTrialityD4 (2 ^ n) :=
        Timmesfeld.card_chevalleyExceptionalModel_two hD4
      have h1 := Item218Proof.padicValNat_ordTrialityD4 hn
      rw [← hcD] at h1
      omega
  · rintro ⟨e⟩
    rw [Nat.card_congr e.toEquiv, KFacts.KS14.card_nativeJ2] at hc
    rcases hc with h | h <;> norm_num at h

theorem false_of_ru_d12
    (h211 : Item211) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hL : IsList218 L)
    (hRu : Nonempty (lBar L ≃* NativeSporadic.Ru))
    (hD12 : Nonempty (starOf A L ≃* DihedralGroup 6)) : False := by
  have h27 := Item2113Proof.card_eq_of_isList218 h211 hpair hL
  have h12 : Nat.card (starOf A L) = 12 := by
    obtain ⟨e⟩ := hD12
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have key : ∀ (X : Type) [Group X], Nonempty (starOf A L ≃* X) → Nat.card X = 12 :=
    fun X _ ⟨e⟩ => (Nat.card_congr e.toEquiv).symm.trans h12
  have hRuc : Nat.card (lBar L) = 145926144000 := by
    obtain ⟨e⟩ := hRu
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Ru.card_Ru]
  have hS3 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have hD8 : Nat.card (DihedralGroup 4) = 8 := by rw [DihedralGroup.nat_card]
  rcases h211 G A E U c L hpair with ⟨-, -, -, -, h9⟩ | ⟨-, -, hQ8⟩ | ⟨-, -, hSD⟩ |
      ⟨hMH, -, -⟩ | ⟨-, -, hS⟩ | ⟨-, -, hGL⟩ | ⟨-, -, hS⟩ | ⟨hGD, -, -⟩ | ⟨-, -, hD⟩ |
      ⟨-, h81, -⟩ | ⟨-, h81, -⟩ | ⟨-, -, hD⟩ | ⟨-, h81, -⟩
  · rw [h12] at h9
    norm_num at h9
  · have h := key _ hQ8
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card] at h
    norm_num at h
  · have h := key _ hSD
    rw [CFSG.Semidihedral.card 4 (by norm_num)] at h
    norm_num at h
  · rcases hMH with e | e
    · rw [Nat.card_congr e.some.toEquiv, CFSG.Sporadic.Mathieu.card_M24] at hRuc
      norm_num at hRuc
    · rw [Nat.card_congr e.some.toEquiv, CFSG.Sporadic.He.card_He] at hRuc
      norm_num at hRuc
  · have h := key _ hS
    rw [hS3] at h
    norm_num at h
  · have h := key _ hGL
    rw [Matrix.card_GL_field] at h
    simp [ZMod.card, Fin.prod_univ_two] at h
  · have h := key _ hS
    rw [hS3] at h
    norm_num at h
  · exact (not_list_of_sporadic (Or.inr hRu)).1 hGD
  · have h := key _ hD
    rw [hD8] at h
    norm_num at h
  · rw [h27] at h81
    norm_num at h81
  · rw [h27] at h81
    norm_num at h81
  · have h := key _ hD
    rw [hD8] at h
    norm_num at h
  · rw [h27] at h81
    norm_num at h81

end Certs

omit [Finite G] in
theorem map_conj_map_conj' (S : Subgroup G) (a b : G) :
    (S.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      S.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev,
    mul_assoc]

end Item21Res8Proof

open Item21Res8Proof

section Main


theorem item2110JON_of_res8 (h211 : Item211) (h45 : Sec4.Item4_5) (h219 : Item219)
    (hAL : Item2110ALInI) (hHJ : Item2110JONHJ) : Item2110JON := by
  intro G _ _ A E U c L hpair hL d hdA hd1 hdcen J hJ hIJ hIA6 hJON
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcA, hc1, hLc, -, hcL⟩ := Item2113Res2Proof.pair_data h45 hpair hL
  have hAe := hpair.mem_S.1.1
  have hmax : ∀ E' : Subgroup G, CFSG.Assembly.IsElemAbelian 3 E' → A ≤ E' → E' = A :=
    hpair.mem_S.1.2.1
  have hG := hpair.standing.toTheoremFourHyp
  have h27' : Nat.card A = 3 ^ 3 := Item2113Proof.card_eq_of_isList218 h211 hpair hL
  have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 :=
    Item2113Res3Proof.card_inf_eq_nine h211 h45 hpair hL
  obtain ⟨hdI, hcases⟩ := h219 G A E U c L hpair hL d hdA hd1 hdcen
  have hdL : d ∈ L := Item2113Proof.mem_of_isCentral218 hdcen
  have hIL : iOf218 L d ≤ L := (Subgroup.map_subtype_le _).trans inf_le_left
  have hIC : iOf218 L d ≤ Subgroup.centralizer ({d} : Set G) :=
    (Subgroup.map_subtype_le _).trans inf_le_right
  have hdc : ∀ x ∈ iOf218 L d, x * d = d * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hIC hx)
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  rcases lBar_sporadic_of_A6 hdI hdc hd3 hd1 hcases hIA6 with hM24 | hJ2 | hRu
  rotate_left
  · exact hHJ G A E U c L hpair hL hJ2 d hdA hd1 hdcen J hJ hIJ hIA6 hJON
  all_goals
    have hMR : Nonempty (lBar L ≃* NativeSporadic.M24) ∨
        Nonempty (lBar L ≃* NativeSporadic.Ru) := by
      first
        | exact Or.inl ‹_›
        | exact Or.inr ‹_›
  all_goals
    have hALI : A ⊓ L ≤ iOf218 L d := hAL G A E U c L hpair hL d hdA hd1 hdcen
    have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
    have hLcomp : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
    have hAcL : Subgroup.zpowers c ⊔ (A ⊓ L) = A := by
      have hle : Subgroup.zpowers c ⊔ (A ⊓ L) ≤ A :=
        sup_le (Subgroup.zpowers_le.mpr hcA) inf_le_left
      have hlt : A ⊓ L < Subgroup.zpowers c ⊔ (A ⊓ L) := by
        refine lt_of_le_of_ne le_sup_right fun h => hcL ?_
        have hc' : c ∈ Subgroup.zpowers c ⊔ (A ⊓ L) :=
          Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
        rw [← h] at hc'
        exact hc'.2
      have hdvd : Nat.card (Subgroup.zpowers c ⊔ (A ⊓ L) : Subgroup G) ∣ 3 ^ 3 := by
        rw [← h27']
        exact Subgroup.card_dvd_of_le hle
      obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
      have hgt : 9 < Nat.card (Subgroup.zpowers c ⊔ (A ⊓ L) : Subgroup G) := by
        rw [← h9]
        exact Subgroup.card_lt_of_lt hlt
      have hj3 : j = 3 := by
        rcases j with _ | _ | _ | _ | j
        · rw [hjc] at hgt; norm_num at hgt
        · rw [hjc] at hgt; norm_num at hgt
        · rw [hjc] at hgt; norm_num at hgt
        · rfl
        · omega
      exact Subgroup.eq_of_le_of_card_ge hle (by rw [hjc, hj3, h27'])
    have hAJ : A ≤ Subgroup.normalizer (J : Set G) :=
      Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe hdA hd1 J hJ
    have hJd : J ≤ Subgroup.centralizer ({d} : Set G) :=
      Sec6.le_centralizer_of_mem_thetaComponentsAt hJ
    have hq : IsQuasisimple (J ⧸ aschbacherSolvableCore 3 J) :=
      Sec6.isQuasisimple_of_mem_thetaComponentsAt hJ
    have hcJ : c ∈ J := Sec13.ON134.mem_of_maximal hAe hmax hcA inf_le_left h9
      (hALI.trans hIJ) hAcL.symm (hAJ hcA) ⟨hdA, hdL⟩ hd1 hJd hq hJON
    have hAJ' : A ≤ J := by
      rw [← hAcL]
      exact sup_le (Subgroup.zpowers_le.mpr hcJ) (hALI.trans hIJ)
    obtain ⟨a, haI, ha3, had, gL, hgL, hgLa⟩ : ∃ a ∈ iOf218 L d, a ^ 3 = 1 ∧
        a ∉ Subgroup.zpowers d ∧ ∃ g ∈ L,
          (Subgroup.zpowers a).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers d := by
      have hnot := not_list_of_sporadic hMR
      rcases Item2113Res2Proof.starOf_cases_of_isList218 h211 hpair hL with
        ⟨-, hD12 | hGL⟩ | ⟨hGD, -⟩ | ⟨hJ2', -⟩
      ·
        have hI27 : 3 ^ 3 ∣ Nat.card (iOf218 L d) := by
          refine (show 3 ^ 3 ∣ Nat.card (lBar (iOf218 L d)) by
            rw [Sec13.card_eq_of_isTripleCover_six hIA6]; norm_num).trans ?_
          exact Item2110Res3Proof.card_lBar_dvd _
        rcases hMR with hM24' | hRu'
        · exact exists_fusion_of_m24 hM24' hdcen hd3 hd1 hI27
        · exact (false_of_ru_d12 h211 hpair hL hRu' hD12).elim
      · obtain ⟨a, haAL, had, g, hg, hga⟩ :=
          exists_conj_of_gl hAe hcA hLc h9 hAcL hdA hdL hd1 hGL
        exact ⟨a, hALI haAL, hAe.2 a haAL.1, had, g, hg, hga⟩
      · exact (hnot.1 hGD).elim
      · exact (hnot.2 hJ2').elim
    have ha1 : a ≠ 1 := fun h => had (h ▸ Subgroup.one_mem _)
    have hcd : c * d = d * c := hcomm c hcA d hdA
    have hca : c * a = a * c :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hLc (hIL haI))).symm
    have hda : d * a = a * d := (hdc a haI).symm
    have hcda : c ∉ Subgroup.zpowers d ⊔ Subgroup.zpowers a := fun h =>
      hcL ((sup_le (Subgroup.zpowers_le.mpr hdL) (Subgroup.zpowers_le.mpr (hIL haI))) h)
    have hE' := isE27_zpowers_sup hc3 hd3 ha3 hd1 ha1 had hcd hca hda hcda
    have hE'J : Subgroup.zpowers c ⊔ (Subgroup.zpowers d ⊔ Subgroup.zpowers a) ≤ J :=
      sup_le (Subgroup.zpowers_le.mpr hcJ)
        (sup_le (Subgroup.zpowers_le.mpr (hIJ hdI)) (Subgroup.zpowers_le.mpr (hIJ haI)))
    have hdE' : d ∈ Subgroup.zpowers c ⊔ (Subgroup.zpowers d ⊔ Subgroup.zpowers a) :=
      Subgroup.mem_sup_right (Subgroup.mem_sup_left (Subgroup.mem_zpowers d))
    have hcE' : c ∈ Subgroup.zpowers c ⊔ (Subgroup.zpowers d ⊔ Subgroup.zpowers a) :=
      Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
    have haE' : a ∈ Subgroup.zpowers c ⊔ (Subgroup.zpowers d ⊔ Subgroup.zpowers a) :=
      Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
    have hcnd : c ∉ Subgroup.zpowers d := fun h => hcL (Subgroup.zpowers_le.mpr hdL h)
    obtain ⟨g, -, hg⟩ := Sec13.ON134.exists_conj_of_le hE' hE'J hdE' hd1 hJd hq hJON hcE' haE'
      hcnd had
    set h := gL * g with hh
    have hch : (Subgroup.zpowers c).map (MulAut.conj h).toMonoidHom = Subgroup.zpowers d := by
      rw [hh, ← map_conj_map_conj', hg, hgLa]
    have hchd : Subgroup.zpowers (h * c * h⁻¹) = Subgroup.zpowers d := by
      rw [← hch, MonoidHom.map_zpowers]
      rfl
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hchd ▸ Subgroup.mem_zpowers (h * c * h⁻¹))
    have hk3 : ¬ (3 : ℤ) ∣ k := by
      rintro ⟨k', rfl⟩
      apply hc1
      have h1 : h * c * h⁻¹ = 1 := by
        rw [← hk, zpow_mul, show (d ^ (3 : ℤ)) = 1 by rw [zpow_ofNat, hd3], one_zpow]
      calc c = h⁻¹ * (h * c * h⁻¹) * h := by group
        _ = 1 := by rw [h1]; group
    have hCd : Subgroup.centralizer ({h * c * h⁻¹} : Set G) =
        Subgroup.centralizer ({d} : Set G) := by
      rw [← hk]
      exact PartOne.S11d.centralizer_zpow_eq Nat.prime_three hd3 hk3
    set L' := L.map (MulAut.conj h).toMonoidHom with hL'
    have hL'd : L' ∈ thetaComponentsAt 3 d := by
      have h1 := Sec12.KS128NotHJSL.map_conj_mem_thetaComponentsAt Nat.prime_three hLcomp h
      rwa [PartOne.S11d.thetaComponentsAt_congr hCd] at h1
    let eL : L ≃* L' := L.equivMapOfInjective _ (MulAut.conj h).injective
    have hZL : Subgroup.center (lBar L) = ⊥ := Item2113Proof.center_lBar_eq_bot_of_isList218 hL
    have hZL' : Subgroup.center (lBar L') = ⊥ :=
      Item2113Proof.center_eq_bot_of_mulEquiv hZL (Sec14.quotThetaEquiv eL).symm
    by_cases hJL : J = L'
    ·
      have h3 := hJON.1
      rw [hJL, hZL', Subgroup.card_bot] at h3
      norm_num at h3
    ·
      have hAN' : A ≤ Subgroup.normalizer (L' : Set G) :=
        Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe hdA hd1 L' hL'd
      have hy₀ : h * d * h⁻¹ ∈ L' := ⟨d, hdL, rfl⟩
      have hy₀3 : (h * d * h⁻¹) ^ 3 = 1 := by
        rw [conj_pow, hd3, mul_one, mul_inv_cancel]
      have hy₀1 : h * d * h⁻¹ ≠ 1 := fun h1 => hd1 (by
        calc d = h⁻¹ * (h * d * h⁻¹) * h := by group
          _ = 1 := by rw [h1]; group)
      exact false_of_ne_of_maximal hAe hmax hAJ' hJ hL'd hJL hAN' hZL' hy₀ hy₀3 hy₀1

end Main

end CFSG.RankThree.PartTwo.Sec21
