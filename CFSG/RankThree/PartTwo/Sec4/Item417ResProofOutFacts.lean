module

import CFSG.RankThree.PartTwo.Sec4.Item413Setup
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res417

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Lift

variable {X : Type} [Group X] [Finite X]

theorem exists_lift_pow_three {y : X ⧸ aschbacherSolvableCore 3 X} (hy : y ^ 3 = 1) :
    ∃ x : X, (x : X ⧸ aschbacherSolvableCore 3 X) = y ∧ x ^ 3 = 1 := by
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective y
  set N := Nat.card (aschbacherSolvableCore 3 X) with hN
  have hN3 : ¬ 3 ∣ N := three_not_dvd_card_aschbacherSolvableCore
  have hN1 : N ^ 2 % 3 = 1 := by
    have : N % 3 = 1 ∨ N % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.pow_mod, h]
  have hx3 : x₀ ^ 3 ∈ aschbacherSolvableCore 3 X := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hy
  refine ⟨x₀ ^ (N ^ 2), ?_, ?_⟩
  · rw [QuotientGroup.mk_pow, ← Nat.div_add_mod (N ^ 2) 3, pow_add, pow_mul,
      show ((x₀ : X ⧸ aschbacherSolvableCore 3 X) ^ 3) = 1 from hy, one_pow, one_mul, hN1,
      pow_one]
  · have h1 : (⟨x₀ ^ 3, hx3⟩ : aschbacherSolvableCore 3 X) ^ N = 1 := pow_card_eq_one'
    have h2 : (x₀ ^ 3) ^ N = 1 := by
      have := congrArg Subtype.val h1
      simpa using this
    rw [← pow_mul, mul_comm, pow_mul, sq, pow_mul, h2, one_pow]

theorem eq_of_lift_pow_three (hθZ : aschbacherSolvableCore 3 X ≤ Subgroup.center X) {x x' : X}
    (h : (x : X ⧸ aschbacherSolvableCore 3 X) = (x' : X ⧸ aschbacherSolvableCore 3 X))
    (hx : x ^ 3 = 1) (hx' : x' ^ 3 = 1) : x = x' := by
  have ht : x⁻¹ * x' ∈ aschbacherSolvableCore 3 X := QuotientGroup.eq.mp h
  have hc : Commute x (x⁻¹ * x') :=
    Subgroup.mem_center_iff.mp (hθZ ht) x
  have h3 : (x⁻¹ * x') ^ 3 = 1 := by
    have : x' = x * (x⁻¹ * x') := by group
    rw [this, hc.mul_pow, hx, one_mul] at hx'
    exact hx'
  have hord : orderOf (⟨x⁻¹ * x', ht⟩ : aschbacherSolvableCore 3 X) = 1 := by
    have hdvd3 : orderOf (⟨x⁻¹ * x', ht⟩ : aschbacherSolvableCore 3 X) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h3))
    have hdvdN := orderOf_dvd_natCard (⟨x⁻¹ * x', ht⟩ : aschbacherSolvableCore 3 X)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h1 | h1
    · exact h1
    · rw [h1] at hdvdN
      exact absurd hdvdN three_not_dvd_card_aschbacherSolvableCore
  have h1 : x⁻¹ * x' = 1 := by
    have := orderOf_eq_one_iff.mp hord
    exact congrArg Subtype.val this
  calc x = x * (x⁻¹ * x') := by rw [h1, mul_one]
    _ = x' := by group

end Lift

variable {G : Type} [Group G] [Finite G]

theorem mk_conj_eq_of_inner {L : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (hout : ¬ InducesOuterTheta a L) {z : L}
    (hz : (z : L ⧸ aschbacherSolvableCore 3 L) ∈
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) :
    ((L.normalizerMonoidHom ⟨a, ha⟩ z : L) : L ⧸ aschbacherSolvableCore 3 L) =
      (z : L ⧸ aschbacherSolvableCore 3 L) := by
  have hin : thetaQuotMulAut L (compAction L ⟨a, ha⟩) ∈
      (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →*
        MulAut (L ⧸ aschbacherSolvableCore 3 L)).range := by
    by_contra h
    exact hout ⟨ha, h⟩
  obtain ⟨y, hy⟩ := hin
  have h1 := congrArg (fun τ : MulAut (L ⧸ aschbacherSolvableCore 3 L) =>
    τ (z : L ⧸ aschbacherSolvableCore 3 L)) hy
  simp only [MulAut.conj_apply] at h1
  rw [Subgroup.mem_center_iff.mp hz y, mul_inv_cancel_right] at h1
  exact h1.symm

theorem center_thetaQuot_eq_bot {L A : Subgroup G} {c : G} (hL : IsComponent L)
    (hAmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hout : ∀ a ∈ A, ¬ InducesOuterTheta a L)
    (hcL : c ∉ L) : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hθZ := aschbacherSolvableCore_le_center hL.1
  obtain ⟨-, hcomap, -⟩ := CFSG.LocalCores.quasisimple_central_quotient hL.1
    (aschbacherSolvableCore 3 L) hθZ
  by_contra hne
  have hZ3 := Census.isPGroup_center_thetaQuotient L
  have : Nontrivial (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ3
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hne (Subgroup.eq_bot_of_card_eq _ hk)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hk]; exact dvd_pow_self 3 hk0)
  have hy3 : (y : L ⧸ aschbacherSolvableCore 3 L) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hy] at h
    exact congrArg Subtype.val h
  have hy1 : (y : L ⧸ aschbacherSolvableCore 3 L) ≠ 1 := by
    intro h
    have : y = 1 := Subtype.ext h
    rw [this, orderOf_one] at hy
    omega
  obtain ⟨z, hzy, hz3⟩ := exists_lift_pow_three hy3
  have hzZ : z ∈ Subgroup.center L := by
    rw [← hcomap, Subgroup.mem_comap, QuotientGroup.mk'_apply, hzy]
    exact y.2
  have hzmk : (z : L ⧸ aschbacherSolvableCore 3 L) ∈
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
    rw [hzy]
    exact y.2
  have hAz : ∀ a ∈ A, a * (z : G) = (z : G) * a := by
    intro a ha
    have h1 := mk_conj_eq_of_inner (hAL ha) (hout a ha) hzmk
    have hc' : (L.normalizerMonoidHom ⟨a, hAL ha⟩ z : L) ^ 3 = 1 := by
      rw [← map_pow, hz3, map_one]
    have h2 := eq_of_lift_pow_three hθZ h1 hc' hz3
    have h3 : a * (z : G) * a⁻¹ = z := by
      have := congrArg Subtype.val h2
      rw [normalizerMonoidHom_apply_coe] at this
      exact this
    calc a * (z : G) = a * (z : G) * a⁻¹ * a := by group
      _ = z * a := by rw [h3]
  have hzA : (z : G) ∈ A := mem_of_maximal_of_commute hAmax
    (by have := congrArg Subtype.val hz3; simpa using this) hAz
  have hzC : (z : G) ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun l hl =>
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp hzZ ⟨l, hl⟩))
  have hzc : (z : G) ∈ Subgroup.zpowers c := hAc ▸ ⟨hzA, hzC⟩
  have hz1 : (z : G) ≠ 1 := by
    intro h
    apply hy1
    rw [← hzy, show z = 1 from Subtype.ext h, QuotientGroup.mk_one]
  apply hcL
  have hc3 : orderOf c = 3 := by
    obtain ⟨⟨hAe, hA3⟩, -⟩ := hAmax
    have hcA : c ∈ A := (hAc ▸ Subgroup.mem_zpowers c : c ∈ A ⊓ _).1
    refine orderOf_eq_prime (hA3 c hcA) fun h => ?_
    rw [h] at hzc
    obtain ⟨j, hj⟩ := hzc
    exact hz1 (by rw [← hj]; simp)
  have hzo : orderOf (z : G) = 3 := by
    refine orderOf_eq_prime (by simpa using congrArg Subtype.val hz3) hz1
  have hle : Subgroup.zpowers c ≤ Subgroup.zpowers (z : G) := by
    apply le_of_eq
    symm
    exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzc)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hc3, hzo])
  exact (Subgroup.zpowers_le.mpr z.2) (hle (Subgroup.mem_zpowers c))

theorem eq_sup_of_inner {L A : Subgroup G} {c : G} (hL : IsComponent L)
    (hAmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hout : ∀ a ∈ A, ¬ InducesOuterTheta a L)
    (hcL : c ∉ L) : A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
  have hθZ := aschbacherSolvableCore_le_center hL.1
  have hZ := center_thetaQuot_eq_bot hL hAmax hAc hAL hout hcL
  have hcA : c ∈ A := (hAc ▸ Subgroup.mem_zpowers c : c ∈ A ⊓ _).1
  have hAe := hAmax.prop
  refine le_antisymm (fun a ha => ?_) (sup_le (Subgroup.zpowers_le.mpr hcA) inf_le_left)
  have hin : ∀ (b : G) (hb : b ∈ A), ∃ xb : L ⧸ aschbacherSolvableCore 3 L,
      thetaQuotMulAut L (compAction L ⟨b, hAL hb⟩) = MulAut.conj xb := by
    intro b hb
    by_contra h
    push Not at h
    exact hout b hb ⟨hAL hb, fun ⟨xb, hxb⟩ => h xb hxb.symm⟩
  obtain ⟨xa, hxa⟩ := hin a ha
  have hxa3 : xa ^ 3 = 1 := by
    have h1 : MulAut.conj (xa ^ 3) = 1 := by
      rw [map_pow, ← hxa, ← map_pow, ← map_pow]
      have : (⟨a, hAL ha⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow]; exact hAe.2 a ha)
      rw [this, map_one, map_one]
    have h2 : xa ^ 3 ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun τ : MulAut (L ⧸ aschbacherSolvableCore 3 L) => τ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * xa ^ 3 = (xa ^ 3 * g * (xa ^ 3)⁻¹) * xa ^ 3 := by rw [this]
        _ = xa ^ 3 * g := by group
    rw [hZ] at h2
    exact h2
  obtain ⟨x, hxx, hx3⟩ := exists_lift_pow_three hxa3
  have hxA : (x : G) ∈ A := by
    refine mem_of_maximal_of_commute hAmax (by simpa using congrArg Subtype.val hx3) ?_
    intro b hb
    obtain ⟨xb, hxb⟩ := hin b hb
    have hab : xb * xa = xa * xb := by
      have hba : b * a = a * b := congrArg Subtype.val (hAe.1.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
      have hNba : (⟨b, hAL hb⟩ * ⟨a, hAL ha⟩ : Subgroup.normalizer (L : Set G)) =
          ⟨a, hAL ha⟩ * ⟨b, hAL hb⟩ := Subtype.ext hba
      have hcomm : thetaQuotMulAut L (compAction L ⟨b, hAL hb⟩) *
          thetaQuotMulAut L (compAction L ⟨a, hAL ha⟩) =
          thetaQuotMulAut L (compAction L ⟨a, hAL ha⟩) *
          thetaQuotMulAut L (compAction L ⟨b, hAL hb⟩) := by
        rw [← map_mul, ← map_mul, hNba, map_mul, map_mul]
      rw [hxa, hxb, ← map_mul, ← map_mul] at hcomm
      set w := (xa * xb)⁻¹ * (xb * xa) with hwdef
      have hw : ∀ g, w * g * w⁻¹ = g := by
        intro g
        have h := congrArg (fun τ : MulAut (L ⧸ aschbacherSolvableCore 3 L) => τ g) hcomm
        simp only [MulAut.conj_apply] at h
        calc w * g * w⁻¹ = (xa * xb)⁻¹ * ((xb * xa) * g * (xb * xa)⁻¹) * (xa * xb) := by
              rw [hwdef]; group
          _ = (xa * xb)⁻¹ * ((xa * xb) * g * (xa * xb)⁻¹) * (xa * xb) := by rw [h]
          _ = g := by group
      have hwZ : w ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) :=
        Subgroup.mem_center_iff.mpr fun g => by
          calc g * w = (w * g * w⁻¹) * w := by rw [hw g]
            _ = w * g := by group
      rw [hZ, Subgroup.mem_bot, hwdef, inv_mul_eq_one] at hwZ
      exact hwZ.symm
    have h1 : ((L.normalizerMonoidHom ⟨b, hAL hb⟩ x : L) : L ⧸ aschbacherSolvableCore 3 L) =
        (x : L ⧸ aschbacherSolvableCore 3 L) := by
      have := congrArg (fun τ : MulAut (L ⧸ aschbacherSolvableCore 3 L) =>
        τ (x : L ⧸ aschbacherSolvableCore 3 L)) hxb
      simp only [MulAut.conj_apply] at this
      rw [← thetaQuotMulAut_mk]
      change thetaQuotMulAut L (compAction L ⟨b, hAL hb⟩) (x : L ⧸ _) = _
      rw [this, hxx, hab, mul_inv_cancel_right]
    have hc' : (L.normalizerMonoidHom ⟨b, hAL hb⟩ x : L) ^ 3 = 1 := by
      rw [← map_pow, hx3, map_one]
    have h2 := eq_of_lift_pow_three hθZ h1 hc' hx3
    have h3 : b * (x : G) * b⁻¹ = x := by
      have := congrArg Subtype.val h2
      rw [normalizerMonoidHom_apply_coe] at this
      exact this
    calc b * (x : G) = b * (x : G) * b⁻¹ * b := by group
      _ = x * b := by rw [h3]
  have hxaC : (x : G)⁻¹ * a ∈ Subgroup.centralizer (L : Set G) := by
    have hN : (x : G)⁻¹ * a ∈ Subgroup.normalizer (L : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer x.2)) (hAL ha)
    have htriv : thetaQuotMulAut L (compAction L ⟨(x : G)⁻¹ * a, hN⟩) = 1 := by
      have : (⟨(x : G)⁻¹ * a, hN⟩ : Subgroup.normalizer (L : Set G)) =
          (⟨(x : G), Subgroup.le_normalizer x.2⟩)⁻¹ * ⟨a, hAL ha⟩ := rfl
      rw [this, map_mul, map_mul, hxa, map_inv, map_inv]
      ext g
      induction g using QuotientGroup.induction_on with
      | H l =>
        simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply]
        rw [← hxx, MulAut.inv_def, MulEquiv.symm_apply_eq, thetaQuotMulAut_mk]
        rfl
    have h1 := eq_one_of_thetaQuotMulAut_eq_one hL.1 htriv
    refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
    have h2 := congrArg (fun σ : MulAut L => ((σ ⟨l, hl⟩ : L) : G)) h1
    simp only [MulAut.one_apply] at h2
    change (x : G)⁻¹ * a * l * ((x : G)⁻¹ * a)⁻¹ = l at h2
    calc l * ((x : G)⁻¹ * a) = (x : G)⁻¹ * a * l * ((x : G)⁻¹ * a)⁻¹ * ((x : G)⁻¹ * a) := by
          rw [h2]
      _ = (x : G)⁻¹ * a * l := by group
  have hxac : (x : G)⁻¹ * a ∈ Subgroup.zpowers c :=
    hAc ▸ ⟨A.mul_mem (A.inv_mem hxA) ha, hxaC⟩
  have : a = (x : G) * ((x : G)⁻¹ * a) := by group
  rw [this, sup_comm]
  exact Subgroup.mul_mem_sup ⟨hxA, x.2⟩ hxac

end CFSG.RankThree.PartTwo.Sec4.Res417
