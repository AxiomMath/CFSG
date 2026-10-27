module

public import CFSG.LocalAnalysis.StandardType.GGLieSU3FixedOn
public import CFSG.LocalAnalysis.StandardType.GGLieSU3FixedCore
public import CFSG.LocalAnalysis.StandardType.GGLieSU3FixedLift
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestUnitaryCenter
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRestInner
import CFSG.LocalAnalysis.StandardType.GGL45FixA2Centre
import CFSG.Assembly.Subnormal
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallJ
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTGlobal
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearEnd
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaGlobal
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryPower
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUEven
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerSp
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Transfer
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowUniqueStep
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapUnique
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggLieSU3Fixed_of_datum
    {X : Type} [Group X] [Finite X] (hX : commutator X = ⊤)
    {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X} (hl : GGAutLocal A δ J)
    (hZJ : Subgroup.center ↥J ≠ ⊥) (hJ3 : Nat.card (Subgroup.center ↥J) ∣ 3)
    {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (θ : X ⧸ Subgroup.center X ≃* LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
    (hInn : GGInducedInn A θ (LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n))) (LargeEvenGUSet (Fin 4) K (2 ^ n)))) :
    ¬ GGAutsFixedInCenter A J := by
  intro hfixed
  have hodd : Odd (2 ^ n + 1) := by
    rw [Nat.odd_add_one, Nat.not_odd_iff_even]
    exact Nat.even_pow.2 ⟨even_two, by omega⟩
  have hcop4 : Nat.Coprime 4 (2 ^ n + 1) :=
    Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hodd)
  have hcop : (2 ^ n + 1).Coprime 4 := hcop4.symm
  have hcenterSU : Subgroup.center ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n)) = ⊥ :=
    CFSG.SeitzReduction.SymplecticPilot.center_statedSU_eq_bot_of_coprime hK hn (by norm_num) hcop4
  let SU := ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))
  letI : Group SU := inferInstance
  have hcenter : Subgroup.center SU = ⊥ := hcenterSU
  let e : SU ≃* LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)) :=
    MulEquiv.ofBijective (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
      ⟨ggLieSU3Fixed_projMk_injective (K := K) (n := n) hK,
        QuotientGroup.mk'_surjective _⟩
  let ψ : X →* SU :=
    e.symm.toMonoidHom.comp (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)))
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨z, hz⟩ := e.symm.surjective y
    obtain ⟨w, hw⟩ := θ.surjective z
    obtain ⟨v, hv⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) w
    refine ⟨v, ?_⟩
    show e.symm (θ ((QuotientGroup.mk' (Subgroup.center X)) v)) = y
    rw [hv, hw, hz]
  have hkerψ : ψ.ker = Subgroup.center X := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : e.symm (θ ((QuotientGroup.mk' (Subgroup.center X)) x)) = 1 := by
        simpa [ψ] using hx
      have h2 : θ ((QuotientGroup.mk' (Subgroup.center X)) x) = 1 :=
        e.symm.injective (by simpa using h1)
      have h3 : (QuotientGroup.mk' (Subgroup.center X)) x = 1 :=
        θ.injective (by simpa using h2)
      have h4 : x ∈ (QuotientGroup.mk' (Subgroup.center X)).ker := by
        rw [MonoidHom.mem_ker]
        exact h3
      rwa [QuotientGroup.ker_mk'] at h4
    · intro hx
      have h1 : x ∈ (QuotientGroup.mk' (Subgroup.center X)).ker := by
        rwa [QuotientGroup.ker_mk']
      rw [MonoidHom.mem_ker] at h1
      change e.symm (θ ((QuotientGroup.mk' (Subgroup.center X)) x)) = 1
      rw [h1, map_one, map_one]
  have hS1 : ¬ 3 ∣ Nat.card (Subgroup.center X) := by
    have hcp := CFSG.StandardType.StdSubRestU.ggCenterPrime_unitary (K := K) (n := n) (d := 4) (p := 3)
      hK hn (by norm_num) (by norm_num) Nat.prime_three (by norm_num) (by norm_num)
    refine hcp X (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)))
      (θ.surjective.comp (QuotientGroup.mk'_surjective _)) ?_ hX
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : (QuotientGroup.mk' (Subgroup.center X)) x = 1 := by
      apply θ.injective
      simpa using hx
    have hx'' : x ∈ (QuotientGroup.mk' (Subgroup.center X)).ker := by
      rw [MonoidHom.mem_ker]
      exact hx'
    rwa [QuotientGroup.ker_mk'] at hx''
  have hI : LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
      (LargeEvenGUSet (Fin 4) K (2 ^ n)) ⊆
      LargeEvenInnSet (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n))) :=
    CFSG.StandardType.TableB.matConjImage_gu_subset_inn (d := 4) (n := n) hK hcop
  have hS2 : ∀ a ∈ A, ∃ s : SU, ∀ x : X, ψ (a x) = s * ψ x * s⁻¹ := by
    intro a ha
    obtain ⟨s, hs⟩ := hI (hInn a ha)
    refine ⟨e.symm s, ?_⟩
    intro x
    have hstep : θ (((a x : X)) : X ⧸ Subgroup.center X) =
        s * θ ((x : X) : X ⧸ Subgroup.center X) * s⁻¹ := by
      rw [← ggInducedAut_apply θ a x, ← hs, MulAut.conj_apply]
    change e.symm (θ (((a x : X)) : X ⧸ Subgroup.center X)) =
      e.symm s * e.symm (θ ((x : X) : X ⧸ Subgroup.center X)) * (e.symm s)⁻¹
    rw [hstep, map_mul, map_mul, map_inv]
  let E : Set SU := {s | ∃ a ∈ A, ∀ x : X, ψ (a x) = s * ψ x * s⁻¹}
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro s hs t ht
    obtain ⟨a, ha, hsa⟩ := hs
    obtain ⟨b, hb, htb⟩ := ht
    have hab : a * b = b * a := by
      have h := (isMulCommutative_iff.mp hl.1.1) ⟨a, ha⟩ ⟨b, hb⟩
      simpa using congrArg Subtype.val h
    have hkey : ∀ y : SU, (s * t) * y * (s * t)⁻¹ = (t * s) * y * (t * s)⁻¹ := by
      intro y
      obtain ⟨x, rfl⟩ := hψsurj y
      calc (s * t) * ψ x * (s * t)⁻¹
          = s * (t * ψ x * t⁻¹) * s⁻¹ := by group
        _ = s * ψ (b x) * s⁻¹ := by rw [← htb x]
        _ = ψ (a (b x)) := (hsa (b x)).symm
        _ = ψ (b (a x)) := by
              rw [show a (b x) = b (a x) from congrArg (fun f : MulAut X => f x) hab]
        _ = t * ψ (a x) * t⁻¹ := htb (a x)
        _ = t * (s * ψ x * s⁻¹) * t⁻¹ := by rw [hsa x]
        _ = (t * s) * ψ x * (t * s)⁻¹ := by group
    have hcentral : (t * s)⁻¹ * (s * t) ∈ Subgroup.center SU := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h3 : (s * t) * y = (t * s) * y * (t * s)⁻¹ * (s * t) := by
        have h := congrArg (fun z => z * (s * t)) (hkey y)
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
      have hmain : (t * s)⁻¹ * (s * t) * y = y * ((t * s)⁻¹ * (s * t)) := by
        calc (t * s)⁻¹ * (s * t) * y = (t * s)⁻¹ * ((s * t) * y) := by group
          _ = (t * s)⁻¹ * ((t * s) * y * (t * s)⁻¹ * (s * t)) := by rw [h3]
          _ = y * ((t * s)⁻¹ * (s * t)) := by group
      exact hmain.symm
    have hu1 : (t * s)⁻¹ * (s * t) = 1 := by
      rw [hcenter] at hcentral
      simpa using hcentral
    have hst : s * t = t * s := by
      have h := congrArg (fun z => (t * s) * z) hu1
      rw [mul_one, mul_inv_cancel_left] at h
      exact h
    exact hst
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := by
    intro s hs
    obtain ⟨a, ha, hsa⟩ := hs
    have ha3 : a ^ 3 = 1 := hl.1.2 a ha
    have hcentral : s ^ 3 ∈ Subgroup.center SU := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := hψsurj y
      have hiter : ψ ((a ^ 3) x) = s ^ 3 * ψ x * (s ^ 3)⁻¹ := by
        calc ψ ((a ^ 3) x) = ψ (a (a (a x))) := by
              rw [pow_three, MulAut.mul_apply, MulAut.mul_apply]
          _ = s * ψ (a (a x)) * s⁻¹ := hsa (a (a x))
          _ = s * (s * ψ (a x) * s⁻¹) * s⁻¹ := by rw [hsa (a x)]
          _ = s * (s * (s * ψ x * s⁻¹) * s⁻¹) * s⁻¹ := by rw [hsa x]
          _ = s ^ 3 * ψ x * (s ^ 3)⁻¹ := by rw [pow_three]; group
      have hxx : ψ ((a ^ 3) x) = ψ x := by rw [ha3, MulAut.one_apply]
      rw [hxx] at hiter
      have hcomm3 : ψ x * s ^ 3 = s ^ 3 * ψ x := by
        conv_lhs => rw [hiter]
        rw [pow_three]
        group
      exact hcomm3
    rw [hcenter] at hcentral
    simpa using hcentral
  obtain ⟨d, hd⟩ := hS2 δ hl.2.1
  have hdE : d ∈ E := ⟨δ, hl.2.1, hd⟩
  have hd1 : d ≠ 1 := by
    intro hd1
    have hgg : ggInducedAut θ δ = 1 := by
      ext q
      obtain ⟨y, rfl⟩ := θ.surjective q
      obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) y
      rw [← hx]
      show ggInducedAut θ δ (θ ((x : X) : X ⧸ Subgroup.center X)) =
        θ ((x : X) : X ⧸ Subgroup.center X)
      rw [ggInducedAut_apply]
      have hx' : θ (((δ x : X)) : X ⧸ Subgroup.center X) =
          θ ((x : X) : X ⧸ Subgroup.center X) := by
        apply e.symm.injective
        change ψ (δ x) = ψ x
        rw [hd x, hd1]
        group
      exact hx'
    exact hl.2.2.1 (ggInducedAut_injective_of_perfect hX θ (by rw [hgg, map_one]))
  have hS4 : (ggAutFixedSubgroup δ).map ψ = Subgroup.centralizer ({d} : Set SU) := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := hd x
      rw [show δ x = x from hx] at h
      conv_lhs => rw [h]
      group
    · intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hy
      obtain ⟨x, rfl⟩ := hψsurj y
      have hconj : d * ψ x * d⁻¹ = ψ x := by
        rw [← hy, mul_assoc, mul_inv_cancel, mul_one]
      have hfixδ : ψ (δ x) = ψ x := by rw [hd x, hconj]
      have hfix : ∀ φ ∈ Subgroup.zpowers δ, ψ (φ x) = ψ x := by
        intro φ hφ
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hφ
        have hδ3z : δ ^ (3 : ℤ) = 1 := by
          rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
          exact hl.1.2 δ hl.2.1
        rw [← hk, zpow_eq_zpow_emod k hδ3z]
        obtain h | h | h : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
        · rw [h, zpow_zero, MulAut.one_apply]
        · rw [h, zpow_one]
          exact hfixδ
        · rw [h]
          have h2 : (δ ^ (2 : ℤ)) x = δ (δ x) := by
            rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast,
              show (2 : ℕ) = 1 + 1 by norm_num, pow_add, pow_one, MulAut.mul_apply]
          rw [h2, hd (δ x), hfixδ, hconj]
      have hF : IsPGroup 3 (Subgroup.zpowers δ) := by
        haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        refine IsPGroup.of_card (n := 1) ?_
        rw [Nat.card_zpowers]
        have hdvd : orderOf δ ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr (hl.1.2 δ hl.2.1)
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
        · exact absurd (orderOf_eq_one_iff.mp h1) hl.2.2.1
        · rw [h3, pow_one]
      have hFker : ∀ φ ∈ Subgroup.zpowers δ, ∀ c ∈ ψ.ker, φ c ∈ ψ.ker := by
        intro φ hφ c hc
        rw [hkerψ] at hc ⊢
        rw [Subgroup.mem_center_iff] at hc ⊢
        intro w
        calc w * φ c = φ ((φ⁻¹) w) * φ c := by simp
          _ = φ ((φ⁻¹) w * c) := by rw [map_mul]
          _ = φ (c * (φ⁻¹) w) := by rw [hc]
          _ = φ c * φ ((φ⁻¹) w) := by rw [map_mul]
          _ = φ c * w := by simp
      obtain ⟨j, -, hjψ, hjfix⟩ :=
        ggLieSU3Fixed_exists_fixed_lift (p := 3) ψ (by rw [hkerψ]; exact hS1)
          (Subgroup.zpowers δ) hF hFker ⊤ (fun _ _ j _ => trivial) trivial hfix
      exact ⟨j, (mem_ggAutFixedSubgroup δ j).mpr (hjfix δ (Subgroup.mem_zpowers δ)), hjψ⟩
  have hZne1 : Nat.card (Subgroup.center ↥J) ≠ 1 := by
    intro h1
    exact hZJ (Subgroup.card_eq_one.mp h1)
  have hZcard : Nat.card (Subgroup.center ↥J) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hJ3 with h | h
    · exact absurd h hZne1
    · exact h
  obtain ⟨z₀, hz₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := Subgroup.center ↥J)).mp hZJ
  have hz₀pow : z₀ ^ 3 = 1 := by
    rw [← hZcard]
    exact pow_card_eq_one'
  let z : X := z₀.1.1
  have hzJ : z ∈ J := z₀.1.2
  have hzc : ∀ j ∈ J, z * j = j * z := by
    intro j hj
    have h : (⟨j, hj⟩ : ↥J) * z₀.1 = z₀.1 * ⟨j, hj⟩ :=
      Subgroup.mem_center_iff.mp z₀.2 ⟨j, hj⟩
    exact (congrArg Subtype.val h).symm
  have hz3 : z ^ 3 = 1 := by
    have h := congrArg (fun w : ↥(Subgroup.center ↥J) => w.1) hz₀pow
    have h' := congrArg (fun w : ↥J => (w : X)) h
    simpa [z, Subgroup.coe_pow] using h'
  have hz1 : z ≠ 1 := by
    intro h
    apply hz₀1
    apply Subtype.ext
    apply Subtype.ext
    simpa [z] using h
  have hzfix : ∀ a ∈ A, a z = z :=
    ggLieSU3Fixed_fixes_center A (fun a ha => hl.1.2 a ha) J hl.2.2.2.2 hJ3 hzJ hzc
  have hzJh : ψ z ∈ J.map ψ := Subgroup.mem_map.mpr ⟨z, hzJ, rfl⟩
  have hzJhc : ∀ u ∈ J.map ψ, ψ z * u = u * ψ z := by
    intro u hu
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hu
    rw [← map_mul, ← map_mul, hzc j hj]
  have hzEc : ∀ u ∈ E, ψ z * u = u * ψ z := by
    intro u hu
    obtain ⟨a, ha, hua⟩ := hu
    have h := hua z
    rw [hzfix a ha] at h
    conv_lhs => rw [h]
    group
  have hz3' : (ψ z) ^ 3 = 1 := by rw [← map_pow, hz3, map_one]
  have hz1' : ψ z ≠ 1 := by
    intro h
    have hzker : z ∈ ψ.ker := MonoidHom.mem_ker.mpr h
    rw [hkerψ] at hzker
    have horder : orderOf z = 3 := by
      have hdvd : orderOf z ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hz3
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) hz1
      · exact h3
    have h3dvd : 3 ∣ Nat.card (Subgroup.center X) := by
      have h := Subgroup.orderOf_dvd_natCard (Subgroup.center X) hzker
      rwa [horder] at h
    exact hS1 h3dvd
  have hJsub : IsSubnormal (J.map ψ) (Subgroup.centralizer ({d} : Set SU)) := by
    have h := CFSG.Assembly.IsSubnormal.map ψ hl.2.2.2.1.2.1
    rwa [hS4] at h
  have hJperf : ⁅J.map ψ, J.map ψ⁆ = J.map ψ := by
    have hperf : commutator ↥J = ⊤ := hl.2.2.2.1.2.2.1
    have hJJ : ⁅J, J⁆ = J := by
      have h := Subgroup.map_subtype_commutator J
      rw [hperf, Subgroup.map_top, Subgroup.range_subtype] at h
      exact h.symm
    have h2 := Subgroup.map_commutator J J ψ
    rw [hJJ] at h2
    exact h2.symm
  obtain ⟨t, htJh, htE, u, huJh, htu⟩ :=
    ggLieSU3Fixed_core hK hn E hEcomm hE3 hdE hd1 (J.map ψ) hJsub hJperf
      hzJh hzJhc hz3' hz1' hzEc
  obtain ⟨x, hxJ, hxψ⟩ := Subgroup.mem_map.mp htJh
  have hfixA : ∀ a ∈ A, ψ (a x) = ψ x := by
    intro a ha
    obtain ⟨s, hs⟩ := hS2 a ha
    have hsE : s ∈ E := ⟨a, ha, hs⟩
    have h1 : s * t = t * s := (htE s hsE).symm
    rw [hs x, hxψ, h1, mul_assoc, mul_inv_cancel, mul_one]
  have hApg : IsPGroup 3 A := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [IsPGroup.iff_orderOf]
    intro φ
    have hdvd : orderOf φ ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr (by
      apply Subtype.ext
      simpa using hl.1.2 φ.1 φ.2)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [h3, pow_one]⟩
  have hFkerA : ∀ φ ∈ A, ∀ c ∈ ψ.ker, φ c ∈ ψ.ker := by
    intro φ hφ c hc
    rw [hkerψ] at hc ⊢
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro w
    calc w * φ c = φ ((φ⁻¹) w) * φ c := by simp
      _ = φ ((φ⁻¹) w * c) := by rw [map_mul]
      _ = φ (c * (φ⁻¹) w) := by rw [hc]
      _ = φ c * φ ((φ⁻¹) w) := by rw [map_mul]
      _ = φ c * w := by simp
  obtain ⟨j, hjJ, hjψ, hjfix⟩ :=
    ggLieSU3Fixed_exists_fixed_lift (p := 3) ψ (by rw [hkerψ]; exact hS1)
      A hApg hFkerA J hl.2.2.2.2 hxJ hfixA
  have hjcenter : (⟨j, hjJ⟩ : ↥J) ∉ Subgroup.center ↥J := by
    intro hjc
    have hcomm : ψ j * u = u * ψ j := by
      obtain ⟨k, hkJ, hku⟩ := Subgroup.mem_map.mp huJh
      have hjk : j * k = k * j := by
        have h := Subgroup.mem_center_iff.mp hjc ⟨k, hkJ⟩
        exact (congrArg Subtype.val h).symm
      rw [← hku, ← map_mul, ← map_mul, hjk]
    exact htu (by rw [← hxψ, ← hjψ]; exact hcomm)
  exact hjcenter (hfixed ⟨j, hjJ⟩ (fun a ha => hjfix a ha))

theorem ggLieSU3FixedInputOn_suFour :
    GGLieSU3FixedInputOn GGLabelSUFour := by
  intro X _ _ hX A δ J hl hZ hm hJ
  obtain ⟨-, lab, hlab, hraw⟩ := hm
  have hSfour : GGLabelSUFour lab := by
    have hrawc := hraw
    obtain ⟨R, _instR, I, F, hQ⟩ := largeEvenRawDatum_exists hrawc
    obtain ⟨-, -, θ, hP⟩ := hQ
    exact hP.2.1
  have hJperf : Group.IsPerfect J := ⟨hJ.1⟩
  have hJ3 : Nat.card (Subgroup.center ↥J) ∣ 3 := by
    obtain ⟨-, lab', hlab', hraw'⟩ := hJ
    obtain ⟨tag', rank', nn'⟩ := lab'
    have hlabprop : GGLabelA2 ⟨tag', rank', nn'⟩ ∧ tag' = .twA := by
      have hrawc := hraw'
      obtain ⟨R', _instR', I', F', hQ'⟩ := largeEvenRawDatum_exists hrawc
      obtain ⟨-, -, θ', hP'⟩ := hQ'
      exact hP'
    obtain ⟨hA2, htag'⟩ := hlabprop
    have hrank' : rank' = 2 := hA2.1
    subst htag'
    subst hrank'
    simp only [LargeEvenRawDatum] at hraw'
    obtain ⟨K', _instK', _instFinK', hK', hQK'⟩ := hraw'
    obtain ⟨-, -, θ', _hP'⟩ := hQK'
    exact gffa2_card_center_dvd_unitary hJperf hA2.2.1 hK' θ'
  obtain ⟨tag, rank, nn⟩ := lab
  rcases hSfour with ⟨htag, hrank⟩ | ⟨htag, hrank⟩
  · subst htag
    subst hrank
    simp only [LargeEvenRawDatum] at hraw
    obtain ⟨K, _instK, _instFinK, hK, hQK⟩ := hraw
    obtain ⟨-, -, θ, hP⟩ := hQK
    exact ggLieSU3Fixed_of_datum (K := K) (n := nn) hX hl hZ hJ3 hK hlab.1 θ hP.2.2
  · subst htag
    subst hrank
    simp only [LargeEvenRawDatum] at hraw
    obtain ⟨K, _instK, _instFinK, hK, hQK⟩ := hraw
    obtain ⟨-, -, θ, hP⟩ := hQK
    exact ggLieSU3Fixed_of_datum (K := K) (n := nn) hX hl hZ hJ3 hK hlab.1 θ hP.2.2

end CFSG.StandardType
