module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab

import CFSG.LocalAnalysis.StandardType.GGLieSU3FixedLift
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36L4Twin
import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EForms
import CFSG.LocalAnalysis.ComponentClassification.OddSelectorInner
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLAllInvolutions
import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggLieSU3Fixed_of_lift {X : Type} [Group X] [Finite X] (hX : commutator X = ⊤)
    {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X} (hl : GGAutLocal A δ J)
    (hZJ : Subgroup.center ↥J ≠ ⊥) (hJ3 : Nat.card (Subgroup.center ↥J) ∣ 3)
    {G : Type} [Group G] (hG : Subgroup.center G = ⊥) (ψ : X →* G)
    (hψ : Function.Surjective ψ) (hker : ψ.ker = Subgroup.center X)
    (h3 : ¬ 3 ∣ Nat.card (Subgroup.center X))
    (hinn : ∀ a ∈ A, ∃ s : G, ∀ x : X, ψ (a x) = s * ψ x * s⁻¹)
    (hcore : ∀ E : Set G, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ 3 = 1) →
      ∀ d ∈ E, d ≠ 1 → ∀ Jh : Subgroup G,
        CFSG.Assembly.IsComponentOf Jh (Subgroup.centralizer ({d} : Set G)) →
        ∀ z ∈ Jh, (∀ j ∈ Jh, z * j = j * z) → z ^ 3 = 1 → z ≠ 1 → (∀ x ∈ E, z * x = x * z) →
          ∃ t ∈ Jh, (∀ x ∈ E, t * x = x * t) ∧ ∃ u ∈ Jh, t * u ≠ u * t) :
    ¬ GGAutsFixedInCenter A J := by
  intro hfixed
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let E : Set G := {s | ∃ a ∈ A, ∀ x : X, ψ (a x) = s * ψ x * s⁻¹}
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro s hs t ht
    obtain ⟨a, ha, hsa⟩ := hs
    obtain ⟨b, hb, htb⟩ := ht
    have hab : a * b = b * a := by
      have h := (isMulCommutative_iff.mp hl.1.1) ⟨a, ha⟩ ⟨b, hb⟩
      simpa using congrArg Subtype.val h
    have hkey : ∀ y : G, (s * t) * y * (s * t)⁻¹ = (t * s) * y * (t * s)⁻¹ := by
      intro y
      obtain ⟨x, rfl⟩ := hψ y
      calc (s * t) * ψ x * (s * t)⁻¹
          = s * (t * ψ x * t⁻¹) * s⁻¹ := by group
        _ = s * ψ (b x) * s⁻¹ := by rw [← htb x]
        _ = ψ (a (b x)) := (hsa (b x)).symm
        _ = ψ (b (a x)) := by
              rw [show a (b x) = b (a x) from congrArg (fun f : MulAut X => f x) hab]
        _ = t * ψ (a x) * t⁻¹ := htb (a x)
        _ = t * (s * ψ x * s⁻¹) * t⁻¹ := by rw [hsa x]
        _ = (t * s) * ψ x * (t * s)⁻¹ := by group
    have hcentral : (t * s)⁻¹ * (s * t) ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h3' : (s * t) * y = (t * s) * y * (t * s)⁻¹ * (s * t) := by
        have h := congrArg (fun z => z * (s * t)) (hkey y)
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
      have hmain : (t * s)⁻¹ * (s * t) * y = y * ((t * s)⁻¹ * (s * t)) := by
        calc (t * s)⁻¹ * (s * t) * y = (t * s)⁻¹ * ((s * t) * y) := by group
          _ = (t * s)⁻¹ * ((t * s) * y * (t * s)⁻¹ * (s * t)) := by rw [h3']
          _ = y * ((t * s)⁻¹ * (s * t)) := by group
      exact hmain.symm
    have hu1 : (t * s)⁻¹ * (s * t) = 1 := by
      rw [hG] at hcentral
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
    have hcentral : s ^ 3 ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := hψ y
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
    rw [hG] at hcentral
    simpa using hcentral
  obtain ⟨d, hd⟩ := hinn δ hl.2.1
  have hdE : d ∈ E := ⟨δ, hl.2.1, hd⟩
  have hd1 : d ≠ 1 := by
    intro hd1
    have hg1 : ggInducedAut (MulEquiv.refl (X ⧸ Subgroup.center X)) δ = 1 := by
      ext q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      change ggInducedAut (MulEquiv.refl (X ⧸ Subgroup.center X)) δ
        ((MulEquiv.refl (X ⧸ Subgroup.center X)) (x : X ⧸ Subgroup.center X)) =
        (1 : MulAut (X ⧸ Subgroup.center X)) ↑x
      rw [ggInducedAut_apply, MulAut.one_apply, MulEquiv.refl_apply]
      have hψeq : ψ (δ x) = ψ x := by
        rw [hd x, hd1]
        group
      have hmem : (δ x)⁻¹ * x ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hψeq, inv_mul_cancel]
      rw [hker] at hmem
      exact QuotientGroup.eq.mpr hmem
    have hδ1 : δ = 1 :=
      ggInducedAut_injective_of_perfect hX (MulEquiv.refl (X ⧸ Subgroup.center X))
        (by rw [hg1, map_one])
    exact hl.2.2.1 hδ1
  have hS4 : (ggAutFixedSubgroup δ).map ψ = Subgroup.centralizer ({d} : Set G) := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := hd x
      rw [show δ x = x from hx] at h
      conv_lhs => rw [h]
      group
    · intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hy
      obtain ⟨x, rfl⟩ := hψ y
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
        refine IsPGroup.of_card (n := 1) ?_
        rw [Nat.card_zpowers]
        have hdvd : orderOf δ ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr (hl.1.2 δ hl.2.1)
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3'
        · exact absurd (orderOf_eq_one_iff.mp h1) hl.2.2.1
        · rw [h3', pow_one]
      have hFker : ∀ φ ∈ Subgroup.zpowers δ, ∀ c ∈ ψ.ker, φ c ∈ ψ.ker := by
        intro φ hφ c hc
        rw [hker] at hc ⊢
        rw [Subgroup.mem_center_iff] at hc ⊢
        intro w
        calc w * φ c = φ ((φ⁻¹) w) * φ c := by simp
          _ = φ ((φ⁻¹) w * c) := by rw [map_mul]
          _ = φ (c * (φ⁻¹) w) := by rw [hc]
          _ = φ c * φ ((φ⁻¹) w) := by rw [map_mul]
          _ = φ c * w := by simp
      obtain ⟨j, -, hjψ, hjfix⟩ :=
        ggLieSU3Fixed_exists_fixed_lift (p := 3) ψ (by rw [hker]; exact h3)
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
    rw [hker] at hzker
    have horder : orderOf z = 3 := by
      have hdvd : orderOf z ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hz3
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3'
      · exact absurd (orderOf_eq_one_iff.mp h1) hz1
      · exact h3'
    have h3dvd : 3 ∣ Nat.card (Subgroup.center X) := by
      have h := Subgroup.orderOf_dvd_natCard (Subgroup.center X) hzker
      rwa [horder] at h
    exact h3 h3dvd
  have hker_le : ψ.ker ≤ Subgroup.center X := hker ▸ le_rfl
  have hJcomp : CFSG.Assembly.IsComponentOf (J.map ψ)
      (Subgroup.centralizer ({d} : Set G)) := by
    have h := CFSG.ComponentClassification.HarrisLit.N36.isComponentOf_map_of_ker_le_center ψ
      hker_le hl.2.2.2.1
    rwa [hS4] at h
  obtain ⟨t, htJh, htE, u, huJh, htu⟩ :=
    hcore E hEcomm hE3 d hdE hd1 (J.map ψ) hJcomp (ψ z)
      hzJh hzJhc hz3' hz1' hzEc
  obtain ⟨x, hxJ, hxψ⟩ := Subgroup.mem_map.mp htJh
  have hfixA : ∀ a ∈ A, ψ (a x) = ψ x := by
    intro a ha
    obtain ⟨s, hs⟩ := hinn a ha
    have hsE : s ∈ E := ⟨a, ha, hs⟩
    have h1 : s * t = t * s := (htE s hsE).symm
    rw [hs x, hxψ, h1, mul_assoc, mul_inv_cancel, mul_one]
  have hApg : IsPGroup 3 A := by
    rw [IsPGroup.iff_orderOf]
    intro φ
    have hdvd : orderOf φ ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr (by
      apply Subtype.ext
      simpa using hl.1.2 φ.1 φ.2)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3'
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [h3', pow_one]⟩
  have hFkerA : ∀ φ ∈ A, ∀ c ∈ ψ.ker, φ c ∈ ψ.ker := by
    intro φ hφ c hc
    rw [hker] at hc ⊢
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro w
    calc w * φ c = φ ((φ⁻¹) w) * φ c := by simp
      _ = φ ((φ⁻¹) w * c) := by rw [map_mul]
      _ = φ (c * (φ⁻¹) w) := by rw [hc]
      _ = φ c * φ ((φ⁻¹) w) := by rw [map_mul]
      _ = φ c * w := by simp
  obtain ⟨j, hjJ, hjψ, hjfix⟩ :=
    ggLieSU3Fixed_exists_fixed_lift (p := 3) ψ (by rw [hker]; exact h3)
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

end CFSG.StandardType
