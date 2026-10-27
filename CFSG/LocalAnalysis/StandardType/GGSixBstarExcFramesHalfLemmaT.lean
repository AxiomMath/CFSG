module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC3ConjCore
import TauCeti.GroupTheory.ExponentPrime

public section

namespace CFSG.StandardType.ExcFramesHalf

open scoped MatrixGroups
open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE TableBExc.E6Three
open CFSG.HardMathSupport.Timmesfeld.CrossChar (pairRefl)

variable {τ : Tag} {K : Type} [Field K]

theorem exists_cube_of_weylTuple_orbit
    {ρ : SL(3, K) →* ModGL τ K} {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ} (hfr : IsA2Frame ρ σ)
    {g : WeylGroup τ} {u μ : Fin τ.rank → ℤ}
    (horb : g⁻¹ • u + g⁻¹ • (g⁻¹ • u) + u + (2 • σ 0 1 + σ 1 2) = μ + μ + μ)
    {b : Fin τ.rank → Kˣ} (hb : weylTuple g b * weylTuple g (weylTuple g b) * b = 1) :
    ∃ z : Kˣ, z ^ 3 * (rootChar b (σ 0 0) * rootChar b (σ 1 0) * rootChar b (σ 2 0)) = 1 := by
  obtain ⟨h0, h1, h2⟩ := SmallExc.frame_col_zero hfr
  have hmul : ∀ (a a' : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ),
      rootChar (a * a') v = rootChar a v * rootChar a' v := fun a a' v => by
    simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]
  have hone : ∀ v : Fin τ.rank → ℤ, rootChar (1 : Fin τ.rank → Kˣ) v = 1 :=
    fun v => by simp [rootChar]
  have horb' := congrArg (fun c => rootChar c u) hb
  simp only [hmul, rootChar_weylTuple, hone] at horb'
  have hv : μ + μ + μ + σ 0 0 + σ 1 0 + σ 2 0 = g⁻¹ • u + g⁻¹ • (g⁻¹ • u) + u := by
    rw [← horb, h0, h1, h2]
    abel
  refine ⟨rootChar b μ, ?_⟩
  have e : rootChar b μ ^ 3 * (rootChar b (σ 0 0) * rootChar b (σ 1 0) * rootChar b (σ 2 0)) =
      rootChar b (μ + μ + μ + σ 0 0 + σ 1 0 + σ 2 0) := by
    simp only [rootChar_add, pow_three, mul_assoc]
  rw [e, hv, rootChar_add, rootChar_add]
  exact horb'


theorem exists_conj_diag_of_le_xHat_frame {ζ : Kˣ} (hζo : orderOf ζ = 3)
    {E : Subgroup (ModGL τ K)} (hE : IsElemAbelian 3 E) {g : WeylGroup τ} (hg3 : g ^ 3 = 1)
    (hEX : E ≤ xHat τ K (Subgroup.zpowers g)) {ρ : SL(3, K) →* ModGL τ K}
    {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ} (hfr : IsA2Frame ρ σ)
    (hpair : pairRefl (σ 0 1, σ 1 2) = g) {u μ u₁ u₂ : Fin τ.rank → ℤ}
    (horb : g⁻¹ • u + g⁻¹ • (g⁻¹ • u) + u + (2 • σ 0 1 + σ 1 2) = μ + μ + μ)
    (hu₁ : u₁ - g⁻¹ • u₁ = σ 0 1) (hu₂ : u₂ - g⁻¹ • u₂ = σ 1 2) :
    ∃ y ∈ adjointGroup τ K, ∀ e ∈ E, ∃ c, y * e * y⁻¹ = rootDiagUnit τ c := by
  have hEM : E ≤ monoHat τ K := hEX.trans (xHat_le_monoHat _)
  have hψ : ∀ e (he : e ∈ E), psiHat τ K ⟨e, hEM he⟩ ∈ Subgroup.zpowers g :=
    fun e he => (mem_xHat.1 (hEX he)).2
  by_cases htor : ∀ e (he : e ∈ E), psiHat τ K ⟨e, hEM he⟩ = 1
  · refine ⟨1, one_mem _, fun e he => ?_⟩
    obtain ⟨c, hc⟩ := exists_rootDiagUnit_eq_of_psiHat_eq_one (htor e he)
    exact ⟨c, by rw [one_mul, inv_one, mul_one]; exact hc⟩
  push Not at htor
  obtain ⟨e₀, he₀, he₀1⟩ := htor
  obtain ⟨x, hxE, hxψ⟩ : ∃ x, ∃ hx : x ∈ E, psiHat τ K ⟨x, hEM hx⟩ = g := by
    have h := TauCeti.zpowers_eq_zpowers_of_mem_zpowers Nat.prime_three hg3 he₀1 (hψ e₀ he₀)
    have hg : g ∈ Subgroup.zpowers (psiHat τ K ⟨e₀, hEM he₀⟩) := by
      rw [h]
      exact Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact ⟨e₀ ^ k, zpow_mem he₀ k, by rw [← hk, ← map_zpow]; rfl⟩
  have hxHat : x ∈ monoHat τ K := hEM hxE
  set m : ModGL τ K := ρ coxSL3 with hm
  have hcox : (coxSL3 : SL(3, K)) = wSL3 0 1 (by decide) * wSL3 1 2 (by decide) := rfl
  obtain ⟨hm0, hq0⟩ := frame_wSL3 hfr 0 1 (by decide)
  obtain ⟨hm1, hq1⟩ := frame_wSL3 hfr 1 2 (by decide)
  have hmMon : m ∈ monomialSubgroup τ K := by
    rw [hm, hcox, map_mul]
    exact mul_mem hm0 hm1
  have hmaps : MapsRootLines m g := by
    have h0 := mapsRootLines_weylQuotientHom (τ := τ) (R := K) ⟨_, hm0⟩
    have h1 := mapsRootLines_weylQuotientHom (τ := τ) (R := K) ⟨_, hm1⟩
    rw [hq0] at h0
    rw [hq1] at h1
    rw [← hpair, hm, hcox, map_mul]
    exact h0.mul h1
  have hm3 : m * m * m = 1 := by
    rw [← pow_three', hm, ← map_pow, SmallExc.coxSL3_pow_three, map_one]
  have hmψ : psiHat τ K ⟨m, monomial_le_monoHat hmMon⟩ = g := psiHat_eq hmaps
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_psiHat_eq_one
    (x := ⟨x, hxHat⟩ * (⟨m, monomial_le_monoHat hmMon⟩ : monoHat τ K)⁻¹)
    (by rw [map_mul, map_inv, hxψ, hmψ, mul_inv_cancel])
  have hb' : x * m⁻¹ = rootDiagUnit τ b := hb
  set t := weylTuple g⁻¹ b with ht
  have hmt : m⁻¹ * rootDiagUnit τ b * m = rootDiagUnit τ t := by
    have h := monomial_conj_rootDiagUnit_weylTuple (inv_mem hmMon) hmaps.inv b
    rwa [inv_inv] at h
  have hxt : x = m * rootDiagUnit τ t := by
    rw [← hmt, ← hb']
    group
  have hconj : ∀ c, m * rootDiagUnit τ c * m⁻¹ = rootDiagUnit τ (weylTuple g c) :=
    monomial_conj_rootDiagUnit_weylTuple hmMon hmaps
  have ht3 : weylTuple g t * weylTuple g (weylTuple g t) * t = 1 := by
    have h1 : x * (x * x) = (m * rootDiagUnit τ t * m⁻¹) *
        (m * (m * rootDiagUnit τ t * m⁻¹) * m⁻¹) *
        ((m * m * m) * rootDiagUnit τ t * (m * m * m)⁻¹) * (m * m * m) := by
      rw [hxt]
      group
    rw [← pow_three, hE.2 x hxE, hconj, hconj, hm3, one_mul, inv_one, mul_one, mul_one,
      ← rootDiagUnit_mul, ← rootDiagUnit_mul] at h1
    exact rootDiagUnit_injective (h1.symm.trans rootDiagUnit_one.symm)
  have hζ : ζ ^ 3 = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  have hω1 : (ζ : K) ≠ 1 := fun h => by
    have h1 : ζ = 1 := Units.ext h
    rw [h1, orderOf_one] at hζo
    exact absurd hζo (by decide)
  have hζ3 : (ζ : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one]
  have hω : (ζ : K) ^ 2 + ζ + 1 = 0 := by
    have h1 : ((ζ : K) - 1) * ((ζ : K) ^ 2 + ζ + 1) = 0 := by linear_combination hζ3
    exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hω1)
  have h3K : (3 : K) ≠ 0 := fun h30 => hω1 (sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp
    (by linear_combination hω - (ζ : K) * h30)))
  obtain ⟨z, hz⟩ := exists_cube_of_weylTuple_orbit hfr horb ht3
  obtain ⟨s, c, hsc⟩ := SmallExc.exists_conj_rootDiagUnit_of_cube hω h3K hfr t hz
  have hsC : ρ s ∈ adjointGroup τ K := by
    have h : ρ s ∈ rootSpan τ K {r | ∃ i j : Fin 3, i ≠ j ∧ r = σ i j} := by
      rw [← hfr.range]
      exact ⟨s, rfl⟩
    exact rootSpan_le_adjointGroup K _ h
  have hxs : ρ s * x * (ρ s)⁻¹ = rootDiagUnit τ c := by
    rw [hxt]
    exact hsc
  obtain ⟨h0, h1, h2⟩ := SmallExc.frame_col_zero hfr
  have hcent : ∀ e (he : e ∈ E), psiHat τ K ⟨e, hEM he⟩ = 1 → ρ s * e * (ρ s)⁻¹ = e := by
    intro e he he1
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_psiHat_eq_one he1
    have ha' : e = rootDiagUnit τ a := ha
    have hcomm : x * rootDiagUnit τ a * x⁻¹ = rootDiagUnit τ a := by
      rw [← ha', TableB.IsElemAbelian.comm hE hxE he, mul_inv_cancel_right]
    have hweyl : weylTuple g a = a := by
      have h := conj_rootDiagUnit_of_mem_monoHat (⟨x, hxHat⟩ : monoHat τ K) a
      rw [hxψ] at h
      exact rootDiagUnit_injective (h.symm.trans hcomm)
    have hker : ∀ v : Fin τ.rank → ℤ, rootChar a (v - g⁻¹ • v) = 1 := fun v => by
      have h := rootChar_weylTuple g a v
      rw [hweyl] at h
      rw [rootChar_sub, ← h, mul_inv_cancel]
    have hα : rootChar a (σ 0 1) = 1 := by
      rw [← hu₁]
      exact hker u₁
    have hβ : rootChar a (σ 1 2) = 1 := by
      rw [← hu₂]
      exact hker u₂
    have hneg : ∀ w, rootChar a w = 1 → rootChar a (-w) = 1 := fun w hw => by
      have h := rootChar_add a w (-w)
      rw [add_neg_cancel, rootChar_zero, hw, one_mul] at h
      exact h.symm
    have hdd : (fun j => rootChar a (σ j 0)) = 1 := by
      funext j
      have hj : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
      rcases hj with rfl | rfl | rfl
      · rw [Pi.one_apply, h0, rootChar_zero]
      · rw [Pi.one_apply, h1]
        exact hneg _ hα
      · rw [Pi.one_apply, h2]
        exact hneg _ (by rw [rootChar_add, hα, hβ, one_mul])
    have hA := hfr.torus a s
    rw [hdd] at hA
    have hA1 : conjDiag3 (1 : Fin 3 → Kˣ) s = s := by
      apply Subtype.ext
      rw [coe_conjDiag3]
      simp [diagGL3]
    rw [hA1] at hA
    rw [ha']
    calc ρ s * rootDiagUnit τ a * (ρ s)⁻¹
        = rootDiagUnit τ a * ρ s * (rootDiagUnit τ a)⁻¹ * rootDiagUnit τ a * (ρ s)⁻¹ := by
          rw [hA]
      _ = rootDiagUnit τ a := by group
  have hpowz : ∀ (a : Fin τ.rank → Kˣ) (n : ℤ),
      rootDiagUnit τ a ^ n = rootDiagUnit τ (a ^ n) := fun a n => by
    rw [← rootDiagHom_apply, ← rootDiagHom_apply, map_zpow]
  refine ⟨ρ s, hsC, fun e he => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hψ e he)
  have hek : e * x ^ (-k) ∈ E := mul_mem he (zpow_mem hxE _)
  have hker : psiHat τ K ⟨e * x ^ (-k), hEM hek⟩ = 1 := by
    have h : (⟨e * x ^ (-k), hEM hek⟩ : monoHat τ K) = ⟨e, hEM he⟩ * ⟨x, hxHat⟩ ^ (-k) := rfl
    rw [h, map_mul, map_zpow, hxψ, ← hk, ← zpow_add, add_neg_cancel, zpow_zero]
  obtain ⟨c', hc'⟩ := exists_rootDiagUnit_eq_of_psiHat_eq_one hker
  have hc'' : e * x ^ (-k) = rootDiagUnit τ c' := hc'
  refine ⟨c' * c ^ k, ?_⟩
  calc ρ s * e * (ρ s)⁻¹ = (ρ s * (e * x ^ (-k)) * (ρ s)⁻¹) * (ρ s * x * (ρ s)⁻¹) ^ k := by
        rw [conj_zpow]
        group
    _ = rootDiagUnit τ c' * rootDiagUnit τ c ^ k := by
        rw [hcent _ hek hker, hc'', hxs]
    _ = rootDiagUnit τ (c' * c ^ k) := by
        rw [rootDiagUnit_mul, hpowz]

end CFSG.StandardType.ExcFramesHalf

end
