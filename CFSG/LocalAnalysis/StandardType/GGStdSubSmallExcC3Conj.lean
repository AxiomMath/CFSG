module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC3ConjCore
public import TauCeti.GroupTheory.ExponentPrime

public section

namespace CFSG.StandardType.SmallExc

open scoped MatrixGroups
open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE TableBExc.E6Three NoOffTwE6Three
open CFSG.HardMathSupport.Timmesfeld.CrossChar (pairRefl)

variable {K : Type} [Field K]

theorem exists_conj_diag_of_le_xHat {ζ : Kˣ} (hζo : orderOf ζ = 3)
    {E : Subgroup (ModGL .E6 K)} (hE : IsElemAbelian 3 E) {i : Fin 3}
    (hEX : E ≤ xHat .E6 K (Subgroup.zpowers (gE6 i))) :
    ∃ y ∈ adjointGroup .E6 K, ∀ e ∈ E, ∃ c, y * e * y⁻¹ = rootDiagUnit .E6 c := by
  have hζ : ζ ^ 3 = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  have hEM : E ≤ monoHat .E6 K := hEX.trans (xHat_le_monoHat _)
  have hψ : ∀ e (he : e ∈ E), psiHat .E6 K ⟨e, hEM he⟩ ∈ Subgroup.zpowers (gE6 i) :=
    fun e he => (mem_xHat.1 (hEX he)).2
  by_cases htor : ∀ e (he : e ∈ E), psiHat .E6 K ⟨e, hEM he⟩ = 1
  · refine ⟨1, one_mem _, fun e he => ?_⟩
    obtain ⟨c, hc⟩ := exists_rootDiagUnit_eq_of_psiHat_eq_one (htor e he)
    exact ⟨c, by rw [one_mul, inv_one, mul_one]; exact hc⟩
  push Not at htor
  obtain ⟨e₀, he₀, he₀1⟩ := htor
  obtain ⟨x, hxE, hxψ⟩ : ∃ x, ∃ hx : x ∈ E, psiHat .E6 K ⟨x, hEM hx⟩ = gE6 i := by
    have h := TauCeti.zpowers_eq_zpowers_of_mem_zpowers Nat.prime_three (gE6_pow_three i) he₀1
      (hψ e₀ he₀)
    have hg : gE6 i ∈ Subgroup.zpowers (psiHat .E6 K ⟨e₀, hEM he₀⟩) := by
      rw [h]
      exact Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact ⟨e₀ ^ k, zpow_mem he₀ k, by rw [← hk, ← map_zpow]; rfl⟩
  have hxHat : x ∈ monoHat .E6 K := hEM hxE
  obtain ⟨ρ, σ, hfr, h01, h12⟩ := exists_frame_a2PairE6 K i
  have hpair : pairRefl (σ 0 1, σ 1 2) = gE6 i := by
    rw [h01, h12]
    exact pairRefl_a2PairE6 i
  set m : ModGL .E6 K := ρ coxSL3 with hm
  have hcox : (coxSL3 : SL(3, K)) = wSL3 0 1 (by decide) * wSL3 1 2 (by decide) := rfl
  obtain ⟨hm0, hq0⟩ := frame_wSL3 hfr 0 1 (by decide)
  obtain ⟨hm1, hq1⟩ := frame_wSL3 hfr 1 2 (by decide)
  have hmMon : m ∈ monomialSubgroup .E6 K := by
    rw [hm, hcox, map_mul]
    exact mul_mem hm0 hm1
  have hmaps : MapsRootLines m (gE6 i) := by
    have h0 := mapsRootLines_weylQuotientHom (τ := .E6) (R := K) ⟨_, hm0⟩
    have h1 := mapsRootLines_weylQuotientHom (τ := .E6) (R := K) ⟨_, hm1⟩
    rw [hq0] at h0
    rw [hq1] at h1
    rw [← hpair, hm, hcox, map_mul]
    exact h0.mul h1
  have hm3 : m * m * m = 1 := by
    rw [← pow_three', hm, ← map_pow, coxSL3_pow_three, map_one]
  have hmHat : m ∈ monoHat .E6 K := monomial_le_monoHat hmMon
  have hmψ : psiHat .E6 K ⟨m, hmHat⟩ = gE6 i := psiHat_eq hmaps
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_psiHat_eq_one
    (x := ⟨x, hxHat⟩ * (⟨m, hmHat⟩ : monoHat .E6 K)⁻¹)
    (by rw [map_mul, map_inv, hxψ, hmψ, mul_inv_cancel])
  have hb' : x * m⁻¹ = rootDiagUnit .E6 b := hb
  set t := weylTuple (gE6 i)⁻¹ b with ht
  have hmt : m⁻¹ * rootDiagUnit .E6 b * m = rootDiagUnit .E6 t := by
    have h := monomial_conj_rootDiagUnit_weylTuple (inv_mem hmMon) hmaps.inv b
    rwa [inv_inv] at h
  have hxt : x = m * rootDiagUnit .E6 t := by
    rw [← hmt, ← hb']
    group
  have hconj : ∀ c, m * rootDiagUnit .E6 c * m⁻¹ = rootDiagUnit .E6 (weylTuple (gE6 i) c) :=
    monomial_conj_rootDiagUnit_weylTuple hmMon hmaps
  have ht3 : weylTuple (gE6 i) t * weylTuple (gE6 i) (weylTuple (gE6 i) t) * t = 1 := by
    have h1 : x * (x * x) = (m * rootDiagUnit .E6 t * m⁻¹) *
        (m * (m * rootDiagUnit .E6 t * m⁻¹) * m⁻¹) *
        ((m * m * m) * rootDiagUnit .E6 t * (m * m * m)⁻¹) * (m * m * m) := by
      rw [hxt]
      group
    rw [← pow_three, hE.2 x hxE, hconj, hconj, hm3, one_mul, inv_one, mul_one, mul_one,
      ← rootDiagUnit_mul, ← rootDiagUnit_mul] at h1
    exact rootDiagUnit_injective (h1.symm.trans rootDiagUnit_one.symm)
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
  obtain ⟨z, hz⟩ := exists_cube_of_weylTuple hfr h01 h12 ht3
  obtain ⟨g, c, hgc⟩ := exists_conj_rootDiagUnit_of_cube hω h3K hfr t hz
  have hyC : ρ g ∈ adjointGroup .E6 K := by
    have h : ρ g ∈ rootSpan .E6 K {r | ∃ i j : Fin 3, i ≠ j ∧ r = σ i j} := by
      rw [← hfr.range]
      exact ⟨g, rfl⟩
    exact rootSpan_le_adjointGroup K _ h
  have hxy : ρ g * x * (ρ g)⁻¹ = rootDiagUnit .E6 c := by
    rw [hxt]
    exact hgc
  obtain ⟨h0, h1, h2⟩ := frame_col_zero hfr
  have hcent : ∀ e (he : e ∈ E), psiHat .E6 K ⟨e, hEM he⟩ = 1 → ρ g * e * (ρ g)⁻¹ = e := by
    intro e he he1
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_psiHat_eq_one he1
    have ha' : e = rootDiagUnit .E6 a := ha
    have ha3 : a ^ 3 = 1 := by
      have h3 : rootDiagUnit .E6 (a ^ 3) = rootDiagUnit .E6 1 := by
        rw [← rootDiagUnit_pow, ← ha', hE.2 e he, rootDiagUnit_one]
      exact rootDiagUnit_injective h3
    have hcomm : x * rootDiagUnit .E6 a * x⁻¹ = rootDiagUnit .E6 a := by
      rw [← ha', TableB.IsElemAbelian.comm hE hxE he, mul_inv_cancel_right]
    have hweyl : weylTuple (gE6 i) a = a := by
      have h := conj_rootDiagUnit_of_mem_monoHat (⟨x, hxHat⟩ : monoHat .E6 K) a
      rw [hxψ] at h
      exact rootDiagUnit_injective (h.symm.trans hcomm)
    obtain ⟨v, rfl⟩ := exists_zetaVec_eq hζo hζ ha3
    have hv : adAct .E6 3 (gE6 i) v = v := by
      refine zetaVec_injective hζo hζ ?_
      rw [← weylTuple_zetaVec]
      exact hweyl
    obtain ⟨hα, hβ⟩ := (adAct_gE6_eq_iff i v).1 hv
    have hα' := (rootChar_zetaVec_eq_one_iff hζo hζ v _).2 hα
    have hβ' := (rootChar_zetaVec_eq_one_iff hζo hζ v _).2 hβ
    rw [← h01] at hα'
    rw [← h12] at hβ'
    have hneg : ∀ u, rootChar (zetaVec ζ hζ v) u = 1 → rootChar (zetaVec ζ hζ v) (-u) = 1 :=
      fun u hu => by
        have h := rootChar_add (zetaVec ζ hζ v) u (-u)
        rw [add_neg_cancel, rootChar_zero, hu, one_mul] at h
        exact h.symm
    have hdd : (fun j => rootChar (zetaVec ζ hζ v) (σ j 0)) = 1 := by
      funext j
      have hj : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
      rcases hj with rfl | rfl | rfl
      · rw [Pi.one_apply, h0, rootChar_zero]
      · rw [Pi.one_apply, h1]
        exact hneg _ hα'
      · rw [Pi.one_apply, h2]
        exact hneg _ (by rw [rootChar_add, hα', hβ', one_mul])
    have hA := hfr.torus (zetaVec ζ hζ v) g
    rw [hdd] at hA
    have hA1 : conjDiag3 (1 : Fin 3 → Kˣ) g = g := by
      apply Subtype.ext
      rw [coe_conjDiag3]
      simp [diagGL3]
    rw [hA1] at hA
    rw [ha']
    calc ρ g * rootDiagUnit .E6 (zetaVec ζ hζ v) * (ρ g)⁻¹
        = rootDiagUnit .E6 (zetaVec ζ hζ v) * ρ g * (rootDiagUnit .E6 (zetaVec ζ hζ v))⁻¹ *
            rootDiagUnit .E6 (zetaVec ζ hζ v) * (ρ g)⁻¹ := by rw [hA]
      _ = rootDiagUnit .E6 (zetaVec ζ hζ v) := by group
  have hpowz : ∀ (a : Fin Tag.E6.rank → Kˣ) (n : ℤ),
      rootDiagUnit .E6 a ^ n = rootDiagUnit .E6 (a ^ n) := fun a n => by
    rw [← rootDiagHom_apply, ← rootDiagHom_apply, map_zpow]
  refine ⟨ρ g, hyC, fun e he => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hψ e he)
  have hek : e * x ^ (-k) ∈ E := mul_mem he (zpow_mem hxE _)
  have hker : psiHat .E6 K ⟨e * x ^ (-k), hEM hek⟩ = 1 := by
    have h : (⟨e * x ^ (-k), hEM hek⟩ : monoHat .E6 K) = ⟨e, hEM he⟩ * ⟨x, hxHat⟩ ^ (-k) := rfl
    rw [h, map_mul, map_zpow, hxψ, ← hk, ← zpow_add, add_neg_cancel, zpow_zero]
  obtain ⟨c', hc'⟩ := exists_rootDiagUnit_eq_of_psiHat_eq_one hker
  have hc'' : e * x ^ (-k) = rootDiagUnit .E6 c' := hc'
  refine ⟨c' * c ^ k, ?_⟩
  calc ρ g * e * (ρ g)⁻¹ = (ρ g * (e * x ^ (-k)) * (ρ g)⁻¹) * (ρ g * x * (ρ g)⁻¹) ^ k := by
        rw [conj_zpow]
        group
    _ = rootDiagUnit .E6 c' * rootDiagUnit .E6 c ^ k := by
        rw [hcent _ hek hker, hc'', hxy]
    _ = rootDiagUnit .E6 (c' * c ^ k) := by
        rw [rootDiagUnit_mul, hpowz]

end CFSG.StandardType.SmallExc

end
