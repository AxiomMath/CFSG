module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcRank
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcPairsE6
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2E6Outer
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Ctx
import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicExcSix
import CFSG.RankThree.PartTwo.Sec4.T444.Item434CoverKit
import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Hat
import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.ChiPow
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcOrder
public import CFSG.LieType.Steinberg.Isogeny.E6
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcPeriodic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.SmithCurtis CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule

private theorem w135c2_e6_direct_comp {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {E k V : Type} [Group E] [Field k] [AddCommGroup V] [Module k V] {πh : E →* ↥L}
    (hπh : Function.Surjective πh) {ρ : Representation k ↥L V} (hρ : IsSimpleRep ρ)
    (hρinj : Function.Injective ρ) (hnt : Nontrivial ↥L) :
    IsSimpleRep (ρ.comp πh) ∧
      (∃ (x : E) (v : V), (ρ.comp πh) x v ≠ v) ∧
      ∀ z, Module.finrank k (LinearMap.range (ρ (πh z) - 1)) =
        Module.finrank k (LinearMap.range ((ρ.comp πh) z - 1)) := by
  refine ⟨CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.simpleRep_comp
    πh hπh hρ, ?_, fun z => rfl⟩
  obtain ⟨s, hs⟩ := exists_ne (1 : ↥L)
  obtain ⟨x, rfl⟩ := hπh s
  refine ⟨x, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hs
  apply hρinj
  rw [map_one]
  exact LinearMap.ext hcon


variable {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)} {t : MulAut W}

private theorem w135c2_e6_direct_hat {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (φ : ↥L →* ↥(adjointGroup .E6 K))
    (hφ : Function.Surjective φ) (hφk : φ.ker ≤ Subgroup.center ↥L)
    (hperfc : commutator ↥L = ⊤) (ψ : MulAut ↥(adjointGroup .E6 K)) :
    ∃ πh : ↥(e6Data_valid.minGroup K) →* ↥L, Function.Surjective πh ∧
      ∀ x, ψ (φ (πh x)) = Isogeny.e6Isogeny K x := by
  classical
  refine CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.exists_hat
    (Isogeny.e6Isogeny K) (ψ.toMonoidHom.comp φ) ?_ ?_ hperfc ?_
    (Isogeny.e6Isogeny_surjective (k := K))
  · exact ψ.surjective.comp hφ
  · intro x hx
    exact hφk (by
      rw [MonoidHom.mem_ker]
      exact ψ.injective (by simpa using hx))
  · intro E _ _ p hp hc
    exact CFSG.StandardType.LayerCycExc.e6_minGroup_exists_section hK E p hp hc

theorem w135c2_four_le_mQuot_e6_direct (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L)
    (htY : t ∈ Y) (ht2 : orderOf t = 2) {n f : ℕ}
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .E6 n 2 f) :
    4 ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
  classical
  obtain ⟨hadm, K, hKfld, hKfin, hK, ⟨e0⟩⟩ := hlie.chevalleyExceptionalModel (by decide)
  have hf1 : 1 ≤ f := hadm.2.1
  have hK2 : Nat.card K = 2 ^ f := hK
  have hcharK : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hf1 hK2
  let : Field K := hKfld
  let : Finite K := hKfin
  let : CharP K 2 := hcharK
  let eS : ↥L ⧸ Subgroup.center ↥L ≃* ↥(adjointGroup .E6 K) :=
    e0.trans (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.adjointQuotientEquiv .E6 K)
  let φ : ↥L →* ↥(adjointGroup .E6 K) :=
    eS.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hφ : Function.Surjective φ :=
    eS.surjective.comp (QuotientGroup.mk'_surjective _)
  have hφk : φ.ker ≤ Subgroup.center ↥L := by
    intro x hx
    have h0 : eS (QuotientGroup.mk x) = 1 := hx
    have h1 : (QuotientGroup.mk x : ↥L ⧸ Subgroup.center ↥L) = 1 :=
      eS.injective (h0.trans (map_one eS).symm)
    exact (QuotientGroup.eq_one_iff x).1 h1
  have hperf : Group.IsPerfect ↥L := hctx.2.2.2.2.1.1
  have hperfc : commutator ↥L = ⊤ := Group.isPerfect_def.1 hperf
  have hLnt : Nontrivial ↥L := by
    have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hctx.2.2.2.2.1.2.1
    exact (QuotientGroup.mk'_surjective (Subgroup.center ↥L)).nontrivial
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← pow_two]; exact hW w
  have hirr := w135c2_x1IsIrrOn_of_ctx hctx
  obtain ⟨δ, m, k, hkfld, hkfin, hkchar, hAlg, ρ, hδ, hρ, hρinj, hfix⟩ :=
    w135c2_periodic_fix (S := ↥L) (K := K) (n := f) hW' hirr (MulEquiv.refl ↥L) hf1 hK2
  let : Field k := hkfld
  let : Finite k := hkfin
  let : CharP k 2 := hkchar
  let : Algebra K k := hAlg
  by_cases htL : t ∈ L
  ·
    let t₀ : ↥L := ⟨t, htL⟩
    have ht1 : t ≠ 1 := by
      intro h
      rw [h, orderOf_one] at ht2
      omega
    have ht₀2 : t₀ ^ 2 = 1 := by
      refine Subtype.ext ?_
      simpa [Subgroup.coe_pow, ht2] using pow_orderOf_eq_one t
    have ht₀1 : t₀ ≠ 1 := by
      intro h
      exact ht1 (congrArg Subtype.val h)
    have ht₀ord : orderOf t₀ = 2 := orderOf_eq_prime ht₀2 ht₀1
    have hodd := w135_odd_card_center hctx
    have ht₀Z : t₀ ∉ Subgroup.center ↥L := by
      intro hmem
      have h2 : orderOf (⟨t₀, hmem⟩ : Subgroup.center ↥L) = 2 := by
        refine orderOf_eq_prime ?_ ?_
        · refine Subtype.ext ?_
          simpa [Subgroup.coe_pow] using ht₀2
        · intro h
          exact ht₀1 (by simpa using congrArg Subtype.val h)
      have hdvd : 2 ∣ Nat.card (Subgroup.center ↥L) := by
        have h := orderOf_dvd_natCard (⟨t₀, hmem⟩ : Subgroup.center ↥L)
        rwa [h2] at h
      exact (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr hdvd)) hodd
    have hφt2 : φ t₀ ^ 2 = 1 := by
      rw [← map_pow, ht₀2, map_one]
    have hφt1 : φ t₀ ≠ 1 := by
      intro h
      exact ht₀Z (hφk (by rw [MonoidHom.mem_ker]; exact h))
    obtain ⟨g, hg⟩ :=
      CFSG.SeitzReduction.exists_conj_mem_innerRepsE6 (K := K) hφt2 hφt1
    let ψ : MulAut ↥(adjointGroup .E6 K) := MulAut.conj g
    have hmem : ψ (φ t₀) ∈ CFSG.SeitzReduction.innerRepsE6 K := by
      simpa [ψ, MulAut.conj_apply] using hg
    obtain ⟨πh, hπh, hπheq⟩ :=
      w135c2_e6_direct_hat (K := K) (n := f) hK2 φ hφ hφk hperfc ψ
    obtain ⟨zh, hzh⟩ := hπh t₀
    have hz : (Isogeny.e6Isogeny K zh : ↥(adjointGroup .E6 K)) ∈
        CFSG.SeitzReduction.innerRepsE6 K := by
      rw [← hπheq zh, hzh]
      exact hmem
    have hcomp := w135c2_e6_direct_comp hπh hρ hρinj hLnt
    have h4 : 4 ≤ Module.finrank k (LinearMap.range ((ρ.comp πh) zh - 1)) :=
      e6_four_le_finrank_inner hcomp.1 hcomp.2.1 zh hz
    have h4' : 4 ≤ Module.finrank k (LinearMap.range (ρ t₀ - 1)) := by
      rw [← hcomp.2.2 zh, hzh] at h4
      exact h4
    have hfin : 4 ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
      have hfix₀ : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) =
          δ * Module.finrank k (LinearMap.range (ρ t₀ - 1)) := by
        simpa using hfix t₀
      rw [hfix₀]
      simpa using Nat.mul_le_mul hδ h4'
    exact hfin
  ·
    obtain ⟨α, hα2, hαout, hbound⟩ :=
      w135c2_exists_outer_aut hW hctx (MulEquiv.refl ↥L) htY ht2 htL
    let abar : MulAut ↥(adjointGroup .E6 K) :=
      eS.symm.trans
        ((CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient α).trans eS)
    have habarapply : ∀ x : ↥L, abar (φ x) = φ (α x) := by
      intro x
      change eS (CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient α
        (eS.symm (eS ((QuotientGroup.mk' (Subgroup.center ↥L)) x)))) =
        eS ((QuotientGroup.mk' (Subgroup.center ↥L)) (α x))
      rw [eS.symm_apply_apply,
        CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk]
    have hc2 : CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient α *
        CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient α = 1 := by
      have hmul : CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient (α * α) =
          CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient α *
            CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient α :=
        map_mul (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥L) α α
      rw [← hmul, hα2]
      exact map_one (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥L)
    have habar2 : abar * abar = 1 := by
      apply MulEquiv.ext
      intro y
      show abar (abar y) = y
      change eS (CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient α
        (eS.symm (eS (CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient α
          (eS.symm y))))) = y
      rw [eS.symm_apply_apply]
      change eS ((CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient α *
        CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient α)
          (eS.symm y)) = y
      rw [hc2, MulAut.one_apply, eS.apply_symm_apply]
    have habarout : ∀ c : ↥(adjointGroup .E6 K), abar ≠ MulAut.conj c := by
      intro c hc
      obtain ⟨c₀, hc₀⟩ := hφ c
      apply hαout c₀
      refine CFSG.RankThree.PartTwo.Sec4.Item434Cover.mulAut_eq_conj_of_ker_le_center
        φ hφk α c₀ ?_
      intro l
      have h1 : φ (α l) = abar (φ l) := (habarapply l).symm
      rw [h1, hc, MulAut.conj_apply, ← hc₀]
    obtain ⟨ψ, xbar, d₁, d₆, hψ⟩ := e6_exists_inv_mul_eq_frame hf1 hK2 abar habar2 habarout
    obtain ⟨x, hφx⟩ := hφ xbar
    obtain ⟨πh, hπh, hπheq⟩ :=
      w135c2_e6_direct_hat (K := K) (n := f) hK2 φ hφ hφk hperfc ψ
    have hφeq : φ ((α x)⁻¹ * x) = (abar xbar)⁻¹ * xbar := by
      rw [map_mul, map_inv, hφx, ← habarapply x, hφx]
    obtain ⟨zh, hzh⟩ := hπh ((α x)⁻¹ * x)
    have hz : ((Isogeny.e6Isogeny K zh : ↥(adjointGroup .E6 K)) : ModGL .E6 K) =
        pinnedX .E6 K (Pi.single (0 : Fin 6) 1) (d₁ : K) *
          pinnedX .E6 K (Pi.single (5 : Fin 6) 1) (d₆ : K) := by
      rw [← hπheq zh, hzh, hφeq, hψ]
    have hcomp := w135c2_e6_direct_comp hπh hρ hρinj hLnt
    have h7 : 7 ≤ Module.finrank k (LinearMap.range ((ρ.comp πh) zh - 1)) :=
      e6_seven_le_finrank_outer_frame hcomp.1 hcomp.2.1 d₁ d₆ zh hz
    have hrank7 : 7 ≤
        Module.finrank k (LinearMap.range (ρ ((α x)⁻¹ * x) - 1)) := by
      rw [← hcomp.2.2 zh, hzh] at h7
      exact h7
    have h7δ : 7 ≤ δ * Module.finrank k
        (LinearMap.range (ρ ((α x)⁻¹ * x) - 1)) := by
      simpa using Nat.mul_le_mul hδ hrank7
    have hm := hbound x
    rw [hfix ((α x)⁻¹ * x)] at hm
    have h2 : 7 ≤ 2 * E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := le_trans h7δ hm
    omega

end CFSG.LocalAnalysis.WeakClosure81
