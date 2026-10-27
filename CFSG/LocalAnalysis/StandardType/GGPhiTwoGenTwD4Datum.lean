module

public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6TwoD4
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenLabels
public import CFSG.LieType.Universal.SpinOmega.Center

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.LieType.SeitzGeneration.ExcHigh
open CFSG.LieType.Chevalley
open CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem exists_d4Datum_twE6
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    ∃ θ : ↥(d4Group σ.toRingHom) ≃*
        OrthRest.RPlus (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) 4,
      commutator ↥(d4Group σ.toRingHom) = ⊤ ∧
      (∀ z : ↥(d4Group σ.toRingHom), (∀ x : ↥(d4Group σ.toRingHom), z * x = x * z) → z = 1) ∧
      orbitRankOneGroup TwistTag.E6 K σ.toRingHom ⟨3, by decide⟩ ≤
        (d4Group σ.toRingHom).map (twistedE6RootGroup K σ).subtype ∧
      (⨆ i, (frameHom σ.toRingHom i).range) ≤ d4Group σ.toRingHom ∧
      (∀ y ∈ d4Group σ.toRingHom, ∀ z ∈ (torusG σ.toRingHom).range, y * z = z * y) := by
  have hkcard : Nat.card (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) = 2 ^ n :=
    CFSG.RankThree.Chevalley.card_eqLocusField_of_pow (by norm_num) (by omega) hK hσ
  haveI : Fintype (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) := Fintype.ofFinite _
  haveI : CharP (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) 2 :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hkcard])
  obtain ⟨Ψ, hΨker, hΨrange⟩ :=
    exists_psi_d4 Nat.prime_two (by omega) σ.toRingHom hkcard
  have hZspin : Subgroup.center
      (spinGroup (CFSG.LieType.Universal.Spin.quadPlus 4
        (RingHom.eqLocusField σ.toRingHom (RingHom.id K)))) = ⊥ :=
    (OrthRest.spinPlus_bij (K := RingHom.eqLocusField σ.toRingHom (RingHom.id K)) (n := 4)
      (by norm_num)).2
  have hinj : Function.Injective Ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx' : x ∈ Subgroup.center
        (spinGroup (CFSG.LieType.Universal.Spin.quadPlus 4
          (RingHom.eqLocusField σ.toRingHom (RingHom.id K)))) := hΨker hx
    rwa [hZspin] at hx'
  let e1 : spinGroup (CFSG.LieType.Universal.Spin.quadPlus 4
        (RingHom.eqLocusField σ.toRingHom (RingHom.id K))) ≃* ↥(d4Group σ.toRingHom) :=
    (MulEquiv.ofBijective Ψ.rangeRestrict
        ⟨fun x y h => hinj (Subtype.ext_iff.mp h), MonoidHom.rangeRestrict_surjective Ψ⟩).trans
      (MulEquiv.subgroupCongr hΨrange)
  let eSpin : spinGroup (CFSG.LieType.Universal.Spin.quadPlus 4
        (RingHom.eqLocusField σ.toRingHom (RingHom.id K))) ≃*
      OrthRest.RPlus (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) 4 :=
    MulEquiv.ofBijective _ (OrthRest.spinPlus_bij
      (K := RingHom.eqLocusField σ.toRingHom (RingHom.id K)) (n := 4) (by norm_num)).1
  let θ : ↥(d4Group σ.toRingHom) ≃*
      OrthRest.RPlus (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) 4 := e1.symm.trans eSpin
  have hcenter : Subgroup.center ↥(d4Group σ.toRingHom) = ⊥ := by
    have hmap := Subgroup.map_center_eq e1
    rw [hZspin, Subgroup.map_bot] at hmap
    exact hmap.symm
  have hperf : commutator ↥(d4Group σ.toRingHom) = ⊤ := by
    have hperfS : Group.IsPerfect (CFSG.Open.StatedOmega
        (CFSG.Open.StatedQuadPlus 4 (RingHom.eqLocusField σ.toRingHom (RingHom.id K)))) :=
      CFSG.LieType.Universal.Spin.isPerfect_statedOmega_quadPlus
        (K := RingHom.eqLocusField σ.toRingHom (RingHom.id K)) (n := 4) (by norm_num)
    haveI : Group.IsPerfect (CFSG.Open.StatedOmega
        (CFSG.Open.StatedQuadPlus 4 (RingHom.eqLocusField σ.toRingHom (RingHom.id K)))) := hperfS
    have hperfD : Group.IsPerfect ↥(d4Group σ.toRingHom) :=
      Group.IsPerfect.ofSurjective
        (f := (θ.trans (rPlusEquivStatedOmega
          (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) 4)).symm.toMonoidHom)
        (θ.trans (rPlusEquivStatedOmega
          (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) 4)).symm.surjective
    exact hperfD.commutator_eq_top
  have hM3 : orbitRankOneGroup TwistTag.E6 K σ.toRingHom ⟨3, by decide⟩ ≤
      (d4Group σ.toRingHom).map (twistedE6RootGroup K σ).subtype := by
    intro y hy
    obtain ⟨A, hA⟩ := (orbitRankOneGroup_le_range_rankOneFix σ.toRingHom orbCenter
      orbCenter_card) hy
    have hyeq : y = (centerHom σ.toRingHom A : ModGL TwistTag.E6.tag K) := hA.symm
    have hA_mem : centerHom σ.toRingHom A ∈ d4Group σ.toRingHom :=
      Subgroup.mem_iSup_of_mem 1 (show centerHom σ.toRingHom A ∈ (d4Rho σ.toRingHom 1).range from
        MonoidHom.mem_range.mpr ⟨A, rfl⟩)
    rw [hyeq]
    exact Subgroup.mem_map_of_mem (twistedE6RootGroup K σ).subtype hA_mem
  have hframe : (⨆ i, (frameHom σ.toRingHom i).range) ≤ d4Group σ.toRingHom := by
    refine iSup_le fun i => ?_
    fin_cases i
    · exact le_iSup (fun i => (d4Rho σ.toRingHom i).range) 0
    · exact le_iSup (fun i => (d4Rho σ.toRingHom i).range) 2
    · exact le_iSup (fun i => (d4Rho σ.toRingHom i).range) 3
    · exact frameHom_three_le_d4Group σ.toRingHom
  have htorus : ∀ y ∈ d4Group σ.toRingHom,
      ∀ z ∈ (torusG σ.toRingHom).range, y * z = z * y := by
    intro y hy z hz
    obtain ⟨t, rfl⟩ := hz
    exact (torusG_commute_d4Group σ.toRingHom t y hy).symm
  refine ⟨θ, hperf, ?_, hM3, hframe, htorus⟩
  intro z hz
  have hz' : z ∈ Subgroup.center ↥(d4Group σ.toRingHom) :=
    Subgroup.mem_center_iff.mpr (fun g => (hz g).symm)
  rw [hcenter] at hz'
  exact Subgroup.mem_bot.mp hz'

end CFSG.StandardType.PhiTwoRootGen

end
