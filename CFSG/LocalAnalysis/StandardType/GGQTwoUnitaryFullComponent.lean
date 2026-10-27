module

public import CFSG.LocalAnalysis.StandardType.GGQTwoUnitaryFullAutomizer
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcEmb
public import Mathlib.GroupTheory.IsPerfect

public noncomputable section

namespace CFSG.StandardType.QTwoUnitaryCav

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.StandardType CFSG.StandardType.LineU CFSG.StandardType.TableBUD
  CFSG.StandardType.UnitTB CFSG.StandardType.UnitAct CFSG.StandardType.InndiagSU
  CFSG.StandardType.QTwoCav CFSG.StandardType.QTwoUnitary
  CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
  CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.SectionRank.OddCover (diagHom)


theorem four_dvd_image_of_full_unitary {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .twA)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ lab.rank)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    4 ∣ Nat.card (ggAutomizer ((J.subgroupOf L).map (MulAut.conj : L →* MulAut L))
      (ggGamma L hN).range) := by
  classical
  obtain ⟨K, hfield, hfinite, h, hK, θ, hN', Q, hQ, hfr, hex⟩ :=
    exists_frame_of_marking_twA_full hS rfl hq2 htag hmark hidx
  letI := hfield
  letI := hfinite
  have hNeq : hN' = hN := Subsingleton.elim _ _
  subst hN'
  let R := LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ 1))
  let c : R →* MulAut R := MulAut.conj
  let ψ : ↥(unitarySU 2 1 K (lab.rank + 1)) →* MulAut R := c.comp (frameMk h Q hQ)
  let Kq : Subgroup R := (J.subgroupOf L).map (ggQuotHom θ)
  let E : Subgroup (MulAut R) := (ggBeta L θ hN).range
  have hL : commutator L = ⊤ := hS.2.1.1
  haveI : Group.IsPerfect L := ⟨hL⟩
  have hZq : Subgroup.center (L ⧸ Subgroup.center L) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot L
  have hZR : Subgroup.center R = ⊥ := by
    apply le_antisymm
    · intro r hr
      have hpre : θ.symm r ∈ Subgroup.center (L ⧸ Subgroup.center L) := by
        rw [Subgroup.mem_center_iff] at hr ⊢
        intro q
        apply θ.injective
        simpa only [map_mul, MulEquiv.apply_symm_apply] using hr (θ q)
      have hpre1 : θ.symm r = 1 := by simpa [hZq] using hpre
      have hr1 : r = 1 := by simpa using congrArg θ hpre1
      simpa [hr1]
    · exact bot_le
  have hc : Function.Injective c := CFSG.mulAutConj_injective_of_center_eq_bot hZR
  have hconj : ∀ (β : MulAut R) (r : R), c (β r) = β * c r * β⁻¹ := by
    intro β r
    ext y
    simp [c, MulAut.mul_apply, MulAut.conj_apply]
  have hψrange : ψ.range = c.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (frameMk_surjective h Q hQ),
      Subgroup.map_top]
  have hψker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 1 K (lab.rank + 1)) := by
    intro u hu
    apply TableBUI.ker_frameMk_le_center h Q hQ
    rw [MonoidHom.mem_ker] at hu ⊢
    apply hc
    simpa [ψ] using hu
  let hDL := d_le_normalizer hS hN
  have hstd : LargeEvenStdSub 3 B x L D J := hS.1.1.2.2
  obtain ⟨-, -, -, -, -, hJcomp, -⟩ := hstd.1
  have hJq : IsComponentOf Kq (⨅ d : D, ggFix (ggBeta L θ hDL d)) :=
    isComponentOf_quotient_image hDL θ hJcomp
  obtain ⟨d, hd1, -, hfixD⟩ := exists_beta_d_generator θ Nat.prime_three hS hN
  let β : MulAut R := ggBeta L θ hDL d
  have hJfix : IsComponentOf Kq (ggFix β) := by
    rwa [hfixD] at hJq
  have hDle : D ≤ Bs := hstd.1.1.trans hS.1.1.2.1.1
  have hβE : β ∈ E := range_ggBeta_le θ hDle hDL hN ⟨d, rfl⟩
  obtain ⟨σ, hσ0, hσ3, hσn, hfrD⟩ := hfr β hβE
  have hpair : (β, diagHom (lab.rank + 1) σ) ∈ SUTorus.suPairs ψ := by
    refine ⟨?_, ?_⟩
    · exact SUTorus.mem_normalizer_of_mem_primeFormUnitary h
        (TableBUD.diagHom_mem_primeFormUnitary h hσn)
    · intro u v hv
      change β * c (frameMk h Q hQ u) * β⁻¹ = c (frameMk h Q hQ v)
      rw [← hconj β]
      exact congrArg c (hfrD u v hv)
  have hfixMap : (ggFix β).map c = c.range ⊓ Subgroup.centralizer {β} := by
    have h := map_fixSubgroup_eq_of_conj c hc β β (hconj β)
    have hgg : ggFix β = fixSubgroup β := by ext r; rfl
    rwa [← hgg] at h
  have hJopen : CFSG.Open.IsComponentOf Kq (ggFix β) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).mp hJfix
  have hJmap := isComponentOf_map_inj hJopen c hc
  rw [hfixMap, ← hψrange] at hJmap
  have hJblock : IsComponentOf (Kq.map c) (ψ.range ⊓ Subgroup.centralizer {β}) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).mpr hJmap
  obtain ⟨I, hI4, -, hblock⟩ := SUTorus.exists_blockSU_of_isComponentOf_two h hψker hpair hJblock
  have hr3 : 3 ≤ lab.rank := three_le_exponent_of_beta_index hS Nat.prime_three θ hN hidx
  have hd4 : 4 ≤ lab.rank + 1 := by omega
  have hfour : 4 ∣ Nat.card (ggAutomizer (Kq.map c) E) := by
    rw [hblock]
    simpa only [ψ, Subgroup.map_map] using
      four_dvd_ggAutomizer_frameBlock_full (h := h) (Q := Q) (hQ := hQ)
        hK hd4 hfr hex I hI4
  have hcard := card_automizer_quotient_image_eq (J := J) θ hL hN
  rwa [hcard] at hfour

end CFSG.StandardType.QTwoUnitaryCav

end
