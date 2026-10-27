module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest15UnitaryEndgame
import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsNNM22
import CFSG.Foundations.MaxOrderThompsonImage
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.QuasiHigh
open CFSG.LieType.Seitz (seitzHyperGamma)


theorem rest15_false_of_linear_m22_quotient
    {G : Type} [Group G] [Finite G]
    (_hS : Standing4 G) (_hU : uniqueFourUnique G) (S : Setup4 G)
    (_hMS : S.InMSigma) (_hPart : PartIAt S.M)
    {L X H K P : Subgroup G} (_hL : L ∈ calC S.M)
    (_hLN : S.M ≤ normalizer (L : Set G)) (_hthin : ¬ F08.Thin8 L)
    (_hXL : X ≤ L) (_hsupp : X ⊔ pCoreOf 2 L = L)
    (_hHtop : H ≠ ⊤) (_hHr : CFSG.Open.pRank 3 H ≤ 3)
    (_hnotStrong : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M)
    (_hXcomp : CFSG.Open.IsComponentOf X (H ⊓ S.M))
    (hKcomp : CFSG.Open.IsComponentOf K H) (hXK : X ≤ K) (hKM : ¬ K ≤ S.M)
    (hX : CFSG.Blueprint.LieModel X .PSL 3 2 2)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P X)
    (hGamma : rankThreeGamma 1 3 P ≤ S.M)
    (_hNormal : (X.subgroupOf (H ⊓ S.M)).Normal)
    (_hGammaH : rankThreeGamma 1 3 (P.subgroupOf H) ≤
      (normalizer (X : Set G)).subgroupOf H)
    (hZK : ¬ 3 ∣ Nat.card (center K))
    (_hAlt : ¬ ∃ n : ℕ, 5 ≤ n ∧
      Nonempty (K ⧸ center K ≃* alternatingGroup (Fin n)))
    (e : K ⧸ center K ≃* (TauCeti.CFSGIndex.sporadic .M22).Group) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXr : 2 ≤ CFSG.Open.pRank 3 X := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hX.two_le_pRank_psl3_of_dvd Nat.prime_three (by norm_num)
  have hPr : 2 ≤ CFSG.Open.pRank 3 P := by
    rwa [CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.pRank_sylow
      Nat.prime_three hP]
  obtain ⟨E, hEP, hE, hEc⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank Nat.prime_three hPr
  have hEK : E ≤ K := hEP.trans (hP.le.trans hXK)
  let F := E.subgroupOf K
  have hF : IsElemAbelian 3 F := CFSG.SectionRank.isElemAbelian_subgroupOf hE K
  have hFc : Nat.card F = 3 ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv, hEc]
  let c : K →* MulAut K := MulAut.conj
  have hc : Function.Injective (c.comp F.subtype) :=
    CFSG.injective_comp_subtype_of_coprime_card_ker c
      (by rw [show c.ker = center K from ker_conj];
          exact (Nat.prime_three.coprime_iff_not_dvd).2 hZK) hF.isPGroup
  let A : Subgroup (MulAut K) := F.map c
  let eF : F ≃* A := MulEquiv.ofBijective (c.subgroupMap F)
    ⟨fun _ _ h => hc (congrArg Subtype.val h), c.subgroupMap_surjective F⟩
  have hA : IsElemAbelian 3 A := CFSG.SectionRank.isElemAbelian_map hF c
  have hAc : Nat.card A = 3 ^ 2 := (Nat.card_congr eF.toEquiv).symm.trans hFc
  have hperf : commutator K = ⊤ := hKcomp.2.2.1
  let β := CFSG.LocalAnalysis.GLTheoremB.quotientCenterAut' K
  have hbarA : IsElemAbelian 3 (A.map β) := CFSG.SectionRank.isElemAbelian_map hA β
  have hbarAc : Nat.card (A.map β) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective
      (CFSG.LocalAnalysis.GLTheoremB.quotientCenterAut'_injective hperf), hAc]
  have hmapped : IsElemAbelian 3
      ((A.map β).map (MulAut.congr e).toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hbarA _
  have hmappedc : Nat.card ((A.map β).map (MulAut.congr e).toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, hbarAc]
    norm_num
  have hm22 : PlaneGen ((A.map β).map (MulAut.congr e).toMonoidHom) :=
    CFSG.HardMathSupport.Solomon.Coordinator.m22_plane_tauCeti _ hmapped hmappedc
  have hquotPlane : PlaneGen (A.map β) := (planeGen_map_congr e (A.map β)).1 hm22
  have hquot := closure_fixed_quotAut_of_seitzHyperGamma hperf
    ((planeGen_iff_seitzHyperGamma Nat.prime_three hbarAc).1 hquotPlane)
  have hhyper : seitzHyperGamma 3 A = ⊤ :=
    seitzHyperGamma_eq_top_of_coprime_center hperf hZK hA.isPGroup hquot
  have hplane : PlaneGen A := (planeGen_iff_seitzHyperGamma Nat.prime_three hAc).2 hhyper
  have hgen : Subgroup.closure
      {k : K | ∃ x ∈ E, x ≠ 1 ∧ x * (k : G) = (k : G) * x} = ⊤ := by
    apply top_le_iff.mp
    rw [← hplane]
    apply Subgroup.closure_mono
    rintro k ⟨φ, ⟨x, hxF, rfl⟩, hx1, hfix⟩
    refine ⟨(x : G), hxF, ?_, ?_⟩
    · intro hx
      have hxK : x = 1 := Subtype.ext hx
      exact hx1 (hxK ▸ map_one c)
    · change x * k * x⁻¹ = k at hfix
      exact congrArg Subtype.val (mul_inv_eq_iff_eq_mul.1 hfix)
  exact false_of_unitary_plane_generation hEP hE hGamma hKM hgen

end CFSG.LocalAnalysis.UniquenessCase.UC22
