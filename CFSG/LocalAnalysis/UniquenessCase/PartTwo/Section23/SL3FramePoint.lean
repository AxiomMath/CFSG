module

public import CFSG.GroupTheory.FixedPointFreeJoin
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSL3PointCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSchurSL3Proof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsSL3FifteenOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsSL3SeventeenElt
public import CFSG.GroupTheory.PCoreSurjective
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.Main
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveKNshape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveKSchur

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx2311

structure SL3Facts {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch) : Prop where
  h1930 : H1930 D
  h4 : S23_4 D Ch
  h12 : S23_12 D Ch
  h14 : S23_14 D Ch
  hV : IsElemAbelian 2 c.V
  h3 : 3 ≤ CFSG.Open.pRank 2 D.Z
  hSL : IsSLn ↥(c.H hV) 3 (CFSG.Open.pRank 2 D.Z)
  hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z)
  hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L
  hN8 : ⁅c.V, c.K⁆ = c.V
  hEE : ⁅c.E, c.E⁆ ≤ D.Z
  hEsq : ∀ x ∈ c.E, x ^ 2 ∈ D.Z

theorem sl3Facts_of {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (h1930 : H1930 D) (hE : UC22P20gExcFacts) (h207 : S20_7 D)
    (h2 : S23_2_natural D Ch) (h3 : S23_3 D Ch) (h4 : S23_4 D Ch)
    (hline : S23_5_line D Ch) (hN1 : S23_9_NotSp4SU4O6m D Ch)
    (hN2 : S23_9_NotO6p D Ch) (hN3 : S23_9_NotLarge D Ch)
    (h12 : S23_12 D Ch) (h14 : S23_14 D Ch) : c.SL3Facts := by
  obtain ⟨h3m, hV, hSL, hnat, hker⟩ :=
    c.sl3Line_of h1930 hE h207 h2 h3 h4 hline kNshape_holds
      KOrdNat.kOrdNatural_holds kSchurL2_holds kSchurSL3_holds hN1 hN2 hN3
  have hN8 : ⁅c.V, c.K⁆ = c.V :=
    c.commutator_V_K_eq_of_sl3 h4 h1930 hV h3m hSL hnat kSL3Span_holds
  obtain ⟨hKW, -, -, -, hWT⟩ :=
    Ctx2311.geom2311_of D Ch hE h207 h2 h3 h4 hline kNshape_holds
      KOrdNat.kOrdNatural_holds kSchurL2_holds kSchurSL3_holds hN1 hN2 hN3
      kSL3Span_holds kSL3Line_holds
  exact
    { h1930 := h1930
      h4 := h4
      h12 := h12
      h14 := h14
      hV := hV
      h3 := h3m
      hSL := hSL
      hnat := hnat
      hker := hker
      hN8 := hN8
      hEE := s23fifteen_commutator_E_E_le_Z c h4 h1930 (hWT h1930 c) (hKW h1930 c)
      hEsq := s23fifteen_sq_mem_Z c h4 h1930 (hWT h1930 c) (hKW h1930 c) }

theorem SL3Facts.normalizer_Z_eq {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (F : c.SL3Facts) : Subgroup.normalizer (D.Z : Set G) = D.M := by
  have h4c := F.h4 F.h1930 c.toCtx23L
  rw [← h4c.1, Data.normalizer_U_eq D]

theorem SL3Facts.mem_M_iff {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (F : c.SL3Facts) (l : ↥c.L) :
    letI : MulDistribMulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
      MulDistribMulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
    letI : MulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
      MulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
    letI : MulAction ↥(c.H F.hV) (Set (c.toCtx23L.W F.hV)) := Set.mulActionSet
    (l : G) ∈ D.M ↔ c.phiL F.hV l ∈ MulAction.stabilizer ↥(c.H F.hV)
      ((c.toCtx23L.Ztil F.hV : Subgroup (c.toCtx23L.W F.hV)) :
        Set (c.toCtx23L.W F.hV)) := by
  letI : MulDistribMulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
  letI : MulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
    MulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
  letI : MulAction ↥(c.H F.hV) (Set (c.toCtx23L.W F.hV)) := Set.mulActionSet
  exact (c.toCtx23L.phiL_mem_stabilizer_Ztil_iff F.hV F.h4 F.h1930 l).symm

private noncomputable def KStar {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (F : c.SL3Facts) : Subgroup ↥(c.H F.hV) :=
  (c.K.subgroupOf c.L).map (c.phiL F.hV)

private noncomputable def phiK {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (F : c.SL3Facts) : ↥c.K →* ↥(KStar F) :=
  ((c.phiL F.hV).comp (Subgroup.inclusion c.K_le_L)).codRestrict (KStar F) fun x =>
    Subgroup.mem_map_of_mem (c.phiL F.hV) x.2

private theorem phiK_surjective {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (F : c.SL3Facts) : Function.Surjective (phiK F) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
  have hxK : (x : G) ∈ c.K := Subgroup.mem_subgroupOf.mp hx
  refine ⟨⟨(x : G), hxK⟩, Subtype.ext ?_⟩
  show c.phiL F.hV ⟨(x : G), c.K_le_L hxK⟩ = (y : ↥(c.H F.hV))
  rw [show (⟨(x : G), c.K_le_L hxK⟩ : ↥c.L) = x from Subtype.ext rfl]
  exact hxy

private theorem phiK_ker_iff {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (F : c.SL3Facts) (x : ↥c.K) :
    phiK F x = 1 ↔ (x : G) ∈ CFSG.Open.pCoreOf 2 c.L := by
  let e : ↥c.L := Subgroup.inclusion c.K_le_L x
  constructor
  · intro hx
    have hx' : c.phiL F.hV e = 1 := by
      have hval := congrArg Subtype.val hx
      change c.phiL F.hV e = 1 at hval
      exact hval
    have hxker : e ∈ (c.phiL F.hV).ker := hx'
    rw [F.hker] at hxker
    exact ⟨e, hxker, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have hyL : (y : ↥c.L) ∈ CFSG.pCore 2 ↥c.L := hy
    have hφy : c.phiL F.hV (y : ↥c.L) = 1 := by
      rw [← MonoidHom.mem_ker, F.hker]
      exact hyL
    have hxy : e = (y : ↥c.L) := Subtype.ext hyx.symm
    have hval : c.phiL F.hV e = 1 := by
      rw [hxy]
      exact hφy
    apply Subtype.ext
    change c.phiL F.hV e = 1
    exact hval

private theorem phiK_ker_isPGroup {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (F : c.SL3Facts) : IsPGroup 2 (phiK F).ker := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ψ : (phiK F).ker →* ↥(CFSG.Open.pCoreOf 2 c.L) :=
    { toFun := fun x => ⟨(x.1 : G), (phiK_ker_iff F x.1).1 x.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl }
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(CFSG.Open.pCoreOf 2 c.L) => (z : G)) hxy
  exact IsPGroup.of_injective (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L) ψ hψinj

theorem SL3Facts.mem_pCoreOf_K_of_map {D : Data G} {Ch : Choice2011 G}
    {c : Ctx2311 D Ch} (F : c.SL3Facts) {k : G} (hk : k ∈ c.K)
    (h : c.phiL F.hV ⟨k, c.K_le_L hk⟩ ∈
      CFSG.Open.pCoreOf 2 ((c.K.subgroupOf c.L).map (c.phiL F.hV))) :
    k ∈ CFSG.Open.pCoreOf 2 c.K := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : Function.Surjective (phiK F) := phiK_surjective F
  have hker2 : IsPGroup 2 (phiK F).ker := phiK_ker_isPGroup F
  have hmapcore := CFSG.map_pCore_eq_of_surjective_of_isPGroup_ker (phiK F) hf hker2
  have hkstar : phiK F ⟨k, hk⟩ ∈ CFSG.pCore 2 ↥(KStar F) := by
    obtain ⟨y, hy, hyf⟩ := Subgroup.mem_map.mp h
    have hyfk : y = phiK F ⟨k, hk⟩ := Subtype.ext hyf
    rwa [hyfk] at hy
  have hmem : phiK F ⟨k, hk⟩ ∈ (CFSG.pCore 2 ↥c.K).map (phiK F) := by
    rw [hmapcore]
    exact hkstar
  obtain ⟨x, hxcore, hfx⟩ := Subgroup.mem_map.mp hmem
  have hdiffker : (⟨k, hk⟩ : ↥c.K) * x⁻¹ ∈ (phiK F).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hfx]
    exact mul_inv_cancel _
  have hdiffcore : (⟨k, hk⟩ : ↥c.K) * x⁻¹ ∈ CFSG.pCore 2 ↥c.K :=
    CFSG.LieType.BorelTits.le_pCore (r := 2) (phiK F).normal_ker hker2 hdiffker
  have hkcore : (⟨k, hk⟩ : ↥c.K) ∈ CFSG.pCore 2 ↥c.K := by
    have hmul := (CFSG.pCore 2 ↥c.K).mul_mem hdiffcore hxcore
    simpa using hmul
  exact Subgroup.mem_map.mpr ⟨⟨k, hk⟩, hkcore, rfl⟩

private theorem pointCore_trivial {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (F : c.SL3Facts) :
    letI : MulDistribMulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
      MulDistribMulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
    letI : MulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
      MulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
    letI : MulAction ↥(c.H F.hV) (Set (c.toCtx23L.W F.hV)) := Set.mulActionSet
    letI : MulDistribMulAction ↥(c.sylowStar F.hV) (c.toCtx23L.W F.hV) :=
      MulDistribMulAction.compHom (c.toCtx23L.W F.hV)
        ((c.H F.hV).subtype.comp (c.sylowStar F.hV : Subgroup ↥(c.H F.hV)).subtype)
    letI : MulAction ↥(c.sylowStar F.hV) (c.toCtx23L.W F.hV) :=
      MulAction.compHom (c.toCtx23L.W F.hV)
        ((c.H F.hV).subtype.comp (c.sylowStar F.hV : Subgroup ↥(c.H F.hV)).subtype)
    ∀ u ∈ CFSG.Open.pCoreOf 2 ((c.K.subgroupOf c.L).map (c.phiL F.hV)),
      ∀ w : c.toCtx23L.W F.hV,
        w⁻¹ * (u • w) ∈ c.toCtx23L.Ztil F.hV := by
  classical
  letI : MulDistribMulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
  letI : MulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
    MulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
  letI : MulAction ↥(c.H F.hV) (Set (c.toCtx23L.W F.hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar F.hV) (c.toCtx23L.W F.hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W F.hV)
      ((c.H F.hV).subtype.comp (c.sylowStar F.hV : Subgroup ↥(c.H F.hV)).subtype)
  letI : MulAction ↥(c.sylowStar F.hV) (c.toCtx23L.W F.hV) :=
    MulAction.compHom (c.toCtx23L.W F.hV)
      ((c.H F.hV).subtype.comp (c.sylowStar F.hV : Subgroup ↥(c.H F.hV)).subtype)
  let S : Sylow 2 ↥(c.H F.hV) := c.sylowStar F.hV
  let Kstar0 : Subgroup ↥(c.H F.hV) :=
    Hinf (MulAction.stabilizer ↥(c.H F.hV)
      ((fixedPointSubgroup ↥S (c.toCtx23L.W F.hV) : Subgroup (c.toCtx23L.W F.hV)) :
        Set (c.toCtx23L.W F.hV)))
  have hℓ : fixedPointSubgroup ↥S (c.toCtx23L.W F.hV) = c.toCtx23L.Ztil F.hV :=
    fixedPointSubgroup_sylowStar_eq_Ztil_of_sl3 c.toCtx23L F.hV F.h3 F.hSL F.hnat
  have hKstar0 : Kstar0 = (c.K.subgroupOf c.L).map (c.phiL F.hV) := by
    change Hinf (MulAction.stabilizer ↥(c.H F.hV)
      ((fixedPointSubgroup ↥S (c.toCtx23L.W F.hV) : Subgroup (c.toCtx23L.W F.hV)) :
        Set (c.toCtx23L.W F.hV))) = _
    rw [hℓ]
    exact (Ctx23L.map_Hinf_inf_eq c.toCtx23L F.hV F.h4 F.h1930).symm
  have hcore := kSL3PointCore_holds (c.toCtx23L.W F.hV) (c.H F.hV)
    (CFSG.Open.pRank 2 D.Z) F.hSL F.hnat
      (le_trans (by norm_num : 2 ≤ 3) F.h3) S
  intro u hu w
  have hu' : u ∈ CFSG.Open.pCoreOf 2 Kstar0 := by rwa [hKstar0]
  simpa [hℓ] using hcore.1 u hu' w

private theorem pointCore_fpf {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (F : c.SL3Facts) :
    letI : MulDistribMulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
      MulDistribMulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
    letI : MulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
      MulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
    letI : MulAction ↥(c.H F.hV) (Set (c.toCtx23L.W F.hV)) := Set.mulActionSet
    letI : MulDistribMulAction ↥(c.sylowStar F.hV) (c.toCtx23L.W F.hV) :=
      MulDistribMulAction.compHom (c.toCtx23L.W F.hV)
        ((c.H F.hV).subtype.comp (c.sylowStar F.hV : Subgroup ↥(c.H F.hV)).subtype)
    letI : MulAction ↥(c.sylowStar F.hV) (c.toCtx23L.W F.hV) :=
      MulAction.compHom (c.toCtx23L.W F.hV)
        ((c.H F.hV).subtype.comp (c.sylowStar F.hV : Subgroup ↥(c.H F.hV)).subtype)
    ∀ k ∈ (c.K.subgroupOf c.L).map (c.phiL F.hV),
      k ∉ CFSG.Open.pCoreOf 2 ((c.K.subgroupOf c.L).map (c.phiL F.hV)) →
      ∀ r : ℕ, Odd r →
        k ^ r ∈ CFSG.Open.pCoreOf 2 ((c.K.subgroupOf c.L).map (c.phiL F.hV)) →
        ∀ w : c.toCtx23L.W F.hV,
          w⁻¹ * (k • w) ∈ c.toCtx23L.Ztil F.hV → w ∈ c.toCtx23L.Ztil F.hV := by
  classical
  letI : MulDistribMulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
  letI : MulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
    MulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
  letI : MulAction ↥(c.H F.hV) (Set (c.toCtx23L.W F.hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar F.hV) (c.toCtx23L.W F.hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W F.hV)
      ((c.H F.hV).subtype.comp (c.sylowStar F.hV : Subgroup ↥(c.H F.hV)).subtype)
  letI : MulAction ↥(c.sylowStar F.hV) (c.toCtx23L.W F.hV) :=
    MulAction.compHom (c.toCtx23L.W F.hV)
      ((c.H F.hV).subtype.comp (c.sylowStar F.hV : Subgroup ↥(c.H F.hV)).subtype)
  let S : Sylow 2 ↥(c.H F.hV) := c.sylowStar F.hV
  let Kstar0 : Subgroup ↥(c.H F.hV) :=
    Hinf (MulAction.stabilizer ↥(c.H F.hV)
      ((fixedPointSubgroup ↥S (c.toCtx23L.W F.hV) : Subgroup (c.toCtx23L.W F.hV)) :
        Set (c.toCtx23L.W F.hV)))
  have hℓ : fixedPointSubgroup ↥S (c.toCtx23L.W F.hV) = c.toCtx23L.Ztil F.hV :=
    fixedPointSubgroup_sylowStar_eq_Ztil_of_sl3 c.toCtx23L F.hV F.h3 F.hSL F.hnat
  have hKstar0 : Kstar0 = (c.K.subgroupOf c.L).map (c.phiL F.hV) := by
    change Hinf (MulAction.stabilizer ↥(c.H F.hV)
      ((fixedPointSubgroup ↥S (c.toCtx23L.W F.hV) : Subgroup (c.toCtx23L.W F.hV)) :
        Set (c.toCtx23L.W F.hV))) = _
    rw [hℓ]
    exact (Ctx23L.map_Hinf_inf_eq c.toCtx23L F.hV F.h4 F.h1930).symm
  have hcore := kSL3PointCore_holds (c.toCtx23L.W F.hV) (c.H F.hV)
    (CFSG.Open.pRank 2 D.Z) F.hSL F.hnat
      (le_trans (by norm_num : 2 ≤ 3) F.h3) S
  intro k hk hkU r hr hkr w hw
  have hk0 : k ∈ Kstar0 := by rwa [hKstar0]
  have hkU0 : k ∉ CFSG.Open.pCoreOf 2 Kstar0 := by rwa [hKstar0]
  have hkr0 : k ^ r ∈ CFSG.Open.pCoreOf 2 Kstar0 := by rwa [hKstar0]
  have hw0 : w⁻¹ * (k • w) ∈ fixedPointSubgroup ↥S (c.toCtx23L.W F.hV) := by
    rwa [hℓ]
  have h := hcore.2.1 k hk0 hkU0 r hr hkr0 w hw0
  rwa [hℓ] at h

private theorem pointCore_irreducible {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (F : c.SL3Facts) :
    letI : MulDistribMulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
      MulDistribMulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
    letI : MulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
      MulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
    letI : MulAction ↥(c.H F.hV) (Set (c.toCtx23L.W F.hV)) := Set.mulActionSet
    letI : MulDistribMulAction ↥(c.sylowStar F.hV) (c.toCtx23L.W F.hV) :=
      MulDistribMulAction.compHom (c.toCtx23L.W F.hV)
        ((c.H F.hV).subtype.comp (c.sylowStar F.hV : Subgroup ↥(c.H F.hV)).subtype)
    letI : MulAction ↥(c.sylowStar F.hV) (c.toCtx23L.W F.hV) :=
      MulAction.compHom (c.toCtx23L.W F.hV)
        ((c.H F.hV).subtype.comp (c.sylowStar F.hV : Subgroup ↥(c.H F.hV)).subtype)
    ∀ N : Subgroup ↥(c.H F.hV),
      N ≤ CFSG.Open.pCoreOf 2 ((c.K.subgroupOf c.L).map (c.phiL F.hV)) → N ≠ ⊥ →
      (∀ k ∈ (c.K.subgroupOf c.L).map (c.phiL F.hV), ∀ x ∈ N, k * x * k⁻¹ ∈ N) →
        N = CFSG.Open.pCoreOf 2 ((c.K.subgroupOf c.L).map (c.phiL F.hV)) := by
  classical
  letI : MulDistribMulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
  letI : MulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
    MulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
  letI : MulAction ↥(c.H F.hV) (Set (c.toCtx23L.W F.hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar F.hV) (c.toCtx23L.W F.hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W F.hV)
      ((c.H F.hV).subtype.comp (c.sylowStar F.hV : Subgroup ↥(c.H F.hV)).subtype)
  letI : MulAction ↥(c.sylowStar F.hV) (c.toCtx23L.W F.hV) :=
    MulAction.compHom (c.toCtx23L.W F.hV)
      ((c.H F.hV).subtype.comp (c.sylowStar F.hV : Subgroup ↥(c.H F.hV)).subtype)
  let S : Sylow 2 ↥(c.H F.hV) := c.sylowStar F.hV
  let Kstar0 : Subgroup ↥(c.H F.hV) :=
    Hinf (MulAction.stabilizer ↥(c.H F.hV)
      ((fixedPointSubgroup ↥S (c.toCtx23L.W F.hV) : Subgroup (c.toCtx23L.W F.hV)) :
        Set (c.toCtx23L.W F.hV)))
  have hℓ : fixedPointSubgroup ↥S (c.toCtx23L.W F.hV) = c.toCtx23L.Ztil F.hV :=
    fixedPointSubgroup_sylowStar_eq_Ztil_of_sl3 c.toCtx23L F.hV F.h3 F.hSL F.hnat
  have hKstar0 : Kstar0 = (c.K.subgroupOf c.L).map (c.phiL F.hV) := by
    change Hinf (MulAction.stabilizer ↥(c.H F.hV)
      ((fixedPointSubgroup ↥S (c.toCtx23L.W F.hV) : Subgroup (c.toCtx23L.W F.hV)) :
        Set (c.toCtx23L.W F.hV))) = _
    rw [hℓ]
    exact (Ctx23L.map_Hinf_inf_eq c.toCtx23L F.hV F.h4 F.h1930).symm
  have hcore := kSL3PointCore_holds (c.toCtx23L.W F.hV) (c.H F.hV)
    (CFSG.Open.pRank 2 D.Z) F.hSL F.hnat
      (le_trans (by norm_num : 2 ≤ 3) F.h3) S
  intro N hN hNne hNnorm
  have hN0 : N ≤ CFSG.Open.pCoreOf 2 Kstar0 := by rwa [hKstar0]
  have hNnorm0 : ∀ k ∈ Kstar0, ∀ x ∈ N, k * x * k⁻¹ ∈ N := by
    intro k hk x hx
    exact hNnorm k (by rwa [hKstar0] at hk) x hx
  have h := hcore.2.2 N hN0 hNne hNnorm0
  have h' : N = CFSG.Open.pCoreOf 2 Kstar0 := h
  rw [hKstar0] at h'
  exact h'

private theorem inv_mul_phiL_mkTil_eq {D : Data G} {Ch : Choice2011 G}
    {c : Ctx2311 D Ch} (F : c.SL3Facts) (e : ↥c.L) (vI zI : IntMod c.V F.hV)
    (hval : zI.val = ⁅vI.val⁻¹, (e : G)⁆) :
    (mkTil (⊥ : Subgroup G) c.V F.hV vI)⁻¹ *
        ((c.phiL F.hV e : MulAut (c.toCtx23L.W F.hV))
          (mkTil (⊥ : Subgroup G) c.V F.hV vI)) =
      mkTil (⊥ : Subgroup G) c.V F.hV zI := by
  have hphi : (c.phiL F.hV e : MulAut (c.toCtx23L.W F.hV))
      (mkTil (⊥ : Subgroup G) c.V F.hV vI) =
      mkTil (⊥ : Subgroup G) c.V F.hV
        (actStab (⊥ : Subgroup G) c.V F.hV ⟨e, c.L_le_stabTil e.2⟩ vI) :=
    c.toCtx23L.phiL_apply_mkTil F.hV e vI
  rw [hphi, ← map_inv, ← map_mul]
  congr 1
  apply IntMod.val_injective
  rw [IntMod.val_mul, IntMod.val_inv, actStab_apply_val, hval]
  group

private theorem commutator_mem_Z_of_pCoreOf_V {D : Data G} {Ch : Choice2011 G}
    {c : Ctx2311 D Ch} (F : c.SL3Facts) {u v : G}
    (hu : u ∈ CFSG.Open.pCoreOf 2 c.K) (hv : v ∈ c.V) : ⁅u, v⁆ ∈ D.Z := by
  classical
  letI : MulDistribMulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
  letI : MulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
    MulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
  letI : MulAction ↥(c.H F.hV) (Set (c.toCtx23L.W F.hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar F.hV) (c.toCtx23L.W F.hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W F.hV)
      ((c.H F.hV).subtype.comp (c.sylowStar F.hV : Subgroup ↥(c.H F.hV)).subtype)
  letI : MulAction ↥(c.sylowStar F.hV) (c.toCtx23L.W F.hV) :=
    MulAction.compHom (c.toCtx23L.W F.hV)
      ((c.H F.hV).subtype.comp (c.sylowStar F.hV : Subgroup ↥(c.H F.hV)).subtype)
  have hU := pointCore_trivial F
  have huK : u ∈ c.K := CFSG.LieType.BorelTits.pCoreOf_le 2 c.K hu
  let e : ↥c.L := ⟨u, c.K_le_L huK⟩
  let vI : IntMod c.V F.hV := IntMod.mk F.hV ⟨v, hv⟩
  let w : c.toCtx23L.W F.hV := mkTil (⊥ : Subgroup G) c.V F.hV vI
  have hmem : w⁻¹ * (c.phiL F.hV e • w) ∈ c.toCtx23L.Ztil F.hV :=
    hU (c.phiL F.hV e)
      (phiL_mem_pCoreOf (c := c) (hV := F.hV) hu) w
  rw [Ctx23L.Ztil, mem_imgTil] at hmem
  obtain ⟨x, hxZ, hxeq⟩ := hmem
  have hyV : ⁅v⁻¹, u⁆ ∈ c.V :=
    Subgroup.commutator_le.mp c.commutator_V_K_le_V v⁻¹ (c.V.inv_mem hv) u huK
  let y : IntMod c.V F.hV := IntMod.mk F.hV ⟨⁅v⁻¹, u⁆, hyV⟩
  have hright : w⁻¹ * (c.phiL F.hV e • w) = mkTil (⊥ : Subgroup G) c.V F.hV y := by
    rw [show c.phiL F.hV e • w =
      (c.phiL F.hV e : MulAut (c.toCtx23L.W F.hV)) w from rfl]
    simpa [w] using inv_mul_phiL_mkTil_eq F e vI y (by rfl)
  have hxy : x = y := by
    apply IntMod.val_injective
    have hmem1 : x.val * y.val⁻¹ ∈ (⊥ : Subgroup G) :=
      (mkTil_eq_iff (⊥ : Subgroup G) c.V F.hV x y).mp (hxeq.trans hright)
    exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem1)
  have hyZ : y.val ∈ D.Z := by
    rw [hxy] at hxZ
    exact hxZ
  have hcomm : ⁅u, v⁆ = v * y.val * v⁻¹ := by
    simp only [y, IntMod.mk, IntMod.val, commutatorElement_def]
    group
  have hconj : v * y.val * v⁻¹ = y.val := by
    have hcommV : v * y.val = y.val * v :=
      congrArg Subtype.val (F.hV.1.is_comm.comm ⟨v, hv⟩ ⟨y.val, hyV⟩)
    calc v * y.val * v⁻¹ = (y.val * v) * v⁻¹ := by rw [hcommV]
      _ = y.val := by group
  rw [hcomm, hconj]
  exact hyZ

private theorem commutator_mem_Z_of_pCoreOf_conj {D : Data G} {Ch : Choice2011 G}
    {c : Ctx2311 D Ch} (F : c.SL3Facts) {u : G}
    (hu : u ∈ CFSG.Open.pCoreOf 2 c.K) {g : G} (hg : g ∈ D.M) {v : G}
    (hv : v ∈ c.V) :
    ⁅u, (MulEquiv.toMonoidHom (MulAut.conj g)) v⁆ ∈ D.Z := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have huK : u ∈ c.K := CFSG.LieType.BorelTits.pCoreOf_le 2 c.K hu
  have hZM : D.M ≤ Subgroup.normalizer (D.Z : Set G) := by
    rw [F.normalizer_Z_eq]
  have hu' : g⁻¹ * u * g ∈ CFSG.Open.pCoreOf 2 c.K := by
    have hmem : (MulAut.conj g⁻¹) u ∈ (CFSG.Open.pCoreOf 2 c.K).map
        (MulAut.conj g⁻¹).toMonoidHom := Subgroup.mem_map_of_mem _ hu
    have hKmap : c.K.map (MulAut.conj g⁻¹).toMonoidHom = c.K := by
      have hKM : c.K ≤ D.M := (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_left
      have hMN : D.M ≤ Subgroup.normalizer (c.K : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp (F.h12 F.h1930 c)
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hMN (D.M.inv_mem hg))
    have hmap := CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv (r := 2)
      (MulAut.conj g⁻¹) c.K
    rw [hKmap] at hmap
    rw [hmap]
    simpa [MulAut.conj_apply] using hmem
  have hcomm' : ⁅g⁻¹ * u * g, v⁆ ∈ D.Z := commutator_mem_Z_of_pCoreOf_V F hu' hv
  have hcommZ : g * ⁅g⁻¹ * u * g, v⁆ * g⁻¹ ∈ D.Z :=
    (Subgroup.mem_normalizer_iff.mp (hZM hg) ⁅g⁻¹ * u * g, v⁆).mp hcomm'
  have heq : ⁅u, (MulEquiv.toMonoidHom (MulAut.conj g)) v⁆ =
      g * ⁅g⁻¹ * u * g, v⁆ * g⁻¹ := by
    simp [MulAut.conj_apply, commutatorElement_def]
    group
  rw [heq]
  exact hcommZ

theorem SL3Facts.commutator_mem_Z_of_pCoreOf {D : Data G} {Ch : Choice2011 G}
    {c : Ctx2311 D Ch} (F : c.SL3Facts) {u : G}
    (hu : u ∈ CFSG.Open.pCoreOf 2 c.K) {x : G} (hx : x ∈ c.E) : ⁅u, x⁆ ∈ D.Z := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have huK : u ∈ c.K := CFSG.LieType.BorelTits.pCoreOf_le 2 c.K hu
  have hEM : c.E ≤ D.M :=
    (c.E_le_pCoreOf_M F.h1930 F.h4 F.h12 F.hN8).trans
      (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)
  have hZM : D.M ≤ Subgroup.normalizer (D.Z : Set G) := by
    rw [F.normalizer_Z_eq]
  have hEeq : c.E = ⨆ g : ↥D.M, c.V.map (MulAut.conj (g : G)).toMonoidHom := by
    rw [Ctx23L.E]
    exact uc22br4_conjClosure_eq D.M c.V
  have hgen : ∀ a ∈ ⋃ g : ↥D.M,
      ((c.V.map (MulAut.conj (g : G)).toMonoidHom : Subgroup G) : Set G),
      a ∈ Subgroup.normalizer (D.Z : Set G) ∧ ⁅u, a⁆ ∈ D.Z := by
    intro a ha
    obtain ⟨g, hg⟩ := Set.mem_iUnion.mp ha
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hg
    have hgM : (g : G) ∈ D.M := g.2
    have hmemE : (MulAut.conj (g : G)) v ∈ c.E := by
      rw [hEeq]
      exact Subgroup.mem_iSup_of_mem g (Subgroup.mem_map_of_mem _ hv)
    exact ⟨hZM (hEM hmemE), commutator_mem_Z_of_pCoreOf_conj F hu hgM hv⟩
  have hxcl : x ∈ Subgroup.closure (⋃ g : ↥D.M,
      ((c.V.map (MulAut.conj (g : G)).toMonoidHom : Subgroup G) : Set G)) := by
    rw [← Subgroup.iSup_eq_closure, ← hEeq]
    exact hx
  exact commutator_mem_of_mem_closure (fun a ha => (hgen a ha).1)
    (fun a ha => (hgen a ha).2) x hxcl

private theorem K_conj_mem {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (F : c.SL3Facts) {k g : G} (hk : k ∈ c.K) (hg : g ∈ D.M) : g * k * g⁻¹ ∈ c.K := by
  have hKM : c.K ≤ D.M := (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_left
  have hMN : D.M ≤ Subgroup.normalizer (c.K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp (F.h12 F.h1930 c)
  exact (Subgroup.mem_normalizer_iff.mp (hMN hg) k).mp hk

private theorem pCoreOf_conj_mem {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (F : c.SL3Facts) {k g : G} (hk : k ∈ CFSG.Open.pCoreOf 2 c.K) (hg : g ∈ D.M) :
    g * k * g⁻¹ ∈ CFSG.Open.pCoreOf 2 c.K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKM : c.K ≤ D.M := (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_left
  have hMN : D.M ≤ Subgroup.normalizer (c.K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp (F.h12 F.h1930 c)
  have hKmap : c.K.map (MulAut.conj g).toMonoidHom = c.K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hMN hg)
  have hmap := CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv (r := 2)
    (MulAut.conj g) c.K
  rw [hKmap] at hmap
  rw [hmap]
  simpa [MulAut.conj_apply] using
    (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hk)

private theorem K_mem_normalizer_conj_V {D : Data G} {Ch : Choice2011 G}
    {c : Ctx2311 D Ch} (F : c.SL3Facts) {k g : G} (hk : k ∈ c.K) (hg : g ∈ D.M) :
    k ∈ Subgroup.normalizer
      ((c.V.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
    have hKG : g⁻¹ * k * g ∈ c.K := by
      simpa using K_conj_mem F hk (D.M.inv_mem hg)
    have hw' : (g⁻¹ * k * g) * w * (g⁻¹ * k * g)⁻¹ ∈ c.V :=
      (Subgroup.mem_normalizer_iff.mp (c.K_le_normalizer_V hKG) w).mp hw
    refine Subgroup.mem_map.mpr
      ⟨(g⁻¹ * k * g) * w * (g⁻¹ * k * g)⁻¹, hw', ?_⟩
    simp [MulAut.conj_apply]
    group
  · intro hy
    obtain ⟨w, hw, hw_eq⟩ := Subgroup.mem_map.mp hy
    have hKG : g⁻¹ * k⁻¹ * g ∈ c.K := by
      simpa using K_conj_mem F (c.K.inv_mem hk) (D.M.inv_mem hg)
    have hw' : (g⁻¹ * k⁻¹ * g) * w * (g⁻¹ * k⁻¹ * g)⁻¹ ∈ c.V :=
      (Subgroup.mem_normalizer_iff.mp (c.K_le_normalizer_V hKG) w).mp hw
    refine Subgroup.mem_map.mpr
      ⟨(g⁻¹ * k⁻¹ * g) * w * (g⁻¹ * k⁻¹ * g)⁻¹, hw', ?_⟩
    have hw_eq' : g * w * g⁻¹ = k * y * k⁻¹ := by
      simpa [MulAut.conj_apply] using hw_eq
    have hy' : y = k⁻¹ * (g * w * g⁻¹) * k := by
      calc y = k⁻¹ * (k * y * k⁻¹) * k := by group
        _ = k⁻¹ * (g * w * g⁻¹) * k := by rw [hw_eq']
    rw [hy']
    simp [MulAut.conj_apply]
    group

private theorem mem_Ztil_of_commutator_mem_V {D : Data G} {Ch : Choice2011 G}
    {c : Ctx2311 D Ch} (F : c.SL3Facts) (e : ↥c.L) {v : G} (hv : v ∈ c.V)
    (hcomm : ⁅(e : G), v⁆ ∈ D.Z) :
    (mkTil (⊥ : Subgroup G) c.V F.hV (IntMod.mk F.hV ⟨v, hv⟩))⁻¹ *
        ((c.phiL F.hV e : MulAut (c.toCtx23L.W F.hV))
          (mkTil (⊥ : Subgroup G) c.V F.hV (IntMod.mk F.hV ⟨v, hv⟩))) ∈
      c.toCtx23L.Ztil F.hV := by
  have hZleV : D.Z ≤ c.V := uc22p22v_le_conjClosure c.N D.Z
  have hcommZ : ⁅v⁻¹, (e : G)⁆ ∈ D.Z := by
    have hv' : v⁻¹ * ⁅(e : G), v⁆ * v = ⁅(e : G), v⁆ := by
      have hcv : v⁻¹ * ⁅(e : G), v⁆ = ⁅(e : G), v⁆ * v⁻¹ :=
        congrArg Subtype.val
          (F.hV.1.is_comm.comm ⟨v⁻¹, c.V.inv_mem hv⟩ ⟨⁅(e : G), v⁆, hZleV hcomm⟩)
      calc v⁻¹ * ⁅(e : G), v⁆ * v = (⁅(e : G), v⁆ * v⁻¹) * v := by rw [hcv]
        _ = ⁅(e : G), v⁆ := by group
    rw [show ⁅v⁻¹, (e : G)⁆ = v⁻¹ * ⁅(e : G), v⁆ * v by group, hv']
    exact hcomm
  let vI : IntMod c.V F.hV := IntMod.mk F.hV ⟨v, hv⟩
  let zI : IntMod c.V F.hV := IntMod.mk F.hV ⟨⁅v⁻¹, (e : G)⁆, hZleV hcommZ⟩
  have hright := inv_mul_phiL_mkTil_eq F e vI zI (by rfl)
  rw [Ctx23L.Ztil, mem_imgTil]
  exact ⟨zI, hcommZ, hright.symm⟩

private theorem mem_Z_of_mem_Ztil {D : Data G} {Ch : Choice2011 G}
    {c : Ctx2311 D Ch} (F : c.SL3Facts) {v : G} (hv : v ∈ c.V)
    {vI : IntMod c.V F.hV} (hvI : vI.val = v)
    (h : mkTil (⊥ : Subgroup G) c.V F.hV vI ∈ c.toCtx23L.Ztil F.hV) :
    v ∈ D.Z := by
  rw [Ctx23L.Ztil, mem_imgTil] at h
  obtain ⟨z, hzZ, hzeq⟩ := h
  have hvz : vI = z := by
    apply IntMod.val_injective
    have hmem1 : vI.val * z.val⁻¹ ∈ (⊥ : Subgroup G) :=
      (mkTil_eq_iff (⊥ : Subgroup G) c.V F.hV vI z).mp hzeq.symm
    exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem1)
  have hvval : v = z.val := by
    have := congrArg IntMod.val hvz
    simpa [hvI] using this
  rw [hvval]
  exact hzZ

private theorem mem_Z_of_commutator_mem_V {D : Data G} {Ch : Choice2011 G}
    {c : Ctx2311 D Ch} (F : c.SL3Facts) {k v : G} (hk : k ∈ c.K)
    (hkO : k ∉ CFSG.Open.pCoreOf 2 c.K) {r : ℕ} (hr : Odd r)
    (hkr : k ^ r ∈ CFSG.Open.pCoreOf 2 c.K) (hv : v ∈ c.V)
    (hcomm : ⁅k, v⁆ ∈ D.Z) : v ∈ D.Z := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulDistribMulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
  letI : MulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
    MulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
  letI : MulAction ↥(c.H F.hV) (Set (c.toCtx23L.W F.hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar F.hV) (c.toCtx23L.W F.hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W F.hV)
      ((c.H F.hV).subtype.comp (c.sylowStar F.hV : Subgroup ↥(c.H F.hV)).subtype)
  letI : MulAction ↥(c.sylowStar F.hV) (c.toCtx23L.W F.hV) :=
    MulAction.compHom (c.toCtx23L.W F.hV)
      ((c.H F.hV).subtype.comp (c.sylowStar F.hV : Subgroup ↥(c.H F.hV)).subtype)
  have hfpf := pointCore_fpf F
  let e : ↥c.L := ⟨k, c.K_le_L hk⟩
  let vI : IntMod c.V F.hV := IntMod.mk F.hV ⟨v, hv⟩
  let w : c.toCtx23L.W F.hV := mkTil (⊥ : Subgroup G) c.V F.hV vI
  have hmemZ : w⁻¹ * (c.phiL F.hV e • w) ∈ c.toCtx23L.Ztil F.hV := by
    rw [show c.phiL F.hV e • w =
      (c.phiL F.hV e : MulAut (c.toCtx23L.W F.hV)) w from rfl]
    simpa [w] using mem_Ztil_of_commutator_mem_V F e hv (by simpa [e] using hcomm)
  have hke : e ∈ c.K.subgroupOf c.L :=
    Subgroup.mem_subgroupOf.mpr (by simpa [e] using hk)
  have hkstar : c.phiL F.hV e ∈ (c.K.subgroupOf c.L).map (c.phiL F.hV) :=
    Subgroup.mem_map_of_mem _ hke
  have hkU : c.phiL F.hV e ∉
      CFSG.Open.pCoreOf 2 ((c.K.subgroupOf c.L).map (c.phiL F.hV)) := by
    intro h
    exact hkO (F.mem_pCoreOf_K_of_map hk h)
  have hkrstar : (c.phiL F.hV e) ^ r ∈
      CFSG.Open.pCoreOf 2 ((c.K.subgroupOf c.L).map (c.phiL F.hV)) := by
    have hkrmem : k ^ r ∈ c.K := c.K.pow_mem hk r
    have hmain := phiL_mem_pCoreOf (c := c) (hV := F.hV)
      (x := ⟨k ^ r, c.K_le_L hkrmem⟩) hkr
    have hsub : (⟨k ^ r, c.K_le_L hkrmem⟩ : ↥c.L) = e ^ r := Subtype.ext rfl
    rw [hsub, map_pow] at hmain
    exact hmain
  have hwZ := hfpf (c.phiL F.hV e) hkstar hkU r hr hkrstar w hmemZ
  exact mem_Z_of_mem_Ztil F (vI := vI) hv rfl (by simpa [w] using hwZ)

private theorem mem_Z_of_commutator_mem_of_conj {D : Data G} {Ch : Choice2011 G}
    {c : Ctx2311 D Ch} (F : c.SL3Facts) {k v g : G} (hk : k ∈ c.K)
    (hkO : k ∉ CFSG.Open.pCoreOf 2 c.K) {r : ℕ} (hr : Odd r)
    (hkr : k ^ r ∈ CFSG.Open.pCoreOf 2 c.K) (hg : g ∈ D.M) (hv : v ∈ c.V)
    (hcomm : ⁅k, (MulEquiv.toMonoidHom (MulAut.conj g)) v⁆ ∈ D.Z) : v ∈ D.Z := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZM : D.M ≤ Subgroup.normalizer (D.Z : Set G) := by
    rw [F.normalizer_Z_eq]
  have hk' : g⁻¹ * k * g ∈ c.K := by
    simpa using K_conj_mem F hk (D.M.inv_mem hg)
  have hk'O : g⁻¹ * k * g ∉ CFSG.Open.pCoreOf 2 c.K := by
    intro hmem
    have hkback : k ∈ CFSG.Open.pCoreOf 2 c.K := by
      have h := pCoreOf_conj_mem F hmem hg
      simpa [mul_assoc] using h
    exact hkO hkback
  have hkr' : (g⁻¹ * k * g) ^ r ∈ CFSG.Open.pCoreOf 2 c.K := by
    have h := pCoreOf_conj_mem F hkr (D.M.inv_mem hg)
    have hpow : (g⁻¹ * k * g) ^ r = g⁻¹ * k ^ r * g := by
      simpa [MulAut.conj_apply] using (map_pow (MulAut.conj g⁻¹) k r).symm
    rw [hpow]
    simpa [inv_inv] using h
  have hcomm' : ⁅g⁻¹ * k * g, v⁆ ∈ D.Z := by
    have heq : ⁅g⁻¹ * k * g, v⁆ =
        g⁻¹ * ⁅k, (MulEquiv.toMonoidHom (MulAut.conj g)) v⁆ * g := by
      simp [MulAut.conj_apply, commutatorElement_def]
      group
    rw [heq]
    have h := (Subgroup.mem_normalizer_iff.mp (hZM (D.M.inv_mem hg))
      ⁅k, (MulEquiv.toMonoidHom (MulAut.conj g)) v⁆).mp hcomm
    simpa [inv_inv] using h
  exact mem_Z_of_commutator_mem_V F hk' hk'O hr hkr' hv hcomm'

theorem SL3Facts.mem_Z_of_commutator_mem {D : Data G} {Ch : Choice2011 G}
    {c : Ctx2311 D Ch} (F : c.SL3Facts) {k : G} (hk : k ∈ c.K)
    (hkO : k ∉ CFSG.Open.pCoreOf 2 c.K) {r : ℕ} (hr : Odd r)
    (hkr : k ^ r ∈ CFSG.Open.pCoreOf 2 c.K) :
    ∀ x ∈ c.E, ⁅k, x⁆ ∈ D.Z → x ∈ D.Z := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKM : c.K ≤ D.M := (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_left
  have hkM : k ∈ D.M := hKM hk
  have hZM : D.M ≤ Subgroup.normalizer (D.Z : Set G) := by
    rw [F.normalizer_Z_eq]
  let f : ↥D.M → Subgroup G := fun g => c.V.map (MulAut.conj (g : G)).toMonoidHom
  have hEeq : c.E = ⨆ g, f g := by
    rw [Ctx23L.E]
    exact uc22br4_conjClosure_eq D.M c.V
  have hB : c.E = ⨆ A ∈ Set.range f, A := by
    rw [hEeq]
    exact (iSup_range (f := f) (g := fun A : Subgroup G => A)).symm
  have hZB : D.Z ≤ c.E :=
    (uc22p22v_le_conjClosure c.N D.Z).trans (uc22p22v_le_conjClosure D.M c.V)
  have hdV : k ∈ Subgroup.normalizer (D.Z : Set G) := by
    rw [F.normalizer_Z_eq]
    exact hkM
  have hdS : ∀ A ∈ Set.range f, k ∈ Subgroup.normalizer ((A : Subgroup G) : Set G) := by
    rintro A ⟨g, rfl⟩
    exact K_mem_normalizer_conj_V F hk g.2
  have hfree : ∀ A ∈ Set.range f, ∀ x ∈ A,
      k * x * k⁻¹ * x⁻¹ ∈ D.Z → x ∈ D.Z := by
    rintro A ⟨g, rfl⟩ x hx hcomm
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hx
    have hvZ := mem_Z_of_commutator_mem_of_conj F hk hkO hr hkr g.2 hv hcomm
    have := (Subgroup.mem_normalizer_iff.mp (hZM g.2) v).mp hvZ
    simpa [MulAut.conj_apply] using this
  exact mem_of_conj_mem_of_iSup hB F.hEE hZB hdV hdS hfree

private theorem map_E_le {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (F : c.SL3Facts) :
    (c.E.subgroupOf c.L).map (c.phiL F.hV) ≤
      CFSG.Open.pCoreOf 2 ((c.K.subgroupOf c.L).map (c.phiL F.hV)) := by
  have hEpK : c.E ≤ CFSG.Open.pCoreOf 2 c.K :=
    (le_pCoreOf_parts c F.h1930 F.h4 F.h12 F.hN8 F.hker).1
  rintro _ ⟨e, he, rfl⟩
  exact phiL_mem_pCoreOf (c := c) (hV := F.hV) (hEpK (Subgroup.mem_subgroupOf.mp he))

private theorem E_le_centralizer_of_map_eq_bot {D : Data G} {Ch : Choice2011 G}
    {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (hbot : (c.E.subgroupOf c.L).map (c.phiL F.hV) = ⊥) :
    c.E ≤ Subgroup.centralizer (c.V : Set G) := by
  have hEL : c.E ≤ c.L :=
    (le_pCoreOf_parts c F.h1930 F.h4 F.h12 F.hN8 F.hker).1.trans
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 c.K).trans c.K_le_L)
  intro e he
  let eL : ↥c.L := ⟨e, hEL he⟩
  have heL : eL ∈ c.E.subgroupOf c.L := Subgroup.mem_subgroupOf.mpr he
  have hφe : c.phiL F.hV eL = 1 := by
    have hmem : c.phiL F.hV eL ∈ (c.E.subgroupOf c.L).map (c.phiL F.hV) :=
      Subgroup.mem_map_of_mem _ heL
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hcent := (c.toCtx23L.phiL_eq_one_iff F.hV eL).mp hφe
  simpa [eL] using hcent

private theorem conj_V_pairwise_commute {D : Data G} {Ch : Choice2011 G}
    {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (hcent : c.E ≤ Subgroup.centralizer (c.V : Set G)) :
    ∀ g h : ↥D.M, ∀ a ∈ c.V.map (MulAut.conj (g : G)).toMonoidHom,
      ∀ b ∈ c.V.map (MulAut.conj (h : G)).toMonoidHom, a * b = b * a := by
  have hEeq : c.E = ⨆ g : ↥D.M, c.V.map (MulAut.conj (g : G)).toMonoidHom := by
    rw [Ctx23L.E]
    exact uc22br4_conjClosure_eq D.M c.V
  have hEMnorm : D.M ≤ Subgroup.normalizer (c.E : Set G) :=
    uc22p22v_le_normalizer_conjClosure D.M c.V
  rintro g h a ⟨va, hva, rfl⟩ b ⟨vb, hvb, rfl⟩
  have haE : (MulAut.conj (g : G)) va ∈ c.E := by
    rw [hEeq]
    exact Subgroup.mem_iSup_of_mem g (Subgroup.mem_map_of_mem _ hva)
  have hhE : (MulAut.conj (h : G)⁻¹) ((MulAut.conj (g : G)) va) ∈ c.E :=
    (Subgroup.mem_normalizer_iff.mp (hEMnorm (D.M.inv_mem h.2))
      ((MulAut.conj (g : G)) va)).mp haE
  have hcv : (MulAut.conj (h : G)⁻¹) ((MulAut.conj (g : G)) va) * vb =
      vb * (MulAut.conj (h : G)⁻¹) ((MulAut.conj (g : G)) va) :=
    (Subgroup.mem_centralizer_iff.mp (hcent hhE) vb hvb).symm
  calc (MulAut.conj (g : G)) va * (MulAut.conj (h : G)) vb
      = (h : G) * ((MulAut.conj (h : G)⁻¹) ((MulAut.conj (g : G)) va) * vb) *
          (h : G)⁻¹ := by
        simp [MulAut.conj_apply]
        group
    _ = (h : G) * (vb * (MulAut.conj (h : G)⁻¹) ((MulAut.conj (g : G)) va)) *
          (h : G)⁻¹ := by rw [hcv]
    _ = (MulAut.conj (h : G)) vb * (MulAut.conj (g : G)) va := by
        simp [MulAut.conj_apply]
        group

private theorem isElemAbelian_E_of_le_centralizer {D : Data G} {Ch : Choice2011 G}
    {c : Ctx2311 D Ch} (F : c.SL3Facts)
    (hcent : c.E ≤ Subgroup.centralizer (c.V : Set G)) : IsElemAbelian 2 c.E := by
  have hEeq : c.E = ⨆ g : ↥D.M, c.V.map (MulAut.conj (g : G)).toMonoidHom := by
    rw [Ctx23L.E]
    exact uc22br4_conjClosure_eq D.M c.V
  rw [hEeq]
  exact CFSG.Quasithin.CosetGeom.isElemAbelian_iSup
    (fun g : ↥D.M => c.V.map (MulAut.conj (g : G)).toMonoidHom)
    (fun g => F.hV.map _) (conj_V_pairwise_commute F hcent)

private theorem map_E_ne_bot {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (F : c.SL3Facts) : (c.E.subgroupOf c.L).map (c.phiL F.hV) ≠ ⊥ := by
  intro hbot
  have hcent := E_le_centralizer_of_map_eq_bot F hbot
  have hEel := isElemAbelian_E_of_le_centralizer F hcent
  haveI : Fact (IsPGroup 2 ↥c.E) :=
    ⟨c.isPGroup_E F.h1930 F.h4 F.h12 F.hN8⟩
  have hphi : frattini ↥c.E = ⊥ :=
    (CFSG.frattini_eq_bot_iff_isElementaryAbelian (R := ↥c.E) (p := 2)).mpr
      hEel.isElementaryAbelian
  exact (F.h14 F.h1930 c) hphi

private theorem map_E_invariant {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (F : c.SL3Facts) :
    ∀ k ∈ (c.K.subgroupOf c.L).map (c.phiL F.hV),
      ∀ x ∈ (c.E.subgroupOf c.L).map (c.phiL F.hV),
        k * x * k⁻¹ ∈ (c.E.subgroupOf c.L).map (c.phiL F.hV) := by
  have hKM : c.K ≤ D.M := (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_left
  have hEL : c.E ≤ c.L :=
    (le_pCoreOf_parts c F.h1930 F.h4 F.h12 F.hN8 F.hker).1.trans
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 c.K).trans c.K_le_L)
  have hEMnorm : D.M ≤ Subgroup.normalizer (c.E : Set G) :=
    uc22p22v_le_normalizer_conjClosure D.M c.V
  intro k hk x hx
  obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨kk, hkk, rfl⟩ := Subgroup.mem_map.mp hk
  have hxE : (e : G) ∈ c.E := Subgroup.mem_subgroupOf.mp he
  have hkkM : (kk : G) ∈ D.M := hKM (Subgroup.mem_subgroupOf.mp hkk)
  have hconjE : (kk : G) * (e : G) * (kk : G)⁻¹ ∈ c.E :=
    (Subgroup.mem_normalizer_iff.mp (hEMnorm hkkM) (e : G)).mp hxE
  refine Subgroup.mem_map.mpr ⟨⟨(kk : G) * (e : G) * (kk : G)⁻¹, hEL hconjE⟩, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mpr hconjE
  · have harg : (⟨(kk : G) * (e : G) * (kk : G)⁻¹, hEL hconjE⟩ : ↥c.L) =
        kk * e * kk⁻¹ := Subtype.ext rfl
    rw [harg, map_mul, map_mul, map_inv]

theorem SL3Facts.map_E_eq {D : Data G} {Ch : Choice2011 G} {c : Ctx2311 D Ch}
    (F : c.SL3Facts) :
    (c.E.subgroupOf c.L).map (c.phiL F.hV) =
      CFSG.Open.pCoreOf 2 ((c.K.subgroupOf c.L).map (c.phiL F.hV)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNle := map_E_le F
  have hNne := map_E_ne_bot F
  letI : MulDistribMulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
  letI : MulAction ↥(c.H F.hV) (c.toCtx23L.W F.hV) :=
    MulAction.compHom (c.toCtx23L.W F.hV) (c.H F.hV).subtype
  letI : MulAction ↥(c.H F.hV) (Set (c.toCtx23L.W F.hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar F.hV) (c.toCtx23L.W F.hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W F.hV)
      ((c.H F.hV).subtype.comp (c.sylowStar F.hV : Subgroup ↥(c.H F.hV)).subtype)
  letI : MulAction ↥(c.sylowStar F.hV) (c.toCtx23L.W F.hV) :=
    MulAction.compHom (c.toCtx23L.W F.hV)
      ((c.H F.hV).subtype.comp (c.sylowStar F.hV : Subgroup ↥(c.H F.hV)).subtype)
  exact pointCore_irreducible F _ hNle hNne (map_E_invariant F)

end Ctx2311

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
