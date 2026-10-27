module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsSL3PointTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SL3Early
public import CFSG.CGT.Timmesfeld75.Sec3EightFixed
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BlockNatural
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineAdj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SL3GeomTransfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Ctx2311

theorem map_pCoreOf_phiL_le {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (hV : IsElemAbelian 2 c.V) :
    ((CFSG.Open.pCoreOf 2 c.K).subgroupOf c.K).map
        ((c.phiL hV).comp (Subgroup.inclusion c.K_le_L)) ≤
      CFSG.Open.pCoreOf 2 ((c.K.subgroupOf c.L).map (c.phiL hV)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Kstar : Subgroup ↥(c.H hV) := (c.K.subgroupOf c.L).map (c.phiL hV)
  let ρ : ↥c.K →* ↥Kstar :=
    ((c.phiL hV).comp (Subgroup.inclusion c.K_le_L)).codRestrict Kstar fun k =>
      Subgroup.mem_map_of_mem (c.phiL hV) k.2
  have hρ : Function.Surjective ρ := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    have hxK : (x : G) ∈ c.K := Subgroup.mem_subgroupOf.mp hx
    refine ⟨⟨(x : G), hxK⟩, Subtype.ext ?_⟩
    show (c.phiL hV ⟨(x : G), c.K_le_L hxK⟩ : ↥(c.H hV)) = (y : ↥(c.H hV))
    rw [show (⟨(x : G), c.K_le_L hxK⟩ : ↥c.L) = x from Subtype.ext rfl]
    exact hxy
  let P : Subgroup ↥c.K := (CFSG.Open.pCoreOf 2 c.K).subgroupOf c.K
  have hPnorm : P.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (CFSG.LieType.BorelTits.pCoreOf_le 2 c.K)).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.K)
  have hP2 : IsPGroup 2 P :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.K).of_equiv
      (Subgroup.subgroupOfEquivOfLe (CFSG.LieType.BorelTits.pCoreOf_le 2 c.K)).symm
  have hcomp : Kstar.subtype.comp ρ = (c.phiL hV).comp (Subgroup.inclusion c.K_le_L) := by
    ext k; rfl
  rw [← hcomp, ← Subgroup.map_map]
  refine CFSG.LieType.BorelTits.le_pCoreOf 2 ?_ ?_ ((hP2.map ρ).map Kstar.subtype)
  · intro y hy
    obtain ⟨z, -, hzy⟩ := Subgroup.mem_map.mp hy
    rw [← hzy]
    exact z.2
  · have hnormal : (P.map ρ).Normal := hPnorm.map ρ hρ
    have hsub : ((P.map ρ).map Kstar.subtype).subgroupOf Kstar = P.map ρ :=
      Subgroup.comap_map_eq_self_of_injective Kstar.subtype_injective (P.map ρ)
    rw [hsub]
    exact hnormal

theorem phiL_mem_pCoreOf {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    {hV : IsElemAbelian 2 c.V} {x : ↥c.L} (hx : (x : G) ∈ CFSG.Open.pCoreOf 2 c.K) :
    c.phiL hV x ∈
      CFSG.Open.pCoreOf 2 ((c.K.subgroupOf c.L).map (c.phiL hV)) := by
  have hxK : (x : G) ∈ c.K := CFSG.LieType.BorelTits.pCoreOf_le 2 c.K hx
  have hmem : (⟨(x : G), hxK⟩ : ↥c.K) ∈ (CFSG.Open.pCoreOf 2 c.K).subgroupOf c.K := by
    rwa [Subgroup.mem_subgroupOf]
  have h := map_pCoreOf_phiL_le c hV (Subgroup.mem_map_of_mem _ hmem)
  have hxeq : (⟨(x : G), c.K_le_L hxK⟩ : ↥c.L) = x := Subtype.ext rfl
  change c.phiL hV ⟨(x : G), c.K_le_L hxK⟩ ∈
    CFSG.Open.pCoreOf 2 ((c.K.subgroupOf c.L).map (c.phiL hV)) at h
  rwa [hxeq] at h

theorem phiL_odd_cube {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    {hV : IsElemAbelian 2 c.V} {d : G} (hdL : d ∈ c.L) (hdodd : Odd (orderOf d))
    (hd3 : d ^ 3 ≠ 1) (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L) :
    Odd (orderOf (c.phiL hV ⟨d, hdL⟩)) ∧ (c.phiL hV ⟨d, hdL⟩) ^ 3 ≠ 1 := by
  have hdodd' : Odd (orderOf (⟨d, hdL⟩ : ↥c.L)) := by rwa [Subgroup.orderOf_mk]
  have hodd : Odd (orderOf (c.phiL hV ⟨d, hdL⟩)) :=
    Odd.of_dvd_nat hdodd' (orderOf_map_dvd (c.phiL hV) ⟨d, hdL⟩)
  refine ⟨hodd, fun hg => ?_⟩
  have hmem : (⟨d ^ 3, c.L.pow_mem hdL 3⟩ : ↥c.L) ∈ (c.phiL hV).ker := by
    rw [MonoidHom.mem_ker,
      show (⟨d ^ 3, c.L.pow_mem hdL 3⟩ : ↥c.L) = ⟨d, hdL⟩ ^ 3 from Subtype.ext rfl,
      map_pow]
    exact hg
  rw [hker] at hmem
  have hodd3 : Odd (orderOf (⟨d ^ 3, c.L.pow_mem hdL 3⟩ : ↥c.L)) := by
    rw [Subgroup.orderOf_mk]
    exact Odd.of_dvd_nat hdodd (orderOf_pow_dvd (x := d) 3)
  have h1 := CFSG.CGT.Timmesfeld75.eq_one_of_odd_orderOf_of_mem
    (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)) hmem hodd3
  exact hd3 (by simpa using congrArg Subtype.val h1)

theorem phiL_commutator_mem_pCoreOf {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    {hV : IsElemAbelian 2 c.V} {d : G} (hdL : d ∈ c.L)
    (hdK : ∀ k ∈ c.K, d * k * d⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 c.K) :
    ∀ k ∈ (c.K.subgroupOf c.L).map (c.phiL hV),
      c.phiL hV ⟨d, hdL⟩ * k * (c.phiL hV ⟨d, hdL⟩)⁻¹ * k⁻¹ ∈
        CFSG.Open.pCoreOf 2 ((c.K.subgroupOf c.L).map (c.phiL hV)) := by
  intro k hk
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hk
  have hxK : (x : G) ∈ c.K := Subgroup.mem_subgroupOf.mp hx
  have hmem := hdK (x : G) hxK
  have hmemL : d * (x : G) * d⁻¹ * (x : G)⁻¹ ∈ c.L :=
    c.L.mul_mem (c.L.mul_mem (c.L.mul_mem hdL x.2) (c.L.inv_mem hdL)) (c.L.inv_mem x.2)
  have hmap := phiL_mem_pCoreOf (c := c) (hV := hV)
    (x := ⟨d * (x : G) * d⁻¹ * (x : G)⁻¹, hmemL⟩) hmem
  have hconj : c.phiL hV ⟨d, hdL⟩ * c.phiL hV x * (c.phiL hV ⟨d, hdL⟩)⁻¹ *
      (c.phiL hV x)⁻¹ = c.phiL hV ⟨d * (x : G) * d⁻¹ * (x : G)⁻¹, hmemL⟩ := by
    rw [← map_mul, ← map_inv, ← map_mul, ← map_inv, ← map_mul]
    exact congrArg (c.phiL hV) (Subtype.ext (by simp [mul_assoc]))
  rw [hconj]
  exact hmap

private theorem pointTorus_fixed {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (hPT : KSL3PointTorus)
    {hV : IsElemAbelian 2 c.V} (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hSL : IsSLn ↥(c.H hV) 3 (CFSG.Open.pRank 2 D.Z))
    (hnatSL : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z))
    (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L)
    {d : G} (hdL : d ∈ c.L) (hdodd : Odd (orderOf d)) (hd3 : d ^ 3 ≠ 1)
    (hdK : ∀ k ∈ c.K, d * k * d⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 c.K) :
    let g : ↥(c.H hV) := c.phiL hV ⟨d, hdL⟩
    (∀ w : c.toCtx23L.W hV, g • w = w → w = 1) ∧
      (∀ u ∈ CFSG.Open.pCoreOf 2 ((c.K.subgroupOf c.L).map (c.phiL hV)),
        g * u * g⁻¹ = u → u = 1) := by
  classical
  letI : MulDistribMulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
    MulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.toCtx23L.W hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.toCtx23L.W hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  letI : MulAction ↥(c.sylowStar hV) (c.toCtx23L.W hV) :=
    MulAction.compHom (c.toCtx23L.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  let g : ↥(c.H hV) := c.phiL hV ⟨d, hdL⟩
  let Kstar : Subgroup ↥(c.H hV) := (c.K.subgroupOf c.L).map (c.phiL hV)
  have hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z) :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hSL, hnatSL⟩))))
  have hKstar : Hinf (MulAction.stabilizer ↥(c.H hV)
      (((fixedPointSubgroup ↥(c.sylowStar hV) (c.toCtx23L.W hV) : Subgroup (c.toCtx23L.W hV)) :
        Set (c.toCtx23L.W hV)))) = Kstar :=
    c.toCtx23L.Hinf_stabilizer_sylowStar_eq_map_Hinf hV kTab23a_holds h4 h1930 hnat
  obtain ⟨hgodd, hg3⟩ := phiL_odd_cube c hdL hdodd hd3 hker
  have hcomm : ∀ k ∈ Hinf (MulAction.stabilizer ↥(c.H hV)
      (((fixedPointSubgroup ↥(c.sylowStar hV) (c.toCtx23L.W hV) : Subgroup (c.toCtx23L.W hV)) :
        Set (c.toCtx23L.W hV)))), g * k * g⁻¹ * k⁻¹ ∈
      CFSG.Open.pCoreOf 2 (Hinf (MulAction.stabilizer ↥(c.H hV)
        (((fixedPointSubgroup ↥(c.sylowStar hV) (c.toCtx23L.W hV) : Subgroup (c.toCtx23L.W hV)) :
          Set (c.toCtx23L.W hV))))) := by
    intro k hk
    rw [hKstar] at hk ⊢
    exact phiL_commutator_mem_pCoreOf c hdL hdK k hk
  have hres := hPT (c.toCtx23L.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) hSL hnatSL h3
    (c.sylowStar hV) g hgodd hg3 hcomm
  rw [hKstar] at hres
  exact hres

private theorem fixed_V_of_centralizes_Kbar {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h1930 : H1930 D) (h4 : S23_4 D Ch)
    (hPT : KSL3PointTorus) {hV : IsElemAbelian 2 c.V}
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hSL : IsSLn ↥(c.H hV) 3 (CFSG.Open.pRank 2 D.Z))
    (hnatSL : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z))
    (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L)
    {d : G} (hdL : d ∈ c.L) (hdodd : Odd (orderOf d)) (hd3 : d ^ 3 ≠ 1)
    (hdK : ∀ k ∈ c.K, d * k * d⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 c.K) :
    c.V ⊓ Subgroup.centralizer ({d} : Set G) = ⊥ := by
  classical
  letI : MulDistribMulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
    MulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.toCtx23L.W hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.toCtx23L.W hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  letI : MulAction ↥(c.sylowStar hV) (c.toCtx23L.W hV) :=
    MulAction.compHom (c.toCtx23L.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  let g : ↥(c.H hV) := c.phiL hV ⟨d, hdL⟩
  obtain ⟨hfix, -⟩ :=
    c.pointTorus_fixed h1930 h4 hPT h3 hSL hnatSL hker hdL hdodd hd3 hdK
  refine le_antisymm ?_ bot_le
  intro v hv
  rw [Subgroup.mem_bot]
  have hvd : d * v * d⁻¹ = v := by
    have h := (Subgroup.mem_centralizer_iff.mp hv.2) d (Set.mem_singleton d)
    rw [h]
    group
  have hgv : g • mkTil (⊥ : Subgroup G) c.V hV (IntMod.mk hV ⟨v, hv.1⟩) =
      mkTil (⊥ : Subgroup G) c.V hV (IntMod.mk hV ⟨v, hv.1⟩) := by
    rw [show g • _ = (g : MulAut (c.toCtx23L.W hV)) _ from rfl,
      show g = c.phiL hV ⟨d, hdL⟩ from rfl,
      c.toCtx23L.phiL_apply_mkTil hV ⟨d, hdL⟩]
    refine congrArg (mkTil (⊥ : Subgroup G) c.V hV) (IntMod.val_injective ?_)
    rw [actStab_apply_val]
    exact hvd
  have h1 : mkTil (⊥ : Subgroup G) c.V hV (IntMod.mk hV ⟨v, hv.1⟩) = 1 := hfix _ hgv
  have h2 : IntMod.mk hV ⟨v, hv.1⟩ = 1 := mkTil_bot_injective hV (by simpa using h1)
  exact congrArg (fun w : ↥c.V => (w : G)) h2

theorem le_pCoreOf_parts {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h1930 : H1930 D) (h4 : S23_4 D Ch) (h12 : S23_12 D Ch)
    (hN8 : ⁅c.V, c.K⁆ = c.V) {hV : IsElemAbelian 2 c.V}
    (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L) :
    (c.E ≤ CFSG.Open.pCoreOf 2 c.K) ∧ (c.S ≤ CFSG.Open.pCoreOf 2 c.L) ∧
      (c.E.subgroupOf c.L) ⊔ (c.S.subgroupOf c.L) ≤
        (CFSG.Open.pCoreOf 2 ((c.K.subgroupOf c.L).map (c.phiL hV))).comap (c.phiL hV) := by
  have hEK : c.E ≤ c.K := c.E_le_K h1930 h4 h12 hN8
  have hE2 : IsPGroup 2 ↥c.E := c.isPGroup_E h1930 h4 h12 hN8
  have hKNE : c.K ≤ Subgroup.normalizer (c.E : Set G) :=
    ((uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_left).trans
      (uc22p22v_le_normalizer_conjClosure D.M c.V)
  have hEpK : c.E ≤ CFSG.Open.pCoreOf 2 c.K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hEK hKNE hE2
  have hIL : c.I ≤ c.L := by
    rw [Ctx2311.I]
    exact TwelveTwentyThree.conjClosure_le (hEK.trans c.K_le_L)
  have hSle : c.S ≤ CFSG.Open.pCoreOf 2 c.L := by
    rw [Ctx2311.S]
    exact CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hIL
      (by rw [Ctx2311.I]; exact TwelveTwentyThree.le_normalizer_conjClosure c.L c.E)
  have hpre : (c.E.subgroupOf c.L) ⊔ (c.S.subgroupOf c.L) ≤
      (CFSG.Open.pCoreOf 2 ((c.K.subgroupOf c.L).map (c.phiL hV))).comap (c.phiL hV) := by
    refine sup_le ?_ ?_
    · intro e he
      rw [Subgroup.mem_comap]
      exact phiL_mem_pCoreOf (c := c) (hV := hV) (hEpK (Subgroup.mem_subgroupOf.mp he))
    · intro s hs
      rw [Subgroup.mem_comap]
      have hsO : (s : G) ∈ CFSG.Open.pCoreOf 2 c.L := hSle (Subgroup.mem_subgroupOf.mp hs)
      have hsKer : c.phiL hV s = 1 := by
        rw [← MonoidHom.mem_ker, hker]
        exact (CFSG.mem_openPCoreOf_iff (p := 2) (H := c.L) s).mp hsO
      rw [hsKer]
      exact (CFSG.Open.pCoreOf 2 ((c.K.subgroupOf c.L).map (c.phiL hV))).one_mem
  exact ⟨hEpK, hSle, hpre⟩

private theorem le_pCoreOf_of_centralizes_Kbar {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h1930 : H1930 D) (h4 : S23_4 D Ch) (h12 : S23_12 D Ch)
    (hN8 : ⁅c.V, c.K⁆ = c.V) (hPT : KSL3PointTorus) {hV : IsElemAbelian 2 c.V}
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hSL : IsSLn ↥(c.H hV) 3 (CFSG.Open.pRank 2 D.Z))
    (hnatSL : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z))
    (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L)
    {d : G} (hdL : d ∈ c.L) (hdodd : Odd (orderOf d)) (hd3 : d ^ 3 ≠ 1)
    (hdK : ∀ k ∈ c.K, d * k * d⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 c.K) :
    (c.E ⊔ c.S) ⊓ Subgroup.centralizer ({d} : Set G) ≤ CFSG.Open.pCoreOf 2 c.L := by
  intro x hx
  obtain ⟨hEpK, hSle, hpre⟩ := c.le_pCoreOf_parts h1930 h4 h12 hN8 hker
  have hEsub : c.E ≤ c.L :=
    hEpK.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 c.K).trans c.K_le_L)
  have hSsub : c.S ≤ c.L := hSle.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 c.L)
  have hxL : x ∈ c.L := (sup_le hEsub hSsub) hx.1
  obtain ⟨-, hfix⟩ :=
    c.pointTorus_fixed h1930 h4 hPT h3 hSL hnatSL hker hdL hdodd hd3 hdK
  have hxmem : (⟨x, hxL⟩ : ↥c.L) ∈ (c.E ⊔ c.S).subgroupOf c.L := by
    rw [Subgroup.mem_subgroupOf]
    simpa using hx.1
  have hxpre : c.phiL hV ⟨x, hxL⟩ ∈
      CFSG.Open.pCoreOf 2 ((c.K.subgroupOf c.L).map (c.phiL hV)) := by
    rw [← Subgroup.subgroupOf_sup hEsub hSsub] at hpre
    exact hpre hxmem
  have hfixg : c.phiL hV ⟨d, hdL⟩ * c.phiL hV ⟨x, hxL⟩ * (c.phiL hV ⟨d, hdL⟩)⁻¹ =
      c.phiL hV ⟨x, hxL⟩ := by
    have hcommx : d * x = x * d :=
      (Subgroup.mem_centralizer_iff.mp hx.2) d (Set.mem_singleton d)
    have hconj : (⟨d, hdL⟩ : ↥c.L) * ⟨x, hxL⟩ * ⟨d, hdL⟩⁻¹ = ⟨x, hxL⟩ := by
      apply Subtype.ext
      show d * x * d⁻¹ = x
      rw [hcommx]
      group
    calc c.phiL hV ⟨d, hdL⟩ * c.phiL hV ⟨x, hxL⟩ * (c.phiL hV ⟨d, hdL⟩)⁻¹
        = c.phiL hV ((⟨d, hdL⟩ : ↥c.L) * ⟨x, hxL⟩ * ⟨d, hdL⟩⁻¹) := by
          rw [map_mul, map_mul, map_inv]
      _ = c.phiL hV ⟨x, hxL⟩ := by rw [hconj]
  have hx1 : c.phiL hV ⟨x, hxL⟩ = 1 := hfix _ hxpre hfixg
  have hxker : (⟨x, hxL⟩ : ↥c.L) ∈ (c.phiL hV).ker := MonoidHom.mem_ker.mpr hx1
  rw [hker] at hxker
  exact (CFSG.mem_openPCoreOf_iff (p := 2) (H := c.L) ⟨x, hxL⟩).mpr hxker

theorem fixed_of_centralizes_Kbar {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h12 : S23_12 D Ch) (hN8 : ⁅c.V, c.K⁆ = c.V)
    (hPT : KSL3PointTorus) {hV : IsElemAbelian 2 c.V}
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hSL : IsSLn ↥(c.H hV) 3 (CFSG.Open.pRank 2 D.Z))
    (hnatSL : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z))
    (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L)
    {d : G} (hdL : d ∈ c.L) (hdodd : Odd (orderOf d)) (hd3 : d ^ 3 ≠ 1)
    (hdK : ∀ k ∈ c.K, d * k * d⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 c.K) :
    c.V ⊓ Subgroup.centralizer ({d} : Set G) = ⊥ ∧
      (c.E ⊔ c.S) ⊓ Subgroup.centralizer ({d} : Set G) ≤ CFSG.Open.pCoreOf 2 c.L :=
  ⟨fixed_V_of_centralizes_Kbar c h1930 h4 hPT h3 hSL hnatSL hker hdL hdodd hd3 hdK,
    le_pCoreOf_of_centralizes_Kbar c h1930 h4 h12 hN8 hPT h3 hSL hnatSL hker hdL hdodd hd3 hdK⟩

end Ctx2311

end CFSG.LocalAnalysis.UniquenessCase.UC22
