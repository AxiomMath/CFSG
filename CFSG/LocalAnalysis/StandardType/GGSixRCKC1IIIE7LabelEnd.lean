module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassYPosition
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE7TwAFrame
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIE7LabelK2
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIE7LabelModel
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIISpBlock
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIUnitaryBlock
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeStepA

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType
open CFSG.LieType.Chevalley (baseChangeGL)
open CFSG.SeitzReduction.E6Pilot (rootProd)
open CFSG.SeitzReduction.E7Pilot (yAS yPsi)
open scoped MatrixGroups

theorem e7End_ggHasLabel_map_mulEquiv {X U : Type} [Group X] [Group U] {K J : Subgroup X}
    (e : ↥K ≃* U) (hJK : J ≤ K) {lab : LargeEvenLabel}
    (h : GGHasLabel lab (↥J ⧸ Subgroup.center ↥J)) :
    GGHasLabel lab
      (↥((J.subgroupOf K).map e.toMonoidHom) ⧸
        Subgroup.center ↥((J.subgroupOf K).map e.toMonoidHom)) :=
  ggHasLabel_quotCenter_of_mulEquiv
    ((Subgroup.subgroupOfEquivOfLe hJK).symm.trans
      (Subgroup.equivMapOfInjective (J.subgroupOf K) e.toMonoidHom e.injective)) h


theorem e7End_shortAt_map_mulEquiv {X U : Type} [Group X] [Group U] {K J : Subgroup X}
    {r : X} (e : ↥K ≃* U) (hJK : J ≤ K) (hrK : r ∈ K) (h : ShortAt J r) :
    ShortAt ((J.subgroupOf K).map e.toMonoidHom) (e ⟨r, hrK⟩) := by
  obtain ⟨rJ, hrJ, hPos⟩ := h
  have h' := shortAt_map_mulEquiv e hJK ⟨rJ, hrJ, hPos⟩
  have hpt : e (⟨r, by rw [← hrJ]; exact hJK rJ.2⟩ : ↥K) = e ⟨r, hrK⟩ :=
    congrArg e (Subtype.ext rfl)
  rwa [hpt] at h'

theorem k2At_of_row_III_of_E7_label {X : Type} [Group X] [Finite X] {K J V : Subgroup X}
    {r d : X} (hKq : CFSG.Assembly.IsQuasisimple ↥K)
    (hlab : GGHasLabel (⟨.E7, 0, 1⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hdK : d ∈ Subgroup.normalizer (K : Set X)) (hd3 : d ^ 3 = 1)
    (hJcomp : IsComponentOf J (K ⊓ Subgroup.centralizer {d})) (hrow : GGSixRCKJRow .III J)
    (hFour : FourAt J V r) (hCore : CoreCommAt J V r) (hShort : ShortAt J r) :
    K2At K V r := by
  have hJK : J ≤ K := hJcomp.1.trans inf_le_left
  have hrV : r ∈ V := hFour.1
  have hVK : V ≤ K := hFour.2.1.trans hJK
  have hrK : r ∈ K := hVK hrV
  have hKqN : CFSG.IsQuasisimple ↥K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥K).mp hKq
  obtain ⟨-, ⟨e⟩⟩ := e7Label_center_eq_bot_and_mulEquiv hKqN hlab
  have hJne : J ≠ K := ne_of_rowIII_of_e7Label hrow hlab
  obtain ⟨s, hs3, hs1, -, hcomp⟩ :=
    e7Label_exists_conj hKqN e hdK hd3 hJcomp hJK hJne
  obtain ⟨m, hm, hlabJ⟩ :
      ∃ m, (m = 5 ∨ m = 6) ∧
        GGHasLabel (⟨.twA, m, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) := by
    rcases e7Label_component_rowIII hKqN hlab hdK hd3 hJcomp hJK hrow with h | h
    · exact ⟨5, Or.inl rfl, h⟩
    · exact ⟨6, Or.inr rfl, h⟩
  let J' : Subgroup ↥(adjointGroup .E7 (ZMod 2)) := (J.subgroupOf K).map e.toMonoidHom
  let V' : Subgroup ↥(adjointGroup .E7 (ZMod 2)) := (V.subgroupOf K).map e.toMonoidHom
  have hlabJ' : GGHasLabel (⟨.twA, m, 1⟩ : LargeEvenLabel)
      (↥J' ⧸ Subgroup.center ↥J') :=
    e7End_ggHasLabel_map_mulEquiv e hJK hlabJ
  obtain ⟨-, -, ι, -, -, -, -, -, -, -, -, -, -, -, ⟨h, hh, hconj⟩,
    ⟨i, ψ, σ, -, hψ, -, ⟨z, W, hz, -, ⟨K₄, hK₄, -, ⟨Φ, θ, hΦ, -, hsurj, hker⟩⟩⟩⟩⟩ :=
    CFSG.StandardType.TablePThreeKG.exists_stdSetup_suCover_of_twA_component_E7
      (F := ZMod 2) (by rw [Nat.card_zmod]) hs3 hs1 hcomp hm hlabJ'
  have hFour' : FourAt J' V' (e ⟨r, hrK⟩) :=
    fourAt_subgroup_map_mulEquiv e hJK hrK hFour
  have hCore' : CoreCommAt J' V' (e ⟨r, hrK⟩) :=
    coreCommAt_subgroup_map_mulEquiv e hJK hrK hCore
  have hShort' : ShortAt J' (e ⟨r, hrK⟩) :=
    e7End_shortAt_map_mulEquiv e hJK hrK hShort
  haveI : Finite ↥(adjointGroup .E7 (ZMod 2)) := inferInstance
  haveI : CharP (AlgebraicClosure (ZMod 2)) 2 :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2))).injective 2
  obtain ⟨x, hx, hxr, hxV⟩ :=
    CFSG.SeitzReduction.E7Pilot.exists_conj_yAS_of_suCover
      (L := AlgebraicClosure (ZMod 2)) (ψ := ψ) (σ := σ) (by omega) hψ
      (z := z) hz (K := K₄) hK₄ (J := J') (ι := ι) (Φ := Φ) hΦ hsurj hker
      hFour' hCore' hShort'
  set x' : ModGL .E7 (AlgebraicClosure (ZMod 2)) := h⁻¹ * x with hx'def
  have hx' : x' ∈ adjointGroup .E7 (AlgebraicClosure (ZMod 2)) := by
    rw [hx'def]
    exact (adjointGroup .E7 (AlgebraicClosure (ZMod 2))).mul_mem
      ((adjointGroup .E7 (AlgebraicClosure (ZMod 2))).inv_mem hh) hx
  refine k2At_of_baseChange_conj_yAS (L := AlgebraicClosure (ZMod 2)) hrK hVK hrV e hx' ?_ ?_
  · have hιr : ι (e ⟨r, hrK⟩) =
        h * baseChangeGL (algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2)))
          (e ⟨r, hrK⟩ : ModGL .E7 (ZMod 2)) * h⁻¹ := hconj _
    calc x' * yAS (AlgebraicClosure (ZMod 2)) * x'⁻¹
        = h⁻¹ * (x * yAS (AlgebraicClosure (ZMod 2)) * x⁻¹) * h := by
          rw [hx'def]; group
      _ = h⁻¹ * ι (e ⟨r, hrK⟩) * h := by rw [hxr]
      _ = baseChangeGL (algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2)))
          (e ⟨r, hrK⟩ : ModGL .E7 (ZMod 2)) := by rw [hιr]; group
  · intro v hv
    have hmem : e ⟨v, hVK hv⟩ ∈ V' := by
      rw [Subgroup.mem_map]
      exact ⟨⟨v, hVK hv⟩, by rw [Subgroup.mem_subgroupOf]; exact hv, rfl⟩
    obtain ⟨c, hc⟩ := hxV _ hmem
    refine ⟨c, ?_⟩
    have hιv : ι (e ⟨v, hVK hv⟩) =
        h * baseChangeGL (algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2)))
          (e ⟨v, hVK hv⟩ : ModGL .E7 (ZMod 2)) * h⁻¹ := hconj _
    calc x'⁻¹ * baseChangeGL (algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2)))
          (e ⟨v, hVK hv⟩ : ModGL .E7 (ZMod 2)) * x'
        = x⁻¹ * (h * baseChangeGL (algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2)))
            (e ⟨v, hVK hv⟩ : ModGL .E7 (ZMod 2)) * h⁻¹) * x := by
          rw [hx'def]; group
      _ = x⁻¹ * ι (e ⟨v, hVK hv⟩) * x := by rw [← hιv]
      _ = rootProd .E7 (AlgebraicClosure (ZMod 2)) yPsi c := hc

theorem k2At_of_e8_three_e7_label_compConfig
    {X : Type} [Group X] [Finite X] {n : ℕ}
    {ψ : (ggU .E8 n 1).K →* X} {G₀ A B₁ D J L K V : Subgroup X} {e r : X}
    (hcfg : RCKRP.RCKCompConfig .E8 n 1 ψ 3 G₀ A B₁ D J L K e)
    (hrow : GGSixRCKJRow .III J) (hFour : FourAt J V r)
    (hCore : CoreCommAt J V r) (hShort : ShortAt J r)
    (hlabel : GGHasLabel ⟨.E7, 0, 1⟩ (↥K ⧸ Subgroup.center ↥K)) : K2At K V r := by
  obtain ⟨-, -, hp, -, hA, hBA, hDB, hDcard, hAN, -, hBNJ, -, -, -, -, -, -, -,
    hJcomp, -, -, -, -, -, -, heD, hene, hKcomp, hJK, -⟩ := hcfg
  obtain ⟨hBNK, d, hdD, -, hJd⟩ := RCKRP.le_normalizer_and_exists_isComponentOf_of_plane
    hp hA hBA hDB hDcard hAN hBNJ hJcomp heD hene hKcomp hJK
  exact k2At_of_row_III_of_E7_label hKcomp.2.2 hlabel (hBNK (hDB hdD))
    (hA.2 d (hBA (hDB hdD))) hJd hrow hFour hCore hShort

end CFSG.StandardType.RCKC1
