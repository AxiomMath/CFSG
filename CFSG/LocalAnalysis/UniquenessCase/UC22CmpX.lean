module

public import CFSG.Quasithin.Background.C118Block
public import CFSG.RankThree.PartOne.S12.PushingUp
import CFSG.Quasithin.Background.E1Amb
import CFSG.LocalAnalysis.AGLEmbedding.NoXBlockBridgeAux
import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.Campbell
open CFSG.RankThree.PartOne (InClassX oResidualTwo)

theorem twoResidual_top_eq_oResidualTwo (X : Type) [Group X] :
    twoResidual (⊤ : Subgroup X) = oResidualTwo X := by
  apply le_antisymm
  · refine le_sInf ?_
    rintro N ⟨hN, hp⟩
    refine iInf₂_le N ⟨le_top, top_le_iff.2 (Subgroup.normalizer_eq_top_iff.2 hN), fun x _ => ?_⟩
    obtain ⟨k, hk⟩ := hp (x : X ⧸ N)
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk⟩
  · refine le_iInf₂ fun N hN => ?_
    obtain ⟨-, hnorm, hpow⟩ := hN
    have hNn : N.Normal := Subgroup.normalizer_eq_top_iff.1 (top_le_iff.1 hnorm)
    refine sInf_le ⟨hNn, fun q => ?_⟩
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨k, hk⟩ := hpow x trivial
      exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩

theorem twoResidual_eq_map_oResidualTwo {Ω : Type} [Group Ω] [Finite Ω] (H : Subgroup Ω) :
    twoResidual H = (oResidualTwo ↥H).map H.subtype := by
  rw [E1.twoResidual_eq_map_top, twoResidual_top_eq_oResidualTwo]

theorem charTwo_of_fitting_eq {Ω : Type} [Group Ω] [Finite Ω] {H : Subgroup Ω}
    (h : CFSG.generalizedFitting ↥H = CFSG.pCore 2 ↥H) : CFSG.QuasithinUnique.CharTwo H := by
  intro x hx
  have hcen : (⟨x, hx.1⟩ : ↥H) ∈ Subgroup.centralizer (CFSG.generalizedFitting ↥H : Set ↥H) := by
    rw [h, Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hx.2 (y : Ω) ⟨y, hy, rfl⟩)
  have hmem := CFSG.centralizer_generalizedFitting_le ↥H hcen
  rw [h] at hmem
  exact ⟨⟨x, hx.1⟩, hmem, rfl⟩

theorem inClassX_oResidualTwo_of_isL2OrA3Block {Ω : Type} [Group Ω] [Finite Ω] {H : Subgroup Ω}
    (hb : IsL2OrA3Block H (twoResidual H)) : InClassX ↥(oResidualTwo ↥H) := by
  obtain ⟨hB, hT⟩ := hb
  have hX : CFSG.AGLEmbedding.InClassXBlock (twoResidual H) :=
    ⟨hB.1, hT.imp (fun ⟨n, hn, hl⟩ => ⟨n, hn.le, hl⟩) (fun hA => ⟨1, le_rfl, hA⟩)⟩
  have hXc := CFSG.AGLEmbedding.NoXBlock.inClassX_of_inClassXBlock hX
  let e : ↥(twoResidual H) ≃* ↥(oResidualTwo ↥H) :=
    (MulEquiv.subgroupCongr (twoResidual_eq_map_oResidualTwo H)).trans
      ((oResidualTwo ↥H).equivMapOfInjective H.subtype H.subtype_injective).symm
  exact CFSG.CGT.PushingUpLit.InClassX.of_mulEquiv e hXc

theorem inClassX_oResidualTwo_of_supplement {Ω : Type} [Group Ω] [Finite Ω] {H : Subgroup Ω}
    (hfit : CFSG.generalizedFitting ↥H = CFSG.pCore 2 ↥H) {k : Type} [Field k] [Finite k] {S : Sylow 2 ↥H}
    {ρ : ↥H →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore ↥H →* Multiplicative (Fin 2 → k)}
    (h : IsSeed S ρ (Ecore ↥H) ψ) {V' : Subgroup ↥H} (hV'S : V' ≤ (S : Subgroup ↥H))
    (hV'n : ∀ s ∈ (S : Subgroup ↥H), ∀ x ∈ V', s * x * s⁻¹ ∈ V')
    (hV'e : CFSG.Open.IsElemAbelian 2 V')
    (hSV' : ⁅(S : Subgroup ↥H), V'⁆ ≤ Subgroup.centralizer ((S : Subgroup ↥H) : Set ↥H))
    (hsup : (S : Subgroup ↥H) = CFSG.pCore 2 ↥H ⊔ V') : InClassX ↥(oResidualTwo ↥H) :=
  inClassX_oResidualTwo_of_isL2OrA3Block
    (isL2OrA3Block_of_supplement (charTwo_of_fitting_eq hfit) h hV'S hV'n hV'e hSV' hsup)

end CFSG.LocalAnalysis.UniquenessCase.UC22
