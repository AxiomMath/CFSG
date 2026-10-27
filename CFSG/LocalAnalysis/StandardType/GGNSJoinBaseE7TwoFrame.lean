module

public import CFSG.LocalAnalysis.StandardType.GGMemberE7TwoTorus
public import Certificates.Certificate3951
import CFSG.LocalAnalysis.StandardType.GGLtBstarOfInner
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueTwo
import CFSG.LocalAnalysis.StandardType.GGMemberE7TwoRankOne
import CFSG.LocalAnalysis.SeitzReduction.E7PilotOuter
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4Toral
import CFSG.GroupTheory.ConjTransport
import CFSG.GroupTheory.ElementaryAbelianTransport

public noncomputable section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem exists_conj_eq_of_ggGamma_range_model {G Q : Type} [Group G] [Group Q]
    {Bs X : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (e : X ≃* Q) {E : Subgroup Q}
    (hconj : Function.Injective (MulAut.conj : Q →* MulAut Q))
    (hmodel : (ggGamma X hN).range.map (MulAut.congr e).toMonoidHom =
      E.map (MulAut.conj : Q →* MulAut Q)) :
    (∀ b ∈ Bs, ∃ ε ∈ E, ∀ y ∈ X,
      b * y * b⁻¹ = ((e.symm ε : X) : G) * y * ((e.symm ε : X) : G)⁻¹) ∧
    (∀ ε ∈ E, ∃ b ∈ Bs, ∀ y ∈ X,
      b * y * b⁻¹ = ((e.symm ε : X) : G) * y * ((e.symm ε : X) : G)⁻¹) := by
  obtain ⟨ρ, -, hρE, hρact⟩ := exists_point_action_of_inner_image e hconj hmodel
  have key : ∀ a : (ggGamma X hN).range, ∀ x : X,
      ((a.1 x : X) : G) =
        ((e.symm (ρ a) : X) : G) * (x : G) * ((e.symm (ρ a) : X) : G)⁻¹ := by
    intro a x
    have h := congrArg (fun q => e.symm q) (hρact a x)
    have h' : (a.1 x : X) = e.symm (ρ a) * x * (e.symm (ρ a))⁻¹ := by
      simpa only [map_mul, map_inv, e.symm_apply_apply] using h
    rw [h']
    rfl
  constructor
  · intro b hb
    let a : (ggGamma X hN).range := ⟨ggGamma X hN ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩⟩
    refine ⟨ρ a, hρE ▸ ⟨a, rfl⟩, fun y hy => ?_⟩
    have hb' : ((ggGamma X hN ⟨b, hb⟩ ⟨y, hy⟩ : X) : G) = b * y * b⁻¹ :=
      ggGamma_coe X hN ⟨b, hb⟩ ⟨y, hy⟩
    exact hb'.symm.trans (key a ⟨y, hy⟩)
  · intro ε hε
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp (hρE.symm ▸ hε : ε ∈ ρ.range)
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp a.2
    refine ⟨(b : G), b.2, fun y hy => ?_⟩
    have h1 : ((ggGamma X hN b ⟨y, hy⟩ : X) : G) = (b : G) * y * (b : G)⁻¹ :=
      ggGamma_coe X hN b ⟨y, hy⟩
    have h3 : ((ggGamma X hN b ⟨y, hy⟩ : X) : G) =
        ((e.symm ε : X) : G) * y * ((e.symm ε : X) : G)⁻¹ := by
      rw [hb, ← ha]
      exact key a ⟨y, hy⟩
    exact h1.symm.trans h3


theorem exists_inner_conj_of_e7Two_marking {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs L D J X : Subgroup G} {x : G}
    (hcfg : GGConfig p B Bs x L D J)
    (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_EE7 p lab ∧ lab.n = 1) p Bs X) :
    ∀ b ∈ Bs, ∃ a : ↥X, ∀ y ∈ X, b⁻¹ * y * b = (a : G)⁻¹ * y * a := by
  obtain ⟨hp3, hN, K, iK, iFin, iChar, hK, e, E, c, hE, hcard, hc, hmodel, -⟩ :=
    exists_e7Two_frame_of_marking hcfg hX hmark
  let := iK
  let := iFin
  let := iChar
  subst hp3
  have hconj : Function.Injective
      (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)) :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.mulAut_conj_injective_adjointGroup
  obtain ⟨hframe, -⟩ := exists_conj_eq_of_ggGamma_range_model hN e hconj hmodel
  intro b hb
  obtain ⟨ε, hε, h⟩ := hframe b⁻¹ (Bs.inv_mem hb)
  refine ⟨(e.symm ε)⁻¹, fun y hy => ?_⟩
  simpa [Subgroup.coe_inv] using h y hy

theorem le_centralizer_of_isPGroup_two_of_e7Two_marking {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs L D J X : Subgroup G} {x : G}
    (hcfg : GGConfig p B Bs x L D J)
    (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_EE7 p lab ∧ lab.n = 1) p Bs X)
    {U : Subgroup G} (hU : IsPGroup 2 U) (hUX : U ≤ X)
    (hBsU : Bs ≤ Subgroup.normalizer (U : Set G)) :
    U ≤ Subgroup.centralizer (X : Set G) := by
  obtain ⟨hp3, hN, K, iK, iFin, iChar, hK, e, E, c, hE, -, hc, hmodel, -⟩ :=
    exists_e7Two_frame_of_marking hcfg hX hmark
  let := iK
  let := iFin
  let := iChar
  subst hp3
  have hconj : Function.Injective
      (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)) :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.mulAut_conj_injective_adjointGroup
  obtain ⟨-, hconjE⟩ := exists_conj_eq_of_ggGamma_range_model hN e hconj hmodel
  let E' : Subgroup G := (E.map e.symm.toMonoidHom).map X.subtype
  have hE'X : E' ≤ X := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hE' : IsElemAbelian 3 E' := (hE.map e.symm.toMonoidHom).map X.subtype
  have hET : E.map (MulAut.conj c⁻¹).toMonoidHom =
      (TableBExcTwoTB.tE K TableBExcTwo.frameE7).range := by
    rw [hc, Subgroup.map_map]
    have hid : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
        MonoidHom.id (adjointGroup .E7 K) := by
      ext y
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    rw [hid, Subgroup.map_id]
  have hP : FrameRoute.P13aConclusion (adjointGroup .E7 K) E 7 :=
    FrameRoute.p13a6_E7 hK (MulAut.conj c⁻¹) hET
  have hcardE' : Nat.card E' = Nat.card E := by
    rw [Subgroup.card_map_of_injective X.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective]
  have hcard3 : 3 ^ 7 ≤ Nat.card E' := hP.1.symm.trans_le hcardE'.ge
  have hUN : U ≤ Subgroup.normalizer (X : Set G) := hUX.trans Subgroup.le_normalizer
  have hE'U : E' ≤ Subgroup.normalizer (U : Set G) := by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨ε, hε, rfl⟩ := Subgroup.mem_map.mp hx'
    obtain ⟨b, hb, hbconj⟩ := hconjE ε hε
    refine CFSG.GroupTheory.mem_normalizer_of_conj_mem ?_
    intro u hu
    have hbU : b * u * b⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hBsU hb) u).mp hu
    rwa [hbconj u (hUX hu)] at hbU
  exact FrameRoute.le_centralizer_of_E7Two_torus hK e hE'X hE' hcard3 hU hUN hE'U

theorem GGConfig.lt_bstar_of_E7two {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_EE7 p lab ∧ lab.n = 1) p Bs L) :
    B < Bs := by
  obtain ⟨hp3, -, K, iK, iFin, -, -, e, -⟩ := exists_e7Two_frame_of_marking hcfg (Or.inl rfl) hmark
  subst hp3
  have hZ : Nat.card (Subgroup.center ↥L) = 1 := by
    rw [CFSG.SeitzReduction.E7Pilot.center_eq_bot_of_mulEquiv_E7 e, Subgroup.card_bot]
  refine hcfg.lt_bstar_of_inner (by rw [hZ]; exact Nat.coprime_one_left 3)
    (exists_inner_conj_of_e7Two_marking hcfg (Or.inl rfl) hmark) fun U hUL hU2 hBsU => ?_
  exact le_centralizer_of_isPGroup_two_of_e7Two_marking hcfg (Or.inl rfl) hmark hU2 hUL hBsU

end CFSG.StandardType

end
