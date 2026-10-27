module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCSixAux
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16c13bcA_exists_other_conj (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hH : Hyp151 D V₀ V L) (hs : s15 D.M V₀ V hV L = 2) :
    ∃ g ∈ Mbar D.M V₀ V hV,
      (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom ≠ lBar V₀ V hV L ∧
      ⁅lBar V₀ V hV L, (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom⁆ = ⊥ ∧
      ∀ b ∈ (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom,
        ∀ w ∈ wTil V₀ V hV L, b w = w := by
  classical
  have hcls : Set.ncard {Y : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar D.M V₀ V hV, Y = (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom} = 2 := by
    unfold s15 at hs
    exact hs
  obtain ⟨g₂, hg₂M, hg₂ne⟩ : ∃ g ∈ Mbar D.M V₀ V hV,
      (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom ≠ lBar V₀ V hV L := by
    by_contra hcon
    have hsingle : {Y : Subgroup (MulAut (Vtil V₀ V hV)) |
        ∃ φ ∈ Mbar D.M V₀ V hV,
          Y = (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom} = {lBar V₀ V hV L} := by
      ext Y
      constructor
      · rintro ⟨φ, hφM, rfl⟩
        by_contra hne
        exact hcon ⟨φ, hφM, hne⟩
      · rintro rfl
        exact ⟨1, (Mbar D.M V₀ V hV).one_mem, by ext y; simp⟩
    rw [hsingle] at hcls
    simp at hcls
  obtain ⟨x, hxM, hxg₂⟩ := (mem_barSub V₀ V hV D.M g₂).1 hg₂M
  have hgne : (lBar V₀ V hV L).map (MulAut.conj g₂⁻¹).toMonoidHom ≠ lBar V₀ V hV L := by
    intro h
    apply hg₂ne
    have h' := congrArg (fun X : Subgroup (MulAut (Vtil V₀ V hV)) =>
      X.map (MulAut.conj g₂).toMonoidHom) h
    rw [← s16c13bc_map_conj_mul, mul_inv_cancel, s16c13bc_map_conj_one] at h'
    exact h'.symm
  have hgM : g₂⁻¹ ∈ Mbar D.M V₀ V hV := (Mbar D.M V₀ V hV).inv_mem hg₂M
  have hconjinv : ((MulAut.conj g₂)⁻¹).toMonoidHom =
      (MulAut.conj g₂⁻¹).toMonoidHom := by
    ext z
    simp [MulAut.conj_apply]
  have hbar : barSub V₀ V hV (conjSubgroup L (x : G)) =
      (lBar V₀ V hV L).map (MulAut.conj g₂⁻¹).toMonoidHom := by
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV x.2 L, hxg₂]
    exact congrArg (fun f : MulAut (Vtil V₀ V hV) →* MulAut (Vtil V₀ V hV) =>
      (barSub V₀ V hV L).map f) hconjinv
  have hxnbar : (x : G) ∉ nBar D.M V₀ V hV L := by
    intro hx
    rw [s15_Infra_mem_nBar_iff hH.hyp125 hV hxM] at hx
    rw [hbar] at hx
    exact hgne hx
  have hcomm := hH.commute (x : G) hxM hxnbar
  rw [hbar] at hcomm
  refine ⟨g₂⁻¹, hgM, hgne, hcomm.1, ?_⟩
  intro b hb w hw
  have hle : wTil V₀ V hV L ≤ fixV ((lBar V₀ V hV L).map (MulAut.conj g₂⁻¹).toMonoidHom) :=
    commSub_eq_bot_iff.mp hcomm.2
  exact (mem_fixV.mp (hle hw)) b hb

theorem s16c13bcA_pair_of_conj {Γ : Type*} [Group Γ] {L L' : Subgroup Γ} (hcomm : ⁅L, L'⁆ = ⊥)
    (hc : Subgroup.center ↥L = ⊥) {ψ ψ' : Γ} (hψ : ψ ∈ L) (hψ' : ψ' ∈ L') (hψ'1 : ψ' ≠ 1) :
    ψ * ψ' = ψ' * ψ ∧ ψ' ∉ Subgroup.zpowers ψ := by
  have hcom : ∀ l ∈ L, l * ψ' = ψ' * l := by
    intro l hl
    have h1 : ⁅l, ψ'⁆ ∈ ⁅L, L'⁆ := Subgroup.commutator_mem_commutator hl hψ'
    rw [hcomm, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  refine ⟨hcom ψ hψ, fun hmem => ?_⟩
  have hψ'L : ψ' ∈ L := (Subgroup.zpowers_le.2 hψ) hmem
  have hz : (⟨ψ', hψ'L⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro c
    exact Subtype.ext (hcom c c.2)
  rw [hc, Subgroup.mem_bot] at hz
  exact hψ'1 (congrArg Subtype.val hz)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
