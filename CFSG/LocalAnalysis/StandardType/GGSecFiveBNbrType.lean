module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestOriginalWeyl
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordConj
import CFSG.LocalAnalysis.StandardType.GGSecFiveBFixLine
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPosition

public section

namespace CFSG.StandardType

private theorem conj_inv_comp_conj_eq_id {E : Type*} [Group E] (δ : MulAut E) :
    (MulAut.conj δ⁻¹).toMonoidHom.comp (MulAut.conj δ).toMonoidHom =
      MonoidHom.id (MulAut E) := by
  refine MonoidHom.ext fun φ => ?_
  show MulAut.conj δ⁻¹ (MulAut.conj δ φ) = φ
  rw [MulAut.conj_apply, MulAut.conj_apply]
  group

private theorem map_conj_inv_map_conj_mulAut {E : Type*} [Group E] (δ : MulAut E)
    (A : Subgroup (MulAut E)) :
    (A.map (MulAut.conj δ).toMonoidHom).map (MulAut.conj δ⁻¹).toMonoidHom = A := by
  rw [Subgroup.map_map, conj_inv_comp_conj_eq_id, Subgroup.map_id]

theorem GGSecFiveRouteCfg.nbr_coordType_of_card_fix {G : Type} [Group G] [Finite G] {p n : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    {y : G} {K : Subgroup G} (hn : GGNbr p B x D J y K)
    (hK : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hfix : Nat.card {b : ↥Bs // ∀ φ ∈ ggAutomizer K Bs, φ b = b} = p) :
    (∃ j : Fin n, (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j ∨
        (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = dCoordinateBlock n p j) ∨
      ∃ δ ∈ bSignedFull n p, (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
        (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom := by
  obtain ⟨hp, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  have hΓ : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom ≤ bSignedFull n p := by
    rw [← hEta]
    exact Subgroup.map_mono hK
  have hW : GGWeylReflectionGroup p (ggAutomizer K Bs) :=
    hR.1.weylReflectionGroup_nbr hX hTCJ hRig hTPn hA8 hraw hiso hR.2.1 hn
  obtain ⟨δ, hδ, i0, hblock⟩ := exists_conj_eq_block_of_weyl hp hp2 eta hΓ hW hfix
  have hback : (((ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom).map
      (MulAut.conj δ).toMonoidHom).map (MulAut.conj δ⁻¹).toMonoidHom =
      (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom :=
    map_conj_inv_map_conj_mulAut δ _
  rcases hblock with hB0 | hD0 | hSigma
  · obtain ⟨j, hj⟩ := exists_map_conj_bCoordinateBlock (inv_mem hδ) i0
    exact Or.inl ⟨j, Or.inl (by rw [← hback, hB0, hj])⟩
  · obtain ⟨j, hj⟩ := exists_map_conj_dCoordinateBlock (inv_mem hδ) i0
    exact Or.inl ⟨j, Or.inr (by rw [← hback, hD0, hj])⟩
  · exact Or.inr ⟨δ⁻¹, inv_mem hδ, by rw [← hback, hSigma]⟩

theorem GGSecFiveRouteCfg.nbr_coordType {G : Type} [Group G] [Finite G] {p n : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hFC : GGResNbrFixCentralizesInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B = Bs)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    {y : G} {K : Subgroup G} (hn : GGNbr p B x D J y K)
    (hK : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) :
    (∃ j : Fin n, (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j ∨
        (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = dCoordinateBlock n p j) ∨
      ∃ δ ∈ bSignedFull n p, (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
        (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom := by
  obtain ⟨hp, -, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  obtain ⟨-, hBs, -, -, -⟩ := hR.1.1.tableB_facts
  exact hR.nbr_coordType_of_card_fix hX hTCJ hRig hTPn hA8 hraw hiso eta hEta hn hK
    ((hR.1.fixLineComp_nbr hFC hR.2.1 hB hn).card_fix hp hBs hn.1.2.2.1)

end CFSG.StandardType

end
