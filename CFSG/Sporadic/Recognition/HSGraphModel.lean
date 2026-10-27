module

public import CFSG.Sporadic.Recognition.HSGraphIso
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignWittAut
public import CFSG.Sporadic.Recognition.HSGraphModelInputs
public import Certificates.Certificate6100
meta import CFSG.Sporadic.Recognition.HSGraphDefs
meta import CFSG.Sporadic.Recognition.HSGraphStab
meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignWittAut
meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Hexads
public import Certificates.Certificate2028
public import Certificates.Certificate2031
public import Certificates.Certificate2195
public import Certificates.Certificate1020
public import Certificates.Certificate1022
public import Certificates.Certificate3029
public import Certificates.Certificate2035
public import Certificates.Certificate2039
public import Certificates.Kernel.ThCent.Leaves
public import Certificates.Certificate1020Base

public section

namespace CFSG.Sporadic.Recognition.HSGraph

open CFSG.ComponentClassification.WittDesign
open scoped Pointwise

theorem card_vert_hexads : Fintype.card (Vert hexads) = 100 := by
  rw [card_vert, card_hexads, Fintype.card_fin]

theorem degree_hexads :
    ∀ v : Vert hexads, (hsGraph hexads).degree v = 22 :=
  Certificates.certificate6100.1

theorem commonNeighbors_adj_hexads :
    ∀ v w : Vert hexads, (hsGraph hexads).Adj v w →
    Fintype.card ((hsGraph hexads).commonNeighbors v w) = 0 :=
  Certificates.certificate6100.2.1

theorem commonNeighbors_not_adj_hexads :
    ∀ v w : Vert hexads, v ≠ w → ¬ (hsGraph hexads).Adj v w →
    Fintype.card ((hsGraph hexads).commonNeighbors v w) = 6 :=
  Certificates.certificate6100.2.2.1

theorem isSRGWith_hexads :
    (hsGraph hexads).IsSRGWith 100 22 0 6 where
  card := card_vert_hexads
  regular := degree_hexads
  of_adj := commonNeighbors_adj_hexads
  of_not_adj := fun v w hne hnadj => commonNeighbors_not_adj_hexads v w hne hnadj

theorem modelVertAtF_injective :
    Function.Injective modelVertAtF := by
  have : ∀ i j : Fin 100, modelVertAtF i = modelVertAtF j → i = j :=
    Certificates.certificate6100.2.2.2.1
  exact fun i j h => this i j h

theorem card_vert_hexads_eq :
    Fintype.card (Fin 100) = Fintype.card (Vert hexads) := by
  rw [Fintype.card_fin, card_vert_hexads]

@[expose] noncomputable def modelVertEquiv :
    Fin 100 ≃ Vert hexads :=
  Equiv.ofBijective modelVertAtF
    ((Fintype.bijective_iff_injective_and_card modelVertAtF).2
      ⟨modelVertAtF_injective, card_vert_hexads_eq⟩)

theorem psiInv_left : ∀ i, psiInvFun (psiFun i) = i :=
  Certificates.certificate6100.2.2.2.2.1

theorem psiInv_right : ∀ i, psiFun (psiInvFun i) = i :=
  Certificates.certificate6100.2.2.2.2.2.1

@[expose] def psiPerm : Equiv.Perm (Fin 100) where
  toFun := psiFun
  invFun := psiInvFun
  left_inv := psiInv_left
  right_inv := psiInv_right

theorem psi_check : ∀ i j : Fin 100,
    (hsGraph hexads).Adj (modelVertAtF (psiPerm i)) (modelVertAtF (psiPerm j)) ↔
      (hsGraph hexads).Adj (modelVertAtF i) (modelVertAtF j) :=
  Certificates.certificate6100.2.2.2.2.2.2.1

@[expose] noncomputable def psiAut :
    Equiv.Perm (Vert hexads) :=
  modelVertEquiv.permCongr psiPerm

theorem psiAut_apply (i : Fin 100) :
    psiAut (modelVertEquiv i) = modelVertEquiv (psiPerm i) := by
  simp [psiAut]

theorem psiAut_mem :
    psiAut ∈ autGroup hexads := by
  intro u v
  obtain ⟨i, rfl⟩ := modelVertEquiv.surjective u
  obtain ⟨j, rfl⟩ := modelVertEquiv.surjective v
  rw [psiAut_apply, psiAut_apply]
  exact psi_check i j

theorem psiAut_vInf :
    psiAut vInf = vPt 0 := by
  have h0 : (vInf : Vert hexads) = modelVertEquiv 0 := rfl
  rw [h0, psiAut_apply]
  have : modelVertAtF (psiPerm 0) = vPt 0 := Certificates.certificate6100.2.2.2.2.2.2.2.1
  exact this

theorem psiAut_vPt :
    psiAut (vPt 0) = vBlk (modelBlkAt 0) := by
  have h0 : (vPt 0 : Vert hexads) = modelVertEquiv 1 := rfl
  rw [h0, psiAut_apply]
  have : modelVertAtF (psiPerm 1) = vBlk (modelBlkAt 0) :=
    Certificates.certificate6100.2.2.2.2.2.2.2.2.1
  exact this

theorem sign_extPerm_sigma :
    Equiv.Perm.sign (extPerm (𝓑 := hexads) sigmaPerm sigmaPerm_mem) = -1 :=
  Certificates.certificate6100.2.2.2.2.2.2.2.2.2 sigmaPerm sigmaPerm_mem rfl

@[expose] noncomputable def mdataHexads :
    MData hexads where
  carrier := M22
  le := M22_le_hexadAut
  card := card_M22'
  simple := CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  pt a b := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M22 a b
    exact ⟨g, g.2, hg⟩
  blk B hB C hC := by
    obtain ⟨g₁, h₁⟩ := mem_hexads_iff.1 hB
    obtain ⟨g₂, h₂⟩ := mem_hexads_iff.1 hC
    have hmul : (g₂ * g₁⁻¹) • B = C := by
      rw [← h₂, ← h₁, smul_smul, mul_assoc, inv_mul_cancel, mul_one]
    rw [Subgroup.smul_def, smul_finset_eq_map] at hmul
    exact ⟨_, (g₂ * g₁⁻¹).2, hmul⟩

theorem hsFacts_hexads :
    HSFacts hexads where
  card_aut := card_hexadAut.1
  mdata := ⟨mdataHexads⟩
  srg := isSRGWith_hexads
  psi := ⟨psiAut, psiAut_mem, 0, modelBlkAt 0, psiAut_vInf, psiAut_vPt⟩
  odd := ⟨extPerm sigmaPerm sigmaPerm_mem, extPerm_mem _ _, extPerm_vInf _ _, sign_extPerm_sigma⟩

end CFSG.Sporadic.Recognition.HSGraph
