module

public import CFSG.Sporadic.Th
public import CFSG.Sporadic.Th.Certificate
public import CFSG.Sporadic.Bridge.Common
public import CFSG.Sporadic.Bridge.ThData
public import CFSG.Sporadic.Presentation.Th
public meta import CFSG.Sporadic.Bridge.ThData
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Certificate9131
public import CFSG.Sporadic.Bridge.ThSurjInputs
public import Certificates.Certificate9220
public import Certificates.Certificate1021
public import Certificates.Certificate1020
public import Certificates.Certificate1022
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.Certificates.CosetTableShort
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.ThBase
public import CFSG.Sporadic.Th.CertificateBase
public import CFSG.Sporadic.Th.CertificateBase1
public import CFSG.Sporadic.ThSchreier.KernelAut
public import CFSG.Sporadic.ThSchreier.KernelAutBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase1
public import Certificates.Certificate9131Base

public section

namespace CFSG.Sporadic.Bridge.Th

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native TauCeti

theorem bridge_check : thCheck pres.relatorLetters = true := by
  exact Certificates.certificate9220

private theorem presentation_eq : SporadicName.Th.presentation = pres := rfl

structure BridgeFacts : Prop where
  size : imgMats.size = 8
  inv : invsOK imgMats (imgMats.map invRows) = true
  relsOK : ∀ r ∈ pres.relatorLetters,
    eqRows (wordRows imgMats (imgMats.map invRows) r) idRows = true
  stdA : eqRows (wordRows imgMats (imgMats.map invRows) (stdWords[0]?.getD [])) (rowsOf seedA) =
    true
  stdB : eqRows (wordRows imgMats (imgMats.map invRows) (stdWords[1]?.getD [])) (rowsOf seedB) =
    true

theorem bridgeFacts : BridgeFacts := by
  have h := bridge_check
  unfold thCheck inverseChecks imageChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem invsOK_mul {I Iv : Array (Array V4)} (h : invsOK I Iv = true) {k : ℕ} (hk : k < I.size) :
    rowsMatrix (I[k]?.getD idRows) * rowsMatrix (Iv[k]?.getD idRows) = 1 := by
  unfold invsOK at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  have := eqRows_iff.1 (h.2 k (List.mem_range.2 hk))
  rw [← rowsMatrix_mulRows, this, rowsMatrix_idRows]

theorem img_mul_inv {k : ℕ} (hk : k < 8) :
    rowsMatrix (imgMats[k]?.getD idRows) * rowsMatrix ((imgMats.map invRows)[k]?.getD idRows) =
      1 :=
  invsOK_mul bridgeFacts.inv (by rw [bridgeFacts.size]; exact hk)

@[expose] noncomputable def imgGL (k : ℕ) : GL (Fin 248) (ZMod 2) :=
  if h : k < 8 then
    ⟨rowsMatrix (imgMats[k]?.getD idRows), rowsMatrix ((imgMats.map invRows)[k]?.getD idRows),
      img_mul_inv h, mul_eq_one_comm.1 (img_mul_inv h)⟩
  else 1

theorem imgMats_spec (k : ℕ) : rowsMatrix (imgMats[k]?.getD idRows) =
    ((imgGL k : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2)) := by
  by_cases hk : k < 8
  · rw [imgGL, dite_eq_left hk]
    try rfl
  · have : imgMats[k]? = none := Array.getElem?_eq_none (by rw [bridgeFacts.size]; omega)
    rw [imgGL, dite_eq_right hk, this, Option.getD_none, rowsMatrix_idRows]
    try rfl

theorem imgInvs_spec
    (k : ℕ) : rowsMatrix ((imgMats.map invRows)[k]?.getD idRows) =
    (((imgGL k)⁻¹ : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2)) := by
  by_cases hk : k < 8
  · rw [imgGL, dite_eq_left hk]
    try rfl
  · have : (imgMats.map invRows)[k]? = none :=
      Array.getElem?_eq_none (by rw [Array.size_map, bridgeFacts.size]; omega)
    rw [imgGL, dite_eq_right hk, this, Option.getD_none, rowsMatrix_idRows, inv_one]
    try rfl

theorem rowsMatrix_imgWord (w : List (ℕ × Bool)) :
    rowsMatrix (wordRows imgMats (imgMats.map invRows) w) =
      ((wordProd imgGL w : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2)) := by
  unfold wordRows wordProd
  suffices ∀ (acc : Array V4) (g : GL (Fin 248) (ZMod 2)),
      rowsMatrix acc = (g : Matrix (Fin 248) (Fin 248) (ZMod 2)) →
      rowsMatrix (w.foldl (fun acc l => mulRows acc (letterRows imgMats (imgMats.map invRows) l))
        acc) =
        ((g * (w.map fun l => if l.2 then imgGL l.1 else (imgGL l.1)⁻¹).prod :
          GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2)) by
    simpa using this idRows 1 (by rw [rowsMatrix_idRows]; rfl)
  induction w with
  | nil => intro acc g h; simpa using h
  | cons l w ih =>
    intro acc g h
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    apply ih
    rw [rowsMatrix_mulRows, h, Units.val_mul]
    congr 1
    unfold letterRows
    split_ifs
    · exact imgMats_spec _
    · exact imgInvs_spec _

theorem hrel : ∀ v ∈ pres.relatorLetters, wordProd imgGL v = 1 := by
  intro v hv
  have e := rowsMatrix_imgWord v
  rw [eqRows_iff.1 (bridgeFacts.relsOK v hv), rowsMatrix_idRows] at e
  exact Units.ext e.symm

noncomputable def φ :
    pres.Group →* GL (Fin 248) (ZMod 2) := presHom _ imgGL hrel

theorem generatorCount_eq : pres.generatorCount = 8 := rfl

theorem imgGL_mem_range (k : ℕ) : imgGL k ∈ φ.range := by
  by_cases hk : k < 8
  · exact ⟨presGen _ k, presHom_presGen _ _ _ (by rw [generatorCount_eq]; exact hk)⟩
  · rw [imgGL, dite_eq_right hk]
    exact φ.range.one_mem

theorem wordProd_std_mem
    (i : ℕ) : wordProd imgGL (stdWords[i]?.getD []) ∈ φ.range :=
  wordProd_mem imgGL_mem_range _

theorem std_gA :
    wordProd imgGL (stdWords[0]?.getD []) = gA := by
  have e := rowsMatrix_imgWord (stdWords[0]?.getD [])
  rw [eqRows_iff.1 bridgeFacts.stdA, rowsMatrix_rowsOf_seedA] at e
  exact Units.ext e.symm

theorem std_gB :
    wordProd imgGL (stdWords[1]?.getD []) = gB := by
  have e := rowsMatrix_imgWord (stdWords[1]?.getD [])
  rw [eqRows_iff.1 bridgeFacts.stdB, rowsMatrix_rowsOf_seedB] at e
  exact Units.ext e.symm

theorem J_le_range : J ≤ φ.range := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · rw [← std_gA]
    exact wordProd_std_mem 0
  · rw [← std_gB]
    exact wordProd_std_mem 1

theorem card_J_of
    {c : ℕ} (hC : CertFacts c) : Nat.card J = 90745943887872000 := by
  have := isPretransitive hC
  have h := Subgroup.card_mul_index (MulAction.stabilizer J (root hC))
  rw [MulAction.index_stabilizer, card_stabilizer_root hC, MulAction.orbit_eq_univ,
    Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin, hC.count] at h
  omega

theorem card_J :
    Nat.card J = 90745943887872000 := CFSG.Sporadic.Th.Kernel.card_J_eq th_kernel_facts

theorem nonempty_mulEquiv_of_le_range
    {P : Type*} [Group P] [Finite P]
    (ψ : P →* GL (Fin 248) (ZMod 2)) (hJ : J ≤ ψ.range) (hP : Nat.card P ≤ Nat.card J) :
    Nonempty (J ≃* P) := by
  have hrange : Nat.card ψ.range ≤ Nat.card P :=
    Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective ψ)
  have hEq : J = ψ.range := Subgroup.eq_of_le_of_card_ge hJ (hrange.trans hP)
  have hmem : ∀ x, ψ x ∈ J := fun x => hEq ▸ ⟨x, rfl⟩
  let ψ' : P →* J := ψ.codRestrict J hmem
  have hψ' : Function.Surjective ψ' := by
    intro j
    obtain ⟨x, hx⟩ : (j : GL (Fin 248) (ZMod 2)) ∈ ψ.range := hEq ▸ j.2
    exact ⟨x, Subtype.ext hx⟩
  exact ⟨(MulEquiv.ofBijective ψ' (hψ'.bijective_of_nat_card_le hP)).symm⟩

theorem nonempty_mulEquiv_of_card_le
    (hfin : Finite SporadicName.Th.Group)
    (hcard : Nat.card SporadicName.Th.Group ≤ 90745943887872000) :
    Nonempty (Blueprint.NativeSporadic.Th ≃* SporadicName.Th.Group) := by
  revert hfin hcard
  show Finite SporadicName.Th.presentation.Group →
    Nat.card SporadicName.Th.presentation.Group ≤ 90745943887872000 →
    Nonempty (Blueprint.NativeSporadic.Th ≃* SporadicName.Th.presentation.Group)
  rw [presentation_eq]
  intro hfin hcard
  obtain ⟨e⟩ := nonempty_mulEquiv_of_le_range φ J_le_range (hcard.trans card_J.symm.le)
  exact ⟨thEquivJ.trans e⟩

theorem nonempty_mulEquiv :
    Nonempty (Blueprint.NativeSporadic.Th ≃* SporadicName.Th.Group) :=
  nonempty_mulEquiv_of_card_le Presentation.Th.finite_card_le.1 Presentation.Th.finite_card_le.2

end CFSG.Sporadic.Bridge.Th
