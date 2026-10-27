module

public import CFSG.Monster.B.TwoA.Fischer.CanonicalIdent
public import CFSG.Monster.B.TwoA.Fischer.CertGram
public import CFSG.Monster.B.TwoA.Fischer.GramData

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Fischer CFSG.Monster.B.TwoA CFSG.Monster.B.Classical.Mog22
  CFSG.Sporadic.SmallF2
open scoped IsMulCommutative Matrix

theorem jWord_mem_J :
    ∀ w : List ℕ, (∀ k ∈ w, k < 13) → Cert.jWord w ∈ J
  | [], _ => J.one_mem
  | k :: w, hw => by
    have hk : jGen k ∈ J := by
      rw [J_eq_closure_jGen]
      exact Subgroup.subset_closure ⟨⟨k, hw k List.mem_cons_self⟩, rfl⟩
    exact J.mul_mem hk (jWord_mem_J w fun k' hk' => hw k' (List.mem_cons_of_mem k hk'))

theorem jWord_labelWord_mem_J
    {i : ℕ} (hi : i < 78) : Cert.jWord (Cert.labelWord i) ∈ J :=
  jWord_mem_J _ (Cert.fischer_gram_minor_certificate.2.1 i hi)

theorem rowsMatrix_gramRowArr (i k : Fin 78) :
    rowsMatrix 78 Cert.gramRowArr i k = if (Cert.gramRow i).testBit k then 1 else 0 := by
  rw [rowsMatrix_apply, toVecD_apply, Cert.gramRow, Array.getElem!_eq_getD,
    Array.getD_eq_getD_getElem?]
  rfl

theorem gramMinor_det_ne_zero :
    (rowsMatrix 78 Cert.gramRowArr).det ≠ 0 :=
  Cert.fischer_gram_minor_certificate.2.2.2.2.2

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

variable (Y) in
@[expose] def gramPt
    (Φ : Y ≃ CFSG.Monster.B.Fischer.Y) (i : ℕ) : Y :=
  Φ.symm (Cert.jWord (Cert.labelWord i) o)

theorem ι_gramPt
    (Φ : Y ≃ CFSG.Monster.B.Fischer.Y) {i : ℕ} (hi : i < 78) :
    (ι (Φ (gramPt Y Φ i)) : ℕ) = Cert.basisPt i := by
  rw [gramPt, Equiv.apply_symm_apply]
  exact Cert.ι_jWord_o hi

theorem eq_gramPt_of_ι
    (Φ : Y ≃ CFSG.Monster.B.Fischer.Y) {i : ℕ} (hi : i < 78) {y : Y}
    (hy : (ι (Φ y) : ℕ) = Cert.basisPt i) : y = gramPt Y Φ i :=
  Φ.injective (ι_injective (Fin.ext (hy.trans (ι_gramPt Φ hi).symm)))

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y) {Φ : Y ≃ CFSG.Monster.B.Fischer.Y}
  {ψ : sliceGroup lab Y ≃* J}
  (hψ : ∀ (h : sliceGroup lab Y) (v w : Y), (w : V) = act (h : S) v →
    (ψ h : Equiv.Perm CFSG.Monster.B.Fischer.Y) (Φ v) = Φ w)
  {x : V} (hx : x ∈ Y) (hxo : Φ ⟨x, hx⟩ = o)
  (hxT : (ψ ⟨lab x, lab_mem_sliceGroup hx⟩ : Equiv.Perm CFSG.Monster.B.Fischer.Y) = tPerm)
include hS hψ hxo hxT

theorem psi_lab_gramPt
    {i : ℕ} (hi : i < 78) :
    (ψ ⟨lab (gramPt Y Φ i), lab_mem_sliceGroup (gramPt Y Φ i).2⟩ :
      Equiv.Perm CFSG.Monster.B.Fischer.Y) = Cert.jLabel (Cert.labelWord i) := by
  set g : J := ⟨Cert.jWord (Cert.labelWord i), jWord_labelWord_mem_J hi⟩ with hg
  set h : sliceGroup lab Y := ψ.symm g with hh
  have hψh : ψ h = g := ψ.apply_symm_apply g
  have hmem : act (h : S) x ∈ Y := hS.mapsTo _ h.2 x hx
  have h1 := hψ h ⟨x, hx⟩ ⟨act (h : S) x, hmem⟩ rfl
  rw [hxo, hψh] at h1
  have h1' : Cert.jWord (Cert.labelWord i) o = Φ ⟨act (h : S) x, hmem⟩ := h1
  have h2 : (⟨act (h : S) x, hmem⟩ : Y) = gramPt Y Φ i := by
    rw [gramPt, h1', Equiv.symm_apply_apply]
  have h3 : (⟨lab (gramPt Y Φ i), lab_mem_sliceGroup (gramPt Y Φ i).2⟩ : sliceGroup lab Y) =
      h * ⟨lab x, lab_mem_sliceGroup hx⟩ * h⁻¹ := by
    rw [← h2]
    exact Subtype.ext (hS.lab_act (h : S) x)
  rw [h3, map_mul, map_mul, map_inv, hψh, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    hxT]
  rfl

theorem ncommInd_gramPt
    {i : ℕ} (hi : i < 78) (z : Y) :
    ncommInd lab (gramPt Y Φ i) z = if (Cert.ncRow i).testBit (ι (Φ z)) then 1 else 0 := by
  have hfix : Commute (lab (gramPt Y Φ i)) (lab z) ↔
      ¬(Cert.ncRow i).testBit (ι (Φ z)) = true := by
    rw [← hS.act_lab_eq_iff (gramPt Y Φ i).2 z.2, ← Cert.jLabel_ne_iff hi, not_not,
      ← hS.psi_lab_gramPt hψ hx hxo hxT hi,
      hψ _ z ⟨act (lab (gramPt Y Φ i)) z, hS.mapsTo _ (lab_mem_sliceGroup (gramPt Y Φ i).2) z z.2⟩
        rfl, Φ.injective.eq_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  by_cases hb : (Cert.ncRow i).testBit (ι (Φ z)) = true
  · rw [ncommInd_of_not_commute lab (fun h => hfix.1 h hb), ite_eq_left hb]
  · rw [ncommInd_of_commute lab (hfix.2 hb), ite_eq_right hb]

theorem ncommQuotForm_gramPt
    (i k : Fin 78) :
    ncommQuotForm lab Y (ncommVec lab Y (gramPt Y Φ i)) (ncommVec lab Y (gramPt Y Φ k)) =
      rowsMatrix 78 Cert.gramRowArr i k := by
  rw [ncommQuotForm_ncommVec, hS.ncommInd_gramPt hψ hx hxo hxT i.2, ι_gramPt Φ k.2,
    rowsMatrix_gramRowArr, Cert.testBit_gramRow i.2 k.2]

theorem linearIndependent_gramPt :
    LinearIndependent (ZMod 2) fun i : Fin 78 => ncommVec lab Y (gramPt Y Φ i) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hvec : g ᵥ* rowsMatrix 78 Cert.gramRowArr = 0 := by
    funext k
    have h1 := congrArg (fun a => ncommQuotForm lab Y a (ncommVec lab Y (gramPt Y Φ k))) hg
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      map_zero, LinearMap.zero_apply] at h1
    show ∑ i, g i * rowsMatrix 78 Cert.gramRowArr i k = 0
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h1
    rw [hS.ncommQuotForm_gramPt hψ hx hxo hxT i k]
  exact congrFun (Matrix.eq_zero_of_vecMul_eq_zero gramMinor_det_ne_zero hvec)

theorem le_finrank_ncommQuot :
    78 ≤ Module.finrank (ZMod 2) (NcommQuot lab Y) := by
  have : Finite Y := hS.finite.to_subtype
  have h := (hS.linearIndependent_gramPt hψ hx hxo hxT).fintype_card_le_finrank
  rwa [Fintype.card_fin] at h

theorem gram_minor_of_identification :
    (List.range 78).map Cert.basisPt =
      [0, 1, 2, 3, 4, 6, 7, 8, 10, 12, 14, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 34, 38,
        39, 40, 42, 54, 55, 56, 57, 58, 59, 60, 62, 63, 64, 66, 70, 71, 72, 74, 86, 87, 88, 90,
        94, 102, 118, 150, 151, 152, 154, 158, 166, 182, 278, 279, 282, 286, 294, 310, 406, 534,
        535, 538, 566, 1046, 1047, 1078, 1110, 1174, 1270, 1334, 1462, 1686, 1942, 2326] ∧
    (∀ i : Fin 78, ∃! y : Y, (ι (Φ y) : ℕ) = Cert.basisPt i) ∧
    (∀ (i k : Fin 78) (y z : Y), (ι (Φ y) : ℕ) = Cert.basisPt i →
      (ι (Φ z) : ℕ) = Cert.basisPt k →
      ncommQuotForm lab Y (ncommVec lab Y y) (ncommVec lab Y z) =
        rowsMatrix 78 Cert.gramRowArr i k) ∧
    (rowsMatrix 78 Cert.gramRowArr).det ≠ 0 ∧
    78 ≤ Module.finrank (ZMod 2) (NcommQuot lab Y) := by
  refine ⟨Cert.fischer_gram_minor_certificate.1, fun i => ⟨gramPt Y Φ i, ι_gramPt Φ i.2,
    fun y hy => eq_gramPt_of_ι Φ i.2 hy⟩, fun i k y z hy hz => ?_, gramMinor_det_ne_zero,
    hS.le_finrank_ncommQuot hψ hx hxo hxT⟩
  rw [eq_gramPt_of_ι Φ i.2 hy, eq_gramPt_of_ι Φ k.2 hz]
  exact hS.ncommQuotForm_gramPt hψ hx hxo hxT i k

omit hψ hxo hxT

theorem nondegenerate_gram_minor
    {C : Set V} (hC : IsSliceMaxClique lab Y C)
    [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] {x : V}
    (hx : x ∈ hexadFiber lab Y C ∅) {η : C ≃ X₀}
    {θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
      CFSG.Blueprint.NativeSporadic.M22}
    (hη : ∀ T : Finset C, Subtype.val '' (T : Set C) ∈ cliqueBlocks lab C ↔
      T.image (fun z => (η z : Fin 24)) ∈ ℬ₀)
    (hθ : ∀ (f : setStab act lab Y C) (z : C),
      (η (setStabPerm act lab Y C f z) : Fin 24) = psiHom (θ f) (η z))
    {φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀}
    (hφ : ∀ z : C, φ (Additive.ofMul (cliqueGen z)) = K₀.mkQ (e (η z)))
    {α : setStab act lab Y C →* F₀}
    (hα : ∀ (r : Subgroup.closure (lab '' C)) (f k : setStab act lab Y C),
      (f : S) = r * k → act (k : S) x = x → α f = wF (φ (Additive.ofMul r)) * kF (θ k))
    (hΦ : IsCliqueIntertwiner act lab Y C x η φ α Φ) :
    (List.range 78).map Cert.basisPt =
      [0, 1, 2, 3, 4, 6, 7, 8, 10, 12, 14, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 34, 38,
        39, 40, 42, 54, 55, 56, 57, 58, 59, 60, 62, 63, 64, 66, 70, 71, 72, 74, 86, 87, 88, 90,
        94, 102, 118, 150, 151, 152, 154, 158, 166, 182, 278, 279, 282, 286, 294, 310, 406, 534,
        535, 538, 566, 1046, 1047, 1078, 1110, 1174, 1270, 1334, 1462, 1686, 1942, 2326] ∧
    (∀ i : Fin 78, ∃! y : Y, (ι (Φ y) : ℕ) = Cert.basisPt i) ∧
    (∀ (i k : Fin 78) (y z : Y), (ι (Φ y) : ℕ) = Cert.basisPt i →
      (ι (Φ z) : ℕ) = Cert.basisPt k →
      ncommQuotForm lab Y (ncommVec lab Y y) (ncommVec lab Y z) =
        rowsMatrix 78 Cert.gramRowArr i k) ∧
    (rowsMatrix 78 Cert.gramRowArr).det ≠ 0 ∧
    78 ≤ Module.finrank (ZMod 2) (NcommQuot lab Y) := by
  obtain ⟨ψ, hψ, -, hxT, -⟩ := hS.canonical_permutation_identification hC hx hη hθ hφ hα hΦ
  exact hS.gram_minor_of_identification hψ hx.1
    ((FullIntertwinerHyp.mk hS hC hx hη hθ hφ hα).phi_base hΦ) hxT

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
