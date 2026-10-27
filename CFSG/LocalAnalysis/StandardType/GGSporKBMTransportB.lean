module

public import CFSG.LocalAnalysis.StandardType.GGSporKBMTransportCore
public import CFSG.LocalAnalysis.StandardType.GGSporKBSevenOrd
import CFSG.Fischer.Classification.Recognition.Basic

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly
open scoped commutatorElement

variable {K K' : Type} [Group K] [Finite K] [Group K'] [Finite K']

private theorem gkB_simple_pullback (e : K ≃* K') {L' : Subgroup K'} (hL' : IsSimpleGroup ↥L') :
    IsSimpleGroup ↥(L'.map e.symm.toMonoidHom) :=
  (L'.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm.isSimpleGroup

theorem bmOrd_of_mulEquiv (p : ℕ) (e : K ≃* K') (h : BMOrd p K) : BMOrd p K' := by
  intro L' hL' hmark
  have eL : ↥L' ≃* ↥(L'.map e.symm.toMonoidHom) :=
    L'.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
  have hLs := gkB_simple_pullback e hL'
  have hLm := largeEvenMarking_true_of_mulEquiv eL hmark
  have h1 := h _ hLs hLm
  rwa [Nat.card_congr e.toEquiv, (Nat.card_congr (MulAut.congr eL).toEquiv).symm] at h1

theorem bSevenOrd_of_mulEquiv (e : K ≃* K') (h : BSevenOrd K) : BSevenOrd K' := by
  intro L' hL' hmark
  have eL : ↥L' ≃* ↥(L'.map e.symm.toMonoidHom) :=
    L'.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
  have hLs := gkB_simple_pullback e hL'
  have hLm := largeEvenMarking_true_of_mulEquiv eL hmark
  have h1 := h _ hLs hLm
  rwa [(Nat.card_congr (MulAut.congr eL).toEquiv).symm, (Nat.card_congr eL.toEquiv).symm] at h1

theorem bmNoLiePComp_of_mulEquiv (p : ℕ) (e : K ≃* K') (h : BMNoLiePComp p K) :
    BMNoLiePComp p K' := by
  intro x' hx' C' hC' hmark
  have hx : orderOf (e.symm x') = p := by rw [MulEquiv.orderOf_eq]; exact hx'
  have hC : LargeEvenPComponent p (Subgroup.centralizer {e.symm x'})
      (C'.map e.symm.toMonoidHom) := by
    rw [← CFSG.Fischer.Classification.Recognition.map_centralizer_singleton e.symm x']
    exact (largeEvenPComponent_map_mulEquiv p e.symm _ _).mpr hC'
  obtain ⟨iso⟩ := bmPSubquot_mulEquiv p e (x := e.symm x') (x' := x') (e.apply_symm_apply x')
    (C := C'.map e.symm.toMonoidHom) (C' := C') (by
      rw [Subgroup.map_map]
      have h1 : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id K' :=
        MonoidHom.ext fun y => e.apply_symm_apply y
      rw [h1, Subgroup.map_id])
  exact h _ hx _ hC (largeEvenMarking_true_of_mulEquiv iso.symm hmark)

theorem bmElevenComp_of_mulEquiv (e : K ≃* K') (h : BMElevenComp K) : BMElevenComp K' := by
  intro x' hx'
  have hx : orderOf (e.symm x') = 11 := by rw [MulEquiv.orderOf_eq]; exact hx'
  obtain ⟨C, hC, hnot⟩ := h (e.symm x') hx
  refine ⟨C.map e.toMonoidHom, ?_, ?_⟩
  · have h1 := (largeEvenPComponent_map_mulEquiv 11 e (Subgroup.centralizer {e.symm x'}) C).mpr hC
    rwa [CFSG.Fischer.Classification.Recognition.map_centralizer_singleton e (e.symm x'),
      e.apply_symm_apply] at h1
  · intro hmark'
    obtain ⟨iso⟩ := bmPSubquot_mulEquiv 11 e (x := e.symm x') (x' := x')
      (e.apply_symm_apply x') (C := C) (C' := C.map e.toMonoidHom) rfl
    exact hnot (largeEvenMarking_true_of_mulEquiv iso.symm hmark')

end CFSG.StandardType.SporadicShape
