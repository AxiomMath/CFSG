module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowFstarLift
public import CFSG.GroupTheory.MulAutCongr
import CFSG.Goldschmidt.Steps.G3b35Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Monster.B.Fischer.Fi22Model

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Monster.B.Fischer
open CFSG.Sporadic.FischerOddCore

private lemma fi22tr_fi22RAut_symm_conj
    (g : ↥fi22P) :
    fi22RAut.symm (MulAut.conj g) =
      ⟨(g : Equiv.Perm (Fin 3510)), fi22P_le_R g.2⟩ := by
  have hconj : fi22RAut ⟨(g : Equiv.Perm (Fin 3510)), fi22P_le_R g.2⟩ = MulAut.conj g := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [MulAut.conj_apply, fi22RAut_apply, fi22ConjHom_apply]
    rfl
  rw [← hconj, MulEquiv.symm_apply_apply]

theorem fi22_outer_transport
    {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hLn : (L.subgroupOf Y).Normal) (hF : Fstar Y = L) (hq : IsQuasisimple ↥L)
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* CFSG.Blueprint.NativeSporadic.Fi22) :
    ∃ F : ↥Y →* Equiv.Perm (Fin 3510), (∀ y : ↥Y, F y ∈ fi22R) ∧
      (∀ l : ↥L, F (Subgroup.inclusion hLY l) ∈ fi22P) ∧
      (∀ p ∈ fi22P, ∃ l : ↥L, F (Subgroup.inclusion hLY l) = p) ∧
      (∀ y : ↥Y, F y ∈ fi22P → (y : MulAut W) ∈ L) ∧
      (∀ l : ↥L, F (Subgroup.inclusion hLY l) = 1 → l ∈ Subgroup.center ↥L) := by
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  let L' : Subgroup ↥Y := L.subgroupOf Y
  haveI : L'.Normal := hLn
  let ι : ↥L' ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLY
  have hperf' : commutator ↥L' = ⊤ := by
    haveI : Group.IsPerfect ↥L := hq.1
    haveI : Group.IsPerfect ↥L' :=
      Group.IsPerfect.ofSurjective (f := ι.symm.toMonoidHom) ι.symm.surjective
    exact Group.IsPerfect.commutator_eq_top
  let qiso : ↥L' ⧸ Subgroup.center ↥L' ≃* ↥L ⧸ Subgroup.center ↥L :=
    QuotientGroup.congr (Subgroup.center ↥L') (Subgroup.center ↥L) ι (Subgroup.map_center_eq ι)
  let ψ : ↥L' ⧸ Subgroup.center ↥L' ≃* ↥fi22P := qiso.trans (e.trans fi22PermEquiv)
  let Ψ : ↥Y →* MulAut (↥L' ⧸ Subgroup.center ↥L') := CFSG.Goldschmidt.G3b.conjQuot L'
  let Φ : ↥Y →* MulAut ↥fi22P := (MulAut.congr ψ).toMonoidHom.comp Ψ
  let F : ↥Y →* Equiv.Perm (Fin 3510) :=
    fi22R.subtype.comp (fi22RAut.symm.toMonoidHom.comp Φ)
  have hPhi : ∀ l : ↥L, Φ (Subgroup.inclusion hLY l) =
      MulAut.conj (ψ ((ι.symm l : ↥L') : ↥L' ⧸ Subgroup.center ↥L')) := by
    intro l
    have hAl : (Subgroup.inclusion hLY l : ↥Y) = (ι.symm l : ↥Y) := by
      apply Subtype.ext
      rw [Subgroup.coe_inclusion]
      rfl
    have hΨl : Ψ (Subgroup.inclusion hLY l) =
        MulAut.conj (((ι.symm l : ↥L') : ↥L' ⧸ Subgroup.center ↥L')) := by
      rw [hAl]
      exact CFSG.Goldschmidt.G3b.conjQuot_of_mem L' (ι.symm l).2
    calc Φ (Subgroup.inclusion hLY l)
        = MulAut.congr ψ (Ψ (Subgroup.inclusion hLY l)) := rfl
      _ = MulAut.congr ψ
            (MulAut.conj (((ι.symm l : ↥L') : ↥L' ⧸ Subgroup.center ↥L'))) := by
            rw [hΨl]
      _ = MulAut.conj (ψ ((ι.symm l : ↥L') : ↥L' ⧸ Subgroup.center ↥L')) :=
            CFSG.mulAut_congr_conj ψ _
  have hFval : ∀ l : ↥L, F (Subgroup.inclusion hLY l) =
      ((ψ ((ι.symm l : ↥L') : ↥L' ⧸ Subgroup.center ↥L') : ↥fi22P) :
        Equiv.Perm (Fin 3510)) := by
    intro l
    show ((fi22RAut.symm (Φ (Subgroup.inclusion hLY l)) : ↥fi22R) :
      Equiv.Perm (Fin 3510)) = ((ψ ((ι.symm l : ↥L') :
        ↥L' ⧸ Subgroup.center ↥L') : ↥fi22P) : Equiv.Perm (Fin 3510))
    rw [hPhi l, fi22tr_fi22RAut_symm_conj]
  refine ⟨F, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    exact (fi22RAut.symm (Φ y)).2
  · intro l
    rw [hFval l]
    exact (ψ ((ι.symm l : ↥L') : ↥L' ⧸ Subgroup.center ↥L')).2
  · intro p hp
    let p' : ↥fi22P := ⟨p, hp⟩
    obtain ⟨l', hl'⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L') (ψ.symm p')
    refine ⟨ι l', ?_⟩
    rw [hFval (ι l'), MulEquiv.symm_apply_apply]
    have hl'' : ((l' : ↥L') : ↥L' ⧸ Subgroup.center ↥L') = ψ.symm p' := hl'
    rw [hl'', MulEquiv.apply_symm_apply]
  · intro y hyP
    let g : ↥fi22P := ⟨F y, hyP⟩
    obtain ⟨l', hl'⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L') (ψ.symm g)
    have hFl : F (Subgroup.inclusion hLY (ι l')) = F y := by
      rw [hFval (ι l'), MulEquiv.symm_apply_apply]
      have hl'' : ((l' : ↥L') : ↥L' ⧸ Subgroup.center ↥L') = ψ.symm g := hl'
      rw [hl'', MulEquiv.apply_symm_apply]
    have hPhiEq : Φ y = Φ (Subgroup.inclusion hLY (ι l')) := by
      apply fi22RAut.symm.injective
      apply Subtype.ext
      change F y = F (Subgroup.inclusion hLY (ι l'))
      rw [hFl]
    have hprod : Φ (y * (Subgroup.inclusion hLY (ι l'))⁻¹) = 1 := by
      rw [map_mul, map_inv, hPhiEq, mul_inv_cancel]
    have hΨ1 : Ψ (y * (Subgroup.inclusion hLY (ι l'))⁻¹) = 1 := by
      apply (MulAut.congr ψ).injective
      rw [map_one]
      exact hprod
    have hcentY : (y * (Subgroup.inclusion hLY (ι l'))⁻¹ : ↥Y) ∈
        Subgroup.centralizer (L' : Set ↥Y) :=
      (CFSG.Goldschmidt.G3b.conjQuot_eq_one_iff L' hperf' _).mp hΨ1
    have hcentW : ((y : MulAut W) * ((ι l' : ↥L) : MulAut W)⁻¹) ∈
        Subgroup.centralizer (L : Set (MulAut W)) := by
      rw [Subgroup.mem_centralizer_iff] at hcentY ⊢
      intro x hx
      have hxL' : (⟨x, hLY hx⟩ : ↥Y) ∈ L' := hx
      have h := hcentY ⟨x, hLY hx⟩ hxL'
      have h' := congrArg (fun w : ↥Y => (w : MulAut W)) h
      simpa [Subgroup.coe_inclusion] using h'
    have hmemY : ((y : MulAut W) * ((ι l' : ↥L) : MulAut W)⁻¹) ∈ Y :=
      Y.mul_mem y.2 (Y.inv_mem (hLY (ι l').2))
    have hprodL : (y : MulAut W) * ((ι l' : ↥L) : MulAut W)⁻¹ ∈ L :=
      mem_of_mem_centralizer_of_fstar_eq hLY hF hmemY hcentW
    have hy_eq : (y : MulAut W) =
        ((y : MulAut W) * ((ι l' : ↥L) : MulAut W)⁻¹) * ((ι l' : ↥L) : MulAut W) := by
      group
    rw [hy_eq]
    exact L.mul_mem hprodL (ι l').2
  · intro l hl1
    have hperm : ((ψ ((ι.symm l : ↥L') : ↥L' ⧸ Subgroup.center ↥L') : ↥fi22P) :
        Equiv.Perm (Fin 3510)) = 1 := by
      rw [← hFval l, hl1]
    have hψ1 : ψ ((ι.symm l : ↥L') : ↥L' ⧸ Subgroup.center ↥L') = 1 := by
      apply Subtype.ext
      simpa using hperm
    have hl'1 : ((ι.symm l : ↥L') : ↥L' ⧸ Subgroup.center ↥L') = 1 := by
      apply ψ.injective
      rw [hψ1, map_one]
    have hl'mem : ι.symm l ∈ Subgroup.center ↥L' :=
      (QuotientGroup.eq_one_iff (ι.symm l)).mp hl'1
    have hmap : ι (ι.symm l) ∈ Subgroup.center ↥L := by
      have h : ι (ι.symm l) ∈ (Subgroup.center ↥L').map (ι : ↥L' →* ↥L) :=
        Subgroup.mem_map_of_mem (ι : ↥L' →* ↥L) hl'mem
      rwa [Subgroup.map_center_eq ι] at h
    rwa [MulEquiv.apply_symm_apply] at hmap

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
