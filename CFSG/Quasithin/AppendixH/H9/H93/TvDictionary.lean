module

public import CFSG.Quasithin.AppendixH.H9.H93.PsiSign
public import CFSG.Quasithin.AppendixH.H9.H93.TvMatrix
public import CFSG.Quasithin.AppendixH.H9.H93.DictPerm.Sym8InvolutionClasses

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

private theorem mem_Mg_of_isTvElt {g : MulAut (PairN 4)} (h : IsTvElt g) : g ∈ Mg 4 :=
  Lg_le_Mg h.1

private theorem psiExt_mul_mul_inv (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8)) {m g : MulAut (PairN 4)}
    (hm : m ∈ Mg 4) (hg : g ∈ Mg 4) :
    psiExt ψ (m * g * m⁻¹) = ψ ⟨m, hm⟩ * psiExt ψ g * (ψ ⟨m, hm⟩)⁻¹ := by
  have hmg : m * g * m⁻¹ ∈ Mg 4 := (Mg 4).mul_mem ((Mg 4).mul_mem hm hg) ((Mg 4).inv_mem hm)
  rw [psiExt_of_mem ψ hmg, psiExt_of_mem ψ hg]
  have h : (⟨m * g * m⁻¹, hmg⟩ : ↥(Mg 4)) = ⟨m, hm⟩ * ⟨g, hg⟩ * ⟨m, hm⟩⁻¹ := rfl
  rw [h, map_mul, map_mul, map_inv]

private theorem psiExt_injOn_Mg (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8)) :
    Set.InjOn (psiExt ψ) {g | g ∈ Mg 4} := by
  intro g hg g' hg' h
  rw [psiExt_of_mem ψ hg, psiExt_of_mem ψ hg'] at h
  exact congrArg Subtype.val (ψ.injective h)

private theorem psiExt_isTvElt_sq (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8)) {g : MulAut (PairN 4)}
    (h : IsTvElt g) :
    psiExt ψ g ^ 2 = 1 ∧ psiExt ψ g ≠ 1 ∧ Equiv.Perm.sign (psiExt ψ g) = 1 := by
  have hM : g ∈ Mg 4 := mem_Mg_of_isTvElt h
  obtain ⟨hsq, hne⟩ := isTvElt_sq h
  rw [psiExt_of_mem ψ hM]
  refine ⟨?_, ?_, ?_⟩
  · rw [← map_pow]
    have h1 : (⟨g, hM⟩ : ↥(Mg 4)) ^ 2 = 1 := Subtype.ext hsq
    rw [h1, map_one]
  · intro h1
    exact hne (congrArg Subtype.val (ψ.injective (h1.trans (map_one ψ).symm)))
  · have := (mem_Lg_iff_sign ψ hM).1 h.1
    rwa [psiExt_of_mem ψ hM] at this

private theorem isTvElt_iff_cycleType_eq (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8))
    {g₀ g : MulAut (PairN 4)} (hg₀ : IsTvElt g₀) (hg : g ∈ Mg 4) :
    IsTvElt g ↔ (psiExt ψ g).cycleType = (psiExt ψ g₀).cycleType := by
  constructor
  · intro h
    obtain ⟨l, hl, rfl⟩ := isTvElt_exists_conj_Lg hg₀ h
    rw [psiExt_mul_mul_inv ψ (Lg_le_Mg hl) (mem_Mg_of_isTvElt hg₀), Equiv.Perm.cycleType_conj]
  · intro h
    obtain ⟨c, hc⟩ := isConj_iff.1 (Equiv.Perm.isConj_iff_cycleType_eq.2 h.symm)
    set m : ↥(Mg 4) := ψ.symm c with hm
    have hmc : ψ ⟨(m : MulAut (PairN 4)), m.2⟩ = c := by
      rw [hm]
      exact ψ.apply_symm_apply c
    have hmg : (m : MulAut (PairN 4)) * g₀ * (m : MulAut (PairN 4))⁻¹ = g := by
      refine psiExt_injOn_Mg ψ
        ((Mg 4).mul_mem ((Mg 4).mul_mem m.2 (mem_Mg_of_isTvElt hg₀)) ((Mg 4).inv_mem m.2)) hg ?_
      rw [psiExt_mul_mul_inv ψ m.2 (mem_Mg_of_isTvElt hg₀), hmc, hc]
    rw [← hmg]
    exact isTvElt_conj_of_mem_Mg m.2 hg₀

private theorem psiExt_image_isTvElt (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8)) {g₀ : MulAut (PairN 4)}
    (hg₀ : IsTvElt g₀) :
    psiExt ψ '' {g : MulAut (PairN 4) | IsTvElt g} =
      {x : Equiv.Perm (Fin 8) | x.cycleType = (psiExt ψ g₀).cycleType} := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (isTvElt_iff_cycleType_eq ψ hg₀ (mem_Mg_of_isTvElt hg)).1 hg
  · intro hx
    obtain ⟨c, hc⟩ := isConj_iff.1 (Equiv.Perm.isConj_iff_cycleType_eq.2 hx.symm)
    set m : ↥(Mg 4) := ψ.symm c with hm
    have hmc : ψ ⟨(m : MulAut (PairN 4)), m.2⟩ = c := by
      rw [hm]
      exact ψ.apply_symm_apply c
    refine ⟨(m : MulAut (PairN 4)) * g₀ * (m : MulAut (PairN 4))⁻¹,
      isTvElt_conj_of_mem_Mg m.2 hg₀, ?_⟩
    rw [psiExt_mul_mul_inv ψ m.2 (mem_Mg_of_isTvElt hg₀), hmc, hc]

private theorem ncard_isTvElt_eq_ncard_cycleType (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8))
    {g₀ : MulAut (PairN 4)} (hg₀ : IsTvElt g₀) :
    Set.ncard {g : MulAut (PairN 4) | IsTvElt g} =
      Set.ncard {x : Equiv.Perm (Fin 8) | x.cycleType = (psiExt ψ g₀).cycleType} := by
  rw [← psiExt_image_isTvElt ψ hg₀]
  exact ((psiExt_injOn_Mg ψ).mono fun g hg => mem_Mg_of_isTvElt hg).ncard_image.symm

theorem isTvElt_iff_cycleType (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8)) {g : MulAut (PairN 4)}
    (hg : g ∈ Mg 4) : IsTvElt g ↔ (psiExt ψ g).cycleType = {2, 2, 2, 2} := by
  obtain ⟨g₀, hg₀⟩ := exists_isTvElt
  obtain ⟨hsq, hne, hsgn⟩ := psiExt_isTvElt_sq ψ hg₀
  have h2 : (psiExt ψ g₀).cycleType = {2, 2, 2, 2} :=
    cycleType_eq_two_two_two_two_of_ncard_class_le hsq hne hsgn
      ((ncard_isTvElt_eq_ncard_cycleType ψ hg₀).symm.trans_le ncard_isTvElt_le)
  rw [← h2]
  exact isTvElt_iff_cycleType_eq ψ hg₀ hg

end CFSG.ASVolI.ChH
