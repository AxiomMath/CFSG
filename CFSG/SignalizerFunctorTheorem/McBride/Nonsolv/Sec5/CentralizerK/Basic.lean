module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210Aux
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.L514.SmearEquiv
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.KGroup

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.CentralizerK

variable {Γ : Type*} [Group Γ]

theorem isDirectProduct_of_subset {S T : Set (Subgroup Γ)} {K : Subgroup Γ}
    (hK : IsDirectProduct S K) (hT : T ⊆ S) : IsDirectProduct T (sSup T) where
  commute J hJ L hL hne := hK.commute J (hT hJ) L (hT hL) hne
  indep := hK.indep.mono hT
  sSup_eq := rfl

theorem isSolvable_of_le {K H : Subgroup Γ} (hKH : K ≤ H) (hH : Group.IsSolvable H) :
    Group.IsSolvable K :=
  Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKH)
    (Subgroup.inclusion_injective hKH)

theorem ne_bot_of_not_isMulCommutative {F : Subgroup Γ} (hnc : ¬ IsMulCommutative F) : F ≠ ⊥ := by
  rintro rfl
  exact hnc inferInstance

theorem orbitClosure_map_conj {A J : Subgroup Γ} {a : Γ} (ha : a ∈ A) :
    orbitClosure (J.map (MulAut.conj a).toMonoidHom) A = orbitClosure J A := by
  refine le_antisymm (orbitClosure_le fun b hb => ?_) (orbitClosure_le fun b hb => ?_)
  · rw [map_conj_map_conj]
    exact map_conj_le_orbitClosure J (mul_mem hb ha)
  · have h := map_conj_le_orbitClosure (J.map (MulAut.conj a).toMonoidHom)
      (mul_mem hb (inv_mem ha))
    rwa [map_conj_map_conj, show b * a⁻¹ * a = b by group] at h

theorem smear_map_conj_of_mem {A J : Subgroup Γ} {a : Γ} (ha : a ∈ A) :
    smear (J.map (MulAut.conj a).toMonoidHom) A = smear J A := by
  unfold smear
  rw [orbitClosure_map_conj ha]

section Finite

variable [Finite Γ]

theorem isSolvable_inf_centralizer_of_isDirectProduct {S : Set (Subgroup Γ)} {L A : Subgroup Γ}
    (hL : IsDirectProduct S L)
    (hA : ∀ a ∈ A, ∀ J ∈ S, J.map (MulAut.conj a).toMonoidHom ∈ S)
    (hS : ∀ J ∈ S, Group.IsSolvable ↥(J ⊓ Subgroup.centralizer
      ((A ⊓ Subgroup.normalizer (J : Set Γ) : Subgroup Γ) : Set Γ))) :
    Group.IsSolvable ↥(L ⊓ Subgroup.centralizer (A : Set Γ)) := by
  refine Near.Thm210.isSolvable_of_forall_projIn hL inf_le_left fun J hJ => ?_
  rw [projIn_centralizer_eq hL hA hJ]
  exact hS J hJ

theorem isSolvable_inf_centralizer_iff_smear {A G J : Subgroup Γ}
    (hAG : A ≤ Subgroup.normalizer (G : Set Γ)) (hJ : J ∈ lcal G) :
    Group.IsSolvable ↥(J ⊓ Subgroup.centralizer
      ((A ⊓ Subgroup.normalizer (J : Set Γ) : Subgroup Γ) : Set Γ)) ↔
        Group.IsSolvable ↥(smear J A) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_smear hAG hJ
  constructor
  · intro h
    exact Nonsolvable.isSolvable_of_mulEquiv e.symm
  · intro h
    exact Nonsolvable.isSolvable_of_mulEquiv e

theorem isSolvable_inf_centralizer_kOf_of_sol_eq_bot {A G : Subgroup Γ}
    (hAG : A ≤ Subgroup.normalizer (G : Set Γ)) (hsol : sol G = ⊥)
    (hS : ∀ J ∈ lcal G, Group.IsSolvable ↥(smear J A)) :
    Group.IsSolvable ↥(kOf G ⊓ Subgroup.centralizer (A : Set Γ)) :=
  isSolvable_inf_centralizer_of_isDirectProduct (isDirectProduct_lcal_kOf hsol)
    (fun _ ha _ hJ => map_conj_mem_lcal hJ (hAG ha)) fun J hJ =>
      (isSolvable_inf_centralizer_iff_smear hAG hJ).mpr (hS J hJ)

end Finite

theorem smear_map_conj_le_of_mem_centralizer {A J : Subgroup Γ} {d : Γ}
    (hd : d ∈ Subgroup.centralizer (A : Set Γ)) :
    smear (J.map (MulAut.conj d).toMonoidHom) A ≤
      (smear J A).map (MulAut.conj d).toMonoidHom := by
  have hcomm : ∀ a ∈ A, a * d = d * a := fun a ha => Subgroup.mem_centralizer_iff.mp hd a ha
  have hO : orbitClosure (J.map (MulAut.conj d).toMonoidHom) A ≤
      (orbitClosure J A).map (MulAut.conj d).toMonoidHom := by
    refine orbitClosure_le fun a ha => ?_
    rw [map_conj_map_conj, hcomm a ha, ← map_conj_map_conj]
    exact Subgroup.map_mono (map_conj_le_orbitClosure J ha)
  intro x hx
  obtain ⟨hxO, hxC⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨y, hy, rfl⟩ := hO hxO
  refine ⟨y, Subgroup.mem_inf.mpr ⟨hy, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩, rfl⟩
  have h1 : a * (d * y * d⁻¹) = (d * y * d⁻¹) * a := by
    simpa [MulAut.conj_apply] using Subgroup.mem_centralizer_iff.mp hxC a ha
  have h2 : d⁻¹ * a * d = a := by
    rw [mul_assoc, hcomm a ha, inv_mul_cancel_left]
  have e1 : a * y = d⁻¹ * (a * (d * y * d⁻¹)) * d := by
    calc a * y = (d⁻¹ * a * d) * y := by rw [h2]
      _ = _ := by group
  have e2 : y * a = d⁻¹ * ((d * y * d⁻¹) * a) * d := by
    calc y * a = y * (d⁻¹ * a * d) := by rw [h2]
      _ = _ := by group
  rw [e1, e2, h1]

theorem isSolvable_smear_map_conj_of_mem_centralizer [Finite Γ] {A J : Subgroup Γ} {d : Γ}
    (hd : d ∈ Subgroup.centralizer (A : Set Γ)) (h : Group.IsSolvable ↥(smear J A)) :
    Group.IsSolvable ↥(smear (J.map (MulAut.conj d).toMonoidHom) A) :=
  isSolvable_of_le (smear_map_conj_le_of_mem_centralizer hd)
    (isSolvable_map_mulEquiv (MulAut.conj d) h)

theorem map_conj_mem_lcal_diff_lcalA [Finite Γ] {A G J : Subgroup Γ}
    (hJ : J ∈ lcal G \ lcalA G A) {g : Γ} (hgG : g ∈ Subgroup.normalizer (G : Set Γ))
    (hg : g ∈ A ∨ g ∈ Subgroup.centralizer (A : Set Γ)) :
    J.map (MulAut.conj g).toMonoidHom ∈ lcal G \ lcalA G A := by
  have hsolv : Group.IsSolvable ↥(smear J A) := by
    by_contra hns
    exact hJ.2 ⟨hJ.1, hns⟩
  refine ⟨map_conj_mem_lcal hJ.1 hgG, fun hmem => hmem.2 ?_⟩
  rcases hg with hg | hg
  · rw [smear_map_conj_of_mem hg]
    exact hsolv
  · exact isSolvable_smear_map_conj_of_mem_centralizer hg hsolv

theorem isDAInvariant_sSup_lcal_diff_lcalA [Finite Γ] {A G : Subgroup Γ}
    (hAG : A ≤ Subgroup.normalizer (G : Set Γ)) :
    IsDAInvariant A G (sSup (lcal G \ lcalA G A)) := by
  refine ⟨sSup_le fun J hJ => lcal_le hJ.1, fun d hd => ?_, fun a ha => ?_⟩
  · have hdG : d ∈ Subgroup.normalizer (G : Set Γ) :=
      Subgroup.le_normalizer (Subgroup.mem_inf.mp hd).1
    exact mem_normalizer_sSup
      (fun J hJ => map_conj_mem_lcal_diff_lcalA hJ hdG (Or.inr (Subgroup.mem_inf.mp hd).2))
      (fun J hJ => map_conj_mem_lcal_diff_lcalA hJ (inv_mem hdG)
        (Or.inr (Subgroup.mem_inf.mp (inv_mem hd)).2))
  · exact mem_normalizer_sSup
      (fun J hJ => map_conj_mem_lcal_diff_lcalA hJ (hAG ha) (Or.inl ha))
      (fun J hJ => map_conj_mem_lcal_diff_lcalA hJ (hAG (inv_mem ha)) (Or.inl (inv_mem ha)))

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.CentralizerK
