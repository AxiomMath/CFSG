module

public import CFSG.Quasithin.Vol2.Ch11SecOE8D

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.L3

open Matrix CFSG.CGT.Timmesfeld75 CFSG.LinearGroups CFSG.Quasithin
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem inf_solvRad_le (hF4 : 4 ≤ Nat.card F) {R : Subgroup (ProjectiveSpecialLinearGroup
    (Fin 3) F)} (hR : projectiveElationSubgroup (pt F 0) ⊔ projectiveElationSubgroup (pt F 1) ≤ R) :
    projectiveElationSubgroup (pt F 0) ⊓ solvRad R ≤
      (kerU F).map ((piP F).comp (elationSubgroup (pt F 0)).subtype) := by
  set S := supU F with hSdef
  set N : Subgroup SL(3, F) := (solvRad R).comap (piP F) ⊓ S with hNdef
  have hSR : S.map (piP F) ≤ R := (map_supU (F := F)).le.trans hR
  have hNS : N ≤ S := inf_le_right
  have hSN : S ≤ Subgroup.normalizer (N : Set SL(3, F)) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    have hsR : piP F s ∈ R := hSR ⟨s, hs, rfl⟩
    have hsN : piP F s ∈ Subgroup.normalizer (R : Set _) := Subgroup.le_normalizer hsR
    have hsi : (piP F s)⁻¹ ∈ Subgroup.normalizer (R : Set _) := inv_mem hsN
    intro y
    constructor
    · rintro ⟨hy1, hy2⟩
      refine ⟨?_, S.mul_mem (S.mul_mem hs hy2) (S.inv_mem hs)⟩
      show piP F (s * y * s⁻¹) ∈ solvRad R
      rw [map_mul, map_mul, map_inv]
      exact conj_mem_solvRad hsN hy1
    · rintro ⟨hy1, hy2⟩
      refine ⟨?_, ?_⟩
      · have h1 : piP F (s * y * s⁻¹) ∈ solvRad R := hy1
        rw [map_mul, map_mul, map_inv] at h1
        have h2 := conj_mem_solvRad hsi h1
        simpa [mul_assoc] using h2
      · have h1 := S.mul_mem (S.mul_mem (S.inv_mem hs) hy2) hs
        simpa [mul_assoc] using h1
  have hNs : Group.IsSolvable ↥N := by
    have hRs : Group.IsSolvable ↥(solvRad R) := solvRad_isSolvable R
    set g : ↥N →* ↥(solvRad R) :=
      ((piP F).comp N.subtype).codRestrict _ fun x => x.2.1 with hg
    have hker : Group.IsSolvable ↥g.ker := by
      refine Group.isSolvable_of_comm fun a b => Subtype.ext (Subtype.ext ?_)
      have ha : ((a : ↥N) : SL(3, F)) ∈ Subgroup.center SL(3, F) := by
        have h : piP F ((a : ↥N) : SL(3, F)) = 1 :=
          congrArg Subtype.val (MonoidHom.mem_ker.mp a.2)
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
      exact (Subgroup.mem_center_iff.mp ha _).symm
    exact Group.isSolvable_of_ker_le_range g.ker.subtype g (by rw [Subgroup.range_subtype])
  rintro x ⟨⟨A, hA, rfl⟩, hx⟩
  have hAN : A ∈ N := ⟨hx, le_sup_left (a := elationSubgroup (pt F 0)) hA⟩
  have h01 := entry_eq_zero_of_solvable hF4 hNS hSN hNs hAN hA
  refine ⟨⟨A, hA⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply]
  rw [show (Subgroup.inclusion elation_zero_le_stabM ⟨A, hA⟩ : ↥(stabM (F := F))) =
    ⟨A, elation_zero_le_stabM hA⟩ from rfl, rho_elation_zero hA, h01]
  exact utriElt_zero

theorem card_le_relIndex_solvRad (hF4 : 4 ≤ Nat.card F) {R : Subgroup
    (ProjectiveSpecialLinearGroup (Fin 3) F)}
    (hR : projectiveElationSubgroup (pt F 0) ⊔ projectiveElationSubgroup (pt F 1) ≤ R) :
    Nat.card F ≤ (projectiveElationSubgroup (pt F 0) ⊓ solvRad R).relIndex
      (projectiveElationSubgroup (pt F 0)) := by
  set ψ := (piP F).comp (elationSubgroup (pt F 0)).subtype with hψ
  have hV : projectiveElationSubgroup (pt F 0) =
      (⊤ : Subgroup ↥(elationSubgroup (pt F 0))).map ψ := by
    rw [← MonoidHom.range_eq_map, hψ, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hle := inf_solvRad_le hF4 hR
  have hne : (projectiveElationSubgroup (pt F 0) ⊓ solvRad R).relIndex
      (projectiveElationSubgroup (pt F 0)) ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 := Subgroup.relIndex_le_of_le_left (L := projectiveElationSubgroup (pt F 0)) hle hne
  have h2 : ((kerU F).map ψ).relIndex (projectiveElationSubgroup (pt F 0)) = Nat.card F := by
    rw [hV, Subgroup.relIndex_map_map_of_injective _ _ piP_injective_elation_zero,
      Subgroup.relIndex_top_right, index_kerU]
  rw [h2] at h1
  exact h1

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.L3
