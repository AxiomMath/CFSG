module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210jAuxK
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210jAuxR
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A G : Subgroup Γ}

theorem thm210j
    (h : SemisimpleAction p A G) {X : Subgroup Γ} (_hXG : X ≤ G)
    (hX : Admits (cenIn G A ⊔ A) X) {J : Subgroup Γ} (hJ : J ∈ lcal G)
    (hFX : ¬ CFSG.fittingSubgroupOf (smear J A) ≤ X) :
    X ⊓ cenIn G A ≤ cenIn (cenIn G A) (smear J A) ∧
      IsDirectProduct {S | ∃ K ∈ lcal G, S = smear K A ∧ S ≠ smear J A}
        (cenIn (cenIn G A) (smear J A)) := by
  exact ⟨h.inf_cenIn_le_cenIn_smear hX hJ hFX, h.isDirectProduct_cenIn_cenIn_smear hJ⟩

theorem thm210k
    (h : SemisimpleAction p A G) :
    IsGreatest {X : Subgroup Γ | X ≤ G ∧ Admits (cenIn G A ⊔ A) X ∧ X ⊓ cenIn G A = ⊥}
      ⁅CFSG.fittingSubgroupOf (mOf A G), A⁆ := by
  have hF : CFSG.fittingSubgroupOf (mOf A G) = fProd A G := by
    rw [h.mOf_eq_kProd, h.fittingSubgroupOf_kProd]
  rw [hF]
  refine ⟨⟨h.commutator_fProd_le_group, h.admits_commutator_fProd,
    h.commutator_fProd_inf_cenIn⟩, ?_⟩
  rintro Z ⟨hZG, hZ, hZD⟩
  have hnil : Group.IsNilpotent Z := by
    refine Thm210.isNilpotent_of_forall_projIn h.isDirectProduct_lcal hZG fun J hJ => ?_
    by_contra hnn
    have hFZ := thm210h h hZG hZ hJ hnn
    have hFD : CFSG.fittingSubgroupOf (smear J A) ≤ cenIn G A :=
      (Subgroup.map_subtype_le _).trans (h.smear_le_cenIn hJ)
    have hle : CFSG.fittingSubgroupOf (smear J A) ≤ Z ⊓ cenIn G A := le_inf hFZ hFD
    rw [hZD, le_bot_iff] at hle
    exact h.fittingSubgroupOf_smear_ne_bot hJ hle
  have hZF : Z ≤ fProd A G := hF ▸ thm210f h hZG hZ hnil
  have hAZ : A ≤ Subgroup.normalizer (Z : Set Γ) := fun a ha => hZ (Subgroup.mem_sup_right ha)
  have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization p
    h.prime A Z h.isPGroup hAZ (h.coprime_card_of_le hZG)
  have hCZ : Z ⊓ Subgroup.centralizer (A : Set Γ) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxZ, hxC⟩ := Subgroup.mem_inf.mp hx
    have hx' : x ∈ Z ⊓ cenIn G A := Subgroup.mem_inf.mpr ⟨hxZ, Subgroup.mem_inf.mpr ⟨hZG hxZ, hxC⟩⟩
    rw [hZD] at hx'
    exact hx'
  rw [hCZ, sup_bot_eq] at hfac
  calc Z = ⁅Z, A⁆ := hfac.symm
    _ ≤ ⁅fProd A G, A⁆ := Subgroup.commutator_mono hZF le_rfl

theorem thm210m
    (h : SemisimpleAction p A G) {X Y : Subgroup Γ} (hXG : X ≤ G) (hYG : Y ≤ G)
    (hX : Admits (cenIn G A ⊔ A) X) (hY : Admits (cenIn G A ⊔ A) Y) (hXY : IsNormalIn X Y)
    (hYs : Group.IsSolvable Y) {J : Subgroup Γ} (hJ : J ∈ lcal G)
    (hVX : ¬ CFSG.fittingSubgroupOf (smear J A) ≤ X)
    (hVY : CFSG.fittingSubgroupOf (smear J A) ≤ Y) :
    IsMulCommutative (projIn (lcal G) J (G ⊓ sectionCentralizer X Y)) := by
  have _ : _ ∧ _ ∧ _ ∧ _ := ⟨hXG, hYG, hY, hYs⟩
  have hle := h.projIn_sectionCentralizer_le hJ hX hXY.1 hVX hVY
  have hF : projIn (lcal G) J (fProd A G) ≤ CFSG.fittingSubgroupOf (kJ A J) :=
    (h.le_fProd_iff.mp le_rfl).2 J hJ
  have := h.isMulCommutative_fittingSubgroupOf_kJ hJ
  exact Thm210.isMulCommutative_of_le (hle.trans hF)

theorem thm210d
    (h : SemisimpleAction p A G) (φ : MulAut ↥G) :
    ∃ g : ↥G, ((mOf A G).subgroupOf G |>.map φ.toMonoidHom).map (MulAut.conj g).toMonoidHom =
      (mOf A G).subgroupOf G :=
  h.exists_conj_map_mOf φ

end CFSG.SignalizerFunctorTheorem.McBride.Near
