module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXY
public import CFSG.Quasithin.Background.RonanF918Five
public import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.Quasithin.H13.P31F

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.RonanF918
open CFSG.Assembly.LowTwoRank

noncomputable def quotCenterEquiv {A Ks : Type} [Group A] [Group Ks] (e : A ≃* Ks) :
    (A ⧸ Subgroup.center A) ≃* (Ks ⧸ Subgroup.center Ks) :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

theorem lieModel_quot_of_equiv {A Ks : Type} [Group A] [Group Ks] (e : A ≃* Ks)
    {t : StatedLieTag} {n p f : ℕ} (h : LieModel (Ks ⧸ Subgroup.center Ks) t n p f) :
    LieModel (A ⧸ Subgroup.center A) t n p f :=
  LieModel.of_mulEquiv (quotCenterEquiv e).symm h

theorem one_le_of_classical {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (h : StatedClassicalModel X t n p f) : 1 ≤ f := h.1.2.1

theorem one_le_of_suzuki {X : Type} [Group X] {p f : ℕ} (h : SuzukiModel X p f) : 1 ≤ f := by
  obtain ⟨-, a, ha, -, -, -, hf, -⟩ := h
  omega

section Four

variable {A Ks : Type} [Group A] [Group Ks]

theorem fourList_target (e : A ≃* Ks) (hq : CFSG.IsQuasisimple A) (hl : IsF918FourListU Ks) :
    (∃ m : ℕ, 1 ≤ m ∧ lieFam1_w31 m (A ⧸ Subgroup.center A)) ∨
      IsPSL 4 2 1 (A ⧸ Subgroup.center A) ∨ IsPSL 5 2 1 (A ⧸ Subgroup.center A) ∨
      IsAlt 7 (A ⧸ Subgroup.center A) ∨ IsSporadic .M22 A ∨
      IsHat A (CFSG.Blueprint.NativeSporadic.Carrier .M22) := by
  rcases hl with (⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩) | ⟨n, h⟩ | h6 | ⟨n, hn, h⟩ | h33 | ⟨n, hn, h⟩ | h42 |
      h52 | ⟨h7, -⟩ | h22 | ⟨-, hZ, ⟨e'⟩⟩
  ·
    have h' : StatedClassicalModel (A ⧸ Subgroup.center A) .PSL 2 2 n :=
      (LieModel.classical_iff (by decide)).1 (lieModel_quot_of_equiv e h)
    exact Or.inl ⟨n, one_le_of_classical h', Or.inl h'⟩
  ·
    have h' : StatedClassicalModel (A ⧸ Subgroup.center A) .PSU 3 2 n :=
      (LieModel.classical_iff (by decide)).1 (lieModel_quot_of_equiv e h)
    exact Or.inl ⟨n, one_le_of_classical h', Or.inr (Or.inr (Or.inl h'))⟩
  ·
    have h' : SuzukiModel (A ⧸ Subgroup.center A) 2 n :=
      (LieModel.twistedB2_iff.1 (lieModel_quot_of_equiv e h)).2
    exact Or.inl ⟨n, one_le_of_suzuki h', Or.inr (Or.inl h')⟩
  ·
    have h' : StatedClassicalModel (A ⧸ Subgroup.center A) .PSL 3 2 n :=
      (LieModel.classical_iff (by decide)).1 (lieModel_quot_of_equiv e h)
    exact Or.inl ⟨n, one_le_of_classical h', Or.inr (Or.inr (Or.inr (Or.inl h')))⟩
  ·
    exact Or.inl ⟨1, le_rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨rfl, ⟨(quotCenterEquiv e).trans h6.some⟩⟩)))))⟩
  ·
    have h' : StatedClassicalModel (A ⧸ Subgroup.center A) .PSp 2 2 n :=
      (LieModel.classical_iff (by decide)).1 (lieModel_quot_of_equiv e h)
    exact Or.inl ⟨n, one_le_of_classical h', Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))⟩
  ·
    have h' : StatedClassicalModel (A ⧸ Subgroup.center A) .PSU 3 3 1 :=
      (LieModel.classical_iff (by decide)).1 (lieModel_quot_of_equiv e h33)
    exact Or.inl ⟨1, le_rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨rfl, h'⟩))))))⟩
  ·
    have h' : ChevalleyExceptionalModel (A ⧸ Subgroup.center A) .G2 2 n :=
      ((LieModel.chevalleyExceptional_iff (by decide)).1 (lieModel_quot_of_equiv e h)).2
    exact Or.inl ⟨n, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))))⟩
  ·
    exact Or.inr (Or.inl ((LieModel.classical_iff (by decide)).1 (lieModel_quot_of_equiv e h42)))
  ·
    exact Or.inr (Or.inr (Or.inl
      ((LieModel.classical_iff (by decide)).1 (lieModel_quot_of_equiv e h52))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨(quotCenterEquiv e).trans h7.some⟩)))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans h22.some⟩))))
  ·
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hq, ?_, ⟨(quotCenterEquiv e).trans e'⟩⟩))))
    have h3 := Subgroup.card_map_of_injective (K := Subgroup.center A) (f := (e : A →* Ks))
      e.injective
    rw [Subgroup.map_center_eq e] at h3
    exact h3.symm.trans hZ

end Four

section Five

variable {A Ks : Type} [Group A] [Group Ks]

theorem fiveList_center_eq_bot (e : A ≃* Ks) (hq : CFSG.IsQuasisimple A)
    (hl : IsF918FiveListU Ks) : Subgroup.center A = ⊥ := by
  have hs : IsSimpleGroup Ks := by
    rcases hl with ⟨n, h⟩ | ⟨n, h⟩ | ⟨e'⟩ | h
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity Ks 2 2 n
        ((LieModel.classical_iff (by decide)).1 h)).2
    · exact (CFSG.LieType.Simplicity.fam_2b2_simplicity Ks 2 n
        (LieModel.twistedB2_iff.1 h).2).2
    · obtain ⟨e''⟩ := e'
      haveI : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
      exact e''.isSimpleGroup
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity Ks 3 2 1
        ((LieModel.classical_iff (by decide)).1 h)).2
  haveI : IsSimpleGroup A := e.isSimpleGroup
  obtain ⟨a, b, hab⟩ := hq.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  have hnab : ∃ x y : A, x * y ≠ y * x := ⟨a', b', fun h => hab (by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).2

theorem fiveList_target (e : A ≃* Ks) (hq : CFSG.IsQuasisimple A) (hl : IsF918FiveListU Ks) :
    ∃ m : ℕ, 1 ≤ m ∧ (IsPSL 2 2 m (A ⧸ Subgroup.center A) ∨ IsSz m (A ⧸ Subgroup.center A) ∨
      IsAlt 5 (A ⧸ Subgroup.center A) ∨ IsPSL 3 2 1 (A ⧸ Subgroup.center A)) := by
  have hZ := fiveList_center_eq_bot e hq hl
  let e2 : (A ⧸ Subgroup.center A) ≃* Ks :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e
  rcases hl with ⟨n, h⟩ | ⟨n, h⟩ | ⟨e'⟩ | h
  · have h' : StatedClassicalModel (A ⧸ Subgroup.center A) .PSL 2 2 n :=
      (LieModel.classical_iff (by decide)).1 (LieModel.of_mulEquiv e2.symm h)
    exact ⟨n, one_le_of_classical h', Or.inl h'⟩
  · have h' : SuzukiModel (A ⧸ Subgroup.center A) 2 n :=
      (LieModel.twistedB2_iff.1 (LieModel.of_mulEquiv e2.symm h)).2
    exact ⟨n, one_le_of_suzuki h', Or.inr (Or.inl h')⟩
  · obtain ⟨e''⟩ := e'
    exact ⟨1, le_rfl, Or.inr (Or.inr (Or.inl ⟨e2.trans e''⟩))⟩
  · have h' : StatedClassicalModel (A ⧸ Subgroup.center A) .PSL 3 2 1 :=
      (LieModel.classical_iff (by decide)).1 (LieModel.of_mulEquiv e2.symm h)
    exact ⟨1, le_rfl, Or.inr (Or.inr (Or.inr h'))⟩

end Five

end CFSG.Quasithin.H13.P31F
