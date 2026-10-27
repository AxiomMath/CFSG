module

public import CFSG.Timmesfeld.Transvection.LineGroup
public import CFSG.Timmesfeld.Transvection.FrameBasic

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)} {r : ℕ} {P Q : Fin r → Subgroup G}

@[expose] def framePt (P Q : Fin r → Subgroup G) : Fin r ⊕ Fin r → Subgroup G := Sum.elim P Q

@[simp] theorem framePt_inl (i : Fin r) : framePt P Q (Sum.inl i) = P i := rfl

@[simp] theorem framePt_inr (i : Fin r) : framePt P Q (Sum.inr i) = Q i := rfl

theorem shortRootGroup_le_lineGroup (P Q P' Q' : Subgroup G) :
    shortRootGroup Δ P Q P' Q' ≤ lineGroup Δ P P' :=
  inf_le_left.trans inf_le_left

private theorem ne_of_elim_ne {a : Fin r ⊕ Fin r} {i : Fin r} (h : Sum.elim id id a ≠ i) :
    a ≠ Sum.inl i ∧ a ≠ Sum.inr i := by
  constructor <;> rintro rfl <;> exact h rfl

namespace IsFrame

variable (hF : IsFrame Δ P Q) (hΔ : IsRootClass Δ)
include hF

theorem framePt_mem (a : Fin r ⊕ Fin r) : framePt P Q a ∈ Δ := by
  rcases a with i | i
  · exact hF.memP i
  · exact hF.memQ i

include hΔ

theorem commuting_framePt {a c : Fin r ⊕ Fin r} (hca : c ≠ Sum.swap a) :
    Commuting (framePt P Q a) (framePt P Q c) := by
  rcases a with i | i <;> rcases c with j | j
  · by_cases hij : i = j
    · subst hij
      exact hΔ.commuting_self (hF.memP i)
    · exact hF.commuting_PP hij
  · exact hF.commuting_PQ fun h => hca (by simp [h])
  · exact hF.commuting_QP fun h => hca (by simp [h])
  · by_cases hij : i = j
    · subst hij
      exact hΔ.commuting_self (hF.memQ i)
    · exact hF.commuting_QQ hij

theorem commuting_framePt_lineGroup {a c d : Fin r ⊕ Fin r} (hca : c ≠ Sum.swap a)
    (hda : d ≠ Sum.swap a) :
    Commuting (framePt P Q a) (lineGroup Δ (framePt P Q c) (framePt P Q d)) :=
  commuting_iff_le_centralizer.2 (iSup₂_le fun _ hC => commuting_iff_le_centralizer.1
    (hC.2 _ (hF.framePt_mem a) (hF.commuting_framePt hΔ hca) (hF.commuting_framePt hΔ hda)))

theorem commuting_lineGroup_lineGroup {a b c d : Fin r ⊕ Fin r} (hca : c ≠ Sum.swap a)
    (hcb : c ≠ Sum.swap b) (hda : d ≠ Sum.swap a) (hdb : d ≠ Sum.swap b) :
    Commuting (lineGroup Δ (framePt P Q a) (framePt P Q b))
      (lineGroup Δ (framePt P Q c) (framePt P Q d)) :=
  commuting_lineGroup (hF.framePt_mem c) (hF.framePt_mem d) (hF.commuting_framePt hΔ hca)
    (hF.commuting_framePt hΔ hda) (hF.commuting_framePt hΔ hcb) (hF.commuting_framePt hΔ hdb)

theorem commuting_framePt_shortRootGroup {a c d : Fin r ⊕ Fin r} (hca : c ≠ Sum.swap a)
    (hda : d ≠ Sum.swap a) :
    Commuting (framePt P Q a) (shortRootGroup Δ (framePt P Q c) (framePt P Q (Sum.swap c))
      (framePt P Q d) (framePt P Q (Sum.swap d))) :=
  (hF.commuting_framePt_lineGroup hΔ hca hda).mono le_rfl (shortRootGroup_le_lineGroup _ _ _ _)

theorem commuting_shortRootGroup {a b c d : Fin r ⊕ Fin r} (hca : c ≠ Sum.swap a)
    (hcb : c ≠ Sum.swap b) (hda : d ≠ Sum.swap a) (hdb : d ≠ Sum.swap b) :
    Commuting (shortRootGroup Δ (framePt P Q a) (framePt P Q (Sum.swap a)) (framePt P Q b)
        (framePt P Q (Sum.swap b)))
      (shortRootGroup Δ (framePt P Q c) (framePt P Q (Sum.swap c)) (framePt P Q d)
        (framePt P Q (Sum.swap d))) :=
  (hF.commuting_lineGroup_lineGroup hΔ hca hcb hda hdb).mono
    (shortRootGroup_le_lineGroup _ _ _ _) (shortRootGroup_le_lineGroup _ _ _ _)

theorem commuting_sup_lineGroup {i : Fin r} {a b : Fin r ⊕ Fin r} (ha : Sum.elim id id a ≠ i)
    (hb : Sum.elim id id b ≠ i) :
    Commuting (P i ⊔ Q i) (lineGroup Δ (framePt P Q a) (framePt P Q b)) := by
  obtain ⟨ha1, ha2⟩ := ne_of_elim_ne ha
  obtain ⟨hb1, hb2⟩ := ne_of_elim_ne hb
  exact Commuting.sup_left (hF.commuting_framePt_lineGroup hΔ (a := Sum.inl i) ha2 hb2)
    (hF.commuting_framePt_lineGroup hΔ (a := Sum.inr i) ha1 hb1)

theorem commuting_sup_shortRootGroup {i : Fin r} {a b : Fin r ⊕ Fin r}
    (ha : Sum.elim id id a ≠ i) (hb : Sum.elim id id b ≠ i) :
    Commuting (P i ⊔ Q i) (shortRootGroup Δ (framePt P Q a) (framePt P Q (Sum.swap a))
      (framePt P Q b) (framePt P Q (Sum.swap b))) :=
  (hF.commuting_sup_lineGroup hΔ ha hb).mono le_rfl (shortRootGroup_le_lineGroup _ _ _ _)

theorem commuting_sup_framePt {i : Fin r} {a : Fin r ⊕ Fin r} (ha : Sum.elim id id a ≠ i) :
    Commuting (P i ⊔ Q i) (framePt P Q a) := by
  obtain ⟨ha1, ha2⟩ := ne_of_elim_ne ha
  exact Commuting.sup_left (hF.commuting_framePt hΔ (a := Sum.inl i) ha2)
    (hF.commuting_framePt hΔ (a := Sum.inr i) ha1)

end IsFrame

end CFSG.Timmesfeld.Transvection
