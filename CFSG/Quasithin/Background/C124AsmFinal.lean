module

public import CFSG.Quasithin.Background.C124AsmBuild
public import CFSG.Quasithin.Background.C124AsmClassify
public import CFSG.Quasithin.Background.C124AsmConclude
public import CFSG.Quasithin.Background.C124AsmLiftL2
public import CFSG.Quasithin.Background.C124AsmStmt
public import CFSG.Quasithin.Background.C124Interface

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

@[expose] def LiftZ3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T V L R : Subgroup G) (m : ℕ) (hV : IsElemAbelian 2 V)
    (Ys : Subgroup (MulAut (IntMod V hV))), EntryPlus X T V L R m hV →
      (m = 5 ∨ m = 6 ∨ m = 7) → Nonempty (↥(autI hV L) ≃* ↥(alternatingGroup (Fin m))) →
        StarZ3 X V L R hV Ys → ∃ Y : Subgroup G, YData X V L R hV Y

theorem altEquiv_of_realizes {G : Type} [Group G] [Finite G] {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} {n : ℕ}
    (hc : ∃ π : ↥(alternatingGroup (Fin n)) →* ↥(autI hV L),
      (FFModel.altDn n).RealizesVia (autI hV L) (commV (autI hV L))
        (fixV (autI hV L) ⊓ commV (autI hV L)) π ∧ Function.Injective π) :
    Nonempty (↥(autI hV L) ≃* ↥(alternatingGroup (Fin n))) := by
  obtain ⟨π, hπ, hinj⟩ := hc
  exact ⟨(MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm⟩

theorem c124StatementSQTK_of_specs (hGN : TheoremC118) (hE23 : E2.E23Statement)
    (hI : B5.B51IrrInputs) (hA21 : AsA21SQTKSection) (hA36 : AsA36NoOddCover)
    (hLiftZ3 : LiftZ3) (h4bL2 : Spec4bL2) (h4bAlt5 : Spec4bAlt5)
    (h4bAlt6b : Spec4bAlt6b) (h4bAlt6c : Spec4bAlt6c) (h4bAlt7 : Spec4bAlt7)
    (h4bHat6 : Spec4bHat6) (h4bA7Four : Spec4bA7Four) (h4cL2 : Spec4cL2) (h4cAlt5 : Spec4cAlt5)
    (h4cAlt6 : Spec4cAlt6) (h4cAlt7 : Spec4cAlt7) (h4cHat6 : Spec4cHat6)
    (h4cA7Four : Spec4cA7Four) (G : Type) [Group G] [Finite G] :
    C124StatementSQTK (G := G) := by
  have h4a := spec4a_holds
  intro X T V L R m hC hSQ hred hT hprod hcomp hCL hVL halt hQR hRT hm
  obtain ⟨C₁, C₂, hGNC⟩ := exists_isGNChoice (G := G) hGN
  rcases entryPlus_or_concl1 hI hA21 hA36 hC hSQ hred hT hprod hcomp hCL hVL halt hQR hRT hm with
    h1 | E
  · exact Or.inl h1
  have hV : IsElemAbelian 2 V := hred.2.2.1
  have hE : Entry X T V L R m hV := E.toEntry
  have hblk2 : ∀ hB : BlockData V L, IsBlock2 X L := fun hB =>
    isBlock2_of_short_of_mem_cComp hcomp hB.short
  rcases h4a G X T V L R m hV hE with hc | hc | hc | hc | hc | hc
  ·
    obtain ⟨Ys, hY⟩ := h4bL2 G X T V L R m hV hE hc
    obtain ⟨Y, hYD⟩ := E.exists_yData_of_starL2 hY
    exact conclude_of_Y hGNC hE23 E hYD fun hB =>
      Or.inl ⟨hblk2 hB, Or.inl ⟨2, by norm_num, h4cL2 G X T V L R m hV hE hc hB⟩⟩
  ·
    obtain ⟨Ys, hY⟩ := h4bAlt5 G X T V L R m hV hE hc
    have hequiv : Nonempty (↥(autI hV L) ≃* ↥(alternatingGroup (Fin m))) := by
      obtain ⟨hm5, hπ⟩ := hc
      subst hm5
      exact altEquiv_of_realizes hπ
    obtain ⟨Y, hYD⟩ := hLiftZ3 G X T V L R m hV Ys E (Or.inl hc.1) hequiv hY
    exact conclude_of_Y hGNC hE23 E hYD fun hB =>
      Or.inl ⟨hblk2 hB, Or.inr ⟨5, ⟨2, rfl⟩, by norm_num, h4cAlt5 G X T V L R m hV hE hc hB⟩⟩
  ·
    have hm6 := hc.1
    have hπ := hc.2
    rcases hm with h5 | h7 | ⟨-, hb⟩ | ⟨-, hc'⟩
    · omega
    · omega
    · obtain ⟨Ys, hY⟩ := h4bAlt6b G X T V L R m hV hE hc hb
      obtain ⟨Y, hYD⟩ := E.exists_yData_of_starL2 hY
      exact conclude_of_Y hGNC hE23 E hYD fun hB =>
        Or.inr ⟨hblk2 hB, Or.inr (Or.inl (h4cAlt6 G X T V L R m hV hE hc hB))⟩
    · obtain ⟨Ys, hY⟩ := h4bAlt6c G X T V L R m hV hE hc hc'
      have hequiv : Nonempty (↥(autI hV L) ≃* ↥(alternatingGroup (Fin m))) := by
        subst hm6
        exact altEquiv_of_realizes hπ
      obtain ⟨Y, hYD⟩ := hLiftZ3 G X T V L R m hV Ys E (Or.inr (Or.inl hm6)) hequiv hY
      exact conclude_of_Y hGNC hE23 E hYD fun hB =>
        Or.inr ⟨hblk2 hB, Or.inr (Or.inl (h4cAlt6 G X T V L R m hV hE hc hB))⟩
  ·
    obtain ⟨Ys, hY⟩ := h4bAlt7 G X T V L R m hV hE hc
    have hequiv : Nonempty (↥(autI hV L) ≃* ↥(alternatingGroup (Fin m))) := by
      obtain ⟨hm7, hπ⟩ := hc
      subst hm7
      exact altEquiv_of_realizes hπ
    obtain ⟨Y, hYD⟩ := hLiftZ3 G X T V L R m hV Ys E (Or.inr (Or.inr hc.1)) hequiv hY
    exact conclude_of_Y hGNC hE23 E hYD fun hB =>
      Or.inl ⟨hblk2 hB, Or.inr ⟨7, ⟨3, rfl⟩, by norm_num, h4cAlt7 G X T V L R m hV hE hc hB⟩⟩
  ·
    obtain ⟨Ys, hY⟩ := h4bHat6 G X T V L R m hV hE hc
    obtain ⟨Y, hYD⟩ := E.exists_yData_of_starL2 hY
    exact conclude_of_Y hGNC hE23 E hYD fun hB =>
      Or.inr ⟨hblk2 hB, Or.inr (Or.inr (h4cHat6 G X T V L R m hV hE hc hB))⟩
  ·
    obtain ⟨Ys, hY⟩ := h4bA7Four G X T V L R m hV hE hc
    obtain ⟨Y, hYD⟩ := E.exists_yData_of_starL2 hY
    exact conclude_of_Y hGNC hE23 E hYD fun hB =>
      Or.inr ⟨hblk2 hB, Or.inl (h4cA7Four G X T V L R m hV hE hc hB)⟩

end CFSG.Quasithin.C124
