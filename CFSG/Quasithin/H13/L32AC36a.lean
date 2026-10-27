module

public import CFSG.Quasithin.H13.L32AC47c
public import CFSG.Quasithin.Background.FourListSporadic

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem fourListFine_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : FourListFine Y) : FourListFine X := by
  let ec : (X ⧸ Subgroup.center X) ≃* (Y ⧸ Subgroup.center Y) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  refine ⟨fourList_congr ec.symm h.1, fun h7 hhat =>
    h.2.1 (IsAlt.of_mulEquiv ec h7) (IsHat.of_mulEquiv e hhat), fun hM => ?_⟩
  rcases h.2.2 (IsSporadic.of_mulEquiv ec hM) with h1 | h1
  · exact Or.inl (IsSporadic.of_mulEquiv e.symm h1)
  · exact Or.inr (IsHat.of_mulEquiv e.symm h1)

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem m22_or_hat_of_sporadic (h30 : Lemma14_7_30) (h32 : Lemma14_7_32) (hD310 : D310)
    (hD391 : D391) (hI4 : Insp4) (hFine : F918Fine4) (hdisj : SporadicFourListDisjoint)
    (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H) {s : TauCeti.SporadicName}
    (hs : IsSporadic s (cStar K ⧸ Subgroup.center (cStar K))) :
    IsSporadic .M22 (cStar K) ∨ IsHat (cStar K) (CFSG.Blueprint.NativeSporadic.Carrier .M22) := by
  obtain ⟨-, hTK, S₀, hF⟩ := reduce_KL1T h30 h32 S hK
  have hSQ := sqtkGroup_of_setting S₀
  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU hF
  have h4 := (F918_4_fine' hF hSQ (conjClosure_T_eq_self hTK) hV₁I hIU W hW hirrU
    hD310 hD391 hI4 hFine).1
  obtain ⟨eA⟩ := L1295B.nonempty_mulEquiv_autIH hF
  have hfine := fourListFine_of_mulEquiv ((cStarEquiv K).trans eA) h4
  exact hfine.2.2 (hdisj _ s hs hfine.1)

end CFSG.Quasithin.H13.L32A.C
