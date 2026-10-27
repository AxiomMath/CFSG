module

public import CFSG.Quasithin.EmptyFaithful.S146zUBSetup

public section

namespace CFSG.Quasithin.S146zU

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

namespace UB

section Module

variable {W : Type} [CommGroup W]

@[expose] def ModSplit (Mp L : Subgroup (MulAut W)) (t : MulAut W) : Prop :=
  IsSumMod (fixV Mp) (commV L) ((commV L).map t.toMonoidHom) ⊤ ∧ commV L ≤ fixV (conjAutSub t L)

@[expose] def FiveCases (Mp L : Subgroup (MulAut W)) (V : Subgroup W) (t : MulAut W) : Prop :=
  (V = ⊤ ∧ ∃ n, IsPSL 2 2 n ↥(autSub L V) ∧ Omega4PlusModule (autSub Mp V) n) ∨
    ModSplit Mp L t ∨ ModSplit Mp (conjAutSub t L) t⁻¹

end Module

section Reduce

variable {W : Type} [CommGroup W] [Finite W]

theorem modSplit_of_modFiveIii {Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
    (e : Nonempty (↥L ≃* SBc16.L216)) (h : ModFiveIii Mp T L V t) :
    ModSplit Mp L t ∧ ((ModFiveA Mp L V ∧ FiveShape ↥L) ∨ D321Three Mp L) := by
  refine ⟨⟨h.1, h.2.1⟩, ?_⟩
  rcases h.2.2 with ha | hb | hc | hd
  · exact Or.inl ha
  · exact (not_isPSL_three_two_of_L216 e hb.1).elim
  · exact (not_isPSL_three_two_of_L216 e hc.1).elim
  · exact Or.inr hd

theorem fiveCases_of_modFive {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
    (e : Nonempty (↥L ≃* SBc16.L216)) (h : ModFive M Mp T L V t) : FiveCases Mp L V t := by
  rcases h with ⟨hV, -, n, hn, hΩ⟩ | ⟨hV, -, hpsl, -⟩ | h | h
  · exact Or.inl ⟨hV, n, hn, hΩ⟩
  · exact (not_isPSL_three_two_of_L216 e (isPSL_of_autSub_top hV hpsl)).elim
  · exact Or.inr (Or.inl (modSplit_of_modFiveIii e h).1)
  · obtain ⟨e'⟩ := e
    exact Or.inr (Or.inr (modSplit_of_modFiveIii ⟨(Subgroup.equivMapOfInjective L
      (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).symm.trans e'⟩ h).1)

end Reduce

section Concrete

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

@[expose] noncomputable def F5Cases (h : HypF918 T V L V₁ Vp H K) {I : Subgroup G}
    (hIU : I ≤ conjClosure Vp H) {t : G} (ht : t ∈ T) : Prop :=
  haveI := factElem h hIU
  FiveCases (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)
    (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t, h.T_le_H ht⟩)

end Concrete

end UB

section Headline

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G]

theorem five_reduce {T V L V₁ Vp H K : Subgroup G} (h : HypF918 T V L V₁ Vp H K) {I : Subgroup G}
    (hIU : I ≤ conjClosure Vp H) (W : Subgroup ↥(tildeOf V₁ (conjClosure Vp H)))
    (hW : ∀ t ∈ autIH V₁ Vp H T, ∀ w ∈ W, t w ∈ W) (hirr : IsIrrPlusTildeU h I W) {s : G}
    (hsT : s ∈ T) (e : Nonempty (OTwoQuot K ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)))
    (hFive : F918Five h hIU hsT) : UB.F5Cases h hIU hsT := by
  have hL := UB.nonempty_autIH_equiv_L216 h hIU (UB.autIH_ne_bot_of_irrPlusU h hIU W hW hirr) e
  have := factElem h hIU
  exact UB.fiveCases_of_modFive hL hFive

theorem exists_f5 {T M : Subgroup G}
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hD36 : D36) (hD37 : D37) (hD321 : D321) (hI5 : Insp5a)
    (S : Setting146 G T M) {K₁ : Subgroup G} {s : G} (hK₁ : K₁ ∈ cComp (mcOf T)) (hsT : s ∈ T)
    (hsN : s ∉ Subgroup.normalizer (K₁ : Set G)) (hK₀ : conjClosure K₁ T ⊔ T = mcOf T)
    (e : Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4))) :
    ∃ (hF : HypF918 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) (mcOf T) K₁)
      (I : Subgroup G) (_ : quasithinOmegaOneCenter T ≤ I)
      (hIU : I ≤ conjClosure (VZ T M) (mcOf T))
      (W : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (conjClosure (VZ T M) (mcOf T)))),
      (∀ t ∈ autIH (quasithinOmegaOneCenter T) (VZ T M) (mcOf T) T, ∀ w ∈ W, t w ∈ W) ∧
        IsIrrPlusTildeU hF I W ∧ F918Five hF hIU hsT := by
  have hF := UB.hypF918_mcOf hA37 hA38 S hK₁ (UB.isSimpleGroup_kbar_of_equiv_L216 e) hK₀
  obtain ⟨I, hV₁I, hIU, W, hW, hirr⟩ := exists_isIrrPlusTildeU hF
  have hH : SQTKGroup ↥(mcOf T) := S.sqtkGroup_of_isHTM S.isHTM_mcOf
  obtain ⟨-, h5⟩ := F918_5' hF hH (UB.conjClosure_ne_self hsT hsN) hV₁I hIU W hW hirr hD36 hD37
    hD321 hI5 hA37 hA38
  exact ⟨hF, I, hV₁I, hIU, W, hW, hirr, h5 s hsT hsN⟩

end Headline

namespace UB

variable {G : Type} [Group G] [Finite G]

theorem exists_f5_cases {T M : Subgroup G}
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hD36 : D36) (hD37 : D37) (hD321 : D321) (hI5 : Insp5a)
    (S : Setting146 G T M) {K₁ : Subgroup G} {s : G} (hK₁ : K₁ ∈ cComp (mcOf T)) (hsT : s ∈ T)
    (hsN : s ∉ Subgroup.normalizer (K₁ : Set G)) (hK₀ : conjClosure K₁ T ⊔ T = mcOf T)
    (e : Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4))) :
    ∃ (hF : HypF918 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) (mcOf T) K₁)
      (I : Subgroup G) (_ : quasithinOmegaOneCenter T ≤ I)
      (hIU : I ≤ conjClosure (VZ T M) (mcOf T))
      (W : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (conjClosure (VZ T M) (mcOf T)))),
      (∀ t ∈ autIH (quasithinOmegaOneCenter T) (VZ T M) (mcOf T) T, ∀ w ∈ W, t w ∈ W) ∧
        IsIrrPlusTildeU hF I W ∧ F5Cases hF hIU hsT := by
  obtain ⟨hF, I, hV₁I, hIU, W, hW, hirr, h5⟩ :=
    exists_f5 hA37 hA38 hD36 hD37 hD321 hI5 S hK₁ hsT hsN hK₀ e
  exact ⟨hF, I, hV₁I, hIU, W, hW, hirr, five_reduce hF hIU W hW hirr hsT e h5⟩

end UB

end CFSG.Quasithin.S146zU
