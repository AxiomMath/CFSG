module

public import CFSG.Milestones.ASVolI.F45.Two
public import CFSG.Milestones.ASVolI.F45.Simple
public import CFSG.Milestones.ASVolI.F45.Classical
public import CFSG.Milestones.ASVolI.F45.L3Six
public import CFSG.Milestones.ASVolI.F45.Tits
public import CFSG.Milestones.ASVolI.F45.F46Tits
public import CFSG.Milestones.ASVolI.F45.F46G2d
import all CFSG.Milestones.ASVolI.F4Reductions
public import CFSG.Milestones.ASVolI.F45.Geom

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

section LieFacts

theorem burnsideF45_lieFactsAll : burnsideF45_LieFactsAll :=
  burnsideF45_lieFactsAll_of_classical
    (fun _ _ _ _ _ _ _ hyp hp => burnsideF45_facts45L_L3 hyp hp _)
    (fun _ _ _ _ _ _ _ hyp hp => burnsideF45_facts45L_Sp4 hyp hp _)
    (fun _ _ _ _ _ _ _ hyp hp => burnsideF45_facts45L_U4 hyp hp _)
    (fun _ _ _ _ _ _ _ hyp hp => burnsideF45_facts45L_U5 hyp hp _)

end LieFacts

@[expose] def burnsideF45_C6Kind (κ : GLKind) : Prop :=
  ∀ (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E), HypF_4_4 κ p f Gp M₁ M₂ → Gp = ⊤ →
    ∀ u v : (incl M₁ M₂).Γ, (incl M₁ M₂).graph.Adj u v → burnsideF45_C6Body p Gp M₁ M₂ u v

section C6

theorem burnsideF45_C6_lie (hL3 : burnsideF45_C6Kind .L3) {κ : GLKind} {p f : ℕ} {E : Type}
    [Group E] {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hκ : κ.IsLie)
    (hGp : Gp = ⊤) :
    ∀ u v : (incl M₁ M₂).Γ, (incl M₁ M₂).graph.Adj u v → burnsideF45_C6Body p Gp M₁ M₂ u v := by
  cases κ
  · exact hL3 p f E Gp M₁ M₂ hyp hGp
  · exact burnsideF45_C6_classical hyp (Or.inl rfl) hGp
  · exact burnsideF45_C6_exc hyp (Or.inl rfl) hGp
  · exact burnsideF45_C6_exc hyp (Or.inr (Or.inl rfl)) hGp
  · exact burnsideF45_C6_exc hyp (Or.inr (Or.inr rfl)) hGp
  · exact burnsideF45_C6_classical hyp (Or.inr (Or.inl rfl)) hGp
  · exact burnsideF45_C6_classical hyp (Or.inr (Or.inr rfl)) hGp
  · exact absurd rfl hκ.1
  · exact absurd rfl hκ.2

end C6

section Main

theorem burnside_as_F_4_5_of (hL3 : burnsideF45_C6Kind .L3) (hG2d : burnsideF45_ExcKind .G2d)
    (hTits : burnsideF45_ExcKind .Tits) : F_4_5 := by
  intro κ p f E _ Gp M₁ M₂ hyp ι hι
  subst hι
  have hL := burnsideF45_lieFactsAll
  have h1 : IsGenPolygon (incl M₁ M₂).graph κ.m := burnsideF45_C1 hL hyp
  have hm : 2 ≤ κ.m := by cases κ <;> simp [GLKind.m]
  have hexc : (κ = .G2d ∨ κ = .Tits) →
      (∀ u v : (incl M₁ M₂).Γ, (incl M₁ M₂).graph.Adj u v → burnsideF45_C6Body p Gp M₁ M₂ u v) ∧
        burnsideF45_C8Body κ (incl M₁ M₂) ∧ burnsideF45_C9Body κ p Gp (incl M₁ M₂) := by
    rintro (rfl | rfl)
    · exact hG2d p f E Gp M₁ M₂ hyp
    · exact hTits p f E Gp M₁ M₂ hyp
  refine ⟨h1, burnsideF45_clause2 hyp, burnsideF45_clause3 _ h1, burnsideF45_clause4 _ h1 hm,
    fun hext u v huv => burnsideF45_C5 hL burnsideF45_simple hyp hext u v huv, ?_,
    burnsideF45_C7 hL hyp, ?_, ?_⟩
  · intro hGp u v huv
    rcases burnsideF45_isLie_or κ with hκ | hκ
    · exact burnsideF45_C6_lie hL3 hyp hκ hGp u v huv
    · exact (hexc hκ).1 u v huv
  · rintro ⟨-, hκ⟩
    exact (hexc hκ.symm).2.1
  · rintro ⟨-, hκ⟩
    exact (hexc hκ.symm).2.2

theorem burnside_as_F_4_5_of_exc (hG2d : burnsideF45_ExcKind .G2d)
    (hTits : burnsideF45_ExcKind .Tits) : F_4_5 :=
  burnside_as_F_4_5_of (fun _ _ _ _ _ _ _ hyp hGp => burnsideF45_C6_L3 hyp hGp) hG2d hTits

theorem burnside_as_F_4_5_of_G2d (hG2d : burnsideF45_ExcKind .G2d) : F_4_5 :=
  burnside_as_F_4_5_of_exc hG2d burnsideF45_excKind_Tits

theorem as_F_4_5 : F_4_5 :=
  burnside_as_F_4_5_of_G2d burnsideF45_excKind_G2d

theorem burnside_as_F_4_6_of (hexc : burnsideF4b_F46Exc) : F_4_6 :=
  burnsideF4b_F46 (burnsideF45_LieFacts burnsideF45_lieFactsAll burnsideF45_simple)
    (fun _ _ _ _ _ _ _ _ hyp => burnsideF45_parabolics hyp.toHypF_4_4g) hexc

theorem burnside_as_F_4_6_of_G2d
    (hG2d : ∀ (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
      HypF_4_4 .G2d p f Gp M₁ M₂ → ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful →
      ∀ ι : Cpl M₁ M₂ ↥(M₁ ⊔ M₂), ι = incl M₁ M₂ → burnsideF4b_F46Body .G2d p Gp M₁ M₂ β ι) :
    F_4_6 :=
  burnside_as_F_4_6_of fun _ p f E _ Gp M₁ M₂ hyp hκ Y _ β hβ ι hι => by
    rcases hκ with rfl | rfl
    · exact hG2d p f E Gp M₁ M₂ hyp Y β hβ ι hι
    · exact burnsideF46_tits p f E Gp M₁ M₂ hyp Y β hβ ι hι

theorem as_F_4_6 : F_4_6 :=
  burnside_as_F_4_6_of_G2d burnsideF46_g2d

end Main

end CFSG.ASVolI
