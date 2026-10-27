module

public import CFSG.RankThree.PartTwo.Setup

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.RankThreeEven

@[expose] def Item433Case (i : TauCeti.CFSGIndex) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], TheoremFourHyp G → (G ≃* i.Group) → IIModel G

@[expose] def Excluded433 (i : TauCeti.CFSGIndex) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], TheoremFourHyp G → (G ≃* i.Group) → False

theorem Excluded433.item433Case {i : TauCeti.CFSGIndex} (h : Excluded433 i) : Item433Case i :=
  fun G _ _ hG e => (h G hG e).elim

theorem item433_of_cases (h : ∀ i, Item433Case i) : Item433 := by
  intro G _ _ hG hcat
  obtain ⟨i, ⟨e⟩⟩ := hcat
  exact h i G hG e

theorem item433Case_Co2 : Item433Case (.sporadic .Co2) :=
  fun _ _ _ _ e => Or.inl ⟨e⟩

theorem item433Case_Th : Item433Case (.sporadic .Th) :=
  fun _ _ _ _ e => Or.inr (Or.inl ⟨e⟩)

theorem item433Case_F4_two (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.F4 q).Valid)
    (hp : q.p = 2) (he : q.exponent = 1) : Item433Case (.lie ⟨.F4 q, hv⟩) := by
  obtain rfl : q = primePowerTwo := TauCeti.PrimePower.ext hp he
  exact fun _ _ _ _ e => Or.inr (Or.inr (Or.inr ⟨e⟩))

theorem item433Case_lie_of_families
    (hA : ∀ r q hv, Item433Case (.lie ⟨.A r q, hv⟩))
    (h2A : ∀ r q hv, Item433Case (.lie ⟨.twistedA r q, hv⟩))
    (hB : ∀ r q hv, Item433Case (.lie ⟨.B r q, hv⟩))
    (hC : ∀ r q hv, Item433Case (.lie ⟨.C r q, hv⟩))
    (hD : ∀ r q hv, Item433Case (.lie ⟨.D r q, hv⟩))
    (h2D : ∀ r q hv, Item433Case (.lie ⟨.twistedD r q, hv⟩))
    (hE6 : ∀ q hv, Item433Case (.lie ⟨.E6 q, hv⟩))
    (hE7 : ∀ q hv, Item433Case (.lie ⟨.E7 q, hv⟩))
    (hE8 : ∀ q hv, Item433Case (.lie ⟨.E8 q, hv⟩))
    (hF4 : ∀ q hv, Item433Case (.lie ⟨.F4 q, hv⟩))
    (hG2 : ∀ q hv, Item433Case (.lie ⟨.G2 q, hv⟩))
    (h2E6 : ∀ q hv, Item433Case (.lie ⟨.twistedE6 q, hv⟩))
    (h3D4 : ∀ q hv, Item433Case (.lie ⟨.trialityD4 q, hv⟩))
    (hSz : ∀ m hv, Item433Case (.lie ⟨.suzuki m, hv⟩))
    (hRee : ∀ m hv, Item433Case (.lie ⟨.reeG2 m, hv⟩))
    (hReeF4 : ∀ m hv, Item433Case (.lie ⟨.reeF4 m, hv⟩))
    (hTits : ∀ hv, Item433Case (.lie ⟨.tits, hv⟩)) :
    ∀ d, Item433Case (.lie d) := by
  rintro ⟨d, hv⟩
  cases d with
  | A r q => exact hA r q hv
  | twistedA r q => exact h2A r q hv
  | B r q => exact hB r q hv
  | C r q => exact hC r q hv
  | D r q => exact hD r q hv
  | twistedD r q => exact h2D r q hv
  | E6 q => exact hE6 q hv
  | E7 q => exact hE7 q hv
  | E8 q => exact hE8 q hv
  | F4 q => exact hF4 q hv
  | G2 q => exact hG2 q hv
  | twistedE6 q => exact h2E6 q hv
  | trialityD4 q => exact h3D4 q hv
  | suzuki m => exact hSz m hv
  | reeG2 m => exact hRee m hv
  | reeF4 m => exact hReeF4 m hv
  | tits => exact hTits hv

end CFSG.RankThree.PartTwo.Census
