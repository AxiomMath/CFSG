module

public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.OneCompAdapter

public section

namespace CFSG.Quasithin.G11.Harris

open CFSG.Open CFSG.Blueprint
open CFSG.Quasithin.Background.Harris.OrdinaryProofs

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem nonempty_quotCenterEquiv {Γ L : Subgroup (GLV V)} (hL : IsComponentOf L Γ)
    (hsimp : IsSimpleGroup ↥L) : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* ↥L) := by
  obtain ⟨-, -, hperf, -⟩ := hL
  have hZ : Subgroup.center ↥L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with h | h
    · exact h
    · exfalso
      have hcomm : commutator ↥L = ⊥ := by
        rw [commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        exact Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top x) y
      rw [hcomm] at hperf
      exact (bot_ne_top hperf : False)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot⟩

theorem center_eq_bot_of_simple_component {Γ L : Subgroup (GLV V)} (hL : IsComponentOf L Γ)
    (hsimp : IsSimpleGroup ↥L) : Subgroup.center ↥L = ⊥ := by
  obtain ⟨-, -, hperf, -⟩ := hL
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with h | h
  · exact h
  · exfalso
    have hcomm : commutator ↥L = ⊥ := by
      rw [commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top x) y
    rw [hcomm] at hperf
    exact (bot_ne_top hperf : False)

theorem oneCompFor_of_simple_quot {P Q : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ (X Y : Type) [Group X] [Group Y], (X ≃* Y) → P Y → P X)
    (hQ : ∀ (X : Type) [Group X], Q X → IsSimpleGroup X ∧ P X)
    (h : ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (Γ A L : Subgroup (GLV V)) (m : ℕ),
      G93Hyp Γ A L L m → P (↥L ⧸ Subgroup.center ↥L) → G93Concl Γ L m) :
    OneCompFor Q := by
  intro V _ _ _ Γ A L m hs hQL
  obtain ⟨hsimp, hPL⟩ := hQ ↥L hQL
  obtain ⟨e⟩ := nonempty_quotCenterEquiv hs.L_comp hsimp
  exact h V Γ A L m (OneCompSetting.toG93Hyp hs) (hP _ _ e hPL)

theorem oneCompFor_famSpor_of_false (s : TauCeti.SporadicName)
    (h : ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (Γ A L : Subgroup (GLV V)) (m : ℕ),
      G93Hyp Γ A L L m → Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier s) →
        False) :
    OneCompFor (FamSpor s) :=
  oneCompFor_of_simple_quot (P := fun X _ => Nonempty (X ≃* NativeSporadic.Carrier s))
    (fun _ _ _ _ e ⟨e'⟩ => ⟨e.trans e'⟩) (fun _ _ h => h)
    (fun V _ _ _ Γ A L m hG hP => (h V Γ A L m hG hP).elim)

theorem oneCompFor_famSz_of_false
    (h : ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (f : ℕ), Odd f → 3 ≤ f →
      ∀ (Γ A L : Subgroup (GLV V)) (m : ℕ),
      G93Hyp Γ A L L m → SuzukiModel (↥L ⧸ Subgroup.center ↥L) 2 f → False) :
    OneCompFor FamSz :=
  oneCompFor_of_simple_quot (P := fun X _ => ∃ f, Odd f ∧ 3 ≤ f ∧ SuzukiModel X 2 f)
    (fun _ _ _ _ e ⟨f, hf, hf3, hm⟩ =>
      ⟨f, hf, hf3, CFSG.SectionRank.suzukiModel_of_mulEquiv e hm⟩)
    (fun _ _ ⟨hs, h⟩ => ⟨hs, h⟩)
    (fun V _ _ _ Γ A L m hG ⟨f, hf, hf3, hP⟩ => (h V f hf hf3 Γ A L m hG hP).elim)

theorem oneCompFor_famU3_of_false
    (h : ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (f : ℕ), 2 ≤ f →
      ∀ (Γ A L : Subgroup (GLV V)) (m : ℕ), G93Hyp Γ A L L m →
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 2 f →
        False) :
    OneCompFor FamU3 :=
  oneCompFor_of_simple_quot
    (P := fun X _ => ∃ f, 2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 2 f)
    (fun _ _ _ _ e ⟨f, hf, hm⟩ => ⟨f, hf, CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hm⟩)
    (fun _ _ ⟨hs, h⟩ => ⟨hs, h⟩)
    (fun V _ _ _ Γ A L m hG ⟨f, hf, hP⟩ => (h V f hf Γ A L m hG hP).elim)

end CFSG.Quasithin.G11.Harris
