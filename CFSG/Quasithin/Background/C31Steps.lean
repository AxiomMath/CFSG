module

public import CFSG.Quasithin.Background.C31Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable (G : Type) [Group G] [Finite G]

@[expose] def C31BasicStep : Prop :=
  ∀ H R M L V K : Subgroup G, HypC28 H R M L V → CFSG.Open.IsComponentOf K H →
    C31Basic H R M L V K

@[expose] def C31SporStep : Prop :=
  ∀ H R M L V K : Subgroup G, HypC28 H R M L V → CFSG.Open.IsComponentOf K H →
    C31Basic H R M L V K → ∀ s : TauCeti.SporadicName,
    (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨ s = .J4 ∨
      s = .HS ∨ s = .He ∨ s = .Ru) →
    IsSporadic s (↥K ⧸ Subgroup.center ↥K) →
    L = conjClosure L M ∧
      (C31Case3 H R M L V K ∨ C31Case4 H R M L V K ∨ C31Case5 H R M L V K ∨
        C31Case6 H R M L V K ∨ C31Case7 H R M L V K ∨ C31Case8 H R M L V K ∨
        C31Case9 H R M L V K)

@[expose] def C31NonLieStep : Prop :=
  ∀ H R M L V K : Subgroup G, HypC28 H R M L V → CFSG.Open.IsComponentOf K H →
    C31Basic H R M L V K →
    ¬ (IsAlt 7 (↥K ⧸ Subgroup.center ↥K) ∨
      ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
        ((∃ f : ℕ, (f = 1 ∨ f = 2) ∧ IsPSL 2 p f (↥K ⧸ Subgroup.center ↥K)) ∨
          IsPSL 3 p 1 (↥K ⧸ Subgroup.center ↥K) ∨ IsPSU 3 p 1 (↥K ⧸ Subgroup.center ↥K)))

@[expose] def C31Lie2Types (S : Type) [Group S] : Prop :=
  IsAlt 5 S ∨ IsAlt 6 S ∨ IsAlt 8 S ∨
    ((∃ f : ℕ, (2 ≤ f ∧ IsPSL 2 2 f S) ∨ (1 ≤ f ∧ IsPSL 3 2 f S) ∨ (2 ≤ f ∧ IsPSU 3 2 f S) ∨
        (2 ≤ f ∧ IsPSp4 2 f S) ∨ (2 ≤ f ∧ IsG2 2 f S) ∨ (1 ≤ f ∧ Is3D4 2 f S) ∨
        (Odd f ∧ 3 ≤ f ∧ Is2F4 f S) ∨ (Odd f ∧ 3 ≤ f ∧ IsSz f S)) ∨
      IsTits S) ∨
    ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ IsPSL n 2 1 S

@[expose] def C31LieStep : Prop :=
  ∀ H R M L V K : Subgroup G, HypC28 H R M L V → CFSG.Open.IsComponentOf K H →
    C31Basic H R M L V K → C31Lie2Types (↥K ⧸ Subgroup.center ↥K) →
    L = conjClosure L M ∧
      (C31Case1 H R M L V K ∨ C31Case2 H R M L V K ∨ C31Case10 H R M L V K)

end CFSG.Quasithin
