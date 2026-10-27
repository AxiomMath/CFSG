module

public import CFSG.LocalAnalysis.UniquenessCase.UC6P6b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.Open

@[expose] def KProjRepL2 : Prop :=
  ∀ (J : Type) [Group J] [Finite J], CFSG.Open.IsQuasisimple J →
    ∀ (N : Subgroup J) [N.Normal], N ≤ center J → ∀ r : ℕ, r.Prime → 5 ≤ r →
      CFSG.Blueprint.LieModel (J ⧸ N) .PSL 2 r 2 →
      ∀ q : ℕ, q.Prime → q ≠ r → ∀ d : ℕ, d ≤ 6 →
        ∀ f : J →* (Matrix.GeneralLinearGroup (Fin d) (ZMod q)) ⧸
          center (Matrix.GeneralLinearGroup (Fin d) (ZMod q)), f = 1

@[expose] def KProjRepTits : Prop :=
  ∀ (J : Type) [Group J] [Finite J], CFSG.Open.IsQuasisimple J →
    ∀ (N : Subgroup J) [N.Normal], N ≤ center J →
      CFSG.Blueprint.LieModel (J ⧸ N) .Tits 0 2 1 →
      ∀ q : ℕ, q.Prime → q ≠ 5 → ∀ d : ℕ, d ≤ 6 →
        ∀ f : J →* (Matrix.GeneralLinearGroup (Fin d) (ZMod q)) ⧸
          center (Matrix.GeneralLinearGroup (Fin d) (ZMod q)), f = 1

@[expose] def KProjRepA10 : Prop :=
  ∀ (J : Type) [Group J] [Finite J], CFSG.Open.IsQuasisimple J →
    ∀ (N : Subgroup J) [N.Normal], N ≤ center J →
      CFSG.LocalAnalysis.UniquenessCase.UC22.IsAlt (J ⧸ N) 10 →
      ∀ q : ℕ, q.Prime → q ≠ 5 → ∀ d : ℕ, d ≤ 6 →
        ∀ f : J →* (Matrix.GeneralLinearGroup (Fin d) (ZMod q)) ⧸
          center (Matrix.GeneralLinearGroup (Fin d) (ZMod q)), f = 1

theorem kProjRep620_of_clauses (hL2 : KProjRepL2) (hT : KProjRepTits) (hA : KProjRepA10) :
    KProjRep620 := by
  intro J _ _ hq N _ hN r hr hr5 hlist q hq' hqr d hd f
  rcases hlist with h | ⟨rfl, h | h⟩
  · exact hL2 J hq N hN r hr hr5 h q hq' hqr d hd f
  · exact hT J hq N hN h q hq' hqr d hd f
  · exact hA J hq N hN h q hq' hqr d hd f

end CFSG.LocalAnalysis.UniquenessCase.UCK
