module

public import CFSG.LieType.BorelTits.AllModels

public section

universe u v w

namespace CFSG.Open

open scoped MatrixGroups in
theorem _root_.CFSG.Milestones.cl_lit_borel_tits_local_parabolic
    (r k n : ℕ) [Fact r.Prime] (hk : 0 < k) (hn : 2 ≤ n) (hsmall : n = 2 → 4 ≤ r ^ k)
    (U : Subgroup PSL(n, GaloisField r k)) (hU : U ≠ ⊥) (hUr : IsPGroup r U) :
    ∃ (S : Sylow r PSL(n, GaloisField r k)) (P : Subgroup PSL(n, GaloisField r k)),
      P ≠ ⊤ ∧
      Subgroup.normalizer (U : Set PSL(n, GaloisField r k)) ≤ P ∧
      pCoreOf r (Subgroup.normalizer (U : Set PSL(n, GaloisField r k))) ≤ pCoreOf r P ∧
      Subgroup.normalizer ((S : Subgroup PSL(n, GaloisField r k)) :
        Set PSL(n, GaloisField r k)) ≤ P := by
  obtain ⟨S, P, hP, hN, hcore, -, hS⟩ :=
    LieType.BorelTits.holds_projectiveSpecialLinearGroup n (GaloisField r k) r U hU hUr
  exact ⟨S, P, hP, hN, hcore, hS⟩

end CFSG.Open

namespace CFSG.Milestones

theorem cl_lit_borel_tits_local_parabolic_all_models
    (X : Type) [Group X] (t : Assembly.LowTwoRank.StatedLieTag) (n r f : ℕ)
    (hmodel : Blueprint.LieModel X t n r f)
    (U : Subgroup X) (hU : U ≠ ⊥) (hUr : IsPGroup r U) :
    ∃ (S : Sylow r X) (P : Subgroup X), P ≠ ⊤ ∧
      Subgroup.normalizer (U : Set X) ≤ P ∧
      Open.pCoreOf r (Subgroup.normalizer (U : Set X)) ≤ Open.pCoreOf r P ∧ U ≤ Open.pCoreOf r P ∧
      (t ≠ .Tits → Subgroup.normalizer ((S : Subgroup X) : Set X) ≤ P) ∧
      (t = .Tits → (S : Subgroup X) ≤ P) :=
  LieType.BorelTits.lieModel_conclusion X t n r f hmodel U hU hUr

end CFSG.Milestones
