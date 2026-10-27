module

public import CFSG.RankThree.PartOne.KC.UnitaryRigidityThree
public import CFSG.RankThree.PartOne.KC.UnitaryRigidityGt

public section

namespace CFSG.RankThree.PartOne.KCUnitaryNonsplit

open Polynomial Module Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryExact CFSG.RankThree.PartOne.KCUnitaryPlane
  CFSG.RankThree.PartOne.KCUnitaryLines CFSG.RankThree.PartOne.KCUnitaryGt
  CFSG.RankThree.PartOne.KCUnitaryThree

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}
  {Ahat : Subgroup (gramSU h (idGram K n))}

theorem rigidity_of_nonsplit (F : NonsplitFacts h n p Ahat) (S : PlaneSetup h n p Ahat)
    (β : MulAut (primeFormP h (idGram K n)))
    (hcent : ∀ x ∈ Ahat, β * primeFormConjHom h (idGram K n) (liftUnitary x) =
      primeFormConjHom h (idGram K n) (liftUnitary x) * β)
    (hblock : ∀ x ∈ Ahat, x ≠ 1 → ∀ i : GoodBlockIdx h x, ∀ g ∈ idSpecialBlock h x (i.1 : K[X]),
      β * primeFormConjHom h (idGram K n) g = primeFormConjHom h (idGram K n) g * β) :
    β = 1 := by
  classical
  have hn := S.three_le
  have hne := S.ne
  obtain ⟨⟨M, τ⟩, rfl⟩ := surjective_primeFormPsi_of_ne (h := h) hn hne β
  have hτ : τ = RingEquiv.refl K := by
    by_cases hbig : ∃ L : Subgroup ↥Ahat, Nat.card L = p ∧
        lineSpace (planeRep h n Ahat) (idForm h n) L ≠ ⊥ ∧
        3 ≤ Module.finrank K ↥(fixedSpace (planeRep h n Ahat) ⊤ ⊔
          lineSpace (planeRep h n Ahat) (idForm h n) L)
    · obtain ⟨L, hL, hVL, hbig⟩ := hbig
      exact tau_eq_one_of_big_line F S hL hVL hbig M τ hblock
    · refine tau_eq_one_of_two_dim_lines F S (fun L hL hVL => ?_) M τ hcent hblock
      by_contra hcon
      exact hbig ⟨L, hL, hVL, by omega⟩
  subst hτ
  have hmat1 : ∀ g : GL (Fin n) K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map
      (RingEquiv.refl K) = ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := fun g => by
    ext
    rfl
  have hMx : ∀ x ∈ Ahat, M * liftUnitary x = liftUnitary x * M := by
    intro x hx
    have := matrix_comm_of_plane S hx M (RingEquiv.refl K) (hcent x hx)
    rw [hmat1] at this
    exact Subtype.ext (Units.ext this)
  have hMb : ∀ x ∈ Ahat, x ≠ 1 → ∀ i : GoodBlockIdx h x, ∀ g ∈ idSpecialBlock h x (i.1 : K[X]),
      M * g = g * M := by
    intro x hx hx1 i g hg
    have := matrix_comm_of_perfect S.three_le S.ne (isPerfect_idSpecialBlock S hx i) M
      (RingEquiv.refl K) (hblock x hx hx1 i) g hg
    rw [hmat1] at this
    exact Subtype.ext (Units.ext this)
  obtain ⟨c, hc⟩ := exists_global_scalar F S M hMx hMb
  exact psi_eq_one_of_scalar hn hne M c hc

end CFSG.RankThree.PartOne.KCUnitaryNonsplit
