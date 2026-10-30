module

public import CFSG.CGT.Timmesfeld75.L2FixedSylow
public import CFSG.RankThree.GF2n.Basic

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open CFSG.CGT.Timmesfeld75
open scoped MatrixGroups

variable {F : Type} [Field F] [Fintype F] [CharP F 2]

theorem MulAut.exists_sylow_inner_or_two_fixed (θ : MulAut SL(2, F)) (hθ : θ * θ = 1) :
    ∃ S : Subgroup SL(2, F), (∀ a ∈ S, a * a = 1) ∧ Nat.card S = Fintype.card F ∧
      S.map θ.toMonoidHom = S ∧
      ((∃ s ∈ S, θ = MulAut.conj s) ∨
        ∃ S' : Subgroup SL(2, F), (∀ a ∈ S', a * a = 1) ∧ Nat.card S' = Fintype.card F ∧
          S' ≠ S ∧ S'.map θ.toMonoidHom = S') := by
  classical
  haveI : Finite F := Finite.of_fintype F
  haveI : Finite (Matrix (Fin 2) (Fin 2) F) := Finite.of_fintype _
  haveI : Finite SL(2, F) :=
    Finite.of_injective (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F))
      Subtype.coe_injective
  have hθ' : ∀ x, θ (θ x) = x := fun x => by
    have h := congrArg (fun φ : MulAut SL(2, F) => φ x) hθ
    simpa using h
  obtain ⟨P, hP⟩ := exists_fixed_sylow_of_involutive θ hθ'
  obtain ⟨g, hg⟩ := exists_conjSubgroup_utri_eq_of_sylow P
  have hSfix : (conjSubgroup g (utri F)).map θ.toMonoidHom = conjSubgroup g (utri F) := by
    rw [hg]
    exact hP
  have hexp : ∀ h : SL(2, F), ∀ a ∈ conjSubgroup h (utri F), a * a = 1 := fun h a ha => by
    rw [← pow_two]
    exact (isElemAbelian_conjSubgroup isElemAbelian_utri h).2 a ha
  have hcard : ∀ h : SL(2, F), Nat.card (conjSubgroup h (utri F)) = Fintype.card F := fun h => by
    rw [card_conjSubgroup, card_utri, Nat.card_eq_fintype_card]
  have hpair : IsL2Pair SL(2, F) (conjSubgroup g (utri F)) (Nat.card F) := by
    refine ⟨F, inferInstance, inferInstance, inferInstance, MulAut.conj g⁻¹, rfl, ?_⟩
    change conjSubgroup g⁻¹ (conjSubgroup g (utri F)) = utri F
    rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  by_cases huniq : ∀ h : SL(2, F),
      (conjSubgroup h (conjSubgroup g (utri F))).map θ.toMonoidHom =
        conjSubgroup h (conjSubgroup g (utri F)) →
      conjSubgroup h (conjSubgroup g (utri F)) = conjSubgroup g (utri F)
  · obtain ⟨t, htS, -, ht⟩ := hpair.exists_involution_of_unique_fixed θ hθ' hSfix huniq
    refine ⟨conjSubgroup g (utri F), hexp g, hcard g, hSfix, Or.inl ⟨t, htS, ?_⟩⟩
    apply MulEquiv.ext
    intro x
    rw [MulAut.conj_apply]
    exact ht x
  · push Not at huniq
    obtain ⟨h, hfix, hne⟩ := huniq
    refine ⟨conjSubgroup g (utri F), hexp g, hcard g, hSfix, Or.inr
      ⟨conjSubgroup h (conjSubgroup g (utri F)), ?_, ?_, hne, hfix⟩⟩
    · rw [← conjSubgroup_mul]
      exact hexp (h * g)
    · rw [← conjSubgroup_mul]
      exact hcard (h * g)

end CFSG.RankThree.GF2n.Tim81.Sec2
