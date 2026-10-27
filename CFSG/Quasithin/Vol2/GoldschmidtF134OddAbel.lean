module

public import CFSG.Quasithin.Vol2.F134Suzuki
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
public import CFSG.Walter.J1Props.Aut
public import CFSG.Walter.Models
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddDickson

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Vol2Native
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open scoped commutatorElement

theorem outer_comm_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∀ a b : Outer Y, a * b = b * a) : ∀ a b : Outer X, a * b = b * a := fun a b =>
  (equivalence e).injective (by rw [map_mul, map_mul]; exact h _ _)

theorem outer_comm_of_j1 {X : Type} [Group X]
    (e : X ≃* CFSG.Blueprint.NativeSporadic.Carrier .J1) : ∀ a b : Outer X, a * b = b * a := by
  intro a b
  have hone : ∀ c : Outer X, c = 1 := by
    intro c
    obtain ⟨ξ, rfl⟩ := QuotientGroup.mk_surjective c
    let ε : X ≃* CFSG.Open.walterJ1 := e.trans CFSG.Walter.walterJ1EquivNative.symm
    obtain ⟨g, hg⟩ := CFSG.Walter.J1Props.J3_aut (ε.symm.trans (ξ.trans ε))
    have hξ : ξ = MulAut.conj (ε.symm g) := by
      apply MulEquiv.ext
      intro x
      apply ε.injective
      have h1 := congrArg (fun f : MulAut CFSG.Open.walterJ1 => f (ε x)) hg
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
      rw [h1]
      simp
    rw [QuotientGroup.eq_one_iff]
    exact ⟨ε.symm g, hξ.symm⟩
  rw [hone a, hone b]

theorem facts134Odd_outAbelian :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A), SQTKHypCat A →
      CFSG.IsComponent L → A38Types ↥L → ∀ a ∈ Subgroup.normalizer (L : Set A),
        ∀ b ∈ Subgroup.normalizer (L : Set A), ⁅a, b⁆ ∈ L ⊔ Subgroup.centralizer (L : Set A) := by
  intro A _ _ L _ _ hT a ha b hb
  rcases hT with ⟨n, hn⟩ | ⟨n, hn⟩ | hJ | ⟨q, hq, -, hpsl⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨e⟩ := nonempty_mulEquiv_psl2_odd hn
    exact F134.commutator_mem_sup_centralizer L (outer_comm_of_mulEquiv e
      (CFSG.LocalAnalysis.ComponentInitial.OuterDerived.outer_psl2_mul_comm _)) ha hb
  · exact F134.commutator_mem_of_suzukiModel hn ha hb
  · have ⟨e⟩ : Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.Carrier .J1) := hJ
    exact F134.commutator_mem_sup_centralizer L (outer_comm_of_j1 e) ha hb
  · have : Fact q.Prime := ⟨hq⟩
    obtain ⟨e⟩ := nonempty_mulEquiv_psl2_odd hpsl
    exact F134.commutator_mem_sup_centralizer L (outer_comm_of_mulEquiv e
      (CFSG.LocalAnalysis.ComponentInitial.OuterDerived.outer_psl2_mul_comm _)) ha hb

end CFSG.Quasithin.H13.NQCore
