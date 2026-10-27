module

public import CFSG.Sporadic.HeldB.InnerClass
public import CFSG.Sporadic.HeldB.AutModelCore
public import CFSG.LocalAnalysis.ComponentInitial.OddCoreCorrespondence
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalUnbalanced
import CFSG.Adapters.WholeGroupLayer

public noncomputable section

namespace CFSG.Sporadic.HeldB

open CFSG.ComponentClassification CFSG.ComponentClassification.OutcomeLocal
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.ComponentInitial
  CFSG.Sporadic.Schreier CFSG.Blueprint

variable {X : Type} [Group X] [Finite X]

theorem centralizer_generalizedFitting_eq_bot
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) :
    Subgroup.centralizer (GeneralizedFitting.subgroup X : Set X) = ⊥ := by
  rw [← CFSG.generalizedFitting_eq_componentClassification] at hsimple hnab ⊢
  exact CFSG.Adapters.centralizer_generalizedFitting_eq_bot_of_isSimpleGroup X hsimple hnab

theorem index_generalizedFitting_le_two_of_outer (hOut : Nat.card (Outer NativeSporadic.He) ≤ 2)
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (θ : GeneralizedFitting.subgroup X ≃* NativeSporadic.He) :
    (GeneralizedFitting.subgroup X).index ≤ 2 := by
  set F := GeneralizedFitting.subgroup X
  have : F.Normal := GeneralizedFitting.normal X
  have hinj : Function.Injective (MulAut.conjNormal : X →* MulAut F) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff,
      ← centralizer_generalizedFitting_eq_bot hsimple hnab]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := congrArg (fun α : MulAut F => ((α ⟨y, hy⟩ : F) : X)) (MonoidHom.mem_ker.1 hx)
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
    calc y * x = x * y * x⁻¹ * x := by rw [h]
      _ = x * y := by group
  have h1 : Nat.card X ≤ Nat.card (MulAut F) := Nat.card_le_card_of_injective _ hinj
  have h2 : Nat.card (MulAut F) ≤ 2 * Nat.card NativeSporadic.He :=
    card_mulAut_le_of_equiv hOut θ.symm
  have h3 : Nat.card NativeSporadic.He = Nat.card F := Nat.card_congr θ.symm.toEquiv
  have h4 := F.card_mul_index
  have hpos : 0 < Nat.card F := Nat.card_pos
  by_contra hlt
  push Not at hlt
  have : Nat.card F * 3 ≤ Nat.card F * F.index := Nat.mul_le_mul_left _ hlt
  omega

theorem oddCore_eq_bot_of_mulEquiv' {A B : Type*} [Group A] [Group B]
    (h : CFSG.oddCore B = ⊥) (e : A ≃* B) : CFSG.oddCore A = ⊥ :=
  oddCore_eq_bot_of_mulEquiv e h

@[expose] def generalizedFittingCentralizerEquiv (s : GeneralizedFitting.subgroup X) :
    Subgroup.centralizer ({s} : Set (GeneralizedFitting.subgroup X)) ≃*
      (GeneralizedFitting.subgroup X ⊓ Subgroup.centralizer {(s : X)} : Subgroup X) :=
  ((Subgroup.centralizer ({s} : Set (GeneralizedFitting.subgroup X))).equivMapOfInjective
    (GeneralizedFitting.subgroup X).subtype (Subgroup.subtype_injective _)).trans
    (MulEquiv.subgroupCongr (map_centralizer_subtype (GeneralizedFitting.subgroup X) s))

theorem inner_pPrimeCore_eq_bot_of_outer
    (hOut : Nat.card (Outer NativeSporadic.He) ≤ 2)
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (θ : GeneralizedFitting.subgroup X ≃* NativeSporadic.He) {t : X}
    (ht : t ∈ GeneralizedFitting.subgroup X) (ht2 : orderOf t = 2) :
    CFSG.pPrimeCore 2 (Subgroup.centralizer ({t} : Set X)) = ⊥ := by
  set F := GeneralizedFitting.subgroup X
  have : F.Normal := GeneralizedFitting.normal X
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx := index_generalizedFitting_le_two_of_outer hOut hsimple hnab θ
  have hp : IsPGroup 2 (X ⧸ F) := by
    have hpos : 0 < F.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have hcard : Nat.card (X ⧸ F) = F.index := rfl
    interval_cases h : F.index
    · exact IsPGroup.of_card (n := 0) (by rw [hcard, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [hcard, pow_one])
  let s : F := ⟨t, ht⟩
  have hs2 : orderOf s = 2 := by rw [← Subgroup.orderOf_coe]; exact ht2
  have hθ2 : orderOf (θ s) = 2 := (@orderOf_mulEquiv_apply _ _ _ Units.instGroup θ s).trans hs2
  have hHe := ctbhi_held_inner_involution_centralizers_odd_core.1 (θ s) hθ2
  rw [← oddCore_eq_pPrimeCore_two'] at hHe
  have hF : CFSG.pPrimeCore 2 ↥(F ⊓ Subgroup.centralizer ({t} : Set X)) = ⊥ := by
    rw [← oddCore_eq_pPrimeCore_two']
    exact oddCore_eq_bot_of_mulEquiv' hHe ((generalizedFittingCentralizerEquiv s).symm.trans
      (@centralizerEquiv _ _ _ Units.instGroup θ s))
  have key := (normal_prime_power_index_prime_complement_core 2 hp).2 t
  rw [hF, Subgroup.map_bot, Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)]
    at key
  exact key

theorem Held_almost_simple_inner_involution_exclusion_of_outer
    (hOut : Nat.card (Outer NativeSporadic.He) ≤ 2)
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (hiso : Nonempty (GeneralizedFitting.subgroup X ≃* NativeSporadic.He)) :
    (GeneralizedFitting.subgroup X).index ≤ 2 ∧
    (∀ t ∈ GeneralizedFitting.subgroup X, orderOf t = 2 →
      CFSG.pPrimeCore 2 (Subgroup.centralizer ({t} : Set X)) = ⊥) ∧
    ∀ z : X, orderOf z = 2 → CFSG.pPrimeCore 2 (Subgroup.centralizer ({z} : Set X)) ≠ ⊥ →
      z ∉ GeneralizedFitting.subgroup X ∧ GeneralizedFitting.subgroup X < ⊤ ∧
        (GeneralizedFitting.subgroup X).index = 2 ∧ UOutcome X := by
  obtain ⟨θ⟩ := hiso
  have hidx := index_generalizedFitting_le_two_of_outer hOut hsimple hnab θ
  have hin : ∀ t ∈ GeneralizedFitting.subgroup X, orderOf t = 2 →
      CFSG.pPrimeCore 2 (Subgroup.centralizer ({t} : Set X)) = ⊥ := fun t ht ht2 =>
    inner_pPrimeCore_eq_bot_of_outer hOut hsimple hnab θ ht ht2
  refine ⟨hidx, hin, fun z hz2 hz => ?_⟩
  have hzF : z ∉ GeneralizedFitting.subgroup X := fun h => hz (hin z h hz2)
  have hlt : GeneralizedFitting.subgroup X < ⊤ :=
    lt_top_iff_ne_top.2 fun h => hzF (h ▸ Subgroup.mem_top z)
  have hne : (GeneralizedFitting.subgroup X).index ≠ 1 := fun h =>
    (lt_top_iff_ne_top.1 hlt) (Subgroup.index_eq_one.1 h)
  have hpos : 0 < (GeneralizedFitting.subgroup X).index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  exact ⟨hzF, hlt, by omega, Or.inr (Or.inr ⟨Or.inr ⟨θ⟩, hlt⟩)⟩

end CFSG.Sporadic.HeldB
