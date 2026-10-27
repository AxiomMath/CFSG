module

public import CFSG.Quasithin.Background.F7TwoInvG2Long
public import CFSG.Quasithin.Background.F7TwoInvG2Short
public import CFSG.Quasithin.Background.F7TwoInvG2Field
public import CFSG.Quasithin.Background.F7TwoInvSQTKFam
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAllInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenFieldInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenInvolutions
public import CFSG.LieType.Chevalley.AdjointCenter

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F7Two.G2Ev

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank

theorem mul_self_eq_one_of_conj {G : Type*} [Group G] (hZ : Subgroup.center G = ⊥) {g : G}
    (h : MulAut.conj g * MulAut.conj g = 1) : g * g = 1 := by
  have hc : g * g ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun x => by
    have hx := congrArg (fun φ : MulAut G => φ x) h
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply] at hx
    calc x * (g * g) = g * (g * x * g⁻¹) * g⁻¹ * (g * g) := by rw [hx]
      _ = g * g * x := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact hc

section Assembly


theorem invAutGen_adjointGroup_g2 {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) (φ : MulAut ↥(adjointGroup .G2 K)) (hφ2 : φ * φ = 1) (hφ1 : φ ≠ 1) :
    InvAutGen ↥(adjointGroup .G2 K) φ := by
  have hcharP : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  have hZ : Subgroup.center ↥(adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf φ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hφ2) hφ1
  rcases even_G2_involution_inner_or_canonical_field hf K hK φ hord with hin | ⟨hfe, hfield⟩
  · obtain ⟨g, rfl⟩ := hin
    have hg2 : g * g = 1 := mul_self_eq_one_of_conj hZ hφ2
    have hg1 : g ≠ 1 := fun h => hφ1 (by rw [h, map_one])
    have hgord : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hg2) hg1
    rcases even_G2_involutions_conjugate_to_root_elements K (ringChar.eq K 2) g hgord with
      hc | hv
    · exact invAutGen_conj_of_isConj hc.symm invAutGen_g2_long
    · exact invAutGen_conj_of_isConj hv.symm invAutGen_g2_short
  · have hδ : ∀ c : K, (iterateFrobenius K 2 (f / 2)) c = c ^ 2 ^ (f / 2) := fun c => rfl
    obtain ⟨β, ψ, hβ, hψ, -⟩ := hfield (iterateFrobenius K 2 (f / 2)) hδ
    refine invAutGen_of_conj_aut ψ⁻¹ ?_ (invAutGen_g2_field hf hfe hK hδ hβ)
    rw [← hψ]
    group

theorem invAutGenFamG2Even : InvAutGenFamG2Even := by
  intro f S _ _ hf hmod φ hφ2 hφ1
  obtain ⟨-, K, _, hKfin, hK, ⟨e⟩⟩ := hmod
  have hZ : Subgroup.center ↥(adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  let Q : AdjointQuotient .G2 K ≃* ↥(adjointGroup .G2 K) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let E : S ≃* ↥(adjointGroup .G2 K) := e.trans Q
  have hφ' : InvAutGen ↥(adjointGroup .G2 K) ((E.symm.trans φ).trans E) := by
    refine invAutGen_adjointGroup_g2 hf hK _ ?_ ?_
    · refine MulEquiv.ext fun x => ?_
      have := MulEquiv.congr_fun hφ2 (E.symm x)
      simp only [MulAut.mul_apply, MulAut.one_apply] at this
      simp [this]
    · intro h1
      apply hφ1
      refine MulEquiv.ext fun y => ?_
      have := MulEquiv.congr_fun h1 (E y)
      simpa using this
  have h2 := InvAutGen.congr E.symm hφ'
  have e1 : (E.trans ((E.symm.trans φ).trans E)).trans E.symm = φ :=
    MulEquiv.ext fun y => by simp
  rwa [show ((E.symm).symm.trans ((E.symm.trans φ).trans E)).trans E.symm = φ from e1] at h2

end Assembly

end CFSG.Quasithin.F7Two.G2Ev
