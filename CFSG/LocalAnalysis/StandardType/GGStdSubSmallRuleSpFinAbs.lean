module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpTwo
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticCover

public section

namespace CFSG.StandardType.SpFin

open CFSG.Assembly TableB

theorem isComponentOf_of_normalized {G : Type*} [Group G] {C Q : Subgroup G} (hQC : Q ≤ C)
    (hQn : ∀ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q) (hQq : CFSG.IsQuasisimple Q) :
    IsComponentOf Q C := by
  refine ⟨hQC, IsSubnormal.step hQC ?_ (IsSubnormal.refl C),
    (TableBSymp.isQuasisimple_iff _).mpr hQq⟩
  rw [Subgroup.normal_subgroupOf_iff hQC]
  intro q c hq hc
  exact hQn c hc q hq

theorem layer_eq_of_isComponentOf {G : Type*} [Group G] [Finite G] {C Q : Subgroup G}
    (hQ : IsComponentOf Q C) (hE : IsComponentOf (LargeEvenLayer C) C) :
    LargeEvenLayer C = Q := by
  have hQE : Q ≤ LargeEvenLayer C := le_sSup hQ
  obtain ⟨hQC, hQs, hQqA⟩ := hQ
  obtain ⟨hEC, hEs, hEqA⟩ := hE
  have hQq : CFSG.IsQuasisimple Q := (TableBSymp.isQuasisimple_iff _).mp hQqA
  have hEq : CFSG.IsQuasisimple (LargeEvenLayer C) := (TableBSymp.isQuasisimple_iff _).mp hEqA
  have hQ'c : CFSG.IsComponent (Q.subgroupOf C) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hQC).symm hQq,
      hQs.subgroupOf⟩
  have hE'c : CFSG.IsComponent ((LargeEvenLayer C).subgroupOf C) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hEC).symm hEq,
      hEs.subgroupOf⟩
  rcases CFSG.LocalCores.distinct_components_commute hQ'c hE'c with h | h
  · have h1 := Subgroup.subgroupOf_inj.mp h
    rw [inf_eq_left.mpr hQC, inf_eq_left.mpr hEC] at h1
    exact h1.symm
  · exfalso
    have hle : Q.subgroupOf C ≤ (LargeEvenLayer C).subgroupOf C := Subgroup.subgroupOf_mono C hQE
    have h1 : ⁅Q.subgroupOf C, Q.subgroupOf C⁆ = ⊥ :=
      le_bot_iff.mp (h ▸ Subgroup.commutator_mono le_rfl hle)
    have h2 : ⁅Q.subgroupOf C, Q.subgroupOf C⁆ = Q.subgroupOf C :=
      Subgroup.isPerfect_iff.mp hQ'c.1.1
    have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hQ'c.1
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(Q.subgroupOf C))
    have hx' : (x : C) ∈ ⁅Q.subgroupOf C, Q.subgroupOf C⁆ := h2.symm ▸ x.2
    rw [h1, Subgroup.mem_bot] at hx'
    exact hx (Subtype.ext hx')

theorem false_of_normal_quasisimple {L' : Type} [Group L'] [Finite L'] {A : Subgroup (MulAut L')}
    {a : MulAut L'} (hcomp : IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a))
    (hcent : ∀ a' ∈ A, ((∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a))
    (hsm : GGStdSubSmallHyp 3 A a) {Q : Subgroup L'} (hQC : Q ≤ ggFix a)
    (hQn : ∀ c ∈ ggFix a, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q) (hQq : CFSG.IsQuasisimple Q)
    (h : (∃ a' ∈ A, a' ∉ Subgroup.zpowers a ∧ ∀ q ∈ Q, a' q = q) ∨
      ∃ E : Subgroup L', E ≤ Q ∧ IsElemAbelian 3 E ∧ (∀ a' ∈ A, ∀ e ∈ E, a' e = e) ∧
        (∀ e ∈ E, MulAut.conj e ∈ A) ∧ 3 ^ 3 ≤ Nat.card E) : False := by
  have hEQ : LargeEvenLayer (ggFix a) = Q :=
    layer_eq_of_isComponentOf (isComponentOf_of_normalized hQC hQn hQq) hcomp
  rcases h with ⟨a', ha', hna', hfix⟩ | ⟨E, hEQ', hEe, hEfix, hEA, hE27⟩
  · exact hna' ((hcent a' ha').mp (hEQ ▸ hfix))
  · have := hsm E hEe (hEQ ▸ hEQ') hEfix (Or.inl hEA)
    omega

end CFSG.StandardType.SpFin
