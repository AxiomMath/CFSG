module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S27
public import CFSG.LocalAnalysis.UniquenessCase.UCR638b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ABGLocalTools
open CFSG.RankTwoShapes (IsAlperinSubgroup)

variable {G : Type} [Group G] [Finite G]

theorem uc22p22q_normalizer_le_of_inU {p : ℕ} (hp : p.Prime) {M X Q : Subgroup G}
    (hM : normalizer (M : Set G) = M) (hX : UC6.InU M X) (hXQ : X ≤ Q) (hQp : IsPGroup p Q) :
    normalizer (Q : Set G) ≤ M :=
  (UC6.InU.of_subnormal hM (UC6.isSubnormal_of_isPGroup hp hQp hXQ) hX).normalizer_le hM

theorem uc22p22q_fusion_control_of_central_inU {p : ℕ} [Fact p.Prime] {M X : Subgroup G}
    (hM : normalizer (M : Set G) = M) (S : Sylow p G) (hXS : X ≤ (S : Subgroup G))
    (hXz : ∀ x ∈ X, ∀ y ∈ (S : Subgroup G), x * y = y * x) (hXU : UC6.InU M X) :
    ∀ x ∈ (S : Subgroup G), ∀ g : G, g * x * g⁻¹ ∈ (S : Subgroup G) →
      ∃ c ∈ M, g * x * g⁻¹ = c⁻¹ * x * c := by
  intro x hx g hg
  refine UC6.fusion_control_of_alperin_uc6 S (fun Q hQ => ?_) hx hg
  have hQS : Q ≤ (S : Subgroup G) := hQ.1
  have hXQ : X ≤ Q := fun e he => by
    refine hQ.2.2.1 (Subgroup.mem_inf.2 ⟨?_, hXS he⟩)
    rw [mem_centralizer_iff]
    intro q hq
    exact (hXz e he q (hQS hq)).symm
  exact uc22p22q_normalizer_le_of_inU (Fact.out : p.Prime) hM hXU hXQ (S.isPGroup'.to_le hQS)

theorem uc22p22q_opRes_eq_of_central_inU (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    {p : ℕ} (hp : p.Prime) {M X : Subgroup G} (hM : normalizer (M : Set G) = M) (S : Sylow p G)
    (hSM : (S : Subgroup G) ≤ M) (hXS : X ≤ (S : Subgroup G))
    (hXz : ∀ x ∈ X, ∀ y ∈ (S : Subgroup G), x * y = y * x) (hXU : UC6.InU M X) :
    UC22.F10.OpRes p M = M := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hSc : (S : Subgroup G) ≤ ⁅M, M⁆ :=
    UC6.sylow_le_commutator_of_fusion_uc6 hG hnab S hSM
      (uc22p22q_fusion_control_of_central_inU hM S hXS hXz hXU)
  have hcomm : (commutator ↥M).map M.subtype = ⁅M, M⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  let SY : Sylow p ↥M := S.subtype hSM
  have hSY : (SY : Subgroup ↥M) ≤ commutator ↥M := by
    intro y hy
    rw [Sylow.coe_subtype] at hy
    obtain ⟨z, hz, hzy⟩ := (hcomm ▸ hSc) hy
    have : z = y := Subtype.ext hzy
    exact this ▸ hz
  have htop := UC6.oResidual_eq_top_of_sylow_le_commutator_uc6 SY hSY
  rw [UC6.opRes_eq_map_oResidual_uc6 hp, htop, Subgroup.map_top, Subgroup.range_subtype]

@[expose] def CentralInU (D : Data G) : Prop :=
  ∀ p ∈ D.sig2 ∪ D.sig3, ∃ P : Subgroup G, IsSylowOf p P D.M ∧ IsSylowOf p P ⊤ ∧
    ∃ X : Subgroup G, X ≤ P ∧ (∀ x ∈ X, ∀ y ∈ P, x * y = y * x) ∧ UC6.InU D.M X

theorem uc22p22q_r6_38_23_of_central (D : Data G) (hX : CentralInU D) : UC6.R6_38Sigma23 D := by
  intro p hp
  have hpσ : p ∈ D.sig := by
    rw [D.sig_sub]
    rcases hp with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hprime : p.Prime := (D.sig_prime p hpσ).1
  haveI : Fact p.Prime := ⟨hprime⟩
  obtain ⟨P, hP, hPtop, X, hXP, hXz, hXU⟩ := hX p hp
  obtain ⟨-, hPp, hPnd⟩ := isSylowOf_iff.1 hPtop
  let S : Sylow p G := hPp.toSylow (by simpa [Subgroup.relIndex_top_right] using hPnd)
  have hS : (S : Subgroup G) = P := rfl
  exact uc22p22q_opRes_eq_of_central_inU D.standing.simple D.standing.nonab hprime
    (UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal) S (hS ▸ hP.le) (hS ▸ hXP)
    (fun x hx y hy => hXz x hx y (hS ▸ hy)) hXU

end CFSG.LocalAnalysis.UniquenessCase.UC22
