module

public import CFSG.Timmesfeld.Transvection.QTwoFischer
public import CFSG.Timmesfeld.Transvection.QTwoThin
public import CFSG.Timmesfeld.Transvection.QTwoR3
public import CFSG.Timmesfeld.Transvection.QTwoSp
public import CFSG.Timmesfeld.Transvection.QTwoSU
public import CFSG.Fischer.Classification.Final
public import CFSG.Fischer.Classification.PartII.O2G.ThreeFinal

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Fischer.Classification

theorem transvectionConclusion_of_card_two {H : Type} [Group H] {Δ : Set (Subgroup H)}
    (h : TransvectionHyp H Δ) {A : Subgroup H} (hA : A ∈ Δ) (h2 : Nat.card A = 2) :
    TransvectionConclusion H Δ 1 le_rfl := by
  have hQ := QTwo.qHyp_rootElts h hA h2
  have hcard : ∀ X ∈ Δ, Nat.card X = 2 := fun X hX => QTwo.card_eq_two h.cls hA h2 hX
  have hΔ := QTwo.mem_iff_exists_zpowers h.cls hcard
  obtain ⟨a, haA, ha1⟩ := h.cls.root.exists_ne_one hA
  have ha : a ∈ rootElts Δ := ⟨A, hA, haA, ha1⟩
  have hD : ∀ x ∈ rootElts Δ, ∀ y, IsConj x y ↔ y ∈ rootElts Δ := fun x hx y => by
    rw [QTwo.rootElts_eq_isConj h.cls hcard hx]
    rfl
  unfold TransvectionConclusion
  rcases statement_of_twinFour o2TwinFourInput H (rootElts Δ) hQ.hyp with hcl | ⟨k, hk⟩
  · rcases hcl with ⟨m, -, φ, hφ⟩ | ⟨m, hm, b, halt, hnd, φ, hφ⟩ | ⟨m, -, Q, hnd, -, hmod⟩ |
      ⟨m, hm, hmod⟩ | ⟨m, hm, f, hsymm, hnd, hmod⟩
    ·
      obtain rfl := QTwo.eq_six_of_perm hQ φ hφ
      obtain ⟨ψ, hψ⟩ := QTwo.exists_sympEquiv_of_perm_six φ hφ
      exact Or.inl (QTwo.spConclusion hΔ hD le_rfl ψ hψ)
    ·
      obtain ⟨ψ, hψ⟩ := QTwo.exists_sympEquiv_of_isometry b halt hnd φ hφ
      exact Or.inl (QTwo.spConclusion hΔ hD hm ψ (hψ _))
    ·
      exact (QTwo.false_of_orthogonal hQ hnd hmod).elim
    ·
      obtain ⟨ψ, hψ⟩ := fischerCentralQuotientModel_iff_U2.1 hmod
      exact Or.inr (QTwo.suConclusion hΔ hD hm ψ hψ)
    ·
      obtain ⟨φ, hφ⟩ := (fischerCentralQuotientModel_iff (rootElts Δ)).1 hmod
      have hf : IsF3Form f := ⟨hsymm, hnd⟩
      rcases Nat.lt_or_ge m 6 with h6 | h6
      · obtain rfl : m = 5 := by omega
        obtain ⟨ψ, hψ⟩ := QTwo.exists_mulEquiv_U2_four_of_R3_five hQ hf φ hφ
        exact Or.inr (QTwo.suConclusion hΔ hD le_rfl ψ hψ)
      · exact (QTwo.false_of_R3_six_le hQ hf h6 φ hφ).elim
  · exact (QTwo.not_hasType hQ k hk).elim

end CFSG.Timmesfeld.Transvection
