module

public import CFSG.OddTranspositions.PartThree.Twelve.FiveChart
public import CFSG.OddTranspositions.PartThree.Twelve.NineAxis
import CFSG.OddTranspositions.PartThree.Twelve.NineCenter
import CFSG.OddTranspositions.PartThree.Twelve.SevenFive
import CFSG.OddTranspositions.PartThree.Twelve.Seven

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open CFSG.Fischer

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem isHypLineSpace_of_pivot (hS : Asc72.Setup G D) {d : G} (hd : d ∈ D)
    (h : ∀ b ∈ D, ¬ Commute b d → ∀ c ∈ lineMem D d b, c ≠ d →
      ¬ Commute c d ∧ lineMem D d c = lineMem D d b) :
    IsHypLineSpace D := by
  intro a ha b hb hba c hc hca
  obtain ⟨g, hg⟩ := isConj_iff.mp (hS.isConj hd ha)
  let b' : G := g⁻¹ * b * g
  let c' : G := g⁻¹ * c * g
  have hb'g : g * b' * g⁻¹ = b := by
    show g * (g⁻¹ * b * g) * g⁻¹ = b
    group
  have hc'g : g * c' * g⁻¹ = c := by
    show g * (g⁻¹ * c * g) * g⁻¹ = c
    group
  have hline : ∀ e : G, lineMem D a (g * e * g⁻¹) = (MulAut.conj g) '' lineMem D d e := by
    intro e
    have hh := lineMem_conj (E := D) (fun g' z hz => hS.conj_mem g' hz) g d e
    rwa [hg] at hh
  have hline_a_b : lineMem D a b = (MulAut.conj g) '' lineMem D d b' := by
    rw [← hb'g]; exact hline b'
  have hline_a_c : lineMem D a c = (MulAut.conj g) '' lineMem D d c' := by
    rw [← hc'g]; exact hline c'
  have hc'line : c' ∈ lineMem D d b' := by
    have hcimg : (MulAut.conj g) c' ∈ (MulAut.conj g) '' lineMem D d b' := by
      rw [← hline_a_b]
      simpa only [MulAut.conj_apply, hc'g] using hc
    obtain ⟨y, hy, hyeq⟩ := hcimg
    rwa [(MulAut.conj g).injective hyeq] at hy
  have hb'd : ¬ Commute b' d := fun hcomm => hba (by
    have h' : Commute (g * b' * g⁻¹) (g * d * g⁻¹) := (Commute.conj_iff g).mpr hcomm
    rwa [hb'g, hg] at h')
  have hc'd : c' ≠ d := fun hceq => hca (by rw [← hc'g, hceq, hg])
  have hb'D : b' ∈ D := by simpa [b'] using hS.conj_mem g⁻¹ hb
  obtain ⟨hnc', hline'⟩ := h b' hb'D hb'd c' hc'line hc'd
  refine ⟨fun hcomm => hnc' ((Commute.conj_iff g).mp (by rwa [← hc'g, ← hg] at hcomm)), ?_⟩
  rw [hline_a_c, hline_a_b, hline']

theorem isHypLineSpace_five (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d}) {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    (h5 : IsFiveReflectionModel k ε π (imageClass hC))
    (hdiam : ∀ w ∈ D, ¬ Commute w hC.d → (commSet D hC.d ∩ commSet D w).Nonempty) :
    IsHypLineSpace D :=
  isHypLineSpace_of_pivot hC.setup hC.hd fun w hw hwd c hc hcne => by
    obtain ⟨v, hv_d, hv_w⟩ := hdiam w hw hwd
    have hvD : v ∈ D := hv_d.1
    have hdv : hC.d ∈ commSet D v :=
      ⟨hC.hd, hv_d.2.1.symm, fun h => hv_d.2.2 h.symm⟩
    have hwv : w ∈ commSet D v :=
      ⟨hw, hv_w.2.1.symm, fun h => hv_w.2.2 h.symm⟩
    have hdw : ¬ Commute hC.d w := fun h => hwd h.symm
    exact (lineMem_five hC hMZ hα hk h5 hvD hdv hwv hdw).2.2 c hc hcne

theorem twelveNine_five (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d}) {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    (h5 : IsFiveReflectionModel k ε π (imageClass hC))
    (hdiam : ∀ w ∈ D, ¬ Commute w hC.d → (commSet D hC.d ∩ commSet D w).Nonempty) (u : D)
    (σ : commGraph D ≃g commGraph D) (hσ : ∀ v : D, Commute (v : G) u → σ v = v) :
    (∀ v : D, σ v = v) ∨ ∀ v : D, (σ v : G) = (u : G) * v * u := by
  obtain ⟨⟨w₁, hw₁, hw₁d, hl₁⟩, ⟨w₂, hw₂, hw₂d, hl₂⟩⟩ :=
    twelveSeven_five_exists hC hMZ hα hk h5
  have hgcd : Nat.gcd ((lineMem D hC.d w₁).ncard - 1) ((lineMem D hC.d w₂).ncard - 1) ∣ 2 := by
    rw [hl₁, hl₂]
    decide
  exact twelveNine_forall hC.setup (isHypLineSpace_five hC hMZ hα hk h5 hdiam)
    (fun a ha b hb h => eq_of_commSet_eq hC hα ha hb h) hC.hd hw₁ hw₂ hw₁d hw₂d hgcd u σ hσ

end CFSG.OddTranspositions.PartThree
