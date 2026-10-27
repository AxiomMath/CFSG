module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitG2Cert
public import CFSG.Quasithin.Vol2.Ch3Sec3CZL32

public section

namespace CFSG.Quasithin.H13.Ins314

open CFSG.Quasithin CFSG.Quasithin.H13.CZL32

@[expose, irreducible] def S0 (g : L3.Γ) : Finset L3.Vec :=
  (Finset.univ.filter fun b : L3.Γ => L3.act b e1 = e1 ∧ ∀ w, w ∈ P12 ↔ L3.act b w ∈ P12).biUnion
    fun b => Finset.univ.image fun w : L3.Vec => L3.act (b * g * b⁻¹) w - w

@[expose, irreducible] def spanStep (S F : Finset L3.Vec) : Finset L3.Vec :=
  F ∪ F.biUnion fun a => S.image (a + ·)

set_option maxRecDepth 100000 in
theorem fl_check : ∀ g : L3.Γ, g ^ 3 = 1 → g ≠ 1 → ∀ u : L3.Vec, u ≠ 0 →
    (∀ b : L3.Γ, (L3.act b e1 = e1 ∧ ∀ w, w ∈ P12 ↔ L3.act b w ∈ P12) →
      L3.act (b * g * b⁻¹) u = u) →
    spanStep (S0 g) (spanStep (S0 g) (spanStep (S0 g) {0})) = Finset.univ := by
  decide +kernel

theorem mem_S0 {g : L3.Γ} {s : L3.Vec} :
    s ∈ S0 g ↔ ∃ b : L3.Γ, (L3.act b e1 = e1 ∧ ∀ w, w ∈ P12 ↔ L3.act b w ∈ P12) ∧
      ∃ w : L3.Vec, L3.act (b * g * b⁻¹) w - w = s := by
  unfold S0
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]

theorem spanStep_induction {S F : Finset L3.Vec} {P : L3.Vec → Prop}
    (hS : ∀ s ∈ S, ∀ a, P a → P (a + s)) (hF : ∀ f ∈ F, P f) :
    ∀ v ∈ spanStep S F, P v := by
  intro v hv
  unfold spanStep at hv
  rcases Finset.mem_union.mp hv with h | h
  · exact hF v h
  · obtain ⟨a, ha, hv'⟩ := Finset.mem_biUnion.mp h
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hv'
    exact hS s hs a (hF a ha)

end CFSG.Quasithin.H13.Ins314
