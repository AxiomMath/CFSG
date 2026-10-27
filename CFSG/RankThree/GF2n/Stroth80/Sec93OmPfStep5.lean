module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.GF2n.Stroth80.Sec5Core
public import CFSG.RankThree.GF2n.Stroth80.Sec711Setup

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


theorem n12Lemma5_of_faith {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    (hc : Ctx M Q Z B) {t r : G} (ht : t ∈ LB M Q B) (hr : Sec7A hc t r)
    (hfaith : ∀ a ∈ Q ⊓ QB B, (∀ l ∈ (QB B ⊓ M) ⊓ hc.CN t, ⁅l, a⁆ ∈ Z) →
      a ∈ Vt M (LB M Q B) B Z t) :
    (∀ a ∈ QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t), (∀ x ∈ n12X hc t, ⁅x, a⁆ ∈ Z) →
      a ∈ Vt M (LB M Q B) B Z t) ∧
    (∀ a ∈ QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t),
      (∀ y ∈ n12Y hc t r, ⁅y, a⁆ ∈ Z) → a ∈ Vt M (LB M Q B) B Z t) := by
  have hrM : r ∈ M := hc.Rt_le_M t hr.mem
  have hrinv : r⁻¹ ∈ M := M.inv_mem hrM
  refine ⟨fun a ha hx => ?_, fun a ha hy => ?_⟩
  · obtain ⟨haB, haW⟩ := Subgroup.mem_inf.mp ha
    have haQ : a ∈ Q := (Subgroup.mem_inf.mp haW).1
    exact hfaith a (Subgroup.mem_inf.mpr ⟨haQ, haB⟩) fun l hl => by
      obtain ⟨hl1, hl2⟩ := Subgroup.mem_inf.mp hl
      exact hx l ⟨hl1, hl2⟩
  · obtain ⟨haB, haW⟩ := Subgroup.mem_inf.mp ha
    have haQ : a ∈ Q := (Subgroup.mem_inf.mp haW).1
    have ha'B : r⁻¹ * a * r ∈ QB B := by
      have h1 : a ∈ conjSubgroup r (QB B) := by rw [← QB_conj]; exact haB
      exact mem_conjSubgroup.mp h1
    have ha'Q : r⁻¹ * a * r ∈ Q := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hrinv) a).mp haQ
      rwa [inv_inv] at h1
    have hcond : ∀ l ∈ (QB B ⊓ M) ⊓ hc.CN t, ⁅l, r⁻¹ * a * r⁆ ∈ Z := by
      intro l hl
      obtain ⟨hl1, hl2⟩ := Subgroup.mem_inf.mp hl
      have hy1 : r * l * r⁻¹ ∈ QB (conjSubgroup r B) := by
        rw [QB_conj, mem_conjSubgroup]
        have e : r⁻¹ * (r * l * r⁻¹) * r = l := by group
        rw [e]
        exact hl1.1
      have hy2 : r * l * r⁻¹ ∈ M := M.mul_mem (M.mul_mem hrM hl1.2) hrinv
      have hy3 : r * l * r⁻¹ ∈ hc.CN t := hc.CN_conj_mem ht hr.mem hl2
      have h1 := hy (r * l * r⁻¹) ⟨Subgroup.mem_inf.mpr ⟨hy1, hy2⟩, hy3⟩
      have h2 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hrinv) _).mp h1
      have e : ⁅l, r⁻¹ * a * r⁆ = r⁻¹ * ⁅r * l * r⁻¹, a⁆ * r⁻¹⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact h2
    have hV := hfaith (r⁻¹ * a * r) (Subgroup.mem_inf.mpr ⟨ha'Q, ha'B⟩) hcond
    have hnorm := hc.Rt_normalizes_Vt ht hr.mem
    have h3 := (Subgroup.mem_normalizer_iff.mp hnorm (r⁻¹ * a * r)).mp hV
    have e : r * (r⁻¹ * a * r) * r⁻¹ = a := by group
    rwa [e] at h3

end CFSG.RankThree.GF2n.Stroth80
