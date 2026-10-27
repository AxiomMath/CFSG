module

public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.Quasithin.H13.F431.Un.OL

open CFSG.Quasithin
open scoped commutatorElement

section PerfectCore

variable {G : Type*} [Group G]

theorem derivedSeriesOf_succ_le {M N : Subgroup G} (hc : ⁅N, N⁆ ≤ M) (n : ℕ) :
    derivedSeriesOf N (n + 1) ≤ derivedSeriesOf M n := by
  induction n with
  | zero => exact hc
  | succ n ih =>
    rw [derivedSeriesOf_succ N (n + 1), derivedSeriesOf_succ M n]
    exact Subgroup.commutator_mono ih ih

theorem perfectCore_eq_of_commutator_le {M N : Subgroup G} (hMN : M ≤ N) (hc : ⁅N, N⁆ ≤ M) :
    perfectCore N = perfectCore M := by
  apply le_antisymm
  · exact le_iInf fun n =>
      (perfectCore_le_derivedSeriesOf N (n + 1)).trans (derivedSeriesOf_succ_le hc n)
  · exact perfectCore_mono hMN

end PerfectCore

section Sup

variable {G : Type*} [Group G]

theorem commutator_sup_le_of_comm {H I : Subgroup G} (hI : I ≤ Subgroup.normalizer (H : Set G))
    (hc : ∀ x ∈ I, ∀ y ∈ I, x * y = y * x) : ⁅H ⊔ I, H ⊔ I⁆ ≤ H := by
  have hM : H ⊔ I ≤ Subgroup.normalizer (H : Set G) := sup_le Subgroup.le_normalizer hI
  have hn : ∀ g ∈ H ⊔ I, ∀ x ∈ H, g * x * g⁻¹ ∈ H := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.1 (hM hg) x).1 hx
  have hn' : ∀ g ∈ H ⊔ I, ∀ x ∈ H, g⁻¹ * x * g ∈ H := fun g hg x hx => by
    simpa using hn g⁻¹ ((H ⊔ I).inv_mem hg) x hx
  have h2 : ∀ g ∈ H ⊔ I, (∀ y ∈ I, ⁅g, y⁆ ∈ H) → ∀ g' ∈ H ⊔ I, ⁅g, g'⁆ ∈ H := by
    intro g hg hgI
    let S : Subgroup G :=
      { carrier := {g' | g' ∈ H ⊔ I ∧ ⁅g, g'⁆ ∈ H}
        mul_mem' := fun {a b} ha hb => ⟨(H ⊔ I).mul_mem ha.1 hb.1, by
          have e : ⁅g, a * b⁆ = ⁅g, a⁆ * (a * ⁅g, b⁆ * a⁻¹) := by
            simp only [commutatorElement_def]; group
          rw [e]
          exact H.mul_mem ha.2 (hn a ha.1 _ hb.2)⟩
        one_mem' := ⟨(H ⊔ I).one_mem, by simp⟩
        inv_mem' := fun {a} ha => ⟨(H ⊔ I).inv_mem ha.1, by
          have e : ⁅g, a⁻¹⁆ = a⁻¹ * ⁅g, a⁆⁻¹ * a := by
            simp only [commutatorElement_def]; group
          rw [e]
          have := hn' a ha.1 _ (H.inv_mem ha.2)
          simpa [mul_assoc] using this⟩ }
    have hHS : H ≤ S := fun x hx => ⟨Subgroup.mem_sup_left hx, by
      have e : ⁅g, x⁆ = (g * x * g⁻¹) * x⁻¹ := by simp only [commutatorElement_def]
      rw [e]
      exact H.mul_mem (hn g hg x hx) (H.inv_mem hx)⟩
    have hIS : I ≤ S := fun y hy => ⟨Subgroup.mem_sup_right hy, hgI y hy⟩
    exact fun g' hg' => (sup_le hHS hIS hg').2
  let S : Subgroup G :=
    { carrier := {g | g ∈ H ⊔ I ∧ ∀ g' ∈ H ⊔ I, ⁅g, g'⁆ ∈ H}
      mul_mem' := fun {a b} ha hb => ⟨(H ⊔ I).mul_mem ha.1 hb.1, fun g' hg' => by
        have e : ⁅a * b, g'⁆ = a * ⁅b, g'⁆ * a⁻¹ * ⁅a, g'⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact H.mul_mem (hn a ha.1 _ (hb.2 g' hg')) (ha.2 g' hg')⟩
      one_mem' := ⟨(H ⊔ I).one_mem, fun g' _ => by simp⟩
      inv_mem' := fun {a} ha => ⟨(H ⊔ I).inv_mem ha.1, fun g' hg' => by
        have e : ⁅a⁻¹, g'⁆ = a⁻¹ * ⁅a, g'⁆⁻¹ * a := by
          simp only [commutatorElement_def]; group
        rw [e]
        have := hn' a ha.1 _ (H.inv_mem (ha.2 g' hg'))
        simpa [mul_assoc] using this⟩ }
  have hHS : H ≤ S := fun x hx => ⟨Subgroup.mem_sup_left hx, fun g' hg' => by
    have e : ⁅x, g'⁆ = x * (g' * x⁻¹ * g'⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact H.mul_mem hx (hn g' hg' _ (H.inv_mem hx))⟩
  have hIS : I ≤ S := fun y hy => ⟨Subgroup.mem_sup_right hy, fun g' hg' =>
    h2 y (Subgroup.mem_sup_right hy) (fun y' hy' => by
      rw [commutatorElement_def, hc y hy y' hy']; simp) g' hg'⟩
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  exact (sup_le hHS hIS hg₁).2 g₂ hg₂

end Sup

end CFSG.Quasithin.H13.F431.Un.OL
