module

public import CFSG.LocalAnalysis.StandardType.GGQ2InLCoverFrame
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalCatalogueU

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem not_q2_iso_A_two {r : ℕ} (hr : 2 ≤ r) :
    ¬ ∃ lab : LargeEvenLabel, GGLabQTwo 3 lab ∧ GGLabelIso lab ⟨.A, r, 2⟩ := by
  rintro ⟨⟨tag, rk, n⟩, hq, hiso⟩
  have hn : n < 2 := hq
  rcases hiso with h | ⟨_, h2, _, _⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨h1, _⟩
  · have h3 : n = 2 := congrArg LargeEvenLabel.n h
    omega
  · rcases h2 with h2 | h2 <;> cases h2
  · have h3 : (2 : ℕ) = n := congrArg LargeEvenLabel.n h2
    omega
  · have h3 := congrArg LargeEvenLabel.tag h2
    cases h3
  · have h3 := congrArg LargeEvenLabel.tag h2
    cases h3
  · have h3 := congrArg LargeEvenLabel.tag h2
    cases h3
  · have h3 : r = 1 := congrArg LargeEvenLabel.rank h2
    omega
  · have h3 := congrArg LargeEvenLabel.tag h1
    cases h3

theorem planeLin_noInternal {t : ℕ} (ε : Fin 2) (h4 : 4 ≤ t) (vx : PlaneRaw.V t) (hvx : vx ≠ 0)
    (ℓ : PlaneRaw.Code t) (hadm : PlaneRaw.admissible (.linear ε) ℓ)
    (hq : ∃ lab : LargeEvenLabel, GGLabQTwo 3 lab ∧
      GGLabelIso lab (PlaneRaw.label (.linear ε) ℓ))
    (hcent : PlaneRaw.cent (.linear ε) ℓ = Submodule.span (ZMod 3) {vx})
    (hin : vx ∈ PlaneRaw.inside (.linear ε) ℓ) : False := by
  rcases ℓ with S | e
  ·
    have hsub : PlaneRaw.vSupport vx ⊆ S := (PlaneRaw.mem_inside_zero (.linear ε) S vx).1 hin
    by_cases hS : ∃ i, i ∉ S
    · obtain ⟨i, hi⟩ := hS
      have hmem : (Pi.single i (1 : ZMod 3) : PlaneRaw.V t) ∈
          PlaneRaw.cent (.linear ε) (.zero S) := by
        rw [PlaneRaw.mem_cent_zero]
        intro i' hi'
        have : i' ≠ i := fun h => hi (h ▸ hi')
        simp [Pi.single_apply, this]
      have hmem' : (Pi.single i (1 : ZMod 3) : PlaneRaw.V t) ∈ Submodule.span (ZMod 3) {vx} := by
        rw [← hcent]
        exact hmem
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem'
      have h1 := congrFun hc i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same] at h1
      have hne : vx i ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at h1
        exact zero_ne_one h1
      exact hi (hsub ((PlaneRaw.mem_vSupport vx i).2 hne))
    · have hS : ∀ i, i ∈ S := fun i => by_contra fun h => hS ⟨i, h⟩
      have hmem : vx ∈ PlaneRaw.cent (.linear ε) (.zero S) := by
        rw [hcent]
        exact Submodule.mem_span_singleton_self vx
      rw [PlaneRaw.mem_cent_zero] at hmem
      exact hvx (funext fun i => hmem i (hS i))
  ·
    by_cases he : ∃ i, e i = 0
    · obtain ⟨i, hi⟩ := he
      have hmem : (Pi.single i (1 : ZMod 3) : PlaneRaw.V t) ∈
          PlaneRaw.cent (.linear ε) (.extension e) := by
        rw [PlaneRaw.mem_cent_extension]
        intro i1 h1 j1 h2
        have n1 : i1 ≠ i := fun h => (PlaneRaw.mem_extSupport e i1).1 h1 (h ▸ hi)
        have n2 : j1 ≠ i := fun h => (PlaneRaw.mem_extSupport e j1).1 h2 (h ▸ hi)
        simp [Pi.single_apply, n1, n2]
      have hmem' : (Pi.single i (1 : ZMod 3) : PlaneRaw.V t) ∈ Submodule.span (ZMod 3) {vx} := by
        rw [← hcent]
        exact hmem
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem'
      have h1 := congrFun hc i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same] at h1
      have hvi : vx i = 0 := ((PlaneRaw.mem_inside_extension (.linear ε) e vx).1 hin).1 i hi
      rw [hvi, mul_zero] at h1
      exact zero_ne_one h1
    · have he : ∀ i, e i ≠ 0 := fun i hi => he ⟨i, hi⟩
      have hsupp : PlaneRaw.Code.extSupport e = Finset.univ := by
        ext i
        simp [he i]
      have hlab : (PlaneRaw.label (.linear ε) (.extension e)) = ⟨.A, t - 1, 2⟩ := by
        simp [PlaneRaw.label, hsupp]
      exact not_q2_iso_A_two (r := t - 1) (by omega) (by rw [← hlab]; exact hq)

theorem inLLeafCases_lin (t : ℕ) (ε : Fin 2) : InLLeafCases (classicalCatalogue (.lin t ε)) := by
  show InLLeafCases (planeEntry (.linear ε) t)
  intro vx hvx ℓ hℓ hq _ hcent hin
  exact (planeLin_noInternal ε hℓ.1 vx hvx ℓ hℓ.2 hq hcent hin).elim

end CFSG.StandardType.GGQ2Frame

end
