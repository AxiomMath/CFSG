module

public import CFSG.RankThree.GF2n.Stroth80.DictModel

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {γ : G → K}

theorem exists_symplectic_frame (M₀ : Tim79.QuadModel QF V K γ) (Y : Submodule K M₀.E)
    (hY : Y ⊓ M₀.B.orthogonal Y = ⊥) (hdim : Module.finrank K Y = 4)
    {w v : M₀.E} (hw : w ∈ Y) (hv : v ∈ Y) (hw0 : w ≠ 0) (hwv : M₀.B w v = 0)
    (hind : ∀ c : K, v ≠ c • w) :
    ∃ a b' : M₀.E, a ∈ Y ∧ b' ∈ Y ∧ M₀.B w a = 1 ∧ M₀.B v b' = 1 ∧ M₀.B a v = 0 ∧
      M₀.B w b' = 0 ∧ M₀.B a b' = 0 ∧ Y = Submodule.span K {w, v, a, b'} := by
  have hc : ∀ x y : M₀.E, M₀.B x y = -M₀.B y x := fun x y =>
    CFSG.RankThree.GF2n.Tim79.QuadModel.B_comm x y
  have hnd : ∀ y ∈ Y, (∀ z ∈ Y, M₀.B y z = 0) → y = 0 := by
    intro y hy h
    have hyO : y ∈ M₀.B.orthogonal Y := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      rw [hc n y, h n hn, neg_zero]
    have hmem : y ∈ Y ⊓ M₀.B.orthogonal Y := ⟨hy, hyO⟩
    rw [hY, Submodule.mem_bot] at hmem
    exact hmem
  obtain ⟨y₁, hy₁, hBy₁⟩ : ∃ y₁ ∈ Y, M₀.B w y₁ = 1 := by
    have hex : ∃ y ∈ Y, M₀.B w y ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hw0 (hnd w hw hcon)
    obtain ⟨y₀, hy₀, hne⟩ := hex
    exact ⟨(M₀.B w y₀)⁻¹ • y₀, Y.smul_mem _ hy₀,
      by simp only [map_smul, smul_eq_mul, inv_mul_cancel₀ hne]⟩
  obtain ⟨z₁, hz₁, hBwz₁, hBvz₁⟩ : ∃ z ∈ Y, M₀.B w z = 0 ∧ M₀.B v z = 1 := by
    have hz : ∃ z ∈ Y, M₀.B w z = 0 ∧ M₀.B v z ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hdec : ∀ y ∈ Y, M₀.B v y = M₀.B v y₁ * M₀.B w y := by
        intro y hy
        have hy' : y - M₀.B w y • y₁ ∈ Y := Y.sub_mem hy (Y.smul_mem _ hy₁)
        have h1 : M₀.B w (y - M₀.B w y • y₁) = 0 := by
          simp only [map_sub, map_smul, smul_eq_mul, hBy₁, mul_one, sub_self]
        have h2 := hcon _ hy' h1
        simp only [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h2
        linear_combination h2
      have hu : v - M₀.B v y₁ • w ∈ Y := Y.sub_mem hv (Y.smul_mem _ hw)
      have hu0 : v - M₀.B v y₁ • w = 0 := by
        apply hnd _ hu
        intro n hn
        simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
          hdec n hn, sub_self]
      exact hind _ (sub_eq_zero.mp hu0)
    obtain ⟨z, hzY, hBwz, hBvz⟩ := hz
    exact ⟨(M₀.B v z)⁻¹ • z, Y.smul_mem _ hzY,
      by simp only [map_smul, smul_eq_mul, hBwz, mul_zero],
      by simp only [map_smul, smul_eq_mul, inv_mul_cancel₀ hBvz]⟩
  have hsurj : ∀ s t : K, ∃ y ∈ Y, M₀.B w y = s ∧ M₀.B v y = t := by
    intro s t
    refine ⟨s • y₁ + (t - s * M₀.B v y₁) • z₁,
      Y.add_mem (Y.smul_mem _ hy₁) (Y.smul_mem _ hz₁), ?_, ?_⟩
    · simp only [map_add, map_smul, smul_eq_mul, hBy₁, hBwz₁, mul_one, mul_zero, add_zero]
    · simp only [map_add, map_smul, smul_eq_mul, hBvz₁, mul_one]
      ring
  obtain ⟨a, haY, hBwa, hBva⟩ := hsurj 1 0
  obtain ⟨b₀, hb₀Y, hBwb₀, hBvb₀⟩ := hsurj 0 1
  have hBvw : M₀.B v w = 0 := by rw [hc v w, hwv, neg_zero]
  have hBaw : M₀.B a w = -1 := by rw [hc a w, hBwa]
  have hBav : M₀.B a v = 0 := by rw [hc a v, hBva, neg_zero]
  obtain ⟨b', hbY, hBwb', hBvb', hBab'⟩ : ∃ b' ∈ Y, M₀.B w b' = 0 ∧ M₀.B v b' = 1 ∧
      M₀.B a b' = 0 := by
    refine ⟨b₀ + M₀.B a b₀ • w, Y.add_mem hb₀Y (Y.smul_mem _ hw), ?_, ?_, ?_⟩
    · simp only [map_add, map_smul, smul_eq_mul, M₀.alt w, mul_zero, add_zero, hBwb₀]
    · simp only [map_add, map_smul, smul_eq_mul, hBvb₀, hBvw, mul_zero, add_zero]
    · simp only [map_add, map_smul, smul_eq_mul, hBaw]
      ring
  have hBbw : M₀.B b' w = 0 := by rw [hc b' w, hBwb', neg_zero]
  have hBbv : M₀.B b' v = -1 := by rw [hc b' v, hBvb']
  have hBba : M₀.B b' a = 0 := by rw [hc b' a, hBab', neg_zero]
  have hli : LinearIndependent K ![w, v, a, b'] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : g 0 • w + g 1 • v + g 2 • a + g 3 • b' = 0 := by
      simpa [Fin.sum_univ_four] using hg
    have e1 := congrArg (fun x => M₀.B x a) hg'
    have e2 := congrArg (fun x => M₀.B x b') hg'
    have e3 := congrArg (fun x => M₀.B x w) hg'
    have e4 := congrArg (fun x => M₀.B x v) hg'
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      map_zero, LinearMap.zero_apply, hBwa, hBva, hBwb', hBvb', hBab', hBaw, hBav, hBbw,
      hBbv, hBba, hwv, hBvw, M₀.alt a, M₀.alt b', M₀.alt w, M₀.alt v] at e1 e2 e3 e4
    have h0 : g 0 = 0 := by linear_combination e1
    have h1 : g 1 = 0 := by linear_combination e2
    have h2 : g 2 = 0 := by linear_combination -e3
    have h3 : g 3 = 0 := by linear_combination -e4
    intro i
    fin_cases i <;> simp [h0, h1, h2, h3]
  have hrange : Set.range ![w, v, a, b'] = ({w, v, a, b'} : Set M₀.E) := by
    ext x
    simp <;> tauto
  have hfr : Module.finrank K (Submodule.span K (Set.range ![w, v, a, b'])) = 4 := by
    rw [finrank_span_eq_card hli]
    simp
  have hle : Submodule.span K (Set.range ![w, v, a, b']) ≤ Y := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> simp [haY, hbY, hw, hv]
  have heq : Submodule.span K (Set.range ![w, v, a, b']) = Y :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hfr, hdim])
  refine ⟨a, b', haY, hbY, hBwa, hBvb', hBav, hBwb', hBab', ?_⟩
  rw [hrange] at heq
  exact heq.symm

end CFSG.RankThree.GF2n.Stroth80
