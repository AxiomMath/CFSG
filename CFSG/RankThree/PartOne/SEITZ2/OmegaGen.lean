module

public import CFSG.RankThree.PartOne.SEITZ2.OmegaCore

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

section Gen

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {b c : K}

theorem elementaryGroup_le_closure_ts [CharP K 2] (F : OmegaFrame Q b c)
    (hQnd : (polarBilin Q).Nondegenerate) :
    elementaryGroup Q ≤ Subgroup.closure {Y | ∃ u w, Q u = 0 ∧ Q w = 0 ∧ polar Q u w = 0 ∧
      eichler Q u w = Y} := by
  set M := Subgroup.closure {Y | ∃ u w, Q u = 0 ∧ Q w = 0 ∧ polar Q u w = 0 ∧
    eichler Q u w = Y} with hMdef
  have hgen : ∀ u w, Q u = 0 → Q w = 0 → polar Q u w = 0 → eichler Q u w ∈ M :=
    fun u w hu hw huw => Subgroup.subset_closure ⟨u, w, hu, hw, huw, rfl⟩
  have hMO : M ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [hMdef, Subgroup.closure_le]
    rintro _ ⟨u, w, -, -, -, rfl⟩
    exact eichler_mem_orthogonalGroup Q u w
  have hsing : ∀ (a : V) (j : Fin 6) (t : K), Q a = 0 → polar Q a (F.six j) = 0 →
      eichler Q a (t • F.six j) ∈ M := fun a j t ha haj =>
    hgen a _ ha (by rw [map_smul_eq_sq, F.six_Q, mul_zero])
      (by rw [polar_smul_right_eq, haj, mul_zero])
  have he00 : F.e 0 ≠ 0 := fun h0 => by
    have := F.polar_ef 0 0
    rw [h0, polar_zero_left] at this
    simp at this
  have hf00 : F.f 0 ≠ 0 := fun h0 => by
    have := F.polar_ef 0 0
    rw [h0, polar_zero_right] at this
    simp at this
  have he0 : IsRootCenter Q M (F.e 0) :=
    isRootCenter_of_span6 he00 (F.Q_e 0) F.six F.polar_e0_six
      (fun j t => hsing _ j t (F.Q_e 0) (F.polar_e0_six j)) F.perp_decomp_e0
  have hf0 : IsRootCenter Q M (F.f 0) :=
    isRootCenter_of_span6 hf00 (F.Q_f 0) F.six F.polar_f0_six
      (fun j t => hsing _ j t (F.Q_f 0) (F.polar_f0_six j)) F.perp_decomp_f0
  exact elementaryGroup_le_of_hypPair hQnd hMO
    ⟨F.e 0, F.f 0, F.Q_e 0, F.Q_f 0, by simpa using F.polar_ef 0 0⟩ he0 hf0

@[expose] def OmegaFrame.hyp (F : OmegaFrame Q b c) (i : Fin 3) : HypPair Q :=
  ⟨F.e i, F.f i, F.Q_e i, F.Q_f i, by simpa using F.polar_ef i i⟩

theorem OmegaFrame.hyp_orth (F : OmegaFrame Q b c) {i j : Fin 3} (h : i ≠ j) :
    (F.hyp i).Orth (F.hyp j) where
  ee := F.polar_ee i j
  ef := by simp [OmegaFrame.hyp, F.polar_ef, h]
  fe := by simp [OmegaFrame.hyp, F.polar_fe, h.symm]
  ff := F.polar_ff i j

theorem exists_mem_elementaryGroup_normal_form (hQ : (polarBilin Q).Nondegenerate)
    {P₀ P₁ P₂ : HypPair Q} (h₀₁ : P₀.Orth P₁) (h₀₂ : P₀.Orth P₂) (h₁₂ : P₁.Orth P₂) {x y : V}
    (hx : Q x = 0) (hy : Q y = 0) (hxy : polar Q x y = 0) (hx0 : x ≠ 0)
    (hya : ∀ a : K, y ≠ a • x) :
    ∃ g ∈ elementaryGroup Q, g x = P₀.e ∧ ∃ a : K, g y = a • P₀.e + P₁.e := by
  obtain ⟨g₁, hg₁, hg₁x⟩ := exists_mem_elementaryGroup_apply_eq hQ h₀₁ hx0 P₀.e_ne_zero
    (by rw [hx, P₀.Q_e])
  have hg₁O := elementaryGroup_le_orthogonalGroup Q hg₁
  obtain ⟨y₁, hy₁def⟩ : ∃ y₁, y₁ = g₁ y := ⟨_, rfl⟩
  have hy₁Q : Q y₁ = 0 := by rw [hy₁def, map_of_mem hg₁O, hy]
  have hy₁e : polar Q y₁ P₀.e = 0 := by
    rw [hy₁def, ← hg₁x, polar_map_of_mem hg₁O, polar_comm, hxy]
  obtain ⟨a, hadef⟩ : ∃ a, a = polar Q y₁ P₀.f := ⟨_, rfl⟩
  obtain ⟨w, hwdef⟩ : ∃ w, w = P₀.proj y₁ := ⟨_, rfl⟩
  have hw_mem : w ∈ P₀.perp := hwdef ▸ P₀.proj_mem_perp y₁
  have hw_perp := HypPair.mem_perp.mp hw_mem
  have hy₁eq : y₁ = a • P₀.e + w := by
    have := P₀.eq_add_proj y₁
    rw [hy₁e, zero_smul, add_zero, ← hadef, ← hwdef] at this
    exact this
  have hwQ : Q w = 0 := by
    have h1 := hy₁Q
    rw [hy₁eq, QuadraticMap.map_add Q, map_smul_eq_sq, P₀.Q_e, polar_smul_left_eq,
      hw_perp.1] at h1
    linear_combination h1
  have hw0 : w ≠ 0 := by
    intro h0
    apply hya a
    apply g₁.injective
    rw [← hy₁def, hy₁eq, h0, add_zero, map_smul, hg₁x]
  have hW := P₀.polarNondegOn_perp hQ
  have hmem : ∀ {P : HypPair Q}, P₀.Orth P → P.e ∈ P₀.perp ∧ P.f ∈ P₀.perp := fun {P} h =>
    ⟨HypPair.mem_perp.mpr ⟨h.ee, h.fe⟩, HypPair.mem_perp.mpr ⟨h.ef, h.ff⟩⟩
  obtain ⟨g₂, hg₂, hg₂w, -, hg₂fix⟩ := exists_mem_elementaryGroup_apply_eq_of_mem hW h₁₂
    (hmem h₀₁).1 (hmem h₀₁).2 (hmem h₀₂).1 (hmem h₀₂).2 hw_mem (hmem h₀₁).1 hw0 P₁.e_ne_zero
    (by rw [hwQ, P₁.Q_e])
  have hg₂e : g₂ P₀.e = P₀.e := hg₂fix P₀.e fun v hv => (HypPair.mem_perp.mp hv).1
  refine ⟨g₂ * g₁, Subgroup.mul_mem _ hg₂ hg₁, ?_, a, ?_⟩
  · rw [LinearEquiv.mul_apply, hg₁x, hg₂e]
  · rw [LinearEquiv.mul_apply, ← hy₁def, hy₁eq, map_add, map_smul, hg₂e, hg₂w]

theorem OmegaFrame.exists_normal_form (F : OmegaFrame Q b c)
    (hQ : (polarBilin Q).Nondegenerate) {x y : V} (hx : Q x = 0) (hy : Q y = 0)
    (hxy : polar Q x y = 0) (hx0 : x ≠ 0) (hya : ∀ a : K, y ≠ a • x) :
    ∃ g ∈ elementaryGroup Q, g x = F.e 0 ∧ ∃ a : K, g y = a • F.e 0 + F.e 1 :=
  exists_mem_elementaryGroup_normal_form hQ (P₀ := F.hyp 0) (P₁ := F.hyp 1) (P₂ := F.hyp 2)
    (F.hyp_orth (by decide)) (F.hyp_orth (by decide)) (F.hyp_orth (by decide)) hx hy hxy hx0 hya

end Gen

end CFSG.RankThree.PartOne.SEITZ2
