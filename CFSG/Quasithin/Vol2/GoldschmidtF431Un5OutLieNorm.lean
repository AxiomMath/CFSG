module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieAut
public import CFSG.Quasithin.Vol2.GoldschmidtF431AGLie
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamilies

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL5

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.Unit CFSG.Quasithin.H13.F431.Un
  CFSG.Quasithin CFSG.QuasithinUnique

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem Ssd5_bot_eq_Uh : Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) ⊥ = Uh h := by
  rw [Uh_eq_map]
  ext α
  constructor
  · rintro ⟨s, hs, φ, hφ, rfl⟩
    rw [Subgroup.mem_bot.1 hφ, fa5_one, mul_one]
    exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, 1, one_mem _, by rw [fa5_one, mul_one]⟩

include h in
theorem isSylowTwoOf_Uh : IsSylowTwoOf (Uh h) (Pi h) := by
  have := h.finite
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  have hZ := u5_center_eq_bot h
  have := AG.isSylowTwoOf_map_range (MulAut.conj : hypPSU h 2 1 →* MulAut (hypPSU h 2 1))
    (CFSG.RankThree.PartOne.U5K.Hyp.conj_injective hZ) (u5_sylow h)
  rw [Uh_eq_map, Pi_eq_map, ← MonoidHom.range_eq_map]
  exact this

include h in
theorem exists_normalized5 (hf : f = 2) {K' : Subgroup (MulAut (hypPSU h 2 1))}
    (hinn : Pi h ≤ K') :
    ∃ g ∈ autStab (hypProjUnitriangular h 2 1), ∃ F₂ : Subgroup (K ≃+* K),
      IsSylowTwoOf (Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂)
        (K'.map (MulAut.conj g).toMonoidHom) := by
  have := h.finite
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  have : Finite (MulAut (hypPSU h 2 1)) := finite_mulAut_hyp h
  have hZ := u5_center_eq_bot h
  set U := hypProjUnitriangular h 2 1 with hU
  have hUh_le : Uh h ≤ K' := Uh_le_Pi.trans hinn
  have hUhQ : Uh h ≤ Q5 h := by
    rw [← Ssd5_bot_eq_Uh h]
    exact Ssd5_mono h le_rfl bot_le
  have hUh2 : IsPGroup 2 (Uh h) := (isPGroup_Q5 h hf).to_le hUhQ
  obtain ⟨T, hUT, hT⟩ := exists_isSylowTwoOf_of_le hUh_le hUh2
  have hTPi : T ⊓ Pi h = Uh h :=
    (isSylowTwoOf_Uh h).eq_of_le (le_inf hUT Uh_le_Pi) inf_le_right
      (hT.isPGroup.to_le inf_le_left)
  have hTU : ∀ α ∈ T, ∀ x ∈ U, α x ∈ U := by
    intro α hα x hx
    have h1 : cj5 h x ∈ Uh h := by
      rw [Uh_eq_map]
      exact ⟨x, hx, rfl⟩
    have h2 : α * cj5 h x * α⁻¹ ∈ T := T.mul_mem (T.mul_mem hα (hUT h1)) (T.inv_mem hα)
    have h3 : α * cj5 h x * α⁻¹ ∈ Pi h :=
      (inferInstance : (Pi h).Normal).conj_mem _ (Uh_le_Pi h1) α
    rw [aut5_mul_cj5_mul_inv] at h2 h3
    have h4 : cj5 h (α x) ∈ Uh h := hTPi ▸ ⟨h2, h3⟩
    rw [Uh_eq_map] at h4
    obtain ⟨y, hy, hyx⟩ := h4
    have : y = α x := CFSG.RankThree.PartOne.U5K.Hyp.conj_injective hZ hyx
    exact this ▸ hy
  have hTstab : T ≤ autStab U := fun α hα x => by
    refine ⟨hTU α hα x, fun hx => ?_⟩
    have := hTU α⁻¹ (T.inv_mem hα) (α x) hx
    simpa using this
  obtain ⟨g₀, hg₀, hconj⟩ := exists_conj_into_Q5 h hf hT.isPGroup hTstab
  have hg : g₀⁻¹ ∈ autStab U := (autStab U).inv_mem hg₀
  set g : MulAut (hypPSU h 2 1) := g₀⁻¹ with hgdef
  set T' : Subgroup (MulAut (hypPSU h 2 1)) := T.map (MulAut.conj g).toMonoidHom with hT'
  have hmemT' : ∀ y, y ∈ T' ↔ g⁻¹ * y * g ∈ T := fun y => by
    rw [hT', Subgroup.mem_map_equiv]
    rfl
  have hT'Q : ∀ y ∈ T', y ∈ Q5 h := by
    intro y hy
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    have := hconj y₀ hy₀
    simpa [hgdef, MulAut.conj_apply] using this
  have hUh_T' : Uh h ≤ T' := by
    intro α hα
    rw [Uh_eq_map] at hα
    obtain ⟨s, hs, rfl⟩ := hα
    rw [hmemT']
    have hs' : g⁻¹ s ∈ U := ((autStab U).inv_mem hg s).1 hs
    have e : g⁻¹ * cj5 h s * g = cj5 h (g⁻¹ s) := by
      have := aut5_mul_cj5_mul_inv h g⁻¹ s
      rwa [inv_inv] at this
    rw [e]
    exact hUT (by rw [Uh_eq_map]; exact ⟨_, hs', rfl⟩)
  set F₂ : Subgroup (K ≃+* K) := T'.comap (fieldP h) with hF₂
  have hT'eq : T' = Ssd5 h U (fStab5_U h) F₂ := by
    ext α
    constructor
    · intro hα
      have hαQ : α ∈ Ssd5 h U (fStab5_U h) ⊤ := hT'Q α hα
      obtain ⟨s, hs, φ, -, rfl⟩ := hαQ
      have hcs : cj5 h s ∈ T' := hUh_T' (by rw [Uh_eq_map]; exact ⟨s, hs, rfl⟩)
      have : fa5 h φ ∈ T' := by
        have := T'.mul_mem (T'.inv_mem hcs) hα
        simpa using this
      exact ⟨s, hs, φ, this, rfl⟩
    · rintro ⟨s, hs, φ, hφ, rfl⟩
      have hcs : cj5 h s ∈ T' := hUh_T' (by rw [Uh_eq_map]; exact ⟨s, hs, rfl⟩)
      exact T'.mul_mem hcs hφ
  refine ⟨g, hg, F₂, ?_⟩
  rw [← hT'eq]
  exact IsSylowTwoOf.map_equiv (MulAut.conj g) hT

end CFSG.Quasithin.H13.F431.Un.OL5
