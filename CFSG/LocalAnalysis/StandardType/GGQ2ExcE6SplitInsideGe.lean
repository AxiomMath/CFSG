module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitWeyl

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.QTwoCav
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.LangRat

open scoped commutatorElement

noncomputable section


variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup .E6 L p}
  {T₀ : Subgroup (ModGL .E6 L)}

omit
  [IsAlgClosed L] in
private theorem e6SplitWeyl_mem_rootSpan_of_mem {c : Finset (ExcRaw.Root 1)}
    {i : ExcRaw.Root 1} (hi : i ∈ c) :
    e6SplitWeyl L i ∈ rootSpan .E6 L (e6SplitCodeRoots c) := by
  have hsub : ({e6SplitRoot i, -e6SplitRoot i} : Set (Fin Tag.E6.rank → ℤ)) ⊆
      e6SplitCodeRoots c := by
    intro δ hδ
    rcases hδ with rfl | rfl
    · exact ⟨i, hi, Or.inl rfl⟩
    · exact ⟨i, hi, Or.inr (Or.inl rfl)⟩
  have hsubσ : ({permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i),
      -permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i)} :
      Set (Fin Tag.E6.rank → ℤ)) ⊆ e6SplitCodeRoots c := by
    intro δ hδ
    rcases hδ with rfl | rfl
    · exact ⟨i, hi, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨i, hi, Or.inr (Or.inr (Or.inr rfl))⟩
  by_cases hfix : ExcRaw.tabFix1.getD i.val false = true
  · rw [e6SplitWeyl, if_pos hfix]
    exact rootSpan_mono hsub (rootSL2_mem_rootSpan_pair (isRoot_e6SplitRoot i) WSL)
  · rw [e6SplitWeyl, if_neg hfix]
    exact mul_mem (rootSpan_mono hsub
        (rootSL2_mem_rootSpan_pair (isRoot_e6SplitRoot i) WSL))
      (rootSpan_mono hsubσ
        (rootSL2_mem_rootSpan_pair (isRoot_permLattice_e6SplitRoot i) WSL))

omit
  [IsAlgClosed L] in
private theorem rootDiagUnit_e6RelCoroot_mem_rootSpan (ζ : Lˣ)
    {c : Finset (ExcRaw.Root 1)} {i : ExcRaw.Root 1} (hi : i ∈ c) :
    rootDiagUnit .E6 (fun j => ζ ^ e6RelCorootPair (e6SplitRoot i) (Pi.single j 1)) ∈
      rootSpan .E6 L (e6SplitCodeRoots c) := by
  have hsub : ({e6SplitRoot i, -e6SplitRoot i} : Set (Fin Tag.E6.rank → ℤ)) ⊆
      e6SplitCodeRoots c := by
    intro δ hδ
    rcases hδ with rfl | rfl
    · exact ⟨i, hi, Or.inl rfl⟩
    · exact ⟨i, hi, Or.inr (Or.inl rfl)⟩
  have hsubσ : ({permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i),
      -permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i)} :
      Set (Fin Tag.E6.rank → ℤ)) ⊆ e6SplitCodeRoots c := by
    intro δ hδ
    rcases hδ with rfl | rfl
    · exact ⟨i, hi, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨i, hi, Or.inr (Or.inr (Or.inr rfl))⟩
  by_cases hfix : ExcRaw.tabFix1.getD i.val false = true
  · have hσ : permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i) = e6SplitRoot i :=
      (e6SplitRoot_fixed_iff i).2 hfix
    have hrel : ∀ j, e6RelCorootPair (e6SplitRoot i) (Pi.single j 1) =
        corootPair (e6SplitRoot i) (Pi.single j 1) := by
      intro j
      rw [e6RelCorootPair, if_pos hσ]
    have heq : rootDiagUnit .E6
        (fun j => ζ ^ e6RelCorootPair (e6SplitRoot i) (Pi.single j 1)) =
        rootSL2 .E6 L (e6SplitRoot i) (HSL ζ) := by
      rw [rootSL2_HSL_eq (isRoot_e6SplitRoot i) ζ]
      congr 1
      funext j
      rw [hrel j]
    rw [heq]
    exact rootSpan_mono hsub
      (rootSL2_mem_rootSpan_pair (isRoot_e6SplitRoot i) (HSL ζ))
  · have hσne : permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i) ≠ e6SplitRoot i := by
      intro h
      rw [(e6SplitRoot_fixed_iff i).1 h] at hfix
      simp at hfix
    have hrel : ∀ j, e6RelCorootPair (e6SplitRoot i) (Pi.single j 1) =
        corootPair (e6SplitRoot i) (Pi.single j 1) +
          corootPair (permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i))
            (Pi.single j 1) := by
      intro j
      rw [e6RelCorootPair, if_neg hσne]
      rfl
    have heq : rootDiagUnit .E6
        (fun j => ζ ^ e6RelCorootPair (e6SplitRoot i) (Pi.single j 1)) =
        rootSL2 .E6 L (e6SplitRoot i) (HSL ζ) *
          rootSL2 .E6 L (permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i))
            (HSL ζ) := by
      rw [rootSL2_HSL_eq (isRoot_e6SplitRoot i) ζ,
        rootSL2_HSL_eq (isRoot_permLattice_e6SplitRoot i) ζ, ← rootDiagUnit_mul]
      congr 1
      funext j
      rw [Pi.mul_apply, ← zpow_add]
      congr 1
      exact hrel j
    rw [heq]
    exact mul_mem
      (rootSpan_mono hsub
        (rootSL2_mem_rootSpan_pair (isRoot_e6SplitRoot i) (HSL ζ)))
      (rootSpan_mono hsubσ
        (rootSL2_mem_rootSpan_pair (isRoot_permLattice_e6SplitRoot i) (HSL ζ)))

namespace E6SplitDatum

theorem coroot_mem_e6SplitComponent (hS : E6SplitLangTwo S) (d : E6SplitDatum S T₀)
    {c : Finset (ExcRaw.Root 1)} {i : ExcRaw.Root 1} (hi : i ∈ c) :
    rootDiagUnit .E6 (fun j => d.ζ ^ e6RelCorootPair (e6SplitRoot i) (Pi.single j 1)) ∈
      e6SplitComponent S c := by
  let h : ModGL .E6 L :=
    rootDiagUnit .E6 (fun j => d.ζ ^ e6RelCorootPair (e6SplitRoot i) (Pi.single j 1))
  let w : ModGL .E6 L := e6SplitWeyl L i
  change h ∈ e6SplitComponent S c
  have hhT : h ∈ T₀ := d.coroot_mem i
  have hnN : w ∈ Subgroup.normalizer (T₀ : Set (ModGL .E6 L)) :=
    e6SplitWeyl_mem_normalizer d hS i
  let t : ↥T₀ := ⟨h, hhT⟩
  have ht_coord : d.coord (Additive.ofMul t) = ExcRaw.coroot 1 i := d.coord_coroot i
  have hφ : ggLin (p := 3) d.coord (ggConjAut T₀ hnN) = ExcRaw.reflection 1 i :=
    ggLin_ggConjAut_e6SplitWeyl d hS i
  have h1 : d.coord (Additive.ofMul (ggConjAut T₀ hnN t)) = -ExcRaw.coroot 1 i := by
    rw [← ggLin_apply_ofMul (p := 3) d.coord (ggConjAut T₀ hnN) t, hφ, ht_coord]
    exact Module.reflection_apply_self (ExcRaw.root_coroot 1 i)
  have h2 : d.coord (Additive.ofMul (t⁻¹)) = -ExcRaw.coroot 1 i := by
    rw [ofMul_inv, map_neg, ht_coord]
  have hsub : ggConjAut T₀ hnN t = t⁻¹ := by
    apply Additive.ofMul.injective
    apply d.coord.injective
    rw [h1, h2]
  have hconj : w * h * w⁻¹ = h⁻¹ := by
    have hval := congrArg (fun x : ↥T₀ => (x : ModGL .E6 L)) hsub
    rw [ggConjAut_apply] at hval
    simpa [t] using hval
  have h3 : h ^ 3 = 1 := fullThreeTorus_pow_three S (d.le_fullThreeTorus hhT)
  have hh2 : h ^ 2 = h⁻¹ := by
    have h3' := h3
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one] at h3'
    exact eq_inv_of_mul_eq_one_right h3'
  have hinv2 : h⁻¹ * h⁻¹ = h := by
    calc h⁻¹ * h⁻¹ = h⁻¹ ^ 2 := (pow_two _).symm
      _ = (h ^ 2)⁻¹ := by rw [inv_pow]
      _ = (h⁻¹)⁻¹ := by rw [hh2]
      _ = h := inv_inv h
  have hcomm_eq : ⁅w, h⁆ = h := by
    rw [commutatorElement_def, hconj, hinv2]
  have hw_span : w ∈ rootSpan .E6 L (e6SplitCodeRoots c) :=
    e6SplitWeyl_mem_rootSpan_of_mem hi
  have hh_span : h ∈ rootSpan .E6 L (e6SplitCodeRoots c) :=
    rootDiagUnit_e6RelCoroot_mem_rootSpan d.ζ hi
  have hwΓ : w ∈ S.Γ := e6SplitWeyl_mem_Γ hS i
  have hΓM : S.Γ ≤ S.D.model := by
    simpa [LangSetup.Γ, LangDatum.Γ] using Subgroup.commutator_le_self S.D.model
  have hwM : w ∈ S.D.model := hΓM hwΓ
  have hhM : h ∈ S.D.model :=
    S.D.torus_le_model (fullThreeTorus_le_torus S (d.le_fullThreeTorus hhT))
  have hcommΓ : ⁅w, h⁆ ∈ S.Γ := by
    simpa [LangSetup.Γ, LangDatum.Γ] using
      (Subgroup.commutator_mem_commutator hwM hhM : ⁅w, h⁆ ∈ ⁅S.D.model, S.D.model⁆)
  have hhΓ : h ∈ S.Γ := hcomm_eq ▸ hcommΓ
  have hwX : w ∈ rootSpan .E6 L (e6SplitCodeRoots c) ⊓ S.Γ := ⟨hw_span, hwΓ⟩
  have hhX : h ∈ rootSpan .E6 L (e6SplitCodeRoots c) ⊓ S.Γ := ⟨hh_span, hhΓ⟩
  have hmem : ⁅w, h⁆ ∈ e6SplitComponent S c :=
    Subgroup.commutator_mem_commutator hwX hhX
  rwa [hcomm_eq] at hmem

theorem inside_le_ggLinImage (hS : E6SplitLangTwo S) (d : E6SplitDatum S T₀)
    (c : Finset (ExcRaw.Root 1)) :
    ExcRaw.inside 1 c ≤ ggLinImage (p := 3) d.coord (e6SplitComponent S c) := by
  rw [ExcRaw.inside]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, hi, rfl⟩
  rw [← d.coord_coroot i]
  exact (ofMul_mem_ggLinImage d.coord (e6SplitComponent S c) ⟨_, d.coroot_mem i⟩).mpr
    (coroot_mem_e6SplitComponent hS d hi)

end E6SplitDatum

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
