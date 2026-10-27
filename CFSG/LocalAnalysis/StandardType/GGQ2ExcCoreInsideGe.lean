module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGLangModelIndex
public import CFSG.LocalAnalysis.StandardType.GGLangRatComp
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompChain
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.QTwoCav
  CFSG.StandardType.LangRat CFSG.HardMathSupport.Timmesfeld.CrossChar

open scoped commutatorElement

noncomputable section


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p}
  {T₀ : Subgroup (ModGL τ L)} {m : Fin 6}

theorem coroot_mem_codeComponent (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hS : NegLangTwo S) (d : ExcCoordDatum S T₀ m) {c : Finset (ExcRaw.Root m)}
    {i : ExcRaw.Root m} (hi : i ∈ c) :
    rootDiagUnit τ (fun j => d.ζ ^ corootPair (d.γ i) (Pi.single j 1)) ∈
      codeComponent S d.γ c := by
  obtain ⟨hq, hAlg, hρ⟩ := hS
  have h2L : (2 : L) = 0 := by
    have h := S.hqpow.2
    rwa [hq] at h
  have hneg : (-1 : L) = 1 := by
    rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, h2L]
  let h : ModGL τ L := rootSL2 τ L (d.γ i) (HSL d.ζ)
  let w : ModGL τ L := rootSL2 τ L (d.γ i) WSL
  let w' : ModGL τ L := h * w * h⁻¹
  have hh_eq : h = rootDiagUnit τ (fun j => d.ζ ^ corootPair (d.γ i) (Pi.single j 1)) :=
    rootSL2_HSL_eq (d.isRoot i) d.ζ
  rw [← hh_eq]
  have hhT : h ∈ T₀ := by
    rw [hh_eq]
    exact d.coroot_mem i
  have hh3 : h ^ 3 = 1 := fullThreeTorus_pow_three S (d.le_fullThreeTorus hhT)
  have hh2 : h ^ 2 = h⁻¹ := by
    have h := hh3
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one] at h
    exact eq_inv_of_mul_eq_one_right h
  have hhM : h ∈ S.D.model :=
    S.D.torus_le_model (fullThreeTorus_le_torus S (d.le_fullThreeTorus hhT))
  have hWSL2 : (WSL : SL2 L) * WSL = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, coe_WSL]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hneg]
  have hw2 : w * w = 1 := by
    dsimp [w]
    rw [← map_mul, hWSL2, map_one]
  have hwΓ : w ∈ S.Γ :=
    rootWeylSL2_mem_Γ_of_rho_neg (S := S) hτ (f := 1) (by simpa using hq) hAlg
      (d.isRoot i) (hρ _ (d.isRoot i))
  have hΓM : S.Γ ≤ S.D.model := by
    simpa [LangSetup.Γ, LangDatum.Γ] using Subgroup.commutator_le_self S.D.model
  have hwM : w ∈ S.D.model := hΓM hwΓ
  have hw'M : w' ∈ S.D.model := by
    dsimp [w']
    exact mul_mem (mul_mem hhM hwM) (inv_mem hhM)
  have hw'_inv : w'⁻¹ = w' := by
    dsimp [w']
    rw [mul_inv_rev, mul_inv_rev, inv_eq_of_mul_eq_one_right hw2]
    group
  have hw'2 : w' ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [← hw'_inv]
    exact mul_inv_cancel w'
  have hw'Γ : w' ∈ S.Γ :=
    langModel_mem_Γ_of_sq_eq_one (S := S) hτ (f := 1) (by simpa using hq) hAlg hw'M hw'2
  have hsub : ({d.γ i, -d.γ i} : Set (Fin τ.rank → ℤ)) ⊆ codeRoots d.γ c := by
    intro x hx
    rcases hx with rfl | rfl
    · exact ⟨i, hi, Or.inl rfl⟩
    · exact ⟨i, hi, Or.inr rfl⟩
  have hw_span : w ∈ rootSpan τ L (codeRoots d.γ c) :=
    rootSpan_mono hsub (rootSL2_mem_rootSpan_pair (d.isRoot i) WSL)
  have hh_span : h ∈ rootSpan τ L (codeRoots d.γ c) :=
    rootSpan_mono hsub (rootSL2_mem_rootSpan_pair (d.isRoot i) (HSL d.ζ))
  have hw'_span : w' ∈ rootSpan τ L (codeRoots d.γ c) := by
    dsimp [w']
    exact mul_mem (mul_mem hh_span hw_span) (inv_mem hh_span)
  have hconj : w * h * w⁻¹ = h⁻¹ := by
    have hHSL_inv : HSL d.ζ⁻¹ = (HSL d.ζ)⁻¹ := (HSL_inv d.ζ).symm
    have h1 := congrArg (rootSL2 τ L (d.γ i))
      (CFSG.StandardType.LangRat.WSL_conj_HSL d.ζ)
    rw [hHSL_inv] at h1
    simpa [h, w] using h1
  have hw_inv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hwhw : w * h * w = h⁻¹ := by
    rw [← hconj, hw_inv]
  have hinv2 : h⁻¹ * h⁻¹ = h := by
    calc h⁻¹ * h⁻¹ = h⁻¹ ^ 2 := (pow_two _).symm
      _ = (h ^ 2)⁻¹ := by rw [inv_pow]
      _ = (h⁻¹)⁻¹ := by rw [hh2]
      _ = h := inv_inv h
  have hww' : w * w' = h := by
    calc w * w' = (w * h * w) * h⁻¹ := by dsimp [w']; group
      _ = h⁻¹ * h⁻¹ := by rw [hwhw]
      _ = h := hinv2
  have hcomm_eq : ⁅w, w'⁆ = h⁻¹ := by
    rw [commutatorElement_def, hw_inv, hw'_inv]
    calc w * w' * w * w' = (w * w') * (w * w') := by group
      _ = h * h := by rw [hww']
      _ = h⁻¹ := by simpa [pow_two] using hh2
  have hwX : w ∈ rootSpan τ L (codeRoots d.γ c) ⊓ S.Γ :=
    Subgroup.mem_inf.mpr ⟨hw_span, hwΓ⟩
  have hw'X : w' ∈ rootSpan τ L (codeRoots d.γ c) ⊓ S.Γ :=
    Subgroup.mem_inf.mpr ⟨hw'_span, hw'Γ⟩
  have hcomm_mem : ⁅w, w'⁆ ∈
      ⁅rootSpan τ L (codeRoots d.γ c) ⊓ S.Γ, rootSpan τ L (codeRoots d.γ c) ⊓ S.Γ⁆ :=
    Subgroup.commutator_mem_commutator hwX hw'X
  show h ∈ codeComponent S d.γ c
  rw [codeComponent, show h = (⁅w, w'⁆)⁻¹ by rw [hcomm_eq, inv_inv]]
  exact inv_mem hcomm_mem

theorem inside_le_ggLinImage_codeComponent (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hS : NegLangTwo S) (d : ExcCoordDatum S T₀ m) (c : Finset (ExcRaw.Root m)) :
    ExcRaw.inside m c ≤ ggLinImage (p := 3) d.coord (codeComponent S d.γ c) := by
  rw [ExcRaw.inside]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, hi, rfl⟩
  rw [← d.coord_coroot i]
  exact (ofMul_mem_ggLinImage d.coord (codeComponent S d.γ c) ⟨_, d.coroot_mem i⟩).mpr
    (coroot_mem_codeComponent hτ hS d hi)

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
