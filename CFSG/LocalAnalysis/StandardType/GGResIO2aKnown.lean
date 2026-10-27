module

public import CFSG.LocalAnalysis.StandardType.GGResIO2aGroup
public import CFSG.LocalAnalysis.StandardType.GGResILineInputs
public import CFSG.LocalAnalysis.StandardType.GGResIFixJ
public import CFSG.LocalAnalysis.StandardType.GGResTwA2Nbr
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGResFFDefs
public import CFSG.LocalAnalysis.StandardType.GGResIO2aTableP
public import CFSG.LocalAnalysis.StandardType.GGTPNLineDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResI_o2a_label (hFix : GGTBFixInput) (hTBJ : GGResLineJLabelInput)
    (hTP : GGNbrTablePNbrInputI1On GGRegimeLine) (hRig : GGLabelRigidInput)
    (hTwA2 : GGTwE6TwA2CompKnown)
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput) (hRk : GGTwE6ThreeNbrRankInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) [Fact p.Prime]
    (hD : GGResLeviDatumCell p Bs L J K ggSelI (ggTypRankLt 8)
      (fun b CL CK u v => GGResO2aCell p b CL CK u v))
    (hK2 : GGInnerDiagOnLabel GGLabQTwo p Bs K) :
    ∃ lab : LargeEvenLabel, (lab = ⟨.A, 5, 1⟩ ∨ lab = ⟨.A, 6, 1⟩) ∧
      GGHasLabel lab (K ⧸ Subgroup.center K) := by
  obtain ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α, hWL, hCL, hWK, hCK, htyp, hφ,
    hrefl, hL, hK, hsel, -, -, hAL, hAK, -, hJ, hcell⟩ := hD
  obtain ⟨hp3, j₀, j₁, h01, hcov, c01, c10, c0b, cb0, c1b, cb1, -⟩ := hcell
  subst hp3
  have hind : LinearIndependent (ZMod 3) h := hsel
  have hspan := ggResI_span_top hFix hH ι hφ hAL hind
  have hdim := ggResI_finrank hspan hind
  have hJcov : ∀ j : {i : Λ // i ≠ b}, j = j₀ ∨ j = j₁ := by
    intro j
    rcases hcov j.1 with h0 | h1 | hb
    · exact Or.inl (Subtype.ext h0)
    · exact Or.inr (Subtype.ext h1)
    · exact absurd hb j.2
  let e : Fin 2 ≃ {i : Λ // i ≠ b} := Equiv.ofBijective ![j₀, j₁] (by
    constructor
    · intro k l hkl
      fin_cases k <;> fin_cases l <;> simp at hkl ⊢
      · exact h01 hkl
      · exact h01 hkl.symm
    · intro j
      rcases hJcov j with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩)
  have he0 : e 0 = j₀ := rfl
  have he1 : e 1 = j₁ := rfl
  have hCLd : ∀ i, CL i i = 2 := hCL.1
  have hindJ : LinearIndependent (ZMod 3) (fun j : {i : Λ // i ≠ b} => α (some j.1)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hsum : ∀ v : V, g j₀ * α (some j₀.1) v + g j₁ * α (some j₁.1) v = 0 := by
      intro v
      have h1 := congrArg (fun f : Module.Dual (ZMod 3) V => f v) hg
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        LinearMap.zero_apply] at h1
      rw [← Equiv.sum_comp e, Fin.sum_univ_two, he0, he1] at h1
      exact h1
    have hb' := hsum (h (some b))
    rw [hL, hL, c0b, c1b] at hb'
    have hg0 : g j₀ = 0 := by
      have : g j₀ * ((-1 : ℤ) : ZMod 3) = 0 := by simpa using hb'
      simpa using this
    have h0' := hsum (h (some j₀.1))
    rw [hL, hL, hCLd, c10, hg0] at h0'
    have hg1 : g j₁ = 0 := by
      have : g j₁ * ((-1 : ℤ) : ZMod 3) = 0 := by simpa using h0'
      simpa using this
    intro j
    rcases hJcov j with rfl | rfl
    · exact hg0
    · exact hg1
  obtain ⟨-, hI1⟩ := ggResI_fixJ_le_D hH ι hφ (fun j _ => hrefl (some j)) hdim hJ hindJ
  have hJD : GGResLineJDatum 3 Bs J .A2 := by
    refine ⟨V, inferInstance, inferInstance, ι, fun k => φ (some (e k).1),
      fun k => h (some (e k).1), fun k => α (some (e k).1), fun k w => hφ _ w, fun k => hrefl _,
      fun i j => ?_,
      hind.comp _ fun a c hac => e.injective (Subtype.ext (Option.some_injective _ hac)), ?_⟩
    · have key : ∀ i j : Fin 2, CL (e i).1 (e j).1 = CartanMatrix.A 2 i j := by
        simp only [Fin.forall_fin_two, he0, he1, hCLd, c01, c10]
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp [CartanMatrix.A, Matrix.of_apply]
      rw [hL]
      exact congrArg (Int.cast) (key i j)
    · rw [hJ]
      congr 1
      ext u
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨e.symm j, by simp⟩
      · rintro ⟨k, rfl⟩
        exact ⟨e k, rfl⟩
  obtain ⟨labJ, hΛJ, hJlab, hhasJ⟩ := hTBJ G 3 B Bs x L D J y K hH rfl .A2 hJD
  have hnb := hH.2.2.2.2.1
  have hinnK : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hnb
  obtain ⟨labK, hΛK, hhasK, R, _, I, F, θ, hq2, -⟩ := largeEvenMarking_exists_hasLabel hK2
  have hcard5 : Nat.card Bs ≤ 3 ^ 5 := by
    classical
    have : Finite V := Finite.of_equiv _ ι.toEquiv
    have hcardV : Nat.card ↥Bs = Nat.card V := Nat.card_congr (Additive.ofMul.trans ι.toEquiv)
    have hV := FiniteField.pow_finrank_eq_natCard 3 V
    have hΛ3 : Fintype.card Λ ≤ 3 := by
      have hsub : (Finset.univ : Finset Λ) ⊆ {j₀.1, j₁.1, b} := by
        intro i _
        rcases hcov i with h | h | h <;> simp [h]
      calc Fintype.card Λ = (Finset.univ : Finset Λ).card := Finset.card_univ.symm
        _ ≤ ({j₀.1, j₁.1, b} : Finset Λ).card := Finset.card_le_card hsub
        _ ≤ 3 := Finset.card_le_three
    rw [hcardV, ← hV, hdim]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨labJ', labK', hΛJ', hΛK', hrow, hhasJ', hhasK'⟩ :=
    hTP G 3 B Bs x L D J y K hH.1 hH.2.2.1.1 hinnK hnb hI1 labJ labK hΛJ hΛK
      ⟨rfl, hcard5, .A2, hJlab⟩ hhasJ hhasK
  have hJlab2 : (labJ.tag = .A ∧ labJ.rank = 2 ∧ 3 ∣ 2 ^ labJ.n - 1) ∨
      (labJ.tag = .twA ∧ labJ.rank = 2 ∧ 3 ∣ 2 ^ labJ.n + 1) := hJlab
  have hJJ' : labJ' = labJ :=
    ggLabelIso_A2_eq (hJlab2.imp (fun h => ⟨h.1, h.2.1⟩) (fun h => ⟨h.1, h.2.1⟩))
      (hRig labJ labJ' _ hΛJ hΛJ' hhasJ hhasJ')
  have hKK' : GGLabelIso labK labK' := hRig labK labK' _ hΛK hΛK' hhasK hhasK'
  rcases ggTablePRow_three_A2_qTwo_iso hΛJ' (hJJ' ▸ hJlab2) hrow hΛK hKK' hq2 with
    ⟨-, h56⟩ | ⟨hJ8, hE6, hn1⟩
  · exact ⟨labK', h56, hhasK'⟩
  · exfalso
    exact ggTwA2_K_absurd hTwA2 hRig (ggNbrSubcomponentInput_of_lBalance hLB hSP) hRk hH.1
      hH.2.2.1 rfl hnb hΛJ' hΛK' hhasJ' hhasK'
      ⟨by rw [hJ8], by rw [hJ8], rfl, hE6, by rw [hn1, hJ8]⟩

theorem ggResCaseIQFourO2Input_of_known (hFix : GGTBFixInput) (hTBJ : GGResLineJLabelInput)
    (hTP : GGNbrTablePNbrInputI1On GGRegimeLine) (hRig : GGLabelRigidInput)
    (hTwA2 : GGTwE6TwA2CompKnown)
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput) (hRk : GGTwE6ThreeNbrRankInput)
    (hZ : GGO2aCentreKnown) (hFF : GGFFLinearProp2Input) : GGResCaseIQFourO2Input := by
  intro G _ _ p B Bs x L D J y K hH _ _ _ _ hP
  obtain ⟨hD, -, hK2⟩ := hP
  exfalso
  obtain ⟨lab, hlab, hhas⟩ :=
    ggResI_o2a_label hFix hTBJ hTP hRig hTwA2 hLB hSP hRk hH hD hK2
  obtain ⟨hp3, hy3, hKy, hKn, hcyc, hfus, ⟨B₁, hB₁K, hB₁EA, hB₁c, hS⟩, h5⟩ :=
    ggResI_o2a_facts hFix hH hD
  subst hp3
  have hlabK : GGHasLabel ⟨.A, 5, 1⟩ K ∨ GGHasLabel ⟨.A, 6, 1⟩ K := by
    have hK := ggO2a_hasLabel_of_centre hZ hK2.1 hlab hhas
    rcases hlab with rfl | rfl
    · exact Or.inl hK
    · exact Or.inr hK
  have hc := hFF G y K B₁ hy3 hKy hKn hlabK hB₁K hB₁EA hB₁c hcyc hfus hH.1.1.2.2.2.1
  rw [hS] at hc
  rcases hc with hc | hc <;> rw [hc] at h5 <;> norm_num at h5

end CFSG.StandardType
