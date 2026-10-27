module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormLinearThreePrime
public import CFSG.LocalAnalysis.StandardType.GGPGLKernelShifts
public import CFSG.LocalAnalysis.StandardType.GGTBWNormQuotTwoShears
public import CFSG.LocalAnalysis.StandardType.GGTBWNormMpCellLabels

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag


namespace TypeA

theorem ggTorusWNormSC_w5 {K : Type} [Field K] [Finite K] [CharP K 2]
    {d p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : p ∣ Nat.card K - 1)
    (hpd : p ∣ d) (hdp : 5 * p ≤ d) :
    GGTorusWNormSC p (projectiveSL d K) (Set.range (conjAut d K)) := by
  have hp2 : p ≠ 2 := by omega
  have hd : 5 ≤ d := by omega
  have hd0 : 0 < d := by omega
  have : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc _ Λ _ _ M C V _ _ ι φ h α
    hM hC hpair hlin hgen s hs
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have hXA : IsElemAbelian p (inducedSub ψ A) := isElemAbelian_inducedSub hψ hA
  set G := (inducedSub ψ A).comap (conjAut d K) with hGdef
  have hG : PGLTor.IsProjElem p G := isProjElem_comap hd0 hXA
  by_cases hcent : ∀ x ∈ G, x ^ p = 1 → ∀ y ∈ G, y * x = x * y
  · rcases PGLTor.toral_or_exists_centralBlockModel hp hp2 hpK hG hcent with h | h
    · obtain ⟨A₀, hA₀⟩ := h
      have hperfSL : commutator (SpecialLinearGroup (Fin d) K) = ⊤ :=
        (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := d) (by omega)
          (Or.inl (by omega))).commutator_eq_top
      obtain ⟨π, hπs, hπker, hdiag⟩ := TypeANbrDvd.exists_actsDiag_model hperfSL
        (slHasSections_of_five_le hd) hψ hker hperf hAI (A₀ := A₀) fun B hB => hA₀ B hB
      exact ggWNormConcl_of_linear_diagonal hp hp2 hpK hd hπs hπker hA h3 hsc hdiag
        hM hC ι φ h α hpair hlin hgen hs
    · exfalso
      obtain ⟨D⟩ := h
      let x₀ : (⊤ : Subgroup (GL (Fin d) K)) := ⟨D.primitive, Subgroup.mem_top _⟩
      refine QuotMove.false_of_shears (QuotMove.isScalarQuot_PSL hd0) hp hp2
        hψ hker hperf hA ?_ h3 (x₀ := x₀) D.primitive.2 D.primitive_pow
        D.scalar_not_pow ?_ hM hC ι φ h α hpair hlin hgen
      · intro a ha
        obtain ⟨φa, hφa, hact⟩ := hAI a ha
        obtain ⟨g, rfl⟩ := hφa
        exact ⟨⟨g, Subgroup.mem_top _⟩, hact⟩
      · intro y hy hyp
        have hyG : (y : GL (Fin d) K) ∈ G := hy
        obtain ⟨E, hEshift, hEfix⟩ := D.exists_SL_kernel_shift hp hp5 hpK hG hyG hyp
        let E' : (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin d) K →*
            GL (Fin d) K).range := ⟨SpecialLinearGroup.toGL E, E, rfl⟩
        refine ⟨E', ?_, ?_⟩
        · exact hEshift
        · intro z hz hzp
          have hzG : (z : GL (Fin d) K) ∈ G := hz
          have hzker : (z : GL (Fin d) K) ∈ D.kernel :=
            (D.kernel_mem_iff z hzG).mpr ⟨1, by simpa using hzp⟩
          exact hEfix z hzker
  · exfalso
    push Not at hcent
    obtain ⟨x₀, hx₀G, hx₀p, y₀, hy₀G, hne⟩ := hcent
    have hu₀1 : PGLTor.commChar hG hx₀G ⟨y₀, hy₀G⟩ ≠ 1 := fun h1 =>
      hne ((PGLTor.commChar_eq_one_iff hG hx₀G ⟨y₀, hy₀G⟩).mp h1).symm
    have hdiag : ∀ i, α i (h i) = 2 := fun i => by rw [hpair i i, hC.1 i]; simp
    exact false_of_noncomm_lifts hp hp5 hpK hpd hd0 hψ hker hperf hA hAI
      hx₀G hy₀G hx₀p (PGLTor.commChar_spec hG hx₀G ⟨y₀, hy₀G⟩) hu₀1
      (PGLTor.commChar_pow_eq_one hG hx₀G ⟨y₀, hy₀G⟩) ι φ h α hdiag hlin hgen

end TypeA

theorem ggTorusWNormSC_linear_w5 {K : Type} [Field K] [Finite K] [CharP K 2]
    {d p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : p ∣ Nat.card K - 1)
    (hpd : p ∣ d) (hdp : 5 * p ≤ d) :
    GGTorusWNormSC p (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk _) Set.univ) :=
  ggTorusWNormSC_of_mulEquiv (TypeA.recipeEquiv d K)
    (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
    (TypeA.ggTorusWNormSC_w5 hp hp5 hpK hpd hdp)

theorem largeEvenLabelAll_wnorm_linear_w5 {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hl : GGTBWNormW5SplitLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  rcases hl with ⟨ht, hp5, hpd, hdp, hpq⟩
  rcases lab with ⟨tag, r, n⟩
  dsimp only at ht hpd hdp hpq ⊢
  subst tag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  change LargeEvenRecipeLinear (r + 1) (2 ^ n) Q at hQ
  change LargeEvenRecipeLinear (r + 1) (2 ^ n)
    (fun R _ I F => Q R I F ∧ GGTorusWNormSC p R I)
  obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
  exact ggTorusWNormSC_linear_w5 hp hp5 (by rwa [hK]) hpd hdp

end CFSG.StandardType
