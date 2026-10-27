module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormLinearTwicePrime
public import CFSG.LocalAnalysis.StandardType.GGTBWNormQuotTransvection
public import CFSG.LocalAnalysis.StandardType.GGPGLBlockFrobenius

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace TypeA

theorem ggTorusWNormSC_three_prime {K : Type} [Field K] [Finite K] [CharP K 2]
    {d p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : p ∣ Nat.card K - 1)
    (hdp : d = 3 * p) :
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
  have hXI : ((inducedSub ψ A : Subgroup (MulAut (projectiveSL d K))) :
      Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K) := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    exact induced_unique ψ hψ hφa hxa ▸ hφaI
  have hcardX : Nat.card (inducedSub ψ A) = Nat.card A :=
    card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨φa, -, hφa⟩ := hAI a ha
      exact ⟨φa, hφa⟩)
  set G := (inducedSub ψ A).comap (conjAut d K) with hGdef
  have hG : PGLTor.IsProjElem p G := isProjElem_comap hd0 hXA
  have hcardG : Nat.card G = Nat.card A * (Nat.card K - 1) := by
    rw [hGdef, card_comap_eq hd0 hXI, hcardX]
  have hdim : Fintype.card (Fin d) = 3 * p := by simpa using hdp
  have hcard : p ^ 3 * (Nat.card K - 1) ≤ Nat.card G := by
    rw [hcardG]
    exact Nat.mul_le_mul_right _ h3
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
      have hn := D.numBlocks_eq_three_of_card_ge hp hdim hcard
      have hk := D.card_kernel_eq_of_card_ge hp hdim hcard
      have hupper := D.card_le
      rw [hn, hcardG] at hupper
      have hK1 : 0 < Nat.card K - 1 := by have := Finite.one_lt_card (α := K); omega
      have hcardA : Nat.card A ≤ p ^ 3 := Nat.le_of_mul_le_mul_right hupper hK1
      obtain ⟨E, hEN, hEfix, hEmove⟩ :=
        D.exists_SL_normalizer_fix_kernel_move hp hp5 hpK hG hn hk.ge
      let E' : (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin d) K →* GL (Fin d) K).range :=
        ⟨SpecialLinearGroup.toGL E, E, rfl⟩
      let x₀ : (⊤ : Subgroup (GL (Fin d) K)) := ⟨D.primitive, Subgroup.mem_top _⟩
      refine QuotMove.false_of_transvection (QuotMove.isScalarQuot_PSL hd0) hp hp5
        hψ hker hperf hA ?_ hcardA (x₀ := x₀) D.primitive.2 D.primitive_pow
        D.scalar_not_pow E' ?_ ?_ ?_ hM hC ι φ h α hpair hlin hgen
      · intro a ha
        obtain ⟨φa, hφa, hact⟩ := hAI a ha
        obtain ⟨g, rfl⟩ := hφa
        exact ⟨⟨g, Subgroup.mem_top _⟩, hact⟩
      · intro x hx
        obtain ⟨g, rfl⟩ := hXI hx
        change conjAut d K (SpecialLinearGroup.toGL E) * conjAut d K g *
          (conjAut d K (SpecialLinearGroup.toGL E))⁻¹ ∈ inducedSub ψ A
        rw [← map_inv, ← map_mul, ← map_mul]
        exact hEN g hx
      · intro z hz hzp
        have hzG : (z : GL (Fin d) K) ∈ G := hz
        have hzker : (z : GL (Fin d) K) ∈ D.kernel :=
          (D.kernel_mem_iff z hzG).mpr ⟨1, by simpa using hzp⟩
        change conjAut d K (SpecialLinearGroup.toGL E) * conjAut d K z *
          (conjAut d K (SpecialLinearGroup.toGL E))⁻¹ = conjAut d K z
        rw [← map_inv, ← map_mul, ← map_mul, hEfix z hzker]
      · intro hEq
        change conjAut d K (SpecialLinearGroup.toGL E) *
          conjAut d K (D.primitive : GL (Fin d) K) *
          (conjAut d K (SpecialLinearGroup.toGL E))⁻¹ =
          conjAut d K (D.primitive : GL (Fin d) K) at hEq
        have hm : conjAut d K (SpecialLinearGroup.toGL E * (D.primitive : GL (Fin d) K) *
            (SpecialLinearGroup.toGL E)⁻¹) = conjAut d K (D.primitive : GL (Fin d) K) := by
          simpa only [map_mul, map_inv] using hEq
        obtain ⟨u, hu⟩ := exists_scalar_mul_of_conjAut_eq hd0 hm
        exact hEmove u hu
  · exfalso
    push Not at hcent
    obtain ⟨x₀, hx₀G, hx₀p, y₀, hy₀G, hne⟩ := hcent
    have hu₀1 : PGLTor.commChar hG hx₀G ⟨y₀, hy₀G⟩ ≠ 1 := fun h1 =>
      hne ((PGLTor.commChar_eq_one_iff hG hx₀G ⟨y₀, hy₀G⟩).mp h1).symm
    have hdiag : ∀ i, α i (h i) = 2 := fun i => by rw [hpair i i, hC.1 i]; simp
    exact false_of_noncomm_lifts hp hp5 hpK (hdp ▸ dvd_mul_left p 3) hd0 hψ hker hperf
      hA hAI hx₀G hy₀G hx₀p (PGLTor.commChar_spec hG hx₀G ⟨y₀, hy₀G⟩) hu₀1
      (PGLTor.commChar_pow_eq_one hG hx₀G ⟨y₀, hy₀G⟩) ι φ h α hdiag hlin hgen

end TypeA

theorem ggTorusWNormSC_linear_three_prime {K : Type} [Field K] [Finite K] [CharP K 2]
    {d p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : p ∣ Nat.card K - 1) (hdp : d = 3 * p) :
    GGTorusWNormSC p (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk _) Set.univ) :=
  ggTorusWNormSC_of_mulEquiv (TypeA.recipeEquiv d K)
    (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
    (TypeA.ggTorusWNormSC_three_prime hp hp5 hpK hdp)

theorem largeEvenLabelAll_wnorm_linear_three_prime {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hp5 : 5 ≤ p) (ht : lab.tag = .A)
    (hdp : lab.rank + 1 = 3 * p) (hpq : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  rcases lab with ⟨tag, r, n⟩
  dsimp only at ht hdp hpq ⊢
  subst tag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  change LargeEvenRecipeLinear (r + 1) (2 ^ n) Q at hQ
  change LargeEvenRecipeLinear (r + 1) (2 ^ n) (fun R _ I F => Q R I F ∧ GGTorusWNormSC p R I)
  obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
  exact ggTorusWNormSC_linear_three_prime hp hp5 (by rwa [hK]) hdp

end CFSG.StandardType
