module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallLinTwoEnd
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeLabels

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Statements

variable {K : Type} [Field K] [Finite K] {d : ℕ}

theorem ggOutdiagPrime_linTwo (hK : Nat.card K = 2) :
    GGOutdiagPrime 3 (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ) := by
  intro φ hφ _
  obtain ⟨A, -, hA⟩ := hφ
  have hdet : (A : Matrix (Fin d) (Fin d) K).det = 1 := TwoThree.det_eq_one_of_card hK A
  have hmem : A ∈ LargeEvenSLGroup (Fin d) K := TypeA.mem_largeEvenSLGroup_iff.mpr hdet
  set a : LargeEvenSLGroup (Fin d) K := ⟨A, hmem⟩ with ha
  refine ⟨LargeEvenProjMk _ a, ?_⟩
  ext x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  have h1 := hA h (a * h * a⁻¹) rfl
  change MulAut.conj (LargeEvenProjMk _ a) (LargeEvenProjMk _ h) = φ (LargeEvenProjMk _ h)
  rw [MulAut.conj_apply, h1, map_mul, map_mul, map_inv]

theorem ggOutdiagOdd_linTwo (hK : Nat.card K = 2) :
    GGOutdiagOdd 3 (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ) :=
  ggOutdiagOdd_of_prime (ggOutdiagPrime_linTwo hK)

theorem exists_frame_of_recipe [CharP K 2] (hK : Nat.card K = 2) (hd : 6 ≤ d) {L' : Type}
    [Group L'] [Finite L']
    (ψ : L' →* LargeEvenProj (LargeEvenSLGroup (Fin d) K))
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (A : Subgroup (MulAut L')) (hA : IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K))
      Set.univ, ∀ l : L', x (ψ l) = ψ (a l))
    (hr : 3 ^ (d / 2) ≤ Nat.card A) :
    ∃ (φ₀ : Matrix.SpecialLinearGroup (Fin d) K →* L') (g : Polynomial K)
      (_ : Fact (Irreducible g)) (s r : ℕ)
      (ε : Fin d ≃ (Fin (CoordSL.rootPB g).dim × Fin s) ⊕ Fin r)
      (A₀ : Matrix.SpecialLinearGroup (Fin d) K) (hC : (CoordSL.rootMat g).det = 1)
      (hCp : CoordSL.rootMat g ^ 3 = 1), SmallL2.IsFrame φ₀ ε A₀ hC hCp A := by
  set e := TypeA.recipeEquiv d K with he
  refine SmallL2.exists_frame_for hK hd (e.toMonoidHom.comp ψ) (e.surjective.comp hψ) ?_ hperf A
    hA ?_ hr
  · intro l hl
    exact hker (by simpa [MonoidHom.mem_ker] using hl)
  · intro a ha
    obtain ⟨x, hx, hxa⟩ := hAI a ha
    refine ⟨MulAut.congr e x, TypeA.congr_recipeEquiv_mem hx, fun l => ?_⟩
    simp [MulAut.congr_apply, hxa l]

theorem ggStdSubTwoTorusNormSmall_linTwo (hK : Nat.card K = 2) (hd : 6 ≤ d) :
    GGStdSubTwoTorusNormSmall 3 (d / 2) (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hα a ha ha1 hEcomp hcentA hsmall
  have : CharP K 2 := charP_two_of_card (m := 1) (by simpa using hK)
  obtain ⟨φ₀, g, hg, s, r, ε, A₀, hC, hCp, hfr⟩ :=
    exists_frame_of_recipe hK hd ψ hψ hker hperf A hA hAI hr
  haveI := hg
  have hnsplit : ¬ 3 ∣ Nat.card K - 1 := by
    rw [hK]
    decide
  obtain ⟨β, rfl⟩ := (hfr.mem_A a).mp ha
  have hβ : β ≠ 0 := by
    rintro rfl
    apply ha1
    rw [ofAdd_zero, map_one, map_one]
  exact SmallL2.concl_of_frame ε hfr.bij hfr.gd hnsplit hfr.s3 hfr.conj_inj hfr.mem_A hβ hEcomp
    hcentA

theorem ggStdSubTwoTorusDeltaSmall_linTwo (hK : Nat.card K = 2) (hd : 6 ≤ d) :
    GGStdSubTwoTorusDeltaSmall 3 (d / 2) (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hδ a ha ha1 hEcomp hcentA hsmall
  have : CharP K 2 := charP_two_of_card (m := 1) (by simpa using hK)
  obtain ⟨φ₀, g, hg, s, r, ε, A₀, hC, hCp, hfr⟩ :=
    exists_frame_of_recipe hK hd ψ hψ hker hperf A hA hAI hr
  haveI := hg
  exfalso
  refine SmallL2.not_ggDeltaAdm_of_inner (p := 3) (by decide) hfr.conj_inj ?_ hδ
  intro b hb
  obtain ⟨β, rfl⟩ := (hfr.mem_A b).mp hb
  exact ⟨_, rfl⟩

end Statements

theorem largeEvenLabelAll_stdSubNormSmall_linTwo {p : ℕ} {lab : LargeEvenLabel}
    (h : GGLinTwoLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧ ∃ r, GGTorusLift p r R ∧
      GGStdSubTwoTorusNormSmall p r R I ∧ GGStdSubTwoTorusDeltaSmall p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hn, hp⟩ := h
  dsimp only at ht hl hn hp
  subst ht hn hp
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have hK2 : Nat.card K = 2 := by simpa using hK
  have : CharP K 2 := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ', ggOutdiagOdd_linTwo hK2, (l + 1) / 2,
    TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (TwoThree.ggTorusLift_two hK2 (by omega)),
    ggStdSubTwoTorusNormSmall_linTwo hK2 (by omega),
    ggStdSubTwoTorusDeltaSmall_linTwo hK2 (by omega)⟩

theorem ggStdSubSmallInputOn_linTwo_holds :
    GGStdSubSmallInputOn GGLinTwoLabel :=
  ggStdSubSmallInputOn_of_labels_normSmall ggLNoncyclicInput_holds fun _ _ _ _ hS _ =>
    largeEvenLabelAll_stdSubNormSmall_linTwo hS

theorem ggStdSubSmallInputOn_of_not_linTwo
    {T : ℕ → LargeEvenLabel → Prop}
    (h : GGStdSubSmallInputOn fun p lab => T p lab ∧ ¬ GGLinTwoLabel p lab) :
    GGStdSubSmallInputOn T :=
  (ggStdSubSmallInputOn_linTwo_holds.or h).mono fun p lab hT => by
    by_cases hl : GGLinTwoLabel p lab
    · exact Or.inl hl
    · exact Or.inr ⟨hT, hl⟩

end CFSG.StandardType

end
