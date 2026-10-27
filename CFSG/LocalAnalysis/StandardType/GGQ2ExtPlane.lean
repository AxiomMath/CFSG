module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExtPlaneInner
public import CFSG.LocalAnalysis.StandardType.GGQ2ExtPlaneAmb
public import CFSG.LocalAnalysis.StandardType.GGQ2ExtClassicalStatements
public import CFSG.LocalAnalysis.StandardType.GGQ2PlaneShapes
public import CFSG.LocalAnalysis.StandardType.GGQ2PlaneChainProofs
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalInsideMoved

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module PlaneRaw

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def PlaneChainFacts : Prop :=
  LeafModelSigned ∧ LeafModelEvenSigned ∧ LeafModelFlip ∧ NbrChainSigned ∧ NbrChainEvenSigned ∧
    AmbientChainEvenSigned

theorem not_q2_linear_ext {t : ℕ} (ht : 4 ≤ t) (ε : Fin 2) {e : V t} (he : ∀ i, e i ≠ 0) :
    ¬ ∃ lab : LargeEvenLabel, GGLabQTwo 3 lab ∧
      GGLabelIso lab (PlaneRaw.label (.linear ε) (.extension e)) := by
  rintro ⟨lab, hq, hiso⟩
  have hcard : (Code.extSupport e).card = t := by
    have : Code.extSupport e = Finset.univ := by
      ext i
      simp [Code.extSupport, he i]
    rw [this, Finset.card_univ, Fintype.card_fin]
  have hlab : PlaneRaw.label (.linear ε) (.extension e) = ⟨.A, t - 1, 2⟩ := by
    simp only [PlaneRaw.label, hcard]
  rw [hlab] at hiso
  unfold GGLabQTwo at hq
  unfold GGLabelIso at hiso
  rcases hiso with h | h | h | h | h | h | h | h
  · rw [h] at hq
    simp at hq
  · simp at h
  · obtain ⟨-, h2⟩ := h
    have := congrArg LargeEvenLabel.n h2
    simp at this
    omega
  · obtain ⟨-, h2⟩ := h
    simp at h2
  · obtain ⟨-, h2⟩ := h
    simp at h2
  · obtain ⟨-, h2⟩ := h
    simp at h2
  · obtain ⟨-, h2⟩ := h
    have := congrArg LargeEvenLabel.rank h2
    simp at this
    omega
  · obtain ⟨h1, -⟩ := h
    simp at h1

theorem extCases_planeEntry (hc : PlaneChainFacts) (kd : PlaneKind) (t : ℕ) :
    ExtCases (planeEntry kd t) := by
  obtain ⟨hLS, hLE, hLF, hNb, hNe, hAmb⟩ := hc
  intro vx hvx0 ℓ hadmℓ hlab hocc hcent hvxin U hU hvxU j hadmj hjocc hjcent hinsj hnormj z hzU
    hzvx k hcand hinsk
  have ht : 4 ≤ t := hadmℓ.1
  obtain ⟨-, hkocc, hkcent, -, hvxk⟩ := hcand
  have hpos : ExtPosition kd vx ℓ U j z k := by
    unfold ExtPosition
    exact ⟨hvx0, hocc, hcent, hvxin, hU, hvxU, hjocc, hjcent, hinsj, hzU, hzvx, hkocc, hkcent,
      hvxk, hinsk⟩
  have hshape := extPlaneShape_of_position lineShapes_holds planeShapes_holds kd ht hpos
  by_cases hkd : kd = .orthogonal 0
  · subst hkd
    rcases hshape with hA1 | hA2 | hB2a | hB2b
    ·
      obtain ⟨a, c, s, s', hac, hs, hs', hvx, hz, hℓ, hj, hk, hU'⟩ := hA1
      have hjcard : (Finset.univ \ {a, c} : Finset (Fin t)).card = t - 2 := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
          Finset.card_pair hac]
      have hadm := hadmj.2
      rw [hj] at hadm
      simp only [PlaneRaw.admissible, hjcard, Fin.val_zero] at hadm
      have hA1' : ExtShapeA1 vx ℓ U j z k := ⟨a, c, s, s', hac, hs, hs', hvx, hz, hℓ, hj, hk, hU'⟩
      rcases Nat.even_or_odd t with hev | hod
      · have ht6 : 6 ≤ t := by
          rcases hadm with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · obtain ⟨m, hm⟩ := hev
            omega
          · obtain ⟨m, hm⟩ := hev
            obtain ⟨n, hn⟩ := h1
            omega
        have hodd : Odd (t - 1) := by
          obtain ⟨m, hm⟩ := hev
          exact ⟨m - 1, by omega⟩
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (extInner_A1_even hNe (by omega) hodd hA1')))))
      · by_cases h5 : t = 5
        · subst h5
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (extD5_A1 hAmb hA1')))))))
        · have ht7 : 7 ≤ t := by
            obtain ⟨m, hm⟩ := hod
            omega
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            (extAmbD_A1 hAmb ht7 hod hA1')))))))
    · exact Or.inr (Or.inr (Or.inl (extLeaf_A2_even hLE ht hA2)))
    · exact Or.inr (Or.inr (Or.inl (extLeaf_B2a_even hLE ht hB2a)))
    · exact Or.inr (Or.inr (Or.inl (extLeaf_B2b hLF _ ht hB2b)))
  · rcases hshape with hA1 | hA2 | hB2a | hB2b
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (extInner_A1_signed hNb hkd ht hA1)))))
    · exact Or.inr (Or.inr (Or.inl (extLeaf_A2_signed hLS hkd ht hA2)))
    · by_cases hlin : ∃ ε, kd = .linear ε
      · obtain ⟨ε, rfl⟩ := hlin
        exfalso
        obtain ⟨b, e', μ, ε', σ, β, hμ, hε, hσ, hβ, he'b, he'i, hvx, hℓ, hj, hU', hz, hk⟩ := hB2a
        refine not_q2_linear_ext ht ε (e := ε' • (e' + σ • unitVec t b))
          (extKey_ne_zero he'b he'i hε hσ) ?_
        rw [hℓ] at hlab
        exact hlab
      · exact Or.inr (Or.inr (Or.inl (extLeaf_B2a_signed hLS hkd ht hB2a)))
    · by_cases hlin : ∃ ε, kd = .linear ε
      · obtain ⟨ε, rfl⟩ := hlin
        exfalso
        obtain ⟨b, e', μ, ε', ε'', σ, β, hμ, hε, hε', hσ, hβ, he'b, he'i, hvx, hℓ, hj, hU', hz, hk⟩ :=
          hB2b
        refine not_q2_linear_ext ht ε (e := ε' • (e' + σ • unitVec t b))
          (extKey_ne_zero he'b he'i hε hσ) ?_
        rw [hℓ] at hlab
        exact hlab
      · exact Or.inr (Or.inr (Or.inl (extLeaf_B2b hLF kd ht hB2b)))

theorem extCasesLin_of_chains (hc : PlaneChainFacts) : ExtCasesLin :=
  fun t ε => extCases_planeEntry hc (.linear ε) t

theorem extCasesSymp_of_chains (hc : PlaneChainFacts) : ExtCasesSymp :=
  fun t => extCases_planeEntry hc .symplectic t

theorem extCasesOrth_of_chains (hc : PlaneChainFacts) : ExtCasesOrth :=
  fun t δ => extCases_planeEntry hc (.orthogonal δ) t

theorem planeChainFacts_holds : PlaneChainFacts :=
  ⟨leafModelSigned_holds, leafModelEvenSigned_holds, leafModelFlip_holds, nbrChainSigned_holds,
    nbrChainEvenSigned_holds, ambientChainEvenSigned_holds⟩

theorem extCasesLin_holds : ExtCasesLin :=
  extCasesLin_of_chains planeChainFacts_holds

theorem extCasesSymp_holds : ExtCasesSymp :=
  extCasesSymp_of_chains planeChainFacts_holds

theorem extCasesOrth_holds : ExtCasesOrth :=
  extCasesOrth_of_chains planeChainFacts_holds

end CFSG.StandardType.GGQ2Frame
