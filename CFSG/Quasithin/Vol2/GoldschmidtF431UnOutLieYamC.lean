module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieYamB
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieYamMap
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnSystem
public import CFSG.Quasithin.Vol2.GoldschmidtF431BNYam

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open CFSG.GH74.BNPair CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.QuasithinUnique
  CFSG.Quasithin.H13.Sec53F.Yam CFSG.Quasithin.H13.F431.BN CFSG.Quasithin.H13.F431.Un
  CFSG.LocalAnalysis.ComponentInitial

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  (ζ : traceZero (unitaryInvolution F 2 f)) [Fact ((ζ : F) ≠ 0)]
  {K : Type} [Field K] [CharP K 2] (h : UnitaryFieldData 2 f K)
  (ε : Xg h ≃* SU (unitaryInvolution F 2 f) 4)

theorem overgroup_Xg (hε : (Psy h).map ε.toMonoidHom = unU hF 4) {M : Subgroup (Xg h)}
    (h1 : Subgroup.normalizer (Psy h : Set (Xg h)) ≤ M) (h2 : M ≠ ⊤)
    (h3 : M ≠ Subgroup.normalizer (Psy h : Set (Xg h))) :
    M = (unSystem hF ζ).P₁.map ε.symm.toMonoidHom ∨
      M = (unSystem hF ζ).P₂.map ε.symm.toMonoidHom := by
  set R := unSystem hF ζ with hR
  have hNU : Subgroup.normalizer ((unU hF 4 : Subgroup _) : Set _) = R.B := BN.normalizer_U_eq_B R
  have hB : R.B ≤ M.map ε.toMonoidHom := by
    rw [← hNU, ← hε, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono h1
  have hback : ∀ A : Subgroup (SU (unitaryInvolution F 2 f) 4),
      (A.map ε.symm.toMonoidHom).map ε.toMonoidHom = A := fun A => by
    rw [Subgroup.map_map]
    ext x
    simp
  have hback' : (M.map ε.toMonoidHom).map ε.symm.toMonoidHom = M := by
    rw [Subgroup.map_map]
    ext x
    simp
  rcases BN.eq_B_or_P_or_top R hB with e | ⟨i, e⟩ | e
  · exfalso
    apply h3
    rw [← hback', e, ← hNU, ← hε, ← Subgroup.map_equiv_normalizer_eq, Subgroup.map_map]
    ext x
    simp
  · cases i
    · right
      rw [← hback', e]
      rfl
    · left
      rw [← hback', e]
      rfl
  · exfalso
    apply h2
    rw [← hback', e, Subgroup.map_top_of_surjective _ ε.symm.surjective]

theorem yamStd_of_eps (hε : (Psy h).map ε.toMonoidHom = unU hF 4) :
    IsSimpleGroup (Xg h) ∧ YamStd (Xg h) (Psy h) (Pt h) (Ln h) := by
  have hS : IsSimpleGroup (Xg h) := ε.isSimpleGroup_congr.2 (isSimpleGroup_unSU hF)
  refine ⟨hS, ?_⟩
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have : Fact ((ζ : F) ≠ 0) := ⟨hζ⟩
  have := isSimpleGroup_unSU hF
  have hU := isSylowTwoOf_unU hF
  have YR := BN.yamStd (unSystem hF ζ) hU
  have YR' := yamStd_map ε.symm YR
  have hU' : (unSystem hF ζ).U.map ε.symm.toMonoidHom = Psy h := by
    rw [show (unSystem hF ζ).U = unU hF 4 from rfl, ← hε, Subgroup.map_map]
    ext x
    simp
  rw [hU'] at YR'
  have hPt := overgroup_Xg hF ζ h ε hε (normalizer_Psy_le_Pt h) (Pt_ne_top h) (Pt_ne_normalizer h)
  have hLn := overgroup_Xg hF ζ h ε hε (normalizer_Psy_le_Ln h) (Ln_ne_top h) (Ln_ne_normalizer h)
  have hne := Pt_ne_Ln h
  rcases hPt with e1 | e1 <;> rcases hLn with e2 | e2
  · exact absurd (e1.trans e2.symm) hne
  · rw [e1, e2]
    exact YR'
  · rw [e1, e2]
    exact yamStd_swap YR'
  · exact absurd (e1.trans e2.symm) hne

end CFSG.Quasithin.H13.F431.Un.OL
