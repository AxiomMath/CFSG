module

public import CFSG.LocalAnalysis.StandardType.GGFamInnerTree
public import CFSG.LocalAnalysis.StandardType.GGFamIsolation
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacDispatch
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTypeA

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
  CFSG.RankThree.Classical2
open scoped MatrixGroups commutatorElement

theorem fam_inner_nonA_strongRecogIn
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1) (i : KernelComponent (famCharHom a))
    (hnA : ¬ (1 ≤ compRank (componentRoots (famCharHom a) i) ∧
      (componentRoots (famCharHom a) i).ncard = compRank (componentRoots (famCharHom a) i) *
        (compRank (componentRoots (famCharHom a) i) + 1)))
    (hinner : twistInner (componentRoots (famCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (famCharHom a) i)])) :
    GGStrongRecogIn (fun t k =>
        (t = .POmegaPlus ∧ k = compRank (componentRoots (famCharHom a) i) ∧
          4 ≤ compRank (componentRoots (famCharHom a) i) ∧
          (componentRoots (famCharHom a) i).ncard = 2 * compRank (componentRoots (famCharHom a) i) *
            (compRank (componentRoots (famCharHom a) i) - 1)) ∨
        (t = .E6 ∧ k = 0 ∧ compRank (componentRoots (famCharHom a) i) = 6 ∧
          (componentRoots (famCharHom a) i).ncard =
            eRootCount (compRank (componentRoots (famCharHom a) i))) ∨
        (t = .E7 ∧ k = 0 ∧ compRank (componentRoots (famCharHom a) i) = 7 ∧
          (componentRoots (famCharHom a) i).ncard =
            eRootCount (compRank (componentRoots (famCharHom a) i))) ∨
        (t = .E8 ∧ k = 0 ∧ compRank (componentRoots (famCharHom a) i) = 8 ∧
          (componentRoots (famCharHom a) i).ncard =
            eRootCount (compRank (componentRoots (famCharHom a) i)))) 2
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i))
      ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) := by
  classical
  obtain ⟨u₀, hu₀⟩ := h1
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp (hap u₀) hu₀
  have hp2 : p ≠ 2 := by
    rw [ringChar.eq L 2] at hℓp
    exact hℓp.symm
  obtain ⟨N, b, j, hN, hN2, hbN, hsel⟩ :=
    exists_isolating_element hτ a hp hp2 hap i
  have hpN : (N : L) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne hN (by rw [ringChar.eq L 2]; exact Ne.symm hN2)
  have hρ : ∀ γ ∈ kernelRoots (famCharHom a), S.ρ γ ∈ kernelRoots (famCharHom a) :=
    fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ
  rcases hτ with rfl | rfl | rfl
  ·
    obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
      exists_cand_of_class kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card S hN hpN hbN j
    rw [hsel] at hrank hncard
    have hshape := e6_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA | hD | hE
    · exact (hnA hA).elim
    · have h := fam_strongRecogIn_of_dClass (Or.inr (Or.inl rfl)) kacE6 facts_E6 e6_tree e6_adj
        e6_check e6_lt e6_card e6_dcount e6_dtrees (fun {F} _ x y h => e6_frames x y h) S hN hpN hρ
        hbN i j hsel hD.1 hD.2 hinner
      rw [ringChar.eq L 2] at h
      exact h.mono (fun t k h' => Or.inl ⟨h'.1, h'.2, hD.1, hD.2⟩)
    · have h := fam_strongRecogIn_of_eClass (Or.inr (Or.inl rfl)) kacE6 facts_E6 e6_tree e6_adj
        e6_check e6_lt e6_card e6_ecount e6_etrees e6_elen (fun {F} _ x y h => e6_frames x y h) S hN
        hpN hρ hbN i j hsel hE.1 hE.2 hinner
      rw [ringChar.eq L 2] at h
      refine h.mono (fun t k h' => ?_)
      rcases h' with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact Or.inr (Or.inl ⟨h1, h2, h3, hE.2⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, hE.2⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, hE.2⟩))
  ·
    obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
      exists_cand_of_class kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card S hN hpN hbN j
    rw [hsel] at hrank hncard
    have hshape := e7_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA | hD | hE
    · exact (hnA hA).elim
    · have h := fam_strongRecogIn_of_dClass (Or.inr (Or.inr (Or.inl rfl))) kacE7 facts_E7 e7_tree
        e7_adj e7_check e7_lt e7_card e7_dcount e7_dtrees (fun {F} _ x y h => e7_frames x y h) S hN
        hpN hρ hbN i j hsel hD.1 hD.2 hinner
      rw [ringChar.eq L 2] at h
      exact h.mono (fun t k h' => Or.inl ⟨h'.1, h'.2, hD.1, hD.2⟩)
    · have h := fam_strongRecogIn_of_eClass (Or.inr (Or.inr (Or.inl rfl))) kacE7 facts_E7 e7_tree
        e7_adj e7_check e7_lt e7_card e7_ecount e7_etrees e7_elen
        (fun {F} _ x y h => e7_frames x y h) S hN hpN hρ hbN i j hsel hE.1 hE.2 hinner
      rw [ringChar.eq L 2] at h
      refine h.mono (fun t k h' => ?_)
      rcases h' with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact Or.inr (Or.inl ⟨h1, h2, h3, hE.2⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, hE.2⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, hE.2⟩))
  ·
    obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
      exists_cand_of_class kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card S hN hpN hbN j
    rw [hsel] at hrank hncard
    have hshape := e8_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA | hD | hE
    · exact (hnA hA).elim
    · have h := fam_strongRecogIn_of_dClass (Or.inr (Or.inr (Or.inr rfl))) kacE8 facts_E8 e8_tree
        e8_adj e8_check e8_lt e8_card e8_dcount e8_dtrees (fun {F} _ x y h => e8_frames x y h) S hN
        hpN hρ hbN i j hsel hD.1 hD.2 hinner
      rw [ringChar.eq L 2] at h
      exact h.mono (fun t k h' => Or.inl ⟨h'.1, h'.2, hD.1, hD.2⟩)
    · have h := fam_strongRecogIn_of_eClass (Or.inr (Or.inr (Or.inr rfl))) kacE8 facts_E8 e8_tree
        e8_adj e8_check e8_lt e8_card e8_ecount e8_etrees e8_elen
        (fun {F} _ x y h => e8_frames x y h) S hN hpN hρ hbN i j hsel hE.1 hE.2 hinner
      rw [ringChar.eq L 2] at h
      refine h.mono (fun t k h' => ?_)
      rcases h' with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact Or.inr (Or.inl ⟨h1, h2, h3, hE.2⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, hE.2⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, hE.2⟩))

theorem fam_inner_nonA_strongRecog
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1) (i : KernelComponent (famCharHom a))
    (hnA : ¬ (1 ≤ compRank (componentRoots (famCharHom a) i) ∧
      (componentRoots (famCharHom a) i).ncard = compRank (componentRoots (famCharHom a) i) *
        (compRank (componentRoots (famCharHom a) i) + 1)))
    (hinner : twistInner (componentRoots (famCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (famCharHom a) i)])) :
    GGStrongRecog 2
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i))
      ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) :=
  (fam_inner_nonA_strongRecogIn hτ S hp hT hap h1 i hnA hinner).mono (fun t k h => by
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide)

theorem langFamRatFieldSL_inner
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1) (i : KernelComponent (famCharHom a))
    (hnA : ¬ (1 ≤ compRank (componentRoots (famCharHom a) i) ∧
      (componentRoots (famCharHom a) i).ncard = compRank (componentRoots (famCharHom a) i) *
        (compRank (componentRoots (famCharHom a) i) + 1)))
    (hinner : twistInner (componentRoots (famCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (famCharHom a) i)]))
    (hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i)) :
    CFSG.StandardType.GGCompFieldAtSL
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i))
      (rationalComponentM S.ρ S.Γ (famCharHom a) i) := by
  obtain ⟨-, t, n, f, hmodel, hpow, ht⟩ :=
    fam_inner_nonA_strongRecog hτ S hp hT hap h1 i hnA hinner
  rw [← hpow]
  exact ggCompFieldAtSL_of_lieModel
    (X := rationalComponentM S.ρ S.Γ (famCharHom a) i)
    (ggStrongRecog_open_isQuasisimple hq) hmodel ht

end CFSG.StandardType.TableCRes
