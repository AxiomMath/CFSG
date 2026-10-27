module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeEnvelopePieces
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPReduction

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE CFSG.Timmesfeld CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.StandardType CFSG.StandardType.GGFinModel

theorem rckNC_twistKind_of_A {τ : Tag} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* GGLˣ} {i : KernelComponent χ}
    (h2 : 2 ≤ compRank (componentRoots χ i))
    (hn : (componentRoots χ i).ncard =
      compRank (componentRoots χ i) * (compRank (componentRoots χ i) + 1)) :
    twistKind ρ χ i = .inner ∨ twistKind ρ χ i = .suN := by
  unfold twistKind
  split_ifs with c1 c2 c3 c4
  · exact Or.inl rfl
  · exfalso
    rcases c2 with ⟨h6, h72⟩ | ⟨h4, h24, -⟩
    · rw [hn, h6] at h72
      omega
    · rw [hn, h4] at h24
      omega
  · exfalso
    obtain ⟨h4, h⟩ := c3
    rw [hn] at h
    generalize compRank (componentRoots χ i) = r at h4 h
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 4 := ⟨r - 4, by omega⟩
    have hk : k + 4 - 1 = k + 3 := by omega
    rw [hk] at h
    nlinarith [h]
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem rckNC_twistKind_of_B3 {τ : Tag} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* GGLˣ} {i : KernelComponent χ}
    (hr : compRank (componentRoots χ i) = 3) (hn : (componentRoots χ i).ncard = 18) :
    twistKind ρ χ i = .inner := by
  unfold twistKind
  split_ifs with c1 c2 c3 c4
  · rfl
  · exfalso
    rcases c2 with ⟨h6, -⟩ | ⟨h4, -, -⟩ <;> omega
  · exfalso
    obtain ⟨h4, -⟩ := c3
    omega
  · exfalso
    obtain ⟨-, h⟩ := c4
    rw [hr, hn] at h
    omega
  · rfl

section Shape


theorem rckF4_class_shape {p : ℕ} (hp : p.Prime) (hp2 : p % 2 = 1) {L : Type} [Field L]
    [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.F4 L p₀) (hpL : ((p : ℕ) : L) ≠ 0)
    {a : Fin Tag.F4.rank → Lˣ} (hTp : rootDiagUnit Tag.F4 a ^ p = 1)
    (h1 : rootDiagUnit Tag.F4 a ≠ 1) (i : KernelComponent (rootCharHom a)) :
    (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) + 1)) ∨
      (compRank (componentRoots (rootCharHom a) i) = 2 ∧
        (componentRoots (rootCharHom a) i).ncard = 8) ∨
      (compRank (componentRoots (rootCharHom a) i) = 3 ∧
        (componentRoots (rootCharHom a) i).ncard = 18) := by
  classical
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · exact Or.inl hA
  obtain ⟨v, μ, x, c, hμ, hc, hcomp, hlen, hroots, hrank, hncard⟩ :=
    exists_cand_of_class kacF4 facts_F4 f4_tree f4_adj f4_check f4_lt f4_card S hp hpL hTp i
  have hnonA' : ¬ (1 ≤ c.length ∧ kacCount Tag.F4 ![2, 3, 4, 2]
      (c.map (idxNode (r := Tag.F4.rank))).toFinset = c.length * (c.length + 1)) := by
    rw [hrank, hncard] at hA
    exact hA
  rcases f4_nonA_cases c hc hlen hnonA' with rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl ⟨by rw [hrank]; rfl, by rw [hncard]; exact kacCount_F4_B2⟩)
  · exact Or.inr (Or.inr ⟨by rw [hrank]; rfl, by rw [hncard]; exact kacCount_F4_B3⟩)
  · exact Or.inr (Or.inr ⟨by rw [hrank]; rfl, by rw [hncard]; exact kacCount_F4_C3⟩)
  · exact (not_comp_eq_B4_F4_odd hp2 hμ hcomp).elim
  · exfalso
    apply h1
    have hall : ∀ j, (Pi.single j 1 : Fin Tag.F4.rank → ℤ) ∈ componentRoots (rootCharHom a) i := by
      intro j
      rw [hroots, rootsOf_eq_parabolicRoots kacF4 facts_F4 (J := Set.univ) (by decide)
        (fun j => by simp only [Set.mem_univ, iff_true]; revert j; decide)]
      exact ⟨v⁻¹ • Pi.single j 1, ⟨IsRoot.smul (isRoot_single _ j) v⁻¹, fun i hi =>
        (hi (Set.mem_univ i)).elim⟩, smul_inv_smul v _⟩
    have ha : a = 1 := by
      funext j
      obtain ⟨hker, -⟩ := hall j
      have h1' : rootChar a (Pi.single j 1) = 1 := hker.2
      rw [CFSG.RankThree.PartOne.KE.CTTorus.rootChar_single] at h1'
      exact h1'
    rw [ha]
    exact rootDiagUnit_one

end Shape

section Holds

open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (rootDiagUnit_pow_eq_one_of_forall)

theorem rckF4Envelope_holds : RCKF4Envelope := by
  intro p hp hp2 S a _ ha1 hap i _
  classical
  have hp2' : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
  have hℓp : ringChar GGL ≠ p := ringChar_ne_of_pow_eq_one hp hap ha1
  have hpL : ((p : ℕ) : GGL) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  rcases rckF4_class_shape hp hp2' S hpL hTp ha1 i with ⟨h1, hA⟩ | ⟨hr, hn⟩ | ⟨hr, hn⟩
  ·
    right
    left
    unfold RCKClassicalShape
    by_cases hr1 : compRank (componentRoots (rootCharHom a) i) = 1
    · exact Or.inl hr1
    · have h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
      rcases rckNC_twistKind_of_A (ρ := S.ρ) h2 hA with hk | hk
      · exact Or.inr (Or.inl ⟨hk, h2, hA⟩)
      · exact Or.inr (Or.inr (Or.inl hk))
  ·
    by_cases hQ : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)
    · right
      left
      unfold RCKClassicalShape
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hr, hn, hQ⟩))))
    · right
      right
      unfold RCKSmallShape
      exact Or.inr ⟨rfl, hr, hn, by omega⟩
  ·
    right
    left
    unfold RCKClassicalShape
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rckNC_twistKind_of_B3 (ρ := S.ρ) hr hn, hr, hn⟩)))

end Holds

end CFSG.StandardType.RCKRP

end
