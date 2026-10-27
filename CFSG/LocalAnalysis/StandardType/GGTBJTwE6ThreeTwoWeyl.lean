module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6ThreeTwoWeylAux

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootTorus CFSG.StandardType.LangRat
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn
  CFSG.RankThree.Chevalley.EvenF4QPlus CFSG.RankThree.PartOne.KE6
  CFSG.HardMathSupport.Timmesfeld.RootAut
open scoped commutatorElement MatrixGroups

theorem tw1w_three_le_compRank
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) (hq2 : S.D.q = 2) (hρ : ∀ γ, S.ρ γ = -γ)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ i, a i ^ 3 = 1) (h1 : rootDiagUnit Tag.E6 a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hQS : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    3 ≤ compRank (componentRoots (rootCharHom a) i) := by
  by_contra hle
  rw [not_le] at hle
  have h3 : ((3 : ℕ) : L) ≠ 0 :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerAbs.natCast_three_ne_zero_of_charTwo
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hfinΨ : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1.1
  have F := kac_facts h3 hap
  have hstab : ∀ γ ∈ componentRoots (rootCharHom a) i,
      S.ρ γ ∈ componentRoots (rootCharHom a) i := by
    intro γ hγ
    rw [hρ γ]
    exact hΨ.neg_mem γ hγ
  have hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
    componentOrbitLength_eq_one hfinΨ hstab
  have hne : (componentRoots (rootCharHom a) i).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rcases F.sizes i with h' | h' | h'
    · rw [h] at h'; simp at h'
    · rw [h] at h'; simp at h'
    · rw [h] at h'; simp only [Set.ncard_empty] at h'; omega
  have h26 := tw1w_ncard_eq_two_or_six (Or.inr (Or.inl rfl)) hΨ hne (by omega)
  rcases h26 with h2 | h6
  ·
    exfalso
    have h1rank : compRank (componentRoots (rootCharHom a) i) = 1 := F.rank_one i h2
    obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
    obtain ⟨K, -, -, g, -, -, hKcard, hK4, -⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn.exists_slCover_of_rankOne
        S hT i h1rank h2 hQS hr hchar he hq
    rw [hs1] at hKcard
    have hpow : r ^ (e * 1) = 2 := by rw [Nat.mul_one, ← hq, hq2]
    omega
  ·
    exfalso
    have hn6 : (componentRoots (rootCharHom a) i).ncard = 6 := h6
    obtain ⟨-, himg, -⟩ := outer_componentOrbitLength_spec S hT i
    rw [hs1, Function.iterate_one] at himg
    exact orbit_ne_of_A2_quasisimple S hq2 hT i (F.frame i hn6) (F.glue i hn6) hQS himg

theorem tw1w_weylPoint_mem
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) (hq2 : S.D.q = 2) (hAlg : S.IsAlgebraic)
    (hρ : ∀ γ, S.ρ γ = -γ)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ i, a i ^ 3 = 1) (h1 : rootDiagUnit Tag.E6 a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hQS : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    ∀ γ ∈ componentRoots (rootCharHom a) i,
      rootSL2 Tag.E6 L γ WSL ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  intro γ hγ
  have hd3 : rootDiagUnit Tag.E6 a ^ 3 = 1 := by
    rw [rootDiagUnit_pow, show a ^ 3 = 1 from funext fun i => hap i, rootDiagUnit_one]
  have h3 := tw1w_three_le_compRank S hq2 hρ hT hap h1 i hQS
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  obtain ⟨ψ, σ, hψ, hnorm, hsub⟩ := QTwoCav.exists_A3_subframe_E6 S hq2 hd3 i h3
  obtain ⟨α, -, hαmem, -, -, hαR, -⟩ :=
    QTwoCav.exists_orthogonal_weyl_pair_of_subframe S (Or.inl rfl) hq2 hAlg
      (fun γ _ => hρ γ) i (by norm_num) hψ hnorm hsub
  have hconn := tw1w_class_connected hΨ hαmem hγ
  induction hconn with
  | refl => exact hαR
  | tail _ hbc ih =>
      exact tw1w_weyl_mem_of_adj S hq2 hAlg hρ hT i hbc.1 hbc.2.1 hbc.2.2 (ih hbc.1)

end CFSG.StandardType

end
