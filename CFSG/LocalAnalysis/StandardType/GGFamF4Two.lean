module

public import CFSG.LocalAnalysis.StandardType.GGFamF4B2
public import CFSG.LocalAnalysis.StandardType.GGFamF4RankThree
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.StandardType.GGFamF4Orbit
import CFSG.LocalAnalysis.StandardType.GGFamTypeACovers
import CFSG.LocalAnalysis.StandardType.GGFamTypeAFrames
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.SelectedLiteralPart1
import CFSG.LocalAnalysis.StandardType.GGF4OrderThreeLabel
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GSympLabel

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.F4ExplicitPos.A2Actual CFSG.StandardType.F4ExplicitPos.SelectedLiteral
  CFSG.RankThree.E6 CFSG.RankThree.PartOne.KF4

theorem famF4_b2_two
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ} (S : LangSetup Tag.F4 L p₀)
    (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type} {a : ι → Fin Tag.F4.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit Tag.F4 (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (h1 : ∃ u, rootDiagUnit Tag.F4 (a u) ≠ 1) (i : KernelComponent (famCharHom a))
    (hB2 : FamF4B2Shape (componentRoots (famCharHom a) i)) (hq2 : S.D.q = 2) :
    CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) ∧
      GGHasLabel ⟨.B2der, 0, 1⟩ (↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i)) := by
  obtain ⟨hQ, hZ, ⟨eR⟩⟩ := famF4_b2_two_equivAlt6 S hp hp2 hT hap h1 i hB2 hq2
  exact ⟨hQ, CFSG.LocalAnalysis.GLTheoremA.Y10GSympLabel.ggHasLabel_b2der
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans eR)⟩

theorem famF4_rankThree_two
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ} (S : LangSetup Tag.F4 L p₀)
    (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type} {a : ι → Fin Tag.F4.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit Tag.F4 (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (i : KernelComponent (famCharHom a))
    (hr3 : FamF4B3Shape (componentRoots (famCharHom a) i) ∨
      FamF4C3Shape (componentRoots (famCharHom a) i)) (hq2 : S.D.q = 2) :
    CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) ∧
      GGHasLabel ⟨.C, 3, 1⟩ (↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i)) := by
  obtain ⟨hQ, e, -, hqe, hLie⟩ := famF4_rankThree_lieModel S hp hp2 hT hap i hr3
  obtain rfl : e = 1 :=
    Nat.pow_right_injective le_rfl (show 2 ^ e = 2 ^ 1 by rw [← hqe, hq2, pow_one])
  refine ⟨hQ, ?_⟩
  rcases hLie with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact ggHasLabel_C_of_statedClassicalModel h
  all_goals exact absurd h0 (by decide)

theorem famF4_not_isQuasisimple_pair_two
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ} (S : LangSetup Tag.F4 L p₀)
    (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type} {a : ι → Fin Tag.F4.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit Tag.F4 (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (i : KernelComponent (famCharHom a))
    (hA1 : FamF4PairShape (componentRoots (famCharHom a) i)) (hq2 : S.D.q = 2) :
    ¬ CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) := by
  intro hQS
  have hρ : ∀ γ ∈ kernelRoots (famCharHom a), S.ρ γ ∈ kernelRoots (famCharHom a) :=
    fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ
  obtain ⟨hr1, hn⟩ := famF4_pairShape_rankCard hA1
  obtain ⟨K, -, -, f, -, hKcard, hqeq, -, hK4, -, -, -⟩ :=
    fam_exists_slCover_rankOne S hρ i hr1 hn hQS
  rw [(famF4_orbit S hp hp2 hT hap i).2, hq2, pow_one] at hqeq
  omega

theorem famF4_not_isQuasisimple_a2_two
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ} (S : LangSetup Tag.F4 L p₀)
    (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type} {a : ι → Fin Tag.F4.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit Tag.F4 (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (i : KernelComponent (famCharHom a))
    (hA2 : FamF4LongA2Shape (componentRoots (famCharHom a) i) ∨
      FamF4ShortA2Shape (componentRoots (famCharHom a) i))
    (hq2 : S.D.q = 2) (hρ : ∀ γ, IsRoot Tag.F4 γ → S.ρ γ = -γ) :
    ¬ CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) := by
  intro hQS
  have hρK : ∀ γ ∈ kernelRoots (famCharHom a), S.ρ γ ∈ kernelRoots (famCharHom a) :=
    fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ
  have hs1 : componentOrbitLength S.ρ (componentRoots (famCharHom a) i) = 1 :=
    (famF4_orbit S hp hp2 hT hap i).2
  have tail : ∀ {ψ : Matrix.SpecialLinearGroup (Fin 3) L →* ModGL Tag.F4 L}
      {σ : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ},
      IsSLFrame ψ σ → componentRoots (famCharHom a) i = frameRoots σ → False := by
    intro ψ σ hψ hΨ
    have hπ : ∀ x y : Fin 3, x ≠ y →
        (S.ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ))^[componentOrbitLength S.ρ
          (componentRoots (famCharHom a) i)] (σ x y) =
          σ ((1 : Equiv.Perm (Fin 3)) y) ((1 : Equiv.Perm (Fin 3)) x) := by
      intro x y hxy
      rw [hs1, Function.iterate_one, hρ (σ x y) (hψ.isRoot x y hxy),
        Equiv.Perm.one_apply]
      exact (hψ.neg x y).symm
    have h32 := fam_not_unitaryFrame_three_two S hρK i (by norm_num : 3 ≤ 3) hψ hΨ
      (1 : Equiv.Perm (Fin 3)) hπ Nat.prime_two inferInstance one_pos
      (show S.D.q = 2 ^ 1 by rw [hq2, pow_one]) hQS
    rw [hs1] at h32
    exact h32 (by norm_num)
  rcases hA2 with hLong | hShort
  · obtain ⟨v, hv⟩ := hLong
    set ρA :=
      (MulAut.conj (canonicalRep (coxeterSystem Tag.F4) L v)).toMonoidHom.comp
        (f4rhoLong_actual (K := L)) with hρA
    set r : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ :=
      fun x y => v • chainRoot f4chainLong x y with hr
    have hψ : IsSLFrame ρA r := by
      rw [hρA, hr]
      exact isSLFrame_long_actual_transport (L := L) v
    have hΨ : componentRoots (famCharHom a) i = frameRoots r := by
      rw [hv, hr, ← frameRoots_f4chainLong_smul (v := v)]
    exact tail hψ hΨ
  · obtain ⟨v, hv⟩ := hShort
    set ρA :=
      (MulAut.conj (canonicalRep (coxeterSystem Tag.F4) L v)).toMonoidHom.comp
        (f4rhoShort_actual (K := L)) with hρA
    set r : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ :=
      fun x y => v • f4ShortSigma x y with hr
    have hψ : IsSLFrame ρA r := by
      rw [hρA, hr]
      exact isSLFrame_short_actual_transport (L := L) v
    have hΨ : componentRoots (famCharHom a) i = frameRoots r := by
      rw [hv, hr, ← frameRoots_f4ShortSigma_smul (v := v)]
    exact tail hψ hΨ

end CFSG.StandardType.TableCRes
