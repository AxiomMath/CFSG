module

public import CFSG.LocalAnalysis.StandardType.GGFamSLRecogDefs
public import CFSG.LocalAnalysis.StandardType.GGFamRatComp
public import CFSG.LocalAnalysis.StandardType.GGFamTameLang
public import CFSG.LocalAnalysis.StandardType.GGFamTameRangeSpan
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.InnerCover
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField

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

theorem fam_exists_inner_cover_le
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ)
    (i : KernelComponent χ)
    (hinner : twistInner (componentRoots χ i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots χ i)])) :
    ∃ σ : L ≃+* L, Finite ↥(fixSubfield σ) ∧
      Nat.card ↥(fixSubfield σ) = S.D.q ^ componentOrbitLength S.ρ
        (componentRoots χ i) ∧
      ∃ f : ↥(componentRootSpan (fixSubfield σ) χ i) →* ModGL τ L,
        rationalComponentM S.ρ S.Γ χ i ≤ f.range ∧
        f.ker ≤ Subgroup.center ↥(componentRootSpan (fixSubfield σ) χ i) ∧
        (⁅componentRootSpan (fixSubfield σ) χ i,
            componentRootSpan (fixSubfield σ) χ i⁆ =
            componentRootSpan (fixSubfield σ) χ i →
          f.range ≤ rationalComponentM S.ρ S.Γ χ i) ∧
        f.range ≤ rootSpan τ L (rationalRootsM S.ρ χ i) ⊓ S.D.model := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := fam_componentOrbitLength_spec S hρ i
  set s := componentOrbitLength S.ρ (componentRoots χ i) with hsdef
  haveI : NeZero s := ⟨hs0.ne'⟩
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := fam_exists_untwist S hρ i hs0 hinner
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  have hσ' : ∀ c, σ c = c ^ (r ^ (e * s)) := fun c => by rw [hσ, hq, ← pow_mul]
  obtain ⟨hfinK, hKcard⟩ := finite_card_fixSubfield (L := L) (r := r) (n := e * s)
    (Nat.mul_pos he hs0) σ hσ'
  have hsL : ∃ u : Lˣ, u ^ 2 ≠ 1 := by
    obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset L)
    have hc0 : c ≠ 0 := fun h => hc (by simp [h])
    refine ⟨Units.mk0 c hc0, fun h => hc ?_⟩
    have h2 : c ^ 2 = 1 := by simpa using congrArg (fun x : Lˣ => (x : L)) h
    have h3 : (c - 1) * (c + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h | h
    · simp [sub_eq_zero.1 h]
    · simp [eq_neg_of_add_eq_zero_left h]
  obtain ⟨f, hf1, hker, hf2, hf4⟩ :=
    fam_rationalComponent_eq_range_componentRootSpan_le S hρ i hs hmin σ z hnorm hz hsL
  exact ⟨σ, hfinK, by rw [hKcard, hq, ← pow_mul], f, hf1, hker, hf2, hf4⟩

theorem fam_exists_inner_cover
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ)
    (i : KernelComponent χ)
    (hinner : twistInner (componentRoots χ i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots χ i)])) :
    ∃ σ : L ≃+* L, Finite ↥(fixSubfield σ) ∧
      Nat.card ↥(fixSubfield σ) = S.D.q ^ componentOrbitLength S.ρ
        (componentRoots χ i) ∧
      ∃ f : ↥(componentRootSpan (fixSubfield σ) χ i) →* ModGL τ L,
        rationalComponentM S.ρ S.Γ χ i ≤ f.range ∧
        f.ker ≤ Subgroup.center ↥(componentRootSpan (fixSubfield σ) χ i) ∧
        (⁅componentRootSpan (fixSubfield σ) χ i,
            componentRootSpan (fixSubfield σ) χ i⁆ =
            componentRootSpan (fixSubfield σ) χ i →
          f.range ≤ rationalComponentM S.ρ S.Γ χ i) := by
  obtain ⟨σ, hfin, hcard, f, hf1, hker, hf2, -⟩ := fam_exists_inner_cover_le S hρ i hinner
  exact ⟨σ, hfin, hcard, f, hf1, hker, hf2⟩

theorem fam_strongRecogIn_of_inner
       {P : StatedLieTag → ℕ → Prop} {τ : Tag} {L : Type}
    [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ)
    (hinner : twistInner (componentRoots χ i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots χ i)]))
    (hrec : ∀ K : Subfield L, Finite ↥K →
      Nat.card ↥K = S.D.q ^ componentOrbitLength S.ρ (componentRoots χ i) →
      GGStrongRecogIn P (ringChar L) (Nat.card ↥K)
        ↥(componentRootSpan K χ i)) :
    GGStrongRecogIn P (ringChar L)
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots χ i))
      ↥(rationalComponentM S.ρ S.Γ χ i) := by
  classical
  obtain ⟨σ, hfin, hcard, f, hf1, hker, hf2⟩ := fam_exists_inner_cover S hρ i hinner
  have hrecσ := hrec (fixSubfield σ) hfin hcard
  have hCperf : ⁅componentRootSpan (fixSubfield σ) χ i,
      componentRootSpan (fixSubfield σ) χ i⁆ =
      componentRootSpan (fixSubfield σ) χ i :=
    Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hrecσ.1)
  have hRf : f.range = rationalComponentM S.ρ S.Γ χ i :=
    le_antisymm (hf2 hCperf) hf1
  rw [hcard] at hrecσ
  exact ggStrongRecogIn_of_range hrecσ f hker hRf

end CFSG.StandardType.TableCRes
