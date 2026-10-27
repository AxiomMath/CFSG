module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormFixedFree
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLLinePSL
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBRefl
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosureRefl
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem ggWNormConcl_of_linear_diagonal {K : Type} [Field K] [Finite K] [CharP K 2]
    {d p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1)
    (hd : 5 ≤ d) {L' : Type} [Group L'] [Finite L']
    {π : SpecialLinearGroup (Fin d) K →* L'} (hπs : Function.Surjective π)
    (hπker : ∀ g, π g = 1 → g ∈ scalars d K)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (h3 : p ^ 3 ≤ Nat.card A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, TypeANbrDvd.ActsDiag π a t)
    [Fact p.Prime] {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} (hM : GGIsWeylMatrix M)
    {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥A ≃+ V) (φ : Λ → MulAut ↥A)
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hlin : ∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i)
    (hgen : ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      Subgroup.closure (Set.range φ))
    {s : MulAut ↥A} (hs : s ∈ ggInduced (⊤ : Subgroup (MulAut L')) A) :
    GGWNormConcl ι φ h α s := by
  classical
  have : Finite (MulAut L') :=
    Finite.of_injective (fun f : MulAut L' => (f : L' → L')) DFunLike.coe_injective
  have : Finite V := Finite.of_injective ι.symm ι.symm.injective
  have : Nontrivial ↥A := Finite.one_lt_card_iff_nontrivial.mp
    (lt_of_lt_of_le (Nat.one_lt_pow (by norm_num : 3 ≠ 0) hp.one_lt) h3)
  have : Nontrivial V := ι.injective.nontrivial
  have hN : ∀ σ : Equiv.Perm (Fin d), NbrInnerWeylA.permConj π σ ∈
      Subgroup.normalizer (A : Set (MulAut L')) :=
    TypeANbrDvd.permConj_mem_normalizer_of_selfCent hπs hπker hA.2 hsc hdiag
  let ρ := TypeANbrDvd.permAut π A hN
  have hρ : Function.Injective ρ :=
    TypeANbrDvd.permAut_injective hp hp2 hpK (by omega) hπs hπker hA hsc hdiag hN
  have hρW : ρ.range = ggAutomizer (MulAut.conj : L' →* MulAut L').range A :=
    (TypeANbrDvd.ggAutomizer_eq_range_permAut hp hp2 hpK hπs hπker hA hsc hdiag hN).symm
  have hsw : ∀ i j, i ≠ j → GGIsReflection p (ρ (Equiv.swap i j)) := by
    intro i j hij
    obtain ⟨_, _, _, _, hr⟩ :=
      TypeANbrDvd.permAut_swap_mem_reflSet hp hp2 hpK (by omega) hπs hπker hA hsc hdiag hN hij
    exact hr
  have hfixed : ∀ a : ↥A, (∀ σ, ρ σ a = a) → a = 1 := by
    intro a ha
    obtain ⟨t, hat⟩ := hdiag a a.2
    apply Subtype.ext
    apply hat.eq_one_of_conj_perm (by omega) hπs hπker
    intro σ
    have he := congrArg Subtype.val (ha σ⁻¹)
    rw [TypeANbrDvd.permAut_apply, ggConjAut_apply] at he
    exact he
  have : (MulAut.conj : L' →* MulAut L').range.Normal :=
    RootCentExc.normal_range_mulAutConj
  apply ggWNormConcl_of_symmetric_fixedFree hp2 hd ι φ h α hM hC hpair hlin
    ρ hρ hsw hfixed (hρW.trans hgen)
  rw [hρW]
  exact mem_normalizer_ggAutomizer_of_mem_ggInduced_of_normal hs

namespace TypeA

theorem ggTorusWNormSC_singular_prime {K : Type} [Field K] [Finite K] [CharP K 2]
    {d p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : p ∣ Nat.card K - 1)
    (hdp : d = p) :
    GGTorusWNormSC p (projectiveSL d K) (Set.range (conjAut d K)) := by
  have hp2 : p ≠ 2 := by omega
  have hd : 5 ≤ d := by omega
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc _ Λ _ _ M C V _ _ ι φ h α
    hM hC hpair hlin hgen s hs
  have hcard : p ^ (d / p + 1) < Nat.card A := by
    have he : p ^ (d / p + 1) < p ^ 3 := by
      rw [hdp, Nat.div_self hp.pos]
      exact Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    exact he.trans_le h3
  obtain ⟨π, hπs, hπker, hdiag⟩ :=
    LinUnitL.exists_model_of_pow_lt_card hp hpK hd hψ hker hperf hA hAI hcard
  exact ggWNormConcl_of_linear_diagonal hp hp2 hpK hd hπs hπker hA h3 hsc hdiag
    hM hC ι φ h α hpair hlin hgen hs

end TypeA

theorem ggTorusWNormSC_linear_singular_prime {K : Type} [Field K] [Finite K] [CharP K 2]
    {d p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : p ∣ Nat.card K - 1)
    (hdp : d = p) :
    GGTorusWNormSC p (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk _) Set.univ) := by
  exact ggTorusWNormSC_of_mulEquiv (TypeA.recipeEquiv d K)
    (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
    (TypeA.ggTorusWNormSC_singular_prime hp hp5 hpK hdp)

theorem largeEvenLabelAll_wnorm_linear_singular_prime {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hp5 : 5 ≤ p) (ht : lab.tag = .A)
    (hdp : lab.rank + 1 = p) (hpq : p ∣ 2 ^ lab.n - 1) :
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
  exact ggTorusWNormSC_linear_singular_prime hp hp5 (by rwa [hK]) hdp

end CFSG.StandardType
