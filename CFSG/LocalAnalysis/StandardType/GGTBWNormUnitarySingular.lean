module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormFixedFree
public import CFSG.LocalAnalysis.StandardType.GGTDModelUPerm
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitaryCover
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosureRefl
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag LineU

theorem ggWNormConcl_of_unitary_diagonal {K : Type} [Field K] [Finite K]
    {n d p : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1) (hd : 5 ≤ d)
    {L' : Type} [Group L'] [Finite L'] {π : ↥(unitarySU 2 n K d) →* L'}
    (hπ : UnitTB.Model π) {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (h3 : p ^ 3 ≤ Nat.card A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU π a t)
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
  obtain ⟨ρ, hρ, hρW, hρapp⟩ := exists_permAut_unitary hπ hK hp hp2 hpq
    (by omega) hA hsc hdiag
  have hN : ∀ σ : Equiv.Perm (Fin d), MulAut.conj (π (permSU hπ.field σ)) ∈
      Subgroup.normalizer (A : Set (MulAut L')) :=
    fun σ => unitDvd_conj_perm_mem_normalizer hπ hp hpq (by omega) hA.2 hsc hdiag σ
  have hsw : ∀ i j, i ≠ j → GGIsReflection p (ρ (Equiv.swap i j)) := by
    intro i j hij
    have hr := unitDvd_swap_mem_reflSet hπ hp hp2 hpq (by omega) hA hsc hdiag hN hij
    obtain ⟨w, hw, ht, he, hr⟩ := hr
    rw [hρapp (Equiv.swap i j) (hN (Equiv.swap i j))]
    exact he ▸ hr
  have hfixed : ∀ a : ↥A, (∀ σ, ρ σ a = a) → a = 1 := by
    intro a ha
    obtain ⟨t, hat⟩ := hdiag a a.2
    apply Subtype.ext
    exact UnitTB.eq_one_of_conj_perm hπ (by omega) hat fun σ => by
      have he := congrArg Subtype.val (ha σ)
      rw [hρapp σ (hN σ), ggConjAut_apply] at he
      exact he
  have : (MulAut.conj : L' →* MulAut L').range.Normal :=
    RootCentExc.normal_range_mulAutConj
  apply ggWNormConcl_of_symmetric_fixedFree hp2 hd ι φ h α hM hC hpair hlin
    ρ hρ hsw hfixed (hρW.trans hgen)
  rw [hρW]
  exact mem_normalizer_ggAutomizer_of_mem_ggInduced_of_normal hs


theorem ggTorusWNormSC_unitary_singular_prime {K : Type} [Field K] [Finite K]
    {n d p : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1) (hdp : d = p) :
    GGTorusWNormSC p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  have hp2 : p ≠ 2 := by omega
  have hd : 5 ≤ d := by omega
  have hd6 : (d, n) ≠ (6, 1) := by
    intro he
    have hd6 : d = 6 := congrArg Prod.fst he
    have hp6 : p = 6 := hdp.symm.trans hd6
    have hpn : ¬ Nat.Prime 6 := by norm_num
    exact hpn (hp6 ▸ hp)
  have hcov := LineU.unitaryCoverAt hK hd hd6
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc _ Λ _ _ M C V _ _ ι φ h α
    hM hC hpair hlin hgen s hs
  have hcard : p ^ (d / p + 2) ≤ Nat.card A := by
    simpa only [hdp, Nat.div_self hp.pos, Nat.reduceAdd] using h3
  obtain ⟨π, hπs, hπker, hdiag⟩ := LineU.exists_diagModel hK hn hd hp hpq
    (by rw [hdp]) hcov hψ hker hperf hA hAI hcard
  have hπ : UnitTB.Model π := ⟨TableBU.unitaryFieldData_of_card hK hn, hπs, hπker⟩
  exact ggWNormConcl_of_unitary_diagonal hK hp hp2 hpq hd hπ hA h3 hsc hdiag
    hM hC ι φ h α hpair hlin hgen hs

theorem largeEvenLabelAll_wnorm_unitary_singular_prime {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 1 ≤ lab.n) (ht : lab.tag = .twA)
    (hdp : lab.rank + 1 = p) (hpq : p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  rcases lab with ⟨tag, r, n⟩
  dsimp only at ht hn hdp hpq ⊢
  subst tag
  intro Q hQ
  obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
  refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
  exact ggTorusWNormSC_unitary_singular_prime hK hn hp hp5 hpq hdp

end CFSG.StandardType
