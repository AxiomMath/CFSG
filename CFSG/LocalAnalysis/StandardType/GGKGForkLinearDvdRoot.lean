module

public import CFSG.LocalAnalysis.StandardType.GGKGForkLinearOne
public import CFSG.LocalAnalysis.StandardType.GGSlDvdRootGenAsm
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBRefl
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

open TypeANbrDvd

private theorem ggKGSd_coordBlockSL_mono {d : ℕ} {K : Type} [Field K] {J J' : Finset (Fin d)}
    (h : J ⊆ J') :
    CFSG.RankThree.CALinearPlane.coordBlockSL K J ≤
      CFSG.RankThree.CALinearPlane.coordBlockSL K J' := by
  intro g hg
  rw [CFSG.RankThree.CALinearPlane.mem_coordBlockSL_iff] at hg ⊢
  intro i j hij
  exact hg i j (by
    rcases hij with h' | h'
    · exact Or.inl fun hi => h' (h hi)
    · exact Or.inr fun hj => h' (h hj))

private theorem ggKGSd_conj_permSL_mem_normalizer {d : ℕ} {K : Type} [Field K] [CharP K 2]
    {L' : Type} [Group L'] {φ' : SpecialLinearGroup (Fin d) K →* L'}
    {A : Subgroup (MulAut L')}
    (hN : ∀ σ, NbrInnerWeylA.permConj φ' σ ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (i j : Fin d) :
    MulAut.conj (φ' (permSL (Equiv.swap i j))) ∈
      Subgroup.normalizer (A : Set (MulAut L')) := by
  have helem : NbrInnerWeylA.permConj φ' (Equiv.swap i j) =
      MulAut.conj (φ' (permSL (Equiv.swap i j))) := by
    show MulAut.conj (φ' (permSL (Equiv.swap i j)⁻¹)) =
      MulAut.conj (φ' (permSL (Equiv.swap i j)))
    rw [Equiv.swap_inv]
  rw [← helem]
  exact hN (Equiv.swap i j)

private theorem ggKGSd_reflection {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) (hd : 4 ≤ d)
    {L' : Type} [Group L'] [Finite L']
    {φ' : SpecialLinearGroup (Fin d) K →* L'} (hφ's : Function.Surjective φ')
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K) {A : Subgroup (MulAut L')}
    (hA : IsElemAbelian p A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, TypeANbrDvd.ActsDiag φ' a t)
    (hN : ∀ σ, NbrInnerWeylA.permConj φ' σ ∈ Subgroup.normalizer (A : Set (MulAut L')))
    {φ₀ : MulAut ↥A}
    (h₀ : φ₀ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A)
    (hrefl : GGIsReflection p φ₀) :
    ∃ i j : Fin d, i ≠ j ∧
      φ₀ = ggConjAut A (ggKGSd_conj_permSL_mem_normalizer hN i j) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (MulAut L') :=
    Finite.of_injective (fun f : MulAut L' => (f : L' → L')) fun f g h => by
      ext x
      exact congrFun h x
  haveI : Finite ↥A := Subtype.finite
  have hsw : ∀ x y : Fin d, x ≠ y →
      GGIsReflection p (TypeANbrDvd.permAut φ' A hN (Equiv.swap x y)) := by
    intro x y hxy
    obtain ⟨-, -, -, -, hR⟩ :=
      TypeANbrDvd.permAut_swap_mem_reflSet hp hp2 hpK (by omega : 3 ≤ d) hφ's hφker hA hsc
        hdiag hN hxy
    exact hR
  have hinj : Function.Injective (TypeANbrDvd.permAut φ' A hN) :=
    TypeANbrDvd.permAut_injective hp hp2 hpK hd hφ's hφker hA hsc hdiag hN
  have hauto : ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      (TypeANbrDvd.permAut φ' A hN).range :=
    TypeANbrDvd.ggAutomizer_eq_range_permAut hp hp2 hpK hφ's hφker hA hsc hdiag hN
  have hφ₀ : φ₀ ∈ (TypeANbrDvd.permAut φ' A hN).range := by
    rw [← hauto]
    exact h₀
  obtain ⟨σ, hσ⟩ := hφ₀
  have hreflE : GGIsReflection p (TypeANbrDvd.permAut φ' A hN σ) := by
    rw [hσ]
    exact hrefl
  have hisSwap : σ.IsSwap :=
    isSwap_of_ggIsReflection hp2 hA (TypeANbrDvd.permAut φ' A hN) hinj hsw hreflE
  obtain ⟨i, j, hij, hσij⟩ := hisSwap
  have helem : NbrInnerWeylA.permConj φ' (Equiv.swap i j) =
      MulAut.conj (φ' (permSL (Equiv.swap i j))) := by
    show MulAut.conj (φ' (permSL (Equiv.swap i j)⁻¹)) =
      MulAut.conj (φ' (permSL (Equiv.swap i j)))
    rw [Equiv.swap_inv]
  refine ⟨i, j, hij, ?_⟩
  have hconj : ggConjAut A (hN (Equiv.swap i j)) =
      ggConjAut A (ggKGSd_conj_permSL_mem_normalizer hN i j) := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    simp only [ggConjAut_apply, helem]
  rw [← hσ, hσij, TypeANbrDvd.permAut_apply]
  exact hconj

private theorem ggKGSd_layer {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hd : 4 ≤ d) (h4 : 4 ≤ Nat.card K) {L' : Type} [Group L']
    {φ' : SpecialLinearGroup (Fin d) K →* L'} (hφ's : Function.Surjective φ')
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K) {A : Subgroup (MulAut L')}
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, TypeANbrDvd.ActsDiag φ' a t)
    {i j : Fin d} (hij : i ≠ j) (a : MulAut L') (ha : a ∈ A)
    (hn : MulAut.conj (φ' (permSL (Equiv.swap i j))) ∈
      Subgroup.normalizer (A : Set (MulAut L')))
    (hfix : ggConjAut A hn ⟨a, ha⟩ = ⟨a, ha⟩) :
    φ' (permSL (Equiv.swap i j)) ∈ LargeEvenLayer (ggFix a) := by
  by_cases ha1 : a = 1
  · subst ha1
    have hSLq : CFSG.IsQuasisimple (SpecialLinearGroup (Fin d) K) :=
      CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (by omega) h4
    have hcent : φ'.ker ≤ Subgroup.center (SpecialLinearGroup (Fin d) K) := by
      intro g hg
      exact scalars_le_center d K (hφker g (MonoidHom.mem_ker.mp hg))
    have hL'q : CFSG.IsQuasisimple L' :=
      CFSG.LocalCores.isQuasisimple_of_surjective hSLq φ' hφ's hcent
    have hqtop : CFSG.IsQuasisimple (↥(⊤ : Subgroup L')) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.topEquiv (G := L')).symm hL'q
    have hqtopA : Assembly.IsQuasisimple (↥(⊤ : Subgroup L')) :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hqtop
    have hcompTop : IsComponentOf (⊤ : Subgroup L') ⊤ :=
      ⟨le_top, IsSubnormal.refl ⊤, hqtopA⟩
    have hlayerTop : LargeEvenLayer (⊤ : Subgroup L') = ⊤ :=
      le_antisymm le_top (le_sSup hcompTop)
    have hfix1 : ggFix (1 : MulAut L') = ⊤ := by
      ext x
      simp [ggFix]
    rw [hfix1, hlayerTop]
    exact Subgroup.mem_top _
  · obtain ⟨t, hact⟩ := hdiag a ha
    obtain ⟨D, hD, haD⟩ := id hact
    have hcomm : MulAut.conj (φ' (permSL (Equiv.swap i j))) * a *
        (MulAut.conj (φ' (permSL (Equiv.swap i j))))⁻¹ = a := by
      have h := congrArg (fun x : ↥A => (x : MulAut L')) hfix
      rw [ggConjAut_apply] at h
      exact h
    have hcomp : TypeANbrDvd.ActsDiag φ' a (t ∘ Equiv.swap i j) := by
      have h := TypeANbrDvd.ActsDiag.conj_perm hact (Equiv.swap i j)
      rwa [hcomm] at h
    obtain ⟨m, hmi, hmj⟩ := exists_ne_of_two (by omega : 3 ≤ d) i j
    have hσm : Equiv.swap i j m = m := Equiv.swap_apply_of_ne_of_ne hmi hmj
    have hσi : Equiv.swap i j i = j := by simp
    have hratio := TypeANbrDvd.ActsDiag.ratio hφker hact hcomp hmi
    rw [Function.comp_apply, hσm, Function.comp_apply, hσi] at hratio
    have htij : t i = t j := by
      have h1 : (t i)⁻¹ = (t j)⁻¹ :=
        mul_left_cancel₀ (TypeANbrDvd.ActsDiag.ne_zero hact m) hratio
      exact inv_injective h1
    obtain ⟨S, hS, -, -, hlayer, -⟩ :=
      layer_coordBlockSL_map_le h4 hφ's hφker hD haD ha1 hij htij
    have hiS : i ∈ S := (hS i).mpr rfl
    have hjS : j ∈ S := (hS j).mpr htij.symm
    have hsub : ({i, j} : Finset (Fin d)) ⊆ S := by
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hiS
      · rw [Finset.mem_singleton.mp hk]
        exact hjS
    exact hlayer (Subgroup.mem_map_of_mem φ'
      (ggKGSd_coordBlockSL_mono hsub permSL_mem_coordBlockSL))

theorem ggTorusRootSL2_psl_dvd {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) (hd : 5 ≤ d)
    (h4 : 4 ≤ Nat.card K) :
    GGTorusRootSL2 p (d - 2) (projectiveSL d K) (Set.range (conjAut d K)) := by
  classical
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3, hsc⟩ := hA
  obtain ⟨φ', hφ's, hφ'ker, hdiag⟩ :=
    exists_actsDiag_model_of_tbGroup hp hpK (by omega : 4 ≤ d) le_rfl
      ⟨hψ, hker, hperf, hAe, hAI, hr, h3, hsc⟩
  have hN : ∀ σ : Equiv.Perm (Fin d),
      NbrInnerWeylA.permConj φ' σ ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    fun σ => TypeANbrDvd.permConj_mem_normalizer_of_selfCent hφ's hφ'ker hAe.2 hsc hdiag σ
  intro φ₀ hφ₀ hrefl
  obtain ⟨i, j, hij, hφ₀eq⟩ :=
    ggKGSd_reflection hp hp2 hpK (by omega : 4 ≤ d) hφ's hφ'ker hAe hsc hdiag hN hφ₀ hrefl
  refine ⟨φ' (permSL (Equiv.swap i j)),
    ggKGSd_conj_permSL_mem_normalizer hN i j,
    (CFSG.RankThree.CALinearPlane.coordBlockSL K ({i, j} : Finset (Fin d))).map φ',
    weyl_mul_apply_inv_diag hφ'ker hdiag hAe.2 _ ⟨Equiv.swap i j, rfl⟩,
    hφ₀eq.symm,
    Subgroup.mem_map_of_mem φ' permSL_mem_coordBlockSL, ?_, ?_, ?_⟩
  · exact SlDvdRootGen.isComponentOf_coordBlockSL_ggHypCent hp hp2 hpK (by omega : 5 ≤ d)
      hφ's hφ'ker hsc hdiag hij
  · exact dvd_card_coordBlockSL_pair hp hpK (by omega : 3 ≤ d) hφ'ker hij
  · intro a ha hfix
    rw [hφ₀eq] at hfix
    exact ggKGSd_layer (by omega : 4 ≤ d) h4 hφ's hφ'ker hdiag hij a ha
      (ggKGSd_conj_permSL_mem_normalizer hN i j) hfix

end TypeA

end CFSG.StandardType
