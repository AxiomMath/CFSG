module

public import CFSG.LocalAnalysis.StandardType.GGSlDvdRootGenHyp
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenAvoidKG
import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL
import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBRefl

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.CALinearPlane

namespace SlDvdRootGen

private theorem two_dvd_card_of_charP_two {K : Type} [Field K] [Finite K] [CharP K 2] :
    2 ∣ Nat.card K := by
  have := Fintype.ofFinite K
  have h0 : ((Fintype.card K : ℕ) : K) = 0 := by simp
  rw [Nat.card_eq_fintype_card]
  exact (CharP.cast_eq_zero_iff K 2 _).mp h0

end SlDvdRootGen

theorem ggTorusRootGenAvoidKG_linearDvd {K : Type} [Field K] [Finite K] [CharP K 2] {d p : ℕ}
    (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 0 < d) (hpd : p ∣ d) {r : ℕ}
    (hr : d - 2 ≤ max r 3) :
    GGTorusRootGenAvoidKG p r (projectiveSL d K) (Set.range (conjAut d K)) := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI hrA h3 hsc ρ
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ Nat.card K := SlDvdRootGen.two_dvd_card_of_charP_two
    have h1 : 0 < Nat.card K := Nat.card_pos
    omega
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hd3 : 3 ≤ d := hp3.trans (Nat.le_of_dvd (by omega) hpd)
  rcases (show d = 3 ∨ d = 4 ∨ 5 ≤ d by omega) with h3d | h4d | h5d
  ·
    subst h3d
    exact absurd ⟨hψ, hker, hperf, hA, hAI, hrA, h3, hsc⟩
      (not_ggTorusTBGroup_small hp hp2 hpK hd (by omega))
  ·
    subst h4d
    exfalso
    have h1 : p ∣ 2 ^ 2 := by
      norm_num
      exact hpd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1))
  ·
    have hmax : p ^ max r 3 ≤ Nat.card A := by
      rcases le_or_gt r 3 with hle | hlt
      · rw [max_eq_right hle]
        exact h3
      · rw [max_eq_left (le_of_lt hlt)]
        exact hrA
    have hTB : GGTorusTBGroup p (max r 3) (projectiveSL d K)
        (Set.range (conjAut d K)) L' ψ A :=
      ⟨hψ, hker, hperf, hA, hAI, hmax, h3, hsc⟩
    obtain ⟨φ', hφ's, hφker, hdiag⟩ :=
      exists_actsDiag_model_of_tbGroup hp hpK (by omega : 4 ≤ d) hr hTB
    have hN : ∀ σ : Equiv.Perm (Fin d),
        NbrInnerWeylA.permConj φ' σ ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
      fun σ => TypeANbrDvd.permConj_mem_normalizer_of_selfCent hφ's hφker hA.2 hsc hdiag σ
    have hinj := TypeANbrDvd.permAut_injective hp hp2 hpK (by omega : 4 ≤ d) hφ's hφker
      hA hsc hdiag hN
    obtain ⟨i₀, j₀, hρ⟩ : ∃ i₀ j₀ : Fin d, ∀ i j : Fin d, i ≠ j →
        ggConjAut A (hN (Equiv.swap i j)) = ρ →
          ({i, j} : Finset (Fin d)) = {i₀, j₀} := by
      by_cases h : ∃ i j : Fin d, i ≠ j ∧ ggConjAut A (hN (Equiv.swap i j)) = ρ
      · obtain ⟨i₀, j₀, hij₀, h₀⟩ := h
        refine ⟨i₀, j₀, fun i j hij hρ' => ?_⟩
        have hperm : TypeANbrDvd.permAut φ' A hN (Equiv.swap i j) =
            TypeANbrDvd.permAut φ' A hN (Equiv.swap i₀ j₀) := by
          rw [TypeANbrDvd.permAut_apply, TypeANbrDvd.permAut_apply]
          exact hρ'.trans h₀.symm
        have hswap : Equiv.swap i j = Equiv.swap i₀ j₀ := hinj hperm
        calc ({i, j} : Finset (Fin d)) = (Equiv.swap i j).support :=
              (Equiv.Perm.support_swap hij).symm
          _ = (Equiv.swap i₀ j₀).support := by rw [hswap]
          _ = {i₀, j₀} := Equiv.Perm.support_swap hij₀
      · push Not at h
        exact ⟨⟨0, by omega⟩, ⟨0, by omega⟩, fun i j hij hρ' => absurd hρ' (h i j hij)⟩
    apply le_antisymm le_top
    rw [← Subgroup.map_top_of_surjective φ' hφ's,
      ← TypeA.iSup_coordBlockSL_pairs (K := K) (by omega : 3 ≤ d) i₀ j₀]
    simp only [Subgroup.map_iSup]
    refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => ?_
    have hne : ggConjAut A (hN (Equiv.swap i j)) ≠ ρ :=
      fun h => hij.2 (hρ i j hij.1 h)
    have hW : GGTorusWeylElt p A (φ' (TypeA.permSL (Equiv.swap i j))) :=
      weyl_mul_apply_inv_diag hφker hdiag hA.2 _ ⟨Equiv.swap i j, rfl⟩
    have hR : GGIsReflection p (ggConjAut A (hN (Equiv.swap i j))) := by
      obtain ⟨-, -, -, -, hR⟩ :=
        TypeANbrDvd.permAut_swap_mem_reflSet hp hp2 hpK (by omega : 3 ≤ d) hφ's
          hφker hA hsc hdiag hN hij.1
      exact hR
    have hmem : φ' (TypeA.permSL (Equiv.swap i j)) ∈
        (coordBlockSL K ({i, j} : Finset (Fin d))).map φ' :=
      Subgroup.mem_map_of_mem φ' TypeA.permSL_mem_coordBlockSL
    have hcomp : IsComponentOf ((coordBlockSL K ({i, j} : Finset (Fin d))).map φ')
        (ggHypCent A (φ' (TypeA.permSL (Equiv.swap i j)))) :=
      SlDvdRootGen.isComponentOf_coordBlockSL_ggHypCent hp hp2 hpK h5d hφ's hφker hsc
        hdiag hij.1
    have hdvd : p ∣ Nat.card
        ((coordBlockSL K ({i, j} : Finset (Fin d))).map φ') :=
      TypeA.dvd_card_coordBlockSL_pair hp hpK (by omega : 3 ≤ d) hφker hij.1
    exact le_iSup_of_le (φ' (TypeA.permSL (Equiv.swap i j)))
      (le_iSup_of_le (hN (Equiv.swap i j))
        (le_iSup_of_le ((coordBlockSL K ({i, j} : Finset (Fin d))).map φ')
          (le_iSup_of_le ⟨hW, hR, hne, hmem, hcomp, hdvd⟩ le_rfl)))

end CFSG.StandardType

end
