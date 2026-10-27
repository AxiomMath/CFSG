module

public import CFSG.LocalAnalysis.StandardType.GGSuDvdRootGenWeyl
public import CFSG.LocalAnalysis.StandardType.GGSuDvdRootGenComp
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverTwo
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNinePGL

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.StandardType.LineU

theorem ggTorusRootGenAvoidKG_unitaryDvd
    {K : Type} [Field K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 2 ≤ n) (hd : 3 ≤ d) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d) {r : ℕ} (hr : d / p + 2 ≤ max r 3) :
    GGTorusRootGenAvoidKG p r (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have h := TableBU.unitaryFieldData_of_card hK (by omega)
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one (by omega) hpq
  have hq : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  intro L' _ _ ψ hψ hker hperf A hA hAI hrA h3 hsc ρ
  rcases (show d = 3 ∨ 4 ≤ d by omega) with rfl | hd4
  · exfalso
    have h2 : 2 < 2 ^ n := by
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hlt := TableBUE.card_lt_unitary_three_all h hK h2 hp hp2 hψ hker hperf hA hAI
    omega
  · rcases (show d = 4 ∨ 5 ≤ d by omega) with rfl | hd5
    · have hp4 : p ∣ 2 ^ 2 := by simpa using hpd
      have hp2' : p = 2 :=
        (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hp4)
      exact absurd hp2' hp2
    · have hcard : p ^ (d / p + 2) ≤ Nat.card A := by
        have h1 : p ^ (d / p + 2) ≤ p ^ max r 3 := Nat.pow_le_pow_right hp.pos hr
        have h2 : p ^ max r 3 ≤ Nat.card A := by
          rcases le_total r 3 with hr3 | hr3
          · rw [max_eq_right hr3]
            exact h3
          · rw [max_eq_left hr3]
            exact hrA
        exact h1.trans h2
      have hdn : (d, n) ≠ (6, 1) := by
        intro hdn'
        have h2 := congrArg Prod.snd hdn'
        simp only at h2
        omega
      obtain ⟨φ, hφs, hφker, hdiag⟩ :=
        LineU.exists_diagModel hK (by omega) hd5 hp hpq hpd
          (LineU.unitaryUniversalCover_holds n d K hK hd5 hdn)
          hψ hker hperf hA hAI hcard
      have hAp : ∀ a ∈ A, a ^ p = 1 := hA.2
      have hN : ∀ σ : Equiv.Perm (Fin d),
          MulAut.conj (φ (permSU h σ)) ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
        fun σ => SuDvdRootGen.conj_permSU_mem_normalizer h hpq (by omega) hφs hφker
          hdiag hAp hsc σ
      obtain ⟨i₀, j₀, hρ⟩ : ∃ i₀ j₀ : Fin d, ∀ i j, i ≠ j →
          ggConjAut A (hN (Equiv.swap i j)) = ρ →
            ({i, j} : Finset (Fin d)) = {i₀, j₀} := by
        by_cases hc : ∃ i j, i ≠ j ∧ ggConjAut A (hN (Equiv.swap i j)) = ρ
        · obtain ⟨i₀, j₀, hij₀, h₀⟩ := hc
          exact ⟨i₀, j₀, fun i j hij hρ' =>
            SuDvdRootGen.pair_eq_of_ggConjAut_eq_permSU h hp hpq (by omega) hφs hφker hdiag
              hsc hij hij₀ (hN (Equiv.swap i j)) (hN (Equiv.swap i₀ j₀))
              (hρ'.trans h₀.symm)⟩
        · push Not at hc
          exact ⟨⟨0, by omega⟩, ⟨0, by omega⟩,
            fun i j hij hρ' => absurd hρ' (hc i j hij)⟩
      apply le_antisymm le_top
      rw [← Subgroup.map_top_of_surjective φ hφs,
        ← SuNsRootGen.iSup_blockSU_pairs h hq (by omega) i₀ j₀]
      simp only [Subgroup.map_iSup]
      refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => ?_
      have hcomm : ∀ a ∈ A, MulAut.conj (φ (permSU h (Equiv.swap i j))) * a =
          a * MulAut.conj (φ (permSU h (Equiv.swap i j))) →
          ∃ t : Fin d → K, ActsDiagU φ a t ∧ t i = t j := by
        intro a ha hconj
        obtain ⟨t, ht⟩ := hdiag a ha
        exact ⟨t, ht,
          (SuDvdRootGen.commute_conj_permSU_swap_iff h (by omega) hφker hφs ht i j).mp hconj⟩
      have hcomp : IsComponentOf
          ((TableBUE.blockSU (K := K) (n := n) ({i, j} : Finset (Fin d))).map φ)
          (ggHypCent A (φ (permSU h (Equiv.swap i j)))) :=
        SuDvdRootGen.isComponentOf_blockSU_pair_ggHypCent h hn hp hpq (by omega) hφs hφker
          hdiag hsc hij.1 hcomm
      exact le_iSup_of_le (φ (permSU h (Equiv.swap i j)))
        (le_iSup_of_le (hN (Equiv.swap i j))
          (le_iSup_of_le ((TableBUE.blockSU (K := K) (n := n)
              ({i, j} : Finset (Fin d))).map φ)
            (le_iSup_of_le
              ⟨SuDvdRootGen.ggTorusWeylElt_permSU h (by omega) hφker hdiag hAp
                  (Equiv.swap i j),
                SuDvdRootGen.isReflection_permSU_swap h hp hpq (by omega) hφs hφker hdiag hAp
                  hsc hij.1 (hN (Equiv.swap i j)),
                fun h' => hij.2 (hρ i j hij.1 h'),
                Subgroup.mem_map_of_mem φ (SuDvdRootGen.permSU_swap_mem_blockSU h i j),
                hcomp,
                SuDvdRootGen.dvd_card_blockSU_pair_map h hp hpq (by omega) hφker hij.1⟩ le_rfl)))

end CFSG.StandardType

end
