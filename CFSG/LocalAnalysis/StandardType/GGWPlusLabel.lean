module

public import CFSG.LocalAnalysis.StandardType.GGWPlusPSL
public import CFSG.LocalAnalysis.StandardType.GGWPlusTransport
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeADvd
public import CFSG.LocalAnalysis.StandardType.GGPGLTorality
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBVac

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag TypeA

theorem ggWPlusTableB_PSL_three {p : ℕ} {K : Type} [Field K] [Finite K] (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) :
    GGWPlusTableB p (projectiveSL 3 K) (Set.range (conjAut 3 K)) :=
  (ggTableBForms_of_vac hp fun _ hXI hX =>
    TypeA.card_lt_of_torality hp hpK (by norm_num) le_rfl (TypeA.ggPGLTorality_holds hp hp2 hpK)
      hX hXI).2.2.2.2

theorem largeEvenLabelAll_wplus_typeA_dvd {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGTypeALabelDvd p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGWPlusTableB p R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨h, hpn, hpl⟩ := h
  dsimp only at h hpn hpl
  subst h
  intro Q hQ
  have hl1 : 1 ≤ l := hlab.2.1
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hQ', ?_⟩
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hm : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, pow_zero] at hK
      omega
    · exact h0
  have hp2 : p ≠ 2 := TypeA.prime_ne_two_of_dvd_two_pow_sub_one hm (hK ▸ hpK)
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h4 : 4 ≤ Nat.card K := by
    have h1 := Nat.le_of_dvd (by omega) hpK
    omega
  have hd3 : 3 ≤ l + 1 := hp3.trans (Nat.le_of_dvd (by omega) hpl)
  have hI : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (l + 1)) K))
      Set.univ, MulAut.congr (TypeA.recipeEquiv (l + 1) K) φ ∈ Set.range (conjAut (l + 1) K) :=
    fun _ hφ => TypeA.congr_recipeEquiv_mem hφ
  rcases (show l = 2 ∨ l = 3 ∨ 4 ≤ l by omega) with hl2 | hl3 | hl4
  · subst hl2
    exact ggWPlusTableB_of_mulEquiv (TypeA.recipeEquiv 3 K) hI
      (ggWPlusTableB_PSL_three hp hp2 hpK)
  · subst hl3
    exfalso
    have h1 : p ∣ 2 ^ 2 := by norm_num; exact hpl
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1))
  · have h5 : 5 ≤ l + 1 := by omega
    exact ggWPlusTableB_of_mulEquiv (TypeA.recipeEquiv (l + 1) K) hI
      (ggWPlusTableB_PSL hp hp2 hpK h5 h4 (TypeA.slHasSections_of_five_le h5))

end CFSG.StandardType
