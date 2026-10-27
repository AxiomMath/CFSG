module

public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
public import CFSG.LocalAnalysis.StandardType.GGL45NtRecLinSmall
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinear
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeACover
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBTypeA
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMonomialIrred
public import CFSG.RankThree.PartOne.KC.LinearNoninnerPlaneInner
public import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.PlaneReductionGeneral

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

private theorem ggL45NtRecLin_isPElt_congr {p : ℕ} {G H : Type*} [Monoid G] [Monoid H]
    (e : G ≃* H) {u : G} (h : GGL45IsPElt p u) : GGL45IsPElt p (e u) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by rw [← map_pow, hk, map_one]⟩

private theorem ggL45NtRecLin_inner_of_isPElt {n : ℕ} {K : Type} [Field K] [Finite K] {p : ℕ}
    (hn : 3 ≤ n) (hp : p.Prime) (hpd : ¬ p ∣ n)
    {a : MulAut (projectiveSL n K)} (haD : a ∈ linearAutGroup n K) (hap : GGL45IsPElt p a) :
    a ∈ CFSG.RankThree.PartOne.innSL n K := by
  obtain ⟨k, hk⟩ := hap
  obtain ⟨g, rfl⟩ := mem_linearAutGroup_iff.mp haD
  have hcop : Nat.Coprime (p ^ k) (Nat.gcd n (Nat.card K - 1)) := by
    have h1 : Nat.Coprime p (Nat.gcd n (Nat.card K - 1)) :=
      (Nat.Prime.coprime_iff_not_dvd hp).mpr
        (fun hdiv => hpd (hdiv.trans (Nat.gcd_dvd_left _ _)))
    exact h1.pow_left k
  have h1 : conjAut n K (g ^ p ^ k) = 1 := by rw [map_pow, hk]
  obtain ⟨c, hc⟩ := CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff hn (g ^ p ^ k) |>.mp h1
  have hdet : (Matrix.GeneralLinearGroup.det g) ^ (p ^ k) = c ^ n := by
    rw [← map_pow, ← hc, CFSG.RankThree.PartOne.KCLinPlane.det_scalar_gl_units]
  obtain ⟨u, hu⟩ := CFSG.RankThree.PartOne.KCLinPlane.exists_pow_eq_of_pow_eq
    (m := Nat.card K - 1) (fun x : Kˣ => by rw [← Nat.card_units]; exact pow_card_eq_one') hcop hdet
  have hdet' : Matrix.GeneralLinearGroup.det
      (GeneralLinearGroup.scalar (Fin n) u⁻¹ * g) = 1 := by
    rw [map_mul, CFSG.RankThree.PartOne.KCLinPlane.det_scalar_gl_units, ← hu, inv_pow,
      inv_mul_cancel]
  have hrange : GeneralLinearGroup.scalar (Fin n) u⁻¹ * g ∈
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →* GL (Fin n) K).range := by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hdet'
  have h2 : conjAut n K g = conjAut n K (GeneralLinearGroup.scalar (Fin n) u⁻¹ * g) := by
    rw [map_mul, conjAut_scalar, one_mul]
  rw [h2]
  show conjAut n K (GeneralLinearGroup.scalar (Fin n) u⁻¹ * g) ∈
    (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range
  rw [← CFSG.RankThree.PartOne.KCLinComm.map_toGL_range_eq_conj_range]
  exact ⟨_, hrange, rfl⟩

private theorem ggL45NtRecLin_centerPrime_of_centerCoprime {p : ℕ} {R : Type} [Group R]
    (h : GGCenterCoprime p R) (hZ : Subgroup.center R = ⊥) : GGCenterPrime p R := by
  intro L' _ _ ψ hψ hker hperf hdvd
  have hZle : Subgroup.center L' ≤ ψ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hzc : ψ z ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨l, rfl⟩ := hψ g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l]
    rw [hZ, Subgroup.mem_bot] at hzc
    exact hzc
  exact h L' ψ hψ hker hperf (hdvd.trans (Subgroup.card_dvd_of_le hZle))

private theorem ggL45NtRecLin_centerPrime_psl {d p : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hpd : Nat.Coprime p d) (hsec : TypeA.SLHasSections d K)
    (hZ : Subgroup.center (projectiveSL d K) = ⊥) :
    GGCenterPrime p (projectiveSL d K) :=
  ggL45NtRecLin_centerPrime_of_centerCoprime (TypeA.ggCenterCoprime_psl hp hpd hsec) hZ

private theorem ggL45NtRecLin_centerPrime_recipe {d p : ℕ} {K : Type} [Field K] [Finite K]
    (hd : 3 ≤ d) (hp : p.Prime) (hpd : ¬ p ∣ d) (hsec : TypeA.SLHasSections d K) :
    GGCenterPrime p (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :=
  ggCenterPrime_of_mulEquiv (TypeA.recipeEquiv d K)
    (ggL45NtRecLin_centerPrime_psl hp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd) hsec
      (CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (n := d) (k := K) hd))

private theorem ggL45NtRecLin_slHasSections {d n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) (hgen : 5 ≤ d ∨ (d = 3 ∧ 3 ≤ n) ∨ (d = 4 ∧ 2 ≤ n)) :
    TypeA.SLHasSections d K := by
  rcases hgen with h5 | ⟨hd3, hn3⟩ | ⟨hd4, hn2⟩
  · exact TypeA.slHasSections_of_five_le h5
  · subst hd3
    have hle : 2 ^ 3 ≤ Nat.card K := by
      rw [hK]; exact Nat.pow_le_pow_right (by norm_num) hn3
    refine TypeA.slHasSections_of_card (by norm_num) ?_ ?_ ?_
    · intro hc; rw [hc] at hle; norm_num at hle
    · rintro ⟨-, hc⟩; rw [hc] at hle; norm_num at hle
    · rintro ⟨h, -⟩; norm_num at h
  · subst hd4
    have hle : 2 ^ 2 ≤ Nat.card K := by
      rw [hK]; exact Nat.pow_le_pow_right (by norm_num) hn2
    refine TypeA.slHasSections_of_card (by norm_num) ?_ ?_ ?_
    · intro hc; rw [hc] at hle; norm_num at hle
    · rintro ⟨h, -⟩; norm_num at h
    · rintro ⟨-, hc⟩; rw [hc] at hle; norm_num at hle

private theorem ggL45NtRecLin_rec {d p : ℕ} {K : Type} [Field K] [Finite K]
    (hd : 3 ≤ d) (hp : p.Prime) (hpd : ¬ p ∣ d)
    (hcen : GGCenterPrime p (LargeEvenProj (LargeEvenSLGroup (Fin d) K))) :
    GGL45NtRec p (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K))) := by
  intro _ _
  refine ⟨?_, ?_, hcen⟩
  · intro r
    exact (RecipeFieldLinear.coe_recI (d := d) (K := K)) ▸
      RecipeFieldLinear.conj_mem_recI r
  · intro u hu hup
    have hlin : MulAut.congr (TypeA.recipeEquiv d K) u ∈ linearAutGroup d K := by
      rw [← RecipeFieldLinear.mem_recI_iff (d := d) (K := K)]
      exact show u ∈ (RecipeFieldLinear.recI d K : Set _) from
        (RecipeFieldLinear.coe_recI (d := d) (K := K)).symm ▸ hu
    have hinner := ggL45NtRecLin_inner_of_isPElt hd hp hpd hlin
      (ggL45NtRecLin_isPElt_congr (MulAut.congr (TypeA.recipeEquiv d K)) hup)
    obtain ⟨r', hr'⟩ := hinner
    refine ⟨(TypeA.recipeEquiv d K).symm r', (MulAut.congr (TypeA.recipeEquiv d K)).injective ?_⟩
    rw [mulAut_congr_conj, MulEquiv.apply_symm_apply]
    exact hr'.symm

theorem ggL45NtRecOn_lin :
    GGL45NtRecOn GGL45NtFamLin := by
  intro p hp hp2 lab hlab hkg hS Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨hnt, hvac, _hexc⟩ := hS.1
  rcases hS.2 with hA | ⟨hD, hr3⟩
  · subst hA
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeLinear] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ'⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQ', ?_⟩
    haveI : Finite K := hfin
    have hn1 : 1 ≤ n := hlab.1
    have hrank1 : 1 ≤ rank := hlab.2.1
    have hrne : rank ≠ 1 := by
      intro h
      exact hvac (Or.inl ⟨rfl, h⟩)
    have hpd : ¬ p ∣ rank + 1 := hnt
    have hcenter : GGCenterPrime p (LargeEvenProj (LargeEvenSLGroup (Fin (rank + 1)) K)) := by
      rcases (show rank = 2 ∨ rank = 3 ∨ 4 ≤ rank by omega) with hr | hr | hr4
      · subst hr
        rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with h1 | h2 | h3
        · subst h1
          exact ggL45NtRecLinSmall_three_two (K := K) (by rw [hK, pow_one]) hp hp2 hpd
        · subst h2
          exact ggL45NtRecLinSmall_three_four (K := K) (by rw [hK]; norm_num) hp hp2 hpd
        · exact ggL45NtRecLin_centerPrime_recipe (by norm_num) hp hpd
            (ggL45NtRecLin_slHasSections hK (Or.inr (Or.inl ⟨rfl, h3⟩)))
      · subst hr
        rcases (show n = 1 ∨ 2 ≤ n by omega) with h1 | h2
        · subst h1
          exact ggL45NtRecLinSmall_four_two (K := K) (by rw [hK, pow_one]) hp hp2
        · exact ggL45NtRecLin_centerPrime_recipe (by norm_num) hp hpd
            (ggL45NtRecLin_slHasSections hK (Or.inr (Or.inr ⟨rfl, h2⟩)))
      · exact ggL45NtRecLin_centerPrime_recipe (by omega) hp hpd
          (ggL45NtRecLin_slHasSections hK (Or.inl (by omega)))
    exact ggL45NtRecLin_rec (by omega) hp hpd hcenter
  · subst hD
    subst hr3
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [if_pos rfl] at hQ ⊢
    dsimp only [LargeEvenRecipeLinear] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ'⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQ', ?_⟩
    haveI : Finite K := hfin
    have hn1 : 1 ≤ n := hlab.1
    have hpd : ¬ p ∣ 4 := by
      intro h
      have h42 : (2 : ℕ) ^ 2 = 4 := by norm_num
      have h2dvd : p ∣ 2 := hp.dvd_of_dvd_pow (n := 2) (h42 ▸ h)
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2dvd)
    have hcenter : GGCenterPrime p (LargeEvenProj (LargeEvenSLGroup (Fin 4) K)) := by
      rcases (show n = 1 ∨ 2 ≤ n by omega) with h1 | h2
      · subst h1
        exact ggL45NtRecLinSmall_four_two (K := K) (by rw [hK, pow_one]) hp hp2
      · exact ggL45NtRecLin_centerPrime_recipe (by norm_num) hp hpd
          (ggL45NtRecLin_slHasSections hK (Or.inr (Or.inr ⟨rfl, h2⟩)))
    exact ggL45NtRecLin_rec (by norm_num) hp hpd hcenter

end CFSG.StandardType
