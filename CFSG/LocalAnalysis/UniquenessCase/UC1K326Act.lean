module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326Amb
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326ActHom
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326SL23
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G] {n : ℕ} {P : Subgroup G}

theorem card_map_mul_card_ker_of_le {M N : Type*} [Group M] [Group N] (f : M →* N)
    {K : Subgroup M} (hker : f.ker ≤ K) :
    Nat.card (K.map f) * Nat.card f.ker = Nat.card K := by
  have h := Subgroup.relIndex_mul_card (H := f.ker) (K := K)
  rw [Subgroup.relIndex_ker (K := K) (f := f), inf_eq_left.mpr hker] at h
  exact h

theorem card_map_eq_three_of_card_ker {M N : Type*} [Group M] [Group N] (f : M →* N)
    {K : Subgroup M} (hker : f.ker ≤ K) (hK : Nat.card K = 81) (hf : Nat.card f.ker = 27) :
    Nat.card (K.map f) = 3 := by
  have h := card_map_mul_card_ker_of_le f hker
  rw [hK, hf] at h
  omega

theorem factorization_card_range_of_ker {M N : Type*} [Group M] [Finite M] [Group N] [Finite N]
    (σ : M →* N) (hker : Nat.card σ.ker = 27) (hfactM : (Nat.card M).factorization 3 = 4) :
    (Nat.card σ.range).factorization 3 = 1 := by
  have hcard : Nat.card M = 27 * Nat.card σ.range := by
    rw [← hker]
    exact (Subgroup.card_ker_mul_card_range σ).symm
  have hHne : Nat.card σ.range ≠ 0 := Nat.card_pos.ne'
  have h27 : (27 : ℕ).factorization 3 = 3 := by
    rw [show (27 : ℕ) = 3 ^ 3 by norm_num, Nat.factorization_pow_self Nat.prime_three]
  have hfact : (Nat.card M).factorization 3 =
      (27 : ℕ).factorization 3 + (Nat.card σ.range).factorization 3 := by
    rw [hcard, Nat.factorization_mul (by norm_num) hHne]
    rfl
  rw [h27, hfactM] at hfact
  omega

theorem factorization_card_of_sylow_le {X : Subgroup G} (hPX : P ≤ X)
    (hPsylow : IsSylowOf 3 P ⊤) (hP81 : Nat.card P = 81) :
    (Nat.card X).factorization 3 = 4 := by
  have hPfact : Nat.card P = 3 ^ (Nat.card G).factorization 3 := by
    have h := hPsylow.card_eq
    rwa [Subgroup.card_top] at h
  have hGfact : (Nat.card G).factorization 3 = 4 := by
    have hpow : (3 : ℕ) ^ (Nat.card G).factorization 3 = 3 ^ 4 := by
      rw [← hPfact, hP81]
      norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow
  have hGnot : ¬ 3 ^ 5 ∣ Nat.card G := by
    rw [Nat.prime_three.pow_dvd_iff_le_factorization (Nat.card_pos (α := G)).ne']
    omega
  have hX4 : 3 ^ 4 ∣ Nat.card X := by
    have hdiv : Nat.card P ∣ Nat.card X := Subgroup.card_dvd_of_le hPX
    rw [hP81] at hdiv
    rwa [show (81 : ℕ) = 3 ^ 4 by norm_num] at hdiv
  have hXnot5 : ¬ 3 ^ 5 ∣ Nat.card X := fun hd =>
    hGnot (hd.trans (Subgroup.card_subgroup_dvd_card X))
  have hXne : Nat.card X ≠ 0 := Nat.card_pos.ne'
  have hge : 4 ≤ (Nat.card X).factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization hXne).mp hX4
  have hle : (Nat.card X).factorization 3 ≤ 4 := by
    by_contra h
    have h5 : 5 ≤ (Nat.card X).factorization 3 := by omega
    exact hXnot5 ((Nat.prime_three.pow_dvd_iff_le_factorization hXne).mpr h5)
  omega

theorem exists_sylow_of_card_three {H : Type*} [Group H] [Finite H] (S : Subgroup H)
    (hS : Nat.card S = 3) (hfact : (Nat.card H).factorization 3 = 1) :
    ∃ S₀ : Sylow 3 H, (S₀ : Subgroup H) = S := by
  refine ⟨Sylow.ofCard S ?_, rfl⟩
  rw [hS, hfact]
  norm_num

theorem normal_of_subgroupOf_map_normal {M N : Type*} [Group M] [Group N] (σ : M →* N)
    {K : Subgroup M} (hker : σ.ker ≤ K)
    (h : ((K.map σ).subgroupOf σ.range).Normal) : K.Normal := by
  have hcomap : (((K.map σ).subgroupOf σ.range).comap σ.rangeRestrict).Normal :=
    h.comap σ.rangeRestrict
  have heq : ((K.map σ).subgroupOf σ.range).comap σ.rangeRestrict = K :=
    Subgroup.comap_map_eq_self hker
  rwa [heq] at hcomap

theorem card_of_ker_eq_27_of_surjective_sl23 {M : Type*} [Group M] [Finite M]
    (σ : M →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (hker : Nat.card σ.ker = 27) (hσtop : σ.range = ⊤) :
    Nat.card M = 648 := by
  have h24 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) = 24 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have h := Subgroup.card_ker_mul_card_range σ
  rw [hker, hσtop, Subgroup.card_top, h24] at h
  omega

theorem noncomp_card_oPrimeResidual (h : Hyp326 G n P) (hn1 : n = 1)
    (hQ27 : Nat.card (CFSG.pCore 3 G) = 27) (hnab : ¬ IsMulCommutative (CFSG.pCore 3 G))
    (hcent : Subgroup.centralizer (CFSG.pCore 3 G : Set G) ≤ CFSG.pCore 3 G) :
    Nat.card (CFSG.GH74.GLS.oPrimeResidual 3 G) = 648 := by
  set X := CFSG.GH74.GLS.oPrimeResidual 3 G with hX
  set Q : Subgroup G := CFSG.pCore 3 G with hQ
  have hQleP : Q ≤ P := pCore_le_sylow h.sylow
  have hPleX : P ≤ X := le_oPrimeResidual_of_sylow h.sylow
  have hQleX : Q ≤ X := hQleP.trans hPleX
  have hP81 : Nat.card P = 81 := by
    obtain ⟨e⟩ := h.wr
    rw [Nat.card_congr e.toEquiv, hn1]
    simpa using (zwr_card_center_Zwr (n := 1) le_rfl).1
  obtain ⟨σ, hσker⟩ := exists_hom_sl23 hQ27 hnab hcent hQleX
  have hker_card : Nat.card σ.ker = 27 := by
    rw [hσker]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQleX).toEquiv).trans hQ27
  have hKcard : Nat.card (P.subgroupOf X) = 81 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPleX).toEquiv).trans hP81
  have hker_le : σ.ker ≤ P.subgroupOf X := by
    rw [hσker]
    exact Subgroup.subgroupOf_mono X hQleP
  have hScard : Nat.card ((P.subgroupOf X).map σ) = 3 :=
    card_map_eq_three_of_card_ker σ hker_le hKcard hker_card
  have hXfact : (Nat.card X).factorization 3 = 4 :=
    factorization_card_of_sylow_le hPleX h.sylow hP81
  have hHfact : (Nat.card σ.range).factorization 3 = 1 :=
    factorization_card_range_of_ker σ hker_card hXfact
  have hSleH : (P.subgroupOf X).map σ ≤ σ.range :=
    Subgroup.map_le_range (f := σ) (P.subgroupOf X)
  have hS'card : Nat.card (((P.subgroupOf X).map σ).subgroupOf σ.range) = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSleH).toEquiv).trans hScard
  obtain ⟨S₀, hS₀⟩ :=
    exists_sylow_of_card_three (((P.subgroupOf X).map σ).subgroupOf σ.range) hS'card hHfact
  have hnot : ¬ (S₀ : Subgroup ↥σ.range).Normal := by
    intro hnorm
    rw [hS₀] at hnorm
    have hKnormal : (P.subgroupOf X).Normal :=
      normal_of_subgroupOf_map_normal σ hker_le hnorm
    have hXnormal : X.Normal := by
      change (CFSG.GH74.GLS.oPrimeResidual 3 G).Normal
      exact CFSG.GH74.GLS.Stage1.Thm6.Prod.oPrimeResidual_normal 3 G
    haveI : X.Normal := hXnormal
    obtain ⟨Px, hPx⟩ :=
      (CFSG.ABGLocalTools.IsSylowOf.of_le h.sylow hPleX le_top).exists_sylow_eq_subgroupOf
    have hPxnorm : (Px : Subgroup ↥X).Normal := by rw [hPx]; exact hKnormal
    haveI : (Px : Subgroup ↥X).Characteristic := Sylow.characteristic_of_normal Px hPxnorm
    have hmapN : ((Px : Subgroup ↥X).map X.subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal (H := X) (K := (Px : Subgroup ↥X))
    rw [hPx, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPleX] at hmapN
    have hPleQ : P ≤ CFSG.pCore 3 G := by
      unfold CFSG.pCore
      exact le_sSup ⟨hmapN, h.sylow.isPGroup⟩
    have hle : Nat.card P ≤ Nat.card (CFSG.pCore 3 G) := Subgroup.card_le_of_le hPleQ
    rw [hP81, hQ27] at hle
    omega
  have hHtop : σ.range = ⊤ := sl23_eq_top_of_not_normal_sylow σ.range ⟨S₀, hnot⟩
  exact card_of_ker_eq_27_of_surjective_sl23 σ hker_card hHtop

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
