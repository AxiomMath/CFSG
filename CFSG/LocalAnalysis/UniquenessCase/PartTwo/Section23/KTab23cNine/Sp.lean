module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23cNine.Generic

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SpChar
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SpHall
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SpParabolic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineSp
import CFSG.LocalAnalysis.UniquenessCase.UC22P22d
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTab23cNine

open CFSG.Open CFSG.Quasithin
open Matrix
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
open CFSG.LocalAnalysis.UniquenessCase.UC22.KTabC
open CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD (lineStab)
open SymplecticFlag (borelSubgroup unipotent mem_unipotent blockMat)
open SymplecticHigher (flagStabilizer)

private theorem unipotent_mulVec_e0 {K : Type} [Field K] (m : ℕ)
    {g : StatedSp (m + 2) K} (hg : g ∈ unipotent (m + 2) K) :
    (((g : GL (Fin (m + 2) ⊕ Fin (m + 2)) K) :
      Matrix (Fin (m + 2) ⊕ Fin (m + 2)) (Fin (m + 2) ⊕ Fin (m + 2)) K)) *ᵥ
      (Pi.single (Sum.inl 0) (1 : K) : Fin (m + 2) ⊕ Fin (m + 2) → K) =
      Pi.single (Sum.inl 0) (1 : K) := by
  obtain ⟨A, C, hA, -, hge⟩ := mem_unipotent.mp hg
  rw [hge]
  ext i
  rw [Matrix.mulVec_single_one, Matrix.col_apply]
  rcases i with j | j
  · rw [blockMat, Matrix.fromBlocks_apply₁₁]
    by_cases hj : j = 0
    · subst hj
      rw [Pi.single_eq_same, hA.2 0]
    · rw [Pi.single_eq_of_ne (show
        Sum.inl j ≠ (Sum.inl (0 : Fin (m + 2)) : Fin (m + 2) ⊕ Fin (m + 2)) from
        fun h => hj (Sum.inl.inj h))]
      exact hA.1 ((Fin.pos_iff_ne_zero' j).mpr hj)
  · rw [blockMat, Matrix.fromBlocks_apply₂₁]
    simp

private theorem sp_conj_eq_one_of_mem_borel_vecStab {K : Type} [Field K] [Finite K] [CharP K 2]
    (m : ℕ) {t : ↥(StatedSp (m + 2) K)}
    (htα : t ∈ Hinf (flagStabilizer (m + 2) K (Set.Icc 2 (m + 2))))
    (htB : t ∈ borelSubgroup (m + 2) K)
    (ht0 : t ∈ KTabC.vecStab (StatedSp (m + 2) K).subtype (Pi.single (Sum.inl 0) 1))
    (hodd : Odd (orderOf t)) : t = 1 := by
  obtain ⟨e, he, hconj⟩ := exists_conj_eq_torusHom_diagHom_sp htB hodd.not_two_dvd_nat
  obtain ⟨c, hc⟩ := exists_diagHom_eq_coroot_of_mem_hinf_sp m htα htB
  have heV : e ∈ KTabC.vecStab (StatedSp (m + 2) K).subtype
      (Pi.single (Sum.inl 0) 1) :=
    KTabC.mem_vecStab.mpr (unipotent_mulVec_e0 m he)
  let d : Fin (m + 2) → Kˣ := Pi.mulSingle 0 c * Pi.mulSingle 1 c⁻¹
  have h1 : e * t * e⁻¹ = SymplecticTorusWeyl.torusHom d := by
    rw [hconj, hc]
  have hfix : (((e * t * e⁻¹ : ↥(StatedSp (m + 2) K)) :
      GL (Fin (m + 2) ⊕ Fin (m + 2)) K) :
      Matrix (Fin (m + 2) ⊕ Fin (m + 2)) (Fin (m + 2) ⊕ Fin (m + 2)) K) *ᵥ
      (Pi.single (Sum.inl 0) 1 : Fin (m + 2) ⊕ Fin (m + 2) → K) =
      Pi.single (Sum.inl 0) 1 := by
    simpa using KTabC.mem_vecStab.mp (mul_mem (mul_mem heV ht0) (inv_mem heV))
  have hfixT : (((SymplecticTorusWeyl.torusHom d : StatedSp (m + 2) K) :
      GL (Fin (m + 2) ⊕ Fin (m + 2)) K) :
      Matrix (Fin (m + 2) ⊕ Fin (m + 2)) (Fin (m + 2) ⊕ Fin (m + 2)) K) *ᵥ
      (Pi.single (Sum.inl 0) 1 : Fin (m + 2) ⊕ Fin (m + 2) → K) =
      Pi.single (Sum.inl 0) 1 := by
    rw [← h1]
    exact hfix
  have h00 : ((d 0 : Kˣ) : K) = 1 := by
    have h := congrFun hfixT (Sum.inl (0 : Fin (m + 2)))
    rw [SymplecticTorusWeyl.coe_torusHom, Matrix.diagonal_mulVec_single] at h
    simpa using h
  have hc1 : c = 1 := by
    apply Units.ext
    simpa [d, Pi.mulSingle_apply, Pi.mul_apply, Fin.zero_ne_one' (n := m + 1)] using h00
  have hd1 : d = 1 := by
    funext i
    simp [d, Pi.mulSingle_apply, hc1]
  have hconj1 : e * t * e⁻¹ = 1 := by
    rw [h1, hd1]
    simp
  calc t = e⁻¹ * (e * t * e⁻¹) * e := by group
    _ = 1 := by rw [hconj1]; group

theorem sp_eq_one_of_mem_hinf_vecStab {K : Type} [Field K] [Finite K] [CharP K 2] (m : ℕ)
    {t : ↥(StatedSp (m + 2) K)}
    (ht : t ∈ Hinf (flagStabilizer (m + 2) K (Set.Icc 2 (m + 2))) ⊓
      KTabC.vecStab (StatedSp (m + 2) K).subtype (Pi.single (Sum.inl 0) 1))
    (hodd : Odd (orderOf t)) : t = 1 := by
  obtain ⟨htα, ht0⟩ := Subgroup.mem_inf.mp ht
  have htQα : t ∈ flagStabilizer (m + 2) K (Set.Icc 2 (m + 2)) :=
    Subgroup.map_subtype_le _ htα
  have htQ0 : t ∈ lineStab (StatedSp (m + 2) K) (Pi.single (Sum.inl 0) 1) :=
    KTabD.mem_lineStab.mpr ⟨1, by
      rw [one_smul]
      exact KTabC.mem_vecStab.mp ht0⟩
  have htB : t ∈ borelSubgroup (m + 2) K := by
    rw [← flagStabilizer_inf_eq_borelSubgroup m K]
    refine ⟨htQα, ?_⟩
    rwa [lineStab_statedSp_eq_flagStabilizer] at htQ0
  exact sp_conj_eq_one_of_mem_borel_vecStab m htα htB ht0 hodd

theorem kTab23cNineAt_of_realizes_sp {W : Type} [CommGroup W] [Finite W]
    (H : Subgroup (MulAut W)) (m : ℕ) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hreal : (FFModel.nat (StatedSp (m + 2) K)).Realizes H ⊤ ⊥) : KTab23cNineAt W H := by
  have hline : KTabC.SylowFixedLine (StatedSp (m + 2) K) (Pi.single (Sum.inl 0) 1) :=
    KTabD.sylowFixedLine_statedSp (K := K) (m + 2)
  have he0 : (Pi.single (Sum.inl 0) 1 : Fin (m + 2) ⊕ Fin (m + 2) → K) ≠ 0 :=
    Pi.single_ne_zero_iff.mpr (one_ne_zero : (1 : K) ≠ 0)
  refine kTab23cNineAt_of_model H (SymplecticFlag.unipotent (m + 2) K)
    (SymplecticHigher.flagStabilizer (m + 2) K (Set.Icc 2 (m + 2)))
    (KTabD.lineStab (StatedSp (m + 2) K) (Pi.single (Sum.inl 0) 1))
    (KTabC.vecStab (StatedSp (m + 2) K).subtype (Pi.single (Sum.inl 0) 1)) ?_
    (isParabolicTwo_flagStabilizer_alpha m K) (unipotent_le_flagStabilizer_alpha m K)
    (not_flagStabilizer_alpha_le_lineStab m K)
    (fun P hP hU hnot => flagStabilizer_alpha_le_of_parabolic m hP hU hnot) ?_
  · intro S
    obtain ⟨U, hU⟩ := SymplecticFlag.exists_sylow_unipotent (K := K) 2 (m + 2)
    obtain ⟨φ, h1, h2, h3⟩ := exists_mulEquiv_pointStab_fixSub_eq_map_sylow hreal he0 hline U
      (hU ▸ unipotent_le_lineStab m K) S
    exact ⟨φ, hU ▸ h1, h2, h3⟩
  · exact fun t ht hodd => sp_eq_one_of_mem_hinf_vecStab m ht hodd

theorem kTab23cNineAt_sp4 {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W))
    {n : ℕ} (h : NatSpn H ⊤ ⊥ 4 n) : KTab23cNineAt W H := by
  obtain ⟨-, K, hKf, hKfin, hKcard, hreal⟩ := h
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hn : 1 ≤ n := by
    have hcard : 1 < Nat.card K := Finite.one_lt_card
    rw [hKcard] at hcard
    by_contra hn
    have h0 : n = 0 := by omega
    subst h0
    norm_num at hcard
  haveI : CharP K 2 := uc22p22d_charP_two hn hKcard
  exact kTab23cNineAt_of_realizes_sp H (m := 0) (K := K) hreal

theorem kTab23cNineAt_sp6 {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W))
    {n : ℕ} (h : NatSpn H ⊤ ⊥ 6 n) : KTab23cNineAt W H := by
  obtain ⟨-, K, hKf, hKfin, hKcard, hreal⟩ := h
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hn : 1 ≤ n := by
    have hcard : 1 < Nat.card K := Finite.one_lt_card
    rw [hKcard] at hcard
    by_contra hn
    have h0 : n = 0 := by omega
    subst h0
    norm_num at hcard
  haveI : CharP K 2 := uc22p22d_charP_two hn hKcard
  exact kTab23cNineAt_of_realizes_sp H (m := 1) (K := K) hreal

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTab23cNine
