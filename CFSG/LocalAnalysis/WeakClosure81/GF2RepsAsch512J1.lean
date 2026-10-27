module

public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineCF
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J1A5GenHolds
public import CFSG.Quasithin.EmptyFaithful.S1565L11
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd
public import CFSG.LocalAnalysis.SteinbergSFRankOneSelectorSmall
public import CFSG.Quasithin.Recognition.F112Crit.ConjAut
public import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsSz IsL3)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open CFSG.Blueprint (LieModel)
open CFSG.Open (StatedProj StatedSL)

theorem le_natCard_of_isCalL1 {X : Type} [Group X]
    (h : IsCalL1 X) : 504 ≤ Nat.card X := by
  obtain ⟨n, hodd, hn1, hL2 | hSz | hL3⟩ := h
  · have hn3 : 3 ≤ n := by
      obtain ⟨k, hk⟩ := hodd
      omega
    have hm : LieModel X .PSL 2 2 n := hL2
    exact CFSG.Quasithin.le_card_of_psl2_or_sz hn3
      (Or.inl (hm.statedClassicalModel (by decide)))
  · have hn3 : 3 ≤ n := by
      obtain ⟨k, hk⟩ := hodd
      omega
    have hm : LieModel X .twistedB2 0 2 n := hSz
    exact CFSG.Quasithin.le_card_of_psl2_or_sz hn3
      (Or.inr (LieModel.suzukiModel hm).2)
  · have hn3 : 3 ≤ n := by
      obtain ⟨k, hk⟩ := hodd
      omega
    have hm : LieModel X .PSL 3 2 n := hL3
    obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ :=
      hm.statedClassicalModel (by decide)
    let _ : Field K := hKfield
    have _ : Finite K := hKfinite
    have hq8 : 8 ≤ Nat.card K := by
      rw [hKcard]
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    have h1 : 512 ≤ Nat.card K ^ 3 := by
      calc 512 = 8 ^ 3 := by norm_num
        _ ≤ Nat.card K ^ 3 := Nat.pow_le_pow_left hq8 3
    have h2 : 63 ≤ Nat.card K ^ 2 - 1 := by
      have h64 : 64 ≤ Nat.card K ^ 2 := by
        calc 64 = 8 ^ 2 := by norm_num
          _ ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left hq8 2
      omega
    have h3 : 1 ≤ Nat.card K ^ 3 - 1 := by omega
    have hP : 504 * 3 ≤
        Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) := by
      calc 504 * 3 = 1512 := by norm_num
        _ ≤ 512 * 63 * 1 := by norm_num
        _ ≤ Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    have hformula :=
      CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSL_three_mul (F := K)
    have hg : Nat.gcd 3 (Nat.card K - 1) ≤ 3 :=
      Nat.gcd_le_left (Nat.card K - 1) (by norm_num)
    have hmain : 504 * 3 ≤ Nat.card (StatedProj (StatedSL 3 K)) * 3 := by
      calc 504 * 3 ≤
          Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) := hP
        _ = Nat.card (StatedProj (StatedSL 3 K)) *
              Nat.gcd 3 (Nat.card K - 1) := hformula.symm
        _ ≤ Nat.card (StatedProj (StatedSL 3 K)) * 3 := Nat.mul_le_mul_left _ hg
    have h504 : 504 ≤ Nat.card (StatedProj (StatedSL 3 K)) :=
      Nat.le_of_mul_le_mul_right hmain (by norm_num)
    rwa [Nat.card_congr e.toEquiv]

theorem not_hasCompFactor_isCalL1_of_natCard_lt
    {Q : Type} [Group Q] [Finite Q] {K : Subgroup Q} (h : Nat.card K < 504) :
    ¬ HasCompFactor K IsCalL1 := by
  rintro ⟨L, hLgroup, hcf, hclass⟩
  let _ : Group L := hLgroup
  have hdvd : Nat.card L ∣ Nat.card K := isCompositionFactor_natCard_dvd hcf
  have hle : Nat.card L ≤ Nat.card K := Nat.le_of_dvd Nat.card_pos hdvd
  have h504 : 504 ≤ Nat.card L := le_natCard_of_isCalL1 hclass
  omega

theorem lGen_calL1_eq_of_isJ1
    {Q : Type} [Group Q] [Finite Q] {H T : Subgroup Q}
    (hH : CFSG.LocalAnalysis.UniquenessCase.UC22.IsJ1 ↥H)
    (hTH : T ≤ H) (hT : IsPGroup 2 T) :
    lGen IsCalL1 H T = H := by
  classical
  let U : Subgroup H := T.subgroupOf H
  have hU : IsPGroup 2 U :=
    hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
  let S : Subgroup (MulAut H) := U.map (MulAut.conj : H →* MulAut H)
  have hS : IsPGroup 2 S := hU.map (MulAut.conj : H →* MulAut H)
  obtain ⟨Δ, -, hΔinv, hΔgen⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.k_J1A5Gen_holds
      (X := ↥H) hH S hS
  have hUcard : Nat.card U ≤ 8 :=
    CFSG.LocalAnalysis.SymplecticFourStandard.RankOneSelector.card_le_of_J1 hH hU
  obtain ⟨eH⟩ := hH
  have hHcard : Nat.card H = 175560 :=
    (Nat.card_congr eH.toEquiv).trans CFSG.Sporadic.J1.card_J1
  have hAle : ∀ A ∈ Δ, A ≤ (lGen IsCalL1 H T).comap H.subtype := by
    intro A hA
    obtain ⟨hAalt, hAinv⟩ := hΔinv A hA
    have hUnorm : U ≤ Subgroup.normalizer (A : Set H) := by
      intro u hu
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact hAinv (MulAut.conj (u : H))
        (Subgroup.mem_map.mpr ⟨(u : H), hu, rfl⟩)
    obtain ⟨eA⟩ := hAalt
    have hAcard : Nat.card A = 60 := by
      rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup,
        Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num [Nat.factorial]
    have hBcard : Nat.card (A ⊔ U : Subgroup H) ≤ 480 := by
      have h := CFSG.Quasithin.F112Crit.card_sup_le_of_le_normalizer hUnorm
      rw [sup_comm] at h
      calc Nat.card (A ⊔ U : Subgroup H) ≤ Nat.card U * Nat.card A := h
        _ ≤ 8 * 60 := Nat.mul_le_mul hUcard (le_of_eq hAcard)
        _ = 480 := by norm_num
    have hCcard : Nat.card ((A ⊔ U : Subgroup H).map H.subtype) ≤ 480 := by
      rw [Subgroup.card_map_of_injective H.subtype_injective]
      exact hBcard
    have hCmem : (A ⊔ U : Subgroup H).map H.subtype ∈ calLT IsCalL1 H T := by
      refine ⟨?_, ?_, ?_⟩
      · intro t ht
        exact Subgroup.mem_map.mpr
          ⟨⟨t, hTH ht⟩, Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr ht), rfl⟩
      · have hCle : (A ⊔ U : Subgroup H).map H.subtype ≤ H :=
          Subgroup.map_subtype_le (A ⊔ U : Subgroup H)
        refine lt_of_le_of_ne hCle ?_
        intro hCH
        have hcard : Nat.card ((A ⊔ U : Subgroup H).map H.subtype) = Nat.card H := by rw [hCH]
        omega
      · exact not_hasCompFactor_isCalL1_of_natCard_lt (by omega)
    refine Subgroup.map_le_iff_le_comap.mp ?_
    exact le_trans (Subgroup.map_mono le_sup_left)
      (le_iSup₂_of_le ((A ⊔ U : Subgroup H).map H.subtype) hCmem le_rfl)
  have htop : (⊤ : Subgroup H) ≤ (lGen IsCalL1 H T).comap H.subtype := by
    rw [← hΔgen]
    exact iSup₂_le fun A hA => hAle A hA
  have hHle : H ≤ lGen IsCalL1 H T := by
    intro h hh
    have hmem : (⟨h, hh⟩ : H) ∈ (lGen IsCalL1 H T).comap H.subtype :=
      htop (Subgroup.mem_top (⟨h, hh⟩ : H))
    exact (Subgroup.mem_comap).mp hmem
  have hle : lGen IsCalL1 H T ≤ H := by
    refine iSup₂_le fun X hX => ?_
    exact hX.2.1.le
  exact le_antisymm hle hHle

end CFSG.LocalAnalysis.WeakClosure81
