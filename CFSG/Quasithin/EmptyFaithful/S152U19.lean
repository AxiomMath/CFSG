module

public import CFSG.Quasithin.EmptyFaithful.S152U18
public import CFSG.Quasithin.EmptyFaithful.QTKELocal

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Main

variable {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I : Subgroup G}

theorem Z_le_of_normal_ne_bot152 (hs : Setting152 T Mc M) (hD : Inputs152 T Mc M H B₀ I)
    {N : Subgroup G} (hNT : N ≤ T) (hTN : T ≤ Subgroup.normalizer (N : Set G))
    (hN2 : ∀ x ∈ N, x ^ 2 = 1) (hN1 : N ≠ ⊥) : quasithinOmegaOneCenter T ≤ N := by
  have hT2 : IsPGroup 2 T := hs.qtfe.sylow.1
  have hnormal : (N.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNT).mpr hTN
  have : Group.IsNilpotent ↥T := hT2.isNilpotent
  have hne' : N.subgroupOf T ≠ ⊥ := by
    obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := N)).1 hN1
    intro hbot
    have hmem : (⟨(x : G), hNT x.2⟩ : ↥T) ∈ N.subgroupOf T := x.2
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hx1 (Subtype.ext (congrArg (fun z : ↥T => (z : G)) hmem))
  have hcenter := Group.IsNilpotent.inf_center_ne_bot_of_normal (H := N.subgroupOf T) hne'
  obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hcenter
  have hyN : ((y : ↥T) : G) ∈ N := y.2.1
  have hyT : ((y : ↥T) : G) ∈ T := (y : ↥T).2
  have hycent : ((y : ↥T) : G) ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have := Subgroup.mem_center_iff.mp y.2.2 ⟨t, ht⟩
    exact congrArg Subtype.val this
  have hy2 : ((y : ↥T) : G) ^ 2 = 1 := hN2 _ hyN
  have hy1' : ((y : ↥T) : G) ≠ 1 := by
    intro h
    apply hy1
    exact Subtype.ext (Subtype.ext h)
  have hyZ : ((y : ↥T) : G) ∈ quasithinOmegaOneCenter T :=
    mem_quasithinOmegaOneCenter_iff.mpr ⟨hyT, hycent, hy2⟩
  have hzp : Subgroup.zpowers ((y : ↥T) : G) ≤ quasithinOmegaOneCenter T :=
    Subgroup.zpowers_le.mpr hyZ
  have hcard : Nat.card (Subgroup.zpowers ((y : ↥T) : G)) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hy2 hy1'
  have hZeq : Subgroup.zpowers ((y : ↥T) : G) = quasithinOmegaOneCenter T :=
    Subgroup.eq_of_le_of_card_ge hzp (by rw [hcard, hD.h17.2.1])
  rw [← hZeq]
  exact Subgroup.zpowers_le.mpr hyN

theorem lemma_15_2_19_two (hs : Setting152 T Mc M) (hB₀ : IsB0 T Mc M B₀)
    (hI : Hyp15215 T Mc M B₀ I) (hD : Inputs152 T Mc M H B₀ I) (hOm : Om4FactsStatement)
    (hii : Concl15218ii T Mc M H B₀ I) : HypC23 I (pCoreOf 2 (M ⊓ I)) (M ⊓ I) := by
  obtain ⟨-, -, hΩ, -, -, -, -, hidx⟩ := hii
  have h36 := (om4_card152 hOm hΩ).1
  have h9 := (om4_card152 hOm hΩ).2
  have hMV : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hTM : T ≤ M := T_le_M152 hs
  have hTV : T ≤ Subgroup.normalizer (V154 T Mc M : Set G) := hTM.trans hMV
  have hM : quasithinIsMaxTwoLocal M := isMaxTwoLocal_M152 hs
  have hNiM : M ⊓ I ≤ M := inf_le_left
  have hCvNi : M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤ M ⊓ I :=
    le_inf inf_le_left ((cv_le_inf152 hs hD).trans inf_le_right)
  have hSNi : sOf152 T Mc M B₀ ≤ M ⊓ I := le_inf (S_le_T152.trans hTM) (S_le_I152 hD)
  have hT4 := card_autOn_T152 hs h36 h9
  have hSbB := autOn_S_eq_B₀152 hs hB₀ hD hT4
  have hB₀Nb : B₀ ≤ autOn (M ⊓ I) (V154 T Mc M) := hSbB ▸ A4.autOn_mono hSNi
  have hNb6 : Nat.card (autOn (M ⊓ I) (V154 T Mc M)) = 6 := by
    have h1 := relIndex_autOn hNiM hMV hCvNi
    have hmul := Subgroup.relIndex_mul_card (autOn (M ⊓ I) (V154 T Mc M))
      (autOn M (V154 T Mc M))
    rw [inf_of_le_left (A4.autOn_mono hNiM), h1, hidx, h36] at hmul
    omega
  have hO2 : pCoreOf 2 (autOn (M ⊓ I) (V154 T Mc M)) = ⊥ := by
    by_contra hne
    have hB2 : IsPGroup 2 B₀ := IsPGroup.of_card (n := 1) (by rw [hB₀.2.1]; norm_num)
    have hsylB : IsSylowTwoOf B₀ (autOn (M ⊓ I) (V154 T Mc M)) := by
      refine ⟨hB₀Nb, hB2, ?_⟩
      have hmul := Subgroup.relIndex_mul_card B₀ (autOn (M ⊓ I) (V154 T Mc M))
      rw [inf_of_le_left hB₀Nb, hNb6, hB₀.2.1] at hmul
      have h3 : B₀.relIndex (autOn (M ⊓ I) (V154 T Mc M)) = 3 := by omega
      intro h2
      have h2' : 2 ∣ B₀.relIndex (autOn (M ⊓ I) (V154 T Mc M)) := h2
      rw [h3] at h2'
      omega
    have hPB : pCoreOf 2 (autOn (M ⊓ I) (V154 T Mc M)) ≤ B₀ :=
      EscapingLocal.pCoreOf_le_of_isSylowTwoOf hsylB
    have hPcard : Nat.card (pCoreOf 2 (autOn (M ⊓ I) (V154 T Mc M))) = 2 := by
      have hdvd := Subgroup.card_dvd_of_le hPB
      rw [hB₀.2.1] at hdvd
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd (Subgroup.card_eq_one.mp h) hne
      · exact h
    have hPeq : pCoreOf 2 (autOn (M ⊓ I) (V154 T Mc M)) = B₀ :=
      Subgroup.eq_of_le_of_card_ge hPB (by rw [hPcard, hB₀.2.1])
    have hNbN : autOn (M ⊓ I) (V154 T Mc M) ≤ Subgroup.normalizer (B₀ : Set (MulAut (V154 T Mc M))) := by
      have := le_normalizer_pCoreOf 2 (autOn (M ⊓ I) (V154 T Mc M))
      rwa [hPeq] at this
    have hNbT : autOn (M ⊓ I) (V154 T Mc M) ≤ autOn T (V154 T Mc M) := fun g hg =>
      normalizer_autS_le_autT hs hB₀ hD hOm g (A4.autOn_mono hNiM hg)
        (by rw [hSbB]; exact hNbN hg)
    have hT2grp := (isPGroup_autOn hs.qtfe.sylow.1 hTV).to_le hNbT
    obtain ⟨n, hn⟩ := hT2grp.exists_card_eq
    have h6 : 2 ^ n = 6 := hn.symm.trans hNb6
    have h3 : 3 ∣ 2 ^ n := h6 ▸ (by norm_num : 3 ∣ 6)
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hRN : pCoreOf 2 (M ⊓ I) ≤ M ⊓ I := pCoreOf_le 2 _
  have hRV' : pCoreOf 2 (M ⊓ I) ≤ Subgroup.normalizer (V154 T Mc M : Set G) :=
    hRN.trans (hNiM.trans hMV)
  have hR2 : IsPGroup 2 (pCoreOf 2 (M ⊓ I)) := pCoreOf_isPGroup 2 _
  have hRV : pCoreOf 2 (M ⊓ I) ≤ Subgroup.centralizer (V154 T Mc M : Set G) := by
    by_contra hcon
    have hne : autOn (pCoreOf 2 (M ⊓ I)) (V154 T Mc M) ≠ ⊥ :=
      autOn_ne_bot_of_not_le_centralizer hRV' hcon
    have hRb : autOn (pCoreOf 2 (M ⊓ I)) (V154 T Mc M) ≤
        pCoreOf 2 (autOn (M ⊓ I) (V154 T Mc M)) :=
      le_pCoreOf_of_le_normalizer 2 (A4.autOn_mono hRN)
        (autOn_le_normalizer_autOn (hNiM.trans hMV) hRV' (le_normalizer_pCoreOf 2 (M ⊓ I)))
        (isPGroup_autOn hR2 hRV')
    rw [hO2] at hRb
    exact hne (le_bot_iff.mp hRb)
  have hCvN : M ≤ Subgroup.normalizer
      ((M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf_centralizer' Subgroup.le_normalizer hMV
  have hRCv : pCoreOf 2 (M ⊓ I) ≤ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) :=
    le_inf (hRN.trans hNiM) hRV
  have hRle : pCoreOf 2 (M ⊓ I) ≤ pCoreOf 2 (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) :=
    le_pCoreOf_of_le_normalizer 2 hRCv (hCvNi.trans (le_normalizer_pCoreOf 2 (M ⊓ I))) hR2
  have hRge : pCoreOf 2 (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) ≤ pCoreOf 2 (M ⊓ I) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans hCvNi)
      (hNiM.trans (hCvN.trans (normalizer_le_normalizer_pCoreOf 2 _))) (pCoreOf_isPGroup 2 _)
  have hReq : pCoreOf 2 (M ⊓ I) =
      pCoreOf 2 (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) := le_antisymm hRle hRge
  have hMR : M ≤ Subgroup.normalizer (pCoreOf 2 (M ⊓ I) : Set G) := by
    rw [hReq]
    exact hCvN.trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hVp : IsPGroup 2 (V154 T Mc M) := fun x => ⟨1, Subtype.ext (by
    simpa using (isElemAbelian_V152 hs).2 x x.2)⟩
  have hVM : V154 T Mc M ≤ M := (V154_le_VZ T Mc M).trans (VZ_le_self hTM)
  have hVCv : V154 T Mc M ≤ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) :=
    le_inf hVM (fun x hx => by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact comm_of_isElemAbelian152 (isElemAbelian_V152 hs) hy hx)
  have hVR : V154 T Mc M ≤ pCoreOf 2 (M ⊓ I) := by
    rw [hReq]
    exact le_pCoreOf_of_le_normalizer 2 hVCv (inf_le_left.trans hMV) hVp
  have hRne : pCoreOf 2 (M ⊓ I) ≠ ⊥ := fun h =>
    V154_ne_bot hs.qtfe (le_bot_iff.mp (h ▸ hVR))
  have hNR : Subgroup.normalizer (pCoreOf 2 (M ⊓ I) : Set G) = M :=
    normalizer_eq_of_le_normalizer hM hRne hR2 hMR
  refine ⟨?_, ⟨hRN.trans inf_le_right, hRne, ?_⟩, inf_le_right, ?_, ?_⟩
  · exact (⟨stronglyQuasithin_of_pCoreOf_ne_bot hs.qtfe.qtke hI.inH.2,
      kGroup_of_pCoreOf_ne_bot hs.qtfe.qtke hs.qtfe.simple hs.qtfe.nonabelian hI.inH.2⟩ :
        SQTKGroup ↥I)
  · rw [hNR, inf_comm]
  · refine iSup_le fun C => iSup_le fun hCR => iSup_le fun hC1 => iSup_le fun hCch => ?_
    have hMC : M ≤ Subgroup.normalizer (C : Set G) := by
      have h1 := normalizer_le_normalizer_map_of_characteristic
        (C.subgroupOf (pCoreOf 2 (M ⊓ I)))
      rw [Subgroup.map_subgroupOf_eq_of_le hCR] at h1
      exact hNR ▸ h1
    rw [normalizer_eq_of_le_normalizer hM hC1 (hR2.to_le hCR) hMC, inf_comm]
  · have hconj : conjClosure (pCoreOf 2 (M ⊓ I)) (M ⊓ I) = pCoreOf 2 (M ⊓ I) := by
      apply le_antisymm
      · exact conjClosure_le fun h hh z hz =>
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (M ⊓ I) hh) z).mp hz
      · exact le_conjClosure _ _
    rw [hconj]
    refine ⟨le_rfl, hR2, ?_⟩
    rw [Subgroup.subgroupOf_self, Subgroup.index_top]
    exact fun h => absurd (Nat.le_of_dvd one_pos h) (by norm_num)

end Main

end CFSG.Quasithin
