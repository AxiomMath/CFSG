module

public import CFSG.Quasithin.Recognition.St84.Gen.AmalVertexLocal
public import CFSG.Quasithin.Recognition.St84.Gen.D4qAmalDefs
public import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne
import CFSG.Quasithin.Recognition.Stroth.Str86Frame
import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.Quasithin.Recognition.St84.Gen.L2SectionHall

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
  CFSG.QuasithinUnique.C5 CFSG.LieType.BorelTits
open scoped MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

theorem D4qLocalData.one_le (hD : D4qLocalData L1 L2 S f) : 1 ≤ f := by
  obtain ⟨F, hField, hFintype, hFcard, -⟩ := hD.nat_right
  letI := hField
  letI := hFintype
  have htwo : 2 ≤ Fintype.card F := Fintype.one_lt_card
  by_contra hf
  have hf0 : f = 0 := by omega
  rw [hf0, pow_zero] at hFcard
  omega

theorem D4qLocalData.twoPart_left (hD : D4qLocalData L1 L2 S f)
    (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) : twoPart L1 = 2 ^ (12 * f) := by
  have hf : 1 ≤ f := hD.one_le
  have h := twoPart_of_isL2Quot (a := 9 * f) (f := 3 * f) (by omega) h1 hD.card_left
  rwa [show 9 * f + 3 * f = 12 * f by ring] at h

theorem D4qLocalData.twoPart_right (hD : D4qLocalData L1 L2 S f) :
    twoPart L2 = 2 ^ (12 * f) := by
  have hf : 1 ≤ f := hD.one_le
  obtain ⟨F, hField, hFintype, hFcard, α, hαsurj, hαker, -⟩ := hD.nat_right
  letI := hField
  letI := hFintype
  have hker : α.ker = CFSG.pCore 2 ↥L2 := hαker
  have hquot : Nat.card (oTwoQuot ↥L2) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
    have h1 : Nat.card (↥L2 ⧸ α.ker) =
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hαsurj).toEquiv
    rw [hker] at h1
    rw [h1, CFSG.Quasithin.card_sl_two_of_fintype F, hFcard]
  have h2f : (2 ^ f) ^ 2 = 2 ^ (2 * f) := by
    rw [← pow_mul]
    congr 1
    ring
  refine twoPart_of_card (u := (2 ^ f) ^ 2 - 1) ?_ ?_
  · rw [h2f]
    exact odd_two_pow_sub_one (by omega)
  · rw [card_eq_card_oTwoQuot_mul, hquot, hD.card_right]
    rw [show 12 * f = 11 * f + f by ring, pow_add]
    ring

theorem D4qLocalData.le_left (hH : Hyp111 L1 L2 S) (hD : D4qLocalData L1 L2 S f)
    (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) : S ≤ L1 := by
  refine hH.le_left_of_twoPart ?_
  rw [hD.twoPart_left h1, hD.card_S]

theorem D4qLocalData.le_right (hH : Hyp111 L1 L2 S) (hD : D4qLocalData L1 L2 S f) :
    S ≤ L2 := by
  refine hH.le_right_of_twoPart ?_
  rw [hD.twoPart_right, hD.card_S]

theorem D4qLocalData.isSylowTwoOf_left (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) :
    IsSylowTwoOf S L1 :=
  isSylowTwoOf_of_card_eq (hD.le_left hH h1) hH.h1.pgroup
    (by rw [hD.card_S, hD.twoPart_left h1])

theorem D4qLocalData.isSylowTwoOf_right (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) : IsSylowTwoOf S L2 :=
  isSylowTwoOf_of_card_eq (hD.le_right hH) hH.h2.pgroup
    (by rw [hD.card_S, hD.twoPart_right])

theorem D4qLocalData.isSylowTwoOf_sup_bigB_left (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) :
    IsSylowTwoOf S (L1 ⊔ bigB L1 L2 S) :=
  isSylowTwoOf_sup_bigB_left_of_le hH (hD.le_left hH h1) (hD.le_right hH)

theorem D4qLocalData.pCoreOf_sup_bigB_left (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) :
    pCoreOf 2 (L1 ⊔ bigB L1 L2 S) = pCoreOf 2 L1 :=
  pCoreOf_sup_bigB_left_of_le hH (hD.le_left hH h1) (hD.le_right hH)

theorem D4qLocalData.pCoreOf_sup_bigB_right (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) :
    pCoreOf 2 (L2 ⊔ bigB L1 L2 S) = pCoreOf 2 L2 :=
  pCoreOf_sup_bigB_right_of_le hH (hD.le_left hH h1) (hD.le_right hH)

theorem D4qLocalData.bigB_eq_inf_normalizer_left (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) :
    bigB L1 L2 S = (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.normalizer (S : Set G) := by
  have hf : 1 ≤ f := hD.one_le
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 3 * f) (n := f) (by omega) hf hH h1 h2
  have h := F1.bigB_eq_parabolic_inf hR
  rwa [show (S ⊓ L1 : Subgroup G) = S from inf_eq_left.mpr (hD.le_left hH h1)] at h

theorem D4qLocalData.sup_pCoreOf (hH : Hyp111 L1 L2 S) (hD : D4qLocalData L1 L2 S f)
    (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) : pCoreOf 2 L1 ⊔ pCoreOf 2 L2 = S := by
  have hf : 1 ≤ f := hD.one_le
  have hS1 : S ≤ L1 := hD.le_left hH h1
  have hQ1S : pCoreOf 2 L1 ≤ S := hH.pCoreOf_le_left
  have hQ2S : pCoreOf 2 L2 ≤ S := hH.pCoreOf_le_right
  have hQ1L : pCoreOf 2 L1 ≤ L1 := pCoreOf_le 2 L1
  have hQ2L : pCoreOf 2 L2 ≤ L1 := hQ2S.trans hS1
  set K : Subgroup G := pCoreOf 2 L1 ⊔ pCoreOf 2 L2 with hKdef
  have hKL : K ≤ L1 := by
    rw [hKdef]
    exact sup_le hQ1L hQ2L
  have hKleS : K ≤ S := by
    rw [hKdef]
    exact sup_le hQ1S hQ2S
  let K1 := ↥L1
  let π : K1 →* oTwoQuot K1 := QuotientGroup.mk' (CFSG.pCore 2 K1)
  let T1 : Subgroup K1 := (S ⊓ L1).subgroupOf L1
  have hT1syl : IsSylowTwoOf T1 ⊤ := by
    refine ⟨le_top, hH.h1.sylow.2.1.of_equiv
      (Subgroup.subgroupOfEquivOfLe hH.h1.sylow.1).symm, ?_⟩
    rw [show (T1.subgroupOf ⊤).index = T1.index from by
      rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]]
    exact hH.h1.sylow.2.2
  let P1 : Sylow 2 K1 := hT1syl.2.1.toSylow hH.h1.sylow.2.2
  let P : Sylow 2 (oTwoQuot K1) := P1.mapSurjective (QuotientGroup.mk'_surjective _)
  have hPcoe : (P : Subgroup (oTwoQuot K1)) = T1.map π :=
    Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective _) P1
  set H : Subgroup (oTwoQuot K1) := (K.subgroupOf L1).map π with hHdef
  have hHP : H ≤ (P : Subgroup (oTwoQuot K1)) := by
    rw [hHdef, hPcoe]
    refine Subgroup.map_mono ?_
    intro x hx
    have hxK : (x : G) ∈ K := Subgroup.mem_subgroupOf.mp hx
    exact Subgroup.mem_subgroupOf.mpr ⟨hKleS hxK, x.2⟩
  have hHne : H ≠ ⊥ := by
    intro hbot
    have hle : K ≤ pCoreOf 2 L1 := by
      intro x hxK
      have hxL : x ∈ L1 := hKL hxK
      have hxsub : (⟨x, hxL⟩ : K1) ∈ K.subgroupOf L1 := Subgroup.mem_subgroupOf.mpr hxK
      have hxH : π (⟨x, hxL⟩ : K1) ∈ H := by
        rw [hHdef]
        exact Subgroup.mem_map_of_mem π hxsub
      rw [hbot] at hxH
      have hx1 : π (⟨x, hxL⟩ : K1) = 1 := Subgroup.mem_bot.mp hxH
      exact (CFSG.mem_openPCoreOf_iff (⟨x, hxL⟩ : K1)).mpr
        ((QuotientGroup.eq_one_iff (⟨x, hxL⟩ : K1)).mp hx1)
    have hQ2K : pCoreOf 2 L2 ≤ K := by
      rw [hKdef]
      exact le_sup_right
    have hcardle : Nat.card (pCoreOf 2 L2) ≤ Nat.card (pCoreOf 2 L1) :=
      Subgroup.card_le_of_le (hQ2K.trans hle)
    rw [hD.card_left, hD.card_right] at hcardle
    have hlt : 2 ^ (9 * f) < 2 ^ (11 * f) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hBNK : borelOf L1 S ≤ Subgroup.normalizer (K : Set G) := by
    rw [hKdef]
    exact (le_sup_left.trans le_sup_left :
        borelOf L1 S ≤ bigB L1 L2 S).trans
      ((le_inf hH.bigB_le_normalizer_pCoreOf_left hH.bigB_le_normalizer_pCoreOf_right).trans
        (Subgroup.inf_normalizer_le_normalizer_sup (pCoreOf 2 L1) (pCoreOf 2 L2)))
  have hB1K : (borelOf L1 S).subgroupOf L1 ≤
      Subgroup.normalizer ((K.subgroupOf L1) : Set K1) := by
    intro b hb
    have hbG : (b : G) ∈ Subgroup.normalizer (K : Set G) :=
      hBNK (Subgroup.mem_subgroupOf.mp hb)
    rw [Subgroup.mem_normalizer_iff] at hbG ⊢
    intro x
    constructor
    · intro hx
      have hxK : (x : G) ∈ K := Subgroup.mem_subgroupOf.mp hx
      have hA : (b : G) * (x : G) * (b : G)⁻¹ ∈ K := (hbG (x : G)).mp hxK
      exact Subgroup.mem_subgroupOf.mpr (by simpa using hA)
    · intro hx
      have hxK : (b : G) * (x : G) * (b : G)⁻¹ ∈ K := by
        simpa using (Subgroup.mem_subgroupOf.mp hx)
      exact Subgroup.mem_subgroupOf.mpr ((hbG (x : G)).mpr hxK)
  have hNP : Subgroup.normalizer ((P : Subgroup (oTwoQuot K1)) : Set (oTwoQuot K1)) =
      ((borelOf L1 S).subgroupOf L1).map π := by
    have hmap := (F1.map_borelOf_eq_normalizer hH.h1.sylow).2.2
    rw [hPcoe]
    simpa [T1, π] using hmap.symm
  have hNPH : Subgroup.normalizer ((P : Subgroup (oTwoQuot K1)) : Set (oTwoQuot K1)) ≤
      Subgroup.normalizer (H : Set (oTwoQuot K1)) := by
    rw [hNP]
    calc ((borelOf L1 S).subgroupOf L1).map π
        ≤ (Subgroup.normalizer ((K.subgroupOf L1) : Set K1)).map π :=
          Subgroup.map_mono hB1K
      _ ≤ Subgroup.normalizer (((K.subgroupOf L1).map π) : Set (oTwoQuot K1)) :=
          Subgroup.le_normalizer_map π
      _ = Subgroup.normalizer (H : Set (oTwoQuot K1)) := by rw [hHdef]
  have hTH : (P : Subgroup (oTwoQuot K1)) ≤ H := by
    intro x hxP
    by_cases hx1 : x = 1
    · rw [hx1]
      exact H.one_mem
    · obtain ⟨h, hh1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hHne
      have hhP : (h : oTwoQuot K1) ∈ (P : Subgroup (oTwoQuot K1)) := hHP h.2
      have hh1' : (h : oTwoQuot K1) ≠ 1 := fun he => hh1 (Subtype.ext he)
      obtain ⟨d, hdN, hdh⟩ := CFSG.Quasithin.Stroth.psl2_normalizer_transitive
        (n := 3 * f) (by omega) h1 P hhP hxP hh1' hx1
      have hdNH : d ∈ Subgroup.normalizer (H : Set (oTwoQuot K1)) := hNPH hdN
      have hmem : d * (h : oTwoQuot K1) * d⁻¹ ∈ H :=
        (Subgroup.mem_normalizer_iff.mp hdNH (h : oTwoQuot K1)).mp h.2
      rwa [hdh] at hmem
  have hSK : S ≤ K := by
    intro s hs
    have hsL : s ∈ L1 := hS1 hs
    have hsP : π (⟨s, hsL⟩ : K1) ∈ (P : Subgroup (oTwoQuot K1)) := by
      rw [hPcoe]
      exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ⟨hs, hsL⟩)
    have hsH : π (⟨s, hsL⟩ : K1) ∈ H := hTH hsP
    obtain ⟨k, hk, hkπ⟩ := Subgroup.mem_map.mp hsH
    have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
    have hdiff : (k : G)⁻¹ * s ∈ pCoreOf 2 L1 := by
      have hπ1 : π (k⁻¹ * (⟨s, hsL⟩ : K1)) = 1 := by
        rw [map_mul, map_inv, hkπ]
        group
      exact (CFSG.mem_openPCoreOf_iff (k⁻¹ * (⟨s, hsL⟩ : K1))).mpr
        ((QuotientGroup.eq_one_iff (k⁻¹ * (⟨s, hsL⟩ : K1))).mp hπ1)
    have hEq : s = (k : G) * ((k : G)⁻¹ * s) := by group
    rw [hEq]
    exact K.mul_mem hkK ((le_sup_left : pCoreOf 2 L1 ≤ pCoreOf 2 L1 ⊔ pCoreOf 2 L2) hdiff)
  exact le_antisymm hKleS hSK

theorem D4qLocalData.card_inf_pCoreOf (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) :
    Nat.card ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2) = 2 ^ (8 * f) := by
  have hS1 : S ≤ L1 := hD.le_left hH h1
  have hN : pCoreOf 2 L2 ≤ Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
    (hH.pCoreOf_le_right.trans hS1).trans (le_normalizer_pCoreOf 2 L1)
  have h := card_sup_mul_card_inf_of_le_normalizer
    (A := pCoreOf 2 L2) (B := pCoreOf 2 L1) hN
  rw [inf_comm (pCoreOf 2 L2) (pCoreOf 2 L1), sup_comm (pCoreOf 2 L2) (pCoreOf 2 L1),
    hD.sup_pCoreOf hH h1, hD.card_S, hD.card_left, hD.card_right] at h
  have h20 : 2 ^ (11 * f) * 2 ^ (9 * f) = 2 ^ (12 * f) * 2 ^ (8 * f) := by
    rw [← pow_add, ← pow_add]
    congr 1
    ring
  rw [h20] at h
  exact Nat.mul_left_cancel (by positivity : 0 < 2 ^ (12 * f)) h

end CFSG.Quasithin.F112R.St84

end
