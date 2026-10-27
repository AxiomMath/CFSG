module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
public import CFSG.LocalAnalysis.UniquenessCase.UC6R2
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3a
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoSyl
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineFour
import CFSG.LocalAnalysis.AGLEmbedding.EscapeTwoCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem le_of_mem_invStar9 {K X R Q : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hR : R ∈ InvStar9 K X p) (hQK : Q ≤ K) (hQ : IsPGroup p Q)
    (hXQ : X ≤ normalizer (Q : Set G)) (hRQ : R ≤ normalizer (Q : Set G)) : Q ≤ R :=
  le_sup_right.trans (hR.2 ⟨sup_le hR.1.1 hQK, hR.1.2.1.to_sup_of_normal_right' hQ hRQ,
    (le_inf hR.1.2.2 hXQ).trans (inf_normalizer_le_normalizer_sup _ _)⟩ le_sup_left)

theorem mem_invStar9_of_not_calCGS_le (D : Data G) (h910 : R910 D) {Y : Subgroup G}
    (hY : Y ∈ calY2Star9 D) (hC : ¬ UC6.calCGS (pCoreOf 2 Y) ≤ D.M) :
    pCoreOf 2 Y ∈ InvStar9 D.M Y 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 Y with hRdef
  have hRY : R ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hYR : Y ≤ normalizer (R : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  obtain ⟨C, hC1, hCR, hchar, hCM⟩ : ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ R ∧
      (C.subgroupOf R).Characteristic ∧ ¬ normalizer (C : Set G) ≤ D.M := by
    by_contra! h
    exact hC (iSup_le fun C => iSup_le fun hC1 => iSup_le fun hCR => iSup_le fun hchar =>
      h C hC1 hCR hchar)
  have hCY : C ≤ Y := hCR.trans hRY
  have hYC : Y ≤ normalizer (C : Set G) := hYR.trans (normalizer_le_normalizer_of_char hCR hchar)
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 Y
  have hSC : IsSylowOf 2 S (D.M ⊓ normalizer (C : Set G)) := by
    by_contra hS'
    have hU : calMOf (D.M ⊓ normalizer (C : Set G)) = {D.M} :=
      h910 Y hY C hC1 hCY ((normal_subgroupOf_iff_le_normalizer hCY).2 hYC) ⟨S, hS, hS'⟩
    have hloc : IsTwoLocal (normalizer (C : Set G)) := ⟨C, hC1, hR2.to_le hCR, rfl⟩
    obtain ⟨M', hCM', hmax⟩ := Finite.exists_le_maximal hloc
    have hmem : M' ∈ calMOf (D.M ⊓ normalizer (C : Set G)) :=
      ⟨⟨hmax.1, fun K hK hMK => le_antisymm (hmax.2 hK hMK) hMK⟩, inf_le_right.trans hCM'⟩
    rw [hU] at hmem
    exact hCM (hmem ▸ hCM')
  refine ⟨⟨hRY.trans hY.prop.1.1, hR2, hYR⟩, fun R₁ hR₁ hRR₁ => ?_⟩
  have hK2 : IsPGroup 2 ↥(R₁ ⊓ normalizer (R : Set G)) := hR₁.2.1.to_le inf_le_left
  have hYK : Y ≤ normalizer ((R₁ ⊓ normalizer (R : Set G) : Subgroup G) : Set G) :=
    (le_inf hR₁.2.2 (hYR.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hSK : S ⊔ (R₁ ⊓ normalizer (R : Set G)) = S := hSC.eq_of_le le_sup_left
    (sup_le hSC.le (le_inf (inf_le_left.trans hR₁.1)
      (inf_le_right.trans (normalizer_le_normalizer_of_char hCR hchar))))
    (hS.isPGroup.to_sup_of_normal_right' hK2 (hS.le.trans hYK))
  have hKR : R₁ ⊓ normalizer (R : Set G) ≤ R :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((le_sup_right.trans hSK.le).trans hS.le) hYK hK2
  by_contra hR₁R
  obtain ⟨x, hxR₁, hxR, hxN⟩ := CFSG.AGLEmbedding.exists_mem_normalizer_not_mem_of_lt_of_isPGroup
    hR₁.2.1 (lt_of_le_of_ne hRR₁ fun h => hR₁R h.ge)
  exact hxR (hKR (mem_inf.2 ⟨hxR₁, hxN⟩))

theorem calCGS_le_of_mem_invStar9 (D : Data G) {L X Y : Subgroup G} (hLM : L ≤ D.M)
    (hLN : D.M ≤ normalizer (L : Set G)) (hUM : UniqueMax D.M (L ⊔ D.T))
    (hcov : L = X ⊔ pCoreOf 2 L) (hXY : X ≤ Y) (hY : Y ∈ calY2_9 D) (hYL : Opp 3 Y ≤ L)
    (hR : pCoreOf 2 Y ∈ InvStar9 D.M Y 2) : UC6.calCGS (pCoreOf 2 Y) ≤ D.M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 Y with hRdef
  set O := pCoreOf 2 L with hOdef
  have hYM : Y ≤ D.M := hY.1.1
  have hMO : D.M ≤ normalizer (O : Set G) :=
    hLN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hOR : O ≤ R := le_of_mem_invStar9 hR ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLM)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) (hYM.trans hMO) (hR.1.1.trans hMO)
  have hLR : L ≤ normalizer (R : Set G) :=
    hcov.le.trans (sup_le (hXY.trans hR.1.2.2) (hOR.trans le_normalizer))
  have hRL : R ⊓ L ≤ O := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
    ((le_inf hLR le_normalizer).trans inf_normalizer_le_normalizer_inf)
    (hR.1.2.1.to_le inf_le_left)
  set C₀ := F08.CentOverO2 D.M L with hC₀def
  have hmemC : ∀ {c : G}, c ∈ C₀ ↔ c ∈ D.M ∧ ∀ l ∈ L, c * l * c⁻¹ * l⁻¹ ∈ O :=
    PartTwo.mem_centOverO2_iff
  have hRC : R ≤ C₀ := fun r hr => hmemC.2 ⟨hR.1.1 hr, fun l hl => hRL (mem_inf.2
    ⟨by simpa [mul_assoc] using
        R.mul_mem hr ((mem_normalizer_iff.1 (hLR hl) r⁻¹).1 (R.inv_mem hr)),
      L.mul_mem ((mem_normalizer_iff.1 (hLN (hR.1.1 hr)) l).1 hl) (L.inv_mem hl)⟩)⟩
  have hMC : D.M ≤ normalizer (C₀ : Set G) := le_normalizer_iff.2 fun m hm c hc => by
    obtain ⟨hcM, hcL⟩ := hmemC.1 hc
    refine hmemC.2 ⟨D.M.mul_mem (D.M.mul_mem hm hcM) (D.M.inv_mem hm), fun l hl => ?_⟩
    have hl' : m⁻¹ * l * m ∈ L := by
      simpa using (mem_normalizer_iff.1 (hLN (D.M.inv_mem hm)) l).1 hl
    have h := (mem_normalizer_iff.1 (hMO hm) _).1 (hcL _ hl')
    convert h using 1
    group
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 Y
  obtain ⟨P, hP, hSP⟩ : ∃ P : Subgroup G, IsSylowOf 2 P D.M ∧ S ≤ P := by
    obtain ⟨Q, hQ⟩ := (hS.isPGroup.comap_subtype (K := D.M)).exists_le_sylow
    exact ⟨(Q : Subgroup D.M).map D.M.subtype, ⟨Q, rfl⟩,
      fun s hs => ⟨⟨s, (hS.le.trans hYM) hs⟩, hQ hs, rfl⟩⟩
  have hPQ : P ≤ normalizer ((P ⊓ C₀ : Subgroup G) : Set G) :=
    (le_inf le_normalizer (hP.le.trans hMC)).trans inf_normalizer_le_normalizer_inf
  have hRQ : R ≤ P ⊓ C₀ := le_inf ((PartTwo.s16c7_pCoreOf_le_of_isSylowOf hS).trans hSP) hRC
  have hLQ : L ≤ normalizer ((P ⊓ C₀ : Subgroup G) : Set G) :=
    le_normalizer_iff.2 fun l hl q hq => by
      have hc0 : l * q * l⁻¹ * q⁻¹ ∈ O := by
        simpa [mul_assoc] using O.inv_mem ((hmemC.1 (mem_inf.1 hq).2).2 l hl)
      have hc : l * q * l⁻¹ * q⁻¹ ∈ P := (mem_inf.1 (hRQ (hOR hc0))).1
      exact mem_inf.2 ⟨by simpa using P.mul_mem hc (mem_inf.1 hq).1,
        (mem_normalizer_iff.1 (hMC (hLM hl)) q).1 (mem_inf.1 hq).2⟩
  have hYQ : Y ≤ normalizer ((P ⊓ C₀ : Subgroup G) : Set G) :=
    le_of_le_of_isSylowOf (hYL.trans hLQ) (hSP.trans hPQ) hS hY.2.2.2.2
  have hQR : P ⊓ C₀ = R :=
    le_antisymm (hR.2 ⟨inf_le_left.trans hP.le, hP.isPGroup.to_le inf_le_left, hYQ⟩ hRQ) hRQ
  have hPR : P ≤ normalizer (R : Set G) := hQR ▸ hPQ
  obtain ⟨m, hmM, hm⟩ := D.sylowM.exists_mem_conj hP
  have hmap : (L ⊔ D.T).map (MulAut.conj m).toMonoidHom ≤ normalizer (R : Set G) := by
    refine map_le_iff_le_comap.2 (sup_le (fun l hl => mem_comap.2 (hLR ?_))
      fun t ht => mem_comap.2 (hPR ((hm _).2 ?_)))
    · simpa using (mem_normalizer_iff.1 (hLN hmM) l).1 hl
    · simpa [mul_assoc] using ht
  have hU : calMOf ((L ⊔ D.T).map (MulAut.conj m).toMonoidHom) = {D.M} :=
    PartTwo.ElevenNine.uniqueMax_map_conj D hUM hmM
  refine iSup_le fun C => iSup_le fun hC1 => iSup_le fun hCR => iSup_le fun hchar => ?_
  have hloc : IsTwoLocal (normalizer (C : Set G)) := ⟨C, hC1, hR.1.2.1.to_le hCR, rfl⟩
  obtain ⟨M', hCM', hmax⟩ := Finite.exists_le_maximal hloc
  have hmem : M' ∈ calMOf ((L ⊔ D.T).map (MulAut.conj m).toMonoidHom) :=
    ⟨⟨hmax.1, fun K hK hMK => le_antisymm (hmax.2 hK hMK) hMK⟩,
      (hmap.trans (normalizer_le_normalizer_of_char hCR hchar)).trans hCM'⟩
  rw [hU] at hmem
  exact hmem ▸ hCM'

theorem calCGS_pCoreOf_le (D : Data G) (h910 : R910 D) {L X Y : Subgroup G} (hLM : L ≤ D.M)
    (hLN : D.M ≤ normalizer (L : Set G)) (hUM : UniqueMax D.M (L ⊔ D.T))
    (hcov : L = X ⊔ pCoreOf 2 L) (hXY : X ≤ Y) (hY : Y ∈ calY2Star9 D) (hYL : Opp 3 Y ≤ L) :
    UC6.calCGS (pCoreOf 2 Y) ≤ D.M := by
  by_contra hC
  exact hC (calCGS_le_of_mem_invStar9 D hLM hLN hUM hcov hXY hY.prop hYL
    (mem_invStar9_of_not_calCGS_le D h910 hY hC))

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
