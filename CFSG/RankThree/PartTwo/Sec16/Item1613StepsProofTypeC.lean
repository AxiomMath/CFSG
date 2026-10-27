module

import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofTypeCCore
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13Tools
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.Theta.ThreeCoreComponentNormalization
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
public import CFSG.RankThree.PartTwo.Sec16.Item169GeneralDefs
public import CFSG.Sporadic.Schreier.Co1WeightChar

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU projImage)

open CFSG.RankThree.PartTwo.Sec16.Proof169 CFSG.RankThree.PartTwo.Sec16.Proof1613 in
theorem kS1613TypeC :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Ctx169 G A c L →
      Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × projSL 3 (GaloisField 2 2)) →
      ¬ Odd (Nat.card (pPrimeCoreOf 3 (Subgroup.centralizer ({c} : Set G)))) →
      ∀ D : Subgroup G, D ≤ A ⊓ L → Nat.card D = 3 →
      ∀ u ∈ Subgroup.normalizer ((D ⊔ Subgroup.zpowers c : Subgroup G) : Set G) ⊓
          Subgroup.normalizer (D : Set G),
        A.map (MulAut.conj u).toMonoidHom ≤ Subgroup.normalizer (A : Set G) →
        A.map (MulAut.conj u).toMonoidHom ≠ A →
        A.map (MulAut.conj u).toMonoidHom ≤ Subgroup.normalizer (L : Set G) →
          ∃ E : Subgroup G, E ≤ A ⊔ A.map (MulAut.conj u).toMonoidHom ∧
            D ⊔ Subgroup.zpowers c ≤ E ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
            Late.sectionCentralizer E L ((aschbacherSolvableCore 3 L).map L.subtype) =
              (Subgroup.zpowers c : Set G) ∧
            Sec4.IsTypeCOn E L := by
  intro G _ _ A c L h ⟨ψ₀⟩ hev D hDAL hD3 u hu hAuA hne hAuL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcL, hAL9, -, ⟨χ⟩⟩ := facts_l34 h ψ₀
  have hK : Sec4.PiField true 2 2 (GaloisField 2 2) :=
    ⟨Nat.prime_two, by norm_num, by rw [GaloisField.card 2 2 (by norm_num)]; rfl⟩
  have hq : Sec4.ModThree true (2 ^ 2) := by
    change 2 ^ 2 % 3 = 1
    norm_num
  have hK4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  set e : L ⧸ aschbacherSolvableCore 3 L ≃*
      projImage (Sec4.slPi true 3 (2 ^ 2) (GaloisField 2 2)) :=
    χ.trans (MulEquiv.subgroupCongr (Sec4.projSL_eq_projImage _ _)) with he
  have hcA : c ∈ A := h.mem_A
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c hcA
  have hc1 : c ≠ 1 := fun h1 => hcL (h1 ▸ L.one_mem)
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)
  obtain ⟨d, hdD, hd1, rfl⟩ := Sec5.exists_eq_zpowers_of_card_eq_prime Nat.prime_three hD3
  have hdA : d ∈ A := (hDAL hdD).1
  set Au := A.map (MulAut.conj u).toMonoidHom with hAudef
  have hAu : CFSG.Assembly.IsElemAbelian 3 Au :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ A h.isElemAbelian
  have hAu27 : Nat.card Au = 27 := by
    rw [hAudef, Subgroup.card_map_of_injective (MulAut.conj u).injective, h.card_eq]
  set B := Subgroup.zpowers d ⊔ Subgroup.zpowers c with hB
  have hBA : B ≤ A := sup_le (Subgroup.zpowers_le.mpr hdA) (Subgroup.zpowers_le.mpr hcA)
  have hBAu : B ≤ Au := by
    have hBv : B.map (MulAut.conj u).toMonoidHom = B :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.mem_inf.mp hu).1
    rw [← hBv]
    exact Subgroup.map_mono hBA
  have hcAu : c ∈ Au := hBAu (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
  have hdAu : d ∈ Au := hBAu (Subgroup.mem_sup_left (Subgroup.mem_zpowers d))
  obtain ⟨w, hwAu, hwA⟩ : ∃ w ∈ Au, w ∉ A := by
    by_contra hall
    push Not at hall
    exact hne (Subgroup.eq_of_le_of_card_ge (fun w hw => hall w hw) (by rw [hAu27, h.card_eq]))
  have hw3 : w ^ 3 = 1 := hAu.2 w hwAu
  have hAuc : ∀ a ∈ Au, ∀ b ∈ Au, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAu.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hwc : w * c = c * w := hAuc w hwAu c hcAu
  have hwd : w * d = d * w := hAuc w hwAu d hdAu
  have hwNA : w ∈ Subgroup.normalizer (A : Set G) := hAuA hwAu
  have hAN : A ≤ Subgroup.normalizer (L : Set G) :=
    h.A_le_centralizer.trans (centralizer_le_normalizer_L h.toSec14Std)
  have hwN : w ∈ Subgroup.normalizer (L : Set G) := hAuL hwAu
  have hALh : IsHyperplane A (A ⊓ L) := ⟨inf_le_left, by rw [h.card_eq, hAL9]⟩
  have hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L) :=
    le_antisymm (le_zpowers_sup_of_not_mem hALh hcA fun hc => hcL hc.2)
      (sup_le (Subgroup.zpowers_le.mpr hcA) inf_le_left)
  obtain ⟨y, hy⟩ : ∃ y : GL (Fin 3) (GaloisField 2 2), ∀ z : L ⧸ aschbacherSolvableCore 3 L,
      ((e (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨w, hwN⟩) z) :
        projImage (Sec4.slPi true 3 (2 ^ 2) (GaloisField 2 2))) :
          Matrix.ProjGenLinGroup (Fin 3) (GaloisField 2 2)) =
        Matrix.ProjGenLinGroup.mk y * (e z : Matrix.ProjGenLinGroup (Fin 3) (GaloisField 2 2)) *
          (Matrix.ProjGenLinGroup.mk y)⁻¹ := by
    set σ := Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨w, hwN⟩) with hσ
    have hw3' : (⟨w, hwN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, hw3, Subgroup.coe_one])
    have hσ3 : σ ^ 3 = 1 := by rw [hσ, ← map_pow, ← map_pow, hw3', map_one, map_one]
    obtain ⟨y, hy⟩ := Proof1613Type.exists_conj_of_pow_three hK4 (MulAut.congr e σ)
      (by rw [← map_pow, hσ3, map_one])
    refine ⟨y, fun z => ?_⟩
    have h1 := hy (e z)
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply] at h1
    exact h1
  have hrank : ∀ W : Subgroup G, W ≤ A ⊔ Subgroup.zpowers w →
      CFSG.Assembly.IsElemAbelian 3 W → Nat.card W = 81 → False := by
    intro W hWP hWab hW81
    have hWC : W ≤ Subgroup.centralizer ({c} : Set G) :=
      hWP.trans (sup_le h.A_le_centralizer (Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_singleton_iff.mpr hwc)))
    set X := pPrimeCoreOf 3 (Subgroup.centralizer ({c} : Set G)) with hX
    have hWX : W ≤ Subgroup.normalizer (X : Set G) := hWC.trans (le_normalizer_pPrimeCoreOf 3 _)
    have hX3 : Nat.Coprime 3 (Nat.card X) := coprime_card_pPrimeCoreOf 3 _
    have h2X : 2 ∣ Nat.card X := by
      rcases Nat.even_or_odd (Nat.card X) with he | ho
      · exact even_iff_two_dvd.mp he
      · exact absurd ho hev
    obtain ⟨T, hWT, hT1⟩ :=
      CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial
        3 2 Nat.prime_three Nat.prime_two W X (isPGroup_three_of_isElemAbelian hWab) hWX hX3 h2X
    have h4 := CFSG.RankThree.Theta.le_localRank_of_le_normalizer (q := 3) (k := 4)
      (by norm_num) hT1 (T.isPGroup'.map _) hWab.1 hWab.2 (by rw [hW81]; norm_num) hWT
    have h3 := h.toTheoremFourHyp.localRank_three
    omega
  obtain ⟨F, hFP, hcF, hdF, hFab, hF27, hsec, hTC⟩ := Proof1613Type.exists_typeC_core hc3 hc1 hLc
    h.isElemAbelian h.card_eq hAeq hAL9 hw3 hwc hwA hwNA hAN hwN hdA hwd hK hq (by norm_num) e hy
    hrank
  refine ⟨F, hFP.trans (sup_le le_sup_left (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right hwAu))),
    sup_le (Subgroup.zpowers_le.mpr hdF) (Subgroup.zpowers_le.mpr hcF), hFab, hF27, hsec, hTC⟩

end CFSG.RankThree.PartTwo.Sec16
