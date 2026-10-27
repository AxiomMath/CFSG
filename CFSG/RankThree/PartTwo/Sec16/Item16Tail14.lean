module

public import CFSG.RankThree.PartTwo.Sec16.Item16Tail14Defs
public import CFSG.RankThree.PartTwo.Sec15.HypS
import CFSG.RankThree.PartTwo.Sec16.Item16Tail14Tools
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13PGL
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
public import CFSG.RankThree.PartTwo.Sec16.Item16Tail13Defs

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof1614

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec16.Proof169
  CFSG.RankThree.PartTwo.Sec16.Proof1613 CFSG.GH74.GLS

section Certs


variable {G : Type} [Group G] [Finite G]

theorem false_of_pgl_pair (h1611 : Step1611) (h1613 : Step1613) (h133 : Item133)
    (hset : Item13SetupAt) (hInv : KS1613Inv) (hTr : KS1614Trans) (hDL : Step1614DL)
    {A L K : Subgroup G} {c e : G} (hc : Ctx169 G A c L) (he : Ctx169 G A e K)
    (hec : Subgroup.zpowers e ≠ Subgroup.zpowers c)
    (hPGLK : Sec8.IsZ3PGLThreePi ↥(lBarA e K A)) : False := by
  have hA := hc.isElemAbelian
  have hA27 : Nat.card A = 27 := hc.card_eq
  have hcA : c ∈ A := hc.mem_A
  have hc3 : Nat.card (Subgroup.zpowers c) = 3 := hc.card_zpowers
  have hcL : c ∉ L := hc.toSec15R.hypS.2.2 c hc.zpowers_mem_omegaA L hc.mem_lA
  obtain ⟨w, hwKW, ⟨k, hwk⟩, d', hd'A, hd'1, hwA, hw1⟩ := hTr G A e K he hPGLK
  have hwW : w ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp hwKW).2
  have hwc : w * c * w⁻¹ ≠ c := by
    intro hwc
    have hd'L := hDL G A c e L K hc he hec hPGLK w hwKW ⟨k, hwk⟩ d' hd'A hd'1 hwA hw1 hwc
    exact false_of_transvection_in_C h1611 h1613 hInv hc he hec hwKW hwk hd'A hwA hw1 hwc hd'L
  have hwH : w ∉ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    intro hwH
    exact hwc (conj_eq_of_mem_zpowers hwk (hA.2 c hcA)
      ((Subgroup.mem_normalizer_iff.mp hwH c).mp (Subgroup.mem_zpowers c)))
  have hPGLL : Sec8.IsZ3PGLThreePi ↥(lBarA c L A) := by
    rcases le_or_pgl h1611 h1613 h133 hc with hle | hP
    · exact absurd (hle hwW) hwH
    · exact hP
  obtain ⟨u, huLW, ⟨k', huk⟩, d, hdA, hd1, huA, hu1⟩ := hTr G A c L hc hPGLL
  obtain ⟨huL, huW⟩ := Subgroup.mem_inf.mp huLW
  have huc : u * c * u⁻¹ = c := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hc.le_centralizer huL), mul_inv_cancel_right]
  have hud : u * d * u⁻¹ = d := conj_center_eq hA huk hdA huA
  have hdL : d ∈ L := center_mem hA hc.le_normalizer huL hdA huA hu1
  have hdc : d ∉ Subgroup.zpowers c := by
    intro hdc'
    apply hcL
    have hzd := zpowers_eq_of_mem_of_ne_one hc3 hdc' hd1
    exact (Subgroup.zpowers_le.mpr hdL) (hzd ▸ Subgroup.mem_zpowers c)
  set B := Subgroup.zpowers c ⊔ Subgroup.zpowers d with hB
  have hdB : d ∈ B := (le_sup_right : Subgroup.zpowers d ≤ B) (Subgroup.mem_zpowers d)
  have hBC : B = A ⊓ Subgroup.centralizer ({u} : Set G) := by
    refine Subgroup.eq_of_le_of_card_ge
      (le_inf (sup_le (Subgroup.zpowers_le.mpr hcA) (Subgroup.zpowers_le.mpr hdA))
        (sup_le (Subgroup.zpowers_le.mpr (mem_centralizer_of_conj_eq huc))
          (Subgroup.zpowers_le.mpr (mem_centralizer_of_conj_eq hud)))) ?_
    have h1 := card_inf_centralizer_le_nine hA27 hu1
    have h2 : 9 ≤ Nat.card B :=
      nine_le_card_of_lt (sup_le (Subgroup.zpowers_le.mpr hcA) (Subgroup.zpowers_le.mpr hdA))
        hA27 hc3 (lt_of_le_of_ne le_sup_left fun heq => hdc (heq ▸ hdB))
    omega
  have huB : ∀ a ∈ A, u * a * u⁻¹ = a → a ∈ B := fun a ha hua => by
    rw [hBC]
    exact ⟨ha, mem_centralizer_of_conj_eq hua⟩
  have hΩB : ∀ F ∈ omegaA A, F ≤ B → F = Subgroup.zpowers c := by
    intro F hF hFB
    by_contra hFc
    obtain ⟨-, -, e', hFe', -⟩ := id hF
    subst hFe'
    obtain ⟨K', hK'⟩ := hset G hc.toPartTwoStanding hc.partTwoS_eq A hc.mem_partTwoF
      hc.not_mem_partTwoT e' hF
    have he' : Ctx169 G A e' K' := ctx169_of_point hc hF hK'
    have he'B : e' ∈ B := hFB (Subgroup.mem_zpowers e')
    have hue' : u * e' * u⁻¹ = e' := by
      have h1 : e' ∈ A ⊓ Subgroup.centralizer ({u} : Set G) := hBC ▸ he'B
      rw [← Subgroup.mem_centralizer_singleton_iff.mp h1.2, mul_inv_cancel_right]
    have hce' : Subgroup.zpowers c ≠ Subgroup.zpowers e' := fun h1 => hFc h1.symm
    have hdK' := hDL G A e' c K' L he' hc hce' hPGLL u huLW ⟨k', huk⟩ d hdA hd1 huA hu1 hue'
    exact false_of_transvection_in_C h1611 h1613 hInv he' hc hce' huLW huk hdA huA hu1 hue'
      hdK'
  have hΩ : ∀ x ∈ Subgroup.normalizer (A : Set G), x * c * x⁻¹ ∈ B →
      Subgroup.zpowers (x * c * x⁻¹) = Subgroup.zpowers c := by
    intro x hx hxB
    have hmem : (Subgroup.zpowers c).map (MulAut.conj x).toMonoidHom ∈ omegaA A :=
      (map_conj_mem_omegaA_iff hx).mpr hc.zpowers_mem_omegaA
    rw [MonoidHom.map_zpowers] at hmem
    exact hΩB _ hmem (Subgroup.zpowers_le.mpr hxB)
  exact false_of_two_transvections hA hA27 hcA hdA hd'A hc3 hdc huW hwW huc hud huA huB
    (conj_center_eq hA hwk hd'A hwA) hwA hwH hΩ

end Certs

end CFSG.RankThree.PartTwo.Sec16.Proof1614

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16.Proof169 CFSG.RankThree.PartTwo.Sec16.Proof1613
  CFSG.RankThree.PartTwo.Sec16.Proof1614 CFSG.GH74.GLS

section Item1614


variable {G : Type} [Group G] [Finite G]

theorem rank3II_16_14_of (h1611 : Step1611) (h1613 : Step1613) (h131 : Item131)
    (h133 : Item133) (hset : Item13SetupAt) (hInv : KS1613Inv)
    (hTr : KS1614Trans) (hDL : Step1614DL) {A L : Subgroup G} {c : G} (h : Ctx169 G A c L) :
    omegaA A = {Subgroup.zpowers c} := by
  ext F
  rw [Set.mem_singleton_iff]
  constructor
  · intro hF
    by_contra hFc
    obtain ⟨hFA, hF3, e, hFe, -⟩ := id hF
    subst hFe
    have heA : e ∈ A := hFA (Subgroup.mem_zpowers e)
    have he1 : e ≠ 1 := by
      rintro rfl
      rw [Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hF3
      norm_num at hF3
    obtain ⟨K, hK⟩ := hset G h.toPartTwoStanding h.partTwoS_eq A h.mem_partTwoF
      h.not_mem_partTwoT e hF
    have he : Ctx169 G A e K := ctx169_of_point h hF hK
    rcases le_or_pgl h1611 h1613 h133 he with hWe | hPGLK
    · rcases h1611 G A c L h with hPGLL | ⟨n, hn⟩
      · exact false_of_pgl_pair h1611 h1613 h133 hset hInv hTr hDL he h
          (fun h1 => hFc h1.symm) hPGLL
      · exact not_le_normalizer_of_l3 h131 kSPGLProper h hn heA he1 hFc hWe
    · exact false_of_pgl_pair h1611 h1613 h133 hset hInv hTr hDL h he hFc hPGLK
  · rintro rfl
    exact h.zpowers_mem_omegaA

theorem step1614_of (h1611 : Step1611) (h1613 : Step1613) (h131 : Item131) (h133 : Item133)
    (hset : Item13SetupAt) (hInv : KS1613Inv) (hTr : KS1614Trans) (hDL : Step1614DL) :
    Step1614 :=
  fun _ _ _ _ _ _ h => rank3II_16_14_of h1611 h1613 h131 h133 hset hInv hTr hDL h

end Item1614

end CFSG.RankThree.PartTwo.Sec16
