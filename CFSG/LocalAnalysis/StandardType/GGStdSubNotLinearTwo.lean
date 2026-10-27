module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LocalAnalysis.StandardType.MarkingClassical
import CFSG.LocalAnalysis.StandardType.GGTableBTransport
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreCl
import CFSG.LocalAnalysis.StandardType.GGNbrLangRestRank
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneRank
import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TypeDet
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggStdSubNotLinearTwoAux_label_arith {lab : LargeEvenLabel} {m : ℕ} (hm : 3 ≤ m)
    (hlab : LargeEvenInLambda2 lab)
    (h1 : markTag lab = .PSL) (h2 : markRank lab = 2) (h3 : markDeg lab = m) :
    (lab.tag = .A ∧ lab.rank = 1 ∧ lab.n = m) ∨
      (lab.tag = .twD ∧ lab.rank = 2 ∧ 2 * lab.n = m) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  cases t <;> simp_all [markTag, markRank, markDeg]
  case twD =>
    have hl2 : l = 2 := by
      by_contra h
      have := h2 h
      split_ifs at this <;> omega
    subst hl2
    simp only [if_true] at h3
    exact ⟨rfl, h3⟩
  case B2der => omega

private theorem ggStdSubNotLinearTwoAux_label
    {J : Type} [Group J] {E : Type} [Field E] [Finite E] {m : ℕ} (hm : 3 ≤ m)
    (hE : Nat.card E = 2 ^ m)
    (σ : J ⧸ Subgroup.center J ≃* LargeEvenProj (LargeEvenSLGroup (Fin 2) E))
    {lab_J : LargeEvenLabel} (hlab_J : LargeEvenInLambda2 lab_J)
    (hMarked : MarkedModel lab_J (J ⧸ Subgroup.center J)) :
    (lab_J.tag = .A ∧ lab_J.rank = 1 ∧ lab_J.n = m) ∨
      (lab_J.tag = .twD ∧ lab_J.rank = 2 ∧ 2 * lab_J.n = m) := by
  have hEchar : CharP E 2 := charP_two_of_card (m := m) hE
  haveI : CharP E 2 := hEchar
  have hEadm : CFSG.Open.StatedLieAdmissible .PSL 2 2 m := by
    refine ⟨Nat.prime_two, by omega, by norm_num, ?_, ?_⟩
    · intro h
      have h2 : 2 ^ m = 2 := congrArg Prod.snd h
      have h8 : 8 ≤ 2 ^ m := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      omega
    · intro h
      have h3 : 2 ^ m = 3 := congrArg Prod.snd h
      have h8 : 8 ≤ 2 ^ m := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      omega
  have hSCM : CFSG.Open.StatedClassicalModel
      (LargeEvenProj (LargeEvenSLGroup (Fin 2) E)) .PSL 2 2 m :=
    statedClassicalModel_linear 2 m hE hEadm
  have hPSL0 : CFSG.Blueprint.LieModel
      (LargeEvenProj (LargeEvenSLGroup (Fin 2) E)) .PSL 2 2 m :=
    Or.inl ⟨by decide, hSCM⟩
  have hPSLJ : CFSG.Blueprint.LieModel (J ⧸ Subgroup.center J) .PSL 2 2 m :=
    lieModel_of_mulEquiv' σ.symm hPSL0
  by_cases hc : markChar lab_J = 2
  · have hLie := NbrInnerMore.lieModel_of_markedModel_two hc hMarked
    obtain ⟨hT, hR, hD⟩ :=
      CFSG.SeitzReduction.RankOne.lieModel_PSL_two_two_unique_of_card_eq hPSLJ hLie rfl
    exact ggStdSubNotLinearTwoAux_label_arith hm hlab_J hT hR hD
  · exact absurd hMarked (NbrInnerMore.not_markedModel_of_char_ne_two hPSLJ
      (fun h => by obtain ⟨-, -, h2⟩ := h; omega)
      (fun h => by obtain ⟨-, h2, -⟩ := h; omega)
      (fun h => by obtain ⟨h1, -, -⟩ := h; exact absurd h1 (by decide)) hc)

private theorem ggStdSubNotLinearTwoAux_linearTwo_contra {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hJperf : commutator J = ⊤)
    {K0 : Type} [Field K0] [Finite K0] {m : ℕ} (hK0 : Nat.card K0 = 2 ^ m)
    (hs : IsSimpleGroup (LargeEvenProj (LargeEvenSLGroup (Fin 2) K0)))
    (hna : ∃ a b : LargeEvenProj (LargeEvenSLGroup (Fin 2) K0), a * b ≠ b * a)
    (θ_J : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSLGroup (Fin 2) K0))
    (hNJ : Bs ≤ Subgroup.normalizer (J : Set G))
    (hall : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K0)) Set.univ,
      LargeEvenInduces θ_J (fun l l' => (l' : G) = b⁻¹ * l * b) φ) : False := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hDJ : LargeEvenStdSub p B x L D J := hcfg.2.2
  have hDcard : Nat.card D = p ^ 2 := hDJ.1.2.2.1
  have hB : IsElemAbelian p B := hcfg.1.2.2.2.2.2.2.1.1.1
  have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G :=
    hcfg.1.2.2.2.2.2.2.1.1.2.1
  have h4 : 4 ≤ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.1.2.2.2
  have hB4 : p ^ 4 ≤ Nat.card B := by
    rw [hBcard]
    exact Nat.pow_le_pow_right hp.pos h4
  let hBJ : B ≤ Subgroup.normalizer (J : Set G) := hBBs.trans hNJ
  let α : ↥B →* MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 2) K0)) :=
    (ggLAut J θ_J).comp (Subgroup.inclusion hBJ)
  have hE_ab : IsElemAbelian p α.range :=
    isElemAbelian_range_of_isElemAbelian hB α
  have hE_I : (α.range : Set (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 2) K0)))) ⊆
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K0)) Set.univ := by
    rintro φ ⟨b, rfl⟩
    exact ggLAut_mem_of_induces J θ_J hBJ (fun b hb => hall b (hBBs hb)) b.2
  have hker_le : α.ker ≤ D.subgroupOf B := by
    intro b hb
    rw [Subgroup.mem_subgroupOf]
    rw [MonoidHom.mem_ker] at hb
    rw [hDJ.1.2.2.2.2.2.2]
    exact ⟨b.2, mem_centralizer_of_ggLAut_eq_one J θ_J hJperf (g := ⟨b, hBJ b.2⟩) hb⟩
  have hker_card : Nat.card α.ker ≤ p ^ 2 := by
    rw [← hDcard]
    calc Nat.card α.ker ≤ Nat.card (D.subgroupOf B) := Subgroup.card_le_of_le hker_le
      _ = Nat.card D := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDJ.1.1).toEquiv
  have hE9 : p ^ 2 ≤ Nat.card α.range := by
    have hcard := Subgroup.card_ker_mul_card_range α
    have h : p ^ 2 * p ^ 2 ≤ p ^ 2 * Nat.card α.range := by
      calc p ^ 2 * p ^ 2 = p ^ 4 := by ring
        _ ≤ Nat.card ↥B := hB4
        _ = Nat.card α.ker * Nat.card α.range := hcard.symm
        _ ≤ p ^ 2 * Nat.card α.range := Nat.mul_le_mul_right _ hker_card
    exact Nat.le_of_mul_le_mul_left h (pow_pos hp.pos 2)
  have hK0char : CharP K0 2 := charP_two_of_card (m := m) hK0
  haveI : CharP K0 2 := hK0char
  have hEp : Nat.card α.range ≤ p :=
    NbrLangRest.card_le_of_forall_mem_conjImage_two (p := p) hp hp2 hs hna α.range hE_ab hE_I
  have hp2lt : p < p ^ 2 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  exact absurd (le_trans hE9 hEp) (not_le.mpr hp2lt)

theorem ggConfig_false_of_innerDiagOn_psl_two {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hIDJ : GGInnerDiagOn Bs J) {E : Type} [Field E] [Finite E] {m : ℕ} (hm : 3 ≤ m)
    (hE : Nat.card E = 2 ^ m)
    (σ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSLGroup (Fin 2) E)) :
    False := by
  obtain ⟨hJperf, lab_J, hlab_J, hraw_J⟩ := hIDJ
  have hraw_marked := largeEvenRawDatum_markedModel hlab_J
    (Q := fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : (↥J ⧸ Subgroup.center ↥J) ≃* R,
        Bs ≤ Subgroup.normalizer (J : Set G) ∧
          ∀ b ∈ Bs, ∃ φ ∈ I,
            LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (fun R _ I F hQ => hQ.2.1) hraw_J
  obtain ⟨R', _, I', F', hQ', hMM'⟩ := largeEvenRawDatum_exists hraw_marked
  obtain ⟨hs', hna', θ', hNJ', hhall'⟩ := hQ'
  have hMarkedCenter : MarkedModel lab_J (↥J ⧸ Subgroup.center ↥J) :=
    MarkedModel.of_mulEquiv θ'.symm hMM'
  have hlabOr := ggStdSubNotLinearTwoAux_label (J := ↥J) hm hE σ hlab_J hMarkedCenter
  rcases hlabOr with ⟨ht, hr, hn⟩ | ⟨ht, hr, hn⟩
  ·
    obtain ⟨t, l, n⟩ := lab_J
    dsimp only at ht hr hn
    subst ht; subst hr; subst hn
    dsimp only [LargeEvenRawDatum] at hraw_J
    obtain ⟨K0, hK0field, hK0fin, hK0card, hQK⟩ := hraw_J
    obtain ⟨hs, hna, θ_J, hNJ, hall⟩ := hQK
    letI : Field K0 := hK0field
    letI : Finite K0 := hK0fin
    exact ggStdSubNotLinearTwoAux_linearTwo_contra hcfg hJperf hK0card hs hna θ_J hNJ hall
  ·
    obtain ⟨t, l, n⟩ := lab_J
    dsimp only at ht hr hn
    subst ht; subst hr
    simp only [LargeEvenRawDatum, ↓reduceIte] at hraw_J
    obtain ⟨K0, hK0field, hK0fin, hK0card, hQK⟩ := hraw_J
    obtain ⟨hs, hna, θ_J, hNJ, hall⟩ := hQK
    letI : Field K0 := hK0field
    letI : Finite K0 := hK0fin
    dsimp only at hK0card
    have hK0card' : Nat.card K0 = 2 ^ m := by
      rw [hK0card, ← pow_mul, show n * 2 = m by omega]
    exact ggStdSubNotLinearTwoAux_linearTwo_contra hcfg hJperf hK0card' hs hna θ_J hNJ hall

end CFSG.StandardType
