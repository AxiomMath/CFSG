module

public import CFSG.LocalAnalysis.StandardType.GGXInLUDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoAssemble
public import Certificates.Certificate1953
public import Certificates.Certificate1954
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.StandardType.GGK1ScFinal
import CFSG.LocalAnalysis.StandardType.GGCSRLabels
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineSmall
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6TwoThree
import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE7
import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine
import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
import CFSG.LocalAnalysis.StandardType.GGNbrBalance
import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts
import CFSG.LocalAnalysis.StandardType.GGTableBBstar
import CFSG.LocalAnalysis.StandardType.GGTableBTransport
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTwF4
import CFSG.RankThree.PartTwo.Census.Carrier.TitsCert

public section

namespace CFSG.StandardType.GGXInL

open CFSG.Assembly

private theorem dispAux_three_dvd_center {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) (hxL : x ∈ L) :
    3 ∣ Nat.card (Subgroup.center ↥L) := by
  have hSStar : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hcomp := hSStar.2.2.2.1
  have hx1 : x ≠ 1 := hSStar.2.2.1
  have hxB : x ∈ B := hSStar.2.1
  have hxBs : x ∈ Bs := hS.1.1.2.1.1 hxB
  have hxp : x ^ 3 = 1 := hS.1.1.2.1.2.1.2 x hxBs
  have hx3 : orderOf x = 3 := orderOf_eq_prime hxp hx1
  have hxcenterL : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hcomp.1 l.2) x (by simp)).symm
  have hx3L : orderOf (⟨x, hxL⟩ : ↥L) = 3 := (Subgroup.orderOf_coe _).symm.trans hx3
  rw [← hx3L]
  exact Subgroup.orderOf_dvd_natCard _ hxcenterL

private theorem dispAux_centerPrime_contra {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {R : Type} [Group R] (θ : ↥L ⧸ Subgroup.center ↥L ≃* R)
    (hperf : commutator ↥L = ⊤) (h3 : 3 ∣ Nat.card (Subgroup.center ↥L))
    (hCP : GGCenterPrime 3 R) : False := by
  let ψ : ↥L →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hψ : Function.Surjective ψ :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center ↥L))
  have hker : ψ.ker ≤ Subgroup.center ↥L := by
    intro z hz
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hz
    have h1 : QuotientGroup.mk' (Subgroup.center ↥L) z = 1 := θ.injective (by simpa using hz)
    exact (QuotientGroup.eq_one_iff z).mp h1
  exact hCP ↥L ψ hψ hker hperf h3

private theorem dispAux_range_contra {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) {R : Type} [Group R]
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) {I : Set (MulAut R)}
    (hact : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hperf : commutator ↥L = ⊤)
    (hbound : ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I →
      IsElemAbelian 3 X → Nat.card X < 3 ^ 3) : False := by
  have hSStar : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hcomp := hSStar.2.2.2.1
  have hx1 : x ≠ 1 := hSStar.2.2.1
  have hxB : x ∈ B := hSStar.2.1
  have hE : IsElemAbelian 3 B := hSStar.1.1
  have hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup 3 S →
      IsCyclic S := hSStar.2.2.2.2
  have hBN : B ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_largeEvenStandardType hS.1.1.1.2.2.2.2.2.2.2
  have hBsB : B ≤ Bs := hS.1.1.2.1.1
  have hactB : ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ :=
    fun b hb => hact b (hBsB hb)
  have hrange : IsElemAbelian 3 (ggBeta L θ hBN).range :=
    isElemAbelian_range (fun a b : ↥B => hE.1.is_comm.comm a b)
      (fun a => Subtype.ext (by simpa using hE.2 a a.2)) (ggBeta L θ hBN)
  have hI : ((ggBeta L θ hBN).range : Set (MulAut R)) ⊆ I := by
    rintro _ ⟨b, rfl⟩
    exact ggBeta_mem L θ hBN hactB b
  have hlt : Nat.card ↥(ggBeta L θ hBN).range < 3 ^ 3 := hbound _ hI hrange
  have hcard : Nat.card ↥(ggBeta L θ hBN).range * 3 = Nat.card ↥B :=
    card_range_ggBeta_mul_of Nat.prime_three hE hxB hx1 hcomp.1 hcyc hperf θ hBN
  have hBcard : Nat.card ↥B = 3 ^ LargeEvenTwoLocalRank 3 G := GGConfig.card_B_eq hS.1.1
  have hbeta : 3 ∈ LargeEvenBeta 4 G := hS.1.1.1.2.2.2.2.2.1
  have hrank : 4 ≤ LargeEvenTwoLocalRank 3 G := hbeta.2.2.2
  have hB81 : 81 ≤ Nat.card ↥B := by
    rw [hBcard]
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ LargeEvenTwoLocalRank 3 G := Nat.pow_le_pow_right (by norm_num) hrank
  omega

private theorem dispAux_kacGeneric {lab : LargeEvenLabel} (hlabn : lab.n = 1)
    (hmem : lab.tag = .A ∨ lab.tag = .twA ∨ lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D ∨
      lab.tag = .twD)
    (h6 : ¬ (lab.tag = .twA ∧ 3 ∣ lab.rank + 1)) : GGKacGenericCl lab 3 := by
  refine ⟨Nat.prime_three, by norm_num, ?_, ?_, ?_, ?_⟩
  · rw [hlabn]
    norm_num
  · simpa using hmem
  · rintro ⟨-, -, h⟩
    rw [hlabn] at h
    norm_num at h
  · rintro ⟨h, h3, -⟩
    exact h6 ⟨h, h3⟩

private theorem dispAux_classical {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {lab : LargeEvenLabel} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hxL : x ∈ L) (hperf : commutator ↥L = ⊤)
    (hraw : LargeEvenRawDatum lab (fun R _ I F => IsSimpleGroup R ∧
      (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* R, GGLabQTwo 3 lab ∧
        Bs ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ))
    (hAll : LargeEvenLabelAll lab fun R _ _ _ => GGCenterPrime 3 R) : False := by
  obtain ⟨R, hR, I, F, hQ⟩ := largeEvenRawDatum_exists (hAll _ hraw)
  letI := hR
  obtain ⟨hQ0, hCP⟩ := hQ
  obtain ⟨-, -, θ, -⟩ := hQ0
  exact (dispAux_centerPrime_contra θ hperf (dispAux_three_dvd_center hS hxL) hCP).elim

theorem lup8g_rank_contra {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {lab : LargeEvenLabel} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hperf : commutator ↥L = ⊤)
    (hraw : LargeEvenRawDatum lab (fun R _ I F => IsSimpleGroup R ∧
      (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* R, GGLabQTwo 3 lab ∧
        Bs ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ))
    (hAll : LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian 3 X → Nat.card X < 3 ^ 3) : False := by
  obtain ⟨R, hR, I, F, hQ⟩ := largeEvenRawDatum_exists (hAll _ hraw)
  letI := hR
  obtain ⟨hQ0, hbound⟩ := hQ
  obtain ⟨-, -, θ, hP⟩ := hQ0
  obtain ⟨-, -, hact⟩ := hP
  exact (dispAux_range_contra hS θ hact hperf hbound).elim

section DispAuxTits

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree


private theorem dispAux_titsThreeRank :
    TableBExcSmallRest.GGTitsThreeRankInput := by
  haveI : Fact (Nat.card (ZMod 2) = 2) := ⟨Nat.card_zmod 2⟩
  haveI : Finite (reeFixed ReeTag.F4 (ZMod 2) 0) := by
    haveI : Finite (ModGL ReeTag.F4.tag (ZMod 2)) := finite_modGL
    have : Finite (adjointGroup ReeTag.F4.tag (ZMod 2)) := Subtype.finite
    exact Subtype.finite
  intro E hE
  by_contra hle
  have hle' : 3 ^ 3 ≤ Nat.card ↥E := not_lt.mp hle
  have hEpg : IsPGroup 3 ↥E := isPGroup_of_isElemAbelian hE
  obtain ⟨k, hk⟩ := hEpg.exists_card_eq
  have hk3 : 3 ≤ k := by
    rw [hk] at hle'
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle'
  let e := CFSG.Sporadic.Schreier.Tits.titsDerivedIso (K := ZMod 2)
  let f : ↥CFSG.Sporadic.Schreier.Tits.titsD →* ↥(reeFixed ReeTag.F4 (ZMod 2) 0) :=
    (Subgroup.subtype (commutator (reeFixed ReeTag.F4 (ZMod 2) 0))).comp e.symm.toMonoidHom
  have hf : Function.Injective f :=
    (Subgroup.subtype_injective (commutator (reeFixed ReeTag.F4 (ZMod 2) 0))).comp
      e.symm.injective
  have hmap : IsElemAbelian 3 (E.map f) := CFSG.SectionRank.isElemAbelian_map hE f
  have hcard : Nat.card ↥(E.map f) = 3 ^ k := by
    rw [Subgroup.card_map_of_injective hf, hk]
  have hle2 : k ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(reeFixed ReeTag.F4 (ZMod 2) 0)) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top hmap hcard
  have hpr := CFSG.RankThree.PartTwo.Census.Carrier.Tits.pRank_three_reeFixed (K := ZMod 2)
    (by norm_num)
  omega

end DispAuxTits

theorem lup8g_dispatch_label
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hxL : x ∈ L) :
    p = 3 ∧
      (((∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K),
          Nonempty (lup8f_UnitaryMarking Bs L n K) ∧ 3 ∣ n ∧ 6 ≤ n) ∧
        GGInnerDiagOnLabel
          (fun p lab => GGLabQTwo p lab ∧ lab.tag = LargeEvenLieTag.twA ∧ 4 ≤ lab.rank) p Bs L) ∨
        GGInnerDiagOnLabel
          (fun p lab => GGLabQTwo p lab ∧ lab.tag = LargeEvenLieTag.twE6) p Bs L) := by
  classical
  have hp : p = 3 := ggQ2_pThree hS
  subst hp
  refine ⟨rfl, ?_⟩
  have hmark := hS.2.1
  dsimp only [GGInnerDiagOnLabel] at hmark
  obtain ⟨hperf, lab, hlab, hraw⟩ := hmark
  obtain ⟨-, -, -, -, -, -, -, hQ2, -, -⟩ := largeEvenRawDatum_exists hraw
  have hlabn : lab.n = 1 := by
    have h1 : 1 ≤ lab.n := hlab.1
    have h2 : lab.n < 2 := hQ2
    omega
  cases htag : lab.tag
  case A =>
    have hgen := dispAux_kacGeneric hlabn (by simp [htag])
      (by rintro ⟨h, -⟩; rw [htag] at h; cases h)
    exact (dispAux_classical hS hxL hperf hraw
      (largeEvenLabelAll_centerPrime_cl hlab hgen)).elim
  case twA =>
    have hlam : LargeEvenInLambda2 lab := hlab
    dsimp only [LargeEvenInLambda2] at hlam
    rw [htag] at hlam
    dsimp only at hlam
    by_cases h3 : 3 ∣ lab.rank + 1
    · have hlabt : lab = ⟨.twA, lab.rank, 1⟩ := by
        obtain ⟨t, r, m⟩ := lab
        simp_all
      have hraw0 := hraw
      rw [hlabt] at hraw
      dsimp only [LargeEvenRawDatum, LargeEvenRecipeUnitary] at hraw
      obtain ⟨K, hKf, hKfin, hKcard, hQ⟩ := hraw
      simp only [Nat.pow_one] at hQ
      obtain ⟨-, -, θ, hP⟩ := hQ
      obtain ⟨-, hBsN, hact⟩ := hP
      have hK4 : Nat.card K = 4 := by
        rw [hKcard]
        norm_num
      have hr2 : 2 ≤ lab.rank := hlam.2.1
      have hrne : lab.rank ≠ 2 := by
        intro h
        have h' := hlam.2.2 h
        omega
      have h3' := h3
      obtain ⟨k, hk⟩ := h3'
      have h6 : 6 ≤ lab.rank + 1 := by omega
      have hlabel : GGInnerDiagOnLabel
          (fun p lab => GGLabQTwo p lab ∧ lab.tag = LargeEvenLieTag.twA ∧ 4 ≤ lab.rank) 3 Bs L := by
        refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono (fun R _ I F hQ => ?_) hraw0⟩
        obtain ⟨hs, hna, θ', hlq, hrest⟩ := hQ
        exact ⟨hs, hna, θ', ⟨hlq, htag, by omega⟩, hrest⟩
      refine Or.inl ⟨⟨lab.rank + 1, K, hKf, hKfin, ⟨?_⟩, h3, h6⟩, hlabel⟩
      letI : Field K := hKf
      letI : Finite K := hKfin
      exact { theta := θ, card_K := hK4, normalizes := hBsN, action := hact }
    · have hgen := dispAux_kacGeneric hlabn (by simp [htag])
        (by rintro ⟨-, h⟩; exact h3 h)
      exact (dispAux_classical hS hxL hperf hraw
        (largeEvenLabelAll_centerPrime_cl hlab hgen)).elim
  case B =>
    have hgen := dispAux_kacGeneric hlabn (by simp [htag])
      (by rintro ⟨h, -⟩; rw [htag] at h; cases h)
    exact (dispAux_classical hS hxL hperf hraw
      (largeEvenLabelAll_centerPrime_cl hlab hgen)).elim
  case C =>
    have hgen := dispAux_kacGeneric hlabn (by simp [htag])
      (by rintro ⟨h, -⟩; rw [htag] at h; cases h)
    exact (dispAux_classical hS hxL hperf hraw
      (largeEvenLabelAll_centerPrime_cl hlab hgen)).elim
  case D =>
    have hgen := dispAux_kacGeneric hlabn (by simp [htag])
      (by rintro ⟨h, -⟩; rw [htag] at h; cases h)
    exact (dispAux_classical hS hxL hperf hraw
      (largeEvenLabelAll_centerPrime_cl hlab hgen)).elim
  case twD =>
    have hgen := dispAux_kacGeneric hlabn (by simp [htag])
      (by rintro ⟨h, -⟩; rw [htag] at h; cases h)
    exact (dispAux_classical hS hxL hperf hraw
      (largeEvenLabelAll_centerPrime_cl hlab hgen)).elim
  case E6 =>
    have hlabE : lab = ⟨.E6, lab.rank, 1⟩ := by
      obtain ⟨t, r, m⟩ := lab
      simp_all
    rw [hlabE] at hraw
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeChevalley] at hraw
    obtain ⟨K, hKf, hKfin, hKcard, -, -, θ, -, -, -⟩ := hraw
    letI : Field K := hKf
    letI : Finite K := hKfin
    have hK2 : Nat.card K = 2 := by simpa using hKcard
    exact (dispAux_centerPrime_contra θ hperf (dispAux_three_dvd_center hS hxL)
      (ggCenterPrime_recipe_E6_two hK2 Nat.prime_three)).elim
  case E7 =>
    have hlabE : lab = ⟨.E7, lab.rank, 1⟩ := by
      obtain ⟨t, r, m⟩ := lab
      simp_all
    rw [hlabE] at hraw
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeChevalley] at hraw
    obtain ⟨K, hKf, hKfin, hKcard, -, -, θ, -, -, -⟩ := hraw
    letI : Field K := hKf
    letI : Finite K := hKfin
    haveI : CharP K 2 := charP_two_of_card hKcard
    exact (dispAux_centerPrime_contra θ hperf (dispAux_three_dvd_center hS hxL)
      (ExcSplitL.ggCenterPrime_recipe_E7 (f := 1) le_rfl hKcard Nat.prime_three
        (by norm_num))).elim
  case E8 =>
    have hlabE : lab = ⟨.E8, lab.rank, 1⟩ := by
      obtain ⟨t, r, m⟩ := lab
      simp_all
    rw [hlabE] at hraw
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeChevalley] at hraw
    obtain ⟨K, hKf, hKfin, hKcard, -, -, θ, -, -, -⟩ := hraw
    letI : Field K := hKf
    letI : Finite K := hKfin
    haveI : CharP K 2 := charP_two_of_card hKcard
    exact (dispAux_centerPrime_contra θ hperf (dispAux_three_dvd_center hS hxL)
      (ExcSplitL.ggCenterPrime_recipe_E8 Nat.prime_three (by norm_num))).elim
  case F4 =>
    have hlabE : lab = ⟨.F4, lab.rank, 1⟩ := by
      obtain ⟨t, r, m⟩ := lab
      simp_all
    rw [hlabE] at hraw
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeChevalley] at hraw
    obtain ⟨K, hKf, hKfin, hKcard, -, -, θ, -, -, -⟩ := hraw
    letI : Field K := hKf
    letI : Finite K := hKfin
    haveI : CharP K 2 := charP_two_of_card hKcard
    exact (dispAux_centerPrime_contra θ hperf (dispAux_three_dvd_center hS hxL)
      (ExcSplitL.ggCenterPrime_recipe_F4 Nat.prime_three (by norm_num))).elim
  case twE6 =>
    refine Or.inr ⟨hperf, lab, hlab, ?_⟩
    refine largeEvenRawDatum_mono (fun R _ I F hQ => ?_) hraw
    obtain ⟨hs, hna, θ, hP⟩ := hQ
    obtain ⟨hlq, hBsN, hact⟩ := hP
    exact ⟨hs, hna, θ, ⟨hlq, htag⟩, hBsN, hact⟩
  case triD4 =>
    exact (lup8g_rank_contra hS hperf hraw
      (NbrInnerNine.largeEvenLabelAll_card_lt_triD4_of Nat.prime_three hlab htag
        (Or.inl rfl))).elim
  case G2 =>
    have h := hlab.2
    rw [htag] at h
    dsimp only at h
    omega
  case twB2 =>
    have h := hlab.2
    rw [htag] at h
    dsimp only at h
    omega
  case twF4 =>
    have h := hlab.2
    rw [htag] at h
    dsimp only at h
    omega
  case B2der =>
    exact (lup8g_rank_contra hS hperf hraw (ggCSR_B2der hlab htag)).elim
  case G2der =>
    exact (lup8g_rank_contra hS hperf hraw (ggCSR_G2der hlab htag)).elim
  case twF4der =>
    have hs : LargeEvenSplit 3 lab := Or.inr (Or.inr (Or.inr ⟨hlabn, rfl⟩))
    exact (lup8g_rank_contra hS hperf hraw
      (TableBExcSmallRest.largeEvenLabelAll_card_lt_twF4der dispAux_titsThreeRank
        Nat.prime_three hlab htag hs)).elim

theorem lup8g_dispatch
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hxL : x ∈ L) :
    p = 3 ∧
      ((∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K),
          Nonempty (lup8f_UnitaryMarking Bs L n K) ∧ 3 ∣ n ∧ 6 ≤ n) ∨
        GGInnerDiagOnLabel (fun _ lab => lab.tag = LargeEvenLieTag.twE6) p Bs L) := by
  obtain ⟨hp, h | h⟩ := lup8g_dispatch_label hS hxL
  · exact ⟨hp, Or.inl h.1⟩
  · exact ⟨hp, Or.inr (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.1.2, hP.2⟩) h)⟩

end CFSG.StandardType.GGXInL

end
