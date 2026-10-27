module

public import CFSG.LocalAnalysis.UniquenessCase.UC1S4Defs462
public import CFSG.GroupTheory.ABGLocalTools.PStabilityChief
public import CFSG.GroupTheory.ThreeTranspositions.Basic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.R920L2OddIMQuot
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920IMOddRep
import CFSG.LocalAnalysis.UniquenessCase.UC1K46InspEven
import CFSG.LocalAnalysis.UniquenessCase.UC6K42j
import CFSG.LocalAnalysis.UniquenessCase.UC1K462Basic
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93h
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93i
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6U4OverAux1
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoFacts
import CFSG.GH74.KGroups.PSL2
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KOdd2Fin
import CFSG.RankThree.PartOne.SRC.ModelL3
import CFSG.Adapters.LieModelSimple
import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ABGLocalTools (IsChiefFactorUnder)
open CFSG.GroupTheory.ThreeTranspositions (HasE9)
open CFSG.LocalAnalysis.UniquenessCase.UCK (fixV)
open CFSG.Theory.Representation (kerRepresentation kerRepresentation_faithful)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal.Odd2
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

private theorem card_map_quotient_of_inf_eq_bot {Q : Type} [Group Q] (N : Subgroup Q)
    [N.Normal] (A : Subgroup Q) (h : A ⊓ N = ⊥) :
    Nat.card (A.map (QuotientGroup.mk' N)) = Nat.card A := by
  let f : ↥A →* Q ⧸ N := (QuotientGroup.mk' N).comp A.subtype
  have hrange : f.range = A.map (QuotientGroup.mk' N) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact Subgroup.mem_map_of_mem _ a.2
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have hker : f.ker = ⊥ := by
    ext x
    constructor
    · intro hx
      have hxN : (x : Q) ∈ N := by
        have hx1 : f x = 1 := hx
        exact (QuotientGroup.eq_one_iff (x : Q)).mp hx1
      have hxA : (x : Q) ∈ A ⊓ N := ⟨x.2, hxN⟩
      rw [h] at hxA
      exact Subtype.ext (Subgroup.mem_bot.mp hxA)
    · intro hx
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      exact map_one f
  have hcard := Subgroup.card_ker_mul_card_range f
  rw [hker, hrange, Subgroup.card_bot, one_mul] at hcard
  exact hcard

private theorem exists_surjective_quotient_bar2 {L : Subgroup G} {n : ℕ}
    (hL2 : IsL2 (Bar2 L) n) (N : Subgroup ↥L) [N.Normal] (hN3 : ¬ 3 ∣ Nat.card N) :
    ∃ π : (↥L ⧸ N) →* Bar2 L, Function.Surjective π := by
  classical
  let P : Subgroup ↥L := CFSG.pCore 2 ↥L
  haveI : P.Normal := CFSG.pCore_normal (p := 2) (G := ↥L)
  have hScm : CFSG.Open.StatedClassicalModel (Bar2 L) .PSL 2 2 n :=
    (CFSG.Blueprint.LieModel.classical_iff (t := .PSL) (by decide)).mp hL2
  have hSthree : 3 ∣ Nat.card (Bar2 L) :=
    CFSG.Open.StatedAPI.three_dvd_card_of_statedClassicalModel_psl_two_two hScm
  haveI hSsimple : IsSimpleGroup (Bar2 L) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
  have hNbarBot : N ≤ P := by
    let Nbar : Subgroup (Bar2 L) := N.map (QuotientGroup.mk' P)
    haveI : Nbar.Normal :=
      Subgroup.Normal.map (inferInstance : N.Normal) (QuotientGroup.mk' P)
        (QuotientGroup.mk'_surjective P)
    have hNbarThree : ¬ 3 ∣ Nat.card Nbar := fun h3 =>
      hN3 (h3.trans (Subgroup.card_map_dvd (H := N) (f := QuotientGroup.mk' P)))
    have hNbar : Nbar = ⊥ ∨ Nbar = ⊤ :=
      IsSimpleGroup.eq_bot_or_eq_top_of_normal Nbar
    rcases hNbar with hbot | htop
    · rw [← QuotientGroup.ker_mk' (N := P)]
      exact (Subgroup.map_eq_bot_iff (H := N) (f := QuotientGroup.mk' P)).mp hbot
    · exact absurd (by rw [htop, Subgroup.card_top]; exact hSthree) hNbarThree
  refine ⟨QuotientGroup.map N P (MonoidHom.id ↥L) (by simpa using hNbarBot), ?_⟩
  refine QuotientGroup.map_surjective_of_surjective (N := N) (M := P)
    (f := MonoidHom.id ↥L) ?_ (by simpa using hNbarBot)
  intro y
  exact QuotientGroup.mk'_surjective P y

private theorem sec8_of_sl2_odd {X F : Type} [Group X] [Field F] [Finite F]
    (hFodd : Odd (Nat.card F)) (e : X ≃* Matrix.SpecialLinearGroup (Fin 2) F) : Sec8 X := by
  have hFodd' : Nat.card F % 2 = 1 := Nat.odd_iff.mp hFodd
  have hSecSL2 : Sec8 (Matrix.SpecialLinearGroup (Fin 2) F) := by
    let φ : Matrix.SpecialLinearGroup (Fin 2) F →*
        Matrix.GeneralLinearGroup (Fin 3) F :=
      Matrix.SpecialLinearGroup.toGL.comp
        (CFSG.RankThree.PartOne.SRC.blockHom (F := F))
    have hφ : Function.Injective φ :=
      Matrix.SpecialLinearGroup.toGL_injective.comp
        (CFSG.RankThree.PartOne.SRC.blockHom_injective (F := F))
    let H : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F) := φ.range
    have hdet : ∀ g ∈ H,
        ((g : Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F).det = 1 := by
      rintro g ⟨A, rfl⟩
      change (CFSG.RankThree.PartOne.SRC.blockMat A).det = 1
      exact CFSG.RankThree.PartOne.SRC.det_blockMat A
    have hSecH : Sec8 ↥H :=
      CFSG.HardMathSupport.Solomon.UniquenessMaximal.Odd2.sec8_of_det_one hFodd' H hdet
    exact Sec8.of_injective (MonoidHom.ofInjective hφ).toMonoidHom
      (MonoidHom.ofInjective hφ).injective hSecH
  exact Sec8.of_injective e.toMonoidHom e.injective hSecSL2

private theorem false_of_sec8_of_isL2 {X : Type} [Group X] [Finite X] {n : ℕ}
    (hn4 : 4 ≤ n) (hL2 : IsL2 X n) (hSec : Sec8 X) : False := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hGF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  obtain ⟨e⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel
    (F := GaloisField 2 n) 2 n (by omega) hGF hL2
  let U : Sylow 2 (CFSG.AGLEmbedding.PSL2GF 2 n) := default
  have hU := CFSG.AGLEmbedding.psl2GF_sylow 2 n hn1 U
  let E : Subgroup X := U.map e.symm.toMonoidHom
  have hEcard : Nat.card E = 2 ^ n := by
    dsimp only [E]
    rw [Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective, hU.2]
  have hEtwo : ∀ x ∈ E, x * x = 1 := by
    intro x hx
    dsimp only [E] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hy2 : y ^ 2 = 1 := hU.1.2 y hy
    have hconj := congrArg (fun z => e.symm z) hy2
    simpa [pow_two] using hconj
  have hle8 : Nat.card E ≤ 8 :=
    hSec E E E.subtype (MonoidHom.id E) E.subtype_injective
      (fun x => ⟨x, rfl⟩) (fun x => by
        show (x : ↥E) * x = 1
        exact Subtype.ext (by simpa using hEtwo x x.2))
  have hge16 : 16 ≤ Nat.card E := by
    rw [hEcard]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn4
  omega

private theorem false_of_isExt_q8d8_a5 {X : Type} [Group X] [Finite X] {s : ℕ}
    (hs : s.Prime) (hs7 : 7 ≤ s) (hdvd : s ∣ Nat.card X)
    (hExt : CFSG.Quasithin.IsExt X
      (fun V _ => CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8 (⊤ : Subgroup V))
      (fun Y _ => CFSG.Quasithin.IsAlt 5 Y)) : False := by
  obtain ⟨V, hVnormal, hQ8, hA5⟩ := hExt
  haveI : V.Normal := hVnormal
  have hVcard : Nat.card ↥V = 32 := by
    have h := (CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8.facts hQ8).1
    simpa using h
  obtain ⟨eA5⟩ := hA5
  have hA5card : Nat.card (X ⧸ V) = 60 := by
    rw [Nat.card_congr eA5.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hcard : Nat.card X = 1920 := by
    have h := Subgroup.card_mul_index (H := V)
    rw [hVcard, Subgroup.index_eq_card, hA5card] at h
    norm_num at h
    exact h.symm
  have h1920 : s ∣ 1920 := hcard ▸ hdvd
  have hfac : 1920 = 2 ^ 7 * 3 * 5 := by norm_num
  rw [hfac] at h1920
  have hnot2 : ¬ s ∣ 2 ^ 7 := by
    intro h
    have h2 : s ∣ 2 := hs.dvd_of_dvd_pow h
    have hle : s ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    omega
  rcases hs.dvd_mul.mp h1920 with h23 | h5
  · rcases hs.dvd_mul.mp h23 with h2 | h3
    · exact hnot2 h2
    · rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h1 | h3'
      · rw [h1] at hs
        exact absurd hs (by norm_num)
      · omega
  · rcases (Nat.dvd_prime Nat.prime_five).mp h5 with h1 | h5'
    · rw [h1] at hs
      exact absurd hs (by norm_num)
    · omega

private theorem false_of_isL2_K42 {Q : Type} [Group Q] [Finite Q] {m s r : ℕ}
    (hmL2 : IsL2 Q m) (hs : s.Prime) (hs7 : 7 ≤ s) (hsdvd : s ∣ 2 ^ m - 1)
    (hr : r.Prime) (hr2 : r ≠ 2) (hK : CFSG.Open.IsKGroup Q)
    {V : Type} [AddCommGroup V] [Module (ZMod r) V] [Finite V] [Nontrivial V]
    (ρ : Representation (ZMod r) Q V) (hρ : Function.Injective ρ)
    (D : Subgroup Q) (hD : Nat.card D = s) (hfixD : fixV ρ D = ⊥) : False := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hs2 : s ≠ 2 := by omega
  have hsr : s ≠ r := by
    intro h
    have hDp : IsPGroup r D := IsPGroup.of_card (n := 1) (by rw [hD, h]; simp)
    exact CFSG.LocalAnalysis.UniquenessCase.UCK.UC46.fixV_ne_bot_of_pGroup
      (ρ := ρ) hDp hfixD
  have hU :=
    (CFSG.LocalAnalysis.UniquenessCase.UCK.insp2L2_holds Q m hmL2 s hs hs2 hsdvd).2
  obtain ⟨R, hR⟩ := hU D hD
  obtain ⟨hR2, hRab, hRne, hDR, hcomm⟩ := hR
  have h42 := CFSG.LocalAnalysis.UniquenessCase.UC6.k42_uc6 r hr Q hK V ρ hρ 2 s
    Nat.prime_two hs (Ne.symm hr2) hsr (Ne.symm hs2) D hD hfixD R hR2 hRne hDR hcomm
  exact h42.1 hRab

private theorem chief_quotient_facts {L A U W : Subgroup G} {r s : ℕ}
    (hAL : A ≤ L) (hs : s.Prime) (hAs : Nat.card A = s)
    (hfixA : ∀ u ∈ U, (∀ a ∈ A, a * u * a⁻¹ * u⁻¹ ∈ W) → u ∈ W)
    {V : Type} [AddCommGroup V] [Module (ZMod r) V] [Finite V] [Nontrivial V]
    (ρ : Representation (ZMod r) ↥L V)
    (hfixV : ∀ B : Subgroup ↥L,
      (∀ u ∈ U, (∀ b ∈ B, (b : G) * u * (b : G)⁻¹ * u⁻¹ ∈ W) → u ∈ W) → fixV ρ B = ⊥) :
    ∃ Ā : Subgroup (↥L ⧸ ρ.ker), Nat.card Ā = s ∧
      fixV (kerRepresentation ρ) Ā = ⊥ ∧ s ∣ Nat.card (↥L ⧸ ρ.ker) := by
  classical
  let A' : Subgroup ↥L := A.subgroupOf L
  have hA'card : Nat.card A' = s := by
    rw [← hAs]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv
  have hfixA' : fixV ρ A' = ⊥ :=
    hfixV A' fun u hu hc =>
      hfixA u hu fun a ha => hc ⟨a, hAL ha⟩ (Subgroup.mem_subgroupOf.mpr ha)
  have hbot_top : (⊥ : Submodule (ZMod r) V) ≠ ⊤ := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hvbot : v ∈ (⊥ : Submodule (ZMod r) V) := h.symm ▸ Submodule.mem_top
    exact hv (by simpa using hvbot)
  have hker_bot : A' ⊓ ρ.ker = ⊥ := by
    by_contra hne
    have hdvd : Nat.card ↥(A' ⊓ ρ.ker) ∣ s := by
      rw [← hA'card]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hcards : Nat.card ↥(A' ⊓ ρ.ker) = s := by
      rcases (Nat.dvd_prime hs).mp hdvd with h | h
      · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hne
      · exact h
    have hEq : A' ⊓ ρ.ker = A' :=
      Subgroup.eq_of_le_of_card_ge inf_le_left
        (by rw [hA'card]; exact le_of_eq hcards.symm)
    have hle : A' ≤ ρ.ker := hEq ▸ inf_le_right
    have htop : fixV ρ A' = ⊤ := by
      ext v
      simp only [Submodule.mem_top, iff_true]
      intro a ha
      rw [hle ha, Module.End.one_apply]
    exact hbot_top (by rw [← hfixA', htop])
  let Ā : Subgroup (↥L ⧸ ρ.ker) := A'.map (QuotientGroup.mk' ρ.ker)
  have hĀcard : Nat.card Ā = s := by
    rw [card_map_quotient_of_inf_eq_bot ρ.ker A' hker_bot, hA'card]
  have hfixĀ : fixV (kerRepresentation ρ) Ā = ⊥ := by
    rw [eq_bot_iff, ← hfixA']
    intro v hv
    have hv' : ∀ b ∈ Ā, kerRepresentation ρ b v = v := hv
    show ∀ a ∈ A', ρ a v = v
    intro a ha
    exact hv' (QuotientGroup.mk' ρ.ker a) (Subgroup.mem_map_of_mem _ ha)
  have hs_dvd : s ∣ Nat.card (↥L ⧸ ρ.ker) := by
    rw [← hĀcard]
    exact Subgroup.card_subgroup_dvd_card Ā
  exact ⟨Ā, hĀcard, hfixĀ, hs_dvd⟩

private theorem false_of_isL2_odd_quotient {X S : Type} [Group X] [Finite X] [Group S]
    [Finite S] {m n r s : ℕ} (π : X →* S) (hπ : Function.Surjective π)
    (hmL2 : IsL2 X m) (hS2 : IsL2 S n) (hs : s.Prime) (hs7 : 7 ≤ s)
    (hsd : s ∣ 2 ^ n - 1) (hr : r.Prime) (hr2 : r ≠ 2) (hK : CFSG.Open.IsKGroup X)
    {V : Type} [AddCommGroup V] [Module (ZMod r) V] [Finite V] [Nontrivial V]
    (ρ : Representation (ZMod r) X V) (hρ : Function.Injective ρ)
    (D : Subgroup X) (hD : Nat.card D = s) (hfixD : fixV ρ D = ⊥) : False := by
  haveI : IsSimpleGroup X :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hmL2
  have hker := IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker
  rcases hker with hbot | htop
  · have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hbot
    let eπ : X ≃* S := MulEquiv.ofBijective π ⟨hinj, hπ⟩
    have hmEq : m = n :=
      s16c6_isL2_param_unique (CFSG.Blueprint.LieModel.of_mulEquiv eπ hmL2) hS2
    have hsd' : s ∣ 2 ^ m - 1 := by rw [hmEq]; exact hsd
    exact false_of_isL2_K42 hmL2 hs hs7 hsd' hr hr2 hK ρ hρ D hD hfixD
  · have htriv : ∀ x : X, π x = 1 := by
      intro x
      have hx : x ∈ π.ker := by rw [htop]; exact Subgroup.mem_top x
      simpa using hx
    have hrange : π.range = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨x, rfl⟩
      rw [htriv x]
      exact Subgroup.mem_bot.mpr rfl
    have htoprange : π.range = ⊤ := MonoidHom.range_eq_top.mpr hπ
    have hcard1 : Nat.card S = 1 := by
      have h : Nat.card ↥(π.range) = 1 := by rw [hrange, Subgroup.card_bot]
      rwa [htoprange, Subgroup.card_top] at h
    have hScm : CFSG.Open.StatedClassicalModel S .PSL 2 2 n :=
      (CFSG.Blueprint.LieModel.classical_iff (t := .PSL) (by decide)).mp hS2
    have hSthree : 3 ∣ Nat.card S :=
      CFSG.Open.StatedAPI.three_dvd_card_of_statedClassicalModel_psl_two_two hScm
    rw [hcard1] at hSthree
    norm_num at hSthree

theorem false_of_odd_chief_factor_L2 (hK462 : UCK.K462) {L Z A U W : Subgroup G} {r s n : ℕ}
    (hKK : CFSG.Open.IsKGroup ↥L) (hE9 : ¬ HasE9 ↥L) (hLperf : ⁅L, L⁆ = L)
    (hL2 : IsL2 (Bar2 L) n) (hn4 : 4 ≤ n) (hZL : Z ≤ L) (hZ3 : Nat.card Z = 3)
    (hLgen : ∀ B : Subgroup G, B ≤ L → L ≤ normalizer (B : Set G) → Z ≤ B → B = L)
    (hr : r.Prime) (hr2 : r ≠ 2) (hUW : IsChiefFactorUnder r L U W)
    (hfix : ∀ u ∈ U, (∀ x ∈ Z, x * u * x⁻¹ * u⁻¹ ∈ W) → u ∈ W)
    (hAL : A ≤ L) (hs : s.Prime) (hAs : Nat.card A = s) (hs7 : 7 ≤ s) (hsd : s ∣ 2 ^ n - 1)
    (hfixA : ∀ u ∈ U, (∀ a ∈ A, a * u * a⁻¹ * u⁻¹ ∈ W) → u ∈ W) : False := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨V, _, _, _, _, ρ, hirr, hfixV⟩ := exists_rep_of_chief_factor hUW
  have hperf : commutator ↥L = ⊤ := by
    haveI : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLperf
    exact Group.IsPerfect.commutator_eq_top
  have hD3 : Nat.card (Z.subgroupOf L) = 3 := by
    rw [← hZ3]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZL).toEquiv
  have hfixZ : fixV ρ (Z.subgroupOf L) = ⊥ :=
    hfixV (Z.subgroupOf L) fun u hu hc =>
      hfix u hu fun x hx => hc ⟨x, hZL hx⟩ (Subgroup.mem_subgroupOf.mpr hx)
  have hcases := quot_ker_K462 hK462 hr2 hKK hE9 hperf hD3
    (F09.normalClosure_subgroupOf_eq_top hZL hLgen) ρ hirr hfixZ
  have hN3 : ¬ 3 ∣ Nat.card ρ.ker :=
    F09.not_three_dvd_card_ker ρ hE9 hD3 hfixZ
  obtain ⟨π, hπ⟩ := exists_surjective_quotient_bar2 hL2 ρ.ker hN3
  obtain ⟨Ā, hĀcard, hfixĀ, hs_dvd⟩ :=
    chief_quotient_facts hAL hs hAs hfixA ρ hfixV
  haveI : IsSimpleGroup (Bar2 L) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
  rcases hcases with hSL2 | hL2odd | hExt
  · obtain ⟨F, hFfield, hFfinite, hFodd, ⟨eF⟩⟩ := hSL2
    letI : Field F := hFfield
    letI : Finite F := hFfinite
    have hSecBar : Sec8 (Bar2 L) :=
      Sec8.of_surjective π hπ (sec8_of_sl2_odd hFodd eF)
    exact false_of_sec8_of_isL2 hn4 hL2 hSecBar
  · obtain ⟨m, -, hmL2⟩ := hL2odd
    exact false_of_isL2_odd_quotient π hπ hmL2 hL2 hs hs7 hsd hr hr2
      (hKK.quotient ρ.ker) (kerRepresentation ρ) (kerRepresentation_faithful ρ)
      Ā hĀcard hfixĀ
  · exact false_of_isExt_q8d8_a5 hs hs7 hs_dvd hExt

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
