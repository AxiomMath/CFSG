module

public import CFSG.RankThree.PartTwo.Sec15.Item155w3ProofHJ
public import CFSG.RankThree.PartTwo.Sec15.Item154PiProofPoint
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155KFacts
import CFSG.RankThree.PartTwo.Sec14.Concl142HJPoint
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.RankThree.PartTwo.KFacts.KS14PGL
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.RankThree.PartTwo.Sec15.Liebeck155Orders

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.Open (StatedClassicalModel)

@[expose] noncomputable def XInPiNHJR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ¬ AllPointsHJ A → ∀ X ∈ scriptY4 A (lB A), ∀ J ∈ scriptY0 A (lB A), X < J →
      (∃ n : ℕ, 1 ≤ n ∧ Sec4.IsoLThreePi (↥J ⧸ CFSG.pCore 2 ↥J) 2 n) →
      (∃ k : ℕ, 1 ≤ k ∧ Sec4.IsoLThreePi (↥X ⧸ CFSG.pCore 2 ↥X) 2 k) ∨
        Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* alternatingGroup (Fin 5))

theorem step155UpPiNHJR_of_xInPi (h : XInPiNHJR) : Step155UpPiNHJR := by
  intro G _ _ A c L hR hS hNHJ Y hY hpi ha5 hcl M hM J hJM hJ0 hXJ hJpi K hK hJK
  exfalso
  have hX4 : oPrimeResidualOf 3 Y ∈ scriptY4 A (lB A) := hY.2.1
  rcases h G A c L hR hNHJ _ hX4 J hJ0 hXJ hJpi with hk | he
  · exact hpi hk
  · obtain ⟨e⟩ := he
    exact ha5.false e

section Sections

variable {G : Type} [Group G] [Finite G]

theorem inf_pCoreOf_le_pCore {X J : Subgroup G} (hXJ : X ≤ J) :
    (X ⊓ CFSG.Open.pCoreOf 2 J).subgroupOf X ≤ CFSG.pCore 2 ↥X := by
  refine le_pCore155 ?_ ?_
  · have hle : X ⊓ CFSG.Open.pCoreOf 2 J ≤ X := inf_le_left
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
    exact (le_inf Subgroup.le_normalizer
      (hXJ.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  · have hp := (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) J).to_le
      (inf_le_right : X ⊓ CFSG.Open.pCoreOf 2 J ≤ CFSG.Open.pCoreOf 2 J)
    exact hp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : X ⊓ CFSG.Open.pCoreOf 2 J ≤ X)).symm

omit [Finite G] in
theorem exists_section_of_le {X J : Subgroup G} (hXJ : X ≤ J) (Ker : Subgroup ↥X) [Ker.Normal]
    (hKer : (X ⊓ CFSG.Open.pCoreOf 2 J).subgroupOf X ≤ Ker) :
    ∃ (H : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)) (N : Subgroup H) (_ : N.Normal),
      Nonempty (↥X ⧸ Ker ≃* ↥H ⧸ N) := by
  set φ : ↥X →* ↥J ⧸ CFSG.pCore 2 ↥J :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥J)).comp (Subgroup.inclusion hXJ) with hφ
  set ψ : ↥X →* ↥φ.range := φ.rangeRestrict with hψ
  have hsurj : Function.Surjective ψ := φ.rangeRestrict_surjective
  have hker : ψ.ker ≤ Ker := by
    intro x hx
    have h1 : φ x = 1 := by
      have := (MonoidHom.mem_ker.mp hx)
      exact congrArg Subtype.val this
    have h2 : Subgroup.inclusion hXJ x ∈ CFSG.pCore 2 ↥J := by
      rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    have h3 : ((Subgroup.inclusion hXJ x : ↥J) : G) ∈ CFSG.Open.pCoreOf 2 J :=
      (CFSG.mem_openPCoreOf_iff _).mpr h2
    apply hKer
    rw [Subgroup.mem_subgroupOf]
    exact ⟨x.2, h3⟩
  haveI hNorm : (Ker.map ψ).Normal := Subgroup.Normal.map inferInstance ψ hsurj
  refine ⟨φ.range, Ker.map ψ, hNorm, ⟨?_⟩⟩
  set χ : ↥X →* ↥φ.range ⧸ Ker.map ψ := (QuotientGroup.mk' (Ker.map ψ)).comp ψ with hχ
  have hχs : Function.Surjective χ :=
    (QuotientGroup.mk'_surjective (Ker.map ψ)).comp hsurj
  have hχk : χ.ker = Ker := by
    ext x
    rw [MonoidHom.mem_ker, hχ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      have : x ∈ Subgroup.comap ψ (Ker.map ψ) := hx
      rw [Subgroup.comap_map_eq] at this
      exact (sup_le le_rfl hker) this
    · intro hx
      exact Subgroup.mem_map_of_mem _ hx
  exact (QuotientGroup.quotientMulEquivOfEq hχk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective χ hχs)

theorem perfect_section_data {A X : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hX : X ∈ scriptY4 A LB) :
    Group.IsPerfect (↥X ⧸ CFSG.pCore 2 ↥X) ∧ (∃ a b : ↥X ⧸ CFSG.pCore 2 ↥X, a * b ≠ b * a) ∧
      CFSG.pCore 2 (↥X ⧸ CFSG.pCore 2 ↥X) = ⊥ := by
  obtain ⟨hperf, -, a, b, hab⟩ := hX.2.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨hperf, ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩,
    Sec18.pCore_quotient_pCore_eq_bot 2⟩

end Sections

section Certified

variable {G : Type} [Group G] [Finite G]

theorem isEmpty_j2_of_not_allPointsHJ (h134 : Item134) (h48 : Sec4.Item4_8) {A : Subgroup G}
    {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (hN : ¬ AllPointsHJ A) {c' : G}
    {L' : Subgroup G} (hc' : Subgroup.zpowers c' ∈ omegaA A) (hL' : L' ∈ lA A c') :
    IsEmpty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) :=
  ⟨fun e => hN (allPointsHJ_of_j2 h134 h48
    { h with zpowers_mem_omegaA := hc', mem_lA := hL' } ⟨e⟩)⟩

theorem false_of_simple_quot_of_orders (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (hbot : Item145BotS14) (hord : SimpleOrderFacts) {A : Subgroup G} {c : G} {L : Subgroup G}
    (hR : Sec15R G A c L) (hNHJ : ¬ AllPointsHJ A) {X : Subgroup G} (hX : X ∈ scriptY4 A (lB A))
    (hsimple : IsSimpleGroup (↥X ⧸ CFSG.pCore 2 ↥X))
    (hm : (∃ j : ℕ, 3 ≤ j ∧ StatedClassicalModel (↥X ⧸ CFSG.pCore 2 ↥X) .PSL 2 2 j) ∨
      StatedClassicalModel (↥X ⧸ CFSG.pCore 2 ↥X) .PSL 2 3 2)
    (hA5 : IsEmpty (↥X ⧸ CFSG.pCore 2 ↥X ≃* alternatingGroup (Fin 5))) : False := by
  have hS : Sec14Std G A c L := hR.toSec14Std
  obtain ⟨hA7, hA10, hL3, hLpi, hM22, hM12⟩ := hord _ hsimple hm
  obtain ⟨-, hnab, -⟩ := perfect_section_data hX
  have hdz : X = deltaZero A (lB A) X := rank3II_15_1_lB hS.isE27 (hbot G A c L hS) hX
  have hP : CFSG.pPrimeCore 3 (↥X ⧸ CFSG.pCore 2 ↥X) = ⊥ :=
    pPrimeCore_three_eq_bot_of_isSimpleGroup hsimple (three_dvd_card_quot_pCore_two hX)
  have hPX : CFSG.pPrimeCore 3 ↥X = CFSG.pCore 2 ↥X := pPrimeCore_three_eq_pCore_two hP
  have hey : letI := ker148_normal hX.1.2
      Nonempty (↥(img148 A X (deltaZero A (lB A) X)) ≃* ↥X ⧸ CFSG.pCore 2 ↥X) := by
    rw [← hdz]
    obtain ⟨e⟩ := nonempty_img148_equiv hX.1.2
    exact ⟨e.trans (QuotientGroup.quotientMulEquivOfEq hPX)⟩
  obtain ⟨c', hc', L', hL', ⟨φ⟩⟩ := exists_lA_of_isSimpleGroup_img148 (h148 G A c L hR) hX.1
    hS.toSec13Data.isElemAbelian.1 KFacts.KS14.ks15Z3PGLNonabelian hsimple hnab hey hA5 hA7 hA10
    hL3
  rcases (hS.chosen136.2 c' hc' L' hL').1 with ⟨⟨e⟩⟩ | ⟨p, e, hp, he, hiso⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact (isEmpty_j2_of_not_allPointsHJ h134 h48 hS hNHJ hc' hL').false e
  · exact hLpi p e (Proof155w3.isoLThreePi_of_mulEquiv φ.symm hiso)
  · exact hA7.false (φ.trans e)
  · exact hM22.false (φ.trans e)
  · exact hM12.false (φ.trans e)

theorem xInPiNHJR_of (hY4 : Y4LThreePiNHJR) (h148 : Item148R) (h134 : Item134)
    (h48 : Sec4.Item4_8) (hbot : Item145BotS14) (hK : EvenPerfectSection)
    (hord : SimpleOrderFacts) : XInPiNHJR := by
  intro G _ _ A c L hR hNHJ X hX J hJ0 hXJ hJpi
  by_contra hcon
  obtain ⟨hno1, hno2⟩ := not_or.mp hcon
  obtain ⟨n, hn, hJiso⟩ := hJpi
  obtain ⟨hperf, hnab, h2⟩ := perfect_section_data hX
  obtain ⟨H, N, hN, he⟩ :=
    exists_section_of_le hXJ.le (CFSG.pCore 2 ↥X) (inf_pCoreOf_le_pCore hXJ.le)
  have hnt : Nontrivial (↥X ⧸ CFSG.pCore 2 ↥X) := by
    obtain ⟨a, b, hab⟩ := hnab
    exact nontrivial_of_ne a b fun h => hab (by rw [h])
  obtain ⟨hsimple, hlist⟩ :=
    hK (↥J ⧸ CFSG.pCore 2 ↥J) n hn hJiso (↥X ⧸ CFSG.pCore 2 ↥X) H N he hperf hnt h2
  have hA5 : IsEmpty (↥X ⧸ CFSG.pCore 2 ↥X ≃* alternatingGroup (Fin 5)) :=
    ⟨fun e => hno2 ⟨e⟩⟩
  have key : ((∃ j : ℕ, 3 ≤ j ∧ StatedClassicalModel (↥X ⧸ CFSG.pCore 2 ↥X) .PSL 2 2 j) ∨
      StatedClassicalModel (↥X ⧸ CFSG.pCore 2 ↥X) .PSL 2 3 2) → False := fun hm =>
    false_of_simple_quot_of_orders h148 h134 h48 hbot hord hR hNHJ hX hsimple hm hA5
  rcases hlist with ⟨j, hj, hmodel⟩ | hA6 | ⟨f, hf, -, hε⟩
  · by_cases hj2 : j = 2
    · subst hj2
      obtain ⟨e⟩ := nonempty_mulEquiv_alt5_of_statedClassicalModel hmodel
      exact hno2 ⟨e⟩
    · exact key (Or.inl ⟨j, by omega, hmodel⟩)
  · exact key (Or.inr hA6)
  · exact hno1 ⟨f, hf, hY4 G A c L hR hNHJ X hX f hf hε⟩

theorem step155UpPiNHJR_of_two_inputs (hY4 : Y4LThreePiNHJR) (h148 : Item148R) (h134 : Item134)
    (h48 : Sec4.Item4_8) (hbot : Item145BotS14) (hK : EvenPerfectSection)
    (hord : SimpleOrderFacts) : Step155UpPiNHJR :=
  step155UpPiNHJR_of_xInPi (xInPiNHJR_of hY4 h148 h134 h48 hbot hK hord)

theorem step155UpPiNHJR_of_sections (hY4 : Y4LThreePiNHJR) (h148 : Item148R) (h134 : Item134)
    (h48 : Sec4.Item4_8) (hbot : Item145BotS14) (hK : EvenPerfectSection) : Step155UpPiNHJR :=
  step155UpPiNHJR_of_two_inputs hY4 h148 h134 h48 hbot hK simpleOrderFacts_holds

end Certified

end CFSG.RankThree.PartTwo.Sec15.Liebeck155
