module

public import CFSG.RankThree.PartTwo.Sec17.Item174KFact39
import CFSG.RankThree.PartTwo.Sec16.Item166Res8ProofComm
import CFSG.RankThree.PartTwo.Sec21.Item21Res11ProofGroup
import CFSG.LocalAnalysis.QuasithinUnique.K1.Glue
import CFSG.GH74.Constrained
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpCoreA

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof174Host

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def KFactStar : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.IsKGroup H → IsSimpleGroup H →
    CFSG.Open.pRank 3 (⊤ : Subgroup H) ≤ 1 → ∀ t : H, orderOf t = 3 →
    ∀ I : Subgroup H, Subgroup.normalizer (Subgroup.zpowers t : Set H) ≤ I →
      ⁅CFSG.Open.pCoreOf 2 I, Subgroup.zpowers t⁆ ≠ ⊥ →
        ∃ n : ℕ, Odd n ∧ Nonempty (H ≃* CFSG.PGLModel.projSL 3 (GaloisField 2 n))

theorem mem_normalizer_zpowers_of {y c : G} (h1 : y * c * y⁻¹ ∈ Subgroup.zpowers c)
    (h2 : y⁻¹ * c * y ∈ Subgroup.zpowers c) :
    y ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨m, rfl⟩
    change y * c ^ m * y⁻¹ ∈ _
    rw [← conj_zpow]
    exact zpow_mem h1 m
  · intro hg
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hg
    have e : g = y⁻¹ * c ^ m * y⁻¹⁻¹ := by
      rw [hm]
      group
    rw [e, ← conj_zpow]
    exact zpow_mem (by simpa using h2) m

theorem kfact26At_of_star {A : Subgroup G} {c : G} {L Y₀ : Subgroup G} (h : Sec17Std G A c L Y₀)
    (h176 : Item176 A (lB A) c L) (hE : IsHyperplane A (A ⊓ L)) (hStar : KFactStar) :
    KFact26At A c L Y₀ := by
  intro hΩ _ hW
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E : Subgroup G := A ⊓ L with hEdef
  set X := normalClosureIn (Subgroup.centralizer (E : Set G)) c with hXdef
  set K := pPrimeCoreOf 3 X with hKdef
  set W := CFSG.Open.pCoreOf 2 (Subgroup.centralizer (Y₀ : Set G)) with hWdef
  haveI : (pPrimeCore 3 ↥X).Normal := pPrimeCore_normal
  set K' := pPrimeCore 3 ↥X with hK'def
  have hcA : c ∈ A := h.mem_A
  have hM : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (W : Set G) :=
    h.normalizer_le.trans (normalizer_le_normalizer_w Y₀)
  have hcCE : c ∈ Subgroup.centralizer (E : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun e he => h.commute he.1 hcA
  have hWC : W ≤ Subgroup.centralizer (E : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans
      (Subgroup.centralizer_le (inf_le_right.trans h.le_y0))
  have hcX : c ∈ X := by
    rw [hXdef, normalClosureIn]
    exact Subgroup.subset_closure ⟨1, one_mem _, by simp⟩
  have hc3 : orderOf c = 3 := by
    have hmem : Subgroup.zpowers c ∈ omegaA A := hΩ ▸ Set.mem_singleton _
    rw [← Nat.card_zpowers]
    exact (mem_omegaA_iff.mp hmem).2.1
  have hK'3 : ¬ 3 ∣ Nat.card K' :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp pPrimeCore_coprime_card
  set t : ↥X ⧸ K' := ((⟨c, hcX⟩ : ↥X) : ↥X ⧸ K') with htdef
  have ht3 : orderOf t = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [htdef, ← QuotientGroup.mk_pow]
      have : (⟨c, hcX⟩ : ↥X) ^ 3 = 1 := Subtype.ext (by simp [← hc3, pow_orderOf_eq_one])
      rw [this, QuotientGroup.mk_one]
    · intro h1
      have hcK : (⟨c, hcX⟩ : ↥X) ∈ K' := (QuotientGroup.eq_one_iff _).mp h1
      rw [mem_pPrimeCore_iff] at hcK
      have hdvd : 3 ∣ Nat.card K := hc3 ▸ Subgroup.orderOf_dvd_natCard K hcK
      have := Nat.Coprime.eq_one_of_dvd (coprime_card_pPrimeCoreOf 3 X) hdvd
      norm_num at this
  have h9 : Nat.card E = 9 := by
    have h27 : Nat.card A = 27 := h.toSec14Std.isE27.2
    have := hE.2
    omega
  have hCE : Subgroup.centralizer (E : Set G) ≠ ⊤ := Proof168Res8Comm.centralizer_ne_top h h9
  have hXtop : X ≠ ⊤ := fun hX =>
    hCE (top_le_iff.mp (hX ▸ le_centralizer_normalClosureIn hcCE))
  have hKg : CFSG.IsKGroup (↥X ⧸ K') :=
    ((h.toTheoremFourHyp.sectionFourHyp hXtop).kGroup).quotient _
  have hr : CFSG.Open.pRank 3 (⊤ : Subgroup (↥X ⧸ K')) ≤ 1 :=
    (CFSG.QuasithinUnique.K1.pRank_top_quotient_le X K' Nat.prime_three hK'3).trans
      ((h176 hΩ).1 _ hCE hcCE).le
  have hO : pPrimeCore 3 (↥X ⧸ K') = ⊥ := CFSG.GH74.pPrimeCore_quotient_pPrimeCore_eq_bot ↥X 3
  have hsimp : IsSimpleGroup (↥X ⧸ K') := by
    haveI : Nontrivial (↥X ⧸ K') := ⟨⟨t, 1, fun h1 => by rw [h1, orderOf_one] at ht3; omega⟩⟩
    set T : Set ↥X := {y | ∃ m ∈ Subgroup.centralizer (E : Set G), (y : G) = m * c * m⁻¹}
      with hTdef
    have hT : Subgroup.closure T = ⊤ := by
      have := Subgroup.closure_closure_coe_preimage
        (k := {x : G | ∃ m ∈ Subgroup.centralizer (E : Set G), x = m * c * m⁻¹})
      exact this
    refine CFSG.RankThree.PartTwo.Sec21.Item21Res11Proof.isSimpleGroup_of_pRank_le_one hr hO
      (S := (QuotientGroup.mk' K') '' T) ?_ ?_
    · rw [← MonoidHom.map_closure, hT, Subgroup.map_top_of_surjective _
        (QuotientGroup.mk'_surjective K')]
    · rintro _ ⟨y, ⟨m, hm, hy⟩, rfl⟩
      have hy3 : y ^ 3 = 1 := by
        refine Subtype.ext ?_
        rw [Subgroup.coe_pow, hy, conj_pow, ← hc3, pow_orderOf_eq_one]
        simp
      have hdvd : orderOf (QuotientGroup.mk' K' y) ∣ 3 := by
        refine orderOf_dvd_of_pow_eq_one ?_
        rw [← map_pow, hy3, map_one]
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · left
        exact orderOf_eq_one_iff.mp h1
      · right
        exact h3
  set M := Subgroup.normalizer (Y₀ : Set G) with hMdef
  set I : Subgroup (↥X ⧸ K') := ((M ⊓ X).subgroupOf X).map (QuotientGroup.mk' K') with hIdef
  have hP3 : IsPGroup 3 (Subgroup.zpowers (⟨c, hcX⟩ : ↥X)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hc3, pow_one])
  have hNI : Subgroup.normalizer (Subgroup.zpowers t : Set (↥X ⧸ K')) ≤ I := by
    have hmap : (Subgroup.zpowers (⟨c, hcX⟩ : ↥X)).map (QuotientGroup.mk' K') =
        Subgroup.zpowers t := MonoidHom.map_zpowers _ _
    rw [← hmap, ← CFSG.GroupTheory.normal_coprime_quotient_normalizer 3 K' hK'3 _ hP3]
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y, Subgroup.mem_subgroupOf.mpr ⟨?_, y.2⟩, rfl⟩
    have hcz : (⟨c, hcX⟩ : ↥X) ∈ Subgroup.zpowers (⟨c, hcX⟩ : ↥X) := Subgroup.mem_zpowers _
    have hval : ∀ z : ↥X, z ∈ Subgroup.zpowers (⟨c, hcX⟩ : ↥X) →
        (z : G) ∈ Subgroup.zpowers c := by
      rintro _ ⟨m, rfl⟩
      exact ⟨m, by simp⟩
    have h1 := hval _ ((Subgroup.mem_normalizer_iff.mp hy _).mp hcz)
    have h2 := hval _ ((Subgroup.mem_normalizer_iff.mp (inv_mem hy) _).mp hcz)
    simp only [Subgroup.coe_mul, inv_inv, Subgroup.coe_inv] at h1 h2
    exact h.normalizer_c_le (mem_normalizer_zpowers_of h1 h2)
  set D : Subgroup (↥X ⧸ K') := ((W ⊓ X).subgroupOf X).map (QuotientGroup.mk' K') with hDdef
  have hW2 : IsPGroup 2 W := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hD2 : IsPGroup 2 D := ((hW2.to_le inf_le_left).comap_subtype).map _
  have hWM : W ≤ M :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (Subgroup.centralizer_le_normalizer _)
  have hDI : D ≤ I := Subgroup.map_mono fun w hw =>
    Subgroup.mem_subgroupOf.mpr ⟨hWM (Subgroup.mem_subgroupOf.mp hw).1,
      (Subgroup.mem_subgroupOf.mp hw).2⟩
  have hID : I ≤ Subgroup.normalizer (D : Set (↥X ⧸ K')) := by
    rintro _ ⟨z, hz, rfl⟩
    have hzW : (z : G) ∈ Subgroup.normalizer (W : Set G) :=
      normalizer_le_normalizer_w Y₀ (Subgroup.mem_subgroupOf.mp hz).1
    rw [Subgroup.mem_normalizer_iff]
    intro d
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw' := Subgroup.mem_subgroupOf.mp hw
      refine ⟨z * w * z⁻¹, Subgroup.mem_subgroupOf.mpr ⟨?_, (z * w * z⁻¹).2⟩, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hzW _).mp hw'.1
    · intro hd
      obtain ⟨w, hw, hwd⟩ := hd
      have hw' := Subgroup.mem_subgroupOf.mp hw
      refine ⟨z⁻¹ * w * z⁻¹⁻¹, Subgroup.mem_subgroupOf.mpr ⟨?_, (z⁻¹ * w * z⁻¹⁻¹).2⟩, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (inv_mem hzW) _).mp hw'.1
      · rw [map_mul, map_mul, hwd]
        simp [mul_assoc]
  have hDO : D ≤ CFSG.Open.pCoreOf 2 I :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hDI hID hD2
  have hcW : Subgroup.zpowers c ≤ Subgroup.normalizer (W : Set G) :=
    (Subgroup.zpowers_le.mpr hcA).trans (Subgroup.le_normalizer.trans hM)
  have hcWX : ⁅W, Subgroup.zpowers c⁆ ≤ W ⊓ X := by
    rw [Subgroup.commutator_comm]
    refine le_inf (Subgroup.le_normalizer_iff_commutator_le_right.mp hcW) ?_
    rw [Subgroup.commutator_le]
    intro g hg w hw
    have hgX : g ∈ X := (Subgroup.zpowers_le.mpr hcX) hg
    have hwX : w * g⁻¹ * w⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_normalClosureIn _ c (hWC hw)) _).mp
        (inv_mem hgX)
    rw [commutatorElement_def]
    have := mul_mem hgX hwX
    rwa [show g * (w * g⁻¹ * w⁻¹) = g * w * g⁻¹ * w⁻¹ by group] at this
  have hO2 : ⁅CFSG.Open.pCoreOf 2 I, Subgroup.zpowers t⁆ ≠ ⊥ := by
    intro hbot
    apply hW
    have hDt : D ≤ Subgroup.centralizer (Subgroup.zpowers t : Set (↥X ⧸ K')) :=
      hDO.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
    have hWXc : ⁅W ⊓ X, Subgroup.zpowers c⁆ ≤ K := by
      rw [Subgroup.commutator_le]
      intro w hw g hg
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      have hd : ((⟨w, hw.2⟩ : ↥X) : ↥X ⧸ K') ∈ D :=
        ⟨⟨w, hw.2⟩, Subgroup.mem_subgroupOf.mpr hw, rfl⟩
      have hs : ((⟨c, hcX⟩ ^ m : ↥X) : ↥X ⧸ K') ∈ Subgroup.zpowers t := by
        rw [QuotientGroup.mk_zpow]
        exact zpow_mem (Subgroup.mem_zpowers t) m
      have hcomm := Subgroup.mem_centralizer_iff.mp (hDt hd) _ hs
      have h1 : ((⁅(⟨w, hw.2⟩ : ↥X), ⟨c, hcX⟩ ^ m⁆ : ↥X) : ↥X ⧸ K') = 1 := by
        rw [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
          QuotientGroup.mk_inv, QuotientGroup.mk_inv, ← hcomm]
        group
      have h2 := (mem_pPrimeCore_iff X _).mp ((QuotientGroup.eq_one_iff _).mp h1)
      simpa [commutatorElement_def] using h2
    have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers c)) (Nat.card W) := by
      obtain ⟨k, hk⟩ := hW2.exists_card_eq
      rw [hk, Nat.card_zpowers, hc3]
      exact Nat.Coprime.pow_right k (by norm_num)
    rw [← CFSG.GH74.GLS.Stage2.Signalizer.Odd87.CoreA.commutator_commutator_eq_of_coprime hcW hcop]
    exact (Subgroup.commutator_mono hcWX le_rfl).trans hWXc
  exact hStar (↥X ⧸ K') hKg hsimp hr t ht3 I hNI hO2

end CFSG.RankThree.PartTwo.Sec17.Proof174Host
