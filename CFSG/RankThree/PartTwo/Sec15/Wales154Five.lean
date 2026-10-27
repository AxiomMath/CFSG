module

public import CFSG.RankThree.PartTwo.Sec15.Wales154Stage
import CFSG.RankThree.PartTwo.Sec15.Item155w2ProofBFix
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item143Proof
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofTools
import CFSG.RankThree.PartTwo.Sec18.Components
import CFSG.RankThree.PartTwo.KFacts.K71Residual
import CFSG.RankThree.PartTwo.KFacts.KS14PGL
import CFSG.RankThree.PartTwo.Sec4.Item424ProofBasic
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.RankThree.PartTwo.Sec14.Item148StepCases
public import CFSG.RankThree.PartTwo.Sec15.Item156ProofType

public section

namespace CFSG.RankThree.PartTwo.Sec15.Wales154

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem not_three_dvd_of_trivial_of_lB_eq_bot {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) {W : Subgroup G} (hW : W ≤ delta A (lB A) W)
    {B : Subgroup G} (hB : IsHyperplane A B) (hLB : lB A B = ⊥)
    (hBtriv : ∀ b ∈ B, ∀ y ∈ W, b * y * b⁻¹ * y⁻¹ ∈ pPrimeCoreOf 3 W) :
    ¬ 3 ∣ Nat.card W := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := h.isE27
  set O := pPrimeCoreOf 3 W with hO
  set OB := pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) with hOB
  set OA := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hOA
  have hpi : ∀ X : Subgroup G, IsPiSubgroup (piCompl 3) (pPrimeCoreOf 3 X) := fun X =>
    (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 X))
  have hK : IsPiSubgroup (piCompl 3) (OA ⊔ OB) :=
    isPiSubgroup_piCompl_sup (hpi _) (hpi _)
      ((pPrimeCoreOf_le 3 _).trans (centralizer_le_normalizer_pPrimeCoreOf hB.1))
  set V := W ⊓ (OA ⊔ OB) with hV
  have hWO : W ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pPrimeCoreOf 3 W
  have hWV : W ≤ V ⊔ O := by
    refine hW.trans (sSup_le fun Q hQ => ?_)
    have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.1.1.2.1
    have hBQ : B ≤ Subgroup.normalizer (Q : Set G) := hB.1.trans hQ.1.1.2.2
    rw [CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization 3
      Nat.prime_three B Q (hA.isPGroup.to_le hB.1) hQ3 hBQ]
    refine sup_le ?_ ?_
    · rw [Subgroup.commutator_le]
      intro q hq b hb
      have h1 := O.inv_mem (hBtriv b hb q (hQ.2 hq))
      have e : ⁅q, b⁆ = (b * q * b⁻¹ * q⁻¹)⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.mem_sup_right h1
    · have h1 := hQ.1.2 B hB
      rw [qBound, hLB, sup_bot_eq, sup_comm] at h1
      exact le_sup_of_le_left (le_inf (inf_le_left.trans hQ.2) h1)
  have hW3 : IsPiSubgroup (piCompl 3) (V ⊔ O) :=
    isPiSubgroup_piCompl_sup (isPiSubgroup_piCompl_of_le hK inf_le_right) (hpi W)
      (inf_le_left.trans hWO)
  exact fun h3 =>
    (isPiSubgroup_piCompl_iff Nat.prime_three _).mp hW3 (h3.trans (Subgroup.card_dvd_of_le hWV))

theorem three_dvd_card_perfectResidual_oPrimeResidual {K S : Type} [Group K] [Finite K]
    [Group S] [Finite S] [IsSimpleGroup S] [Group.IsPerfect S] (φ : K →* S)
    (hφ : Function.Surjective φ) (h3 : 3 ∣ Nat.card S) :
    3 ∣ Nat.card (inSubgroup perfectResidual (oPrimeResidual 3 K)) := by
  have hN : (oPrimeResidual 3 K).map φ = ⊤ := by
    rw [Stage1.Thm6.Prod.map_oPrimeResidual φ hφ Nat.prime_three]
    exact Sec17.Proof171Steps.oPrimeResidual_eq_top_of_isSimpleGroup h3
  have hP : (inSubgroup perfectResidual (oPrimeResidual 3 K)).map φ = ⊤ := by
    rw [KFacts.map_inSubgroup_perfectResidual_hom φ, hN, eq_top_iff]
    intro s _
    have hperf : Group.IsPerfect ↥(⊤ : Subgroup S) :=
      Group.IsPerfect.ofSurjective
        (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup S) ≃* S).symm.toMonoidHom) (MulEquiv.surjective _)
    have htop : perfectResidual ↥(⊤ : Subgroup S) = ⊤ :=
      eq_top_iff.2 ((perfect_residual_transport (MonoidHom.id ↥(⊤ : Subgroup S))).2.2 ⊤
        (Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv :
          ↥(⊤ : Subgroup ↥(⊤ : Subgroup S)) ≃* ↥(⊤ : Subgroup S)).symm.toMonoidHom)
          (MulEquiv.surjective _)))
    rw [inSubgroup, htop]
    exact ⟨⟨s, Subgroup.mem_top s⟩, Subgroup.mem_top _, rfl⟩
  have hd := Subgroup.card_map_dvd (inSubgroup perfectResidual (oPrimeResidual 3 K)) φ
  rw [hP, Subgroup.card_top] at hd
  exact h3.trans hd

theorem three_dvd_card_perfectResidual_oPrimeResidualOf {K H : Subgroup G} (hKH : K ≤ H)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] [Group.IsPerfect S] (φ : ↥K →* S)
    (hφ : Function.Surjective φ) (h3 : 3 ∣ Nat.card S) :
    3 ∣ Nat.card (inSubgroup perfectResidual (oPrimeResidualOf 3 H)) := by
  have h1 := three_dvd_card_perfectResidual_oPrimeResidual φ hφ h3
  have h2 : (inSubgroup perfectResidual (oPrimeResidual 3 ↥K)).map K.subtype =
      inSubgroup perfectResidual (oPrimeResidualOf 3 K) :=
    KFacts.map_inSubgroup_perfectResidual_hom K.subtype _
  have h4 : inSubgroup perfectResidual (oPrimeResidualOf 3 K) ≤
      inSubgroup perfectResidual (oPrimeResidualOf 3 H) :=
    Sec18.inSubgroup_perfectResidual_mono (oPrimeResidualOf_mono 3 hKH)
  refine (h1.trans ?_).trans (Subgroup.card_dvd_of_le h4)
  rw [← h2, Subgroup.card_map_of_injective K.subtype_injective]

theorem not_mem_centralizer_of_inducesOuterTheta {H : Type} [Group H] [Finite H] {x : H}
    {M : Subgroup H} (h : Sec4.InducesOuterTheta x M) :
    x ∉ Subgroup.centralizer (M : Set H) := by
  intro hc
  obtain ⟨hx, hout⟩ := h
  apply hout
  have h1 : Sec4.compAction M ⟨x, hx⟩ = 1 := by
    have hmem : (⟨x, hx⟩ : Subgroup.normalizer (M : Set H)) ∈ (Sec4.compAction M).ker := by
      rw [Sec4.compAction_ker]
      exact Subgroup.mem_subgroupOf.mpr hc
    exact hmem
  rw [h1, map_one]
  exact ⟨1, map_one _⟩

theorem alpha148_mem_centralizer {A Z : Subgroup G} [(ker148 A Z).Normal] {c : G}
    (hcA : c ∈ A) (hAZ : A ≤ Subgroup.normalizer (Z : Set G))
    (htriv : ∀ z ∈ Z, c * z * c⁻¹ * z⁻¹ ∈ pPrimeCoreOf 3 Z) :
    alpha148 A Z c hcA ∈ Subgroup.centralizer (img148 A Z Z : Set _) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨z, hz, rfl⟩
  have hzZ : (z : G) ∈ Z := Subgroup.mem_subgroupOf.mp hz
  have hc' : c⁻¹ ∈ trivSub Z := inv_mem (show c ∈ trivSub Z from ⟨hAZ hcA, htriv⟩)
  have h1 := hc'.2 _ (Z.inv_mem hzZ)
  rw [inv_inv, inv_inv] at h1
  simp only [alpha148, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul]
  rw [QuotientGroup.eq]
  show _ ∈ (pPrimeCoreOf 3 Z).subgroupOf (Z ⊔ A)
  rw [Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
  convert h1 using 1
  group

section Five


theorem eq_one_of_trivial_of_case5 {A : Subgroup G} {c₀ : G} {L₀ : Subgroup G}
    (h : Sec14Std G A c₀ L₀) (hLB : ∀ B, IsHyperplane A B → lB A B = ⊥) {Z : Subgroup G}
    (hAZ : A ≤ Subgroup.normalizer (Z : Set G)) [(ker148 A Z).Normal] {c : G} (hcA : c ∈ A)
    {L : Subgroup G} (hL : L ∈ lA A c) {n : ℕ} (hn : 1 ≤ n)
    (hfield : KFacts.InducesStdKind (img148 A Z Z) (alpha148 A Z c hcA) .field)
    (hK₀ : inSubgroup perfectResidual
        (oPrimeResidualOf 3 (Z ⊓ Subgroup.centralizer ({c} : Set G))) =
      deltaZero A (lB A) (inSubgroup perfectResidual
        (oPrimeResidualOf 3 (Z ⊓ Subgroup.centralizer ({c} : Set G)))))
    {K : Subgroup G} (hKLZ : K ≤ L ⊓ Z) (hKn : Sec4.IsoLThreePi ↥(img148 A Z K) 2 n)
    (hKp : Group.IsPerfect ↥K) {e : G} (heA : e ∈ A)
    (htriv : ∀ z ∈ Z, e * z * e⁻¹ * z⁻¹ ∈ pPrimeCoreOf 3 Z) : e = 1 := by
  by_contra he1
  have hA : Late.IsE27 A := h.isE27
  have hAe := h.toSec13Data.isElemAbelian
  set H := Z ⊓ Subgroup.centralizer ({c} : Set G) with hH
  set K₀ := inSubgroup perfectResidual (oPrimeResidualOf 3 H) with hK₀def
  have hout := KFacts.InducesStdKind.inducesOuterTheta _ hfield (by decide)
  have hcn : ¬ ∀ z ∈ Z, c * z * c⁻¹ * z⁻¹ ∈ pPrimeCoreOf 3 Z := fun ht =>
    not_mem_centralizer_of_inducesOuterTheta hout (alpha148_mem_centralizer hcA hAZ ht)
  have hne : c ∉ Subgroup.zpowers e := by
    intro hmem
    exact hcn ((Subgroup.zpowers_le.mpr (show e ∈ trivSub Z from ⟨hAZ heA, htriv⟩)) hmem).2
  set B := Subgroup.closure ({e, c} : Set G) with hBdef
  have hB9 : Nat.card B = 9 :=
    Sec4.Item424Proof.card_closure_pair_eq_nine hAe hA.2 heA hcA he1 hne
  have hBA : B ≤ A := by
    rw [hBdef, Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · rw [hx]; exact heA
    · rw [Set.mem_singleton_iff.mp hx]; exact hcA
  have hB : IsHyperplane A B := ⟨hBA, by rw [hA.2, hB9]⟩
  have hK₀H : K₀ ≤ H := (Sec6.inSubgroup_perfectResidual_le _).trans (Subgroup.map_subtype_le _)
  have hK₀Z : K₀ ≤ Z := hK₀H.trans inf_le_left
  have hK₀C : K₀ ≤ Subgroup.centralizer ({c} : Set G) := hK₀H.trans inf_le_right
  have hAC : A ≤ Subgroup.centralizer ({c} : Set G) := fun a ha => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, ha⟩ ⟨c, hcA⟩)
  have hAH : A ≤ Subgroup.normalizer (H : Set G) :=
    Late.le_normalizer_inf hAZ (hAC.trans Subgroup.le_normalizer)
  have hAK₀ : A ≤ Subgroup.normalizer (K₀ : Set G) :=
    Proof155w2.le_normalizer_inSubgroup_perfectResidual_of
      (Sec14.le_normalizer_oPrimeResidualOf hAH)
  have hBT : B ≤ trivSub K₀ := by
    rw [hBdef, Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · rw [hx]
      exact ⟨hAK₀ heA, trivial_of_le hK₀Z (hAK₀ heA) htriv⟩
    · rw [Set.mem_singleton_iff.mp hx]
      refine ⟨hAK₀ hcA, fun k hk => ?_⟩
      have hkc := Subgroup.mem_centralizer_singleton_iff.mp (hK₀C hk)
      rw [show c * k * c⁻¹ * k⁻¹ = 1 by rw [← hkc]; group]
      exact one_mem _
  have hK₀Δ : K₀ ≤ delta A (lB A) K₀ := hK₀.le.trans (deltaZero_le_delta _)
  refine not_three_dvd_of_trivial_of_lB_eq_bot h hK₀Δ hB (hLB B hB)
    (fun b hb y hy => (hBT hb).2 y hy) ?_
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) := by
    obtain ⟨L', -, rfl⟩ := hL.1
    exact Subgroup.map_subtype_le _
  have hKH : K ≤ H := le_inf (hKLZ.trans inf_le_right) ((hKLZ.trans inf_le_left).trans hLC)
  have hKZA : K ≤ Z ⊔ A := (hKLZ.trans inf_le_right).trans le_sup_left
  set φ : ↥K →* ↥(img148 A Z K) :=
    ((QuotientGroup.mk' (ker148 A Z)).subgroupMap (K.subgroupOf (Z ⊔ A))).comp
      (Subgroup.subgroupOfEquivOfLe hKZA).symm.toMonoidHom with hφdef
  have hφ : Function.Surjective φ :=
    ((QuotientGroup.mk' (ker148 A Z)).subgroupMap_surjective _).comp (MulEquiv.surjective _)
  have : Group.IsPerfect ↥(img148 A Z K) := @Group.IsPerfect.ofSurjective _ _ _ _ φ hKp hφ
  have h3 : 3 ∣ Nat.card ↥(img148 A Z K) := Main148.three_dvd_card_of_isoLThreePi148 hn hKn
  have : Nontrivial ↥(img148 A Z K) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have := Nat.le_of_dvd Nat.card_pos h3
    omega
  have : IsSimpleGroup ↥(img148 A Z K) :=
    Main148.isSimpleGroup_of_isLThreeEpsAt148 hn (Sec14.isLThreeEpsAt_of_isoLThreePi148 hKn)
  exact three_dvd_card_perfectResidual_oPrimeResidualOf hKH φ hφ h3

end Five

section Read5


theorem read154_nhj5 (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8)
    {A L : Subgroup G} {c : G} (hR : Sec15R G A c L) (hNHJ : ¬ AllPointsHJ A) {Z : Subgroup G}
    (hZ : Z ∈ scriptY4 A (lB A)) :
    (∃ c' : G, Subgroup.zpowers c' ∈ omegaA A ∧
      (∀ z ∈ Z, c' * z * c'⁻¹ * z⁻¹ ∈ pPrimeCoreOf 3 Z) ∧
      ∃ L' ∈ lA A c',
        Nonempty (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z ≃* ↥L' ⧸ aschbacherSolvableCore 3 ↥L') ∨
        ((Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
            (∃ _ : Fact (Nat.Prime 5), Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃*
              CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 5 2))) ∨
            (∃ _ : Fact (Nat.Prime 5), Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃*
              CFSG.Assembly.RankThreeEven.projSU 3 5 1))) ∧
          Nonempty (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z ≃* alternatingGroup (Fin 7))) ∨
        (∃ (p f e : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ 1 ≤ e ∧
          Sec4.IsoLThreePi (↥L' ⧸ aschbacherSolvableCore 3 ↥L') p (f * e) ∧
          IsLThreeEpsAt (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z) p f)) ∨
    Nonempty (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z ≃* alternatingGroup (Fin 10)) ∨
    (∃ (c' : G) (L' : Subgroup G) (n m : ℕ), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
      1 ≤ n ∧ 1 ≤ m ∧ Sec4.IsoLThreePi (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z) 2 (3 * n) ∧
      IsLThreeEpsAt (↥L' ⧸ aschbacherSolvableCore 3 ↥L') 2 (n * m) ∧
      (∀ a ∈ A, (∀ z ∈ Z, a * z * a⁻¹ * z⁻¹ ∈ pPrimeCoreOf 3 Z) → a = 1) ∧
      (letI := ker148_normal hZ.1.2; Case148Five A (lB A) Z)) := by
  have hZΔ := Proof1523Res3.eq_deltaZero_of_mem_scriptY4 h134 h48 hR hZ
  have hLB : ∀ B, IsHyperplane A B → lB A B = ⊥ := fun B hB =>
    lB_eq_bot_of_not_allPointsHJ' h134 h48 hR.toSec14Std hNHJ hB
  have hHJ : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) →
        False :=
    fun c' L' hc' hL' hJ => hNHJ (allPointsHJ_of_point h134 h48 hR.toSec14Std hc' hL' hJ)
  let := ker148_normal hZ.1.2
  have hq := Proof1515.isQuasisimple_quot_pPrimeCore hZ
  have hne := Proof1515.pPrimeCore_ne_top_of_mem_scriptY4 hZ
  obtain ⟨e0⟩ : Nonempty (↥(img148 A Z (deltaZero A (lB A) Z)) ≃* ↥Z ⧸ CFSG.pPrimeCore 3 ↥Z) := by
    rw [← hZΔ]
    exact Sec15.nonempty_img148_equiv hZ.1.2
  have hqX : IsQuasisimple ↥(img148 A Z (deltaZero A (lB A) Z)) :=
    CFSG.LocalCores.isQuasisimple_of_surjective hq e0.symm.toMonoidHom e0.symm.surjective
      (by rw [(MonoidHom.ker_eq_bot_iff _).mpr e0.symm.injective]; exact bot_le)
  rcases (h148 G A c L hR Z hZ.1).2 with h1 | h2 | h3 | h4 | h5 | h6 | h7
  ·
    exfalso
    apply hne
    rw [← hZΔ] at h1
    refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨z, hz, hzy⟩ := h1 y.2
    rwa [show z = y from Subtype.ext hzy] at hz
  ·
    obtain ⟨c', hc', hdec, L', hL', hcases⟩ := h2
    rw [← hZΔ] at hdec
    obtain ⟨hc'A, hc'3, -⟩ := zpowers_mem_omegaA_iff.mp hc'
    have hc'o : orderOf c' = 3 := by rw [← Nat.card_zpowers]; exact hc'3
    have htriv := trivial_of_dec hc'A hc'o hZ.1.2 hdec
    refine Or.inl ⟨c', hc', htriv, L', hL', ?_⟩
    rcases hcases with hφ | ⟨hL, hφ⟩ | ⟨p, f, e, hp, hf, he, hiso, hε⟩ | ⟨hJ, -⟩
    · obtain ⟨φ⟩ := hφ
      exact Or.inl ⟨e0.symm.trans φ⟩
    · obtain ⟨φ⟩ := hφ
      exact Or.inr (Or.inl ⟨hL, ⟨e0.symm.trans φ⟩⟩)
    · exact Or.inr (Or.inr ⟨p, f, e, hp, hf, he, hiso, IsLThreeEpsAt.of_mulEquiv e0 hε⟩)
    · exact (hHJ c' L' hc' hL' hJ).elim
  ·
    obtain ⟨c', -, L', hc', hL', hJ, -⟩ := h3
    exact (hHJ c' L' hc' hL' hJ).elim
  ·
    obtain ⟨⟨φ⟩, -, -⟩ := h4
    exact Or.inr (Or.inl ⟨e0.symm.trans φ⟩)
  ·
    have h5raw := h5
    obtain ⟨c', hc'A, L', n, m, hc', hL', hn, hm, hiso, -, -, hfield, hε, hK₀, K, hKLZ, hKn, hKp,
      -⟩ := h5
    refine Or.inr (Or.inr ⟨c', L', n, m, hc', hL', hn, hm, Proof1515.isoLThreePi_congr e0 hiso,
      hε, fun a ha htriv => ?_, h5raw⟩)
    rw [← hZΔ] at hfield hK₀
    exact eq_one_of_trivial_of_case5 hR.toSec14Std hLB hZ.1.2 hc'A hL' hn hfield hK₀ hKLZ hKn hKp
      ha htriv
  ·
    obtain ⟨-, ⟨c', L', hc', hL', hJ⟩, -⟩ := h6
    exact (hHJ c' L' hc' hL' hJ).elim
  ·
    exfalso
    obtain ⟨-, -, L₁, L₂, J₁, J₂, p₁, f₁, -, p₂, f₂, -, -, -, -, -, -, -, hJ₁, hJ₂, hsup, hinf,
      hcomm, -, -, -, -, hZ₁, hZ₂, -, -⟩ := h7
    set X := img148 A Z (deltaZero A (lB A) Z) with hX
    have hJ₁le : img148 A Z J₁ ≤ X := hsup ▸ le_sup_left
    have hJ₂le : img148 A Z J₂ ≤ X := hsup ▸ le_sup_right
    have hC₁ : img148 A Z J₂ ≤ Subgroup.centralizer (img148 A Z J₁ : Set _) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hcomm
    have hC₂ : img148 A Z J₁ ≤ Subgroup.centralizer (img148 A Z J₂ : Set _) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hN₁ : ((img148 A Z J₁).subgroupOf X).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hJ₁le).mpr ?_
      rw [← hsup]
      exact sup_le Subgroup.le_normalizer (hC₁.trans (Subgroup.centralizer_le_normalizer _))
    have hN₂ : ((img148 A Z J₂).subgroupOf X).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hJ₂le).mpr ?_
      rw [← hsup]
      exact sup_le (hC₂.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
    have hsup' : (img148 A Z J₁).subgroupOf X ⊔ (img148 A Z J₂).subgroupOf X = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hJ₁le hJ₂le, hsup, Subgroup.subgroupOf_self]
    have hinf' : (img148 A Z J₁).subgroupOf X ⊓ (img148 A Z J₂).subgroupOf X = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have h1 : (x : ↥(Z ⊔ A) ⧸ ker148 A Z) ∈ img148 A Z J₁ ⊓ img148 A Z J₂ := ⟨hx.1, hx.2⟩
      rw [hinf] at h1
      exact (Subgroup.mem_bot).mpr (Subtype.ext ((Subgroup.mem_bot).mp h1))
    have hbot : img148 A Z J₁ = ⊥ ∨ img148 A Z J₂ = ⊥ := by
      rcases Sec15.eq_bot_or_eq_bot_of_isQuasisimple hqX hN₁ hN₂ hsup' hinf' with h | h
      · left
        rw [Subgroup.subgroupOf_eq_bot] at h
        exact disjoint_self.mp (h.mono_right hJ₁le)
      · right
        rw [Subgroup.subgroupOf_eq_bot] at h
        exact disjoint_self.mp (h.mono_right hJ₂le)
    have hAle : A ≤ Z ⊔ A := le_sup_right
    have key : ∀ J : Subgroup G, J ≤ Z → img148 A Z J = ⊥ →
        ∀ p f : ℕ, IsZ3PGLThreeAt ↥(img148 A Z (J ⊔ A)) p f → False := by
      intro J hJZ hJ p f hZ'
      rw [Sec15.img148_sup (hJZ.trans le_sup_left) hAle, hJ, bot_sup_eq] at hZ'
      obtain ⟨a, b, hab⟩ := KFacts.KS14.ks15Z3PGLNonabelian _ p f hZ'
      exact hab (Sec15.img148_comm hR.isElemAbelian.1 a b)
    rcases hbot with h | h
    · exact key J₁ (hJ₁.trans inf_le_right) h p₁ f₁ hZ₁
    · exact key J₂ (hJ₂.trans inf_le_right) h p₂ f₂ hZ₂

end Read5

end CFSG.RankThree.PartTwo.Sec15.Wales154
