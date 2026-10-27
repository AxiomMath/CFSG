module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1L3Defs
public import CFSG.RankThree.PartTwo.Sec15.Item15Res6ProofComp
public import CFSG.RankThree.PartTwo.Sec14.Item14Tools
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofPoints
public import CFSG.RankThree.PartTwo.Sec15.Gagen155INorm
public import CFSG.RankThree.PartTwo.Sec15.Item15Res6ProofTools
public import CFSG.RankThree.PartTwo.Sec15.Gagen1511WStar
public import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
public import CFSG.RankThree.PartTwo.Sec16.Item166ResProofDeltaSz

public section

namespace CFSG.RankThree.PartTwo.Sec15.GagenL3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_two_le_pPrimeCoreOf_three {X M : Subgroup G} (hXM : X ≤ M)
    (hMX : M = Subgroup.normalizer (X : Set G)) :
    CFSG.Open.pCoreOf 2 X ≤ pPrimeCoreOf 3 M := by
  refine Sec14.le_pPrimeCoreOf ?_ ?_ ?_
  · exact (CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hXM
  · rw [hMX]
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X
  · obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
    rw [hn]
    exact Nat.Coprime.pow_right _ (by norm_num)

theorem isSimpleGroup_img148_caseTwo_l3 {A : Subgroup G} {L M : Subgroup G}
    [(ker148 A M).Normal] (hQ : Res1L3Q (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hQ' : ∀ {c' : G} {L' : Subgroup G}, Subgroup.zpowers c' ∈ omegaA A →
      L' ∈ lA A c' → L' = L)
    (h2 : Case148Two A (lB A) M) :
    IsSimpleGroup ↥(img148 A M (deltaZero A (lB A) M)) := by
  obtain ⟨c', hc', -, L', hL', hcases⟩ := h2
  have hLL : L' = L := hQ' hc' hL'
  rcases hcases with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨p, f, e', hp, hf, he', -, hε⟩ | ⟨⟨φ⟩, -⟩
  · rw [hLL] at φ
    have : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) := hQ.2.1
    exact φ.isSimpleGroup
  · have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by simp)
    exact φ.isSimpleGroup
  · have : Fact p.Prime := hp
    rcases hε with ⟨⟨ψ⟩⟩ | ⟨hq, ⟨ψ⟩⟩
    · have : IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField p f)) :=
        Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field _
      exact ψ.isSimpleGroup
    · have : IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSU 3 p f) :=
        Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two p f hf (by omega)
      exact ψ.isSimpleGroup
  · rw [hLL] at φ
    exact ((Proof15Res6.isEmpty_j2_of_types (Or.inl hQ.1)).false φ).elim

theorem mem_pPrimeCoreOf_of_centralizes_img148_l3 {A X M : Subgroup G} [(ker148 A M).Normal]
    (hO2M : CFSG.Open.pCoreOf 2 X ≤ pPrimeCoreOf 3 M)
    (hDs : IsSimpleGroup ↥(img148 A M (deltaZero A (lB A) M)))
    {V : Subgroup ↥(img148 A M (deltaZero A (lB A) M))}
    (hVsub : V.IsSubnormal) (hVq : CFSG.IsQuasisimple ↥V)
    (hVeq : V = (img148 A M X).subgroupOf (img148 A M (deltaZero A (lB A) M)))
    {b : G} (hbMA : b ∈ M ⊔ A) (hbD : b ∈ deltaZero A (lB A) M)
    (hbU : b ∈ u155 A M X) : b ∈ pPrimeCoreOf 3 M := by
  have hone : (⟨QuotientGroup.mk' (ker148 A M) ⟨b, hbMA⟩,
      mem_img148_iff.mpr ⟨b, hbMA, hbD, rfl⟩⟩ :
      ↥(img148 A M (deltaZero A (lB A) M))) = 1 := by
    have hVtop : V = ⊤ := by
      have hVne : V ≠ ⊥ :=
        (Subgroup.nontrivial_iff_ne_bot V).mp
          (CFSG.LocalCores.isQuasisimple_nontrivial hVq)
      exact (hVsub.eq_bot_or_top_of_isSimpleGroup hDs).resolve_left hVne
    have : IsSimpleGroup ↥V := by
      have : IsSimpleGroup ↥(⊤ : Subgroup ↥(img148 A M (deltaZero A (lB A) M))) :=
        Subgroup.topEquiv.isSimpleGroup
      rwa [hVtop]
    refine Sec16.ProofDeltaSz166.eq_one_of_forall_commute (D := V) hVq ?_ ?_
    · rw [hVtop]
      exact Subgroup.mem_top _
    · intro v hv
      have hv' : (v : ↥(M ⊔ A) ⧸ ker148 A M) ∈ img148 A M X := by
        rw [hVeq] at hv
        exact Subgroup.mem_subgroupOf.mp hv
      obtain ⟨x, hxMA, hxX, hxv⟩ := mem_img148_iff.mp hv'
      have hcomm : ⁅x, b⁆ ∈ pPrimeCoreOf 3 M := hO2M (hbU.2.2.2 x hxX)
      have hmemMA : ⁅x, b⁆ ∈ M ⊔ A :=
        Subgroup.mem_sup_left (Sec14.pPrimeCoreOf_le 3 M hcomm)
      have hz : QuotientGroup.mk' (ker148 A M) ⟨⁅x, b⁆, hmemMA⟩ = 1 :=
        mk'_ker148_eq_one_iff.mpr hcomm
      have heq : (⟨⁅x, b⁆, hmemMA⟩ : ↥(M ⊔ A)) =
          ⁅(⟨x, hxMA⟩ : ↥(M ⊔ A)), (⟨b, hbMA⟩ : ↥(M ⊔ A))⁆ := by
        apply Subtype.ext
        simp [commutatorElement_def]
      rw [heq, map_commutatorElement] at hz
      have hcm := commutatorElement_eq_one_iff_mul_comm.mp hz
      apply Subtype.ext
      change QuotientGroup.mk' (ker148 A M) ⟨b, hbMA⟩ *
        (v : ↥(M ⊔ A) ⧸ ker148 A M) =
        (v : ↥(M ⊔ A) ⧸ ker148 A M) *
          QuotientGroup.mk' (ker148 A M) ⟨b, hbMA⟩
      rw [← hxv]
      exact hcm.symm
  exact mk'_ker148_eq_one_iff.mp (congrArg Subtype.val hone)

theorem b155_le_pPrimeCoreOf_l3 {A X M : Subgroup G} [(ker148 A M).Normal]
    (hXM : X ≤ M) (hMX : M = Subgroup.normalizer (X : Set G))
    (hI₀M : oPrimeResidualOf 3 (delta A (lB A) M) ≤ M)
    (hI₀Δ : oPrimeResidualOf 3 (delta A (lB A) M) ≤ deltaZero A (lB A) M)
    (hDs : IsSimpleGroup ↥(img148 A M (deltaZero A (lB A) M)))
    {V : Subgroup ↥(img148 A M (deltaZero A (lB A) M))}
    (hVsub : V.IsSubnormal) (hVq : CFSG.IsQuasisimple ↥V)
    (hVeq : V = (img148 A M X).subgroupOf (img148 A M (deltaZero A (lB A) M))) :
    b155 A M X ≤ pPrimeCoreOf 3 M := by
  have hO2M : CFSG.Open.pCoreOf 2 X ≤ pPrimeCoreOf 3 M :=
    pCoreOf_two_le_pPrimeCoreOf_three hXM hMX
  have hBI₀ : b155 A M X ≤ oPrimeResidualOf 3 (delta A (lB A) M) :=
    Sec15.oPrimeResidualOf_mono 3 inf_le_left
  intro b hb
  have hbU : b ∈ u155 A M X := Sec14.oPrimeResidualOf_le_self 3 _ hb
  have hbM : b ∈ M := hI₀M (hBI₀ hb)
  have hbMA : b ∈ M ⊔ A := Subgroup.mem_sup_left hbM
  have hbD : b ∈ deltaZero A (lB A) M := hI₀Δ (hBI₀ hb)
  exact mem_pPrimeCoreOf_of_centralizes_img148_l3 hO2M hDs hVsub hVq hVeq hbMA hbD hbU

theorem oPrimeResidualOf_b155 (A M X : Subgroup G) :
    oPrimeResidualOf 3 (b155 A M X) = b155 A M X :=
  Sec14.oPrimeResidualOf_eq_of_le (Sec14.oPrimeResidualOf_le_self 3 _) fun x hx k hk => by
    show x ∈ oPrimeResidualOf 3 (u155 A M X)
    rw [Sec14.oPrimeResidualOf_eq_closure]
    exact Subgroup.subset_closure ⟨hx, k, hk⟩

theorem eq_bot_of_le_pPrimeCoreOf_three {B M : Subgroup G}
    (hB : B ≤ pPrimeCoreOf 3 M) (hBB : oPrimeResidualOf 3 B = B) : B = ⊥ := by
  have hB3 : ¬ 3 ∣ Nat.card B := by
    intro h3
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (Sec14.coprime_card_pPrimeCoreOf 3 M) (h3.trans (Subgroup.card_dvd_of_le hB))
  exact hBB.symm.trans (Sec16.oPrimeResidualOf_three_eq_bot_of_not_dvd hB3)


theorem isSimpleGroup_img148_caseFive_l3 {A M : Subgroup G} [(ker148 A M).Normal]
    (h5 : Case148Five A (lB A) M) :
    IsSimpleGroup ↥(img148 A M (deltaZero A (lB A) M)) := by
  obtain ⟨c', hcA, L', n, m, hc', hL', hn, hm, hiso, -⟩ := h5
  have hq : 2 ^ (3 * n) ≠ 2 := by
    intro h2'
    have h3n : 3 * n = 1 :=
      Nat.pow_right_injective (by norm_num : 2 ≤ 2) (h2'.trans (pow_one 2).symm)
    omega
  rcases hiso with ⟨-, ⟨ψ⟩⟩ | ⟨-, ⟨ψ⟩⟩
  · have : IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 (3 * n))) :=
      Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field _
    exact ψ.isSimpleGroup
  · have : IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSU 3 2 (3 * n)) :=
      Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two 2 (3 * n) (by omega) hq
    exact ψ.isSimpleGroup


theorem isSimpleGroup_img148_deltaZero_l3 {A : Subgroup G} {c : G} {L M : Subgroup G}
    [(ker148 A M).Normal]
    (hR : Sec15R G A c L) (hQ : Res1L3Q (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hN : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (h148 : Item148 A (lB A)) (hM2 : M ∈ scriptY2 A)
    (hΩ : omegaA A = {Subgroup.zpowers c})
    {V : Subgroup ↥(img148 A M (deltaZero A (lB A) M))}
    (hVq : CFSG.IsQuasisimple ↥V) :
    IsSimpleGroup ↥(img148 A M (deltaZero A (lB A) M)) := by
  have h3L : 3 ∣ Nat.card L := by
    refine Proof1515.three_dvd_card_of_thetaQuot ?_
    obtain ⟨E, -, hE9⟩ := hQ.2.2
    have h3E : 3 ∣ Nat.card E := by rw [hE9]; norm_num
    exact h3E.trans (Subgroup.card_subgroup_dvd_card E)
  have hQ' : ∀ {c' : G} {L' : Subgroup G}, Subgroup.zpowers c' ∈ omegaA A →
      L' ∈ lA A c' → L' = L := by
    intro c' L' hc' hL'
    have hcc : Subgroup.zpowers c' = Subgroup.zpowers c := by
      rw [hΩ] at hc'
      exact Set.mem_singleton_iff.mp hc'
    exact Proof1515.eq_of_mem_lA_of_zpowers_eq hR.toSec14Std h3L hcc hL'
  have hD0 := hR.toSec13Data
  rcases (h148 M hM2.1).2 with h1 | h2 | h3 | h4 | h5 | h6 | h7
  ·
    exfalso
    have hD1 : img148 A M (deltaZero A (lB A) M) = ⊥ := img148_eq_bot_of_le h1
    have hsub : Subsingleton ↥(img148 A M (deltaZero A (lB A) M)) := by
      refine ⟨fun x y => Subtype.ext ?_⟩
      exact (Subgroup.mem_bot.mp (hD1 ▸ x.2)).trans
        (Subgroup.mem_bot.mp (hD1 ▸ y.2)).symm
    have hVbot : V = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      exact hsub.elim x 1
    exact (Subgroup.nontrivial_iff_ne_bot V).mp
      (CFSG.LocalCores.isQuasisimple_nontrivial hVq) hVbot
  ·
    exact isSimpleGroup_img148_caseTwo_l3 hQ hQ' h2
  ·
    obtain ⟨c', d, L', hc', hL', ⟨φ⟩, -⟩ := h3
    rw [hQ' hc' hL'] at φ
    exact ((Proof15Res6.isEmpty_j2_of_types (Or.inl hQ.1)).false φ).elim
  ·
    obtain ⟨-, -, hW⟩ := h4
    exact (Proof1511Point.not_wStarS4_of_le_normalizer hR.isE27 hD0.mem_A hD0.ne_one hN
      hW).elim
  ·
    exact isSimpleGroup_img148_caseFive_l3 h5
  ·
    obtain ⟨-, ⟨c', L', hc', hL', ⟨φ⟩⟩, -⟩ := h6
    rw [hQ' hc' hL'] at φ
    exact ((Proof15Res6.isEmpty_j2_of_types (Or.inl hQ.1)).false φ).elim
  ·
    exact (Proof15Res6.false_of_case148Seven_two hR.toSec14Std h148 hM2 h7).elim

theorem res1_b155_eq_bot_l3 {A : Subgroup G} {c : G} {L : Subgroup G} (hR : Sec15R G A c L)
    (hQ : Res1L3Q (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hN : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (h148 : Item148 A (lB A)) (h149 : Item149 A (lB A))
    {X K Y M T P' : Subgroup G} (hC : Ctx155 A X K Y M T) (hE : End155N A X K Y M T P')
    (hΩ : omegaA A = {Subgroup.zpowers c})
    (hMX : M = Subgroup.normalizer (X : Set G)) : b155 A M X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := hR.toSec14Std
  have hX4 : X ∈ scriptY4 A (lB A) := hC.res ▸ hC.isY.2.1
  have hXY : X ≤ Y := hC.res ▸ Sec14.oPrimeResidualOf_le_self 3 Y
  have hMXm : M ∈ CFSG.maximalTwoLocalsContaining ((X ⊔ A : Subgroup G) : Set G) := by
    refine ⟨hC.mem_m.1, ?_⟩
    have hAY : (A ⊔ Y : Subgroup G) ≤ M := hC.mem_m.2
    exact fun z hz => (sup_le (hXY.trans (le_sup_right.trans hAY))
      (le_sup_left.trans hAY)) hz
  obtain ⟨hXM, hAM, hM2, -⟩ := facts_of_mem_maximalTwoLocalsContaining h hMXm
  let : (ker148 A M).Normal := ker148_normal hM2.1.2
  obtain ⟨heq149, -, -⟩ := h149 M hM2.1
  have hI₀Δ : oPrimeResidualOf 3 (delta A (lB A) M) ≤ deltaZero A (lB A) M := by
    rw [heq149]
    exact (Sec14.oPrimeResidualOf_le_self 3 _).trans (Sec14.inSubgroup_oResidual_le_self 2 _)
  have hXI₀ : X ≤ oPrimeResidualOf 3 (delta A (lB A) M) := le_oPrimeResidualOf_delta hX4 hXM
  have hI₀M : oPrimeResidualOf 3 (delta A (lB A) M) ≤ M :=
    (Sec14.oPrimeResidualOf_le_self 3 _).trans (delta_le M)
  have hXD : X ≤ deltaZero A (lB A) M := hXI₀.trans hI₀Δ
  set D := img148 A M (deltaZero A (lB A) M) with hD
  set V := (img148 A M X).subgroupOf D with hV
  have hVsub : V.IsSubnormal := by
    rw [hV, hD]
    exact Proof153Twin3.isSubnormal_img_subgroupOf hAM hE.mem_x
  obtain ⟨eY⟩ := Proof155INorm.nonempty_quot_equiv_img hAM hE.mem_x hXD
  have hVq : CFSG.IsQuasisimple ↥V := CFSG.LocalCores.isQuasisimple_of_mulEquiv eY
    (Proof1515.isQuasisimple_quot_pPrimeCore hX4)
  have hDs : IsSimpleGroup ↥D := by
    rw [hD]
    exact isSimpleGroup_img148_deltaZero_l3 hR hQ hN h148 hM2 hΩ hVq
  have hBle : b155 A M X ≤ pPrimeCoreOf 3 M :=
    b155_le_pPrimeCoreOf_l3 hXM hMX hI₀M hI₀Δ hDs hVsub hVq hV
  exact eq_bot_of_le_pPrimeCoreOf_three hBle (oPrimeResidualOf_b155 A M X)

theorem res1_b155_eq_bot_l3_of_tau (h148 : Item148R) (h149 : Sec16.Item149S14)
    {Q : ∀ (X : Type) [Group X], Prop} {P : ∀ (Y : Type) [Group Y], Prop}
    (hQ : ∀ (X : Type) [Group X], Q X → Res1L3Q X) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L X K Y M T P' : Subgroup G)
      (Yc : Subgroup (Res1Q A L)) (z : G),
      Sylow155R1.Res1Tau Q P A c L X K Y M T P' Yc z → b155 A M X = ⊥ :=
  fun G _ _ A c L _ _ _ _ _ _ _ _ τ =>
    res1_b155_eq_bot_l3 τ.sec15 (hQ _ τ.q) τ.norm (h148 G A c L τ.sec15) (h149 G A c L τ.std)
      τ.ctx τ.endN τ.omega τ.m_eq

end CFSG.RankThree.PartTwo.Sec15.GagenL3
