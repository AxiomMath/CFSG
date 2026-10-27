module

public import CFSG.RankThree.LocalRank.PartTwoCollections
import CFSG.LocalAnalysis.SignalizerFunctor.HyperplaneGeneration
import CFSG.LieType.BorelTits.Basic
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Source

open CFSG.Assembly.RankThreeEven

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem assembly_pCoreOf_eq_open (p : ℕ) (H : Subgroup G) :
    CFSG.Assembly.pCoreOf p H = CFSG.Open.pCoreOf p H :=
  rfl

theorem inf_eq_bot_of_isPGroup {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup q K) : H ⊓ K = ⊥ := by
  obtain ⟨a, ha⟩ := hH.exists_card_eq
  obtain ⟨b, hb⟩ := hK.exists_card_eq
  have hcop : Nat.Coprime (Nat.card H) (Nat.card K) := by
    rw [ha, hb]
    exact Nat.Coprime.pow a b ((Nat.coprime_primes Fact.out Fact.out).mpr hpq)
  exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)

omit [Finite G] in
theorem card_eq_nine_of_index {A B : Subgroup G} (hA : Nat.card A = 27) (hBA : B ≤ A)
    (hB : (B.subgroupOf A).index = 3) : Nat.card B = 9 := by
  have h := Subgroup.relIndex_mul_card B A
  rw [inf_of_le_left hBA] at h
  change (B.subgroupOf A).index * Nat.card B = Nat.card A at h
  rw [hB, hA] at h
  omega

omit [Finite G] in
theorem isElemAbelian_of_le {p : ℕ} {A B : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian p A)
    (hBA : B ≤ A) : CFSG.Assembly.IsElemAbelian p B := CFSG.Open.IsElemAbelian.mono hA hBA

theorem le_assembly_pRank {p : ℕ} (hp : p.Prime) {H E : Subgroup G} (hEH : E ≤ H)
    (hE : CFSG.Assembly.IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) :
    k ≤ CFSG.Assembly.pRank p H :=
  CFSG.SectionRank.le_pRank hp.one_lt hEH hE hk

theorem normalizer_le_aschCore {A B : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) (hBA : B ≤ A) (hB9 : Nat.card B = 9) :
    Subgroup.normalizer (B : Set G) ≤ aschCore 2 3 A := by
  refine le_sSup ⟨B, hBA, ?_, ?_, rfl⟩
  · exact le_assembly_pRank Nat.prime_three le_rfl (isElemAbelian_of_le hA hBA)
      (by rw [hB9]; norm_num)
  · have hAC : A ⊓ Subgroup.centralizer (B : Set G) = A := by
      refine inf_of_le_left fun a ha => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact congrArg Subtype.val (hA.1.is_comm.comm ⟨b, hBA hb⟩ ⟨a, ha⟩)
    rw [hAC, sup_of_le_right hBA]
    exact le_assembly_pRank Nat.prime_three le_rfl hA (by rw [hA27]; norm_num)

theorem le_aschCore_of_le_normalizer {A S : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) (hS : IsPGroup 2 S) (hAS : A ≤ Subgroup.normalizer (S : Set G)) :
    S ≤ aschCore 2 3 A := by
  have hAne : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hA27
    omega
  have hcop : Nat.Coprime 3 (Nat.card S) := by
    obtain ⟨k, hk⟩ := hS.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_hyperplane_generation 3
    Nat.prime_three A S hA hAne hAS hcop
  rw [← hgen]
  refine iSup_le fun B => iSup_le fun hBA => iSup_le fun hB => ?_
  exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
    (normalizer_le_aschCore hA hA27 hBA (card_eq_nine_of_index hA27 hBA hB)))

theorem isPGroup_pCoreOf_two (H : Subgroup G) : IsPGroup 2 (CFSG.Assembly.pCoreOf 2 H) :=
  CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H

omit [Finite G] in
theorem le_normalizer_pCoreOf_two (H : Subgroup G) :
    H ≤ Subgroup.normalizer (CFSG.Assembly.pCoreOf 2 H : Set G) :=
  CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H

theorem inf_centralizer_pCoreOf_eq_bot (hchar : CFSG.Assembly.IsCharTwoType G) {H B : Subgroup G}
    (hH : CFSG.Assembly.IsTwoLocal H) {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) (hB : IsPGroup q B)
    (hBH : B ≤ H) :
    B ⊓ Subgroup.centralizer (CFSG.Assembly.pCoreOf 2 H : Set G) = ⊥ := by
  have h := hchar H hH
  have hle : B ⊓ Subgroup.centralizer (CFSG.Assembly.pCoreOf 2 H : Set G) ≤
      B ⊓ CFSG.Assembly.pCoreOf 2 H :=
    le_inf inf_le_left ((inf_le_inf_right _ hBH).trans h)
  rw [eq_bot_iff]
  refine hle.trans ?_
  rw [inf_eq_bot_of_isPGroup hq hB (isPGroup_pCoreOf_two H)]

theorem exists_faithful_twoSubgroup (hchar : CFSG.Assembly.IsCharTwoType G) {A : Subgroup G}
    (hA : A ∈ CFSG.RankThree.LocalRank.partTwoE G) :
    ∃ S : Subgroup G, IsPGroup 2 S ∧ A ≤ Subgroup.normalizer (S : Set G) ∧
      A ⊓ Subgroup.centralizer (S : Set G) = ⊥ := by
  obtain ⟨-, hA27, U, hU1, hU2, hAU⟩ := hA
  have hH : CFSG.Assembly.IsTwoLocal (Subgroup.normalizer (U : Set G)) := ⟨U, hU1, hU2, rfl⟩
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA27]; norm_num)
  exact ⟨CFSG.Assembly.pCoreOf 2 (Subgroup.normalizer (U : Set G)), isPGroup_pCoreOf_two _,
    hAU.trans (le_normalizer_pCoreOf_two _),
    inf_centralizer_pCoreOf_eq_bot hchar hH (by norm_num) hA3 hAU⟩

theorem eq_bot_of_twoSubgroup_le_centralizer (hchar : CFSG.Assembly.IsCharTwoType G)
    {A Y R : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) (hY : IsPGroup q Y)
    (hΓ : aschCore 2 3 A ≤ Subgroup.normalizer (Y : Set G))
    (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥) (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hRY : R ≤ Subgroup.centralizer (Y : Set G)) : Y = ⊥ := by
  have hH : CFSG.Assembly.IsTwoLocal (Subgroup.normalizer (R : Set G)) := ⟨R, hR1, hR2, rfl⟩
  set H := Subgroup.normalizer (R : Set G) with hH_def
  set S' := CFSG.Assembly.pCoreOf 2 H with hS'_def
  have hS'2 : IsPGroup 2 S' := isPGroup_pCoreOf_two H
  have hS'Y : S' ≤ Subgroup.normalizer (Y : Set G) :=
    (le_aschCore_of_le_normalizer hA hA27 hS'2 (hAR.trans (le_normalizer_pCoreOf_two H))).trans hΓ
  have hYH : Y ≤ H :=
    (Subgroup.le_centralizer_iff.mp hRY).trans (Subgroup.centralizer_le_normalizer _)
  have hYS' : Y ≤ Subgroup.normalizer (S' : Set G) := hYH.trans (le_normalizer_pCoreOf_two H)
  have hc1 : ⁅S', Y⁆ ≤ S' := Subgroup.le_normalizer_iff_commutator_le_left.mp hYS'
  have hc2 : ⁅S', Y⁆ ≤ Y := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hS'Y
  have hinf : S' ⊓ Y = ⊥ := inf_eq_bot_of_isPGroup (Ne.symm hq) hS'2 hY
  have hbot : ⁅S', Y⁆ = ⊥ := eq_bot_iff.mpr ((le_inf hc1 hc2).trans hinf.le)
  have hYC : Y ≤ Subgroup.centralizer (S' : Set G) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
  have hYS : Y ≤ S' := (le_inf hYH hYC).trans (hchar H hH)
  rw [eq_bot_iff, ← hinf]
  exact le_inf hYS le_rfl

end CFSG.RankThree.PartTwo.Source
