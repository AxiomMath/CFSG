module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cent361
import CFSG.RankThree.PartTwo.Sec15.Gagen1511WStar
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofPoints
import CFSG.RankThree.PartTwo.Sec15.Liebeck1515Img
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsQuot
public import CFSG.RankThree.PartTwo.Sec15.Item153Claims
public import CFSG.RankThree.PartTwo.Sec15.Item15Type

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem res1340_card_le_card_img148 {A Y L : Subgroup G} [(ker148 A Y).Normal]
    (hLY : L ≤ Y ⊔ A) (hsimple : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (h3 : 3 ∣ Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
    Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) ≤ Nat.card (img148 A Y L) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (aschbacherSolvableCore 3 ↥L).Normal := Subgroup.normal_of_characteristic _
  set f : ↥L →* ↥(Y ⊔ A) ⧸ ker148 A Y :=
    (QuotientGroup.mk' (ker148 A Y)).comp (Subgroup.inclusion hLY) with hf
  have hker : f.ker ≤ aschbacherSolvableCore 3 ↥L := by
    haveI hn : (f.ker.map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))).Normal :=
      f.normal_ker.map _ (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (f.ker.map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) with hb | ht
    · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hb
      exact hb
    · exfalso
      have himg : f.ker.map L.subtype ≤ pPrimeCoreOf 3 Y := by
        rintro _ ⟨l, hl, rfl⟩
        exact mk'_ker148_eq_one_iff.mp hl
      have hk3 : Nat.Coprime 3 (Nat.card f.ker) := by
        have h := (coprime_card_pPrimeCoreOf 3 Y).coprime_dvd_right
          (Subgroup.card_dvd_of_le himg)
        rwa [Subgroup.card_map_of_injective L.subtype_injective] at h
      have hdvd : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∣ Nat.card f.ker := by
        have h1 := Subgroup.card_map_dvd f.ker (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))
        rwa [ht, Subgroup.card_top] at h1
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hk3 (h3.trans hdvd)
  have hrange : f.range ≤ img148 A Y L := by
    rintro _ ⟨l, rfl⟩
    exact mem_img148_iff.mpr ⟨l, hLY l.2, l.2, rfl⟩
  calc Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = (aschbacherSolvableCore 3 ↥L).index := rfl
    _ ≤ f.ker.index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Subgroup.index_dvd_of_le hker)
    _ = Nat.card f.range := Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    _ ≤ Nat.card (img148 A Y L) := Subgroup.card_le_of_le hrange

theorem res1340_le_sup_of_card_img148_le {A Y L D : Subgroup G} [(ker148 A Y).Normal]
    (hLD : L ≤ D) (hDY : D ≤ Y ⊔ A)
    (hsimple : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (h3 : 3 ∣ Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hcard : Nat.card (img148 A Y D) ≤ Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
    D ≤ L ⊔ pPrimeCoreOf 3 Y := by
  have heq : img148 A Y L = img148 A Y D :=
    Subgroup.eq_of_le_of_card_ge (Liebeck1515.img148_mono hLD)
      (hcard.trans (res1340_card_le_card_img148 (hLD.trans hDY) hsimple h3))
  intro d hd
  have hdα : QuotientGroup.mk' (ker148 A Y) ⟨d, hDY hd⟩ ∈ img148 A Y L := by
    rw [heq]
    exact mem_img148_iff.mpr ⟨d, hDY hd, hd, rfl⟩
  obtain ⟨g, hg, hgL, hgd⟩ := mem_img148_iff.mp hdα
  have h1 : g⁻¹ * d ∈ pPrimeCoreOf 3 Y := by
    have h : QuotientGroup.mk' (ker148 A Y) ((⟨g, hg⟩ : ↥(Y ⊔ A))⁻¹ * ⟨d, hDY hd⟩) = 1 := by
      rw [map_mul, map_inv, hgd, inv_mul_cancel]
    exact mk'_ker148_eq_one_iff.mp h
  have e : d = g * (g⁻¹ * d) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hgL h1

section Types

private theorem res1340_card {X : Type} [Group X]
    (hQ : Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) :
    Nat.card X = 2520 ∨ Nat.card X = 443520 := by
  rcases hQ with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · left
    rw [Nat.card_congr e.toEquiv]
    exact KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1
  · right
    rw [Nat.card_congr e.toEquiv]
    exact KFacts.KS14.card_nativeM22

private theorem res1340_not_isoLThreePi {X : Type} [Group X]
    (hQ : Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) (p e : ℕ) [Fact p.Prime] :
    ¬ Sec4.IsoLThreePi X p e := by
  rcases res1340_card hQ with h | h
  · exact Proof1514.not_isoLThreePi_of_card_2520 h p e
  · exact KFacts.KS14.not_isoLThreePi_of_card h
      (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) KFacts.KS14.checkSL_m22)
      (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) KFacts.KS14.checkSU_m22) p e

private theorem res1340_not_isLThreeEpsAt {X : Type} [Group X]
    (hQ : Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) (p f : ℕ) [Fact p.Prime] :
    ¬ IsLThreeEpsAt X p f := by
  rcases res1340_card hQ with h | h
  · exact KFacts.KS14.not_isLThreeEpsAt_of_card h
      (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) Proof1514.checkSL_a7)
      (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) Proof1514.checkSU_a7) p f
  · exact KFacts.KS14.not_isLThreeEpsAt_of_card h
      (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) KFacts.KS14.checkSL_m22)
      (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) KFacts.KS14.checkSU_m22) p f

private theorem res1340_not_j2 {X : Type} [Group X]
    (hQ : Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) :
    ¬ Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  rintro ⟨e⟩
  have h := Nat.card_congr e.toEquiv
  rw [KFacts.KS14.card_nativeJ2] at h
  rcases res1340_card hQ with h' | h' <;> omega

end Types

namespace Res1Tau

variable {Q : ∀ (X : Type) [Group X], Prop} {P : ∀ (Y : Type) [Group Y], Prop}
  {A : Subgroup G} {c : G} {L X K Y M T P' : Subgroup G} {Yc : Subgroup (Res1Q A L)} {z : G}

private theorem res1340_mem_m {M' : Subgroup G} (hC' : Ctx155 A X K Y M' T) :
    M' ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) := by
  rw [sup_comm]
  exact hC'.mem_m

theorem le_oPrimeResidualOf_delta_of_competing (τ : Res1Tau Q P A c L X K Y M T P' Yc z)
    {M' : Subgroup G} (hC' : Ctx155 A X K Y M' T) :
    X ≤ oPrimeResidualOf 3 (delta A (lB A) M') := by
  have hX4 : X ∈ scriptY4 A (lB A) := τ.ctx.res ▸ τ.ctx.isY.2.1
  have hXY : X ≤ Y := τ.ctx.res ▸ Sec14.oPrimeResidualOf_le_self 3 Y
  have hYM : Y ≤ M' := le_sup_right.trans (SetLike.coe_subset_coe.mp hC'.mem_m.2)
  exact le_oPrimeResidualOf_delta hX4 (hXY.trans hYM)

theorem oPrimeResidualOf_delta_le_of_competing (τ : Res1Tau Q P A c L X K Y M T P' Yc z)
    (h149 : Item149 A (lB A)) {M' : Subgroup G} (hC' : Ctx155 A X K Y M' T) :
    oPrimeResidualOf 3 (delta A (lB A) M') ≤ deltaZero A (lB A) M' ∧
      M' ≤ Subgroup.normalizer (oPrimeResidualOf 3 (delta A (lB A) M') : Set G) := by
  obtain ⟨-, -, hM2, -⟩ := facts_of_mem_maximalTwoLocalsContaining τ.std (res1340_mem_m hC')
  obtain ⟨heq, hn, -⟩ := h149 M' hM2.1
  rw [← heq] at hn
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact (Sec14.oPrimeResidualOf_le_self 3 _).trans (Sec14.inSubgroup_oResidual_le_self 2 _)
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      ((Sec14.oPrimeResidualOf_le_self 3 _).trans (delta_le M'))).mp hn

theorem deltaZero_le_sup_of_competing
    (τ : Res1Tau Q P A c L X K Y M T P' Yc z)
    (hQ : ∀ (X : Type) [Group X], Q X →
      Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22))
    (hQE9 : Res1QE9 Q) (h148 : Item148 A (lB A)) (h149 : Item149 A (lB A))
    {M' : Subgroup G} (hC' : Ctx155 A X K Y M' T) :
    deltaZero A (lB A) M' ≤ L ⊔ pPrimeCoreOf 3 M' := by
  have hL := hQ _ τ.q
  have hsimple := (hQE9 _ τ.q).1
  have h3 : 3 ∣ Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
    rcases res1340_card hL with hc | hc <;> rw [hc] <;> norm_num
  have h3L : 3 ∣ Nat.card L := Proof1515.three_dvd_card_of_thetaQuot h3
  have hpt : ∀ {c' : G} {L' : Subgroup G}, Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      L' = L := by
    intro c' L' hc' hL'
    rw [τ.omega] at hc'
    exact Proof1515.eq_of_mem_lA_of_zpowers_eq τ.std h3L (Set.mem_singleton_iff.mp hc') hL'
  have hQ' : ∀ {c' : G} {L' : Subgroup G}, Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M22) := by
    intro c' L' hc' hL'
    rw [hpt hc' hL']
    exact hL
  obtain ⟨-, -, hM2, -⟩ := facts_of_mem_maximalTwoLocalsContaining τ.std (res1340_mem_m hC')
  let : (ker148 A M').Normal := ker148_normal hM2.1.2
  have hLD : L ≤ deltaZero A (lB A) M' :=
    τ.l_le.trans ((τ.le_oPrimeResidualOf_delta_of_competing hC').trans
      (τ.oPrimeResidualOf_delta_le_of_competing h149 hC').1)
  have hDM : deltaZero A (lB A) M' ≤ M' ⊔ A := (deltaZero_le M').trans le_sup_left
  refine res1340_le_sup_of_card_img148_le hLD hDM hsimple h3 ?_
  have hD0 := τ.sec15.toSec13Data
  rcases (h148 M' hM2.1).2 with h1 | h2 | h3' | h4 | h5 | h6 | h7
  ·
    rw [img148_eq_bot_of_le h1, Subgroup.card_bot]
    exact Nat.card_pos
  ·
    obtain ⟨c', hc', -, L', hL', hcases⟩ := h2
    rcases hcases with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨p, f, e, hp, -, -, hiso, -⟩ | ⟨⟨φ⟩, -⟩
    · rw [Nat.card_congr φ.toEquiv, hpt hc' hL']
    · rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
      rcases res1340_card hL with hc | hc <;> rw [hc] <;> norm_num
    · exact (res1340_not_isoLThreePi (hQ' hc' hL') p (f * e) hiso).elim
    · exact (res1340_not_j2 (hQ' hc' hL') ⟨φ⟩).elim
  ·
    obtain ⟨c', d, L', hc', hL', ⟨φ⟩, -⟩ := h3'
    exact (res1340_not_j2 (hQ' hc' hL') ⟨φ⟩).elim
  ·
    obtain ⟨-, -, hW⟩ := h4
    exact (Proof1511Point.not_wStarS4_of_le_normalizer τ.sec15.isE27 hD0.mem_A hD0.ne_one
      τ.norm hW).elim
  ·
    obtain ⟨c', -, L', n, m, hc', hL', -, -, -, -, -, -, hε, -⟩ := h5
    exact (res1340_not_isLThreeEpsAt (hQ' hc' hL') 2 (n * m) hε).elim
  ·
    obtain ⟨-, ⟨c', L', hc', hL', ⟨φ⟩⟩, -⟩ := h6
    exact (res1340_not_j2 (hQ' hc' hL') ⟨φ⟩).elim
  ·
    obtain ⟨a₁, a₂, L₁, L₂, J₁, J₂, p₁, f₁, e₁, p₂, f₂, e₂, hp₁, hp₂, hΩ₁, -, hL₁, -, -, -, -,
      -, -, -, -, -, -, -, -, hiso, -⟩ := h7
    have := hp₁
    exact (res1340_not_isoLThreePi (hQ' hΩ₁ hL₁) p₁ (f₁ * e₁) hiso).elim

theorem oPrimeResidualOf_delta_le_sup_commutator_of_le (τ : Res1Tau Q P A c L X K Y M T P' Yc z)
    (h149 : Item149 A (lB A)) {M' : Subgroup G} (hC' : Ctx155 A X K Y M' T)
    (h3 : deltaZero A (lB A) M' ≤ L ⊔ pPrimeCoreOf 3 M') :
    oPrimeResidualOf 3 (delta A (lB A) M') ≤ L ⊔ ⁅L, pPrimeCoreOf 3 M'⁆ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE' : oPrimeResidualOf 3 (delta A (lB A) M') ≤ L ⊔ pPrimeCoreOf 3 M' :=
    (τ.oPrimeResidualOf_delta_le_of_competing h149 hC').1.trans h3
  rw [Sec14.oPrimeResidualOf_eq_closure, Subgroup.closure_le]
  rintro y ⟨hy, k, hk⟩
  have hyE : y ∈ oPrimeResidualOf 3 (delta A (lB A) M') := by
    rw [Sec14.oPrimeResidualOf_eq_closure]
    exact Subgroup.subset_closure ⟨hy, k, hk⟩
  have hle : L ⊔ pPrimeCoreOf 3 M' ≤ (L ⊔ ⁅L, pPrimeCoreOf 3 M'⁆) ⊔ pPrimeCoreOf 3 M' :=
    sup_le_sup_right le_sup_left _
  exact Sec14.mem_left_of_pow_prime_pow Nat.prime_three
    (Sec14.le_normalizer_sup_commutator L _) (coprime_card_pPrimeCoreOf 3 M') (hle (hE' hyE)) hk

end Res1Tau

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
