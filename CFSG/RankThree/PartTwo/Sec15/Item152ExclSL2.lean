module

public import CFSG.RankThree.PartTwo.Sec15.Item152StepsExcl
public import CFSG.RankThree.PartTwo.Sec15.Item152ExclSL2Tools
public import CFSG.RankThree.PartTwo.Sec15.Item15Type
public import CFSG.RankThree.PartTwo.Sec14.Item148StepsNHJ
import CFSG.RankThree.PartTwo.Sec14.Item143Proof
import CFSG.RankThree.PartTwo.Sec15.Item15No135
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.KFacts.KS14PGL
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
public import CFSG.Sporadic.J2

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

section CaseB

theorem isoLThreePi_of_mulEquiv' {X X' : Type} [Group X] [Group X'] (e : X ≃* X') {p n : ℕ}
    [Fact p.Prime] (h : Sec4.IsoLThreePi X p n) : Sec4.IsoLThreePi X' p n := by
  rcases h with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  · exact Or.inl ⟨hq, ⟨e.symm.trans φ⟩⟩
  · exact Or.inr ⟨hq, ⟨e.symm.trans φ⟩⟩

theorem three_dvd_card_of_isoLThreePi' {X : Type} [Group X] {p n : ℕ} [Fact p.Prime]
    (hn : n ≠ 0) (h : Sec4.IsoLThreePi X p n) : 3 ∣ Nat.card X := by
  rcases h with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · exact KFacts.three_dvd_card_of_mulEquiv_projSL φ
  · exact KFacts.three_dvd_card_of_mulEquiv_projSU hn φ

theorem false_of_img148_psl2 {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (h148 : Item148 A LB) {Y : Subgroup G} (hY : Y ∈ scriptY A) (hAab : IsMulCommutative A)
    (hHJ : AllPointsHJ A) (hch : Chosen136 A) (hList : KSL2pNotList148) {p : ℕ}
    [Fact p.Prime] (hp5 : 5 < p)
    (he : letI := ker148_normal hY.2
      Nonempty (↥(img148 A Y (deltaZero A LB Y)) ≃* PSL(2, ZMod p))) : False := by
  let := ker148_normal hY.2
  obtain ⟨e⟩ := he
  obtain ⟨hJ, hA5, hA7, hA10, hL37, hL38⟩ := hList p hp5
  set X := img148 A Y (deltaZero A LB Y) with hX
  have hKs : IsSimpleGroup PSL(2, ZMod p) := isSimpleGroup_PSL2 (by omega)
  have hXs : IsSimpleGroup ↥X := e.isSimpleGroup
  have hXnab : ∃ a b : ↥X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := exists_ne_comm_PSL2 (p := p) (by omega)
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hXnt : Nontrivial ↥X := hXs.toNontrivial
  have h3X : 3 ∣ Nat.card ↥X := by
    rw [Nat.card_congr e.toEquiv]
    exact three_dvd_card_PSL2 (by omega)
  have hLHJ : ∀ c' : G, Subgroup.zpowers c' ∈ omegaA A → ∀ L' ∈ lA A c', 3 ∣ Nat.card L' →
      Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) := by
    intro c' hc' L' hL' h3
    obtain ⟨Le, hLe, hJe⟩ := hHJ c' hc'
    rw [(hch.2 c' hc' Le hLe).2 L' hL'.1 h3]
    exact hJe
  rcases (h148 Y hY).2 with h1 | h2 | h3 | h4 | h5 | h6 | h7
  ·
    have hX1 : X = ⊥ := img148_eq_bot_of_le h1
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥X)
    exact hx (Subtype.ext ((Subgroup.mem_bot).mp (hX1 ▸ x.2)))
  ·
    obtain ⟨c', hc', -, L', hL', hcases⟩ := h2
    rcases hcases with hφ | ⟨-, hφ⟩ | ⟨p', f, e', hp', hf, he', hiso', -⟩ | ⟨-, h3A6 | hφ⟩
    ·
      obtain ⟨φ⟩ := hφ
      have h3L : 3 ∣ Nat.card L' := by
        refine h3X.trans ?_
        rw [Nat.card_congr φ.toEquiv]
        exact Subgroup.card_quotient_dvd_card _
      obtain ⟨ψ⟩ := hLHJ c' hc' L' hL' h3L
      exact hJ.false (e.symm.trans (φ.trans ψ))
    ·
      obtain ⟨φ⟩ := hφ
      exact hA7.false (e.symm.trans φ)
    ·
      have hfe : f * e' ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
      have h3L : 3 ∣ Nat.card L' :=
        (three_dvd_card_of_isoLThreePi' hfe hiso').trans (Subgroup.card_quotient_dvd_card _)
      obtain ⟨ψ⟩ := hLHJ c' hc' L' hL' h3L
      exact KFacts.KS14.ks17J2NotList.1 p' (f * e') (isoLThreePi_of_mulEquiv' ψ hiso')
    ·
      exact not_isTripleCover_of_isSimpleGroup hXs hXnab h3A6
    ·
      obtain ⟨φ⟩ := hφ
      exact hA5.false (e.symm.trans φ)
  ·
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h⟩ := h3
    rcases h with hON | hCP | hA6A5 | hφ | hφ | ⟨_, hφ⟩
    · exact not_isTripleCover_of_isSimpleGroup hXs hXnab hON
    · exact not_isCentralProductA6Covers_of_isSimpleGroup hXs hXnab hCP
    · exact not_isA6CoverTimesA5_of_isSimpleGroup hXs hA6A5
    · obtain ⟨φ⟩ := hφ
      exact (isEmpty_mulEquiv_prod_of_isSimpleGroup hXs).false φ
    · obtain ⟨φ⟩ := hφ
      exact hA7.false (e.symm.trans φ)
    · obtain ⟨φ⟩ := hφ
      exact (hL37 _).false (e.symm.trans φ)
  ·
    obtain ⟨⟨φ⟩, -⟩ := h4
    exact hA10.false (e.symm.trans φ)
  ·
    obtain ⟨-, -, -, n, -, -, -, hn, -, hiso, -⟩ := h5
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact hL38 n hn (isoLThreePi_of_mulEquiv' e hiso)
  ·
    obtain ⟨⟨φ⟩, -⟩ := h6
    have : Nontrivial (alternatingGroup (Fin 5)) :=
      alternatingGroup.nontrivial_of_three_le_card (by simp)
    have hne : IsEmpty (↥X ≃* alternatingGroup (Fin 5)) := ⟨fun ψ => hA5.false (e.symm.trans ψ)⟩
    exact (isEmpty_mulEquiv_prod_of_isSimpleGroup' (H₂ := CFSG.Blueprint.NativeSporadic.J2) hXs
      hne).false φ
  ·
    obtain ⟨-, -, L₁, L₂, J₁, J₂, p₁, f₁, -, p₂, f₂, -, -, -, -, -, -, -, hJ₁, hJ₂, hsup, hinf,
      hcomm, -, -, -, -, hZ₁, hZ₂, -, -⟩ := h7
    rw [← hX] at hsup
    have hJ₁le : img148 A Y J₁ ≤ X := hsup ▸ le_sup_left
    have hJ₂le : img148 A Y J₂ ≤ X := hsup ▸ le_sup_right
    have hN : ((img148 A Y J₁).subgroupOf X).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hJ₁le).mpr ?_
      rw [← hsup]
      refine sup_le Subgroup.le_normalizer ?_
      have hC : img148 A Y J₂ ≤ Subgroup.centralizer (img148 A Y J₁ : Set _) := by
        rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
        exact hcomm
      exact hC.trans (Subgroup.centralizer_le_normalizer _)
    have hbot : img148 A Y J₁ = ⊥ ∨ img148 A Y J₂ = ⊥ := by
      rcases hN.eq_bot_or_eq_top with h | h
      · left
        rw [Subgroup.subgroupOf_eq_bot] at h
        exact disjoint_self.mp (h.mono_right hJ₁le)
      · right
        rw [Subgroup.subgroupOf_eq_top] at h
        have := le_inf (hJ₂le.trans h) le_rfl
        rwa [hinf, le_bot_iff] at this
    have hAle : A ≤ Y ⊔ A := le_sup_right
    have key : ∀ J : Subgroup G, J ≤ Y → img148 A Y J = ⊥ →
        ∀ p f : ℕ, IsZ3PGLThreeAt ↥(img148 A Y (J ⊔ A)) p f → False := by
      intro J hJY hJ p f hZ
      rw [img148_sup (hJY.trans le_sup_left) hAle, hJ, bot_sup_eq] at hZ
      obtain ⟨a, b, hab⟩ := KFacts.KS14.ks15Z3PGLNonabelian _ p f hZ
      exact hab (img148_comm hAab a b)
    rcases hbot with h | h
    · exact key J₁ (hJ₁.trans inf_le_right) h p₁ f₁ hZ₁
    · exact key J₂ (hJ₂.trans inf_le_right) h p₂ f₂ hZ₂

end CaseB

section Data

theorem facts_of_step152ExclSL2 {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {Y M X : Subgroup G} (hY : Y ∈ scriptY4 A LB) (hM : M ∈ scriptY2 A)
    (hX : X ∈ thetaComponentsIn M) (hYX : Y ≤ X) :
    A ≤ Subgroup.normalizer (X : Set G) ∧ X = oPrimeResidualOf 3 X ∧ X ∈ scriptY A := by
  have hYp := isPerfect_of_mem_scriptY4 hY
  have hY1 := ne_bot_of_mem_scriptY4 hY
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_of_mem_thetaComponentsIn hM.1.2 hX hYX hYp hY1 hY.1.2
  have hX3 : X = oPrimeResidualOf 3 X :=
    eq_oPrimeResidualOf_of_le (isPerfect_of_mem_thetaComponentsIn hX)
      (isQuasisimple_theta_of_mem_thetaComponentsIn hX) hYX hY.2.1 hYp hY1
  have hXM : X ≤ M := le_of_mem_thetaComponentsIn hX
  have hXtop : X ≠ ⊤ := fun h => hM.1.1 (top_le_iff.mp (h ▸ hXM))
  exact ⟨hAX, hX3, hXtop, hAX⟩

end Data

section CaseA

theorem step152ExclSL2_nhj (h134 : Item134) (h48 : Sec4.Item4_8) (hAut : KSL2pAutThree)
    {A L : Subgroup G} {c : G} (h : Sec15R G A c L) (hNHJ : ¬ AllPointsHJ A) :
    Step152ExclSL2 A (lB A) := by
  intro Y hY M hM hYM hF X hX hYX hΔ p hp hp5 he
  exfalso
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := he
  obtain ⟨hAX, -, -⟩ := facts_of_step152ExclSL2 hY hM hX hYX
  set N := Sec4.oTwoP p ↥X with hN
  have : N.Characteristic := oTwoP_characteristic p
  obtain ⟨B, hB, hB3, hBX⟩ :=
    exists_hyperplane_of_kSL2pAutThree hAut h.isElemAbelian h.card_eq hAX hp5 N e
  have hLB : lB A B = ⊥ := lB_eq_bot_of_not_allPointsHJ' h134 h48 h.toSec14Std hNHJ hB
  have hN3 : ¬ 3 ∣ Nat.card (N.map X.subtype) := by
    rw [Subgroup.card_map_of_injective X.subtype_injective]
    exact (isPiSubgroup_piCompl_iff Nat.prime_three N).mp
      (isPiSubgroup_oTwoP hp (by omega))
  have hXN : X ≤ Subgroup.normalizer ((N.map X.subtype : Subgroup G) : Set G) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le N)).mp ?_
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
    infer_instance
  have hX3 := threePrime_of_qGen hΔ hB hB3 hLB hXN hN3 hBX
  have h3X : 3 ∣ Nat.card X :=
    (three_dvd_card_SL2 (p := p) (by omega)).trans
      (Subgroup.card_dvd_of_surjective (f := e.toMonoidHom.comp (QuotientGroup.mk' N))
        (e.surjective.comp (QuotientGroup.mk'_surjective N)))
  exact hX3 h3X

end CaseA

section CaseB'

theorem step152ExclSL2_hj (h134 : Item134) (h48 : Sec4.Item4_8) (h148 : Item148HJS14)
    (hList : KSL2pNotList148) {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (hHJ : AllPointsHJ A) : Step152ExclSL2 A (lB A) := by
  intro Y hY M hM hYM hF X hX hYX hΔ p hp hp5 he
  exfalso
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := he
  obtain ⟨hAX, hX3, hXY⟩ := facts_of_step152ExclSL2 hY hM hX hYX
  have hΔ0 : X = deltaZero A (lB A) X :=
    eq_deltaZero_of_eq_delta' h134 CFSG.Sporadic.J2.isSimpleGroup_J2 h48
      Sec4.Sporadic.rank3II_4_15 (KFacts.KS14.center_nativeJ2_eq_bot Sec4.Sporadic.rank3II_4_15)
      h.toSec14Std hAX hX3 hΔ
  have he' : letI := ker148_normal hXY.2
      Nonempty (↥(img148 A X (deltaZero A (lB A) X)) ≃* PSL(2, ZMod p)) := by
    let := ker148_normal hXY.2
    rw [← hΔ0]
    obtain ⟨φ⟩ := nonempty_img148_equiv hAX
    obtain ⟨ψ⟩ := nonempty_quotient_pPrimeCore_equiv_psl hp5 e
    exact ⟨φ.trans ψ⟩
  exact false_of_img148_psl2 (h148 G A c L h.toSec14Std hHJ) hXY h.isElemAbelian.1 hHJ
    h.chosen136 hList hp5 he'

theorem step152ExclSL2_at (h134 : Item134) (h48 : Sec4.Item4_8) (h148 : Item148HJS14)
    (hAut : KSL2pAutThree) (hList : KSL2pNotList148) {A L : Subgroup G} {c : G}
    (h : Sec15R G A c L) : Step152ExclSL2 A (lB A) := by
  by_cases hHJ : AllPointsHJ A
  · exact step152ExclSL2_hj h134 h48 h148 hList h hHJ
  · exact step152ExclSL2_nhj h134 h48 hAut h hHJ

theorem step152ExclSL2_of (h134 : Item134) (h48 : Sec4.Item4_8) (h148 : Item148HJS14)
    (hAut : KSL2pAutThree) (hList : KSL2pNotList148) : Step152ExclSL2R :=
  fun _ _ _ _ _ _ h => step152ExclSL2_at h134 h48 h148 hAut hList h

end CaseB'

end CFSG.RankThree.PartTwo.Sec15
