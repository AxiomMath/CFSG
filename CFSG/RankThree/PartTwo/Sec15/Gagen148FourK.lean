module

public import CFSG.RankThree.PartTwo.Sec15.ThmDDefs
import CFSG.RankThree.PartTwo.Sec14.Item148ProofNHJ
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec14.Ronan148KTypes
import CFSG.RankThree.PartTwo.Sec14.Item148RankProofTenTools
import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofCases
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
public import CFSG.RankThree.PartTwo.Sec14.Item145BotNo135
public import CFSG.RankThree.PartTwo.Sec15.Item15Type
public import CFSG.Sporadic.J2

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof148FourK

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem not_type148_of_card_a10 {X : Type} [Group X] (hX : Nat.card X = 1814400) :
    ¬ Type148 X := by
  have hSL := KFacts.KS14.forall_of_forall_lt (N := 1814400) (B := 122) (by norm_num)
    (by norm_num) (P := fun q => 1814400 * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)))
    (by decide +kernel)
  have hSU := KFacts.KS14.forall_of_forall_lt (N := 1814400) (B := 122) (by norm_num)
    (by norm_num) (P := fun q => 1814400 * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)))
    (by decide +kernel)
  obtain ⟨-, h7, -⟩ := KFacts.KS14.card_alternatingGroup_five_seven_ten
  rintro (⟨p, e, _, -, h⟩ | ⟨p, f, _, -, -, h⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩)
  · exact KFacts.KS14.not_isoLThreePi_of_card hX hSL hSU p e h
  · exact KFacts.KS14.not_isLThreeEpsAt_of_card hX hSL hSU p f h
  · have h := Nat.card_congr φ.toEquiv
    rw [hX, h7] at h
    norm_num at h
  · have h := Nat.card_congr φ.toEquiv
    rw [hX, KFacts.KS14.card_nativeM12] at h
    norm_num at h
  · have h := Nat.card_congr φ.toEquiv
    rw [hX, KFacts.KS14.card_nativeM22] at h
    norm_num at h
  · have h := Nat.card_congr φ.toEquiv
    rw [hX, KFacts.KS14.card_nativeJ2] at h
    norm_num at h

theorem not_allPointsHJ_of_a7 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {c' : G}
    {L' : Subgroup G} (hc' : Subgroup.zpowers c' ∈ omegaA A) (hL' : L' ∈ lA A c')
    (h7 : Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* alternatingGroup (Fin 7))) :
    ¬ AllPointsHJ A := by
  intro hHJ
  obtain ⟨Le, hLe, ⟨φ⟩⟩ := hHJ c' hc'
  have h3 : 3 ∣ Nat.card Le := by
    have hc := Nat.card_congr φ.toEquiv
    rw [KFacts.KS14.card_nativeJ2] at hc
    have hdvd := Subgroup.card_quotient_dvd_card (aschbacherSolvableCore 3 ↥Le)
    rw [hc] at hdvd
    exact (by norm_num : (3 : ℕ) ∣ 604800).trans hdvd
  have hLeL : Le = L' := (h.chosen136.2 c' hc' L' hL').2 Le hLe.1 h3
  subst hLeL
  obtain ⟨ψ⟩ := h7
  exact KFacts.KS14.isEmpty_mulEquiv_j2_alternating.2.1.false (φ.symm.trans ψ)

omit [Finite G] in
theorem img148_eq_of_mem_thetaComponentsIn {A Y : Subgroup G} [(ker148 A Y).Normal]
    (hsY : IsSimpleGroup ↥(img148 A Y Y)) {J : Subgroup G} (hJ : J ∈ thetaComponentsIn Y)
    (hJ1 : img148 A Y J ≠ ⊥) : img148 A Y J = img148 A Y Y := by
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hsn : (J.subgroupOf Y).IsSubnormal := ((mem_thetaComponentsIn_iff.mp hJ).2).2.1
  have hle : img148 A Y J ≤ img148 A Y Y := img148_mono hJY
  rcases (Item148Rank.isSubnormal_img148_subgroupOf148 le_sup_left hJY hsn
      le_rfl).eq_bot_or_top_of_isSimpleGroup hsY with hb | ht
  · exact absurd ((Subgroup.subgroupOf_eq_bot.mp hb).eq_bot_of_le hle) hJ1
  · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp ht)

section Certs


theorem print148FourK_of_steps (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (hCore : Step148Core) (hPoint : Step148Point) (hKT : Step148KType) (hLift : Step148Lift)
    (hD4 : Step148D4) {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {Y : Subgroup G}
    (hY0 : Y ∈ scriptY0 A (lB A))
    (h10 : Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* alternatingGroup (Fin 10)))
    {c' : G} {L' : Subgroup G} (hc' : Subgroup.zpowers c' ∈ omegaA A) (hL' : L' ∈ lA A c')
    (h7 : Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* alternatingGroup (Fin 7))) :
    ThmD.Print148FourK A Y := by
  obtain ⟨ψ⟩ := h10
  have hY : Y ∈ scriptY A := hY0.1.1
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
  letI := ker148_normal hAY
  have h5 : 5 ≤ Nat.card (Fin 10) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num
  have : IsSimpleGroup (alternatingGroup (Fin 10)) := alternatingGroup.isSimpleGroup h5
  have hcard10 : Nat.card (alternatingGroup (Fin 10)) = 1814400 :=
    KFacts.KS14.card_alternatingGroup_five_seven_ten.2.2
  obtain ⟨χ⟩ := nonempty_img148_equiv hAY
  have hsY : IsSimpleGroup ↥(img148 A Y Y) := (χ.trans ψ).isSimpleGroup
  have hcY : Nat.card ↥(img148 A Y Y) = 1814400 := by
    rw [Nat.card_congr (χ.trans ψ).toEquiv, hcard10]
  have hs : ¬ Group.IsSolvable ↥Y := by
    intro hsol
    have hsol10 : Group.IsSolvable (alternatingGroup (Fin 10)) :=
      Group.isSolvable_of_surjective (f := ψ.toMonoidHom.comp (QuotientGroup.mk' _))
        (ψ.surjective.comp (QuotientGroup.mk'_surjective _))
    have : Group.IsPerfect (alternatingGroup (Fin 10)) := ⟨commutator_alternatingGroup_eq_top h5⟩
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 10)) hsol10
  have hNHJ : ¬ AllPointsHJ A := not_allPointsHJ_of_a7 h hc' hL' h7
  have hYB : ∀ B : Subgroup G, IsHyperplane A B → YBOne A (lB A) Y B := fun B hB =>
    yBOne_of_lB_eq_bot h.isElemAbelian.1 hB (lB_eq_bot_of_not_allPointsHJ h134
      CFSG.Sporadic.J2.isSimpleGroup_J2 h48 h415 (KFacts.KS14.center_nativeJ2_eq_bot h415) h
      hNHJ hB)
  by_cases hcore : ∀ B : Subgroup G, IsHyperplane A B → ∀ Q ∈ scriptQZero A (lB A),
      Q ≤ Y ⊓ Subgroup.centralizer (B : Set G) →
      ∀ b ∈ B, b ≠ 1 → Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G))
  · exfalso
    have h1 : deltaZero A (lB A) Y ≤ pPrimeCoreOf 3 Y := case148One_of_core hCore h hY hs hYB hcore
    have hYΔ : Y = deltaZero A (lB A) Y := rank3II_15_1_of' h134 CFSG.Sporadic.J2.isSimpleGroup_J2
      h48 h415 (KFacts.KS14.center_nativeJ2_eq_bot h415) h hY0.1
    have hle : Y ≤ pPrimeCoreOf 3 Y := hYΔ.le.trans h1
    have htop : CFSG.pPrimeCore 3 ↥Y = ⊤ := by
      rw [eq_top_iff]
      intro y _
      obtain ⟨z, hz, hzy⟩ := hle y.2
      rwa [show z = y from Subtype.ext hzy] at hz
    have hidx : (CFSG.pPrimeCore 3 ↥Y).index = 1814400 := by
      rw [← hcard10]
      exact Nat.card_congr ψ.toEquiv
    rw [htop, Subgroup.index_top] at hidx
    norm_num at hidx
  push Not at hcore
  obtain ⟨B, hB, Q, hQ, hQY, b, hb, hb1, hQb⟩ := hcore
  obtain ⟨e, K, Le, hP⟩ := hPoint G A c L h Y hY hs hYB B hB Q hQ hQY b hb hb1 hQb
  have hkt : KType148 A Y e K Le := hKT G A c L h Y hY hs hYB B Q e K Le hP
  obtain ⟨-, -, -, heB, he1, hK, hKΔ, -, -, hpt⟩ := id hP
  have heA : e ∈ A := hB.1 heB
  have ht : Type148 ↥(img148 A Y K) := type148_of_kType148 h.chosen136 hkt
  obtain ⟨J, hJ, hKJ, hAJ, halt⟩ := hLift G A c L h Y hY hs e heA he1 K hK
    (le_normalizer_of_eq_deltaZero hKΔ) hkt.1 ht
  have hK1 : img148 A Y K ≠ ⊥ := by
    intro hbot
    have h3 := Ronan148K.three_dvd_card_of_type148 ht
    rw [hbot, Subgroup.card_bot] at h3
    norm_num at h3
  have hJeq : img148 A Y J = img148 A Y Y :=
    img148_eq_of_mem_thetaComponentsIn hsY hJ fun hbot =>
      hK1 (le_bot_iff.mp ((img148_mono hKJ).trans hbot.le))
  have hKle : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) := le_of_mem_thetaComponentsIn hK
  rcases halt with heq | ⟨⟨φ⟩, -⟩ | ⟨n, hn, -, hJ3, -⟩ | h4
  ·
    have heq' : img148 A Y K = img148 A Y J := heq
    exfalso
    refine not_type148_of_card_a10 ?_ ht
    rw [heq', hJeq, hcY]
  ·
    have heΩ : Subgroup.zpowers e ∈ omegaA A := by
      rcases hpt with ⟨heΩ, -⟩ | ⟨c'', L'', hc'', -, hL'', hJ2, hdc, -⟩
      · exact heΩ
      · exact (hNHJ fun e' he' => exists_hj_of_hj_point h134 h48 h415 h hc'' hL'' hJ2 heA he1
          hdc he').elim
    obtain ⟨μ⟩ := Y4Core.nonempty_img148_equiv_map hAY (hKle.trans inf_le_left)
    exact ⟨e, heA, heΩ, K, hKle, ⟨μ.symm.trans φ⟩⟩
  ·
    have hJt : Type148 ↥(img148 A Y J) := Or.inl ⟨2, 3 * n, inferInstance, by omega, hJ3⟩
    exfalso
    refine not_type148_of_card_a10 ?_ hJt
    rw [hJeq, hcY]
  ·
    exact (hD4 G A c L h Y hY hs hYB B Q e K Le hP hkt heA J hJ hKJ hAJ h4).elim

theorem step148FourKFact_of_steps (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (hCore : Step148Core) (hPoint : Step148Point) (hKT : Step148KType) (hLift : Step148Lift)
    (hD4 : Step148D4) : ThmD.Step148FourKFact := by
  intro G _ _ A c L hR Y hY0 h10 ⟨c', L', hc', hL', h7⟩ _
  exact print148FourK_of_steps h134 h48 h415 hCore hPoint hKT hLift hD4 hR.toSec14Std hY0 h10 hc'
    hL' h7

end Certs

end CFSG.RankThree.PartTwo.Sec15.Proof148FourK
