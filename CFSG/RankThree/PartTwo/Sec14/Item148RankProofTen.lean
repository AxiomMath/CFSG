module

public import CFSG.RankThree.PartTwo.Sec14.Item148StepRank
public import CFSG.RankThree.PartTwo.Sec14.Item148RankProofTenTools
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.Sporadic.J2
import CFSG.Models.PGLOrders

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

section Steps

@[expose] def Step148RankTenRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      Ind148 A (lB A) Y → (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      (letI := ker148_normal hY.2; KType148 A Y e K Le) →
      ∀ (_he : e ∈ A) (J : Subgroup G), J ∈ thetaComponentsIn Y → K ≤ J →
        A ≤ Subgroup.normalizer (J : Set G) →
        (letI := ker148_normal hY.2; Lift148Ten A Y K J) →
        A = Subgroup.zpowers e ⊔ (A ⊓ J) →
        (letI := ker148_normal hY.2; img148 A Y (deltaZero A (lB A) Y) = img148 A Y J) →
        (Sec4.IsTripleCover (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) CFSG.Blueprint.NativeSporadic.ON ∨
          (Subgroup.zpowers e ∈ omegaA A ∧ Le ∈ lA A e ∧
            ((∃ _ : Fact (Nat.Prime 5), Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃*
                CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 5 2))) ∨
              (∃ _ : Fact (Nat.Prime 5), Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃*
                CFSG.Assembly.RankThreeEven.projSU 3 5 1))) ∧
            Sec8.IsZ3PGLThreePi (lBarA e Le A))) →
        (∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
          Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* alternatingGroup (Fin 7))) ∧
        (Nonempty (wStar A ≃* Equiv.Perm (Fin 4)) ∨
          Nonempty (wStar A ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))

end Steps

namespace Item148Rank

variable {G : Type} [Group G] [Finite G]

theorem not_isoLThreePi_of_card_2520 {X : Type} [Group X] (hX : Nat.card X = 2520) (p e : ℕ)
    [Fact p.Prime] : ¬ Sec4.IsoLThreePi X p e :=
  KFacts.KS14.not_isoLThreePi_of_card hX
    (KFacts.KS14.forall_of_forall_lt (B := 14) (by norm_num) (by norm_num) (by decide))
    (KFacts.KS14.forall_of_forall_lt (B := 14) (by norm_num) (by norm_num) (by decide)) p e

theorem not_isLThreeEpsAt_of_card_2520 {X : Type} [Group X] (hX : Nat.card X = 2520)
    (p f : ℕ) [Fact p.Prime] : ¬ IsLThreeEpsAt X p f :=
  KFacts.KS14.not_isLThreeEpsAt_of_card hX
    (KFacts.KS14.forall_of_forall_lt (B := 14) (by norm_num) (by norm_num) (by decide))
    (KFacts.KS14.forall_of_forall_lt (B := 14) (by norm_num) (by norm_num) (by decide)) p f

theorem not_isoLThreePi_of_card_443520 {X : Type} [Group X] (hX : Nat.card X = 443520)
    (p e : ℕ) [Fact p.Prime] : ¬ Sec4.IsoLThreePi X p e :=
  KFacts.KS14.not_isoLThreePi_of_card hX
    (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) KFacts.KS14.checkSL_m22)
    (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) KFacts.KS14.checkSU_m22) p e

theorem card_a7_148 : Nat.card (alternatingGroup (Fin 7)) = 2520 :=
  KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1

theorem card_projSU_three_five148 [Fact (Nat.Prime 5)] :
    Nat.card (CFSG.Assembly.RankThreeEven.projSU 3 5 1) = 126000 :=
  CFSG.PGLModel.card_projSU_three_five

theorem card_projSL_three_twentyfive148 [Fact (Nat.Prime 5)] :
    Nat.card (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 5 2)) = 50778000000 := by
  have h := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 5 2)
  rw [GaloisField.card 5 2 (by norm_num)] at h
  norm_num at h
  omega

theorem cases133_of_irreducible148 (h133 : Item133)
    {A : Subgroup G} {e : G} {Le : Subgroup G} (hD : Sec13Data G A e Le)
    (hS : HypS A ∨ HypT A) (hirr : Sec21.IsIrreducibleOn (wStar A)) :
    ((Nonempty (wStar A ≃* Equiv.Perm (Fin 4)) ∨
        Nonempty (wStar A ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) ∧
        Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* alternatingGroup (Fin 7))) ∨
      Sec8.IsZ3PGLThreePi (lBarA e Le A) ∨
      Nat.card (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) ∣ 3 * 95040 ∨
      Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  have hA27 : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA27.1.2
  obtain ⟨heA, hc3, -⟩ := zpowers_mem_omegaA_iff.mp hD.zpowers_mem_omegaA
  rcases h133 G A e Le hD hS with h1 | ⟨hW, ⟨φ⟩, -⟩ | ⟨-, -, -, h9, -⟩ | hPGL | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  ·
    exfalso
    refine false_of_isIrreducibleOn_wStar148 hirr (Subgroup.zpowers_le.mpr heA) ?_ ?_ h1
    · intro hb
      rw [hb, Subgroup.card_bot] at hc3
      norm_num at hc3
    · intro h
      have hc := hA27.2
      rw [← h, hc3] at hc
      norm_num at hc
  ·
    left
    have hA7s : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    have hA7p := (isPerfect_center_of_isSimpleGroup hA7s (by rw [card_a7_148]; norm_num)).1
    exact ⟨hW, nonempty_thetaQuot_equiv hD hA7p φ⟩
  ·
    exfalso
    refine false_of_isIrreducibleOn_wStar_of_oThree148 hirr ?_ ?_ h9
    · exact isPGroup_three_of_pow148 hA3
    · rw [hA27.2]
      norm_num
  · exact Or.inr (Or.inl hPGL)
  ·
    right; right; left
    obtain ⟨η, -⟩ := exists_lBarEquiv hD.mem_thetaComponentsAt
    rw [Nat.card_congr η.toEquiv]
    have h1 := Subgroup.card_dvd_of_le (lBar_le_lBarA (c := e) (L := Le) (A := A))
    rw [Nat.card_congr φ.toEquiv, Nat.card_prod, KFacts.KS14.card_nativeM12] at h1
    simpa [Nat.card_eq_fintype_card] using h1
  ·
    right; right; right
    have hJ2p := (isPerfect_center_of_isSimpleGroup CFSG.Sporadic.J2.isSimpleGroup_J2
      (by rw [KFacts.KS14.card_nativeJ2]; norm_num)).1
    exact nonempty_thetaQuot_equiv hD hJ2p φ

end Item148Rank

open Item148Rank

theorem step148RankTen_of
    (h133 : Item133) (hRest : Step148RankTenRest) : Step148RankTen := by
  intro G _ _ A c L hstd Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hTen hA hXJ
  have := ker148_normal hY.2
  have hAF : A ∈ partTwoF G := hstd.mem_partTwoF
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
  have hA27 : Late.IsE27 A := Late.isE27_of_mem_partTwoE hstd.toSec13Data.mem_partTwoE
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({e} : Set G)) := hP.2.2.2.2.2.1
  have hle : img148 A Y A ≤ img148 A Y J :=
    img148_le_of_lift148Ten148 hAF hAY he hK hKJ hJY hAJ hkt.1 hTen
  have hirr : Sec21.IsIrreducibleOn (wStar A) :=
    isIrreducibleOn_wStar148 hA27 hle hTen.2
  obtain ⟨⟨φK⟩, -⟩ := id hTen
  have hcK : Nat.card ↥(img148 A Y K) = 2520 := by
    rw [Nat.card_congr φK.toEquiv, card_a7_148]
  rcases hkt.2 with ⟨heΩ, hLeA, htype⟩ | ⟨hON, -⟩
  swap
  · exact hRest G A c L hstd Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hTen
      hA hXJ (Or.inl hON)
  have hD : Sec13Data G A e Le :=
    { hstd.toSec13Data with zpowers_mem_omegaA := heΩ, mem_lA := hLeA }
  have h13 := cases133_of_irreducible148 h133 hD hstd.hypS_or_hypT hirr
  rcases htype with ⟨⟨ψ⟩⟩ | ⟨hT2, -⟩ | ⟨p, f, e', hp, -, -, -, hKeps⟩
  ·
    have hL7 : Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* alternatingGroup (Fin 7)) :=
      ⟨ψ.symm.trans φK⟩
    have hcL : Nat.card (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) = 2520 := by
      rw [← Nat.card_congr ψ.toEquiv, hcK]
    rcases h13 with ⟨hW, -⟩ | hPGL | hM12 | ⟨⟨χ⟩⟩
    · exact ⟨⟨e, Le, heΩ, hLeA, hL7⟩, hW⟩
    · exfalso
      obtain ⟨p', e'', hp', -, hiso⟩ := (facts_of_isZ3PGLThreePi hD hPGL).1
      exact not_isoLThreePi_of_card_2520 hcL p' e'' hiso
    · exfalso
      rw [hcL] at hM12
      norm_num at hM12
    · exfalso
      rw [Nat.card_congr χ.toEquiv, KFacts.KS14.card_nativeJ2] at hcL
      norm_num at hcL
  · rcases hT2 with ⟨⟨ψ⟩⟩ | h25 | h5
    ·
      exfalso
      have hcL : Nat.card (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) = 443520 := by
        rw [Nat.card_congr ψ.toEquiv, KFacts.KS14.card_nativeM22]
      rcases h13 with ⟨-, ⟨χ⟩⟩ | hPGL | hM12 | ⟨⟨χ⟩⟩
      · rw [Nat.card_congr χ.toEquiv, card_a7_148] at hcL
        norm_num at hcL
      · obtain ⟨p', e'', hp', -, hiso⟩ := (facts_of_isZ3PGLThreePi hD hPGL).1
        exact not_isoLThreePi_of_card_443520 hcL p' e'' hiso
      · rw [hcL] at hM12
        norm_num at hM12
      · rw [Nat.card_congr χ.toEquiv, KFacts.KS14.card_nativeJ2] at hcL
        norm_num at hcL
    ·
      obtain ⟨h5f, ⟨ψ⟩⟩ := h25
      have hcL : Nat.card (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) = 50778000000 := by
        rw [Nat.card_congr ψ.toEquiv, card_projSL_three_twentyfive148]
      rcases h13 with ⟨-, ⟨χ⟩⟩ | hPGL | hM12 | ⟨⟨χ⟩⟩
      · rw [Nat.card_congr χ.toEquiv, card_a7_148] at hcL
        norm_num at hcL
      · exact hRest G A c L hstd Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ
          hTen hA hXJ (Or.inr ⟨heΩ, hLeA, Or.inl ⟨h5f, ⟨ψ⟩⟩, hPGL⟩)
      · exfalso
        rw [hcL] at hM12
        norm_num at hM12
      · rw [Nat.card_congr χ.toEquiv, KFacts.KS14.card_nativeJ2] at hcL
        norm_num at hcL
    ·
      obtain ⟨h5f, ⟨ψ⟩⟩ := h5
      have hcL : Nat.card (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) = 126000 := by
        rw [Nat.card_congr ψ.toEquiv, card_projSU_three_five148]
      rcases h13 with ⟨-, ⟨χ⟩⟩ | hPGL | hM12 | ⟨⟨χ⟩⟩
      · rw [Nat.card_congr χ.toEquiv, card_a7_148] at hcL
        norm_num at hcL
      · exact hRest G A c L hstd Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ
          hTen hA hXJ (Or.inr ⟨heΩ, hLeA, Or.inr ⟨h5f, ⟨ψ⟩⟩, hPGL⟩)
      · exfalso
        rw [hcL] at hM12
        norm_num at hM12
      · rw [Nat.card_congr χ.toEquiv, KFacts.KS14.card_nativeJ2] at hcL
        norm_num at hcL
  ·
    exact (not_isLThreeEpsAt_of_card_2520 hcK p f hKeps).elim

end CFSG.RankThree.PartTwo.Sec14
