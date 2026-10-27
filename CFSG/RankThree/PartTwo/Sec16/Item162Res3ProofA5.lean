module

public import CFSG.RankThree.PartTwo.Sec16.Item162ResProofUJ
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
public import CFSG.RankThree.PartTwo.Sec15.Item156ProofType

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

@[expose] def Step162UJHJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
      ∀ Y₁ Y₂ S₁ S₂ : Subgroup G, MaxCE162 A (lB A) Y₁ Y₂ S₁ S₂ →
      ¬ S₁ ≤ S₂ → ¬ S₂ ≤ S₁ →
      ¬ TransOn A (lB A) (xA A)
          (delta A (lB A) (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G))) →
      ∀ J ∈ scriptY0 A (lB A),
        J ≤ delta A (lB A) (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G)) →
        Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5)) →
        (¬ ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
          L' = (L' ⊓ J) ⊔ CFSG.Open.pCoreOf 2 L') →
        (Y₁ = (Y₁ ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y₁ ∧ L = (Y₁ ⊓ L) ⊔ CFSG.Open.pCoreOf 2 L) →
        (Y₂ = (Y₂ ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y₂ ∧ L = (Y₂ ⊓ L) ⊔ CFSG.Open.pCoreOf 2 L) →
        oPrimeResidualOf 3
          (delta A (lB A) (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G))) = ⊥

namespace Res162c

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem exists_hj_of_a5 {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h148 : Item148Small A (lB A))
    {J : Subgroup G} (hJ : J ∈ scriptY4 A (lB A))
    (φ : ↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5)) :
    ∃ (c₀ : G) (L₀ : Subgroup G), Subgroup.zpowers c₀ ∈ omegaA A ∧ L₀ ∈ lA A c₀ ∧
      Nonempty (↥L₀ ⧸ aschbacherSolvableCore 3 ↥L₀ ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  have hJY : J ∈ scriptY A := hJ.1
  have hJΔ : J = deltaZero A (lB A) J := rank3II_15_1_lB h.isE27 hbot hJ
  have hq : IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) := hJ.2.2.2
  have : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (α := Fin 5) (by simp)
  have hs : IsSimpleGroup (↥J ⧸ CFSG.pCore 2 ↥J) := φ.isSimpleGroup
  have hcardQ : Nat.card (↥J ⧸ CFSG.pCore 2 ↥J) = 60 := by
    rw [Nat.card_congr φ.toEquiv, card_alternatingGroup_five]
  have hnab : ∃ a b : ↥J ⧸ CFSG.pCore 2 ↥J, a * b ≠ b * a := by
    obtain ⟨-, -, a, b, hab⟩ := hq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    refine ⟨a, b, fun hab' => hab ?_⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hab']
  have hZ3 : IsPGroup 3 (Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J)) := by
    rw [center_eq_bot_of_isSimpleGroup hs hnab]
    exact IsPGroup.of_bot
  have h3 : 3 ∣ Nat.card (↥J ⧸ CFSG.pCore 2 ↥J) := by
    rw [hcardQ]
    norm_num
  have hcore : CFSG.pPrimeCore 3 ↥J = CFSG.pCore 2 ↥J :=
    pPrimeCore_three_eq_pCore_two (pPrimeCore_three_eq_bot_of_isQuasisimple hq h3 hZ3)
  let := ker148_normal hJY.2
  obtain ⟨ψ⟩ := nonempty_img148_equiv hJY.2
  have he : Nonempty (↥(img148 A J (deltaZero A (lB A) J)) ≃* ↥J ⧸ CFSG.pCore 2 ↥J) := by
    rw [← hJΔ]
    exact ⟨ψ.trans (QuotientGroup.quotientMulEquivOfEq hcore)⟩
  obtain ⟨e⟩ := he
  have hqI : IsQuasisimple ↥(img148 A J (deltaZero A (lB A) J)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq
  have hcardI : Nat.card ↥(img148 A J (deltaZero A (lB A) J)) = 60 ∨
      Nat.card ↥(img148 A J (deltaZero A (lB A) J)) = 1080 := by
    left
    rw [Nat.card_congr e.toEquiv]
    exact hcardQ
  obtain ⟨c₀, hc₀, -, L₀, hL₀, hJ2⟩ := h148 J hJY hqI hcardI
  exact ⟨c₀, L₀, hc₀, hL₀, hJ2⟩

end Res162c

theorem step162UJA5_of (hbot : Item145BotS14) (h148 : Item148SmallS14) (h153 : Item153MainR)
    (hobs : Claim153ObsR) (h1411 : Item1411_1R) (h155 : Item155R) (h1523 : Item1523R)
    (hHJ : Step162UJHJ) : Step162UJA5 := by
  intro G _ _ A c L h Y₁ Y₂ S₁ S₂ hmax h12 h21 hnt J hJ hJK hφ
  obtain ⟨φ⟩ := hφ
  by_cases hcov : ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧
      L' ∈ lA A c' ∧ L' = (L' ⊓ J) ⊔ CFSG.Open.pCoreOf 2 L'
  ·
    exact h12 (Proof162.le_of_maxCE162 (h153 G A c L h) (hobs G A c L h) (h1411 G A c L h)
      (h155 G A c L h) hmax fun _ _ _ => ⟨J, hJ, hJK, Or.inr hcov⟩)
  have h14 := h.toSec14Std
  obtain ⟨c₀, L₀, hc₀, hL₀, hJ2⟩ :=
    Res162c.exists_hj_of_a5 h14 (hbot G A c L h14) (h148 G A c L h14) hJ.1 φ
  have h₀ : Sec15R G A c₀ L₀ := sec15R_of_point h hc₀ hL₀
  have h23 := h1523 G A c₀ L₀ h₀ hJ2
  have hO := hHJ G A c₀ L₀ h₀ hJ2 Y₁ Y₂ S₁ S₂ hmax h12 h21 hnt J hJ hJK ⟨φ⟩ hcov
    (h23 Y₁ hmax.1.mem₁) (h23 Y₂ hmax.1.mem₂)
  have hJle := le_oPrimeResidualOf_delta hJ.1 (hJK.trans (delta_le _))
  rw [hO] at hJle
  exact ne_bot_of_mem_scriptY0 hJ (le_bot_iff.mp hJle)

end CFSG.RankThree.PartTwo.Sec16
