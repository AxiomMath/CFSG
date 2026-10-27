module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res3ProofMeet
import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

@[expose] def Claim1724DeltaNorm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G) (w : G) (Q : Subgroup G), Sec17W G A c L Y₀ Y₁ S p P w Q →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
      ∀ R : Subgroup G, Maximal (fun R : Subgroup G => R ∈ scriptQPi A (lB A) ⊤ (piOf p) ∧
          R ≠ ⊥ ∧ Y₀ = (Y₀ ⊓ Subgroup.centralizer (R : Set G)) ⊔ CFSG.Open.pCoreOf 2 Y₀) R →
        ∀ T ∈ scriptQPi A (lB A) ⊤ (piOf p), R < T → T ≤ Subgroup.normalizer (R : Set G) →
          T ≤ Subgroup.normalizer (Y₀ : Set G)

namespace Proof1723N

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G}
  {p : ℕ} {P : Subgroup G} {w : G} {Q : Subgroup G}

open Proof17Res3 in
theorem covers_of_le_M
    (h1514 : Item1514S17) (hMeets : Claim1715Meets) (h : Sec17W G A c L Y₀ Y₁ S p P w Q)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {D : Subgroup G} (hDp : IsPGroup p D) (hDM : D ≤ Subgroup.normalizer (Y₀ : Set G))
    (hAD : A ≤ Subgroup.normalizer (D : Set G)) :
    Y₀ = (Y₀ ⊓ Subgroup.centralizer (D : Set G)) ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
  have hs := h.toSec17Std
  obtain ⟨hJ2, h9, -, -, -, -⟩ := hs.j2_local hJ
  obtain ⟨-, hY, -⟩ := rank3II_17_15_HJ_of hs (h1514 G A c L Y₀ hs) (hMeets G A c L Y₀ hs) hJ
  obtain ⟨e⟩ := nonempty_quotient_pCore_two_equiv hs.le_y0 hY
  obtain ⟨f⟩ := hJ2
  have hYJ : Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* CFSG.Blueprint.NativeSporadic.J2) :=
    ⟨e.trans f⟩
  have hB3 : IsPGroup 3 (A ⊓ L : Subgroup G) := hs.isE27.isPGroup.to_le inf_le_left
  have hp2 : p ≠ 2 := by
    have := h.three_lt_p
    omega
  exact eq_sup_of_mk_conj_eq h.p_prime hp2 hDp hDM fun d hd y =>
    mk_conj_eq_of_j2 hYJ h.p_prime h.three_lt_p hDp hDM
      (inf_le_right.trans hs.le_y0) hB3 h9 (inf_le_left.trans hAD) hd y

end Proof1723N

theorem claim1724DeltaMax_of_norm
    (h1514 : Item1514S17) (hMeets : Claim1715Meets) (hnorm : Claim1724DeltaNorm) :
    Claim1724DeltaMax := by
  intro G _ _ A c L Y₀ Y₁ S p P w Q h hJ R hR
  have : Fact p.Prime := ⟨h.p_prime⟩
  refine ⟨hR.prop.1, fun R' hR' hRR' => ?_⟩
  by_contra hne
  have hR'p : IsPGroup p R' := isPGroup_of_mem_scriptQPi h.p_prime hR'
  have hRne : R ≠ R' := fun heq => hne (heq ▸ le_rfl)
  have hlt : R < R' ⊓ Subgroup.normalizer (R : Set G) :=
    CFSG.Goldschmidt.G310.lt_inf_normalizer hR'p hRR' hRne
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := hR.prop.1.1.1.1.2.2
  have hAR' : A ≤ Subgroup.normalizer (R' : Set G) := hR'.1.1.1.2.2
  have hAT : A ≤ Subgroup.normalizer
      ((R' ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf hAR' (hAR.trans Subgroup.le_normalizer)
  have hT : R' ⊓ Subgroup.normalizer (R : Set G) ∈ scriptQPi A (lB A) ⊤ (piOf p) :=
    mem_scriptQPi_of_le hR' inf_le_left hAT
  have hTM := hnorm G A c L Y₀ Y₁ S p P w Q h hJ R hR _ hT hlt inf_le_right
  have hTcov := Proof1723N.covers_of_le_M h1514 hMeets h hJ (hR'p.to_le inf_le_left) hTM hAT
  have hT1 : R' ⊓ Subgroup.normalizer (R : Set G) ≠ ⊥ := fun hbot =>
    hR.prop.2.1 (le_bot_iff.mp (hbot ▸ hlt.le))
  exact absurd (hR.2 ⟨hT, hT1, hTcov⟩ hlt.le) (not_le_of_gt hlt)

end CFSG.RankThree.PartTwo.Sec17
