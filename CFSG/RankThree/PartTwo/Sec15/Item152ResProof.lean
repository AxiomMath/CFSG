module

public import CFSG.RankThree.PartTwo.Sec15.Item152ResProofPS
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec15.Item152ConfAProofTheta

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise commutatorElement

namespace Proof152Res

variable {G : Type} [Group G] [Finite G]

variable {A : Subgroup G}

theorem le_deltaZero_of_tData (hA : Late.IsE27 A) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    {X P T K S : Subgroup G} {p : ℕ} (hPd : PData152 A X p P)
    (hTd : TData152 A (lB A) X P T) (hKd : KData152 A (lB A) P T K S)
    (hPQ : P ∈ scriptQ A (lB A)) : P ≤ deltaZero A (lB A) K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := T ⊓ Subgroup.normalizer (P : Set G) with hN
  set U := ⁅N, A⁆ with hU
  have hT := hTd.mem_t
  have hAN : A ≤ Subgroup.normalizer (N : Set G) :=
    Late.le_normalizer_inf hT.prop.1.1.1.2.2
      (hPd.norm_p.trans (Sec6.normalizer_le_normalizer_normalizer P))
  have hUN : U ≤ N := Subgroup.le_normalizer_iff_commutator_le_left.mp hAN
  have hAU : A ≤ Subgroup.normalizer (U : Set G) :=
    Sec14.le_normalizer_commutator hAN Subgroup.le_normalizer
  have hTK : T ≤ K := le_sup_left.trans hKd.le_k
  have hPK : P ≤ K := le_sup_right.trans hKd.le_k
  have hUK : U ≤ K := hUN.trans (inf_le_left.trans hTK)
  have hUQ : U ∈ scriptQ A (lB A) := mem_scriptQ_of_le hT.prop.1.1 (hUN.trans inf_le_left) hAU
  have hN3 : ¬ 3 ∣ Nat.card N := by
    intro h3
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
      ((isPGroup_of_mem_scriptQPi Nat.prime_two hT.prop).to_le inf_le_left)
    rw [hk] at h3
    have := Nat.prime_three.dvd_of_dvd_pow h3
    omega
  have hUA : ⁅U, A⁆ = U :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3 Nat.prime_three A N
      hA.isPGroup hN3 hAN
  set D := ⁅U ⊔ P, A⁆ with hD
  have hUD : U ≤ D := by
    rw [← hUA]
    exact Subgroup.commutator_mono le_sup_left le_rfl
  have hPD : P ≤ Subgroup.normalizer (D : Set G) :=
    le_sup_right.trans (Subgroup.normalizer_commutator_ge_left (U ⊔ P) A)
  have hPle : P ≤ D :=
    calc P = ⁅U, P⁆ := hTd.eq_comm_p
      _ ≤ ⁅D, P⁆ := Subgroup.commutator_mono hUD le_rfl
      _ ≤ D := Subgroup.le_normalizer_iff_commutator_le_left.mp hPD
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := hKd.mem_k.1.2
  have h145 := (rank3II_14_5 hA (isNaturalFamily_lB A) hbot hAK).2.1
  have hUPΔ : U ⊔ P ≤ delta A (lB A) K := sup_le (le_delta hUQ hUK) (le_delta hPQ hPK)
  rw [h145]
  exact hPle.trans (Subgroup.commutator_mono hUPΔ le_rfl)

end Proof152Res

open Proof152ResT Proof152ResPS Proof152Res

section Named

variable {G : Type} [Group G] [Finite G]

@[expose] def Step152ConfThetaLeD (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ (Y M X : Subgroup G) (c' : G) (L' : Subgroup G) (p : ℕ) (P T K S : Subgroup G),
    Pt152 A LB Y M X c' L' → PData152 A X p P → TData152 A LB X P T → KData152 A LB P T K S →
    P ∈ scriptQ A LB → P ≤ deltaZero A LB K →
      P ≤ (aschbacherSolvableCore 3 ↥K).map K.subtype

@[expose] def Step152ConfThetaNormD (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ (Y M X : Subgroup G) (c' : G) (L' : Subgroup G) (p : ℕ) (P T K S : Subgroup G),
    Pt152 A LB Y M X c' L' → PData152 A X p P → TData152 A LB X P T → KData152 A LB P T K S →
    P ∈ scriptQ A LB → P ≤ deltaZero A LB K →
    P ≤ (aschbacherSolvableCore 3 ↥K).map K.subtype →
      ((P ⊔ CFSG.Open.pCoreOf 2 K).subgroupOf K).Normal

@[expose] noncomputable def Step152ConfThetaLeDR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step152ConfThetaLeD A (lB A)

@[expose] noncomputable def Step152ConfThetaNormDR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step152ConfThetaNormD A (lB A)

end Named

section Bridges

variable {G : Type} [Group G] [Finite G]

theorem mem_scriptQ_and_le_deltaZero
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (h147 : ∀ X ∈ scriptY A, X = delta A (lB A) X →
      ⁅deltaZero A (lB A) X, pPrimeCoreOf 3 X⁆ ≤ delta A (lB A) (pPrimeCoreOf 3 X))
    {Y M X : Subgroup G} {c' : G} {L' : Subgroup G} {p : ℕ} {P T K S : Subgroup G}
    (hpt : Pt152 A (lB A) Y M X c' L') (hPd : PData152 A X p P)
    (hTd : TData152 A (lB A) X P T) (hKd : KData152 A (lB A) P T K S) :
    P ∈ scriptQ A (lB A) ∧ P ≤ deltaZero A (lB A) K := by
  have hA : Late.IsE27 A := h.isE27
  obtain ⟨hX0, h147X, -⟩ := facts_of_ctx152 rfl hA h146 hbot h147 hpt.ctx
  have hPQ := mem_scriptQ_of_tData hA h146 hpt.ctx.norm_x hX0 h147X hPd
    (Proof152ConfA.PData152.ne_three hpt.ctx hPd) hTd
  exact ⟨hPQ, le_deltaZero_of_tData hA hbot hPd hTd hKd hPQ⟩

theorem step152ConfThetaLe_of_D
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (h147 : ∀ X ∈ scriptY A, X = delta A (lB A) X →
      ⁅deltaZero A (lB A) X, pPrimeCoreOf 3 X⁆ ≤ delta A (lB A) (pPrimeCoreOf 3 X))
    (hD : Step152ConfThetaLeD A (lB A)) : Step152ConfThetaLe A (lB A) := by
  intro Y M X c' L' p P T K S hpt hPd hTd hKd
  obtain ⟨hPQ, hPΔ⟩ := mem_scriptQ_and_le_deltaZero h h146 hbot h147 hpt hPd hTd hKd
  exact hD Y M X c' L' p P T K S hpt hPd hTd hKd hPQ hPΔ

theorem step152ConfThetaNorm_of_D
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (h147 : ∀ X ∈ scriptY A, X = delta A (lB A) X →
      ⁅deltaZero A (lB A) X, pPrimeCoreOf 3 X⁆ ≤ delta A (lB A) (pPrimeCoreOf 3 X))
    (hD : Step152ConfThetaNormD A (lB A)) : Step152ConfThetaNorm A (lB A) := by
  intro Y M X c' L' p P T K S hpt hPd hTd hKd hθ
  obtain ⟨hPQ, hPΔ⟩ := mem_scriptQ_and_le_deltaZero h h146 hbot h147 hpt hPd hTd hKd
  exact hD Y M X c' L' p P T K S hpt hPd hTd hKd hPQ hPΔ hθ

theorem step152ConfThetaLeR_of_D
    (h1444 : Item1444S14) (h146 : Item146S14) (hbot : Item145BotS14)
    (hD : Step152ConfThetaLeDR) : Step152ConfThetaLeR :=
  fun G _ _ A c L hR => step152ConfThetaLe_of_D hR.toSec14Std (h146 G A c L hR.toSec14Std)
    (hbot G A c L hR.toSec14Std)
    (fun _ hXY hXΔ => commutator_le_delta_of_eq_delta hR.toSec14Std.isE27
      (h1444 G A c L hR.toSec14Std) (h146 G A c L hR.toSec14Std) hXY.2 hXΔ)
    (hD G A c L hR)

theorem step152ConfThetaNormR_of_D
    (h1444 : Item1444S14) (h146 : Item146S14) (hbot : Item145BotS14)
    (hD : Step152ConfThetaNormDR) : Step152ConfThetaNormR :=
  fun G _ _ A c L hR => step152ConfThetaNorm_of_D hR.toSec14Std (h146 G A c L hR.toSec14Std)
    (hbot G A c L hR.toSec14Std)
    (fun _ hXY hXΔ => commutator_le_delta_of_eq_delta hR.toSec14Std.isE27
      (h1444 G A c L hR.toSec14Std) (h146 G A c L hR.toSec14Std) hXY.2 hXΔ)
    (hD G A c L hR)

end Bridges

end CFSG.RankThree.PartTwo.Sec15
