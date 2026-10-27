module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res7ProofMemFix
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
public import CFSG.RankThree.PartTwo.Sec6.Item612Plus

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def Step143HJMemFixL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ a ∈ A, a ≠ 1 → Subgroup.zpowers a ∉ omegaA A →
      ∀ (B : Subgroup G) (b d : G) (Lb : Subgroup G), IsHyperplane A B → a ∈ B →
        IsLBConfig A B b d Lb →
        ∀ (b' d' : G) (Lb' X : Subgroup G), Subgroup.zpowers b' ∈ omegaA A → Lb' ∈ lA A b' →
          Nonempty (↥Lb' ⧸ aschbacherSolvableCore 3 ↥Lb' ≃* CFSG.Blueprint.NativeSporadic.J2) →
          d' ∈ A → d' ≠ 1 → IsThreeCentralIn Lb' d' → a ∈ Subgroup.closure {b', d'} →
          X ≤ delta A (lB A) (Subgroup.centralizer ({a} : Set G)) →
          (∀ D' : Subgroup G, IsHyperplane A D' → a ∈ D' →
            lB A D' ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X) →
          delta A (lB A) (Subgroup.centralizer ({a} : Set G)) =
            pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
              pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X →
          Subgroup.centralizer ({a} : Set G) ≤
            Subgroup.normalizer
              ((pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X : Subgroup G) :
                Set G) →
          Subgroup.zpowers a = Subgroup.zpowers d' →
          (∃ 𝒳 : Set (Subgroup G), 𝒳 ⊆ thetaComponentsAt 3 a ∧ 𝒳.Nonempty ∧ X = sSup 𝒳) →
          (Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
              CFSG.Blueprint.NativeSporadic.ON ∨
            IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X)) →
          ∀ D : Subgroup G, IsHyperplane A D → a ∈ D →
            (∀ B' : Subgroup G, IsHyperplane A B' → a ∈ B' → B' ≠ D →
              ¬ ⁅pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X, B'⁆ ≤
                pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))) →
            ¬ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X ≤
              lB A D ⊔ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) →
            ∀ R : Subgroup G,
              R ≤ (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X) ⊓
                Subgroup.centralizer (D : Set G) →
              ¬ 3 ∣ Nat.card R → A ≤ Subgroup.normalizer (R : Set G) → R = ⁅R, A⁆ →
                R ≤ qBound A (lB A) D

namespace Res7DescFix

variable {G : Type} [Group G] [Finite G]

theorem card_eq_of_isTripleCover_a6 {Q : Type*} [Group Q]
    (h : Sec4.IsTripleCover Q (alternatingGroup (Fin 6))) : Nat.card Q = 1080 := by
  obtain ⟨hZ, ⟨e⟩⟩ := h
  have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Q), hZ,
    Nat.card_congr e.toEquiv, hA6]

theorem sup_le_sup_lB_of_tripleA6 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {a : G}
    {B : Subgroup G} {b d : G} {Lb : Subgroup G} (hB : IsHyperplane A B) (haB : a ∈ B)
    (hc : IsLBConfig A B b d Lb) {X : Subgroup G} (hX : X ∈ thetaComponentsAt 3 a)
    (htype : Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6)))
    (hLB : lB A B ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X) :
    pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X ≤
      lB A B ⊔ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) with hO
  set J := inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G)) with hJdef
  have hLBJ : lB A B = J := Item148HJ.lB_eq_residual h hB hc
  obtain ⟨hdL, -, hq, hZ, -, htc, -⟩ := Item148HJ.resProj_facts h hB hc
  have hON : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (O : Set G) :=
    le_normalizer_pPrimeCoreOf 3 _
  have hJa : J ≤ Subgroup.centralizer ({a} : Set G) :=
    (Item148HJ.residual_le_centralizer hc).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haB))
  have hXa : X ≤ Subgroup.centralizer ({a} : Set G) := le_centralizer_of_mem_thetaComponentsAt hX
  have hO3 : Nat.Coprime 3 (Nat.card O) := coprime_card_pPrimeCoreOf 3 _
  set M : Subgroup ↥J := O.subgroupOf J with hM
  have hMn : M.Normal := Subgroup.normal_subgroupOf_of_le_normalizer (hJa.trans hON)
  have hMcard : Nat.card M = Nat.card (O ⊓ J : Subgroup G) := by
    rw [hM, ← Subgroup.card_map_of_injective J.subtype_injective, Subgroup.subgroupOf_map_subtype]
  have hM3 : ¬ 3 ∣ Nat.card M := by
    rw [hMcard]
    intro h3
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hO3
      (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hMker := Item148HJ.le_ker_of_normal (Item148HJ.resProj Lb d) hq hZ hMn hM3
  have hrange : Nat.card (Item148HJ.resProj Lb d).range = 1080 := card_eq_of_isTripleCover_a6 htc
  have hJcard : Nat.card J = 1080 * Nat.card (Item148HJ.resProj Lb d).ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Item148HJ.resProj Lb d).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange (Item148HJ.resProj Lb d)).toEquiv,
      hrange]
  have hJge : 1080 * Nat.card (J ⊓ O : Subgroup G) ≤ Nat.card J := by
    rw [hJcard, inf_comm, ← hMcard]
    exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hMker)
  have hθX := Res7MemFix.theta_le_of_mem hX
  have hXcard : Nat.card X = 1080 * Nat.card (inSubgroup (aschbacherSolvableCore 3) X) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥X),
      card_eq_of_isTripleCover_a6 htype, inSubgroup,
      Subgroup.card_map_of_injective X.subtype_injective]
  have hXle : Nat.card X ≤ 1080 * Nat.card (X ⊓ O : Subgroup G) := by
    rw [hXcard]
    exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le
      (le_inf (Subgroup.map_subtype_le _) hθX))
  have h1 := Sec6.card_sup_mul_card_inf (hJa.trans hON)
  have h2 := Sec6.card_sup_mul_card_inf (hXa.trans hON)
  have hpos1 : 0 < Nat.card (J ⊓ O : Subgroup G) := Nat.card_pos
  have hpos2 : 0 < Nat.card (X ⊓ O : Subgroup G) := Nat.card_pos
  have hJO : 1080 * Nat.card O ≤ Nat.card (J ⊔ O : Subgroup G) := by
    refine Nat.le_of_mul_le_mul_right ?_ hpos1
    calc 1080 * Nat.card O * Nat.card (J ⊓ O : Subgroup G)
        = 1080 * Nat.card (J ⊓ O : Subgroup G) * Nat.card O := by ring
      _ ≤ Nat.card J * Nat.card O := Nat.mul_le_mul_right _ hJge
      _ = Nat.card (J ⊔ O : Subgroup G) * Nat.card (J ⊓ O : Subgroup G) := h1.symm
  have hXO : Nat.card (X ⊔ O : Subgroup G) ≤ 1080 * Nat.card O := by
    refine Nat.le_of_mul_le_mul_right ?_ hpos2
    calc Nat.card (X ⊔ O : Subgroup G) * Nat.card (X ⊓ O : Subgroup G)
        = Nat.card X * Nat.card O := h2
      _ ≤ 1080 * Nat.card (X ⊓ O : Subgroup G) * Nat.card O := Nat.mul_le_mul_right _ hXle
      _ = 1080 * Nat.card O * Nat.card (X ⊓ O : Subgroup G) := by ring
  have hle : J ⊔ O ≤ X ⊔ O := by
    rw [sup_comm X O]
    exact sup_le (hLBJ ▸ hLB) le_sup_left
  have heq : J ⊔ O = X ⊔ O := Subgroup.eq_of_le_of_card_ge hle (hXO.trans hJO)
  rw [hLBJ, sup_comm O X, ← heq]

end Res7DescFix

open Res7MemFix Res7DescFix

end CFSG.RankThree.PartTwo.Sec14
