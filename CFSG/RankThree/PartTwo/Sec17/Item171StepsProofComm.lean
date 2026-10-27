module

public import CFSG.RankThree.PartTwo.Sec17.Item171Proof
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofTools
import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

@[expose] noncomputable def Step171CommQ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ∀ b ∈ A, b ≠ 1 →
      ¬ Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (Y₀ : Set G) →
      ∀ B : Subgroup G, IsHyperplane A B → b ∈ B → c ∉ B →
        ⁅CFSG.Open.pCoreOf 2 Y₀ ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆ ⊓
            Subgroup.centralizer (B : Set G) ≤ qBound A (lB A) B

namespace Proof171Steps

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

omit [Finite G] in
theorem le_normalizer_commutator {X H K : Subgroup G} (hH : X ≤ Subgroup.normalizer (H : Set G))
    (hK : X ≤ Subgroup.normalizer (K : Set G)) :
    X ≤ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := fun x hx =>
  mem_normalizer_of_map_conj_eq'' (by
    rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer' (hH hx),
      map_conj_eq_of_mem_normalizer' (hK hx)])

theorem mem_scriptQZero_of_commQ (hQ : Step171CommQ) (h : Sec17Std G A c L Y₀) {b : G}
    (hb : b ∈ A) (hb1 : b ≠ 1)
    (hbM : ¬ Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (Y₀ : Set G)) :
    ⁅CFSG.Open.pCoreOf 2 Y₀ ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆ ∈
      collectionIn (scriptQZero A (lB A)) (Subgroup.centralizer ({b} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  have hA : Late.IsE27 A := HeadProof.isE27_of_std h
  have hcA : c ∈ A := hD.mem_A
  set V := CFSG.Open.pCoreOf 2 Y₀ with hV
  set W := V ⊓ Subgroup.centralizer ({b} : Set G) with hW
  set P := ⁅W, Subgroup.zpowers c⁆ with hP
  have hV2 : IsPGroup 2 V := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀
  have hMV : Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := h.le_normalizer_y0.trans hMV
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx hb)
  have hAc : A ≤ Subgroup.centralizer ({c} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx hcA)
  have hAW : A ≤ Subgroup.normalizer (W : Set G) :=
    Late.le_normalizer_inf hAV (hAb.trans Subgroup.le_normalizer)
  have hAzc : A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    hAc.trans (centralizer_singleton_le_normalizer_zpowers c)
  have hzcW : Subgroup.zpowers c ≤ Subgroup.normalizer (W : Set G) :=
    Subgroup.zpowers_le.mpr (hAW hcA)
  have hPW : P ≤ W := Subgroup.le_normalizer_iff_commutator_le_left.mp hzcW
  have hP2 : IsPGroup 2 P := hV2.to_le (hPW.trans inf_le_left)
  have hP3 : ¬ 3 ∣ Nat.card P := Proof171.not_three_dvd_of_isPGroup_two hP2
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := le_normalizer_commutator hAW hAzc
  have hPc : ⁅P, Subgroup.zpowers c⁆ = P :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3 Nat.prime_three
      (Subgroup.zpowers c) W (Proof171.isPGroup_zpowers_of_pow_three (hD.isElemAbelian.2 c hcA))
      (Proof171.not_three_dvd_of_isPGroup_two (hV2.to_le inf_le_left)) hzcW
  have hPA : P = ⁅P, A⁆ := le_antisymm
    (hPc.symm.le.trans (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hcA)))
    (Subgroup.le_normalizer_iff_commutator_le_left.mp hAP)
  have hhyp : ∀ B : Subgroup G, IsHyperplane A B →
      P ⊓ Subgroup.centralizer (B : Set G) ≤ qBound A (lB A) B := by
    intro B hB
    have hV3 : ∀ X : Subgroup G, X ≤ Subgroup.normalizer (Y₀ : Set G) →
        V ⊓ X ≤ pPrimeCoreOf 3 X := fun X hX =>
      le_pPrimeCoreOf inf_le_right (Late.le_normalizer_inf (hX.trans hMV) Subgroup.le_normalizer)
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
          (Proof171.not_three_dvd_of_isPGroup_two (hV2.to_le inf_le_left)))
    by_cases hcB : c ∈ B
    ·
      have hCB : Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (Y₀ : Set G) :=
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcB)).trans
          (HeadProof.centralizer_c_le_M h)
      refine le_trans ?_ (le_sup_of_le_left le_sup_left)
      exact (inf_le_inf_right _ (hPW.trans inf_le_left)).trans (hV3 _ hCB)
    by_cases hbB : b ∈ B
    · exact hQ G A c L Y₀ h b hb hb1 hbM B hB hbB hcB
    ·
      have hAle : A ≤ B ⊔ Subgroup.zpowers b := le_sup_zpowers_of_not_mem hA hB hb hbB
      have hCA : P ⊓ Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer (A : Set G) :=
        fun x hx => mem_centralizer_of_le_sup hAle hx.2 ((hPW.trans inf_le_right) hx.1)
      refine le_trans ?_ (le_sup_of_le_left le_sup_right)
      exact (le_inf ((inf_le_left.trans hPW).trans inf_le_left) hCA).trans
        (hV3 _ (HeadProof.centralizer_le_M h))
  exact ⟨⟨⟨⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three P).mpr hP3, hAP⟩, hhyp⟩, hPA⟩,
    hPW.trans inf_le_right⟩

end Proof171Steps

theorem step171Comm_of (hQ : Step171CommQ) (hD0 : Step171Delta0) : Step171Comm := by
  intro G _ _ A c L Y₀ h b hb hb1 hbM
  obtain ⟨hmem, hle⟩ := Proof171Steps.mem_scriptQZero_of_commQ hQ h hb hb1 hbM
  exact (le_deltaZero hmem hle).trans (Proof171.deltaZero_le_yb171 h hD0 hb hb1)

end CFSG.RankThree.PartTwo.Sec17
