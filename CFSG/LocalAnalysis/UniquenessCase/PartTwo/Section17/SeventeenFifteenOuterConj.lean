module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenOuterPGL
import CFSG.GroupTheory.PGL2Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.CGT.Timmesfeld75 (IsTI)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem gap17_15_autPGL2At_of (D : Data G) {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) :
    IsL2Over17 (Bar2 L) 7 →
      CFSG.Quasithin.F6.IsPGL2 7 (Bar2 (L ⊔ NTL17 D L)) →
        ∃ (A : Type) (_ : Group A)
          (φ : ↥((L ⊔ D.T) ⊓ normalizer (L : Set G)) →* A),
          Function.Surjective φ ∧
          (∀ x : ↥((L ⊔ D.T) ⊓ normalizer (L : Set G)),
            φ x = 1 ↔ (x : G) ∈ centSection (L ⊔ D.T) L (oTwoThreeIn L)) ∧
          (CFSG.Quasithin.F6.IsPGL2 7 A ∨
            Inputs1719.IsAutOf A (alternatingGroup (Fin 6)) ∨ Inputs1719.IsM10 A ∨
            CFSG.Quasithin.F6.IsPGL2 9 A) := by
  intro h7 hPGL
  classical
  let S : Subgroup G := NTL17 D L
  let N : Subgroup G := L ⊔ D.T
  let LS : Subgroup G := L ⊔ S
  have hSN : S ≤ N := inf_le_left.trans le_sup_right
  have hLSM : LS ≤ N ⊓ Subgroup.normalizer (L : Set G) :=
    le_inf (sup_le le_sup_left hSN) (sup_le Subgroup.le_normalizer inf_le_right)
  have hLLS : L ≤ LS := le_sup_left
  have hSNL : S ≤ Subgroup.normalizer (L : Set G) := inf_le_right
  have hLSnorm : (L.subgroupOf LS).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLLS).mpr
      (sup_le Subgroup.le_normalizer hSNL)
  have hS2 : IsPGroup 2 S := D.sylowM.isPGroup.to_le inf_le_left
  have hdataLS := bar2_sup_data (L := L) (R := S) hS2 hSNL h7
  have hcentK : Subgroup.centralizer ((L.subgroupOf LS).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥LS)) : Set (Bar2 LS)) = ⊥ := by
    simpa [LS, S] using hdataLS.1
  have hcentLS : CFSG.Open.pCoreOf 2 LS = centSection LS L (oTwoThreeIn L) :=
    pCoreOf_eq_centSection hLLS hLSnorm h7 hcentK
  let φ : ↥(N ⊓ Subgroup.normalizer (L : Set G)) →* MulAut (Bar2 L) :=
    autBar2 (L := L) (N := N)
  let ψ : ↥LS →* MulAut (Bar2 L) := φ.comp (Subgroup.inclusion hLSM)
  have hker : ψ.ker = (CFSG.Open.pCoreOf 2 LS).subgroupOf LS := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hxφ : φ (Subgroup.inclusion hLSM x) = 1 := by simpa [ψ] using hx
      have hx' : (Subgroup.inclusion hLSM x : G) ∈
          centSection N L (CFSG.Open.pCoreOf 2 L) :=
        (autBar2_eq_one_iff (Subgroup.inclusion hLSM x)).mp (by simpa [φ] using hxφ)
      obtain ⟨-, hxNL, hxNB, hxcomm⟩ := hx'
      have hxLS' : (x : G) ∈ centSection LS L (oTwoThreeIn L) := by
        rw [oTwoThreeIn_eq_pCoreOf h7]
        exact ⟨x.2, hxNL, hxNB, hxcomm⟩
      rw [← hcentLS] at hxLS'
      exact hxLS'
    · intro hx
      have hx' : (x : G) ∈ centSection LS L (oTwoThreeIn L) := by
        rw [← hcentLS]
        exact hx
      obtain ⟨-, hxNL, hxNB, hxcomm⟩ := hx'
      rw [oTwoThreeIn_eq_pCoreOf h7] at hxNB hxcomm
      have hmem : (Subgroup.inclusion hLSM x : G) ∈
          centSection N L (CFSG.Open.pCoreOf 2 L) :=
        ⟨(hLSM x.2).1, hxNL, hxNB, hxcomm⟩
      have h1 : φ (Subgroup.inclusion hLSM x) = 1 :=
        (autBar2_eq_one_iff (Subgroup.inclusion hLSM x)).mpr (by simpa [φ] using hmem)
      simpa [ψ] using h1
  have hψcard : Nat.card ↥ψ.range = 336 := by
    have h1 : Nat.card ↥ψ.ker * Nat.card ↥ψ.range = Nat.card ↥LS := by
      rw [← Subgroup.index_ker ψ, Subgroup.card_mul_index]
    have h2 : Nat.card ↥(CFSG.pCore 2 ↥LS) * Nat.card (Bar2 LS) = Nat.card ↥LS := by
      have h := Subgroup.card_mul_index (H := CFSG.pCore 2 ↥LS) (G := ↥LS)
      rwa [Subgroup.index_eq_card] at h
    have hcard : Nat.card (Bar2 LS) = 336 := CFSG.GroupTheory.card_of_isPGL2_seven hPGL
    rw [hker, CFSG.openPCoreOf_subgroupOf, ← h2] at h1
    have := Nat.mul_left_cancel (Nat.card_pos (α := ↥(CFSG.pCore 2 ↥LS))) h1
    simpa [hcard] using this
  have hψle : ψ.range ≤ φ.range := by
    rintro y ⟨x, rfl⟩
    exact ⟨Subgroup.inclusion hLSM x, rfl⟩
  have hφcard : Nat.card ↥φ.range = 336 := by
    have hle : Nat.card ↥ψ.range ≤ Nat.card ↥φ.range :=
      Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hψle)
    have hAutcard : Nat.card (MulAut (Bar2 L)) = 336 := card_mulAut_of_isL2Over17_seven h7
    have hφle : Nat.card ↥φ.range ≤ 336 := by
      rw [← hAutcard]
      exact Subgroup.card_le_card_group φ.range
    omega
  have hφtop : φ.range = ⊤ :=
    Subgroup.eq_top_of_card_eq φ.range
      (by rw [hφcard, card_mulAut_of_isL2Over17_seven h7])
  refine ⟨MulAut (Bar2 L), inferInstance, φ, ?_, ?_,
    Or.inl (isPGL2_mulAut_of_isL2Over17_seven h7)⟩
  · exact MonoidHom.range_eq_top.mp hφtop
  · intro x
    change autBar2 (L := L) (N := N) x = 1 ↔
      (x : G) ∈ centSection N L (oTwoThreeIn L)
    rw [autBar2_eq_one_iff, oTwoThreeIn_eq_pCoreOf h7]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
