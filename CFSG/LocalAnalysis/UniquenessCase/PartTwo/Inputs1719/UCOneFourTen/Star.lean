module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Shape
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ThreeLStarClosure
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem mem_center_bar2_of_commutator_mem_pCoreOf {L A : Subgroup G} (hAL : A ≤ L)
    (h : ∀ a ∈ A, ∀ l ∈ L, ⁅a, l⁆ ∈ pCoreOf 2 L) {a : G} (ha : a ∈ A) :
    (QuotientGroup.mk (⟨a, hAL ha⟩ : ↥L) : Bar2 L) ∈ Subgroup.center (Bar2 L) := by
  rw [Subgroup.mem_center_iff]
  intro x
  induction x using QuotientGroup.induction_on with
  | H l =>
    set aL : ↥L := ⟨a, hAL ha⟩ with haL
    have hxL : ⁅aL, l⁆ ∈ CFSG.pCore 2 ↥L := by
      have hval : ((⁅aL, l⁆ : ↥L) : G) = ⁅a, (l : G)⁆ :=
        map_commutatorElement L.subtype aL l
      have hval2 : ((⁅aL, l⁆ : ↥L) : G) ∈ pCoreOf 2 L := by
        rw [hval]
        exact h a ha (l : G) l.2
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hval2
      exact (Subtype.ext hyx) ▸ hy
    have hone : ⁅(QuotientGroup.mk' (CFSG.pCore 2 ↥L)) aL,
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) l⁆ = 1 := by
      rw [← map_commutatorElement (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) aL l]
      exact (QuotientGroup.eq_one_iff ⁅aL, l⁆).mpr hxL
    exact (commutatorElement_eq_one_iff_mul_comm.mp hone).symm

theorem inf_normalizer_le_normalizer {M L A : Subgroup G} {n : ℕ} (hL : L ∈ calC M)
    (hSz : IsSz (Bar2 L) n) (hAL : A ≤ L) (hA : (Nat.card A).Prime) (hA2 : Nat.card A ≠ 2) :
    M ⊓ normalizer (A : Set G) ≤ normalizer (L : Set G) := by
  intro g hg
  obtain ⟨hgM, hgN⟩ := hg
  have hZ : Subgroup.center (Bar2 L) = ⊥ := FourteenEight.center_eq_bot_of_isSz hSz
  set L' := L.map (MulAut.conj g).toMonoidHom with hL'def
  have hL' : L' ∈ calC M := by
    rw [hL'def]
    exact calC_map_conj_of_mem_normalizer hL (Subgroup.le_normalizer hgM)
  have hmapA : A.map (MulAut.conj g).toMonoidHom = A :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN
  have hAleq : A ≤ L' := by
    rw [hL'def, ← hmapA]
    exact Subgroup.map_mono hAL
  by_cases hEq : L' = L
  · have hmapL : L.map (MulAut.conj g).toMonoidHom = L := hL'def ▸ hEq
    rwa [Subgroup.mem_normalizer_iff_map_conj_eq]
  · exfalso
    have hne : L ≠ L' := fun h => hEq h.symm
    have hcomm : ⁅L, L'⁆ ≤ pCoreOf 2 L ⊓ pCoreOf 2 L' :=
      PartTwo.calC_commutator_le_of_ne hL hL' hne
    have hmem : ∀ a ∈ A, ∀ l ∈ L, ⁅a, l⁆ ∈ pCoreOf 2 L := by
      intro a ha l hl
      have h1 : ⁅a, l⁆ ∈ ⁅L', L⁆ := Subgroup.commutator_mem_commutator (hAleq ha) hl
      have h2 : ⁅L', L⁆ = ⁅L, L'⁆ := Subgroup.commutator_comm L' L
      exact (hcomm (h2 ▸ h1)).1
    have hpcoreL : A ≤ pCoreOf 2 L := by
      intro a ha
      have hc := mem_center_bar2_of_commutator_mem_pCoreOf hAL hmem ha
      rw [hZ, Subgroup.mem_bot] at hc
      rw [QuotientGroup.eq_one_iff] at hc
      exact Subgroup.mem_map.mpr ⟨⟨a, hAL ha⟩, hc, rfl⟩
    have h2 : IsPGroup 2 ↥A := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le hpcoreL
    rcases h2.card_eq_or_dvd with h1 | hd
    · exact absurd h1 (by have := hA.two_le; omega)
    · rcases hA.eq_one_or_self_of_dvd 2 hd with h3 | h3
      · norm_num at h3
      · exact hA2 h3.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
