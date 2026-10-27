module

public import CFSG.Quasithin.H13.NQCatKG68Singer
public import CFSG.Quasithin.H13.NQCatLieCartanG2
public import CFSG.Quasithin.H13.NQCatLieCentralG2

public section

namespace CFSG.Quasithin.H13.KG68.Singer.G2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
  CFSG.Quasithin.H13.NQCat

variable {K : Type} [Field K]

theorem cartanSingerCover_g2
    [Finite K] [CharP K 2] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) :
    CartanSingerCover ↥(adjointGroup Tag.G2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hBC⟩ := triangular_borel_structure.{0, 0} Tag.G2 K
  have hUC : posUnipotent Tag.G2 K ≤ adjointGroup Tag.G2 K := posUnipotent_le_adjointGroup
  have hHC : torusGroup Tag.G2 K ≤ adjointGroup Tag.G2 K := le_sup_left.trans (hBC K).1
  have hU : IsSylowTwoOf (posUnipotent Tag.G2 K) (adjointGroup Tag.G2 K) :=
    isSylowTwoOf_iff_isSylowOf.2 (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1
  have hrC : IsRoot Tag.G2 rC := (isRoot_pos_iff.2 (by simp)).1
  have e0 : (∑ j, Tag.G2.cartan i0 j * rC j) = 1 := by decide
  have hFacts := G2.parabolicFacts_one hK hf
  refine cartanSingerCover_of_le hUC hU hHC torusGroup_le_normalizer_posUnipotent ?_
    (pinnedX_injective Tag.G2 K rC) (pinnedX_zero _ _ _)
    (fun c => hUC (LieCentral.G2.gX_mem_posUnipotent (by simp) c))
    (fun c t ht =>
      (Subgroup.mem_centralizer_iff.1 (LieCentral.G2.gX_rC_mem_centralizer c) t ht).symm)
    (fun g hg hgc => ?_) (fun h hh => ?_) (fun u => ?_)
  · rw [inf_comm, LieCartan.G2.normalizer_posUnipotent_inf_eq, borelGroup, sup_comm]
  · have hUP := posUnipotent_le_parabolicSubgroup (τ := Tag.G2) (K := K) {i1}
    have hQU := parabolicRadical_le_posUnipotent (τ := Tag.G2) (K := K) {i1}
    have hgC : g ∈ Subgroup.centralizer
        (parabolicRadical Tag.G2 K {i1} : Set (ModGL Tag.G2 K)) :=
      Subgroup.mem_centralizer_iff.2 fun q hq => (hgc q (hQU hq)).symm
    obtain ⟨t, ht⟩ := LieMult.eq_gX_rC_of_mem_center_one
      ⟨hFacts.selfCentralizing ⟨hUP hg, hgC⟩, hgC⟩
    exact ⟨t, ht.symm⟩
  · have hle : torusGroup Tag.G2 K ≤ actsBySubgroup (pinnedX Tag.G2 K rC) := by
      rw [torusGroup, Subgroup.closure_le]
      rintro _ ⟨⟨i, v⟩, rfl⟩
      exact ⟨v ^ (∑ j, Tag.G2.cartan i j * rC j), LieCartan.G2.torusElt_conj_gX i v hrC⟩
    exact hle hh
  · refine ⟨torusElt Tag.G2 K i0 u, torusElt_mem_torusGroup i0 u, fun c => ?_⟩
    rw [LieCartan.G2.torusElt_conj_gX i0 u hrC, e0, zpow_one]

end CFSG.Quasithin.H13.KG68.Singer.G2
