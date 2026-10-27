module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs
import CFSG.RankThree.GroupTheory.SteinbergCEAlternatingDegreeThirteen
import CFSG.LocalAnalysis.UniquenessCase.UC6K620Fi22Cover
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFi22
import CFSG.RankThree.PartOne.S11b.Sec109SixFiveArith
public import CFSG.Sporadic.Fi22.Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.RankThree.GroupTheory
  (alternating_central_covers_degree_thirteen_force_two_local_three_rank_four)

theorem coverHasLargeTwoLocal_of_mulEquiv_alternatingGroup {L : Type*} [Group L] {n : ℕ}
    (hn : 13 ≤ n) (e : L ≃* alternatingGroup (Fin n)) : CoverHasLargeTwoLocal L := by
  intro J' _ _ _ φ hφ hZ _
  let π : (⊤ : Subgroup J') →* alternatingGroup (Fin n) :=
    (e : L →* alternatingGroup (Fin n)).comp (φ.comp (⊤ : Subgroup J').subtype)
  have hπ : Function.Surjective π :=
    e.surjective.comp (hφ.comp fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
  have hπker : π.ker ≤ Subgroup.center (⊤ : Subgroup J') := by
    intro x hx
    have hxφ : φ (x : J') = 1 := e.injective (by simpa [π] using MonoidHom.mem_ker.1 hx)
    exact Subgroup.mem_center_iff.2 fun y =>
      Subtype.ext ((Subgroup.mem_center_iff.1 (hZ hxφ)) (y : J'))
  obtain ⟨U, V, -, hU, hU2, hVN, hV, hVcard⟩ :=
    (alternating_central_covers_degree_thirteen_force_two_local_three_rank_four
      (G := J') (K := ⊤) (n := n) π hπ hπker).1 hn
  exact ⟨U, hU, hU2, CFSG.SectionRank.le_pRank (by norm_num) (hVN.trans inf_le_right)
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 V).1 hV) hVcard⟩

theorem coverHasLargeTwoLocal_of_isFi22
    {L : Type} [Group L] (hs : IsSimpleGroup L)
    (hL : CFSG.AGLEmbedding.IsFi22 L) : CoverHasLargeTwoLocal L := by
  intro J' _ _ _ φ hφ hZ hodd
  obtain ⟨eL⟩ := CFSG.AGLEmbedding.KFactProofs.SmallIdent.nonempty_equiv_fi22 hs hL
  let e : L ≃* CFSG.Sporadic.Fi22.J := eL.trans CFSG.Sporadic.Fi22.fi22EquivJ
  let ψ : (⊤ : Subgroup J') →* CFSG.Sporadic.Fi22.J :=
    (e : L →* CFSG.Sporadic.Fi22.J).comp (φ.comp (⊤ : Subgroup J').subtype)
  have hψ : Function.Surjective ψ :=
    e.surjective.comp (hφ.comp fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
  have hker : ψ.ker = φ.ker.subgroupOf (⊤ : Subgroup J') := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, ← MonoidHom.comap_ker,
      Subgroup.comap_subtype]
  have hψker : ψ.ker ≤ Subgroup.center (⊤ : Subgroup J') := by
    intro x hx
    have hxφ : φ (x : J') = 1 :=
      MonoidHom.mem_ker.1 ((Subgroup.mem_subgroupOf).1 (hker ▸ hx))
    exact Subgroup.mem_center_iff.2 fun y =>
      Subtype.ext ((Subgroup.mem_center_iff.1 (hZ hxφ)) (y : J'))
  have hψodd : Odd (Nat.card ψ.ker) := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_top).toEquiv]
    exact hodd
  have hrank : 4 ≤ localRank 3 J' :=
    CFSG.LocalAnalysis.UniquenessCase.UCK.four_le_localRank_three_of_fi22_cover
      (G := J') (K := ⊤) ψ hψ hψker hψodd
  obtain ⟨U, hU2, hU, E, hEN, hE, hEcard⟩ :=
    CFSG.RankThree.PartOne.Sec109.exists_elementary_abelian_of_le_localRank
      (G := J') (p := 3) (k := 4) Nat.prime_three (by norm_num) hrank
  exact ⟨U, hU, hU2, CFSG.SectionRank.le_pRank (by norm_num) hEN
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).1 hE) hEcard⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
