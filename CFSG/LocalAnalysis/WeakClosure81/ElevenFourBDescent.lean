module

public import CFSG.LocalAnalysis.WeakClosure81.ElevenFourBBlocks
public import CFSG.LocalAnalysis.WeakClosure81.ElevenFourBAlt

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6 Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_centralizer_of_isTwoPow_of_mem_gammaEleven {M V U W : Subgroup G} (hUV : U ≤ V)
    (hW : W ∈ gammaEleven M V) {x : G} (hxM : x ∈ M)
    (hxW : x ∈ Subgroup.centralizer (W : Set G)) (hx : ∃ k : ℕ, orderOf x = 2 ^ k) :
    x ∈ Subgroup.centralizer (U : Set G) := by
  have h1 : x ∈ Opp 2 (M ⊓ Subgroup.centralizer (W : Set G)) :=
    Subgroup.subset_closure ⟨⟨hxM, hxW⟩, hx⟩
  exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hUV) (hW.2.2.2 h1)

theorem eleven_four_descent_B {M V Q U W Y : Subgroup G}
    (hset : Setting11 M V Q) (hUV : U ≤ V) (hW : W ∈ gammaEleven M V) (hWU : W ≤ U)
    (hY : Y ∈ elevenBlocksB M Q U) : Y ∈ elevenBlocksB M Q W := by
  have hCle : Subgroup.centralizer (U : Set G) ≤ Subgroup.centralizer (W : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hWU)
  obtain ⟨𝒢, h⟩ := exists_isBHSFamily_centralizer hset hW
  have hK : CFSG.QuasithinUnique.CharTwo (Subgroup.centralizer (W : Set G)) :=
    Setting11.charTwo_centralizer hset hW.1 hW.2.1
  have hQ : IsSylowOf 2 Q (Subgroup.centralizer (W : Set G)) :=
    eleven_two_sylow hset.isElemAbelian hset.V_le_M hset.uniqueMax hset.sylowQ hW
  have hne : cStarIn (Subgroup.centralizer (W : Set G)) Q ≠
      Subgroup.centralizer (W : Set G) :=
    Setting11.cStarIn_centralizer_ne hset hW
  obtain ⟨⟨hYB, hYnotU, hYmax⟩, hYM⟩ := hY
  have hYK : IsBTBlock (Subgroup.centralizer (W : Set G)) Q Y :=
    isBTBlock_of_le hYB (hYB.le.trans hCle)
  have hYnotC : ¬ Y ≤ cStarIn (Subgroup.centralizer (W : Set G)) Q := fun hle =>
    hYM (hle.trans (Setting11.cStarIn_le hset _))
  obtain ⟨E, hE, hYE⟩ := h.cover Y hYK hYnotC
  have hYeq : Y = E := by
    rcases h.shape E hE with ⟨⟨n, hn2, hnat⟩, -⟩ | halt
    · exact eq_of_le_linear hK hQ (h.isBlock E hE) hn2 hnat
        ⟨1, Subgroup.one_mem _, by rw [A1b.conjSub_one]; exact hYK⟩ hYE
    · have hUN : U ≤ Subgroup.normalizer (E : Set G) :=
        Setting11.le_normalizer_of_isBTBlock hset hUV (h.isBlock E hE)
      have hU2 : IsPGroup 2 U := (B2F.isPGroup_of_isElemAbelian hset.isElemAbelian).to_le hUV
      have hcent : ∀ x ∈ cStarIn (Subgroup.centralizer (W : Set G)) Q ⊓ E,
          (∃ k : ℕ, orderOf x = 2 ^ k) → x ∈ Subgroup.centralizer (U : Set G) :=
        fun x hx hkx => mem_centralizer_of_isTwoPow_of_mem_gammaEleven hUV hW
          (Setting11.cStarIn_le hset _ hx.1) (h.le hE hx.2) hkx
      have hEC : E ≤ Subgroup.centralizer (U : Set G) :=
        le_centralizer_of_alt h hK hQ hne hE halt hU2 hUN hcent hYE hYB.le hYnotC
      exact (hYmax E (isBTBlock_of_le (h.isBlock E hE) hEC) hYE).symm
  rw [mem_elevenBlocksB_iff]
  exact ⟨by rw [hYeq]; exact (IsBHSFamily.mem_iff h hK hQ).1 hE, hYM⟩

theorem isBlockOfInX_of_eleven_four_descent_B
    {M V Q U W Y : Subgroup G} (hset : Setting11 M V Q) (hUV : U ≤ V) (hW : W ∈ gammaEleven M V)
    (hWU : W ≤ U) (hY : Y ∈ elevenBlocksB M Q U) :
    IsBlockOfInX (Subgroup.centralizer (W : Set G)) Y :=
  isBlockOfInX_of_mem_elevenBlocksB hset hW (eleven_four_descent_B hset hUV hW hWU hY)

end CFSG.LocalAnalysis.WeakClosure81
