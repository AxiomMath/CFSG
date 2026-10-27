module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenThreeHigh
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenEightThreeY
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenOneMinShapeAt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem gap19_3At_holds
    (D : Data G)
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    (h68 : S17.R17_68At D V₀ V) : Gap19_3At D V₀ V p L K h := by
  intro _hm J hJ _hJV
  have hLc : L ∈ calC D.M := h.hyp.hL.1
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hLc.1
  have hL2case : IsL2 (Bar2 L) 2 → ∀ J' ∈ calC D.M, ∃ Y : Subgroup G, Y ≤ D.M ∧
      Nat.card Y = 5 ∧ (Y : Set G) * D.T = D.T * Y ∧ ⁅Y, J'⁆ ≤ pCoreOf 2 D.M :=
    fun hL2 J' hJc => by
      obtain ⟨y, hyM, hy5, hyT, -, -, hyJ⟩ := exists_five_elem_19 D h h68 hL2
      exact ⟨Subgroup.zpowers y, Subgroup.zpowers_le.2 hyM, by rw [Nat.card_zpowers, hy5], hyT,
        hyJ J' (CFSG.Quasithin.A3.subnormal_le hJc.1) hJc.2.1⟩
  rcases hJ with hJK | ⟨hJL, hL2, -⟩
  · rw [hJK]
    rcases h.shape with hL2 | hU3
    · exact hL2case hL2 K h.hK
    ·
      have hMN : D.M ≤ normalizer (L : Set G) := fun m hm =>
        Subgroup.mem_normalizer_iff_map_conj_eq.2 (map_conj_eq_self_of_isU3 D h hU3 m hm)
      have hLn : (L.subgroupOf D.M).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 hMN
      have hT : CFSG.Quasithin.IsSylowIn 2 D.T D.M :=
        (CFSG.ABGLocalTools.isSylowOf_iff (p := 2) (P := D.T) (K := D.M)).1 D.sylowM
      obtain ⟨A, hAL, hA5, -, hAT⟩ :=
        Inputs1719.exists_permutes_of_isSU3_bar2 (n := 2) (q := 5) (D.sylowM.le.trans hMN)
          (CFSG.Quasithin.IsSylowIn.inf_normal hT hLM hLn) (uc22p22d_isSU3_of_isU3 hLc.2.2 hU3)
          Nat.prime_five (by norm_num) (by norm_num)
      have hLK : ⁅L, K⁆ ≤ pCoreOf 2 D.M :=
        ((calC_commutator_le_of_ne hLc h.hK (Ne.symm h.hne)).trans inf_le_left).trans
          (UC22.P22s.pCoreOf_le_of_isSubnormal hLc.1)
      exact ⟨A, hAL.trans hLM, hA5, hAT, (Subgroup.commutator_mono hAL le_rfl).trans hLK⟩
  · rw [hJL]
    exact hL2case hL2 L hLc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
