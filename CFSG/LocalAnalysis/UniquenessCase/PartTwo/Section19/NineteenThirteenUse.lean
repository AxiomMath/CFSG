module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenSeventeen
public import CFSG.GroupTheory.ElemAbelianRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem commute_of_concl19_13 {D : Data G} {A : Subgroup G} (h13 : Concl19_13 D A)
    (h3 : 3 ∈ piSet A) {Q : Subgroup G} (hQ : IsPGroup 3 Q) {x y : G} (hxQ : x ∈ Q)
    (hx : x ^ 3 = 1) (hyQ : y ∈ Q) (hy : y ^ 3 = 1) : x * y = y * x := by
  have hc := omegaOne_comm_of_concl19_13 h13 h3 hQ
  exact congrArg Subtype.val (hc.is_comm.comm ⟨x, Subgroup.subset_closure ⟨hxQ, hx⟩⟩
    ⟨y, Subgroup.subset_closure ⟨hyQ, hy⟩⟩)

theorem card_le_27_of_concl19_13 {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (h13 : Concl19_13 D A) (h3 : 3 ∈ piSet A) {X : Subgroup G} (hX : IsElemAbelian 3 X) :
    Nat.card X ≤ 27 := by
  classical
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 D.M
  obtain ⟨hPG, -⟩ := h13 h3 P hP
  have hcard : Nat.card P = 3 ^ (Nat.card G).factorization 3 := by
    rw [hPG.card_eq, Subgroup.card_top]
  let P' : Sylow 3 G := Sylow.ofCard P hcard
  have hXp : IsPGroup 3 X := CFSG.Open.IsElemAbelian.isPGroup hX
  obtain ⟨Q', hXQ'⟩ := hXp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q' P'
  have hXgP : X.map (MulAut.conj g).toMonoidHom ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (MulAut.conj g).toMonoidHom x ∈ ((g • Q' : Sylow 3 G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ (hXQ' hx)
    rw [hg] at hx'
    exact hx'
  have hPM : P ≤ D.M := hP.le
  have hXel' : IsElemAbelian 3 (X.map (MulAut.conj g).toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hX _
  have hcardX : Nat.card X = 3 ^ CFSG.Open.pRank 3 X :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_three hX
  have hcardXg : Nat.card (X.map (MulAut.conj g).toMonoidHom) = 3 ^ CFSG.Open.pRank 3 X := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcardX]
  have hle1 : CFSG.Open.pRank 3 X ≤ CFSG.Open.pRank 3 D.M :=
    CFSG.SectionRank.le_pRank (by norm_num) (hXgP.trans hPM) hXel' hcardXg
  have hle2 : CFSG.Open.pRank 3 D.M ≤ evenRank G :=
    CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3 Nat.prime_three
      (by norm_num) D.M D.maxLocal.1
  have hev : evenRank G = 3 := evenRank_eq_three_of_ctx h
  rw [hcardX]
  calc 3 ^ CFSG.Open.pRank 3 X ≤ 3 ^ 3 :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 27 := by norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
