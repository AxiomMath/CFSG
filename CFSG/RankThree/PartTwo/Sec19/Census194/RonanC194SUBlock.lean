module

public import CFSG.LocalAnalysis.SectionRank.EvenCover.Unitary
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Core
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatch
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Extremal
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.RankThree.PartTwo.Sec19.Item194Used

public section

namespace CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary CFSG.SectionRank.EvenCover
  CFSG.LieType.BorelTits

theorem eq_one_of_blockGL_mem_statedScalars_pos {K : Type} [Field K] {a m : ℕ} (hm : 1 ≤ m)
    {g : GL (Fin a) K} (h : blockGL (m := m) g ∈ StatedScalars (Fin (a + m)) K) : g = 1 := by
  obtain ⟨c, hc⟩ := h
  have hlast := congrArg (fun M : GL (Fin (a + m)) K =>
    (M : Matrix (Fin (a + m)) (Fin (a + m)) K) (Fin.natAdd a ⟨0, hm⟩) (Fin.natAdd a ⟨0, hm⟩)) hc
  have hc1 : (c : K) = 1 := by
    simp only [coe_blockGL, blockMat, Matrix.reindex_apply, Matrix.submatrix_apply,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂, Matrix.one_apply_eq,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at hlast
    exact hlast
  apply Units.ext
  ext i j
  have := congrArg (fun M : GL (Fin (a + m)) K =>
    (M : Matrix (Fin (a + m)) (Fin (a + m)) K) (Fin.castAdd m i) (Fin.castAdd m j)) hc
  simp only [Matrix.GeneralLinearGroup.coe_scalar, coe_blockGL, blockMat_apply_castAdd,
    Matrix.scalar_apply, Matrix.diagonal_apply, Fin.castAdd_inj, hc1] at this
  rw [← this]
  simp [Matrix.one_apply]

theorem su_block_lift
    {K : Type} [Field K] [Finite K] [CharP K 2] {f a m : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2)
    (ha : 2 ≤ a) (hae : Even a) (hm : 1 ≤ m) {L : Type} [Group L] [Finite L]
    (hodd : Odd (Nat.card (Subgroup.center L)))
    (e : L ⧸ Subgroup.center L ≃* StatedProj (StatedSU (a + m) (2 ^ f) K)) :
    ∃ β : StatedSU a (2 ^ f) K →* L, Function.Injective β := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ := unitaryInvolution K 2 f
  let ι : SU σ a →* StatedSU (a + m) (2 ^ f) K :=
    (MulEquiv.subgroupCongr (SUid_eq_statedSU hK (a + m))).toMonoidHom.comp
      ((blockSUid σ).comp ((MulEquiv.subgroupCongr (SUid_eq_statedSU hK a)).symm.toMonoidHom.comp
        (equivStatedSU hK a).toMonoidHom))
  let α : SU σ a →* L ⧸ Subgroup.center L :=
    e.symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp ι)
  have hα : Function.Injective α := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    simp only [α, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
    set y := equivStatedSU hK a x with hy
    have hιx : ((ι x : StatedSU (a + m) (2 ^ f) K) : GL (Fin (a + m)) K) =
        blockGL ((y : StatedSU a (2 ^ f) K) : GL (Fin a) K) := rfl
    rw [hιx] at hx
    have hy1 : y = 1 := Subtype.ext (eq_one_of_blockGL_mem_statedScalars_pos hm hx)
    rw [Subgroup.mem_bot]
    exact (equivStatedSU hK a).injective (hy1.trans (map_one _).symm)
  have hker : (QuotientGroup.mk' (Subgroup.center L)).ker = Subgroup.center L :=
    QuotientGroup.ker_mk' _
  obtain ⟨α', hα', -⟩ := even_su_existsUnique_lift hK ha hae
    (QuotientGroup.mk'_surjective (Subgroup.center L)) hker.le (by rw [hker]; exact hodd) α
  have hα'inj : Function.Injective α' := by
    intro x y hxy
    apply hα
    rw [← hα', MonoidHom.comp_apply, MonoidHom.comp_apply, hxy]
  exact ⟨α'.comp (equivStatedSU hK a).symm.toMonoidHom,
    hα'inj.comp (equivStatedSU hK a).symm.injective⟩

end CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194
