module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitaryBlock
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Unitary
import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.GroupTheory.WeirSylow.GL
public import CFSG.GroupTheory.WeirSylow.UnitaryBridge
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLInner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5SU2
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open

theorem exists_blkSU_lift
    {X : Type} [Group X] [Finite X] {m n : ℕ} (hm : 4 ≤ m) {F₀ : Type} [Field F₀] [Finite F₀]
    (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n F₀)
    (e : (X ⧸ Subgroup.center X) ≃* StatedProj (StatedSU m (2 ^ n) F₀))
    (hodd : Odd (Nat.card (Subgroup.center X))) :
    ∃ α : ↥(StatedSU 3 (2 ^ n) F₀) →* X,
      (∀ h, e (QuotientGroup.mk (α h)) =
        (QuotientGroup.mk (CFSG.OddStandard.GH71.S55.C5U.blkSU hU 0 (by omega) h) :
          StatedProj (StatedSU m (2 ^ n) F₀))) ∧
      ∀ h, α h ∈ commutator X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F₀ 2 := hU.charP
  have hK : Nat.card F₀ = (2 ^ n) ^ 2 := by rw [hU.card, ← pow_mul, mul_comm]
  let B4 : StatedSU 4 (2 ^ n) F₀ →* StatedSU m (2 ^ n) F₀ :=
    CFSG.OddStandard.GH71.S55.C5U.blkSU hU 0 (show 0 + 4 ≤ m by omega)
  let B34 : StatedSU 3 (2 ^ n) F₀ →* StatedSU 4 (2 ^ n) F₀ :=
    CFSG.OddStandard.GH71.S55.C5U.blkSU hU 0 (show 0 + 3 ≤ 4 by omega)
  let E4 : CFSG.LieType.Universal.Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution F₀ 2 n) 4 ≃* StatedSU 4 (2 ^ n) F₀ :=
    CFSG.LieType.Universal.Unitary.equivStatedSU (p := 2) (f := n) hK 4
  let ι : CFSG.LieType.Universal.Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution F₀ 2 n) 4 →* X ⧸ Subgroup.center X :=
    e.symm.toMonoidHom.comp
      ((QuotientGroup.mk' ((StatedScalars (Fin m) F₀).subgroupOf
        (StatedSU m (2 ^ n) F₀))).comp (B4.comp E4.toMonoidHom))
  have hker : (QuotientGroup.mk' (Subgroup.center X)).ker = Subgroup.center X :=
    QuotientGroup.ker_mk' _
  obtain ⟨α', hα', -⟩ :=
    CFSG.SectionRank.EvenCover.even_su_existsUnique_lift (F := F₀) (f := n) hK
      (by norm_num) (by norm_num : Even 4)
      (QuotientGroup.mk'_surjective (Subgroup.center X)) (le_of_eq hker)
      (by rw [hker]; exact hodd) ι
  let β : StatedSU 4 (2 ^ n) F₀ →* X := α'.comp E4.symm.toMonoidHom
  let α : StatedSU 3 (2 ^ n) F₀ →* X := β.comp B34
  refine ⟨α, ?_, ?_⟩
  · intro h
    have hblock : B4 (B34 h) =
        CFSG.OddStandard.GH71.S55.C5U.blkSU hU 0 (show 0 + 3 ≤ m by omega) h := by
      apply Subtype.ext
      apply Units.ext
      dsimp only [B4, B34]
      simp only [CFSG.OddStandard.GH71.S55.C5U.coe_blkSU,
        CFSG.ClassicalInvolution.Phan.coe_blockGL]
      exact blockMat_blockMat_zero (by norm_num : 3 ≤ 4) _
    have hmk : QuotientGroup.mk (α h) = e.symm (QuotientGroup.mk (B4 (B34 h))) := by
      calc QuotientGroup.mk (α h)
          = QuotientGroup.mk' (Subgroup.center X) (α' (E4.symm (B34 h))) := rfl
        _ = ι (E4.symm (B34 h)) := DFunLike.congr_fun hα' _
        _ = e.symm (QuotientGroup.mk (B4 (E4 (E4.symm (B34 h))))) := rfl
        _ = e.symm (QuotientGroup.mk (B4 (B34 h))) := by rw [MulEquiv.apply_symm_apply]
    rw [hmk, MulEquiv.apply_symm_apply, hblock]
  · intro h
    have hperf : Group.IsPerfect (StatedSU 4 (2 ^ n) F₀) :=
      CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (K := F₀) (p := 2) (f := n)
        (n := 4) hK (by norm_num) (by simp)
    have hmem : B34 h ∈ (⁅(⊤ : Subgroup (StatedSU 4 (2 ^ n) F₀)),
        (⊤ : Subgroup (StatedSU 4 (2 ^ n) F₀))⁆) := by
      rw [← commutator_def, hperf.commutator_eq_top]
      exact Subgroup.mem_top _
    have hcomm : β (B34 h) ∈ (⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆) := by
      apply Subgroup.commutator_mono le_top le_top
      rw [← Subgroup.map_commutator (f := β)]
      exact Subgroup.mem_map_of_mem β hmem
    rw [commutator_def]
    exact hcomm

end CFSG.LocalAnalysis.WeakClosure81

end
