module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveDefs
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveIa

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G} {g : G} {X T : Subgroup G}

theorem Hyp167.le_pCoreOf_X (h1 : W16One G) (hS : Std15 G) (hX : Hyp167 M V₀ V U S H g X T)
    (hVO : V ≤ pCoreOf 2 H) : V ≤ pCoreOf 2 X ∧ V ≤ kerMOf M X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2S : pCoreOf 2 H ≤ S := Cex16.pCoreOf_le_S h1 hS hX.cex hX.min.1
  have hO2M : pCoreOf 2 H ≤ M := hO2S.trans hX.cex.S_le_M
  have hO2H : pCoreOf 2 H ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hO2normH : ((pCoreOf 2 H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hO2H).2
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  have hO2KH : pCoreOf 2 H ≤ kerMOf M H := le_kerMOf_of_normal hO2H hO2normH hO2M
  obtain ⟨P, hPsyl, hPK⟩ := hX.mem.2.1
  have hO2normKH : ((pCoreOf 2 H).subgroupOf (kerMOf M H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hO2KH).2
      ((kerMOf_le_group M H).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
  have hO2P : pCoreOf 2 H ≤ P :=
    hPsyl.le_of_normal hO2KH hO2normKH (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
  have hO2KX : pCoreOf 2 H ≤ kerMOf M X := hO2P.trans hPK
  have hO2X : pCoreOf 2 H ≤ X := hO2KX.trans (kerMOf_le_group M X)
  have hO2normX : ((pCoreOf 2 H).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hO2X).2
      (hX.mem.1.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
  have hO2pcX : pCoreOf 2 H ≤ pCoreOf 2 X :=
    le_pCoreOf_of_isPGroup_of_normal hO2X hO2normX
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
  exact ⟨hVO.trans hO2pcX, hVO.trans hO2KX⟩

theorem Hyp167.isElemAbelian_I (h1 : W16One G) (hS : Std15 G) (hX : Hyp167 M V₀ V U S H g X T)
    (hVO : V ≤ pCoreOf 2 H) : IsElemAbelian 2 (conjClosure V X) :=
  CFSG.Open.IsElemAbelian.mono (Cex16.isElemAbelian_iSub16 h1 hS hX.cex hX.min.1)
    (conjClosure_mono (le_inf le_rfl hVO) hX.mem.1)

theorem Hyp167.not_mem_M (h1 : W16One G) (hS : Std15 G) (hX : Hyp167 M V₀ V U S H g X T)
    (hVO : V ≤ pCoreOf 2 H) : g ∉ M := by
  intro hgM
  have hgN : g ∈ normalizer (V : Set G) := by
    rw [hX.cex.hyp.h6.normalizer_eq]
    exact hgM
  have hconj : conjSubgroup V g = V := conjSubgroup_eq_iff_mem_normalizer.2 hgN
  have hVK : V ≤ kerMOf M X := (Hyp167.le_pCoreOf_X h1 hS hX hVO).2
  exact hX.mem.2.2.not_le_ker (by rwa [hconj])

theorem Hyp167.quad_of_le_conjSubgroup_M (hX : Hyp167 M V₀ V U S H g X T)
    (hIA : conjClosure V X ≤ conjSubgroup M g) :
    ∀ a ∈ conjSubgroup V g, ∀ b ∈ conjSubgroup V g, ∀ e ∈ conjClosure V X,
      a * (b * e * b⁻¹ * e⁻¹) * a⁻¹ = b * e * b⁻¹ * e⁻¹ := by
  intro a ha b hb e he
  have hAab : IsElemAbelian 2 (conjSubgroup V g) :=
    E3.isElemAbelian_conjSubgroup hX.cex.hyp.h6.elemAbelian g
  have hnorm : conjSubgroup M g = normalizer (conjSubgroup V g : Set G) := by
    rw [← E3.conjSubgroup_normalizer, hX.cex.hyp.h6.normalizer_eq]
  have heN : e ∈ normalizer (conjSubgroup V g : Set G) := hnorm ▸ hIA he
  have hcomm : b * e * b⁻¹ * e⁻¹ ∈ conjSubgroup V g := by
    have h1 : e * b⁻¹ * e⁻¹ ∈ conjSubgroup V g :=
      (Subgroup.mem_normalizer_iff.1 heN b⁻¹).1 (Subgroup.inv_mem _ hb)
    have h2 : b * (e * b⁻¹ * e⁻¹) ∈ conjSubgroup V g :=
      (conjSubgroup V g).mul_mem hb h1
    simpa [mul_assoc] using h2
  have hcommute : a * (b * e * b⁻¹ * e⁻¹) = (b * e * b⁻¹ * e⁻¹) * a :=
    B2F.isElemAbelian_comm hAab ha hcomm
  calc a * (b * e * b⁻¹ * e⁻¹) * a⁻¹
      = (b * e * b⁻¹ * e⁻¹) * a * a⁻¹ := by rw [hcommute]
    _ = b * e * b⁻¹ * e⁻¹ := by group

theorem Hyp167.inf_centralizer_eq (hX : Hyp167 M V₀ V U S H g X T) {Y : Subgroup G} (hYX : Y ≤ X)
    (hYM : ¬ Y ≤ M) : V ⊓ centralizer (Y : Set G) = U := by
  have hUY : U ≤ Subgroup.centralizer (Y : Set G) :=
    Subgroup.le_centralizer_iff.2 ((hYX.trans hX.mem.1).trans hX.min.1.2.1)
  let W : Subgroup G := V ⊓ Subgroup.centralizer (Y : Set G)
  have hW : W = V ⊓ Subgroup.centralizer (Y : Set G) := rfl
  have hUW : U ≤ W := by rw [hW]; exact le_inf hX.cex.le hUY
  have hWV : W ≤ V := by rw [hW]; exact inf_le_left
  have hYW : Y ≤ Subgroup.centralizer (W : Set G) :=
    Subgroup.le_centralizer_iff.2 (hW.le.trans inf_le_right)
  have hnot : ¬ Subgroup.centralizer (W : Set G) ≤ M := fun hle => hYM (hYW.trans hle)
  have hq1 : (E3.mQuot V U : ℕ∞) ≤ (E3.mQuot V W : ℕ∞) := by
    rw [hX.cex.mquot]
    exact rMV_le_mQuot M V W hWV hnot
  have hq2 : E3.mQuot V W ≤ E3.mQuot V U := E3.mQuot_mono hUW
  have hq : E3.mQuot V W = E3.mQuot V U := le_antisymm hq2 (by exact_mod_cast hq1)
  have hV2 : IsPGroup 2 V := hX.cex.hyp.h6.elemAbelian.isPGroup
  have hcard : Nat.card W = Nat.card U := by
    have e1 := E3.card_eq_two_pow_mul hV2 hWV
    have e2 := E3.card_eq_two_pow_mul hV2 hX.cex.le
    rw [hq] at e1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) (e1.symm.trans e2)
  have hWU : W = U := (Subgroup.eq_of_le_of_card_ge hUW (le_of_eq hcard)).symm
  rw [← hW]
  exact hWU

end CFSG.LocalAnalysis.WeakClosure81

end
