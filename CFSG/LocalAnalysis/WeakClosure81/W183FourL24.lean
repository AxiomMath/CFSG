module

public import CFSG.LocalAnalysis.WeakClosure81.W183FourDefs
public import CFSG.LocalAnalysis.WeakClosure81.W183FourConj
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Master1
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Master2
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Comp2
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Base
public import CFSG.LocalAnalysis.WeakClosure81.W18Asch5
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
import CFSG.LocalAnalysis.WeakClosure81.W18KernBridge
import CFSG.LocalAnalysis.WeakClosure81.W183L312
import CFSG.LocalAnalysis.WeakClosure81.W183L313
import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)

variable {G : Type} [Group G] [Finite G]

section Certified


private theorem w183four24_card_psl_2_2_2 {X : Type} [Group X] (h : IsL2 X 2) :
    Nat.card X = 60 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_four
    (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide))

private theorem w183four24_card_psu_3_2_2 {X : Type} [Group X] (h : IsU3 X 2) :
    Nat.card X = 62400 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_four
    (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide))

private theorem w183four24_nonab_of_simple_of_card {X : Type} [Group X] (hs : IsSimpleGroup X)
    {n : ℕ} (hcard : Nat.card X = n) (hn : ¬ n.Prime) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hnab
  have hcomm : IsMulCommutative X := IsMulCommutative.of_comm (fun a b => by
    by_contra hab
    exact hnab ⟨a, b, hab⟩)
  letI : IsMulCommutative X := hcomm
  have hp : (Nat.card X).Prime := CommGroup.is_simple_iff_prime_card.mp hs
  rw [hcard] at hp
  exact hn hp

private theorem w183four24_simple_nonab_of_shape {X : Type} [Group X]
    (h : IsL2 X 2 ∨ IsU3 X 2) :
    IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  rcases h with h2 | h3
  · have hs := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h2
    exact ⟨hs, w183four24_nonab_of_simple_of_card hs (w183four24_card_psl_2_2_2 h2)
      (by norm_num)⟩
  · have hs := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h3
    exact ⟨hs, w183four24_nonab_of_simple_of_card hs (w183four24_card_psu_3_2_2 h3)
      (by norm_num)⟩

theorem w183four24_three_dvd (hO : LieOrderFormulasInput) {K L : Subgroup G}
    (hX : HasQuotShape L (K : Set G) (fun X _ => IsL2 X 2 ∨ IsU3 X 2)) :
    3 ∣ K.relIndex L := by
  obtain ⟨X, hXg, φ, hs, hk, hP⟩ := hX
  have hker : φ.ker = K.subgroupOf L := by
    ext k
    rw [MonoidHom.mem_ker, hk k, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hs,
    Subgroup.card_top]
  rcases hP with h2 | h3
  · rw [w183four24_card_psl_2_2_2 h2]
    norm_num
  · rw [w183four24_card_psu_3_2_2 h3]
    norm_num

theorem w183four_conj_cases_of_dvd (h210 : Asch2_10)
    {D : Data G} {V₀ V H : Subgroup G} {i : ℕ} (c : MinCex183 D V₀ V H i)
    (h2 : ¬ Concl182 D V₀ V H i) {L : Subgroup G}
    (hL : IsComponentModN (kerMV V H) H L) (hLT : L ⊔ D.T = H)
    (h3 : 3 ∣ (kerMV V H).relIndex L) :
    (∀ t ∈ D.T, conjSubgroup L t = L) ∨
      ∃ t ∈ D.T, conjSubgroup L t ≠ L ∧
        ∀ s ∈ D.T, conjSubgroup L s = L ∨ conjSubgroup L s = conjSubgroup L t := by
  have hr : CFSG.Open.pRank 3 H ≤ 3 := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank 3 H]
    exact (not_concl182_iff.mp h2).1.1
  exact w183four_conj_cases
    (h210 G H D.T (kerMV V H) L c.hyp.kgroup c.hyp.isSylowIn_T hr hL h3 hLT)

theorem w183four24_conj_cases (hO : LieOrderFormulasInput) (h210 : Asch2_10)
    {D : Data G} {V₀ V H : Subgroup G} {i : ℕ} (c : MinCex183 D V₀ V H i)
    (h2 : ¬ Concl182 D V₀ V H i) {L : Subgroup G}
    (hL : IsComponentModN (kerMV V H) H L) (hLT : L ⊔ D.T = H)
    (hX : HasQuotShape L (kerMV V H : Set G) (fun X _ => IsL2 X 2 ∨ IsU3 X 2)) :
    (∀ t ∈ D.T, conjSubgroup L t = L) ∨
      ∃ t ∈ D.T, conjSubgroup L t ≠ L ∧
        ∀ s ∈ D.T, conjSubgroup L s = L ∨ conjSubgroup L s = conjSubgroup L t :=
  w183four_conj_cases_of_dvd h210 c h2 hL hLT (w183four24_three_dvd hO hX)

theorem w183four24_one_comp (rows : Br1Rows) {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}
    (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    (hN : calNIn H D.T = {H ⊓ D.M})
    (hK : kerMV V H ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G)) {L : Subgroup G}
    (hLH : L ≤ H) (hLn : H ≤ Subgroup.normalizer (L : Set G)) (hLT : L ⊔ D.T = H)
    (hX : HasQuotShape L (kerMV V H : Set G) (fun X _ => IsL2 X 2 ∨ IsU3 X 2)) {g : G}
    (hgT : vInH V H g ≤ D.T) (hgK : ¬ vInH V H g ≤ kerMV V H)
    (hgi : E3.mQuot (conjSubgroup V g) (vInH V H g) ≤ i)
    (hA : 3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g)) :
    False := by
  classical
  have hQ : HasQuotShape L (kerMV V H : Set G)
      (fun X _ => IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a) := by
    obtain ⟨X, hXg, φ, hs, hk, hP⟩ := hX
    exact ⟨X, hXg, φ, hs, hk, w183four24_simple_nonab_of_shape hP⟩
  have hbase := x.br1_comp_base M hK hLH hLn hLT hQ
  have hsh : IsL2 ↥(M.img L) 2 ∨ IsU3 ↥(M.img L) 2 :=
    x.br1_shape_transport M hK hLH
      (fun X Y _ _ e h => h.elim (fun h2 => Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h2))
        (fun h3 => Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e h3))) hX
  have hgam : Gam183 V H (eOmegaZ H D.T) i g := ⟨hgi, fun hle =>
    hgK ((le_inf inf_le_right hle).trans x.hyp.inf_centralizer_eOmegaZ_le_kerMV)⟩
  have hab : IsElemAbelian 2 (vInH V H g) :=
    (E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g).mono inf_le_left
  obtain ⟨-, hA4⟩ := four_le_card_img M inf_le_right hab hA
  have hAH : M.img (vInH V H g) ≤ M.img H := M.img_mono inf_le_right
  have hA4' : 4 ≤ Nat.card ↥(M.img (vInH V H g)) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv) ▸ hA4
  have hAmem : M.img (vInH V H g) ∈ Ctx188.packFamilyU D V H i M := ⟨g, hgam, rfl⟩
  rcases br1_master_one_small rows (x.br2Common M hN) hbase.1 hbase.2.1 hbase.2.2.1
      hbase.2.2.2.1 hbase.2.2.2.2 hsh hAmem hA4' with
    ⟨hL2, A, hAm, hAT, hsyl⟩ | ⟨hU3, A, hAm, hAT, S, hSsyl, hAeq⟩
  · obtain ⟨g', hg', hg'T, hAeq⟩ := x.w183l31_exists_member_le_T M hAm hAT
    exact false_of_L24_member x M hLH hLn hLT hL2 hg' hg'T (hAeq ▸ hsyl)
  · obtain ⟨g', hg', hg'T, hAeq'⟩ := x.w183l31_exists_member_le_T M hAm hAT
    exact false_of_U34_member x M hLH hLn hLT hbase.2.2.2.2 hU3 hg' hg'T
      (hAeq' ▸ ⟨S, hSsyl, hAeq⟩)

theorem w183four24_two_comp (rows : Br1Rows) {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}
    (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    (hN : calNIn H D.T = {H ⊓ D.M})
    (hK : kerMV V H ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G)) {L : Subgroup G}
    (hL : IsComponentModN (kerMV V H) H L) (hLT : L ⊔ D.T = H)
    (hX : HasQuotShape L (kerMV V H : Set G) (fun X _ => IsL2 X 2)) {t : G} (htT : t ∈ D.T)
    (hne : conjSubgroup L t ≠ L)
    (hall : ∀ s ∈ D.T, conjSubgroup L s = L ∨ conjSubgroup L s = conjSubgroup L t) {g : G}
    (hgT : vInH V H g ≤ D.T) (hgK : ¬ vInH V H g ≤ kerMV V H)
    (hgi : E3.mQuot (conjSubgroup V g) (vInH V H g) ≤ i)
    (hA : 3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g)) :
    False := by
  classical
  have hQ : HasQuotShape L (kerMV V H : Set G)
      (fun X _ => IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a) := by
    obtain ⟨X, hXg, φ, hs, hk, hP⟩ := hX
    exact ⟨X, hXg, φ, hs, hk, w183four24_simple_nonab_of_shape (Or.inl hP)⟩
  have hsh : IsL2 ↥(M.img L) 2 :=
    x.br1_shape_transport M hK hL.2.2.1
      (fun X Y _ _ e h => CFSG.Blueprint.LieModel.of_mulEquiv e h) hX
  have htwo := x.br1_twoComp M hK hL hLT hQ htT hne hall
  have hgam : Gam183 V H (eOmegaZ H D.T) i g := ⟨hgi, fun hle =>
    hgK ((le_inf inf_le_right hle).trans x.hyp.inf_centralizer_eOmegaZ_le_kerMV)⟩
  have hab : IsElemAbelian 2 (vInH V H g) :=
    (E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g).mono inf_le_left
  obtain ⟨-, hA4⟩ := four_le_card_img M inf_le_right hab hA
  have hAH : M.img (vInH V H g) ≤ M.img H := M.img_mono inf_le_right
  have hA4' : 4 ≤ Nat.card ↥(M.img (vInH V H g)) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv) ▸ hA4
  have hAmem : M.img (vInH V H g) ∈ Ctx188.packFamilyU D V H i M := ⟨g, hgam, rfl⟩
  exact br1_master_two_small rows (x.br2Common M hN) htwo hsh hAmem hA4'

theorem tail1812FourL24U34_of_masters (hO : LieOrderFormulasInput) (rows : Br1Rows)
    (h210 : Asch2_10) (hU : FourU34Two G) : Tail1812FourL24U34 G := by
  intro h162 h172 h5_4 h5_11 h5_12 h5_13 D V₀ V H i c h2 hK hshape g hgT hgK hgi hA
  obtain ⟨L, hL, hLT, hX⟩ := hshape
  have hLH : L ≤ H := hL.2.2.1
  have x : Ctx188 D V₀ V H i 3 := c.ctx188_three_AS h162 h5_11 h2
  obtain ⟨M⟩ := exists_modDataE c.hyp.isElemAbelian_eOmegaZ (Hyp183.normalizer_eOmegaZ H D.T)
  have hN : calNIn H D.T = {H ⊓ D.M} := c.calNIn_eq_AS h5_11 h5_13
  rcases w183four24_conj_cases hO h210 c h2 hL hLT hX with hn | ⟨t, htT, hne, hall⟩
  · have hLn : H ≤ Subgroup.normalizer (L : Set G) := w183four_le_normalizer hLT hn
    exact w183four24_one_comp rows x M hN hK hLH hLn hLT hX hgT hgK hgi hA
  · obtain ⟨X, hXg, φ, hs, hk, hP⟩ := hX
    rcases hP with h2' | h3'
    · exact w183four24_two_comp rows x M hN hK hL hLT ⟨X, hXg, φ, hs, hk, h2'⟩ htT hne hall
        hgT hgK hgi hA
    · exact hU h162 h172 h5_4 h5_11 h5_12 h5_13 c h2 hK
        ⟨L, hL, hLT, ⟨X, hXg, φ, hs, hk, h3'⟩, t, htT, hne⟩ hgT hgK hgi hA

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
