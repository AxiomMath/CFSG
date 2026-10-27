module

public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Master1
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Master2
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Comp2
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Base
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
import CFSG.LocalAnalysis.WeakClosure81.W183B2ED
import CFSG.LocalAnalysis.WeakClosure81.W18KernBridge
import CFSG.LocalAnalysis.WeakClosure81.W183Br1ShapeAux1
import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Sp44Main
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lieOrderNumerator lieOrderDivisor)

variable {G : Type} [Group G] [Finite G]

private theorem w183fourbig_card_alt6 {X : Type} [Group X] (h : IsAlt X 6) :
    Nat.card X = 360 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  norm_num

private theorem w183fourbig_card_PSL_3_2_1 {T : Type} [Group T] (hO : LieOrderFormulasInput)
    (h : CFSG.Blueprint.LieModel T .PSL 3 2 1) : Nat.card T = 168 := by
  obtain ⟨-, hM, -⟩ := hO T .PSL 3 2 1 h.admissible h
  have hd : lieOrderDivisor .PSL 3 (2 ^ 1) = 1 := by decide
  rw [hd, mul_one] at hM
  rw [hM]
  simp [lieOrderNumerator, show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair]

private theorem w183fourbig_card_PSL_3_2_2 {T : Type} [Group T] (hO : LieOrderFormulasInput)
    (h : CFSG.Blueprint.LieModel T .PSL 3 2 2) : Nat.card T = 20160 := by
  obtain ⟨-, hM, -⟩ := hO T .PSL 3 2 2 h.admissible h
  have hd : lieOrderDivisor .PSL 3 (2 ^ 2) = 3 := by decide
  rw [hd] at hM
  have hnum : lieOrderNumerator .PSL 3 (2 ^ 2) = 60480 := by
    simp [lieOrderNumerator, show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair]
  rw [hnum] at hM
  omega

private theorem w183fourbig_card_PSp_2_2_2 {T : Type} [Group T] (hO : LieOrderFormulasInput)
    (h : CFSG.Blueprint.LieModel T .PSp 2 2 2) : Nat.card T = 979200 := by
  obtain ⟨-, hM, -⟩ := hO T .PSp 2 2 2 h.admissible h
  have hd : lieOrderDivisor .PSp 2 (2 ^ 2) = 1 := by decide
  rw [hd, mul_one] at hM
  rw [hM]
  simp [lieOrderNumerator, show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair]

private theorem w183fourbig_nonab_of_simple_of_card {X : Type} [Group X] (hs : IsSimpleGroup X)
    {n : ℕ} (hcard : Nat.card X = n) (hn : ¬ n.Prime) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hnab
  have hcomm : IsMulCommutative X := IsMulCommutative.of_comm (fun a b => by
    by_contra hab
    exact hnab ⟨a, b, hab⟩)
  letI : IsMulCommutative X := hcomm
  have hp : (Nat.card X).Prime := CommGroup.is_simple_iff_prime_card.mp hs
  rw [hcard] at hp
  exact hn hp

private theorem w183fourbig_simple_nonab_of_shape {X : Type} [Group X]
    (h : IsAlt X 6 ∨ IsL3 X 1 ∨ IsL3 X 2 ∨ IsSp4 X 2) :
    IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  rcases h with hAlt | hL31 | hL32 | hSp
  · obtain ⟨e⟩ := hAlt
    have hs : IsSimpleGroup X :=
      (MulEquiv.isSimpleGroup_congr e).mpr (alternatingGroup.isSimpleGroup (by simp))
    exact ⟨hs, w183fourbig_nonab_of_simple_of_card hs (w183fourbig_card_alt6 ⟨e⟩)
      (by norm_num)⟩
  · have hs : IsSimpleGroup X :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL31
    have hcard : Nat.card X = 168 :=
      CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two
        (CFSG.Blueprint.LieModel.statedClassicalModel hL31 (by decide))
    exact ⟨hs, w183fourbig_nonab_of_simple_of_card hs hcard (by norm_num)⟩
  · have hs : IsSimpleGroup X :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL32
    exact ⟨hs, w183_exists_mul_ne_of_isL3_two hL32⟩
  · have hs : IsSimpleGroup X :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hSp
    have hcard : Nat.card X = 979200 :=
      CFSG.ComponentClassification.GSThmB.CF23I.card_of_lieModel_Sp44 hSp
    exact ⟨hs, w183fourbig_nonab_of_simple_of_card hs hcard (by norm_num)⟩

private theorem w183fourbig_shape_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsAlt X 6 ∨ IsL3 X 1 ∨ IsL3 X 2 ∨ IsSp4 X 2) :
    IsAlt Y 6 ∨ IsL3 Y 1 ∨ IsL3 Y 2 ∨ IsSp4 Y 2 := by
  rcases h with hAlt | hL31 | hL32 | hSp
  · exact Or.inl ⟨e.symm.trans hAlt.some⟩
  · exact Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e hL31))
  · exact Or.inr (Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e hL32)))
  · exact Or.inr (Or.inr (Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e hSp)))

private theorem w183fourbig_two_le_mRank_of_mem {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}
    (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    (hbig : ∀ g' : G, Gam183 V H (eOmegaZ H D.T) i g' →
      3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g'))
    {A : Subgroup (LGL 2 M.W)} (hA : A ∈ Ctx188.packFamilyU D V H i M) :
    2 ≤ mRank A := by
  obtain ⟨g', hgam, rfl⟩ := hA
  have hab : IsElemAbelian 2 (vInH V H g') :=
    (E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g').mono inf_le_left
  obtain ⟨-, hA4⟩ := four_le_card_img M inf_le_right hab (hbig g' hgam)
  have hAH : M.img (vInH V H g') ≤ M.img H := M.img_mono inf_le_right
  have hA4' : 4 ≤ Nat.card ↥(M.img (vInH V H g')) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv) ▸ hA4
  have hp : 2 ^ 2 ≤ Nat.card ↥(M.img (vInH V H g')) := by simpa using hA4'
  have hlog := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hp
  simpa only [mRank] using hlog

theorem w183four_big_three_dvd (hO : LieOrderFormulasInput) {K L : Subgroup G}
    (hX : HasQuotShape L (K : Set G)
      (fun X _ => IsAlt X 6 ∨ IsL3 X 1 ∨ IsL3 X 2 ∨ IsSp4 X 2)) : 3 ∣ K.relIndex L := by
  obtain ⟨X, hXg, φ, hs, hk, hP⟩ := hX
  have hker : φ.ker = K.subgroupOf L := by
    ext k
    rw [MonoidHom.mem_ker, hk k, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hs,
    Subgroup.card_top]
  rcases hP with hAlt | hL31 | hL32 | hSp
  · rw [w183fourbig_card_alt6 hAlt]; norm_num
  · rw [w183fourbig_card_PSL_3_2_1 hO hL31]; norm_num
  · rw [w183fourbig_card_PSL_3_2_2 hO hL32]; norm_num
  · rw [w183fourbig_card_PSp_2_2_2 hO hSp]; norm_num

theorem w183four_not_sp4 (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : IsAlt X 6 ∨ IsL3 X 1 ∨ IsL3 X 2) : ¬ IsSp4 X 2 := by
  intro hsp
  have hcardSp := w183fourbig_card_PSp_2_2_2 hO hsp
  rcases h with hAlt | hL31 | hL32
  · rw [w183fourbig_card_alt6 hAlt] at hcardSp; norm_num at hcardSp
  · rw [w183fourbig_card_PSL_3_2_1 hO hL31] at hcardSp; norm_num at hcardSp
  · rw [w183fourbig_card_PSL_3_2_2 hO hL32] at hcardSp; norm_num at hcardSp

theorem w183four_big_one (rows : Br1Rows) {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}
    (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    (hN : calNIn H D.T = {H ⊓ D.M})
    (hK : kerMV V H ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G)) {L : Subgroup G}
    (hLH : L ≤ H) (hLn : H ≤ Subgroup.normalizer (L : Set G)) (hLT : L ⊔ D.T = H)
    (hX : HasQuotShape L (kerMV V H : Set G)
      (fun X _ => IsAlt X 6 ∨ IsL3 X 1 ∨ IsL3 X 2 ∨ IsSp4 X 2))
    (hD : ∃ t ∈ D.T, ActsOnDynkinMod (kerMV V H) L t)
    (hPT : PairTest (M.img H) (Ctx188.packFamilyU D V H i M))
    (hbig : ∀ g' : G, Gam183 V H (eOmegaZ H D.T) i g' →
      3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g')) {g : G}
    (hgK : ¬ vInH V H g ≤ kerMV V H) (hgi : E3.mQuot (conjSubgroup V g) (vInH V H g) ≤ i)
    (hA : 3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g)) :
    False := by
  classical
  have hQ : HasQuotShape L (kerMV V H : Set G)
      (fun X _ => IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a) := by
    obtain ⟨X, hXg, φ, hs, hk, hP⟩ := hX
    exact ⟨X, hXg, φ, hs, hk, w183fourbig_simple_nonab_of_shape hP⟩
  have hbase := x.br1_comp_base M hK hLH hLn hLT hQ
  have hshapeX : IsAlt ↥(M.img L) 6 ∨ IsL3 ↥(M.img L) 1 ∨ IsL3 ↥(M.img L) 2 ∨
      IsSp4 ↥(M.img L) 2 :=
    x.br1_shape_transport M hK hLH
      (fun X Y _ _ e h => w183fourbig_shape_of_mulEquiv e h) hX
  have hshape : IsL3 ↥(M.img L) 1 ∨ IsAlt ↥(M.img L) 6 ∨ IsL3 ↥(M.img L) 2 ∨
      IsSp4 ↥(M.img L) 2 := by
    rcases hshapeX with hAlt | hL31 | hL32 | hSp
    · exact Or.inr (Or.inl hAlt)
    · exact Or.inl hL31
    · exact Or.inr (Or.inr (Or.inl hL32))
    · exact Or.inr (Or.inr (Or.inr hSp))
  obtain ⟨t, htT, hD'⟩ := hD
  have htH : t ∈ H := x.hyp.hyp171.2.1 htT
  have hτ : ∃ τ ∈ M.img D.T, ActsOnDynkinMod ⊥ (M.img L) τ :=
    ⟨M.ρ ⟨t, htH⟩, M.mem_img.2 ⟨⟨t, htH⟩, htT, rfl⟩,
      x.br1_dynkin_of_H M hK hLH htH hD'⟩
  have hB := x.br2Common M hN
  have hgam : Gam183 V H (eOmegaZ H D.T) i g := ⟨hgi, fun hle =>
    hgK ((le_inf inf_le_right hle).trans x.hyp.inf_centralizer_eOmegaZ_le_kerMV)⟩
  have hne : (Ctx188.packFamilyU D V H i M).Nonempty :=
    ⟨M.img (vInH V H g), ⟨g, hgam, rfl⟩⟩
  have hall : ∀ A ∈ Ctx188.packFamilyU D V H i M, 2 ≤ mRank A :=
    fun A hA => w183fourbig_two_le_mRank_of_mem x M hbig hA
  exact br1_master_one_big rows hB hbase.1 hbase.2.1 hbase.2.2.1 hbase.2.2.2.1
    hbase.2.2.2.2 hshape hτ hne hall (fun _ => hPT)

theorem w183four_big_two (hO : LieOrderFormulasInput) (rows : Br1Rows) {D : Data G}
    {V₀ V H : Subgroup G} {i : ℕ} (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    (hN : calNIn H D.T = {H ⊓ D.M})
    (hK : kerMV V H ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G)) {L : Subgroup G}
    (hL : IsComponentModN (kerMV V H) H L) (hLT : L ⊔ D.T = H)
    (hX : HasQuotShape L (kerMV V H : Set G)
      (fun X _ => IsAlt X 6 ∨ IsL3 X 1 ∨ IsL3 X 2 ∨ IsSp4 X 2))
    (hD : ∃ t ∈ D.T, ActsOnDynkinMod (kerMV V H) L t) {t : G} (htT : t ∈ D.T)
    (hne : conjSubgroup L t ≠ L)
    (hall : ∀ s ∈ D.T, conjSubgroup L s = L ∨ conjSubgroup L s = conjSubgroup L t)
    (hPT : PairTest (M.img H) (Ctx188.packFamilyU D V H i M))
    (h5 : HasQuotShape L (kerMV V H : Set G) (fun X _ => IsSp4 X 2) →
      ∀ A ∈ Ctx188.packFamilyU D V H i M, ∀ P : Subgroup (LGL 2 M.W),
        IsSylowIn 5 P (M.img H ⊓ Subgroup.normalizer (A : Set (LGL 2 M.W))) → IsCyclic ↥P)
    (hbig : ∀ g' : G, Gam183 V H (eOmegaZ H D.T) i g' →
      3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g')) {g : G}
    (hgK : ¬ vInH V H g ≤ kerMV V H) (hgi : E3.mQuot (conjSubgroup V g) (vInH V H g) ≤ i)
    (hA : 3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g)) :
    False := by
  classical
  have hLH : L ≤ H := hL.2.2.1
  have hQ : HasQuotShape L (kerMV V H : Set G)
      (fun X _ => IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a) := by
    obtain ⟨X, hXg, φ, hs, hk, hP⟩ := hX
    exact ⟨X, hXg, φ, hs, hk, w183fourbig_simple_nonab_of_shape hP⟩
  have htwo := x.br1_twoComp M hK hL hLT hQ htT hne hall
  have hshapeX : IsAlt ↥(M.img L) 6 ∨ IsL3 ↥(M.img L) 1 ∨ IsL3 ↥(M.img L) 2 ∨
      IsSp4 ↥(M.img L) 2 :=
    x.br1_shape_transport M hK hLH
      (fun X Y _ _ e h => w183fourbig_shape_of_mulEquiv e h) hX
  have hshape : IsL2 ↥(M.img L) 2 ∨ IsL3 ↥(M.img L) 2 ∨ IsSp4 ↥(M.img L) 2 ∨
      IsL3 ↥(M.img L) 1 ∨ IsAlt ↥(M.img L) 6 := by
    rcases hshapeX with hAlt | hL31 | hL32 | hSp
    · exact Or.inr (Or.inr (Or.inr (Or.inr hAlt)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hL31)))
    · exact Or.inr (Or.inl hL32)
    · exact Or.inr (Or.inr (Or.inl hSp))
  have hτ : (IsL3 ↥(M.img L) 1 ∨ IsAlt ↥(M.img L) 6 ∨ IsSp4 ↥(M.img L) 2 ∨
      IsL3 ↥(M.img L) 2) → ∃ τ ∈ M.img D.T, ActsOnDynkinMod ⊥ (M.img L) τ := by
    intro _
    obtain ⟨t', ht'T, hD'⟩ := hD
    have ht'H : t' ∈ H := x.hyp.hyp171.2.1 ht'T
    exact ⟨M.ρ ⟨t', ht'H⟩, M.mem_img.2 ⟨⟨t', ht'H⟩, ht'T, rfl⟩,
      x.br1_dynkin_of_H M hK hLH ht'H hD'⟩
  have hB := x.br2Common M hN
  have hgam : Gam183 V H (eOmegaZ H D.T) i g := ⟨hgi, fun hle =>
    hgK ((le_inf inf_le_right hle).trans x.hyp.inf_centralizer_eOmegaZ_le_kerMV)⟩
  have hneΓ : (Ctx188.packFamilyU D V H i M).Nonempty :=
    ⟨M.img (vInH V H g), ⟨g, hgam, rfl⟩⟩
  have hall' : ∀ A ∈ Ctx188.packFamilyU D V H i M, 2 ≤ mRank A :=
    fun A hA => w183fourbig_two_le_mRank_of_mem x M hbig hA
  obtain ⟨ED, hED⟩ := x.br2ED M
  have h5' : IsSp4 ↥(M.img L) 2 → ∀ A ∈ Ctx188.packFamilyU D V H i M,
      ∀ P : Subgroup (LGL 2 M.W),
        IsSylowIn 5 P (M.img H ⊓ Subgroup.normalizer (A : Set (LGL 2 M.W))) →
          IsCyclic ↥P := by
    intro hsp
    obtain ⟨X, hXg, φ, hs, hk, hP⟩ := hX
    rcases hP with hAlt | hL31 | hL32 | hSp
    · exfalso
      have hAltY : IsAlt ↥(M.img L) 6 :=
        x.br1_shape_transport M hK hLH
          (fun X Y _ _ e h => (⟨e.symm.trans h.some⟩ : IsAlt Y 6))
          ⟨X, hXg, φ, hs, hk, hAlt⟩
      exact w183four_not_sp4 hO (Or.inl hAltY) hsp
    · exfalso
      have hL31Y : IsL3 ↥(M.img L) 1 :=
        x.br1_shape_transport M hK hLH
          (fun X Y _ _ e h => CFSG.Blueprint.LieModel.of_mulEquiv e h)
          ⟨X, hXg, φ, hs, hk, hL31⟩
      exact w183four_not_sp4 hO (Or.inr (Or.inl hL31Y)) hsp
    · exfalso
      have hL32Y : IsL3 ↥(M.img L) 2 :=
        x.br1_shape_transport M hK hLH
          (fun X Y _ _ e h => CFSG.Blueprint.LieModel.of_mulEquiv e h)
          ⟨X, hXg, φ, hs, hk, hL32⟩
      exact w183four_not_sp4 hO (Or.inr (Or.inr hL32Y)) hsp
    · exact h5 ⟨X, hXg, φ, hs, hk, hSp⟩
  exact br1_master_two rows hB htwo hshape hτ hneΓ hall' hED (fun _ => hPT) h5'

end CFSG.LocalAnalysis.WeakClosure81

end
