module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveFourteenG
public import CFSG.LocalAnalysis.WeakClosure81.EightFour

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G} {g : G} {X T : Subgroup G}

theorem Hyp167.I_le_conjSubgroup_M (h1 : W16One G) (hS : Std15 G)
    (hX : Hyp167 M V₀ V U S H g X T) (hVO : V ≤ pCoreOf 2 H)
    (hBE : conjSubgroup V₀ g ⊓ eSub V₀ X T ≠ ⊥) : conjClosure V X ≤ conjSubgroup M g := by
  have hV₀ne : V₀ ≠ ⊥ := hX.cex.hyp.ne_bot
  obtain ⟨⟨b, hbB, hbE⟩, hb1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hBE
  have hb1 : b ≠ 1 := fun h => hb1' (Subtype.ext h)
  have hle : V₀ ⊓ Subgroup.centralizer (T : Set G) ≤ V :=
    inf_le_left.trans hX.cex.hyp.h6.le
  have hbI : b ∈ conjClosure V X := (conjClosure_mono hle le_rfl) hbE
  have hTI₀ : CFSG.CGT.Timmesfeld75.IsTI V₀ := hX.cex.hyp.h6.isTI hV₀ne
  have hTI_B : CFSG.CGT.Timmesfeld75.IsTI (conjSubgroup V₀ g) := isTI_conj hTI₀ g
  have hNB : Subgroup.normalizer (conjSubgroup V₀ g : Set G) = conjSubgroup M g := by
    rw [← E3.conjSubgroup_normalizer V₀ g, hX.cex.hyp.h6.normalizer₀ hV₀ne]
  rw [← hNB]
  intro i hi
  have hIab : IsElemAbelian 2 (conjClosure V X) := Hyp167.isElemAbelian_I h1 hS hX hVO
  have hcomm : i * b = b * i := B2F.isElemAbelian_comm hIab hi hbI
  exact CFSG.RankThree.GF2n.Tim77.mem_normalizer_of_commute_of_isTI hTI_B hbB hb1 hcomm

theorem Hyp167.false_of_mQuot_A_le (h1 : W16One G) (hS : Std15 G) (h152 : Thm152 G)
    (hX : Hyp167 M V₀ V U S H g X T) (hVO : V ≤ pCoreOf 2 H)
    (hIA : conjClosure V X ≤ conjSubgroup M g)
    (hle : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ kerMOf M X) ≤
      E3.mQuot V (U ⊔ V₀)) : False := by
  set A : Subgroup G := conjSubgroup V g with hA
  have hex : ∃ x ∈ X, ¬ conjSubgroup A x ≤ M := by
    by_contra hcon
    have hM : ∀ x ∈ X, conjSubgroup A x ≤ M := by
      intro x hx
      by_contra hxM
      exact hcon ⟨x, hx, hxM⟩
    have hAX_le_M : conjClosure A X ≤ M := by
      refine conjClosure_le fun x hx a ha => ?_
      have h1 : x * a * x⁻¹ ∈ conjSubgroup A x⁻¹ := by
        rw [mem_conjSubgroup_iff]
        have e : (x⁻¹) * (x * a * x⁻¹) * (x⁻¹)⁻¹ = a := by group
        rw [e]
        exact ha
      exact hM x⁻¹ (X.inv_mem hx) h1
    have hA_le_X : A ≤ X := hX.mem.2.2.A_le
    have hAX_le_X : conjClosure A X ≤ X := by
      refine conjClosure_le fun x hx a ha => ?_
      exact X.mul_mem (X.mul_mem hx (hA_le_X ha)) (X.inv_mem hx)
    have hAXnorm : X ≤ Subgroup.normalizer (conjClosure A X : Set G) :=
      le_normalizer_conjClosure A X
    have hAX_le_K : conjClosure A X ≤ kerMOf M X :=
      le_kerMOf_of_normal hAX_le_X
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hAX_le_X).2 hAXnorm) hAX_le_M
    exact hX.mem.2.2.not_le_ker ((le_conjClosure A X).trans hAX_le_K)
  obtain ⟨x, hxX, hxM⟩ := hex
  have hW_eq : conjSubgroup A x = conjSubgroup V (g * x) := by
    rw [hA, conjSubgroup_conjSubgroup]
  have hA_le_X : A ≤ X := hX.mem.2.2.A_le
  have hW_le_X : conjSubgroup A x ≤ X := by
    intro y hy
    rw [mem_conjSubgroup_iff] at hy
    have e : y = x⁻¹ * (x * y * x⁻¹) * x := by group
    rw [e]
    exact X.mul_mem (X.mul_mem (X.inv_mem hxX) (hA_le_X hy)) hxX
  have hW_le_CU : conjSubgroup A x ≤ Subgroup.centralizer (U : Set G) :=
    hW_le_X.trans (hX.mem.1.trans hX.min.1.2.1)
  have hAelem : IsElemAbelian 2 A := E3.isElemAbelian_conjSubgroup hX.cex.hyp.h6.elemAbelian g
  have hWelem : IsElemAbelian 2 (conjSubgroup A x) := E3.isElemAbelian_conjSubgroup hAelem x
  have hWinfM_le_V₀ : ⁅conjSubgroup A x ⊓ M, V⁆ ≤ V₀ := by
    refine Subgroup.commutator_le.2 fun w hw v hv => ?_
    obtain ⟨hwW, hwM⟩ := Subgroup.mem_inf.1 hw
    have hwCU : w ∈ Subgroup.centralizer (U : Set G) := hW_le_CU hwW
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hWelem.isPGroup) ⟨w, hwW⟩
    have ht2 : ∃ k : ℕ, orderOf w = 2 ^ k :=
      ⟨k, by rw [← hk]; exact Subgroup.orderOf_coe ⟨w, hwW⟩⟩
    exact (FourteenTwo.mem_cTilde_iff_comm.1
      (hX.cex.mem_cTilde_of_orderOf ⟨hwM, hwCU⟩ ht2)).2.2 v hv
  have hIx : conjSubgroup (conjClosure V X) x = conjClosure V X := by
    rw [conjSubgroup_eq_iff_mem_normalizer]
    exact le_normalizer_conjClosure V X hxX
  have hI_le_Mgx : conjClosure V X ≤ conjSubgroup M (g * x) := by
    have h2 := E3.conjSubgroup_mono_left x hIA
    rw [conjSubgroup_conjSubgroup] at h2
    rwa [hIx] at h2
  have hMgx_eq : Subgroup.normalizer (conjSubgroup A x : Set G) = conjSubgroup M (g * x) := by
    rw [hW_eq, ← E3.conjSubgroup_normalizer V (g * x), hX.cex.hyp.h6.normalizer_eq]
  have hV_le_NW : V ≤ Subgroup.normalizer (conjSubgroup A x : Set G) := by
    rw [hMgx_eq]
    exact (le_conjClosure V X).trans hI_le_Mgx
  have hWinfM_le_W : ⁅conjSubgroup A x ⊓ M, V⁆ ≤ conjSubgroup A x :=
    (Subgroup.commutator_mono inf_le_left le_rfl).trans
      ((Subgroup.le_normalizer_iff_commutator_le_left).1 hV_le_NW)
  have hWinfV₀ : conjSubgroup A x ⊓ V₀ = ⊥ := by
    by_contra hne
    obtain ⟨⟨t, htW, htV₀⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
    have hW_le_Ct : conjSubgroup A x ≤ Subgroup.centralizer ({t} : Set G) := by
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact B2F.isElemAbelian_comm hWelem htW hu
    exact hxM (hW_le_Ct.trans (hX.cex.hyp.centralizer_le htV₀ ht1'))
  have hWinfM_eq_one : ⁅conjSubgroup A x ⊓ M, V⁆ = ⊥ := by
    refine le_bot_iff.1 ?_
    calc ⁅conjSubgroup A x ⊓ M, V⁆ ≤ conjSubgroup A x ⊓ V₀ :=
          le_inf hWinfM_le_W hWinfM_le_V₀
      _ = ⊥ := hWinfV₀
  have hWinfM_le_CV : conjSubgroup A x ⊓ M ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hWinfM_eq_one
  have hKx : conjSubgroup (kerMOf M X) x = kerMOf M X := by
    rw [conjSubgroup_eq_iff_mem_normalizer]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (kerMOf_le_group M X)).1
      (normal_subgroupOf_kerMOf M X) hxX
  have hWinfK_eq : conjSubgroup A x ⊓ kerMOf M X = conjSubgroup (A ⊓ kerMOf M X) x := by
    rw [E3.conjSubgroup_inf, hKx]
  have hAK_le_AM : conjSubgroup A x ⊓ kerMOf M X ≤ conjSubgroup A x ⊓ M :=
    le_inf inf_le_left (inf_le_right.trans (kerMOf_le_left M X))
  have hmQuot_eq : E3.mQuot (conjSubgroup A x) (conjSubgroup A x ⊓ kerMOf M X) =
      E3.mQuot A (A ⊓ kerMOf M X) := by
    rw [hWinfK_eq]
    exact E3.mQuot_conjSubgroup A (A ⊓ kerMOf M X) x
  have hWlt : E3.mQuot (conjSubgroup A x) (conjSubgroup A x ⊓ M) <
      mBar M V₀ V hX.cex.hyp.h6.elemAbelian := by
    calc E3.mQuot (conjSubgroup A x) (conjSubgroup A x ⊓ M)
        ≤ E3.mQuot (conjSubgroup A x) (conjSubgroup A x ⊓ kerMOf M X) :=
          E3.mQuot_mono hAK_le_AM
      _ = E3.mQuot A (A ⊓ kerMOf M X) := hmQuot_eq
      _ ≤ E3.mQuot V (U ⊔ V₀) := hle
      _ < mBar M V₀ V hX.cex.hyp.h6.elemAbelian := hX.cex.n_lt_mBar
  set U'' : Subgroup G := V ⊓ conjSubgroup M ((g * x)⁻¹) with hU''
  have hU''_eq : U'' = conjSubgroup (conjSubgroup A x ⊓ M) ((g * x)⁻¹) := by
    rw [hU'', E3.conjSubgroup_inf, hW_eq]
    congr 1
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
  have hU''V : U'' ≤ V := inf_le_left
  have hU''lt : E3.mQuot V (U'' ⊔ V₀) < mBar M V₀ V hX.cex.hyp.h6.elemAbelian := by
    have h1 : E3.mQuot V (U'' ⊔ V₀) ≤ E3.mQuot V U'' := E3.mQuot_mono le_sup_left
    have h2 : E3.mQuot V U'' = E3.mQuot (conjSubgroup A x) (conjSubgroup A x ⊓ M) := by
      rw [hU''_eq]
      have hV_eq : conjSubgroup (conjSubgroup A x) ((g * x)⁻¹) = V := by
        rw [hW_eq, conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
      rw [← hV_eq]
      exact E3.mQuot_conjSubgroup (conjSubgroup A x) (conjSubgroup A x ⊓ M) ((g * x)⁻¹)
    exact lt_of_le_of_lt (h1.trans (le_of_eq h2)) hWlt
  have hVinv_le_M : conjSubgroup V ((g * x)⁻¹) ≤ M := by
    have hV_le_Mgx : V ≤ conjSubgroup M (g * x) := (le_conjClosure V X).trans hI_le_Mgx
    have h := E3.conjSubgroup_mono_left ((g * x)⁻¹) hV_le_Mgx
    rwa [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at h
  have hVinv_le_CU'' : conjSubgroup V ((g * x)⁻¹) ≤ Subgroup.centralizer (U'' : Set G) := by
    have h1 : conjSubgroup (conjSubgroup A x ⊓ M) ((g * x)⁻¹) ≤
        Subgroup.centralizer (conjSubgroup V ((g * x)⁻¹) : Set G) := by
      have h := E3.conjSubgroup_mono_left ((g * x)⁻¹) hWinfM_le_CV
      rwa [E3.conjSubgroup_centralizer] at h
    have h2 : conjSubgroup V ((g * x)⁻¹) ≤
        Subgroup.centralizer ((conjSubgroup (conjSubgroup A x ⊓ M) ((g * x)⁻¹)) : Set G) := by
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact (Subgroup.mem_centralizer_iff.1 (h1 hw) v hv).symm
    simpa [hU''_eq] using h2
  have hVinv_le_wClos : conjSubgroup V ((g * x)⁻¹) ≤
      E3.wClos V 0 (M ⊓ Subgroup.centralizer (U'' : Set G)) :=
    conjSubgroup_le_wClos_zero (le_inf hVinv_le_M hVinv_le_CU'')
  have hmain := h1 hS hX.cex.hyp hX.cex.mbar hU''V hU''lt
  have hVinv_le_CV : conjSubgroup V ((g * x)⁻¹) ≤ Subgroup.centralizer (V : Set G) :=
    hVinv_le_wClos.trans hmain
  have hV_le_CW : V ≤ Subgroup.centralizer (conjSubgroup A x : Set G) := by
    have h := E3.conjSubgroup_mono_left (g * x) hVinv_le_CV
    rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one,
      E3.conjSubgroup_centralizer, ← hW_eq] at h
    exact h
  have hW_le_CV : conjSubgroup A x ≤ Subgroup.centralizer (V : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (Subgroup.mem_centralizer_iff.1 (hV_le_CW hv) w hw).symm
  have hW_le_M : conjSubgroup A x ≤ M :=
    hW_le_CV.trans ((Subgroup.centralizer_le_normalizer (V : Set G)).trans
      (le_of_eq hX.cex.hyp.h6.normalizer_eq))
  exact hxM hW_le_M

end CFSG.LocalAnalysis.WeakClosure81

end
