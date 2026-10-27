module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2G1Def

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.SignalizerFunctorTheorem.Quadratic
open CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem conjSubgroup_le_of_le_of_mem {A H : Subgroup G} {h : G} (hA : A ≤ H)
    (hh : h ∈ H) : conjSubgroup A h ≤ H := by
  intro x hx
  rw [mem_conjSubgroup_iff] at hx
  rw [show x = h⁻¹ * (h * x * h⁻¹) * h by group]
  exact H.mul_mem (H.mul_mem (H.inv_mem hh) (hA hx)) hh

namespace ModDataE

variable {J E : Subgroup G} (M : ModDataE J E)

private theorem sp_inj_of_le {S T : Subgroup G} (hS : S ≤ E) (hT : T ≤ E)
    (h : M.sp S = M.sp T) : S = T := by
  refine le_antisymm ?_ ?_
  · intro x hx
    have hx' : M.ι x ∈ M.sp S := ⟨x, ⟨hx, hS hx⟩, rfl⟩
    rw [h] at hx'
    obtain ⟨y, hy, hyι⟩ := hx'
    have hxy : x = y := M.ι_injOn (hS hx) hy.2 hyι.symm
    rw [hxy]
    exact hy.1
  · intro x hx
    have hx' : M.ι x ∈ M.sp T := ⟨x, ⟨hx, hT hx⟩, rfl⟩
    rw [← h] at hx'
    obtain ⟨y, hy, hyι⟩ := hx'
    have hxy : x = y := M.ι_injOn (hT hx) hy.2 hyι.symm
    rw [hxy]
    exact hy.1

end ModDataE

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

theorem img_mem_hatGamma (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) : Mo.img V ∈ hatGamma Mo V :=
  ⟨1, H.one_mem, by rw [conjSubgroup_one]⟩

private theorem hat_inf_pCore (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    ∀ A ∈ hatGamma Mo V, A ⊓ pCoreOf 2 (Mo.img H) = ⊥ := by
  rintro A ⟨h, hh, rfl⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPle : pCoreOf 2 (Mo.img H) ≤ Mo.img H :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 (Mo.img H)
  have hPn : ((pCoreOf 2 (Mo.img H)).subgroupOf (Mo.img H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPle).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Mo.img H))
  have hPp : IsPGroup 2 (pCoreOf 2 (Mo.img H)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Mo.img H)
  obtain ⟨X, hCX, hXH, hXn, hX2, hXimg⟩ :=
    Mo.exists_normal_preimage_of_pGroup hPle hPn hPp
  have hVX : V ⊓ X = U ⊔ V₀ :=
    inf_eq_sup_of_relIndex_two_pow h1 h5 h15 hS c hCX hXH hXn hX2
  rw [← hXimg]
  apply le_bot_iff.1
  rintro r ⟨hrA, hrX⟩
  obtain ⟨j, hjV, hjρ⟩ := Mo.mem_img.1 hrA
  have hjX : (j : G) ∈ X := by
    have hmem : Mo.ρ j ∈ Mo.img X := by rw [hjρ]; exact hrX
    rw [Mo.ρ_mem_img_iff hXH j.2, sup_eq_left.2 hCX] at hmem
    exact hmem
  have hjVX : (j : G) ∈ conjSubgroup (V ⊓ X) h := by
    rw [E3.conjSubgroup_inf,
      conjSubgroup_eq_iff_mem_normalizer.2
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mp hXn hh)]
    exact ⟨hjV, hjX⟩
  rw [hVX] at hjVX
  have hjI : (j : G) ∈ conjClosure (U ⊔ V₀) H :=
    conjSubgroup_le_conjClosure_of_mem hh le_rfl hjVX
  have hjcent : (j : G) ∈ centralizer (conjClosure (U ⊔ V₀) H : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun z hz => (c.mem.2.2 (j : G) hjI z hz).symm
  have hρ1 : Mo.ρ j = 1 := (Mo.ρ_eq_one_iff j).2 hjcent
  rw [Subgroup.mem_bot, ← hjρ, hρ1]

private theorem hat_normalizer_eq (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    ∀ A ∈ hatGamma Mo V, Mo.img H ⊓ Subgroup.normalizer (A : Set (LGL 2 Mo.W)) =
      stabilizerOf (Mo.img H) (hatVA Mo V₀ V A) := by
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  rintro A ⟨x, hx, rfl⟩
  rw [hatVA_img_conj h1 h5 h15 hS c Mo hx]
  ext r
  constructor
  · rintro ⟨hrG, hrN⟩
    obtain ⟨y, -, rfl⟩ := Mo.mem_img.1 hrG
    refine ⟨Mo.mem_img.2 ⟨y, y.2, rfl⟩, ?_⟩
    have himg : Mo.img (conjSubgroup V (x * (y : G)⁻¹)) = Mo.img (conjSubgroup V x) := by
      rw [← conjSubgroup_conjSubgroup,
        ← Mo.img_conj (A := conjSubgroup V x) (conjSubgroup_le_of_le_of_mem hVH hx) y]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hrN
    have hmemM : x * (y : G)⁻¹ * x⁻¹ ∈ M :=
      (img_conjSubgroup_eq_iff h1 h5 h15 hS c Mo
        (H.mul_mem hx (H.inv_mem y.2)) hx).1 himg
    have hV₀eq : conjSubgroup V₀ (x * (y : G)⁻¹) = conjSubgroup V₀ x := by
      have h1n : x * (y : G)⁻¹ * x⁻¹ ∈ normalizer (V₀ : Set G) := by
        rw [c.cex.hyp.normalizer₀]
        exact hmemM
      have h2 : conjSubgroup V₀ (x * (y : G)⁻¹ * x⁻¹) = V₀ :=
        conjSubgroup_eq_iff_mem_normalizer.2 h1n
      calc conjSubgroup V₀ (x * (y : G)⁻¹)
          = conjSubgroup (conjSubgroup V₀ (x * (y : G)⁻¹ * x⁻¹)) x := by
            rw [conjSubgroup_conjSubgroup]
            congr 1
            group
        _ = conjSubgroup V₀ x := by rw [h2]
    rw [Mo.conjSub_sp (conjSubgroup V₀ x) y, conjSubgroup_conjSubgroup, hV₀eq]
  · rintro ⟨hrG, hrS⟩
    obtain ⟨y, -, rfl⟩ := Mo.mem_img.1 hrG
    refine ⟨Mo.mem_img.2 ⟨y, y.2, rfl⟩, ?_⟩
    have hrS' : Mo.sp (conjSubgroup V₀ (x * (y : G)⁻¹)) =
        Mo.sp (conjSubgroup V₀ x) := by
      rw [← conjSubgroup_conjSubgroup, ← Mo.conjSub_sp (conjSubgroup V₀ x) y]
      exact hrS
    have hV₀eq : conjSubgroup V₀ (x * (y : G)⁻¹) = conjSubgroup V₀ x :=
      ModDataE.sp_inj_of_le (M := Mo)
        (conjSubgroup_le_conjClosure_of_mem (H.mul_mem hx (H.inv_mem y.2)) le_sup_right)
        (conjSubgroup_le_conjClosure_of_mem hx le_sup_right) hrS'
    have hmemM : x * (y : G)⁻¹ * x⁻¹ ∈ M := by
      have h1n : x * (y : G)⁻¹ * x⁻¹ ∈ normalizer (V₀ : Set G) := by
        have h2 : conjSubgroup V₀ (x * (y : G)⁻¹ * x⁻¹) = V₀ := by
          rw [← conjSubgroup_conjSubgroup, hV₀eq, conjSubgroup_conjSubgroup,
            mul_inv_cancel, conjSubgroup_one]
        exact conjSubgroup_eq_iff_mem_normalizer.1 h2
      rwa [c.cex.hyp.normalizer₀] at h1n
    have himg : Mo.img (conjSubgroup V (x * (y : G)⁻¹)) = Mo.img (conjSubgroup V x) :=
      (img_conjSubgroup_eq_iff h1 h5 h15 hS c Mo
        (H.mul_mem hx (H.inv_mem y.2)) hx).2 hmemM
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change cj (Mo.ρ y) (Mo.img (conjSubgroup V x)) = Mo.img (conjSubgroup V x)
    rw [Mo.img_conj (A := conjSubgroup V x) (conjSubgroup_le_of_le_of_mem hVH hx) y,
      conjSubgroup_conjSubgroup]
    exact himg

private theorem hat_cond2 (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    ∀ A ∈ hatGamma Mo V, ∀ B' : Subgroup (LGL 2 Mo.W), B' ≤ A →
      mOf A B' ≤ E3.mQuot V (U ⊔ V₀) →
        CFSG.Quasithin.G11.commSpace A (fixSub B') ≤ hatVA Mo V₀ V A := by
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  rintro A ⟨x, hx, rfl⟩ B' hB'A _
  have hVxH : conjSubgroup V x ≤ H := conjSubgroup_le_of_le_of_mem hVH hx
  obtain ⟨B₁, hB₁A, hCB₁, hB₁img⟩ := Mo.exists_preimage hVxH hB'A
  have hB₁H : B₁ ≤ H := hB₁A.trans hVxH
  have hle : ⁅Subgroup.centralizer (B₁ : Set G) ⊓ conjClosure (U ⊔ V₀) H,
      conjSubgroup V x⁆ ≤ conjSubgroup V₀ x := by
    refine (Subgroup.commutator_mono inf_le_right le_rfl).trans ?_
    rw [Subgroup.commutator_comm (conjClosure (U ⊔ V₀) H) (conjSubgroup V x)]
    exact comm_conj_conjClosure_le h1 hS c hx
  have hfix : fixSub B' = Mo.sp (Subgroup.centralizer (B₁ : Set G)) := by
    rw [← hB₁img]
    exact Mo.fixSub_img hB₁H
  calc CFSG.Quasithin.G11.commSpace (Mo.img (conjSubgroup V x)) (fixSub B')
      = CFSG.Quasithin.G11.commSpace (Mo.img (conjSubgroup V x))
          (Mo.sp (Subgroup.centralizer (B₁ : Set G))) := by rw [hfix]
    _ ≤ Mo.sp (conjSubgroup V₀ x) :=
        Mo.commSpace_img_sp_le (A := conjSubgroup V x) hVxH hle
    _ = hatVA Mo V₀ V (Mo.img (conjSubgroup V x)) :=
        (hatVA_img_conj h1 h5 h15 hS c Mo hx).symm

private theorem hat_quadratic (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    ∀ A ∈ hatGamma Mo V,
      CFSG.Quasithin.G11.commSpace A
        (CFSG.SignalizerFunctorTheorem.Quadratic.commSub A) = ⊥ := by
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  rintro A ⟨x, hx, rfl⟩
  have hVxH : conjSubgroup V x ≤ H := conjSubgroup_le_of_le_of_mem hVH hx
  refine Mo.commSpace_commSub_img_eq_bot hVxH (le_bot_iff.1 ?_)
  have hcomm : ⁅⁅conjClosure (U ⊔ V₀) H, conjSubgroup V x⁆, conjSubgroup V x⁆ =
      ⁅⁅conjSubgroup V x, conjClosure (U ⊔ V₀) H⁆, conjSubgroup V x⁆ := by
    rw [Subgroup.commutator_comm (conjClosure (U ⊔ V₀) H) (conjSubgroup V x)]
  rw [hcomm]
  refine (Subgroup.commutator_mono (comm_conj_conjClosure_le h1 hS c hx) le_rfl).trans ?_
  exact le_of_eq ((Subgroup.commutator_eq_bot_iff_le_centralizer).mpr fun y hy => by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact B2F.isElemAbelian_comm
      (E3.isElemAbelian_conjSubgroup c.cex.hyp.h6.elemAbelian x) hz
      (E3.conjSubgroup_mono_left x c.cex.hyp.h6.le hy))

theorem assumption131_hat (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    Assumption131 (Mo.img H) (hatGamma Mo V) (hatVA Mo V₀ V) (E3.mQuot V (U ⊔ V₀)) := by
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  refine
    { pos_i := one_le_mQuot c
      le_G := ?_
      isElemAb := ?_
      invariant := ?_
      ne_bot := ?_
      inf_pCore := hat_inf_pCore h1 h5 h15 hS c Mo
      normalizer_eq := hat_normalizer_eq h1 h5 h15 hS c Mo
      disjoint := ?_
      cond2 := hat_cond2 h1 h5 h15 hS c Mo
      quadratic := hat_quadratic h1 h5 h15 hS c Mo
      equivariant := ?_ }
  · rintro A ⟨x, hx, rfl⟩
    exact Mo.img_mono (conjSubgroup_le_of_le_of_mem hVH hx)
  · rintro A ⟨x, hx, rfl⟩
    exact Mo.isElemAbelian_img (E3.isElemAbelian_conjSubgroup c.cex.hyp.h6.elemAbelian x)
  · rintro A ⟨h, hh, rfl⟩ r hrG
    obtain ⟨y, -, rfl⟩ := Mo.mem_img.1 hrG
    refine ⟨h * (y : G)⁻¹, H.mul_mem hh (H.inv_mem y.2), ?_⟩
    rw [Mo.img_conj (A := conjSubgroup V h) (conjSubgroup_le_of_le_of_mem hVH hh) y,
      conjSubgroup_conjSubgroup]
  · rintro A ⟨h, hh, rfl⟩ hbot
    apply not_le_centralizer_conjClosure h1 h5 h15 hS c
    have hVh_cent : conjSubgroup V h ≤
        centralizer (conjClosure (U ⊔ V₀) H : Set G) := by
      intro v hv
      have hvhH : v ∈ H := conjSubgroup_le_of_le_of_mem hVH hh hv
      have hρ1 : Mo.ρ ⟨v, hvhH⟩ = 1 := by
        have hmem : Mo.ρ ⟨v, hvhH⟩ ∈ Mo.img (conjSubgroup V h) :=
          Mo.mem_img.2 ⟨⟨v, hvhH⟩, hv, rfl⟩
        rw [hbot, Subgroup.mem_bot] at hmem
        exact hmem
      exact (Mo.ρ_eq_one_iff ⟨v, hvhH⟩).1 hρ1
    have hcent_inv : conjSubgroup (centralizer (conjClosure (U ⊔ V₀) H : Set G)) h⁻¹ =
        centralizer (conjClosure (U ⊔ V₀) H : Set G) := by
      rw [E3.conjSubgroup_centralizer,
        conjSubgroup_eq_iff_mem_normalizer.2
          (le_normalizer_conjClosure (U ⊔ V₀) H (H.inv_mem hh))]
    have hconj := E3.conjSubgroup_mono_left h⁻¹ hVh_cent
    rwa [E3.conjSubgroup_conj_inv, hcent_inv] at hconj
  · rintro A ⟨x, hx, rfl⟩ B ⟨y, hy, rfl⟩ hne
    rw [hatVA_img_conj h1 h5 h15 hS c Mo hx, hatVA_img_conj h1 h5 h15 hS c Mo hy]
    refine sp_conjSubgroup_inf_eq_bot c Mo fun hxy => hne ?_
    exact (img_conjSubgroup_eq_iff h1 h5 h15 hS c Mo hx hy).2 hxy
  · rintro A ⟨x, hx, rfl⟩ r hrG
    have hVxH : conjSubgroup V x ≤ H := conjSubgroup_le_of_le_of_mem hVH hx
    obtain ⟨y, -, rfl⟩ := Mo.mem_img.1 hrG
    rw [Mo.img_conj (A := conjSubgroup V x) hVxH y,
      conjSubgroup_conjSubgroup,
      hatVA_img_conj h1 h5 h15 hS c Mo (H.mul_mem hx (H.inv_mem y.2)),
      hatVA_img_conj h1 h5 h15 hS c Mo hx,
      Mo.conjSub_sp (conjSubgroup V₀ x) y, conjSubgroup_conjSubgroup]

theorem mRank_le_hat (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    ∀ A ∈ hatGamma Mo V, mRank A ≤ E3.mQuot V (U ⊔ V₀) := by
  rintro A ⟨x, hx, rfl⟩
  rw [mRank, card_img_conjSubgroup h1 h5 h15 hS c Mo hx]
  exact le_of_eq (Nat.log_pow (show 1 < 2 by norm_num) (E3.mQuot V (U ⊔ V₀)))

theorem hatVA_le_fixSub (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    ∀ A ∈ hatGamma Mo V, hatVA Mo V₀ V A ≤ fixSub A := by
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  rintro A ⟨x, hx, rfl⟩
  rw [hatVA_img_conj h1 h5 h15 hS c Mo hx,
    Mo.fixSub_img (conjSubgroup_le_of_le_of_mem hVH hx)]
  apply Mo.sp_mono
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact B2F.isElemAbelian_comm
    (E3.isElemAbelian_conjSubgroup c.cex.hyp.h6.elemAbelian x) hz
    (E3.conjSubgroup_mono_left x c.cex.hyp.h6.le hy)

theorem hatK_transitive (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    ∀ A ∈ hatGamma Mo V, ∃ n : ↥(Mo.img H), (n : LGL 2 Mo.W) ∈ kHatOf (hatGamma Mo V) ∧
      A = cj (n : LGL 2 Mo.W) (Mo.img V) := by
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  rintro A ⟨h, hh, rfl⟩
  obtain ⟨k, hk, hVk, -⟩ := exists_mem_conjClosure_conjSubgroup_eq h15 hS c hh
  have hkH : k ∈ H := conjClosure_le_H c hk
  let j : ↥H := ⟨k⁻¹, H.inv_mem hkH⟩
  refine ⟨⟨Mo.ρ j, Mo.mem_img.2 ⟨j, j.2, rfl⟩⟩, ?_, ?_⟩
  · rw [kHatOf_hatGamma_eq Mo V hVH]
    exact Mo.mem_img.2 ⟨j, (conjClosure V H).inv_mem hk, rfl⟩
  · rw [Mo.img_conj (A := V) hVH j]
    rw [show ((j : ↥H)⁻¹ : G) = k by simp [j]]
    rw [← hVk]

end Cfg1620

end CFSG.LocalAnalysis.WeakClosure81
