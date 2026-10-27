module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Img
public import CFSG.LocalAnalysis.WeakClosure81.W183K3CoreSetting
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.WeakClosure81.W18KernBridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open W183K3

variable {G : Type} [Group G] [Finite G]

theorem w183k3_two_le_mRank_of_mem {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}
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

theorem w183k3_four_le_card_of_mem {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}
    (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    (hbig : ∀ g' : G, Gam183 V H (eOmegaZ H D.T) i g' →
      3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g'))
    {A : Subgroup (LGL 2 M.W)} (hA : A ∈ Ctx188.packFamilyU D V H i M) :
    4 ≤ Nat.card ↥A := by
  obtain ⟨g', hgam, rfl⟩ := hA
  have hab : IsElemAbelian 2 (vInH V H g') :=
    (E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g').mono inf_le_left
  obtain ⟨-, hA4⟩ := four_le_card_img M inf_le_right hab (hbig g' hgam)
  have hAH : M.img (vInH V H g') ≤ M.img H := M.img_mono inf_le_right
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv) ▸ hA4

theorem w183k3_odd_center_of_quasiCentre {W : Type} [Group W] {L : Subgroup W}
    (h : Odd (Nat.card ↥(quasiCentre L))) : Odd (Nat.card ↥(Subgroup.center ↥L)) := by
  rw [quasiCentre] at h
  rwa [Subgroup.card_map_of_injective L.subtype_injective] at h

theorem w183k3_nontrivial_center_of_ne_bot {W : Type} [Group W] {L : Subgroup W}
    (h : quasiCentre L ≠ ⊥) : Nontrivial ↥(Subgroup.center ↥L) := by
  rw [Subgroup.nontrivial_iff_ne_bot]
  intro hbot
  exact h (by rw [quasiCentre, hbot, Subgroup.map_bot])

theorem w183k3_gam_of_not_le_ker {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}
    (x : Ctx188 D V₀ V H i 3) {g : G}
    (hgi : E3.mQuot (conjSubgroup V g) (vInH V H g) ≤ i) (hgK : ¬ vInH V H g ≤ kerMV V H) :
    Gam183 V H (eOmegaZ H D.T) i g :=
  ⟨hgi, fun hle =>
    hgK ((le_inf inf_le_right hle).trans x.hyp.inf_centralizer_eOmegaZ_le_kerMV)⟩

theorem w183k3_kk_ne_bot {D : Data G} {V H : Subgroup G} (M : ModDataE H (eOmegaZ H D.T))
    {Kk : Subgroup ↥(M.img H)}
    (hKk : ∀ (j : ↥H) (r : ↥(M.img H)), (r : LGL 2 M.W) = M.ρ j →
      (r ∈ Kk ↔ (j : G) ∈ kerMV V H))
    (hKH : kerMV V H ≤ H)
    (hK : ¬ kerMV V H ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G)) : Kk ≠ ⊥ := by
  intro hbot
  apply hK
  intro k hk
  have hkH : k ∈ H := hKH hk
  let j : ↥H := ⟨k, hkH⟩
  let r : ↥(M.img H) := ⟨M.ρ j, M.mem_img.mpr ⟨j, j.2, rfl⟩⟩
  have hr : r ∈ Kk := (hKk j r rfl).2 hk
  rw [hbot] at hr
  have hρ1 : M.ρ j = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp hr)
  exact (M.ρ_eq_one_iff j).1 hρ1

theorem w183k3_not_le_ker_of_gam {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}
    (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    {Kk F : Subgroup ↥(M.img H)} (hker : KStarData Kk F)
    (hKk : ∀ (j : ↥H) (r : ↥(M.img H)), (r : LGL 2 M.W) = M.ρ j →
      (r ∈ Kk ↔ (j : G) ∈ kerMV V H))
    {g' : G} (hg' : Gam183 V H (eOmegaZ H D.T) i g') : ¬ vInH V H g' ≤ kerMV V H := by
  intro hle
  apply hg'.2
  intro a ha
  have haH : a ∈ H := (Subgroup.mem_inf.mp ha).2
  let j : ↥H := ⟨a, haH⟩
  let r : ↥(M.img H) := ⟨M.ρ j, M.mem_img.mpr ⟨j, j.2, rfl⟩⟩
  have hk : (j : G) ∈ kerMV V H := hle ha
  have hrK : r ∈ Kk := (hKk j r rfl).2 hk
  have hab : IsElemAbelian 2 (vInH V H g') :=
    (E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g').mono inf_le_left
  have hA : IsPGroup 2 ((M.img (vInH V H g')).subgroupOf (M.img H)) :=
    (M.isPGroup_img (CFSG.Open.IsElemAbelian.isPGroup hab)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (M.img_mono inf_le_right)).symm
  have hbot := isPGroup_inf_odd_eq_bot hA hker.odd
  have hrA : r ∈ (M.img (vInH V H g')).subgroupOf (M.img H) := by
    rw [Subgroup.mem_subgroupOf]
    exact M.mem_img.mpr ⟨j, ha, rfl⟩
  have hrbot : r ∈ (⊥ : Subgroup ↥(M.img H)) := by
    rw [← hbot]
    exact Subgroup.mem_inf.mpr ⟨hrA, hrK⟩
  have hρ1 : M.ρ j = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp hrbot)
  exact (M.ρ_eq_one_iff j).1 hρ1

theorem w183k3_two_center_nontrivial {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {Y T L₁ L₂ : Subgroup (LGL 2 V)} (htwo : Br3TwoComp Y T L₁ L₂)
    (h : quasiCentre L₁ ⊔ quasiCentre L₂ ≠ ⊥) : Nontrivial ↥(Subgroup.center ↥L₁) := by
  rw [Subgroup.nontrivial_iff_ne_bot]
  intro hc1
  apply h
  have hq1 : quasiCentre L₁ = ⊥ := by rw [quasiCentre, hc1, Subgroup.map_bot]
  have hc2 : Subgroup.center ↥L₂ = ⊥ := by
    rw [← Subgroup.map_center_eq htwo.swapEquiv, hc1, Subgroup.map_bot]
  have hq2 : quasiCentre L₂ = ⊥ := by rw [quasiCentre, hc2, Subgroup.map_bot]
  rw [hq1, hq2, bot_sup_eq]

end CFSG.LocalAnalysis.WeakClosure81

end
