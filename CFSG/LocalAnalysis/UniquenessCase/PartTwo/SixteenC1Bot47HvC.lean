module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Bot47Base
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Bot47Plane
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Forty7aCommon
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResultsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_core_bot_V (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (hkit : OmegaKit) {V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D ⊥ V L hV)
    (hc : Case167_1 D ⊥ V hV L) (hr : (4 : ℕ∞) < rMV D.M V) {z : G} (hz : z ∈ V) (hz1 : z ≠ 1) :
    ∀ h ∈ centralizer ({z} : Set G),
      ¬ V ⊓ conjSubgroup V h ≤ Subgroup.zpowers z → h ∈ D.M := by
  intro h hh hnot
  rw [SetLike.not_le_iff_exists] at hnot
  obtain ⟨w, hw, hwz⟩ := hnot
  have hwV : w ∈ V := hw.1
  have hz2 : z ^ 2 = 1 := hV.2 z hz
  have hw2 : w ^ 2 = 1 := hV.2 w hwV
  have hzw : z * w = w * z := by
    have h := IntMod.val_comm (hV := hV) (IntMod.mk hV ⟨z, hz⟩) (IntMod.mk hV ⟨w, hwV⟩)
    simpa only [IntMod.mk, IntMod.val] using h
  have hwconj : w ∈ conjSubgroup V h := hw.2
  have hhz : h * z * h⁻¹ = z := by
    have hc : z * h = h * z := (Subgroup.mem_centralizer_iff.mp hh) z (by simp)
    rw [← hc]
    group
  have hzconj : z ∈ conjSubgroup V h := by
    rw [mem_conjSubgroup_iff]
    rwa [hhz]
  have hPV : Subgroup.zpowers z ⊔ Subgroup.zpowers w ≤ V :=
    sup_le (Subgroup.zpowers_le.mpr hz) (Subgroup.zpowers_le.mpr hwV)
  have hPh : Subgroup.zpowers z ⊔ Subgroup.zpowers w ≤ conjSubgroup V h :=
    sup_le (Subgroup.zpowers_le.mpr hzconj) (Subgroup.zpowers_le.mpr hwconj)
  exact s16c1_plane_mem_M D hSg h1219 hkit hS hc hr hPV
    (s16c1_card_sup_zpowers hz1 hz2 hw2 hzw hwz) hPh

theorem s16c1_comm_V_conjV (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (hkit : OmegaKit) {V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D ⊥ V L hV)
    (hc : Case167_1 D ⊥ V hV L) (hr : (4 : ℕ∞) < rMV D.M V) (h43 : R16_43_1 D) {z : G}
    (hz : z ∈ V) (hz1 : z ≠ 1)
    (hle : ∀ h ∈ centralizer ({z} : Set G), conjSubgroup V h ≤ D.M) :
    ∀ h ∈ centralizer ({z} : Set G), ⁅V, conjSubgroup V h⁆ = ⊥ := by
  let H := centralizer ({z} : Set G)
  have hM : D.M ≤ normalizer (V : Set G) :=
    hS.setting.hyp151.hyp125.pairFacts.le_normalizer
  intro h hh
  by_cases hhM : h ∈ D.M
  · have hWeq : conjSubgroup V h = V :=
      (conjSubgroup_eq_iff_mem_normalizer (A := V) (g := h)).2 (hM hhM)
    rw [hWeq, Subgroup.commutator_self_eq_bot_iff]
    exact hV.1
  · have hWM : conjSubgroup V h ≤ D.M := hle h hh
    have hWnV : conjSubgroup V h ≤ normalizer (V : Set G) := hWM.trans hM
    have hVnW : V ≤ normalizer (conjSubgroup V h : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro v hv x hx
      have hxh : h * x * h⁻¹ ∈ V := mem_conjSubgroup_iff.mp hx
      have haM : h * v * h⁻¹ ∈ D.M :=
        hle h⁻¹ (H.inv_mem hh) (by
          rw [mem_conjSubgroup_iff]
          rwa [show h⁻¹ * (h * v * h⁻¹) * h⁻¹⁻¹ = v by group])
      have ha : h * v * h⁻¹ ∈ normalizer (V : Set G) := hM haM
      have hconj : (h * v * h⁻¹) * (h * x * h⁻¹) * (h * v * h⁻¹)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp ha (h * x * h⁻¹)).mp hxh
      rw [mem_conjSubgroup_iff]
      rw [show h * (v * x * v⁻¹) * h⁻¹ =
        (h * v * h⁻¹) * (h * x * h⁻¹) * (h * v * h⁻¹)⁻¹ by group]
      exact hconj
    have hcore : V ⊓ conjSubgroup V h ≤ Subgroup.zpowers z := by
      by_contra hnot
      exact hhM (s16c1_core_bot_V D hSg h1219 hkit hS hc hr hz hz1 h hh hnot)
    have hcent : ∀ w ∈ conjSubgroup V h, ∀ v ∈ V, w * v * w⁻¹ = v := by
      intro w hw
      have hwstab : w ∈ stabTil (⊥ : Subgroup G) V :=
        ⟨hWnV hw, by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top _⟩
      have hwbar : actTil (⊥ : Subgroup G) V hV ⟨w, hwstab⟩ ∈ lBar (⊥ : Subgroup G) V hV L := by
        have h43w := h43 (⊥ : Subgroup G) V L hV hS hc 0 (conjSubgroup V h) h
          (s16c1_hyp1643_conj_V D hV (hle h hh))
        exact h43w (actTil_mem_barSub (⊥ : Subgroup G) V hV hw hwstab)
      refine s16c1_centralizes_of_comm_le_zpowers
        ((hkit (Vtil (⊥ : Subgroup G) V hV) (lBar (⊥ : Subgroup G) V hV L) hc.2.1).2.2)
        hz hz1 hwstab hwbar ?_
      intro v hv
      have hmemV : w * v * w⁻¹ * v⁻¹ ∈ V := by
        have h1 : w * v * w⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hWnV hw) v).mp hv
        exact V.mul_mem h1 (V.inv_mem hv)
      have hmemW : w * v * w⁻¹ * v⁻¹ ∈ conjSubgroup V h := by
        have h2 : v * w⁻¹ * v⁻¹ ∈ conjSubgroup V h :=
          (Subgroup.le_normalizer_iff.mp hVnW v hv w⁻¹ ((conjSubgroup V h).inv_mem hw))
        have h3 : w * (v * w⁻¹ * v⁻¹) = w * v * w⁻¹ * v⁻¹ := by group
        rw [← h3]
        exact (conjSubgroup V h).mul_mem hw h2
      exact hcore (Subgroup.mem_inf.mpr ⟨hmemV, hmemW⟩)
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (mul_inv_eq_iff_eq_mul.mp (hcent w hw v hv)).symm

theorem s16c1_V_le_pCoreOf_of_comm {V : Subgroup G} {z : G} (hV : IsElemAbelian 2 V) (hz : z ∈ V)
    (hcomm : ∀ h ∈ centralizer ({z} : Set G), ⁅V, conjSubgroup V h⁆ = ⊥) :
    V ≤ pCoreOf 2 (centralizer ({z} : Set G)) := by
  let H := centralizer ({z} : Set G)
  let Y := hConjClosure z V
  have hYdef : Y = hConjClosure z V := rfl
  have hVH : V ≤ H := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    letI : IsMulCommutative ↥V := hV.1
    exact congrArg Subtype.val (mul_comm' (⟨z, hz⟩ : ↥V) (⟨v, hv⟩ : ↥V))
  have hVkH : ∀ k : ↥H, conjSubgroup V (k : G) ≤ H := by
    intro k
    calc conjSubgroup V (k : G) ≤ conjSubgroup H (k : G) :=
          E3.conjSubgroup_mono_left (k : G) hVH
      _ = H := (conjSubgroup_eq_iff_mem_normalizer (A := H) (g := (k : G))).2
                  (Subgroup.le_normalizer k.2)
  have hYH : Y ≤ H := by
    rw [hYdef, hConjClosure]
    exact iSup_le hVkH
  have hYcl : ⁅Y, Y⁆ ≤ (⊥ : Subgroup G) ∧ ∀ e ∈ Y, e ^ 2 ∈ (⊥ : Subgroup G) := by
    let T : Set G := ⋃ k : ↥H, (conjSubgroup V k : Set G)
    have hX : Subgroup.closure T = Y := by
      show Subgroup.closure (⋃ k : ↥H, (conjSubgroup V k : Set G)) = hConjClosure z V
      rw [hConjClosure]
      exact (Subgroup.iSup_eq_closure (fun k : ↥H => conjSubgroup V k)).symm
    have hZ : ∀ c ∈ (⊥ : Subgroup G), ∀ x ∈ Y, c * x = x * c := by
      intro c hc x hx
      rw [Subgroup.mem_bot] at hc
      subst hc
      rw [one_mul, mul_one]
    have hsq : ∀ a ∈ T, a ^ 2 ∈ (⊥ : Subgroup G) := by
      intro a ha
      change a ∈ (⋃ k : ↥H, (conjSubgroup V k : Set G)) at ha
      rw [Set.mem_iUnion] at ha
      obtain ⟨k, hk⟩ := ha
      have hkaV : (k : G) * a * (k : G)⁻¹ ∈ V := mem_conjSubgroup_iff.mp hk
      have hsq1 : ((k : G) * a * (k : G)⁻¹) ^ 2 = 1 := hV.2 _ hkaV
      have hconj : ((k : G) * a * (k : G)⁻¹) ^ 2 = (k : G) * a ^ 2 * (k : G)⁻¹ := by
        rw [show (k : G) * a * (k : G)⁻¹ = MulAut.conj (k : G) a by
          simp [MulAut.conj_apply]]
        rw [← map_pow (MulAut.conj (k : G)) a 2]
        simp [MulAut.conj_apply]
      have hcalc : a ^ 2 = (k : G)⁻¹ * ((k : G) * a * (k : G)⁻¹) ^ 2 * (k : G) := by
        rw [hconj]
        group
      rw [hcalc, hsq1]
      simp
    have hcommE : ∀ a ∈ T, ∀ b ∈ T, ⁅a, b⁆ ∈ (⊥ : Subgroup G) := by
      intro a ha b hb
      change a ∈ (⋃ k : ↥H, (conjSubgroup V k : Set G)) at ha
      change b ∈ (⋃ k : ↥H, (conjSubgroup V k : Set G)) at hb
      rw [Set.mem_iUnion] at ha hb
      obtain ⟨k, hak⟩ := ha
      obtain ⟨k', hbk⟩ := hb
      have hk : (k : G) * (k' : G)⁻¹ ∈ H := H.mul_mem k.2 (H.inv_mem k'.2)
      have ha'' : (k' : G) * a * (k' : G)⁻¹ ∈ conjSubgroup V ((k : G) * (k' : G)⁻¹) := by
        rw [mem_conjSubgroup_iff]
        rw [show ((k : G) * (k' : G)⁻¹) * ((k' : G) * a * (k' : G)⁻¹) *
              ((k : G) * (k' : G)⁻¹)⁻¹ = (k : G) * a * (k : G)⁻¹ by group]
        exact mem_conjSubgroup_iff.mp hak
      have hb' : (k' : G) * b * (k' : G)⁻¹ ∈ V := mem_conjSubgroup_iff.mp hbk
      have hcommut : ⁅(k' : G) * a * (k' : G)⁻¹, (k' : G) * b * (k' : G)⁻¹⁆ = 1 := by
        have hleC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (hcomm ((k : G) * (k' : G)⁻¹) hk)
        have hxy : ((k' : G) * a * (k' : G)⁻¹) * ((k' : G) * b * (k' : G)⁻¹) =
            ((k' : G) * b * (k' : G)⁻¹) * ((k' : G) * a * (k' : G)⁻¹) :=
          (Subgroup.mem_centralizer_iff.mp (hleC hb')) ((k' : G) * a * (k' : G)⁻¹) ha''
        exact commutatorElement_eq_one_iff_mul_comm.mpr hxy
      have hcb : ⁅a, b⁆ = (k' : G)⁻¹ *
          ⁅(k' : G) * a * (k' : G)⁻¹, (k' : G) * b * (k' : G)⁻¹⁆ * (k' : G) := by
        simp only [commutatorElement_def]
        group
      rw [hcb, hcommut]
      simp
    exact s16c1_closure_comm_sq (T := T) (X := Y) (Z := (⊥ : Subgroup G)) hX hZ hcommE hsq
  have hYcomm : ⁅Y, Y⁆ = ⊥ := le_bot_iff.mp hYcl.1
  have hYsq : ∀ e ∈ Y, e ^ 2 = 1 := fun e he => Subgroup.mem_bot.mp (hYcl.2 e he)
  have hpgY : IsPGroup 2 Y := fun y => ⟨1, Subtype.ext (by simpa using hYsq (y : G) y.2)⟩
  have hYnorm : H ≤ normalizer (Y : Set G) := by
    intro k hk
    refine (conjSubgroup_eq_iff_mem_normalizer (A := Y) (g := k)).1 ?_
    have hconj := s16c1_conjSubgroup_hConjClosure V hk
    rwa [← hYdef] at hconj
  have hnormal : (Y.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYH).2 hYnorm
  have hpg : IsPGroup 2 (Y.subgroupOf H) :=
    hpgY.of_equiv (Subgroup.subgroupOfEquivOfLe hYH).symm
  have hle_pCore : Y.subgroupOf H ≤ CFSG.pCore 2 ↥H :=
    le_sSup (s := {K : Subgroup ↥H | K.Normal ∧ IsPGroup 2 K}) ⟨hnormal, hpg⟩
  have hYle : Y ≤ pCoreOf 2 H := by
    calc Y = (Y.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hYH).symm
      _ ≤ (CFSG.pCore 2 ↥H).map H.subtype := Subgroup.map_mono hle_pCore
      _ = pCoreOf 2 H := rfl
  have hVY : V ≤ Y := by
    rw [hYdef, hConjClosure]
    calc V = conjSubgroup V (1 : G) := (conjSubgroup_one V).symm
      _ ≤ ⨆ k : ↥H, conjSubgroup V (k : G) :=
            le_iSup (fun k : ↥H => conjSubgroup V (k : G)) ⟨1, one_mem H⟩
  exact hVY.trans hYle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
