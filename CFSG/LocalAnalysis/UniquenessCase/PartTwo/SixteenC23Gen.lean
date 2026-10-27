module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23CoreB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Xz
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Idx
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Cfg
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Hyp141
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Til
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoStab

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c23_uniqueMax_generic (D : Data G) (hx : DataExt D) (h115 : F11.R115 D)
    (h127 : R127 D) (h1217 : R1217 D) (h119 : R119W D) (h145 : Thm145 D)
    {V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D ⊥ V L hV)
    (hc : Case167_2 D ⊥ V hV L) (hv1 : v1Sub D.M ⊥ V hV L = ⊥) {x : G} (hxM : x ∈ D.M)
    (hxn : x ∉ nBar D.M ⊥ V hV L) {w : G} (hwV : w ∈ V)
    (hw : mkTil ⊥ V hV (IntMod.mk hV ⟨w, hwV⟩) ∈
      c23Omega (wTil ⊥ V hV L) (wTil ⊥ V hV (conjSubgroup L x))) :
    UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have h151 := hS.setting.hyp151
  have hP := hS.setting.hyp16.hyp125.pairFacts
  have hMs : D.M ≤ stabTil ⊥ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  obtain ⟨hL3, hnat0, hs, hsig⟩ := hc
  have hnat := c23_binaryNatural_of_v1_eq_bot D.M hV hv1 hnat0
  have hcore := c23_core_of_case2 h1217 h151 hV hs hL3 hnat hv1 hxM hxn
  obtain ⟨K₁, K₂, hK₁, hK₂, hne, hbarA, hMN, hL₁, hL₂, hn₁, hn₂⟩ :=
    c23_lift_pair D h119 hV (Hyp125.hyp11 h127 h151.hyp125) h151 hs hL3 hxM hxn
      (fun a ha b hb => c23_core_commute hcore ha hb) (c23_core_inf_A_eq_bot hcore)
  have hK₁M : K₁ ≤ D.M := uc22p22a_le_of_isSubnormal hK₁.1
  have hK₂M : K₂ ≤ D.M := uc22p22a_le_of_isSubnormal hK₂.1
  obtain ⟨a, ha⟩ := s16c7_card_of_bar2 (s16c7_bar2_of_calC hV hMs hK₁M hK₁.2.2 hL₁).1
  obtain ⟨b, hb⟩ := s16c7_card_of_bar2 (s16c7_bar2_of_calC hV hMs hK₂M hK₂.2.2 hL₂).1
  obtain ⟨z, X, hΩ, hzT, hzX, hXsyl, hperm, hzN⟩ :=
    c23_exists_X_z D hV hMs hK₁M hK₂M hn₁ hMN ha hb hcore hbarA
  have h49 := c23_relIndex_inf_centralizer_eq D hV hMs hcore hΩ
  have h7 := c23_seven_dvd_card_inf D hx hsig h49
  have hH141 : Hyp141 D K₁ K₂ X :=
    c23_hyp141_of_case2 D hx h115 h127 h1217 hS ⟨hL3, hnat0, hs, hsig⟩ hK₁ hK₂ hne hL₁ hL₂
      hXsyl hperm
  have hUz := c23_uniqueMax_of_thm145 D h145 hH141 hzT hzX hzN h7
  obtain ⟨a₁, ha₁, b₁, hb₁, hab⟩ := c23_omega_trans hcore hΩ hw
  obtain ⟨g₁, hg₁M, rfl⟩ := (mem_barSub ⊥ V hV D.M a₁).1 (hcore.le₁ ha₁)
  obtain ⟨g₂, hg₂M, rfl⟩ := (mem_barSub ⊥ V hV D.M b₁).1 (hcore.le₂ hb₁)
  rw [actTil_mk, actTil_mk] at hab
  have hval := congrArg IntMod.val (s16c7_mkTil_injective V hV hab)
  rw [actStab_apply_val, actStab_apply_val] at hval
  have hval' : (g₁ : G) * ((g₂ : G) * z.val * (g₂ : G)⁻¹) * (g₁ : G)⁻¹ = w := hval
  have hconj : ((g₁ : G) * g₂)⁻¹ * w * (((g₁ : G) * g₂)⁻¹)⁻¹ = z.val := by
    rw [← hval']
    group
  refine c23_uniqueMax_of_conj D (m := ((g₁ : G) * g₂)⁻¹)
    (D.M.inv_mem (D.M.mul_mem hg₁M hg₂M)) ?_
  rw [hconj]
  exact hUz

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
