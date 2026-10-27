module

public import CFSG.Quasithin.Vol2.Ch10SecDTL3
public import CFSG.Quasithin.Vol2.Ch10SecDFacts211b
public import CFSG.Quasithin.Vol2.Ch10SecDTL2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

theorem factTransvList_of (hG31 : ASInputs.AS_G_3_1_O2) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h1029 : Stmt10_2_9) : FactTransvList := by
  intro G _ _ T L I h h3 hc t v₁ v₂ hd _ hR2 hE _
  exfalso
  have hd' := hd
  obtain ⟨ht, htn, hv1, hv11, hv2, hv21⟩ := hd'
  set Gz := Subgroup.centralizer ({v₁ * v₂} : Set G) with hGz
  set W := Vz v₁ v₂ with hW
  have h1 := stmt10_2_11_one h37 h38 h1029 h h3 hc hd
  have hcommW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (h1.1 hb).2) a (h1.1 ha).1
  have hsqW := sq_eq_one_of_mem_Vz h37 h38 h1029 h h3 hc hd
  have hEGz := closure_le_centralizer_z h hd
  have hWGz : W ≤ Gz := conjClosure_le fun g hg e he =>
    Gz.mul_mem (Gz.mul_mem hg (hEGz he)) (Gz.inv_mem hg)
  have hGzN : Gz ≤ Subgroup.normalizer (W : Set G) := le_normalizer_conjClosure _ _
  have hEW : Subgroup.closure {v₁, v₂} ≤ W := le_conjClosure _ _
  have hv1E : v₁ ∈ Subgroup.closure {v₁, v₂} := Subgroup.subset_closure (Set.mem_insert _ _)
  have hv2E : v₂ ∈ Subgroup.closure {v₁, v₂} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hv1W := hEW hv1E
  have hv2W := hEW hv2E
  have : IsMulCommutative ↥W := ⟨⟨fun x y => Subtype.ext (hcommW _ x.2 _ y.2)⟩⟩
  have hWN1 : W ≤ Subgroup.normalizer (fsuUL T L I : Set G) := fun w hw =>
    (h1.2 ⟨hWGz hw, Subgroup.mem_centralizer_iff.mpr fun x hx => hcommW x hx w hw⟩).2
  obtain ⟨hcomm, -⟩ := h.three
  have hVab : ∀ x ∈ fsuVM T L I, ∀ y ∈ fsuVM T L I, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hle2 : ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ fsuVM T L I :=
    commutator_le_left_of_le_normalizer
      ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  have hzV : v₁ * v₂ ∈ fsuVM T L I := (fsuVM T L I).mul_mem (V1_le_V hv1.1) (hle2 hv2.1)
  have hV1Gz : fsuUL T L I ≤ Gz := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hVab u (V1_le_V hu) _ hzV)
  have hV1N : fsuUL T L I ≤ Subgroup.normalizer (W : Set G) := hV1Gz.trans hGzN
  have hcomm1 : ∀ w ∈ W, ∀ u ∈ fsuUL T L I,
      u * w * u⁻¹ * w⁻¹ = 1 ∨ u * w * u⁻¹ * w⁻¹ = v₁ := by
    intro w hw u hu
    have hcW : u * w * u⁻¹ * w⁻¹ ∈ W :=
      W.mul_mem ((Subgroup.mem_normalizer_iff.mp (hV1N hu) w).mp hw) (W.inv_mem hw)
    have hc1 : u * w * u⁻¹ * w⁻¹ ∈ fsuUL T L I := by
      have h2 : w * u⁻¹ * w⁻¹ ∈ fsuUL T L I :=
        (Subgroup.mem_normalizer_iff.mp (hWN1 hw) u⁻¹).mp ((fsuUL T L I).inv_mem hu)
      have := (fsuUL T L I).mul_mem hu h2
      rwa [show u * (w * u⁻¹ * w⁻¹) = u * w * u⁻¹ * w⁻¹ by group] at this
    have hcE : u * w * u⁻¹ * w⁻¹ ∈ Subgroup.closure {v₁, v₂} := by
      rw [← hE]
      exact ⟨V1_le_V hc1, Subgroup.mem_centralizer_iff.mpr fun x hx => hcommW x hx _ hcW⟩
    exact eq_one_or_eq_of_mem_E h37 h38 h hc hd hcE hc1
  have hv1sq : v₁ ^ 2 = 1 := (SecA.isElemAbelian_fsuVM h).2 v₁ (V1_le_V hv1.1)
  have hCV1 : fsuUL T L I ⊓ Subgroup.centralizer (W : Set G) = Subgroup.zpowers v₁ := by
    apply le_antisymm
    · rintro c ⟨hc1, hcC⟩
      have hcE : c ∈ Subgroup.closure {v₁, v₂} := by
        rw [← hE]
        exact ⟨V1_le_V hc1, hcC⟩
      exact (mem_zpowers_iff_of_sq hv1sq).mpr (eq_one_or_eq_of_mem_E h37 h38 h hc hd hcE hc1)
    · rw [Subgroup.zpowers_le]
      have hv1VC : v₁ ∈ fsuVM T L I ⊓ Subgroup.centralizer (W : Set G) := by
        rw [hE]
        exact hv1E
      exact ⟨hv1.1, hv1VC.2⟩
  have hcard4 : Nat.card (autOn (fsuUL T L I) W) = 4 := by
    rw [card_autOn_eq_relIndex hV1N, hCV1]
    have hm := Subgroup.relIndex_mul_card (Subgroup.zpowers v₁) (fsuUL T L I)
    rw [inf_of_le_left ((Subgroup.zpowers_le).mpr hv1.1), card_V1 h3 hc,
      card_zpowers_of_sq hv1sq hv11] at hm
    omega
  set a : ↥W := ⟨v₁, hv1W⟩ with ha_def
  set b : ↥W := ⟨v₂, hv2W⟩ with hb_def
  have hasq : a ^ 2 = 1 := Subtype.ext (by simpa using hsqW v₁ hv1W)
  have hsub : autOn (fsuUL T L I) W ≤ ASInputs.transvGroup (autOn Gz W) (Subgroup.zpowers a) := by
    intro σ hσ
    apply Subgroup.subset_closure
    refine ⟨A4.autOn_mono hV1Gz hσ, fun v => ?_⟩
    obtain ⟨⟨u, huN⟩, hu, rfl⟩ := mem_autOn_iff.mp hσ
    rw [mem_zpowers_iff_of_sq hasq]
    rcases hcomm1 v v.2 u hu with h2 | h2
    · exact Or.inl (Subtype.ext h2)
    · exact Or.inr (Subtype.ext h2)
  have hA : 4 ≤ Nat.card (ASInputs.transvGroup (autOn Gz W) (Subgroup.zpowers a)) := by
    rw [← hcard4]
    exact Subgroup.card_le_of_le hsub
  obtain ⟨hn, -, hR⟩ := hR2
  have hO2 := pCoreOf_autOn_eq_bot hWGz hGzN hR
  have htGz : t⁻¹ ∈ Gz := Gz.inv_mem (T_le_centralizer_z h37 h38 h h3 hc hd ht)
  have hg₁ : conjAct W ⟨t⁻¹, hGzN htGz⟩ ∈ autOn Gz W :=
    mem_autOn_iff.mpr ⟨_, htGz, rfl⟩
  have hg₁a : conjAct W ⟨t⁻¹, hGzN htGz⟩ a = b := by
    apply Subtype.ext
    show t⁻¹ * v₁ * t⁻¹⁻¹ = v₂
    rw [inv_inv, ← conj_v2 h37 h38 h h3 hc hd]
    group
  have hfix : ∀ g ∈ autOn Gz W, g (a * b) = a * b := by
    intro g hg
    obtain ⟨⟨x, hxN⟩, hx, rfl⟩ := mem_autOn_iff.mp hg
    apply Subtype.ext
    show x * (v₁ * v₂) * x⁻¹ = v₁ * v₂
    rw [Subgroup.mem_centralizer_singleton_iff.mp hx, mul_inv_cancel_right]
  have hV : ∀ v : ↥W, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hsqW v v.2)
  have ha : a ≠ 1 := fun h' => hv11 (congrArg Subtype.val h')
  have hb : b ≠ 1 := fun h' => hv21 (congrArg Subtype.val h')
  have hab : a ≠ b := fun h' => by
    have h12 : v₁ = v₂ := congrArg Subtype.val h'
    have hm : v₁ ∈ fsuUL T L I ⊓ ⁅fsuVM T L I, CFSG.conjugate L t⁆ := ⟨hv1.1, h12 ▸ hv2.1⟩
    rw [V1_inf_V2 h37 h38 h hc ht htn, Subgroup.mem_bot] at hm
    exact hv11 hm
  exact false_of_g31 hG31 hV hO2 ha hb hab hA hg₁ hg₁a hfix

end CFSG.Quasithin.Vol2.Ch10.SecD
