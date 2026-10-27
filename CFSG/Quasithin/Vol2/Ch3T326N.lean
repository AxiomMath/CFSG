module

public import CFSG.Quasithin.Vol2.Ch3T326D
public import CFSG.Quasithin.Vol2.Ch3T326M
public import CFSG.Quasithin.Vol2.Ch3T325E
public import CFSG.Quasithin.Vol2.Ch3T325I

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative
open T325 (M_le_NVM map_subgroupOf_conjAct)
open CFSG.Quasithin.Vol2.Ch10.SecA (conjugate_conjugate conjugate_one)

section Offender

variable {W : Type} [CommGroup W] [Finite W]

theorem exists_qhatStar_commSub_ne_bot {X S : Subgroup (MulAut W)} (hS : IsSylowTwoOf S X)
    (hq : qhatOf X ≤ ((2 : ℚ) : WithTop ℚ)) {U U' : Subgroup W} (hsup : U ⊔ U' = ⊤)
    {g : MulAut W} (hg : g ∈ S) (hgU : U'.map g.toMonoidHom = U) :
    ∃ A ∈ QhatStar X, A ≤ S ∧ commSub U A ≠ ⊥ := by
  have hne : qhatOf X ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hq
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
  have hr2 : r ≤ 2 := WithTop.coe_le_coe.mp (hr ▸ hq)
  obtain ⟨B, hB⟩ := QhatStar_nonempty hr.symm hr2
  have hB2 : IsPGroup 2 ↥B := by
    obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hB
    exact hA2.isElemAbelian2.isPGroup
  obtain ⟨x, hx, hBx⟩ := F7.isSylowTwoOf_exists_conj_le hS (QhatStar_le hB) hB2
  have hA : conjBy x⁻¹ B ∈ QhatStar X := conjBy_mem_QhatStar hB (X.inv_mem hx)
  have hAS : conjBy x⁻¹ B ≤ S := fun y hy => by
    rw [mem_conjBy_iff, inv_inv] at hy
    have h1 := hBx hy
    rw [mem_conjSub] at h1
    simpa [mul_assoc] using h1
  have hA2 : IsA2 X (conjBy x⁻¹ B) := by
    obtain ⟨r', -, -, ⟨⟨h, -⟩, -⟩, -⟩ := QhatStar_spec hA
    exact h
  by_cases hUA : commSub U (conjBy x⁻¹ B) = ⊥
  · refine ⟨conjBy g (conjBy x⁻¹ B), conjBy_mem_QhatStar hA (hS.1 hg), fun y hy => ?_,
      fun h => ?_⟩
    · rw [mem_conjBy_iff] at hy
      have e : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      rw [e]
      exact S.mul_mem (S.mul_mem hg (hAS hy)) (S.inv_mem hg)
    · rw [commSub_eq_bot_iff] at hUA h
      have hU' : U' ≤ fixV (conjBy x⁻¹ B) := by
        intro u hu a ha
        have hgu : g u ∈ U'.map g.toMonoidHom := ⟨u, hu, rfl⟩
        rw [hgU] at hgu
        have hga : g * a * g⁻¹ ∈ conjBy g (conjBy x⁻¹ B) := by
          rw [mem_conjBy_iff]
          have e : g⁻¹ * (g * a * g⁻¹) * g = a := by group
          rw [e]
          exact ha
        have h1 := h hgu _ hga
        simpa [MulAut.mul_apply] using h1
      have htop : (⊤ : Subgroup W) ≤ fixV (conjBy x⁻¹ B) := by
        rw [← hsup]
        exact sup_le hUA hU'
      apply hA2.ne_bot
      rw [eq_bot_iff]
      intro a ha
      rw [Subgroup.mem_bot]
      ext w
      simpa using htop (Subgroup.mem_top w) a ha
  · exact ⟨_, hA, hAS, hUA⟩

theorem qhatOf_autSub_le_of_qhatStar (hW : ∀ w : W, w ^ 2 = 1) {X Y A : Subgroup (MulAut W)}
    (hA : A ∈ QhatStar X) (hAY : A ≤ Y) {U : Subgroup W} (hU : A ≤ stabSub U)
    (hUA : commSub U A ≠ ⊥) : qhatOf (autSub Y U) ≤ ((2 : ℚ) : WithTop ℚ) := by
  obtain ⟨r, hr, hr2, ⟨⟨hA2, hAr⟩, hAk⟩, -⟩ := QhatStar_spec hA
  have hplus : A ∈ RPlus X := D2_3_2 hA2 hAk (by rw [hAr]; exact hr.symm)
  have hAY2 : IsA2 Y A := ⟨hAY, hA2.2⟩
  have h5 := D2_5 hW (X := Y) (A := A) (r := r) ⟨⟨hAY2, hAr.le⟩, hAY2, hplus.2⟩ hU hUA
  exact (kq_le_iff.mpr ⟨autSub A U, h5.1, commSeries_autSub_eq_bot hU hAk, h5.2⟩).trans
    (WithTop.coe_le_coe.mpr hr2)

end Offender

section Restrict

variable {G : Type} [Group G] {X U VM : Subgroup G} [IsMulCommutative ↥VM]
  [IsMulCommutative ↥U]

theorem autSub_map_le_autOn (hU : U ≤ VM) :
    (autSub (autOn X VM) (U.subgroupOf VM)).map
        (T325.congrHom (Subgroup.subgroupOfEquivOfLe hU)) ≤ autOn X U := by
  rintro _ ⟨φ, hφ, rfl⟩
  obtain ⟨h, hhD, rfl⟩ := mem_autSub.mp hφ
  obtain ⟨g, hgX, hg⟩ := Setup.mem_autOn_iff.mp hhD
  have hgU : (g : G) ∈ Subgroup.normalizer (U : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    by_cases hn : n ∈ VM
    · have h1 := mem_stabSub.mp h.2 ⟨n, hn⟩
      rw [← hg, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Setup.coe_conjAct_apply] at h1
      exact h1.symm
    · refine iff_of_false (fun h' => hn (hU h')) (fun h' => hn ?_)
      exact (Subgroup.mem_normalizer_iff.mp g.2 n).mpr (hU h')
  refine Setup.mem_autOn_iff.mpr ⟨⟨(g : G), hgU⟩, hgX, ?_⟩
  ext u
  rw [T325.congrHom_apply, Setup.coe_conjAct_apply]
  change _ = (((h : MulAut ↥VM) ((Subgroup.subgroupOfEquivOfLe hU).symm u : ↥VM)) : G)
  rw [← hg, Setup.coe_conjAct_apply]
  rfl

theorem qhatOf_autOn_le_autSub [Finite G] (hU : U ≤ VM) :
    qhatOf (autOn X U) ≤ qhatOf (autSub (autOn X VM) (U.subgroupOf VM)) :=
  (kq_le_kq_of_le216 (autSub_map_le_autOn hU) 3).trans
    (T325.kq_map_congr_le (Subgroup.subgroupOfEquivOfLe hU) _ 3)

end Restrict

namespace Ctx

variable {G : Type} [Group G] [Finite G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem sylow_autOn : IsSylowTwoOf
    (autOn T (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
    (autOn (Subgroup.normalizer (conjClosure L T : Set G))
      (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))) := by
  have hMW := M_le_NVM T (conjClosure L T) V₀
  have h := isSylowTwoOf_map_subgroupOf ((conjAct _).comp (Subgroup.inclusion hMW)) c.sylowM
  rwa [map_subgroupOf_conjAct c.T_le_M hMW, map_subgroupOf_conjAct le_rfl hMW] at h

theorem qhat_U (h316 : Theorem316Statement) (hA37 : Vol2Native.A37ForSQTKCat)
    (hA38 : Vol2Native.A38ForSQTKCat)
    [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))]
    (hacts : ∀ A ∈ QhatStar (V := ↥(conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))))
        (autOn (Subgroup.normalizer (conjClosure L T : Set G))
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))),
      ∀ a ∈ A, ∀ u : ↥(conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G))),
        (u : G) ∈ ⁅conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ →
        ((a u : ↥(conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)))) : G) ∈
          ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆) :
    ∃ _ : IsMulCommutative ↥⁅conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G)), L⁆,
      qhatOf (V := ↥⁅conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)), L⁆)
        (autOn (conjClosure L T ⊔ T) ⁅conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)), L⁆) ≤ 2 := by
  obtain ⟨t, ht, htn⟩ := c.exists_t
  have hsup := c.sup_U hA37 hA38 ht htn
  have hTW := c.T_le_NVM
  have hsyl := c.sylow_autOn
  obtain ⟨_, hq⟩ := qhat_VM h316 c
  have hUVM := Subgroup.le_normalizer_iff_commutator_le_left.mp c.L_le_NVM
  have hUtVM : CFSG.conjugate ⁅conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ t ≤
      conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) :=
    le_of_le_of_eq (Subgroup.map_mono hUVM) (c.conjugate_VM (c.T_le_M ht))
  have hexp : ∀ w : ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G))), w ^ 2 = 1 :=
    fun w => Subtype.ext (by simpa using c.elemVM.2 w w.2)
  set VM := conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))
    with hVMdef
  set U := ⁅VM, L⁆ with hUdef
  have hUc : IsMulCommutative ↥U := isMulCommutative_anti hUVM
  refine ⟨hUc, ?_⟩
  have hsup' : U.subgroupOf VM ⊔ (CFSG.conjugate U t).subgroupOf VM = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hUVM hUtVM, hsup, Subgroup.subgroupOf_self]
  have hgU : ((CFSG.conjugate U t).subgroupOf VM).map
      (conjAct VM ⟨t, hTW ht⟩).toMonoidHom = U.subgroupOf VM := by
    rw [map_conjAct_subgroupOf hUtVM]
    change (CFSG.conjugate (CFSG.conjugate U t) t⁻¹).subgroupOf VM = _
    rw [conjugate_conjugate, mul_inv_cancel, conjugate_one]
  have hgT : conjAct VM ⟨t, hTW ht⟩ ∈ autOn T VM :=
    Setup.mem_autOn_iff.mpr ⟨⟨t, hTW ht⟩, ht, rfl⟩
  obtain ⟨A, hA, hAT, hUA⟩ :=
    exists_qhatStar_commSub_ne_bot hsyl (by exact_mod_cast hq) hsup' hgT hgU
  have hAU : A ≤ stabSub (U.subgroupOf VM) := by
    intro a ha
    rw [mem_stabSub]
    intro w
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 := hacts A hA a⁻¹ (A.inv_mem ha) (a w) h
      rwa [MulAut.inv_apply_self] at h1
    · exact hacts A hA a ha w
  have hAY : A ≤ autOn (conjClosure L T ⊔ T) VM := fun a ha => by
    obtain ⟨g, hg, rfl⟩ := Setup.mem_autOn_iff.mp (hAT ha)
    exact Setup.mem_autOn_iff.mpr ⟨g, Subgroup.mem_sup_right hg, rfl⟩
  have h1 := qhatOf_autSub_le_of_qhatStar hexp hA hAY hAU hUA
  have h2 := qhatOf_autOn_le_autSub (X := conjClosure L T ⊔ T) hUVM
  exact_mod_cast h2.trans h1

end Ctx

end CFSG.Quasithin.H13.T326
