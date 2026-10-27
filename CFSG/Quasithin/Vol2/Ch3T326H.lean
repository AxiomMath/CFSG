module

public import CFSG.Quasithin.Background.F918J3
public import CFSG.Quasithin.Vol2.Ch3T326E
public import CFSG.Quasithin.Vol2.Ch3T326F

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative
open T325 (M_le_NVM)

section Models

variable {W : Type} [CommGroup W]

theorem realizes_of_autSub_top {D : FFModel} {Mp : Subgroup (MulAut W)}
    (h : D.Realizes (autSub Mp (⊤ : Subgroup W)) ⊤ ⊥) : D.Realizes Mp ⊤ ⊥ := by
  have hfaith : Mp ⊓ centSub (⊤ : Subgroup W) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    ext w
    exact hg.2 w trivial
  have hbot : Mp ≤ stabSub (⊥ : Subgroup W) := fun g _ u => by simp [Subgroup.mem_bot]
  refine FFModel.Realizes.of_autSub (le_stabSub_top Mp) hbot bot_le hfaith ?_
  rwa [Subgroup.bot_subgroupOf]

theorem realizes_of_autSub_eq_top {D : FFModel} {Mp : Subgroup (MulAut W)} {U : Subgroup W}
    (hU : U = ⊤) (h : D.Realizes (autSub Mp U) ⊤ ⊥) : D.Realizes Mp ⊤ ⊥ := by
  subst hU
  exact realizes_of_autSub_top h

theorem lieModel_of_isPSL {X : Type} [Group X] {n p e : ℕ} (h : IsPSL n p e X) :
    CFSG.Blueprint.LieModel X .PSL n p e :=
  Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], h⟩

end Models

namespace Ctx

variable {G : Type} [Group G] [Finite G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem autOn_L₀_eq (hA37 : Vol2Native.A37ForSQTKCat) (hA38 : Vol2Native.A38ForSQTKCat)
    [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))] {s : G}
    (hs : s ∈ T) (hsn : s ∉ Subgroup.normalizer (L : Set G)) :
    autOn (conjClosure L T)
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) =
      autOn L (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) ⊔
        conjAutSub (conjAct (conjClosure (conjClosure V₀ T)
            (Subgroup.normalizer (conjClosure L T : Set G))) ⟨s⁻¹, c.T_le_NVM (T.inv_mem hs)⟩)
          (autOn L (conjClosure (conjClosure V₀ T)
            (Subgroup.normalizer (conjClosure L T : Set G)))) := by
  set VM := conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))
    with hVM
  have hLs : CFSG.conjugate L s ≤ Subgroup.normalizer (VM : Set G) :=
    (Vol2.Ch10.SecA.conjugate_le_fsuL0 hs).trans c.L₀_le_NVM
  have e : autOn (conjClosure L T) VM = autOn (L ⊔ CFSG.conjugate L s) VM :=
    congrArg (fun X => autOn X VM) (c.L₀_eq hA37 hA38 hs hsn)
  rw [e, H13.autOn_sup c.L_le_NVM hLs]
  exact congrArg (autOn L VM ⊔ ·) (autOn_conjugate c.L_le_NVM (c.T_le_NVM (T.inv_mem hs)))

theorem not_mem_normalizer (hA37 : Vol2Native.A37ForSQTKCat)
    [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))] {s : G} (hs : s ∈ T)
    (hsn : s ∉ Subgroup.normalizer (L : Set G)) :
    conjAct (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))
        ⟨s⁻¹, c.T_le_NVM (T.inv_mem hs)⟩ ∉
      Subgroup.normalizer (autOn L (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))) : Set _) := by
  set VM := conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))
    with hVM
  set K := autOn L VM with hK
  set t := conjAct VM ⟨s⁻¹, c.T_le_NVM (T.inv_mem hs)⟩ with ht
  intro htn
  have hconj : autOn (CFSG.conjugate L s) VM = conjAutSub t K :=
    autOn_conjugate c.L_le_NVM (c.T_le_NVM (T.inv_mem hs))
  have hab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x := by
    intro x hx y hy
    have hy' : t⁻¹ * y * t ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (K : Set (MulAut ↥VM))).inv_mem htn) y).mp hy
      rwa [inv_inv] at this
    have hyc : y ∈ autOn (CFSG.conjugate L s) VM := by
      rw [hconj]
      show y ∈ K.map (MulAut.conj t).toMonoidHom
      refine Subgroup.mem_map.2 ⟨t⁻¹ * y * t, hy', ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    exact c.commute_autOn hA37 hs hsn hx hyc
  have hq := c.quasi_LVM
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hq.1
  have hbot : ⁅K, K⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => hab y hy x hx
  rw [hperf] at hbot
  have := CFSG.LocalCores.isQuasisimple_nontrivial hq
  exact (Subgroup.nontrivial_iff_ne_bot K).mp this hbot

end Ctx

end CFSG.Quasithin.H13.T326
