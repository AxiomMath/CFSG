module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CZD
public import CFSG.Quasithin.Vol2.Ch10SecQ3CZF

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I H K : Subgroup G} {n k : ℕ} {b : G}
  {hel : IsElemAbelian 2 (VZ T H)} {I' : Finset (Subgroup (MulAut (IntMod (VZ T H) hel)))}
  {K₀ : Subgroup (MulAut (IntMod (VZ T H) hel))}

namespace Ctx

variable (c : Ctx T L I H K n k b hel I' K₀)
include c

theorem all_natural : ∀ L' ∈ I', ∃ m, E2.IsL2Natural L' (fixV (autI hel (twoResidual H))) m := by
  intro L' hL'
  rcases c.hD.types L' hL' with h | h5
  · exact h
  · exfalso
    have hc := SecA.card_of_isL2Natural c.isL2Natural
    rw [SecA.card_of_isA5Module (isA5Module_of_isA5Module c.hD hL' h5 K₀ c.hK₀)] at hc
    exact SecA.two_pow_mul_ne_120 k hc.symm

omit [Finite G] c in
theorem twoResidual_le_normalizer :
    twoResidual H ≤ Subgroup.normalizer (VZ T H : Set G) :=
  (twoResidual_le H).trans (le_normalizer_conjClosure _ H)

theorem inf_centralizer_twoResidual_eq_bot :
    omegaOneCenterOf (thompsonJ T) ⊓ Subgroup.centralizer (twoResidual H : Set G) = ⊥ := by
  by_contra hne
  have hN : T ≤ Subgroup.normalizer ((omegaOneCenterOf (thompsonJ T) ⊓
      Subgroup.centralizer (twoResidual H : Set G) : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨le_normalizer_E T hx,
      SecA.le_normalizer_centralizer (le_normalizer_twoResidual H) (c.T_le_H hx)⟩
  obtain ⟨z, hz, hz1, hzZ⟩ := c.exists_mem_Z inf_le_left hN hne
  apply hz1 (c.eq_one_of_mem_centralizer_H hzZ _)
  have hzT := quasithinOmegaOneCenter_le_center T hzZ
  have hle : H ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [c.hHK]
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hz.2 x (c.K_le_twoResidual hx))
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzT.2 x hx)
  exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

theorem E_le_W : omegaOneCenterOf (thompsonJ T) ≤ VZ T H := by
  have h := (c.hD.two c.all_natural).2.2.2
  rw [c.inf_centralizer_twoResidual_eq_bot, sup_bot_eq] at h
  calc omegaOneCenterOf (thompsonJ T) ≤ conjClosure (omegaOneCenterOf (thompsonJ T))
        (twoResidual H) := le_conjClosure _ _
    _ = ⁅VZ T H, twoResidual H⁆ := h
    _ ≤ VZ T H := Subgroup.le_normalizer_iff_commutator_le_left.mp twoResidual_le_normalizer

theorem isSylowTwoOf_inf : IsSylowTwoOf (autI hel (thompsonJ T) ⊓ K₀) K₀ := by
  have hsyl := (c.hD.two c.all_natural).2.1
  have hKJ : K₀ ≤ autI hel (thompsonJ H) := by
    rw [c.hD.jeq]
    exact le_iSup₂ (f := fun L (_ : L ∈ I') => L) K₀ c.hK₀
  have hJN : autI hel (thompsonJ H) ≤ Subgroup.normalizer (K₀ : Set _) := by
    rw [c.hD.jeq]
    refine iSup₂_le fun L' hL' => ?_
    by_cases h : L' = K₀
    · rw [h]
      exact Subgroup.le_normalizer
    · exact SecE.le_normalizer_of_commute fun x hx y hy => c.hD.comm L' hL' K₀ c.hK₀ h x hx y hy
  exact A4.isSylowTwoOf_inf_normal hsyl hKJ hJN

theorem b_mem_normalizer_E :
    b ∈ Subgroup.normalizer (omegaOneCenterOf (thompsonJ T) : Set G) := by
  rw [← C1Pack.omegaOneCenterOf_baum]
  exact A4.normalizer_le_normalizer_omegaOneCenterOf _ c.hbS

theorem card_le_of_fix {A : Subgroup G}
    (hAE : A ≤ omegaOneCenterOf (thompsonJ T)) (hA : ∀ a ∈ A, b * a * b⁻¹ = a → a = 1) :
    Nat.card A ≤ 2 ^ k := by
  classical
  obtain ⟨F', _, hF', ψ, hψ⟩ := exists_fun_of_fix_sylow c.isL2Natural c.isSylowTwoOf_inf
  have hEW := c.E_le_W
  have hbE := c.b_mem_normalizer_E
  set E := omegaOneCenterOf (thompsonJ T) with hEdef
  have hw : ∀ e ∈ E, b * e * b⁻¹ * e⁻¹ ∈ E := fun e he =>
    E.mul_mem ((Subgroup.mem_normalizer_iff.mp hbE e).mp he) (E.inv_mem he)
  set x : ↥A → IntMod (VZ T H) hel := fun a =>
    IntMod.mk hel ⟨b * (a : G) * b⁻¹ * (a : G)⁻¹, hEW (hw a (hAE a.2))⟩ with hx
  have hxv : ∀ a : ↥A, (x a).val = b * (a : G) * b⁻¹ * (a : G)⁻¹ := fun a => rfl
  have hxK : ∀ a, x a ∈ commV K₀ := by
    intro a
    set ā : IntMod (VZ T H) hel := IntMod.mk hel ⟨a, hEW (hAE a.2)⟩ with hā
    have he : x a = c.autB ā * ā⁻¹ := IntMod.val_injective (by
      rw [hxv, IntMod.val_mul, IntMod.val_inv, convI_apply_val]
      rfl)
    rw [he]
    exact Subgroup.subset_closure ⟨c.autB, oTwoUpper_le _ c.autB_mem, ā, rfl⟩
  have hxP : ∀ a, ∀ p ∈ autI hel (thompsonJ T) ⊓ K₀, p (x a) = x a := by
    intro a p hp
    obtain ⟨g, hgJ, rfl⟩ := (mem_autI hel).mp hp.1
    refine IntMod.val_injective ?_
    rw [convI_apply_val, hxv]
    have hc := (A4.omegaOneCenterOf_le_centerOf _ (hw a (hAE a.2))).2
    rw [Subgroup.mem_centralizer_iff.mp hc _ hgJ, mul_inv_cancel_right]
  have hRN : twoResidual H ≤ Subgroup.normalizer (VZ T H : Set G) := twoResidual_le_normalizer
  have hinj : Function.Injective fun a => ψ (x a) := by
    intro a a' h
    have h1 := hψ _ (hxK a) _ (hxK a') (hxP a) (hxP a') h
    rw [mem_fixV_autI hel hRN, IntMod.val_mul, IntMod.val_inv, hxv, hxv] at h1
    have h2 : b * (a : G) * b⁻¹ * (a : G)⁻¹ * (b * (a' : G) * b⁻¹ * (a' : G)⁻¹)⁻¹ ∈
        E ⊓ Subgroup.centralizer (twoResidual H : Set G) :=
      ⟨E.mul_mem (hw a (hAE a.2)) (E.inv_mem (hw a' (hAE a'.2))), h1⟩
    rw [c.inf_centralizer_twoResidual_eq_bot, Subgroup.mem_bot, mul_inv_eq_one] at h2
    have h3' := mul_inv_eq_iff_eq_mul.mp h2
    have h3 : b * ((a' : G)⁻¹ * a) * b⁻¹ = (a' : G)⁻¹ * a := by
      calc b * ((a' : G)⁻¹ * a) * b⁻¹ = (b * (a' : G) * b⁻¹)⁻¹ * (b * (a : G) * b⁻¹) := by
            group
        _ = (b * (a' : G) * b⁻¹)⁻¹ * (b * (a' : G) * b⁻¹ * (a' : G)⁻¹ * a) := by rw [h3']
        _ = (a' : G)⁻¹ * a := by group
    have h4 := hA _ (A.mul_mem (A.inv_mem a'.2) a.2) h3
    exact Subtype.ext (by rw [inv_mul_eq_one] at h4; exact h4.symm)
  calc Nat.card A ≤ Nat.card F' := Nat.card_le_card_of_injective _ hinj
    _ = 2 ^ k := by rw [Nat.card_eq_fintype_card, hF']

end Ctx

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
