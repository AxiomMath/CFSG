module

public import CFSG.RankThree.PartTwo.J2Residue.C4725Module

public section

namespace CFSG.RankThree.PartTwo.J2Residue.C4725

open CFSG.ComponentClassification.J2Cover.Models CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.J2.Module12

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
attribute [local irreducible] phiL sec Psi

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem exists_linearEquiv_of_fixed
    [Finite V] [Nontrivial V]
    (ρ : P →* Module.End (ZMod 2) V)
    (hirr : ∀ U : Submodule (ZMod 2) V, (∀ g : P, ∀ u ∈ U, ρ g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hfix : ∀ u : V, ρ x0P u = u → u = 0) :
    ∃ θ : (Fin 12 → ZMod 2) ≃ₗ[ZMod 2] V,
      ∀ j < 2, ∀ y, θ ((Mj j).mulVec y) = ρ (letterP j) (θ y) := by
  obtain ⟨v, hv0, hv⟩ := exists_fixed_ne_zero ρ
  have hT : ∀ j < 2, ∀ f ∈ LinearMap.ker (phiL ρ v) ⊓ LinearMap.ker Psi,
      T (letterP j) f ∈ LinearMap.ker (phiL ρ v) ⊓ LinearMap.ker Psi := by
    intro j hj f hf
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hf
    refine Submodule.mem_inf.2 ⟨?_, Psi_T_eq_zero hj h2⟩
    rw [LinearMap.mem_ker] at h1 ⊢
    rw [phiL_T ρ hv, h1, map_zero]
  have hO : ∀ a : Fin 4725, ev a + ev (cosetAct a x0P) + ev (cosetAct (cosetAct a x0P) x0P) ∈
      LinearMap.ker (phiL ρ v) ⊓ LinearMap.ker Psi := fun a =>
    Submodule.mem_inf.2 ⟨phiL_orbit ρ hv hfix a, Psi_orbit a⟩
  have hZ := range_sec_sup_eq_top _ hT hO
  have hker : ∀ f, Psi f = 0 → phiL ρ v f = 0 := by
    intro f hf
    have hf' : f ∈ LinearMap.range sec ⊔ (LinearMap.ker (phiL ρ v) ⊓ LinearMap.ker Psi) :=
      hZ ▸ Submodule.mem_top
    obtain ⟨u, ⟨y, rfl⟩, w, hw, rfl⟩ := Submodule.mem_sup.1 hf'
    obtain ⟨hw1, hw2⟩ := Submodule.mem_inf.1 hw
    rw [map_add, Psi_sec, LinearMap.mem_ker.1 hw2, add_zero] at hf
    rw [map_add, hf, map_zero, map_zero, zero_add]
    exact hw1
  have hθ : ∀ f, phiL ρ v f = phiL ρ v (sec (Psi f)) := by
    intro f
    have h0 : Psi (f - sec (Psi f)) = 0 := by
      rw [map_sub, Psi_sec]
      exact sub_self _
    have h := hker _ h0
    rwa [map_sub, sub_eq_zero] at h
  have hθM : ∀ j < 2, ∀ y,
      phiL ρ v (sec ((Mj j).mulVec y)) = ρ (letterP j) (phiL ρ v (sec y)) := by
    intro j hj y
    have hf : T (letterP j) (T (letterP j)⁻¹ (sec y)) = sec y := T_inv_apply _ _
    have h1 : (Mj j).mulVec y = Psi (T (letterP j)⁻¹ (sec y)) := by
      rw [← Mj_mulVec_Psi_T hj, hf, Psi_sec]
    rw [h1, ← hθ, phiL_T ρ hv, inv_inv]
  have hstab : ∀ j < 2, ∀ y ∈ LinearMap.ker ((phiL ρ v).comp sec),
      (Mj j).mulVec y ∈ LinearMap.ker ((phiL ρ v).comp sec) := by
    intro j hj y hy
    rw [LinearMap.mem_ker, LinearMap.comp_apply] at hy ⊢
    rw [hθM j hj, hy, map_zero]
  have hirr12 := eq_bot_or_eq_top_of_mulVec_mem (LinearMap.ker ((phiL ρ v).comp sec))
    (fun y hy => Mj_zero ▸ hstab 0 (by norm_num) y hy)
    (fun y hy => Mj_one ▸ hstab 1 (by norm_num) y hy)
  have hφ0 : phiL ρ v (ev 0) = v := by
    rw [phiL_ev, show repP ((0 : Fin 4725) : ℕ) = 1 from Subtype.ext rep_zero, inv_one, map_one,
      Module.End.one_apply]
  have hinj : Function.Injective ((phiL ρ v).comp sec) := by
    rcases hirr12 with h | h
    · exact LinearMap.ker_eq_bot.1 h
    · exfalso
      apply hv0
      have h0 : (phiL ρ v).comp sec (Psi (ev 0)) = 0 :=
        LinearMap.mem_ker.1 (h ▸ Submodule.mem_top)
      rw [LinearMap.comp_apply, ← hθ, hφ0] at h0
      exact h0
  have hsurj : Function.Surjective ((phiL ρ v).comp sec) := by
    have hstabφ : ∀ g : P, ∀ u ∈ LinearMap.range (phiL ρ v),
        ρ g u ∈ LinearMap.range (phiL ρ v) := by
      rintro g u ⟨f, rfl⟩
      exact ⟨T g⁻¹ f, by rw [phiL_T ρ hv, inv_inv]⟩
    rcases hirr _ hstabφ with h | h
    · exfalso
      apply hv0
      have : phiL ρ v (ev 0) ∈ LinearMap.range (phiL ρ v) := ⟨ev 0, rfl⟩
      rw [h, Submodule.mem_bot, hφ0] at this
      exact this
    · intro u
      obtain ⟨f, hf⟩ : u ∈ LinearMap.range (phiL ρ v) := h ▸ Submodule.mem_top
      exact ⟨Psi f, by rw [LinearMap.comp_apply, ← hθ, hf]⟩
  have happ : ∀ x, LinearEquiv.ofBijective ((phiL ρ v).comp sec) ⟨hinj, hsurj⟩ x =
      phiL ρ v (sec x) := fun x => rfl
  refine ⟨LinearEquiv.ofBijective ((phiL ρ v).comp sec) ⟨hinj, hsurj⟩, fun j hj y => ?_⟩
  rw [happ, happ]
  exact hθM j hj y

end CFSG.RankThree.PartTwo.J2Residue.C4725
