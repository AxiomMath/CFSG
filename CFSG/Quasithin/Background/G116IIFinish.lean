module

public import CFSG.Quasithin.Background.G116IIModule
public import CFSG.Quasithin.Background.G116IIStruct

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem selfDual_of_restrictRange_top {H : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}
    (hHI : Invariant H I) (h : SelfDual (restrictRange H I hHI) ⊤) : SelfDual H I := by
  obtain ⟨f, hnd, hinv⟩ := h
  let e : ↥(⊤ : Submodule (ZMod 2) ↥I) ≃ₗ[ZMod 2] ↥I := Submodule.topEquiv
  refine ⟨LinearMap.BilinForm.congr e f, LinearMap.BilinForm.Nondegenerate.congr e hnd,
    fun k hk i j i' j' hki hkj => ?_⟩
  rw [LinearMap.BilinForm.congr_apply, LinearMap.BilinForm.congr_apply]
  refine hinv (restrictEquiv k I (hHI.conjSub_eq hk)) (restrictEquiv_mem_restrictRange hHI hk)
    (e.symm i) (e.symm j) (e.symm i') (e.symm j') ?_ ?_
  · exact Subtype.ext hki
  · exact Subtype.ext hkj

theorem autAll_of_restrictRange_top {H : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}
    (hHI : Invariant H I) (h : AutAll (restrictRange H I hHI) ⊤) : AutAll H I := by
  intro g
  let e : ↥(⊤ : Submodule (ZMod 2) ↥I) ≃ₗ[ZMod 2] ↥I := Submodule.topEquiv
  obtain ⟨k, hk, hkg⟩ := h (e.trans (g.trans e.symm))
  obtain ⟨h₀, hh₀, hkh⟩ := (mem_restrictRange_iff hHI).1 hk
  refine ⟨h₀, hh₀, fun i => ?_⟩
  have := hkg (e.symm i)
  rw [← hkh i]
  exact congrArg Subtype.val this

theorem concl8_of_alt [Finite V] {B : LinearMap.BilinForm (ZMod 2) V}
    {Γ H X : Subgroup (GLV V)} {I : Submodule (ZMod 2) V} {x : GLV V} {n : ℕ} (hn5 : 5 ≤ n)
    (hn6 : n ≠ 6) (hHΓ : H ≤ Γ) (hXΓ : X ≤ Γ) (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H)
    (hirr : IsIrr H I) (hxX : x ∈ X) (hcompl : IsCompl I (conjSub x I))
    (hne : conjSub x I ≠ I) (hn : ¬ HIso H I (conjSub x I)) (hiso : Isotropic B I)
    (hd4 : Module.finrank (ZMod 2) ↥I = 4) (hE : EndIsField (restrictRange H I hirr.1) 1)
    (e : ↥H ≃* ↥(alternatingGroup (Fin n))) :
    Module.finrank (ZMod 2) V = 8 ∧ Nonempty (↥Γ ≃* Equiv.Perm (Fin n)) ∧
      ∃ I' : Submodule (ZMod 2) V, Module.finrank (ZMod 2) ↥I' = 4 ∧
        (∀ w ∈ I', ∀ w' ∈ I', B w w' = 0) ∧
        (∀ γ ∈ (genFittingLayer ↥Γ).map Γ.subtype, ∀ v ∈ I', γ v ∈ I') ∧
        ∃ x ∈ X, (∃ v ∈ I', x v ∉ I') ∧ IsCompl I' (I'.map (x : V →ₗ[ZMod 2] V)) := by
  have hxΓ : x ∈ Γ := hXΓ hxX
  have hC : ∀ c ∈ Γ, (∀ h ∈ H, c * h = h * c) → c = 1 := fun c hcΓ hc =>
    eq_one_of_commute_of_endIsField hN hxΓ hirr hcompl hn hE hcΓ hc
  have hxH : x ∉ H := fun hxH => hne (hirr.1.conjSub_eq hxH)
  have hd8 : Module.finrank (ZMod 2) V = 8 := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [finrank_conjSub] at h1
    omega
  refine ⟨hd8, nonempty_mulEquiv_perm_of_alt hn5 hn6 hHΓ hN e hC ⟨x, hxΓ, hxH⟩, I, hd4, hiso,
    ?_, x, hxX, ?_, hcompl⟩
  · intro γ hγ v hv
    exact hirr.1 γ (layer_le_of_centralizer_eq_one hHΓ hN hC hγ) v hv
  · by_contra hcon
    push Not at hcon
    apply hne
    refine Submodule.eq_of_le_of_finrank_eq ?_ (finrank_conjSub x I)
    rintro _ ⟨v, hv, rfl⟩
    exact hcon v hv

end G11

end CFSG.Quasithin
