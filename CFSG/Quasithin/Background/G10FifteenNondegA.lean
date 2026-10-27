module

public import CFSG.Quasithin.Background.G10FifteenSplit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem isPerfect_normalClosure {Γ L : Subgroup (GLV V)} (hL : Group.IsPerfect ↥L) :
    Group.IsPerfect ↥(normalClosure Γ L) := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => ?_) ?_
  · rw [commutatorElement_def]
    exact (normalClosure Γ L).mul_mem ((normalClosure Γ L).mul_mem
      ((normalClosure Γ L).mul_mem h₁ h₂) ((normalClosure Γ L).inv_mem h₁))
      ((normalClosure Γ L).inv_mem h₂)
  · unfold normalClosure
    rw [Subgroup.closure_le]
    rintro _ ⟨γ, hγ, l, hl, rfl⟩
    have hLL : ⁅L, L⁆ = L := Subgroup.commutator_eq_self (H := L)
    have hl' : l ∈ ⁅L, L⁆ := by rw [hLL]; exact hl
    have h1 : γ * l * γ⁻¹ ∈ (⁅L, L⁆).map (MulAut.conj γ).toMonoidHom :=
      ⟨l, hl', by simp [MulAut.conj_apply]⟩
    rw [Subgroup.map_commutator] at h1
    have hconj : L.map (MulAut.conj γ).toMonoidHom ≤
        Subgroup.closure {x | ∃ γ ∈ Γ, ∃ l ∈ L, x = γ * l * γ⁻¹} := by
      rintro _ ⟨l', hl'', rfl⟩
      exact Subgroup.subset_closure ⟨γ, hγ, l', hl'', by simp [MulAut.conj_apply]⟩
    exact Subgroup.commutator_mono hconj hconj h1


namespace G108Hyp

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} (hyp : G108Hyp B Γ v₁ W X X₀ L)

include hyp

theorem conj_le_orthogonal (h10 : G1010Concl Γ v₁ X L) (h11 : G1011Concl Γ v₁ X L)
    (h12 : G1012Concl Γ v₁ W X L) {I : Submodule (ZMod 2) V}
    (hI : IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) (hnd : NondegOn B I) :
    conjSub x I ≤ B.orthogonal I := by
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  have hirr' : IsIrr (normalClosure Γ L) (conjSub x I) :=
    hirr.conj_of_normal (normalClosure_normal Γ L) (hyp.X_le hx)
  have hcompl : IsCompl I (B.orthogonal I) := hyp.isCompl_orthogonal hnd
  have hU : Invariant (normalClosure Γ L) (B.orthogonal I) :=
    hI.1.orthogonal hyp.H_isometry
  have hsplit := hyp.isCompl_sup_conj h10 h11 h12 hI hfix hx hne
  have hUle : B.orthogonal I ≤ I ⊔ conjSub x I := by
    rw [codisjoint_iff.1 hsplit.codisjoint]
    exact le_top
  have hU0 : B.orthogonal I ≠ ⊥ := by
    intro h
    have hItop : I = ⊤ := by
      have := hcompl.sup_eq_top
      rwa [h, sup_bot_eq] at this
    have hle : conjSub x I ≤ I := by rw [hItop]; exact le_top
    have hbot := hyp.conj_inf_eq_bot hI hx hne
    rw [inf_eq_left.2 hle] at hbot
    exact hirr'.ne_bot hbot
  rcases hyp.le_of_le_sup_conj hI hfix hx hne hU hUle hU0 with h | h
  · exfalso
    have hdis := hcompl.disjoint
    rw [disjoint_iff, inf_eq_left.2 h] at hdis
    exact hirr.ne_bot hdis
  · exact h

theorem not_le_perp_of_nondeg {I : Submodule (ZMod 2) V} {x : GLV V} {i : V} (hiI : i ∈ I)
    (hi0 : i ≠ 0) (hv : v₁ = i + x i) (hnd : NondegOn B I)
    (horth : conjSub x I ≤ B.orthogonal I) : ¬ I ≤ perp B v₁ := by
  intro hle
  have hrefl := hyp.toG101Hyp.isRefl
  apply hi0
  refine hnd i hiI fun u hu => ?_
  have h1 : B v₁ u = 0 := hle hu
  have h2 : B (x i) u = 0 := by
    have : x i ∈ B.orthogonal I := horth (apply_mem_conjSub hiI)
    exact hrefl _ _ ((LinearMap.BilinForm.mem_orthogonal_iff.1 this) u hu)
  rw [hv, map_add, LinearMap.add_apply, h2, add_zero] at h1
  exact h1

theorem finrank_inf_perp_add_one {I : Submodule (ZMod 2) V} (hnle : ¬ I ≤ perp B v₁) :
    Module.finrank (ZMod 2) ↥(I ⊓ perp B v₁) + 1 = Module.finrank (ZMod 2) I := by
  have h1 := finrank_le_finrank_inf_perp_add_one hyp.toG101Hyp.nondegenerate' hyp.point I
  have h2 : I ⊓ perp B v₁ < I := lt_of_le_of_ne inf_le_left fun h => hnle (h ▸ inf_le_right)
  have h3 := Submodule.finrank_lt_finrank_of_lt h2
  omega

end G108Hyp

end G11

end CFSG.Quasithin
