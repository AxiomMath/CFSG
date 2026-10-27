module

public import CFSG.LocalAnalysis.StandardType.GGNineDepCtx
public import CFSG.LocalAnalysis.StandardType.GGNineDepRestrictAux
public import CFSG.LocalAnalysis.StandardType.GGCartanALinear

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {h : Fin (9 - 1) → V} {α : Fin (9 - 1) → Module.Dual (ZMod 3) V}
    {r : Fin (9 - 1) → (V ≃ₗ[ZMod 3] V)} {T : Type} {s : T → (V ≃ₗ[ZMod 3] V)} {x : V}

@[expose] def ggNineSeven (i : Fin 7) : Fin (9 - 1) := ⟨i, by omega⟩

theorem ggNineDep_pair_seven (C : GGNineDepCase 3 9 h α r s x) (i j : Fin 7) :
    α (ggNineSeven i) (h (ggNineSeven j)) = (CartanMatrix.A 7 i j : ZMod 3) := by
  have hA : ∀ i j : Fin 7,
      CartanMatrix.A (9 - 1) (ggNineSeven i) (ggNineSeven j) = CartanMatrix.A 7 i j := by
    intro i j
    simp only [CartanMatrix.A, Matrix.of_apply, ggNineSeven, Fin.ext_iff]
  rw [C.lin.pair, hA]

theorem ggNineDep_linearIndependent_seven (C : GGNineDepCase 3 9 h α r s x) :
    LinearIndependent (ZMod 3) (fun j : Fin 7 => h (ggNineSeven j)) :=
  cartanA_linearIndependent (by decide) (ggNineDep_pair_seven C)

theorem ggNineDep_eq_zero_of_mem_fix (C : GGNineDepCase 3 9 h α r s x) {v : V}
    (hv : v ∈ Submodule.span (ZMod 3) (Set.range fun j : Fin 7 => h (ggNineSeven j)))
    (hfix : v ∈ ggLinFix (Set.range r)) : v = 0 := by
  refine cartanA_eq_zero_of_mem_span (by decide) (ggNineDep_pair_seven C) hv fun i => ?_
  have h1 : r (ggNineSeven i) v = v := hfix _ ⟨_, rfl⟩
  rw [C.lin.refl_form] at h1
  have h2 : α (ggNineSeven i) v • h (ggNineSeven i) = 0 := by
    have := congrArg (fun w => v - w) h1
    simpa using this
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact h3
  · have h4 := l04nD2_pair_diag C (ggNineSeven i)
    rw [h3, map_zero] at h4
    exact absurd h4.symm (by decide)

theorem ggNineDep_finrank_eq_nine (C : GGNineDepCase 3 9 h α r s x) :
    Module.finrank (ZMod 3) V = 9 := by
  haveI : Module.Finite (ZMod 3) V := l04nD2_finite C
  have h2 := C.two
  have h9 := C.lin.dim_le
  set S := Submodule.span (ZMod 3) (Set.range fun j : Fin 7 => h (ggNineSeven j))
  set F := ggLinFix (Set.range r)
  have hS : Module.finrank (ZMod 3) S = 7 := by
    rw [finrank_span_eq_card (ggNineDep_linearIndependent_seven C), Fintype.card_fin]
  have hinf : S ⊓ F = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    exact (Submodule.mem_bot _).mpr (ggNineDep_eq_zero_of_mem_fix C hv.1 hv.2)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq S F
  rw [hinf, finrank_bot, add_zero, hS] at hsum
  have hle := Submodule.finrank_le (S ⊔ F)
  omega

theorem ggLargeRho_apply_coe {p N : ℕ} [Fact p.Prime] {W : Type} [AddCommGroup W]
    [Module (ZMod p) W] {ι : Type} {r : Fin (N - 1) → (W ≃ₗ[ZMod p] W)} {s : ι → (W ≃ₗ[ZMod p] W)}
    (hA : ggLargeGrp r s ≤ ggLinStab (ggFixLineT r s)) (a : ↥(ggLargeGrp r s))
    (v : ↥(ggFixLineT r s)) :
    ((ggLargeRho r s hA a v : ↥(ggFixLineT r s)) : W) = (a : W ≃ₗ[ZMod p] W) (v : W) :=
  l04nD2_restrict_apply _ _ v

theorem ggNineDep_finrank_eq_nine_of_neg_mem (X : GGNineDepCtx h α r s x)
    {z : ↥(ggFixLineT r s) ≃ₗ[ZMod 3] ↥(ggFixLineT r s)} (hz : z ∈ ggNineQ X)
    (hneg : ∀ v, z v = -v) : Module.finrank (ZMod 3) ↥(ggFixLineT r s) = 9 := by
  set ρ := ggLargeRho r s X.hA
  have hinj : Function.Injective ρ := X.restr.1
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hz
  have haT : ∀ v ∈ ggFixLineT r s, (a : V ≃ₗ[ZMod 3] V) v = -v := by
    intro v hv
    have h1 := ggLargeRho_apply_coe X.hA a ⟨v, hv⟩
    rw [show ρ a = z from ha, hneg] at h1
    rw [← h1]
    rfl
  have hcomm : ∀ b : ↥(ggLargeGrp r s), b * a = a * b := by
    intro b
    apply hinj
    rw [map_mul, map_mul, show ρ a = z from ha]
    ext v
    simp [LinearEquiv.mul_apply, hneg]
  have hsq : a * a = 1 := by
    apply hinj
    rw [map_mul, map_one, show ρ a = z from ha]
    ext v
    simp [LinearEquiv.mul_apply, hneg]
  have hsq' : ∀ v, (a : V ≃ₗ[ZMod 3] V) ((a : V ≃ₗ[ZMod 3] V) v) = v := by
    intro v
    have h1 := congrArg (fun c : ↥(ggLargeGrp r s) => (c : V ≃ₗ[ZMod 3] V) v) hsq
    simpa [LinearEquiv.mul_apply] using h1
  have hfixA : ∀ v, ∀ g ∈ ggLargeGrp r s,
      g ((a : V ≃ₗ[ZMod 3] V) v + v) = (a : V ≃ₗ[ZMod 3] V) v + v := by
    intro v g hg
    set w := (a : V ≃ₗ[ZMod 3] V) v + v with hw
    have haw : (a : V ≃ₗ[ZMod 3] V) w = w := by
      rw [hw, map_add, hsq', add_comm]
    have hu : g w - w ∈ ggFixLineT r s := l04nD2_disp X.case g hg w
    have hag : (a : V ≃ₗ[ZMod 3] V) (g w) = g ((a : V ≃ₗ[ZMod 3] V) w) := by
      have h1 := congrArg (fun c : ↥(ggLargeGrp r s) => (c : V ≃ₗ[ZMod 3] V) w)
        (hcomm ⟨g, hg⟩)
      simpa [LinearEquiv.mul_apply] using h1.symm
    have h1 : (a : V ≃ₗ[ZMod 3] V) (g w - w) = g w - w := by
      rw [map_sub, hag, haw]
    have h2 := haT _ hu
    rw [h1] at h2
    have h3 : (2 : ZMod 3) • (g w - w) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [h2]
      exact neg_add_cancel _
    have h4 : g w - w = 0 := by
      have h5 := congrArg (fun u => (2 : ZMod 3) • u) h3
      simp only [smul_zero, smul_smul] at h5
      rw [show (2 : ZMod 3) * 2 = 1 from rfl, one_smul] at h5
      exact h5
    exact sub_eq_zero.mp h4
  have hzero : ∀ v, (a : V ≃ₗ[ZMod 3] V) v + v = 0 := by
    intro v
    set w := (a : V ≃ₗ[ZMod 3] V) v + v
    have hwr : w ∈ ggLinFix (Set.range r) := by
      rintro _ ⟨i, rfl⟩
      exact hfixA v _ (Subgroup.subset_closure (Or.inl ⟨i, rfl⟩))
    have hws : w ∈ ggLinFix (Set.range s) := by
      rintro _ ⟨k, rfl⟩
      exact hfixA v _ (Subgroup.subset_closure (Or.inr ⟨k, rfl⟩))
    rw [X.case.lin.fix_s] at hws
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hws
    by_cases hc0 : c = 0
    · rw [← hc, hc0, zero_smul]
    · exfalso
      apply X.case.lin.x_not_fix
      have hx : x = c⁻¹ • w := by
        rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [hx]
      exact (ggLinFix (Set.range r)).smul_mem _ hwr
  have htop : ggFixLineT r s = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have h1 : (a : V ≃ₗ[ZMod 3] V) v - v = v := by
      have h2 := hzero v
      have h3 : (a : V ≃ₗ[ZMod 3] V) v = -v := eq_neg_of_add_eq_zero_left h2
      rw [h3]
      have h4 : (3 : ZMod 3) • v = 0 := by
        rw [show (3 : ZMod 3) = 0 from rfl, zero_smul]
      have h5 : (3 : ZMod 3) • v = v + v + v := by
        rw [show (3 : ZMod 3) = 1 + 1 + 1 from rfl, add_smul, add_smul, one_smul]
      rw [h5] at h4
      calc -v - v = -v - v + (v + v + v) := by rw [h4, add_zero]
        _ = v := by abel
    rw [← h1]
    exact l04nD2_disp X.case _ a.2 v
  rw [htop, finrank_top]
  exact ggNineDep_finrank_eq_nine X.case

theorem ggNineDep_false_of_neg_mem (X : GGNineDepCtx h α r s x)
    (hd : Module.finrank (ZMod 3) ↥(ggFixLineT r s) ≤ 8)
    {z : ↥(ggFixLineT r s) ≃ₗ[ZMod 3] ↥(ggFixLineT r s)} (hz : z ∈ ggNineQ X)
    (hneg : ∀ v, z v = -v) : False := by
  have := ggNineDep_finrank_eq_nine_of_neg_mem X hz hneg
  omega

end CFSG.StandardType

end
