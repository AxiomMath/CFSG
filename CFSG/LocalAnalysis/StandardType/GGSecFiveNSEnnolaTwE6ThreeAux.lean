module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableBE6Three
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelIndep
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLFinite
import CFSG.LocalAnalysis.StandardType.GGE6DepZLWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three

@[expose] def ggNE3_s (i : Fin 6) (y : E6Dep.Vec6) : E6Dep.Vec6 := y - y i • E6Dep.cartanE6 i

theorem ggNE3_adRefl_eq (i : Fin 6) (y : E6Dep.Vec6) : adRefl .E6 3 i y = ggNE3_s i y :=
  E6Dep.ZL.adRefl_E6_eq i y

theorem ggNE3_cube_31 : ∀ y : E6Dep.Vec6, ((fun z => ggNE3_s 3 (ggNE3_s 1 z))^[3]) y = y := by
  decide +kernel

theorem ggNE3_cube_32 : ∀ y : E6Dep.Vec6, ((fun z => ggNE3_s 3 (ggNE3_s 2 z))^[3]) y = y := by
  decide +kernel

theorem ggNE3_cube_34 : ∀ y : E6Dep.Vec6, ((fun z => ggNE3_s 3 (ggNE3_s 4 z))^[3]) y = y := by
  decide +kernel

theorem ggNE3_sq_12 : ∀ y : E6Dep.Vec6, ((fun z => ggNE3_s 1 (ggNE3_s 2 z))^[2]) y = y := by
  decide +kernel

theorem ggNE3_sq_14 : ∀ y : E6Dep.Vec6, ((fun z => ggNE3_s 1 (ggNE3_s 4 z))^[2]) y = y := by
  decide +kernel

theorem ggNE3_sq_24 : ∀ y : E6Dep.Vec6, ((fun z => ggNE3_s 2 (ggNE3_s 4 z))^[2]) y = y := by
  decide +kernel

theorem ggNE3_move_31 :
    ∃ x : E6Dep.Vec6, dotProduct E6Dep.ZL.kappa x = 0 ∧ ggNE3_s 3 (ggNE3_s 1 x) ≠ x := by
  decide +kernel

theorem ggNE3_move_32 :
    ∃ x : E6Dep.Vec6, dotProduct E6Dep.ZL.kappa x = 0 ∧ ggNE3_s 3 (ggNE3_s 2 x) ≠ x := by
  decide +kernel

theorem ggNE3_move_34 :
    ∃ x : E6Dep.Vec6, dotProduct E6Dep.ZL.kappa x = 0 ∧ ggNE3_s 3 (ggNE3_s 4 x) ≠ x := by
  decide +kernel

theorem ggNE3_move_12 :
    ∃ x : E6Dep.Vec6, dotProduct E6Dep.ZL.kappa x = 0 ∧ ggNE3_s 1 (ggNE3_s 2 x) ≠ x := by
  decide +kernel

theorem ggNE3_move_14 :
    ∃ x : E6Dep.Vec6, dotProduct E6Dep.ZL.kappa x = 0 ∧ ggNE3_s 1 (ggNE3_s 4 x) ≠ x := by
  decide +kernel

theorem ggNE3_move_24 :
    ∃ x : E6Dep.Vec6, dotProduct E6Dep.ZL.kappa x = 0 ∧ ggNE3_s 2 (ggNE3_s 4 x) ≠ x := by
  decide +kernel

section Group

variable {L' : Type} [Group L'] [Finite L'] {Z : Subgroup L'} {A : Subgroup (MulAut L')}
  {Φ : A →* Multiplicative (Fin 6 → ZMod 3)} {T : Subgroup L'} {w : Fin 6 → L'}

theorem ggNE3_rho_toAdd (h : GGE6ThreeData Z A Φ T w) (i : Fin 6) (a : A) :
    Multiplicative.toAdd (Φ (h.conjAut i a)) = ggNE3_s i (Multiplicative.toAdd (Φ a)) :=
  (h.conjAut_apply_toAdd i a).trans (ggNE3_adRefl_eq i _)

theorem ggNE3_pair_iter (h : GGE6ThreeData Z A Φ T w) (i j : Fin 6) (n : ℕ) (a : A) :
    Multiplicative.toAdd (Φ (((h.conjAut i * h.conjAut j) ^ n) a)) =
      ((fun z => ggNE3_s i (ggNE3_s j z))^[n]) (Multiplicative.toAdd (Φ a)) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih, Function.iterate_succ_apply]
    exact congrArg (fun z => ((fun z => ggNE3_s i (ggNE3_s j z))^[n]) z)
      ((ggNE3_rho_toAdd h i _).trans (congrArg (ggNE3_s i) (ggNE3_rho_toAdd h j a)))

theorem ggNE3_pair_pow_eq_one (h : GGE6ThreeData Z A Φ T w) (i j : Fin 6) (n : ℕ)
    (hn : ∀ y : E6Dep.Vec6, ((fun z => ggNE3_s i (ggNE3_s j z))^[n]) y = y) :
    (h.conjAut i * h.conjAut j) ^ n = 1 := by
  refine MulEquiv.ext fun a => ?_
  apply h.injective
  apply Multiplicative.toAdd.injective
  rw [ggNE3_pair_iter, hn, MulAut.one_apply]

theorem ggNE3_pair_ne_one (h : GGE6ThreeData Z A Φ T w) (i j : Fin 6) (x : E6Dep.Vec6)
    (hx : dotProduct E6Dep.ZL.kappa x = 0) (hne : ggNE3_s i (ggNE3_s j x) ≠ x) :
    h.conjAut i * h.conjAut j ≠ 1 := by
  intro h1
  have hxr : Multiplicative.ofAdd x ∈ Φ.range := by
    rcases h.range with h0 | h0
    · rw [h0]; trivial
    · exact (h0 x).2 ((E6Dep.ZL.kDotP_eq_kappa_dotProduct x).trans hx)
  obtain ⟨a, ha⟩ := hxr
  have h2 : Multiplicative.toAdd (Φ a) = ggNE3_s i (ggNE3_s j (Multiplicative.toAdd (Φ a))) := by
    have := ggNE3_pair_iter h i j 1 a
    rw [pow_one, h1, MulAut.one_apply, Function.iterate_one] at this
    exact this
  rw [ha] at h2
  exact hne h2.symm

end Group

end CFSG.StandardType

end
