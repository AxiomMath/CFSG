module

public import CFSG.Quasithin.Background.SmithB45Alt7Ind
public import CFSG.Quasithin.Background.SmithB45HatA6Six

public section

namespace CFSG.Quasithin.B45Alt7

open Equiv Equiv.Perm CFSG.QuasithinUnique.Setup.X3E CFSG.QuasithinUnique.Setup.X3
  CFSG.QuasithinUnique.Setup.Offender

theorem regW_facts :
    ((eval7 (regW.getD 0 []) : A7) : Perm (Fin 7)) = swap 0 1 * swap 2 3 ∧
    ((eval7 (regW.getD 1 []) : A7) : Perm (Fin 7)) = swap 0 2 * swap 1 3 := by
  decide +kernel

theorem reg_facts :
    eval7 (regW.getD 0 []) * eval7 (regW.getD 0 []) = 1 ∧
    eval7 (regW.getD 1 []) * eval7 (regW.getD 1 []) = 1 ∧
    eval7 (regW.getD 0 []) * eval7 (regW.getD 1 []) =
      eval7 (regW.getD 1 []) * eval7 (regW.getD 0 []) ∧
    eval7 (regW.getD 0 []) ≠ 1 ∧ eval7 (regW.getD 1 []) ≠ 1 ∧
    eval7 (regW.getD 0 []) ≠ eval7 (regW.getD 1 []) := by
  refine ⟨Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [Subgroup.coe_mul, regW_facts.1]
    decide
  · rw [Subgroup.coe_mul, regW_facts.2]
    decide
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, regW_facts.1, regW_facts.2]
    decide
  · have := congrArg Subtype.val h
    rw [regW_facts.1] at this
    exact absurd this (by decide)
  · have := congrArg Subtype.val h
    rw [regW_facts.2] at this
    exact absurd this (by decide)
  · have := congrArg Subtype.val h
    rw [regW_facts.1, regW_facts.2] at this
    exact absurd this (by decide)

theorem getD_four_inj : ∀ k k' : Fin 4,
    [0, 5, 10, 15].getD k.val 0 = [0, 5, 10, 15].getD k'.val 0 → k = k' := by
  decide

section Four

variable {V : Type} [CommGroup V] [Module (ZMod 2) (Additive V)] [Finite V]
  {L : Subgroup (MulAut V)} (ι : ↥L ≃* A7)

omit [Finite V] in
theorem rho7_eval7 : ∀ (w : List Bool) (x : Additive V),
    rho7 ι (eval7 w) x = (wmap (fun b => ((rho7 ι (gen7 b) : Additive V ≃ₗ[ZMod 2] Additive V) :
      Additive V →ₗ[ZMod 2] Additive V)) w) x
  | [], x => by simp [eval7, wmap]
  | b :: w, x => by
    rw [eval7, map_mul, LinearEquiv.mul_apply, rho7_eval7 w x, wmap_cons]
    rfl

theorem exists_four_offender {i : ℕ} (hi : i < 2) (Ψ : Vec 4 ≃ₗ[ZMod 2] Additive V)
    (hΨ : ∀ b s, Ψ (lin 4 (indBlk true i b) s) = rho7 ι (gen7 b) (Ψ s)) :
    ∃ E : Subgroup (MulAut V), E ≤ L ∧ IsElemAbelian2 E ∧ Nat.card E = 4 ∧
      Nat.card V ≤ 4 * Nat.card (fixV E) := by
  classical
  obtain ⟨h1, h2, h12, h1n, h2n, hne⟩ := reg_facts
  set e1 : A7 := eval7 (regW.getD 0 []) with he1
  set e2 : A7 := eval7 (regW.getD 1 []) with he2
  set u1 : MulAut V := (ι.symm e1 : MulAut V) with hu1
  set u2 : MulAut V := (ι.symm e2 : MulAut V) with hu2
  have hu11 : u1 * u1 = 1 := by
    rw [hu1, ← Subgroup.coe_mul, ← map_mul, h1, map_one]
    rfl
  have hu22 : u2 * u2 = 1 := by
    rw [hu2, ← Subgroup.coe_mul, ← map_mul, h2, map_one]
    rfl
  have hu12 : u1 * u2 = u2 * u1 := by
    rw [hu1, hu2, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, h12]
  have hinj : ∀ x y : A7, (ι.symm x : MulAut V) = (ι.symm y : MulAut V) → x = y :=
    fun x y h => ι.symm.injective (Subtype.ext h)
  have hu1n : u1 ≠ 1 := fun h => h1n (hinj _ _ (h.trans (by rw [map_one]; rfl)))
  have hu2n : u2 ≠ 1 := fun h => h2n (hinj _ _ (h.trans (by rw [map_one]; rfl)))
  have hu12n : u1 ≠ u2 := fun h => hne (hinj _ _ h)
  set E : Subgroup (MulAut V) := Subgroup.closure {u1, u2} with hE
  have hEL : E ≤ L := by
    rw [hE, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact (ι.symm e1).2
    · exact (ι.symm e2).2
  refine ⟨E, hEL, B45HatA6.isElemAbelian2_closure_pair hu11 hu22 hu12,
    B45HatA6.card_closure_pair_eq_four hu11 hu22 hu12 hu1n hu2n hu12n, ?_⟩
  have hreg : ∀ v ∈ [5, 10, 15], ∀ j < 2,
      wapp 4 (indBlk true i) (regW.getD j []) v = v := by
    have h := regOK_true
    unfold regOK at h
    simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    intro v hv j hj
    have hi' : i ∈ [0, 1] := by
      interval_cases i <;> simp
    have := h i hi' v hv
    interval_cases j
    · exact this.1
    · exact this.2
  have hfixW : ∀ v ∈ [5, 10, 15], ∀ j < 2,
      rho7 ι (eval7 (regW.getD j [])) (Ψ (toVec 4 v)) = Ψ (toVec 4 v) := by
    intro v hv j hj
    have hw := wmap_intertwine (fun b => lin 4 (indBlk true i b))
      (fun b => ((rho7 ι (gen7 b) : Additive V ≃ₗ[ZMod 2] Additive V) :
        Additive V →ₗ[ZMod 2] Additive V)) Ψ.toLinearMap (fun b s => hΨ b s)
      (regW.getD j []) (toVec 4 v)
    simp only [LinearEquiv.coe_coe] at hw
    rw [rho7_eval7, ← hw, ← toVec_wapp, hreg v hv j hj]
  have hmem : ∀ v ∈ [0, 5, 10, 15], Additive.toMul (Ψ (toVec 4 v)) ∈ fixV E := by
    intro v hv
    have hgen : ∀ j < 2, (ι.symm (eval7 (regW.getD j [])) : MulAut V)
        (Additive.toMul (Ψ (toVec 4 v))) = Additive.toMul (Ψ (toVec 4 v)) := by
      intro j hj
      rcases List.mem_cons.1 hv with rfl | hv'
      · rw [toVec_zero, map_zero]
        exact map_one _
      · have := hfixW v hv' j hj
        rw [rho7_apply] at this
        exact congrArg Additive.toMul this
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · exact hgen 0 (by norm_num)
      · exact hgen 1 (by norm_num)
    | one => rfl
    | mul p q _ _ hp hq => rw [MulAut.mul_apply, hq, hp]
    | inv p _ hp =>
      calc p⁻¹ (Additive.toMul (Ψ (toVec 4 v))) =
          p⁻¹ (p (Additive.toMul (Ψ (toVec 4 v)))) := by rw [hp]
        _ = Additive.toMul (Ψ (toVec 4 v)) := by simp
  let F : Fin 4 → ↥(fixV E) := fun k =>
    ⟨Additive.toMul (Ψ (toVec 4 ([0, 5, 10, 15].getD k.val 0))), hmem _ (by
      fin_cases k <;> simp)⟩
  have hF : Function.Injective F := by
    intro k k' h
    have h1 : Ψ (toVec 4 ([0, 5, 10, 15].getD k.val 0)) =
        Ψ (toVec 4 ([0, 5, 10, 15].getD k'.val 0)) := congrArg Subtype.val h
    have h2 := Ψ.injective h1
    have hlt : ∀ k : Fin 4, [0, 5, 10, 15].getD k.val 0 < 2 ^ 4 := by decide
    exact getD_four_inj k k' (toVec_injOn (hlt k) (hlt k') h2)
  have h4 : 4 ≤ Nat.card (fixV E) := by
    have := Nat.card_le_card_of_injective F hF
    simpa using this
  have hV : Nat.card V = 16 := by
    rw [card_eq_of_equiv Ψ]
    norm_num
  omega

end Four

end CFSG.Quasithin.B45Alt7
