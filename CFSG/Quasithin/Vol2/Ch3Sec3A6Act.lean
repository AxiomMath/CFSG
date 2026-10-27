module

public import CFSG.Quasithin.Vol2.Ch3Sec3A6Inputs

public section

namespace CFSG.Quasithin.H13.A6Coc

theorem crd_add (x y : Fin 6 → ZMod 2) : crd (x + y) = crd x + crd y := Matrix.mulVec_add _ _ _

theorem sec_add (u v : Vec4) : sec (u + v) = sec u + sec v := Matrix.mulVec_add _ _ _

theorem crd_zero : crd 0 = 0 := Matrix.mulVec_zero _

theorem sec_zero : sec 0 = 0 := Matrix.mulVec_zero _

theorem crd_const : ∀ c : ZMod 2, crd (fun _ => c) = 0 := by decide

theorem crd_sec : ∀ v : Vec4, crd (sec v) = v := by decide +kernel

theorem sum_sec_aux :
    ∀ v : Vec4, sec v 0 + sec v 1 + sec v 2 + sec v 3 + sec v 4 + sec v 5 = 0 := by
  decide +kernel

theorem sum_sec (v : Vec4) : ∑ i, sec v i = 0 := by
  rw [Fin.sum_univ_six]
  exact sum_sec_aux v

theorem sec_crd_aux : ∀ x : Fin 6 → ZMod 2, x 0 + x 1 + x 2 + x 3 + x 4 + x 5 = 0 →
    sec (crd x) = x ∨ sec (crd x) = x + fun _ => 1 := by
  decide +kernel

theorem sec_crd (x : Fin 6 → ZMod 2) (hx : ∑ i, x i = 0) :
    ∃ c : ZMod 2, ∀ i, sec (crd x) i = x i + c := by
  rw [Fin.sum_univ_six] at hx
  rcases sec_crd_aux x hx with h | h
  · exact ⟨0, fun i => by rw [h, add_zero]⟩
  · exact ⟨1, fun i => by rw [h]; rfl⟩

theorem act_crd (σ : Equiv.Perm (Fin 6)) (x : Fin 6 → ZMod 2) (hx : ∑ i, x i = 0) :
    act σ (crd x) = crd fun i => x (σ⁻¹ i) := by
  obtain ⟨c, hc⟩ := sec_crd x hx
  have e : (fun i => sec (crd x) (σ⁻¹ i)) = (fun i => x (σ⁻¹ i)) + fun _ => c := by
    funext i
    rw [hc]
    rfl
  show crd (fun i => sec (crd x) (σ⁻¹ i)) = _
  rw [e, crd_add, crd_const, add_zero]

theorem act_mul (σ τ : Equiv.Perm (Fin 6)) (v : Vec4) : act (σ * τ) v = act σ (act τ v) := by
  have hs : ∑ i, sec v (τ⁻¹ i) = 0 := by
    rw [Equiv.sum_comp τ⁻¹ (sec v)]
    exact sum_sec v
  show crd (fun i => sec v ((σ * τ)⁻¹ i)) = act σ (crd fun i => sec v (τ⁻¹ i))
  rw [act_crd σ _ hs, mul_inv_rev]
  rfl

theorem act_one (v : Vec4) : act 1 v = v := by
  show crd (fun i => sec v ((1 : Equiv.Perm (Fin 6))⁻¹ i)) = v
  rw [inv_one]
  exact crd_sec v

theorem act_add (σ : Equiv.Perm (Fin 6)) (u v : Vec4) : act σ (u + v) = act σ u + act σ v := by
  show crd (fun i => sec (u + v) (σ⁻¹ i)) =
    crd (fun i => sec u (σ⁻¹ i)) + crd (fun i => sec v (σ⁻¹ i))
  rw [← crd_add, sec_add]
  rfl

theorem act_zero (σ : Equiv.Perm (Fin 6)) : act σ 0 = 0 := by
  show crd (fun i => sec 0 (σ⁻¹ i)) = 0
  rw [sec_zero]
  exact crd_zero

@[expose] def actHom (σ : Equiv.Perm (Fin 6)) : Vec4 →+ Vec4 where
  toFun := act σ
  map_zero' := act_zero σ
  map_add' := act_add σ

theorem act_neg (σ : Equiv.Perm (Fin 6)) (v : Vec4) : act σ (-v) = -act σ v :=
  map_neg (actHom σ) v

theorem act_sub (σ : Equiv.Perm (Fin 6)) (u v : Vec4) : act σ (u - v) = act σ u - act σ v :=
  map_sub (actHom σ) u v

end CFSG.Quasithin.H13.A6Coc
