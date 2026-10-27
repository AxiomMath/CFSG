module

public import CFSG.Quasithin.H13.GoldschmidtU43EMat2
public import CFSG.Quasithin.H13.GoldschmidtU43ENorm1

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

abbrev Mat3 : Type := Matrix (Fin 4) (Fin 4) (ZMod 3)

@[expose] def Zmat : Mat3 := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]

@[expose] def Umat : Mat3 := !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]

@[expose] def Vmat : Mat3 := !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]

theorem evC_unit {C : Type} [CommGroup C] {x : Fin 4 → C} (c : Fin 4 → ZMod 3) (k : Fin 4)
    (h : c = Pi.single k 1) : evC x c = x k := by
  subst h
  exact evC_single k

theorem evC_unit_neg {C : Type} [CommGroup C] {x : Fin 4 → C} (hx : ∀ i, x i ^ 3 = 1)
    (c : Fin 4 → ZMod 3) (k : Fin 4) (h : c = -(Pi.single k 1 : Fin 4 → ZMod 3)) :
    evC x c = (x k)⁻¹ := by
  subst h
  have := evC_neg hx (Pi.single k 1 : Fin 4 → ZMod 3)
  rwa [evC_single] at this

namespace JWSetup

variable [Finite G] {z : G} {S : JWSetup z}

@[expose] def conjM (S : JWSetup z) (n : G) (hn : n ∈ S.Ng) : ↥S.Mg →* ↥S.Mg where
  toFun m := ⟨n * m * n⁻¹, (S.mem_Ng.mp hn m).mp m.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    show n * ((a : G) * b) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹)
    group)

omit [Finite G] in
theorem conj_eq_of_comm {a n : G} (h : a * n = n * a) : n * a * n⁻¹ = a := by
  rw [mul_inv_eq_iff_eq_mul]
  exact h.symm

omit [Finite G] in
theorem conj_z_sigG (S : JWSetup z) : z * S.sigG * z⁻¹ = S.sigG := conj_eq_of_comm S.sigG_comm_z

omit [Finite G] in
theorem conj_z_sigp (S : JWSetup z) : z * S.sigp * z⁻¹ = S.sigp :=
  conj_eq_of_comm (z_comm_H (S.σ₁ * S.σ₂⁻¹))

omit [Finite G] in
theorem conj_u_sigG (S : JWSetup z) : (S.u : G) * S.sigG * (S.u : G)⁻¹ = S.sigG :=
  conj_eq_of_comm S.sigG_comm_u

omit [Finite G] in
theorem conj_u_sigp (S : JWSetup z) : (S.u : G) * S.sigp * (S.u : G)⁻¹ = S.sigp⁻¹ := by
  have e1 : S.u * S.σ₁ * S.u⁻¹ = S.σ₂ := by
    rw [mul_inv_eq_iff_eq_mul]
    exact S.u_mul_σ₁
  have e2 : S.u * S.σ₂ * S.u⁻¹ = S.σ₁ := by
    rw [mul_inv_eq_iff_eq_mul]
    exact S.u_mul_σ₂
  have h : S.u * (S.σ₁ * S.σ₂⁻¹) * S.u⁻¹ = (S.σ₁ * S.σ₂⁻¹)⁻¹ := by
    calc S.u * (S.σ₁ * S.σ₂⁻¹) * S.u⁻¹ = (S.u * S.σ₁ * S.u⁻¹) * (S.u * S.σ₂ * S.u⁻¹)⁻¹ := by
          group
      _ = (S.σ₁ * S.σ₂⁻¹)⁻¹ := by rw [e1, e2]; group
  exact congrArg Subtype.val h

theorem conj_u_rho (S : JWSetup z) (r : S.Rho) : (S.u : G) * r.ρ * (S.u : G)⁻¹ = r.ρ :=
  conj_eq_of_comm (Subgroup.mem_centralizer_singleton_iff.mp r.mem.2)

theorem conj_u_rho2 (S : JWSetup z) (r : S.Rho) :
    (S.u : G) * S.rho2 r.ρ * (S.u : G)⁻¹ = (S.rho2 r.ρ)⁻¹ := by
  have h : S.rho2 r.ρ * (z * (S.u : G)) = (z * (S.u : G)) * S.rho2 r.ρ :=
    Subgroup.mem_centralizer_singleton_iff.mp (S.rho2_mem_T2 r.mem).2
  have h1 : (z * (S.u : G)) * S.rho2 r.ρ * (z * (S.u : G))⁻¹ = S.rho2 r.ρ := conj_eq_of_comm h
  have h2 : (S.u : G) * S.rho2 r.ρ * (S.u : G)⁻¹ =
      z⁻¹ * ((z * (S.u : G)) * S.rho2 r.ρ * (z * (S.u : G))⁻¹) * z := by group
  rw [h2, h1]
  have h3 := S.z_rho2 r.inv
  rw [← h3, S.z_inv]

theorem conj_v_of_mem_Tg (S : JWSetup z) {x : G} (hx : x ∈ S.Tg) :
    (S.v : G) * x * (S.v : G)⁻¹ = x⁻¹ := by
  have h := S.v_inv_Tg (S.Tg.inv_mem hx)
  rw [inv_inv] at h
  calc (S.v : G) * x * (S.v : G)⁻¹ = (S.v : G) * ((S.v : G)⁻¹ * x⁻¹ * S.v) * (S.v : G)⁻¹ := by
        rw [h]
    _ = x⁻¹ := by group

theorem conj_v_rho (S : JWSetup z) (r : S.Rho) :
    (S.v : G) * r.ρ * (S.v : G)⁻¹ = (S.rho2 r.ρ)⁻¹ := by
  have h := S.v_rho2 r.inv
  calc (S.v : G) * r.ρ * (S.v : G)⁻¹ = ((S.v : G) * r.ρ⁻¹ * (S.v : G)⁻¹)⁻¹ := by group
    _ = (S.rho2 r.ρ)⁻¹ := by
      congr 1
      calc (S.v : G) * r.ρ⁻¹ * (S.v : G)⁻¹
          = (S.v : G) * ((S.v : G)⁻¹ * S.rho2 r.ρ * S.v) * (S.v : G)⁻¹ := by rw [h]
        _ = S.rho2 r.ρ := by group

theorem conj_v_rho2 (S : JWSetup z) (r : S.Rho) : (S.v : G) * S.rho2 r.ρ * (S.v : G)⁻¹ = r.ρ := by
  unfold JWSetup.rho2
  group

theorem isRep_z (S : JWSetup z) (r : S.Rho) :
    IsRep (basis r) (S.conjM z S.z_mem_Ng) Zmat := by
  refine isRep_of_cols (fun _ => S.pow_three_M _) _ _ fun j => ?_
  fin_cases j
  · have h := evC_unit (x := basis r) (fun i => Zmat i 0) 0
      (by funext i; fin_cases i <;> simp [Zmat])
    show S.conjM z S.z_mem_Ng (basis r 0) = evC (basis r) (fun i => Zmat i 0)
    rw [h]
    exact Subtype.ext (S.conj_z_sigG)
  · have h := evC_unit (x := basis r) (fun i => Zmat i 1) 1
      (by funext i; fin_cases i <;> simp [Zmat])
    show S.conjM z S.z_mem_Ng (basis r 1) = evC (basis r) (fun i => Zmat i 1)
    rw [h]
    exact Subtype.ext (S.conj_z_sigp)
  · have h := evC_unit_neg (x := basis r) (fun _ => S.pow_three_M _)
      (fun i => Zmat i 2) 2 (by funext i; fin_cases i <;> simp [Zmat] <;> rfl)
    show S.conjM z S.z_mem_Ng (basis r 2) = evC (basis r) (fun i => Zmat i 2)
    rw [h]
    exact Subtype.ext (r.inv)
  · have h := evC_unit_neg (x := basis r) (fun _ => S.pow_three_M _)
      (fun i => Zmat i 3) 3 (by funext i; fin_cases i <;> simp [Zmat] <;> rfl)
    show S.conjM z S.z_mem_Ng (basis r 3) = evC (basis r) (fun i => Zmat i 3)
    rw [h]
    exact Subtype.ext (S.z_rho2 r.inv)

theorem isRep_u (S : JWSetup z) (r : S.Rho) :
    IsRep (basis r) (S.conjM (S.u : G) S.u_mem_Ng) Umat := by
  refine isRep_of_cols (fun _ => S.pow_three_M _) _ _ fun j => ?_
  fin_cases j
  · have h := evC_unit (x := basis r) (fun i => Umat i 0) 0
      (by funext i; fin_cases i <;> simp [Umat])
    show S.conjM (S.u : G) S.u_mem_Ng (basis r 0) = evC (basis r) (fun i => Umat i 0)
    rw [h]
    exact Subtype.ext (S.conj_u_sigG)
  · have h := evC_unit_neg (x := basis r) (fun _ => S.pow_three_M _)
      (fun i => Umat i 1) 1 (by funext i; fin_cases i <;> simp [Umat] <;> rfl)
    show S.conjM (S.u : G) S.u_mem_Ng (basis r 1) = evC (basis r) (fun i => Umat i 1)
    rw [h]
    exact Subtype.ext (S.conj_u_sigp)
  · have h := evC_unit (x := basis r) (fun i => Umat i 2) 2
      (by funext i; fin_cases i <;> simp [Umat])
    show S.conjM (S.u : G) S.u_mem_Ng (basis r 2) = evC (basis r) (fun i => Umat i 2)
    rw [h]
    exact Subtype.ext (S.conj_u_rho r)
  · have h := evC_unit_neg (x := basis r) (fun _ => S.pow_three_M _)
      (fun i => Umat i 3) 3 (by funext i; fin_cases i <;> simp [Umat] <;> rfl)
    show S.conjM (S.u : G) S.u_mem_Ng (basis r 3) = evC (basis r) (fun i => Umat i 3)
    rw [h]
    exact Subtype.ext (S.conj_u_rho2 r)

theorem isRep_v (S : JWSetup z) (r : S.Rho) :
    IsRep (basis r) (S.conjM (S.v : G) S.v_mem_Ng) Vmat := by
  refine isRep_of_cols (fun _ => S.pow_three_M _) _ _ fun j => ?_
  fin_cases j
  · have h := evC_unit_neg (x := basis r) (fun _ => S.pow_three_M _)
      (fun i => Vmat i 0) 0 (by funext i; fin_cases i <;> simp [Vmat] <;> rfl)
    show S.conjM (S.v : G) S.v_mem_Ng (basis r 0) = evC (basis r) (fun i => Vmat i 0)
    rw [h]
    exact Subtype.ext (S.conj_v_of_mem_Tg S.sigG_mem_Tg)
  · have h := evC_unit_neg (x := basis r) (fun _ => S.pow_three_M _)
      (fun i => Vmat i 1) 1 (by funext i; fin_cases i <;> simp [Vmat] <;> rfl)
    show S.conjM (S.v : G) S.v_mem_Ng (basis r 1) = evC (basis r) (fun i => Vmat i 1)
    rw [h]
    exact Subtype.ext (S.conj_v_of_mem_Tg S.sigp_mem_Tg)
  · have h := evC_unit_neg (x := basis r) (fun _ => S.pow_three_M _)
      (fun i => Vmat i 2) 3 (by funext i; fin_cases i <;> simp [Vmat] <;> rfl)
    show S.conjM (S.v : G) S.v_mem_Ng (basis r 2) = evC (basis r) (fun i => Vmat i 2)
    rw [h]
    exact Subtype.ext (S.conj_v_rho r)
  · have h := evC_unit (x := basis r) (fun i => Vmat i 3) 2
      (by funext i; fin_cases i <;> simp [Vmat])
    show S.conjM (S.v : G) S.v_mem_Ng (basis r 3) = evC (basis r) (fun i => Vmat i 3)
    rw [h]
    exact Subtype.ext (S.conj_v_rho2 r)

end JWSetup

end CFSG.Quasithin.H13.U43
