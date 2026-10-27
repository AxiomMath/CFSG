module

public import CFSG.Quasithin.H13.GoldschmidtU43EV1
public import CFSG.Quasithin.H13.GoldschmidtU43ENorm1

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

theorem u43_comm_of_cube {a s x : G} (ha4 : a * a * a * a = 1)
    (hcube : a * s * (a * s) * (a * s) = 1) (hx : s * x = x * s)
    (hy : s * (a * x * a⁻¹) = (a * x * a⁻¹) * s)
    (hxx : s * (a * a * x * a⁻¹ * a⁻¹) = (a * a * x * a⁻¹ * a⁻¹) * s) : a * x = x * a := by
  have e1 : (a * s) * x * (a * s)⁻¹ = a * x * a⁻¹ := by
    calc (a * s) * x * (a * s)⁻¹ = a * (s * x) * s⁻¹ * a⁻¹ := by group
      _ = a * (x * s) * s⁻¹ * a⁻¹ := by rw [hx]
      _ = a * x * a⁻¹ := by group
  have e2 : (a * s) * (a * x * a⁻¹) * (a * s)⁻¹ = a * a * x * a⁻¹ * a⁻¹ := by
    calc (a * s) * (a * x * a⁻¹) * (a * s)⁻¹ = a * (s * (a * x * a⁻¹)) * s⁻¹ * a⁻¹ := by group
      _ = a * ((a * x * a⁻¹) * s) * s⁻¹ * a⁻¹ := by rw [hy]
      _ = a * a * x * a⁻¹ * a⁻¹ := by group
  have e3 : (a * s) * (a * a * x * a⁻¹ * a⁻¹) * (a * s)⁻¹ = a * a * a * x * a⁻¹ * a⁻¹ * a⁻¹ := by
    calc (a * s) * (a * a * x * a⁻¹ * a⁻¹) * (a * s)⁻¹
        = a * (s * (a * a * x * a⁻¹ * a⁻¹)) * s⁻¹ * a⁻¹ := by group
      _ = a * ((a * a * x * a⁻¹ * a⁻¹) * s) * s⁻¹ * a⁻¹ := by rw [hxx]
      _ = a * a * a * x * a⁻¹ * a⁻¹ * a⁻¹ := by group
  have e4 : x = a * a * a * x * a⁻¹ * a⁻¹ * a⁻¹ := by
    calc x = (a * s * (a * s) * (a * s)) * x * (a * s * (a * s) * (a * s))⁻¹ := by
          rw [hcube]; group
      _ = (a * s) * ((a * s) * ((a * s) * x * (a * s)⁻¹) * (a * s)⁻¹) * (a * s)⁻¹ := by group
      _ = a * a * a * x * a⁻¹ * a⁻¹ * a⁻¹ := by rw [e1, e2, e3]
  have ha3 : a * a * a = a⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    exact ha4
  have ha3' : a⁻¹ * a⁻¹ * a⁻¹ = a := by
    calc a⁻¹ * a⁻¹ * a⁻¹ = (a * a * a)⁻¹ := by group
      _ = a := by rw [ha3, inv_inv]
  rw [ha3] at e4
  calc a * x = a * (a⁻¹ * x * a⁻¹ * a⁻¹ * a⁻¹) := by rw [← e4]
    _ = x * (a⁻¹ * a⁻¹ * a⁻¹) := by group
    _ = x * a := by rw [ha3']

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z) (r : S.Rho)

noncomputable abbrev a₂G : G := ((S.a₂ : ↥(Hz z)) : G)

@[expose] noncomputable def Ag : Subgroup G :=
  Subgroup.closure ({(S.σ₁ : G), r.ρ, S.rho2 r.ρ} : Set G)

@[expose] noncomputable def Bg : Subgroup G :=
  (S.Ag r).map (MulAut.conj (S.a₂G)⁻¹).toMonoidHom

theorem mem_Bg {x : G} : x ∈ S.Bg r ↔ S.a₂G * x * S.a₂G⁻¹ ∈ S.Ag r := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    show S.a₂G * ((S.a₂G)⁻¹ * y * (S.a₂G)⁻¹⁻¹) * S.a₂G⁻¹ ∈ S.Ag r
    have e : S.a₂G * ((S.a₂G)⁻¹ * y * (S.a₂G)⁻¹⁻¹) * S.a₂G⁻¹ = y := by group
    rw [e]
    exact hy
  · intro h
    refine ⟨S.a₂G * x * S.a₂G⁻¹, h, ?_⟩
    show (S.a₂G)⁻¹ * (S.a₂G * x * S.a₂G⁻¹) * (S.a₂G)⁻¹⁻¹ = x
    group

theorem Ag_le_Mg : S.Ag r ≤ S.Mg := by
  rw [Ag, Subgroup.closure_le]
  rintro x (rfl | rfl | rfl)
  · exact S.Tg_le_Mg S.σ₁G_mem_Tg
  · exact r.mem_Mg
  · exact S.rho2_mem_Mg r.mem_Mg

theorem σ₁_mem_Ag : (S.σ₁ : G) ∈ S.Ag r := Subgroup.subset_closure (by simp)

theorem Ag_le_Vg (hAU : (S.A : G) ∈ Uz z) : S.Ag r ≤ S.Vg := by
  rw [Ag, Subgroup.closure_le]
  rintro x (rfl | rfl | rfl)
  · exact S.σ₁_mem_Vg
  · exact S.rho_mem_Vg hAU r
  · exact S.rho2_mem_Vg hAU r

omit [Finite G] in
theorem a₂G_mem_Cg1 : S.a₂G ∈ S.Cg1 := S.a₂_mem_Cg1

theorem Bg_le_Vg (hAU : (S.A : G) ∈ Uz z) : S.Bg r ≤ S.Vg := by
  rintro _ ⟨y, hy, rfl⟩
  exact S.conj_mem_Vg (inv_mem S.a₂G_mem_Cg1) (S.Ag_le_Vg r hAU hy)

theorem σ₁_mem_Bg : (S.σ₁ : G) ∈ S.Bg r := by
  refine (S.mem_Bg r).mpr ?_
  have h : S.a₂G * (S.σ₁ : G) = (S.σ₁ : G) * S.a₂G := congrArg Subtype.val S.a₂_comm_σ₁
  have : S.a₂G * (S.σ₁ : G) * S.a₂G⁻¹ = (S.σ₁ : G) := by
    rw [mul_inv_eq_iff_eq_mul]
    exact h
  rw [this]
  exact S.σ₁_mem_Ag r

theorem isPGroup_Ag : IsPGroup 3 (S.Ag r) :=
  IsPGroup.to_le (IsPGroup.of_card (n := 4) (by rw [S.card_Mg_eq_81]; norm_num))
    (S.Ag_le_Mg r)

theorem isPGroup_Bg : IsPGroup 3 (S.Bg r) := (S.isPGroup_Ag r).map _

theorem card_Bg : Nat.card (S.Bg r) = Nat.card (S.Ag r) :=
  Subgroup.card_map_of_injective (MulAut.conj (S.a₂G)⁻¹).injective

theorem Ag_inf_Bg (hAU : (S.A : G) ∈ Uz z) {x : G} (hxA : x ∈ S.Ag r) (hxB : x ∈ S.Bg r) :
    x ∈ Subgroup.zpowers (S.σ₁ : G) := by
  have hxM : x ∈ S.Mg := S.Ag_le_Mg r hxA
  have hyA : S.a₂G * x * S.a₂G⁻¹ ∈ S.Ag r := (S.mem_Bg r).mp hxB
  have hyM : S.a₂G * x * S.a₂G⁻¹ ∈ S.Mg := S.Ag_le_Mg r hyA
  have haa : S.a₂G * S.a₂G = z := congrArg Subtype.val S.a₂_sq
  have hzx : z * x * z⁻¹ ∈ S.Mg := (S.mem_Ng.mp S.z_mem_Ng x).mp hxM
  have hxxM : S.a₂G * S.a₂G * x * S.a₂G⁻¹ * S.a₂G⁻¹ ∈ S.Mg := by
    have e : S.a₂G * S.a₂G * x * S.a₂G⁻¹ * S.a₂G⁻¹ =
        (S.a₂G * S.a₂G) * x * (S.a₂G * S.a₂G)⁻¹ := by group
    rw [e, haa]
    exact hzx
  have hσ₂M : (S.σ₂ : G) ∈ S.Mg := S.Tg_le_Mg S.σ₂G_mem_Tg
  have ha4 : S.a₂G * S.a₂G * S.a₂G * S.a₂G = 1 := by
    calc S.a₂G * S.a₂G * S.a₂G * S.a₂G = (S.a₂G * S.a₂G) * (S.a₂G * S.a₂G) := by group
      _ = 1 := by rw [haa, S.z_sq]
  have hcube : S.a₂G * (S.σ₂ : G) * (S.a₂G * (S.σ₂ : G)) * (S.a₂G * (S.σ₂ : G)) = 1 :=
    congrArg Subtype.val S.a₂σ₂_cube
  have hcomm := u43_comm_of_cube ha4 hcube (S.abelian_Mg _ hσ₂M _ hxM)
    (S.abelian_Mg _ hσ₂M _ hyM) (S.abelian_Mg _ hσ₂M _ hxxM)
  have hxH : x ∈ Hz z := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : z * x = x * z := by
      calc z * x = S.a₂G * S.a₂G * x := by rw [haa]
        _ = S.a₂G * (S.a₂G * x) := by group
        _ = S.a₂G * (x * S.a₂G) := by rw [hcomm]
        _ = (S.a₂G * x) * S.a₂G := by group
        _ = (x * S.a₂G) * S.a₂G := by rw [hcomm]
        _ = x * (S.a₂G * S.a₂G) := by group
        _ = x * z := by rw [haa]
    exact this.symm
  exact S.Vg_inf_Hz hAU (S.Ag_le_Vg r hAU hxA) hxH

omit [Finite G] in
theorem sigG_mul_sigp (S : JWSetup z) : S.sigG * S.sigp = (S.σ₁ : G) * (S.σ₁ : G) := by
  have hc : (S.σ₂ : G) * (S.σ₁ : G) = (S.σ₁ : G) * (S.σ₂ : G) := by
    have := congrArg Subtype.val S.σ₁σ₂_comm
    exact this.symm
  rw [sigG_eq, sigp_eq]
  calc (S.σ₁ : G) * S.σ₂ * ((S.σ₁ : G) * (S.σ₂ : G)⁻¹)
      = S.σ₁ * ((S.σ₂ : G) * S.σ₁) * (S.σ₂ : G)⁻¹ := by group
    _ = S.σ₁ * ((S.σ₁ : G) * S.σ₂) * (S.σ₂ : G)⁻¹ := by rw [hc]
    _ = (S.σ₁ : G) * S.σ₁ := by group

@[expose] def vec3 (i j k : ZMod 3) : Fin 4 → ZMod 3 := ![2 * i, 2 * i, j, k]

theorem evC_vec3_mem_Ag (i j k : ZMod 3) :
    ((evC (basis r) (vec3 i j k) : ↥S.Mg) : G) ∈ S.Ag r := by
  have h : evC (basis r) (vec3 i j k) = basis r 0 ^ (2 * i).val * basis r 1 ^ (2 * i).val *
      basis r 2 ^ j.val * basis r 3 ^ k.val := by
    simp [evC, Fin.prod_univ_four, vec3]
  rw [h]
  have hcomm : Commute S.sigG S.sigp := S.abelian_Mg _ (S.Tg_le_Mg S.sigG_mem_Tg) _
    (S.Tg_le_Mg S.sigp_mem_Tg)
  have hAσ : (S.σ₁ : G) * S.σ₁ ∈ S.Ag r := (S.Ag r).mul_mem (S.σ₁_mem_Ag r) (S.σ₁_mem_Ag r)
  have h0 : ((basis r 0 : ↥S.Mg) : G) = S.sigG := rfl
  have h1 : ((basis r 1 : ↥S.Mg) : G) = S.sigp := rfl
  have h2 : ((basis r 2 : ↥S.Mg) : G) = r.ρ := rfl
  have h3 : ((basis r 3 : ↥S.Mg) : G) = S.rho2 r.ρ := rfl
  have e : ((basis r 0 ^ (2 * i).val * basis r 1 ^ (2 * i).val * basis r 2 ^ j.val *
      basis r 3 ^ k.val : ↥S.Mg) : G) =
      ((S.σ₁ : G) * S.σ₁) ^ (2 * i).val * r.ρ ^ j.val * S.rho2 r.ρ ^ k.val := by
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, h0, h1, h2, h3]
    rw [← hcomm.mul_pow, S.sigG_mul_sigp]
  rw [e]
  refine (S.Ag r).mul_mem ((S.Ag r).mul_mem (pow_mem hAσ _) (pow_mem ?_ _)) (pow_mem ?_ _)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

theorem card_Ag_ge : 27 ≤ Nat.card (S.Ag r) := by
  have hinj : Function.Injective (fun t : ZMod 3 × ZMod 3 × ZMod 3 =>
      (⟨((evC (basis r) (vec3 t.1 t.2.1 t.2.2) : ↥S.Mg) : G),
        S.evC_vec3_mem_Ag r t.1 t.2.1 t.2.2⟩ : S.Ag r)) := by
    rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
    have h0 : ((evC (basis r) (vec3 i j k) : ↥S.Mg) : G) =
        ((evC (basis r) (vec3 i' j' k') : ↥S.Mg) : G) := by
      have := congrArg (fun t : ↥(S.Ag r) => (t : G)) h
      simpa using this
    have h2 := (evC_basis_bijective r).1 (Subtype.ext h0)
    have e0 : 2 * i = 2 * i' := by simpa [vec3] using congrFun h2 0
    have e2 : j = j' := by simpa [vec3] using congrFun h2 2
    have e3 : k = k' := by simpa [vec3] using congrFun h2 3
    have key : ∀ a b : ZMod 3, 2 * a = 2 * b → a = b := by decide
    rw [key _ _ e0, e2, e3]
  have := Nat.card_le_card_of_injective _ hinj
  rwa [show Nat.card (ZMod 3 × ZMod 3 × ZMod 3) = 27 by
    rw [Nat.card_eq_fintype_card]; simp] at this

end JWSetup

end CFSG.Quasithin.H13.U43
