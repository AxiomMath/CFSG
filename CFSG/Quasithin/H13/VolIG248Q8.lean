module

public import CFSG.Quasithin.H13.VolIG248Block
public import CFSG.Quasithin.H13.VolIF956Core

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin
  CFSG.Quasithin.A5Model Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

namespace G248

@[expose] def paA : A5 := ⟨pa, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def pbA : A5 := ⟨pb, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

theorem paA_mem : paA ∈ K4 := Or.inr (Or.inl rfl)

theorem pbA_mem : pbA ∈ K4 := Or.inr (Or.inr (Or.inl rfl))

theorem e02_pa : e2 0 2 + pw pa (e2 0 2) = wA 4 := by decide

theorem e01_pb : e2 0 1 + pw pb (e2 0 1) = wA 4 := by decide

theorem e02_pb : pw pb (e2 0 2) = e2 0 2 := by decide

theorem e01_pa : pw pa (e2 0 1) = e2 0 1 := by decide

theorem e02_four : ((e2 0 2 : ↥Ev) : Fin 5 → ZMod 2) 4 = 0 := by decide

theorem e01_four : ((e2 0 1 : ↥Ev) : Fin 5 → ZMod 2) 4 = 0 := by decide

namespace Setting

variable [Finite G] {V V₁ L T H : Subgroup G} {g : G} (X : Setting V V₁ L T H g)
include X

omit [Finite G] in
theorem psi_comm_eq (ev : ↥(conjClosure V₁ L)) (l : ↥L) :
    Multiplicative.toAdd (X.St.D.ψ (X.St.D.comm ev l)) =
      Multiplicative.toAdd (X.St.D.ψ ev) +
        pw (X.St.D.θ l : Equiv.Perm (Fin 5)) (Multiplicative.toAdd (X.St.D.ψ ev)) := by
  rw [RawData5.psi_comm, toAdd_mul, toAdd_inv, toAdd_pact]
  congr 1
  exact neg_eq_of_add_eq_zero_left (Ev_add_self _)

@[expose] noncomputable def z : G := (X.St.D.ψ.symm W4 : G)

omit [Finite G] in
theorem z_mem_VL : X.z ∈ conjClosure V₁ L := (X.St.D.ψ.symm W4).2

omit [Finite G] in
theorem psi_z : X.St.D.ψ ⟨X.z, X.z_mem_VL⟩ = W4 := X.St.D.ψ.apply_symm_apply W4

omit [Finite G] in
theorem z_mem : X.z ∈ V₁ := (X.St.D.line _).2 (Or.inr X.psi_z)

omit [Finite G] in
theorem z_ne_one : X.z ≠ 1 := by
  intro h
  apply W4_ne_one
  rw [← X.psi_z]
  have : (⟨X.z, X.z_mem_VL⟩ : ↥(conjClosure V₁ L)) = 1 := Subtype.ext h
  rw [this, map_one]

omit [Finite G] in
theorem z_sq : X.z * X.z = 1 := by
  have := X.VL_sq X.z_mem_VL
  rwa [pow_two] at this

omit [Finite G] in
theorem eq_one_or_eq_z {v : G} (hv : v ∈ V₁) : v = 1 ∨ v = X.z := by
  have hvL : v ∈ conjClosure V₁ L := le_conjClosure V₁ L hv
  rcases (X.St.D.line ⟨v, hvL⟩).1 hv with h | h
  · left
    have : (⟨v, hvL⟩ : ↥(conjClosure V₁ L)) = 1 := X.St.D.ψ.injective (by rw [h, map_one])
    exact congrArg Subtype.val this
  · right
    have : (⟨v, hvL⟩ : ↥(conjClosure V₁ L)) = ⟨X.z, X.z_mem_VL⟩ :=
      X.St.D.ψ.injective (by rw [h, X.psi_z])
    exact congrArg Subtype.val this

omit [Finite G] in
theorem z_comm {y : G} (hy : y ∈ normalizer (V₁ : Set G)) : y * X.z = X.z * y := by
  have h1 : y * X.z * y⁻¹ ∈ V₁ := (mem_normalizer_iff.mp hy _).mp X.z_mem
  rcases X.eq_one_or_eq_z h1 with h | h
  · exfalso
    apply X.z_ne_one
    have := congrArg (fun w => y⁻¹ * w * y) h
    simpa [mul_assoc] using this
  · calc y * X.z = (y * X.z * y⁻¹) * y := by group
      _ = X.z * y := by rw [h]

omit [Finite G] in
theorem comm_eq_z {ev : ↥(conjClosure V₁ L)} {l : ↥L}
    (h : Multiplicative.toAdd (X.St.D.ψ ev) +
      pw (X.St.D.θ l : Equiv.Perm (Fin 5)) (Multiplicative.toAdd (X.St.D.ψ ev)) = wA 4) :
    (ev : G) * l * (ev : G)⁻¹ * (l : G)⁻¹ = X.z := by
  have h1 : X.St.D.comm ev l = ⟨X.z, X.z_mem_VL⟩ := by
    apply X.St.D.ψ.injective
    apply Multiplicative.toAdd.injective
    rw [X.psi_comm_eq, h, X.psi_z]
    rfl
  have h2 := congrArg Subtype.val h1
  rw [RawData5.coe_comm, commutatorElement_def] at h2
  exact h2

omit [Finite G] in
theorem comm_eq_one {ev : ↥(conjClosure V₁ L)} {l : ↥L}
    (h : pw (X.St.D.θ l : Equiv.Perm (Fin 5)) (Multiplicative.toAdd (X.St.D.ψ ev)) =
      Multiplicative.toAdd (X.St.D.ψ ev)) :
    (ev : G) * l = l * ev := by
  have h1 : X.St.D.comm ev l = 1 := by
    apply X.St.D.ψ.injective
    apply Multiplicative.toAdd.injective
    rw [X.psi_comm_eq, h, map_one, toAdd_one, Ev_add_self]
  have h2 := congrArg Subtype.val h1
  rw [RawData5.coe_comm, commutatorElement_def] at h2
  calc (ev : G) * l = ((ev : G) * l * (ev : G)⁻¹ * (l : G)⁻¹) * (l * ev) := by group
    _ = l * ev := by rw [h2]; simp

theorem exists_U_theta {σ : A5} (hσ : σ ∈ K4) :
    ∃ u : G, ∃ hu : u ∈ conjClosure V H, X.St.D.θ ⟨u, X.U_le_L hu⟩ = σ := by
  rw [← X.St.Ubar_eq_K4] at hσ
  obtain ⟨u, rfl⟩ := hσ
  refine ⟨u, u.2, ?_⟩
  rw [A5SettingCore.betaU_apply, ← X.St.Phi_of_L ⟨u, X.U_le_L u.2⟩]

omit [Finite G] in
theorem theta_VL {e : G} (he : e ∈ conjClosure V₁ L) (heL : e ∈ L) :
    X.St.D.θ ⟨e, heL⟩ = 1 := by
  have h1 : ((⟨e, heL⟩ : ↥L) : G) ∈ pCoreOf 2 (L ⊔ T) := X.St.VL_le_O he
  rw [← MonoidHom.mem_ker, X.St.D.ker_eq, mem_subgroupOf]
  exact h1

theorem exists_lift {σ : A5} (hσ : σ ∈ K4) {ev : ↥(conjClosure V₁ L)} (hev : (ev : G) ∈ V)
    (h : Multiplicative.toAdd (X.St.D.ψ ev) +
      pw (σ : Equiv.Perm (Fin 5)) (Multiplicative.toAdd (X.St.D.ψ ev)) = wA 4) :
    ∃ f : G, ∃ hf : f ∈ conjClosure V H, X.St.D.θ ⟨f, X.U_le_L hf⟩ = σ ∧ f * f = 1 := by
  obtain ⟨u, hu, huθ⟩ := X.exists_U_theta hσ
  have hsq : u * u ∈ V₁ := by
    have := X.St.hyp.G22_sq_mem hu
    rwa [pow_two] at this
  rcases X.eq_one_or_eq_z hsq with h1 | h1
  · exact ⟨u, hu, huθ, h1⟩
  · have heU : (ev : G) ∈ conjClosure V H := le_conjClosure V H hev
    have heL : (ev : G) ∈ L := X.VL_le_L ev.2
    refine ⟨u * ev, mul_mem hu heU, ?_, ?_⟩
    · have : (⟨u * ev, X.U_le_L (mul_mem hu heU)⟩ : ↥L) = ⟨u, X.U_le_L hu⟩ * ⟨ev, heL⟩ := rfl
      rw [this, map_mul, huθ, X.theta_VL ev.2 heL, mul_one]
    · have hc := X.comm_eq_z (ev := ev) (l := ⟨u, X.U_le_L hu⟩) (by rw [huθ]; exact h)
      have h2 : (ev : G) * u = X.z * (u * ev) := by
        rw [← hc]
        group
      have hzu := X.z_comm (X.St.U_le_normV₁ hu)
      have he2 : (ev : G) * ev = 1 := by
        have := X.VL_sq ev.2
        rwa [pow_two] at this
      calc u * ev * (u * ev) = u * ((ev : G) * u) * ev := by group
        _ = u * (X.z * (u * ev)) * ev := by rw [h2]
        _ = (u * X.z) * u * ((ev : G) * ev) := by group
        _ = (X.z * u) * u * ((ev : G) * ev) := by rw [hzu]
        _ = X.z * (u * u) * ((ev : G) * ev) := by group
        _ = 1 := by rw [h1, he2, mul_one]; exact X.z_sq

@[expose] noncomputable def eA : ↥(conjClosure V₁ L) :=
  X.St.D.ψ.symm (Multiplicative.ofAdd (e2 0 2))

@[expose] noncomputable def eB : ↥(conjClosure V₁ L) :=
  X.St.D.ψ.symm (Multiplicative.ofAdd (e2 0 1))

omit [Finite G] in
theorem psi_eA : Multiplicative.toAdd (X.St.D.ψ X.eA) = e2 0 2 := by
  rw [eA, MulEquiv.apply_symm_apply, toAdd_ofAdd]

omit [Finite G] in
theorem psi_eB : Multiplicative.toAdd (X.St.D.ψ X.eB) = e2 0 1 := by
  rw [eB, MulEquiv.apply_symm_apply, toAdd_ofAdd]

omit [Finite G] in
theorem eA_mem_V : (X.eA : G) ∈ V := (X.St.D.hV _).2 (by rw [X.psi_eA]; exact e02_four)

omit [Finite G] in
theorem eB_mem_V : (X.eB : G) ∈ V := (X.St.D.hV _).2 (by rw [X.psi_eB]; exact e01_four)

theorem isQ8Sq : IsQ8Sq ↥(conjClosure V H) := by
  have hAU : (X.eA : G) ∈ conjClosure V H := le_conjClosure V H X.eA_mem_V
  have hBU : (X.eB : G) ∈ conjClosure V H := le_conjClosure V H X.eB_mem_V
  obtain ⟨f₁, hf₁, hf₁θ, hf₁2⟩ :=
    X.exists_lift paA_mem X.eA_mem_V (by rw [X.psi_eA]; exact e02_pa)
  obtain ⟨f₂, hf₂, hf₂θ, hf₂2⟩ :=
    X.exists_lift pbA_mem X.eB_mem_V (by rw [X.psi_eB]; exact e01_pb)
  have h11 : (X.eA : G) * f₁ * (X.eA : G)⁻¹ * f₁⁻¹ = X.z :=
    X.comm_eq_z (l := ⟨f₁, X.U_le_L hf₁⟩) (by rw [hf₁θ, X.psi_eA]; exact e02_pa)
  have h21 : (X.eB : G) * f₁ = f₁ * X.eB :=
    X.comm_eq_one (l := ⟨f₁, X.U_le_L hf₁⟩) (by rw [hf₁θ, X.psi_eB]; exact e01_pa)
  have h22 : (X.eB : G) * f₂ * (X.eB : G)⁻¹ * f₂⁻¹ = X.z :=
    X.comm_eq_z (l := ⟨f₂, X.U_le_L hf₂⟩) (by rw [hf₂θ, X.psi_eB]; exact e01_pb)
  have h12 : (X.eA : G) * f₂ = f₂ * X.eA :=
    X.comm_eq_one (l := ⟨f₂, X.U_le_L hf₂⟩) (by rw [hf₂θ, X.psi_eA]; exact e02_pb)
  have hAB : (X.eA : G) * X.eB = X.eB * X.eA := X.VL_comm X.eA.2 X.eB.2
  have hA2 : (X.eA : G) * X.eA = 1 := by
    have := X.VL_sq X.eA.2
    rwa [pow_two] at this
  have hzf₂ : f₂ * X.z = X.z * f₂ := X.z_comm (X.St.U_le_normV₁ hf₂)
  have hzi : X.z⁻¹ = X.z := inv_eq_of_mul_eq_one_right X.z_sq
  obtain ⟨f, hfU, hf2, hf₁f, hBf, hAf⟩ : ∃ f : G, f ∈ conjClosure V H ∧ f * f = 1 ∧
      f₁ * f = f * f₁ ∧ (X.eB : G) * f * (X.eB : G)⁻¹ * f⁻¹ = X.z ∧ (X.eA : G) * f = f * X.eA := by
    rcases X.eq_one_or_eq_z (X.St.hyp.G22_commutator_mem hf₁ hf₂) with h | h
    · refine ⟨f₂, hf₂, hf₂2, ?_, h22, h12⟩
      calc f₁ * f₂ = (f₁ * f₂ * f₁⁻¹ * f₂⁻¹) * (f₂ * f₁) := by group
        _ = f₂ * f₁ := by rw [h, one_mul]
    · refine ⟨f₂ * X.eA, mul_mem hf₂ hAU, ?_, ?_, ?_, ?_⟩
      · calc f₂ * X.eA * (f₂ * X.eA) = f₂ * ((X.eA : G) * f₂) * X.eA := by group
          _ = f₂ * (f₂ * X.eA) * X.eA := by rw [h12]
          _ = (f₂ * f₂) * ((X.eA : G) * X.eA) := by group
          _ = 1 := by rw [hf₂2, hA2, one_mul]
      · have e1 : f₁ * f₂ = X.z * (f₂ * f₁) := by
          rw [← h]
          group
        have e2 : f₁ * X.eA = X.z * ((X.eA : G) * f₁) := by
          have : (X.eA : G) * f₁ = X.z * (f₁ * X.eA) := by
            rw [← h11]
            group
          calc f₁ * X.eA = X.z⁻¹ * (X.z * (f₁ * X.eA)) := by group
            _ = X.z * ((X.eA : G) * f₁) := by rw [← this, hzi]
        calc f₁ * (f₂ * X.eA) = (f₁ * f₂) * X.eA := by group
          _ = X.z * (f₂ * f₁) * X.eA := by rw [e1]
          _ = X.z * f₂ * (f₁ * X.eA) := by group
          _ = X.z * f₂ * (X.z * ((X.eA : G) * f₁)) := by rw [e2]
          _ = X.z * (f₂ * X.z) * ((X.eA : G) * f₁) := by group
          _ = X.z * (X.z * f₂) * ((X.eA : G) * f₁) := by rw [hzf₂]
          _ = (X.z * X.z) * (f₂ * X.eA) * f₁ := by group
          _ = f₂ * X.eA * f₁ := by rw [X.z_sq, one_mul]
      · have hAB' : (X.eA : G) * (X.eB : G)⁻¹ = (X.eB : G)⁻¹ * X.eA :=
          Commute.inv_right (a := (X.eA : G)) (b := (X.eB : G)) hAB
        calc (X.eB : G) * (f₂ * X.eA) * (X.eB : G)⁻¹ * (f₂ * X.eA)⁻¹
            = (X.eB : G) * f₂ * ((X.eA : G) * (X.eB : G)⁻¹) * (X.eA : G)⁻¹ * f₂⁻¹ := by
              group
          _ = (X.eB : G) * f₂ * ((X.eB : G)⁻¹ * X.eA) * (X.eA : G)⁻¹ * f₂⁻¹ := by
              rw [hAB']
          _ = (X.eB : G) * f₂ * (X.eB : G)⁻¹ * f₂⁻¹ := by group
          _ = X.z := h22
      · calc (X.eA : G) * (f₂ * X.eA) = ((X.eA : G) * f₂) * X.eA := by group
          _ = f₂ * X.eA * X.eA := by rw [h12]
  exact isQ8Sq_of_basis X.card_U hAU hBU hf₁ hfU X.z_ne_one X.z_sq
    (X.VL_comm X.z_mem_VL X.eA.2) (X.VL_comm X.z_mem_VL X.eB.2) hA2
    (by have := X.VL_sq X.eB.2; rwa [pow_two] at this) hf₁2 hf2 hAB hf₁f h11 hBf hAf h21

end Setting

end G248

end CFSG.Quasithin.H13.VolI
