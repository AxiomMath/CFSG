module

public import CFSG.Monster.Code.LoopIdentities
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.Monster.Spin

open CFSG.Monster.Code

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem two_eq_zero' : (2 : ZMod 2) = 0 := rfl

@[expose] def ΩC : C := ⟨Ω, Ω_mem_C⟩

@[simp] theorem coe_ΩC : (ΩC : Fin 24 → ZMod 2) = Ω := rfl

@[expose] def μ₀ : C →ₗ[ZMod 2] ZMod 2 := (LinearMap.proj 0 ∘ₗ ψ) ∘ₗ C.subtype

theorem μ₀_apply (d : C) : μ₀ d = ψ d 0 := rfl

theorem μ₀_eq_repr (d : C) : μ₀ d = basisC.repr d 0 := (repr_apply d 0).symm

@[simp] theorem μ₀_ΩC : μ₀ ΩC = 1 := by decide

@[expose] def C₀ : Submodule (ZMod 2) C := LinearMap.ker μ₀

theorem mem_C₀ {d : C} : d ∈ C₀ ↔ μ₀ d = 0 := LinearMap.mem_ker

instance : DecidablePred (· ∈ C₀) := fun _ => decidable_of_iff _ mem_C₀.symm

@[simp] theorem μ₀_coe (c : C₀) : μ₀ (c : C) = 0 := mem_C₀.1 c.2

@[expose] def π₀ : C →ₗ[ZMod 2] C₀ :=
  LinearMap.codRestrict C₀ (LinearMap.id + μ₀.smulRight ΩC) fun u => by
    rw [mem_C₀, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply, map_add,
      map_smul, μ₀_ΩC, smul_eq_mul, mul_one, ← two_mul, two_eq_zero', zero_mul]

theorem coe_π₀ (u : C) : (π₀ u : C) = u + μ₀ u • ΩC := rfl

@[simp] theorem π₀_coe (c : C₀) : π₀ (c : C) = c := by
  apply Subtype.ext
  rw [coe_π₀, μ₀_coe, zero_smul, add_zero]

@[simp] theorem π₀_ΩC : π₀ ΩC = 0 := by
  apply Subtype.ext
  rw [coe_π₀, μ₀_ΩC, one_smul, add_self_C]
  rfl

theorem π₀_add_μ₀ (u : C) : (π₀ u : C) + μ₀ u • ΩC = u := by
  rw [coe_π₀, add_assoc, ← two_smul (ZMod 2), smul_smul, two_eq_zero', zero_mul, zero_smul,
    add_zero]

theorem eq_of_π₀_μ₀ {u v : C} (h₁ : π₀ u = π₀ v) (h₂ : μ₀ u = μ₀ v) : u = v := by
  rw [← π₀_add_μ₀ u, ← π₀_add_μ₀ v, h₁, h₂]

@[expose] def splitC : C ≃ₗ[ZMod 2] C₀ × ZMod 2 where
  toFun u := (π₀ u, μ₀ u)
  invFun p := (p.1 : C) + p.2 • ΩC
  map_add' u v := by simp only [map_add, Prod.mk_add_mk]
  map_smul' c u := by simp only [map_smul, RingHom.id_apply, Prod.smul_mk]
  left_inv u := π₀_add_μ₀ u
  right_inv p := by
    refine Prod.ext ?_ ?_
    · simp only [map_add, map_smul, π₀_coe, π₀_ΩC, smul_zero, add_zero]
    · simp only [map_add, map_smul, μ₀_coe, μ₀_ΩC, smul_eq_mul, mul_one, zero_add]

theorem natCard_C : Nat.card C = 2 ^ 12 := by
  rw [Nat.card_congr basisC.equivFun.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem natCard_C₀ : Nat.card C₀ = 2 ^ 11 := by
  have h := natCard_C
  rw [Nat.card_congr splitC.toEquiv, Nat.card_prod, Nat.card_zmod] at h
  omega

theorem card_C : Fintype.card C = 4096 := by
  rw [Fintype.card_eq_nat_card, natCard_C]; rfl

theorem card_C₀ : Fintype.card C₀ = 2048 := by
  rw [Fintype.card_eq_nat_card, natCard_C₀]; rfl

abbrev Cocode : Type := (Fin 24 → ZMod 2) ⧸ C

noncomputable instance : DecidableEq Cocode := Classical.decEq _

@[expose] def dotL (a : Fin 24 → ZMod 2) : (Fin 24 → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun x := a ⬝ᵥ x
  map_add' x y := dotProduct_add a x y
  map_smul' c x := by rw [dotProduct_smul, RingHom.id_apply]

@[expose] def pair (a : C) : Cocode →ₗ[ZMod 2] ZMod 2 :=
  C.liftQ (dotL a) fun _ hx => LinearMap.mem_ker.2 (dotProduct_eq_zero a.2 hx)

theorem pair_mk (a : C) (x : Fin 24 → ZMod 2) :
    pair a (Submodule.Quotient.mk x) = (a : Fin 24 → ZMod 2) ⬝ᵥ x := rfl

theorem pair_add_left (a b : C) (δ : Cocode) : pair (a + b) δ = pair a δ + pair b δ := by
  induction δ using Submodule.Quotient.induction_on with
  | H x => simp only [pair_mk, Submodule.coe_add, add_dotProduct]

theorem pair_smul_left (c : ZMod 2) (a : C) (δ : Cocode) : pair (c • a) δ = c * pair a δ := by
  induction δ using Submodule.Quotient.induction_on with
  | H x => simp only [pair_mk, Submodule.coe_smul, smul_dotProduct, smul_eq_mul]

@[simp] theorem pair_zero_left (δ : Cocode) : pair 0 δ = 0 := by
  induction δ using Submodule.Quotient.induction_on with
  | H x => simp only [pair_mk, Submodule.coe_zero, zero_dotProduct]

theorem pair_add_right (a : C) (δ ε : Cocode) : pair a (δ + ε) = pair a δ + pair a ε :=
  map_add _ _ _

@[simp] theorem pair_zero_right (a : C) : pair a 0 = 0 := map_zero _

@[expose] def pairing : C →ₗ[ZMod 2] Cocode →ₗ[ZMod 2] ZMod 2 where
  toFun := pair
  map_add' a b := LinearMap.ext fun δ => pair_add_left a b δ
  map_smul' c a := LinearMap.ext fun δ => pair_smul_left c a δ

theorem pairing_apply (a : C) (δ : Cocode) : pairing a δ = pair a δ := rfl

theorem eq_zero_of_forall_pair {δ : Cocode} (h : ∀ u : C, pair u δ = 0) : δ = 0 := by
  induction δ using Submodule.Quotient.induction_on with
  | H x =>
    rw [Submodule.Quotient.mk_eq_zero, mem_C_iff_forall_dotProduct]
    intro y hy
    rw [dotProduct_comm]
    exact h ⟨y, hy⟩

theorem ext_pair {δ ε : Cocode} (h : ∀ u : C, pair u δ = pair u ε) : δ = ε := by
  rw [← sub_eq_zero]
  exact eq_zero_of_forall_pair fun u => by rw [map_sub, h u, sub_self]

theorem eq_zero_of_forall_pair_left {a : C} (h : ∀ δ : Cocode, pair a δ = 0) : a = 0 := by
  apply Subtype.ext
  funext i
  have := h (Submodule.Quotient.mk (Pi.single i 1))
  rw [pair_mk, dotProduct_single, mul_one] at this
  exact this

theorem exists_pair_eq (f : C →ₗ[ZMod 2] ZMod 2) : ∃ δ : Cocode, ∀ u : C, pair u δ = f u := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f
  refine ⟨Submodule.Quotient.mk fun i => g fun j => if i = j then 1 else 0, fun u => ?_⟩
  rw [pair_mk, ← hg, LinearMap.comp_apply, Submodule.subtype_apply,
    LinearMap.pi_apply_eq_sum_univ g (u : Fin 24 → ZMod 2)]
  simp only [dotProduct, smul_eq_mul]

theorem pair_perfect (f : C →ₗ[ZMod 2] ZMod 2) : ∃! δ : Cocode, ∀ u : C, pair u δ = f u := by
  obtain ⟨δ, hδ⟩ := exists_pair_eq f
  exact ⟨δ, hδ, fun ε hε => ext_pair fun u => by rw [hε u, hδ u]⟩

@[expose] noncomputable def cocodeDual : Cocode ≃ₗ[ZMod 2] Module.Dual (ZMod 2) C :=
  LinearEquiv.ofBijective pairing.flip
    ⟨fun _ _ h => ext_pair fun u => LinearMap.congr_fun h u,
      fun f => (exists_pair_eq f).imp fun _ hδ => LinearMap.ext hδ⟩

theorem cocodeDual_apply (δ : Cocode) (u : C) : cocodeDual δ u = pair u δ := rfl

theorem finrank_cocode : Module.finrank (ZMod 2) Cocode = 12 := by
  have h : Module.finrank (ZMod 2) Cocode + Module.finrank (ZMod 2) C = 24 := by
    have := Submodule.finrank_quotient_add_finrank C
    rwa [Module.finrank_fin_fun] at this
  rw [finrank_C] at h
  omega

theorem natCard_cocode : Nat.card Cocode = 2 ^ 12 := by
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), finrank_cocode,
    ZMod.card]

theorem card_cocode : Fintype.card Cocode = 4096 := by
  rw [Fintype.card_eq_nat_card, natCard_cocode]; rfl

theorem pair_ΩC_mk_single : pair ΩC (Submodule.Quotient.mk (Pi.single 0 1)) = 1 := by
  rw [pair_mk, dotProduct_single, mul_one]
  rfl

private theorem K_Ω (a : C) : K a Ω = 0 := by
  have h : (a : Fin 24 → ZMod 2) * Ω = a := by
    funext i; simp [Ω]
  rw [K_eq, h]
  obtain ⟨m, hm⟩ := four_dvd_wt a.2
  rw [hm, show 4 * m / 2 = 2 * m by omega, Nat.cast_mul, Nat.cast_ofNat, two_eq_zero', zero_mul]

@[simp] theorem θ_ΩC_left (u : C) : θ ΩC u = 0 := θ_Ω u

@[simp] theorem θ_ΩC_right (a : C) : θ a ΩC = 0 := by
  have h := θ_add_θ_swap a ΩC
  rw [θ_ΩC_left, add_zero, coe_ΩC, K_Ω] at h
  exact h

theorem P_Ω : P Ω = 0 := by decide

@[simp] theorem θ_π₀ (a u : C) : θ a (π₀ u) = θ a u := by
  rw [coe_π₀, θ_add_right, θ_smul_right, θ_ΩC_right, mul_zero, add_zero]

theorem pair_π₀ (u : C) (δ : Cocode) : pair (π₀ u) δ = pair u δ + μ₀ u * pair ΩC δ := by
  rw [coe_π₀, pair_add_left, pair_smul_left]

@[expose] noncomputable def θL (a : C) : C →ₗ[ZMod 2] ZMod 2 where
  toFun := θ a
  map_add' := θ_add_right a
  map_smul' c e := by rw [θ_smul_right, smul_eq_mul, RingHom.id_apply]

theorem θL_apply (a u : C) : θL a u = θ a u := rfl

@[expose] noncomputable def thetaD (a : C) : Cocode := (exists_pair_eq (θL a)).choose

theorem pair_thetaD (a u : C) : pair u (thetaD a) = θ a u :=
  (exists_pair_eq (θL a)).choose_spec u

theorem thetaD_unique {a : C} {δ : Cocode} (h : ∀ u : C, pair u δ = θ a u) : δ = thetaD a :=
  ext_pair fun u => by rw [h u, pair_thetaD]

theorem pair_self_thetaD (a : C) : pair a (thetaD a) = P a := by
  rw [pair_thetaD, θ_self]

@[simp] theorem pair_ΩC_thetaD (a : C) : pair ΩC (thetaD a) = 0 := by
  rw [pair_thetaD, θ_ΩC_right]

@[simp] theorem thetaD_zero : thetaD 0 = 0 :=
  (thetaD_unique fun u => by rw [pair_zero_right, θ_zero_left]).symm

theorem thetaD_ΩC : thetaD ΩC = 0 :=
  (thetaD_unique fun u => by rw [pair_zero_right, θ_ΩC_left]).symm

@[expose] def Acocode (a b : C) : Cocode :=
  Submodule.Quotient.mk ((a : Fin 24 → ZMod 2) * b)

theorem pair_Acocode (a b u : C) : pair u (Acocode a b) = A a b u := by
  rw [Acocode, pair_mk, A_eq_sum, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.mul_apply]; ring

theorem Acocode_unique {a b : C} {δ : Cocode} (h : ∀ u : C, pair u δ = A a b u) :
    δ = Acocode a b :=
  ext_pair fun u => by rw [h u, pair_Acocode]

@[simp] theorem pair_ΩC_Acocode (a b : C) : pair ΩC (Acocode a b) = 0 := by
  rw [pair_Acocode, A_comm₂₃, A_comm₁₂]
  calc A Ω a b = ∑ i, (a : Fin 24 → ZMod 2) i * (b : Fin 24 → ZMod 2) i := by
        rw [A_eq_sum]
        exact Finset.sum_congr rfl fun i _ => by simp [Ω]
    _ = (a : Fin 24 → ZMod 2) ⬝ᵥ b := rfl
    _ = 0 := dotProduct_eq_zero a.2 b.2

theorem thetaD_add (a b : C) : thetaD (a + b) = thetaD a + thetaD b + Acocode a b :=
  (thetaD_unique fun u => by
    rw [pair_add_right, pair_add_right, pair_thetaD, pair_thetaD, pair_Acocode,
      θ_add_left]).symm

end CFSG.Monster.Spin
