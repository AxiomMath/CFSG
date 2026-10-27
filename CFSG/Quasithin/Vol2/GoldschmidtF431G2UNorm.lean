module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2Root
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2RootRel

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2

section Collect

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [CharP K 2]

@[expose] def nf (α ρ μ ν β γ : K) : C K := xa α * xr ρ * xu μ * xv ν * xb β * xc γ

theorem nf_tail (α ρ μ ν β γ : K) (Z : C K) :
    nf α ρ μ ν β γ * Z = xa α * (xr ρ * (xu μ * (xv ν * (xb β * (xc γ * Z))))) := by
  simp only [nf, mul_assoc]

theorem nf_eq_tail (α ρ μ ν β γ : K) :
    nf α ρ μ ν β γ = xa α * (xr ρ * (xu μ * (xv ν * (xb β * xc γ)))) := by
  simp only [nf, mul_assoc]

theorem nf_tail_congr {α α' ρ ρ' μ μ' ν ν' β β' γ γ' : K} (Z : C K) (hα : α = α') (hρ : ρ = ρ')
    (hμ : μ = μ') (hν : ν = ν') (hβ : β = β') (hγ : γ = γ') :
    xa α * (xr ρ * (xu μ * (xv ν * (xb β * (xc γ * Z))))) =
      xa α' * (xr ρ' * (xu μ' * (xv ν' * (xb β' * (xc γ' * Z))))) := by
  subst hα hρ hμ hν hβ hγ
  rfl

theorem nf_one : nf (0 : K) 0 0 0 0 0 = 1 := by
  simp [nf, xa_zero, xr_zero, xu_zero, xv_zero, xb_zero, xc_zero]

theorem nf_mul_xa (α ρ μ ν β γ s : K) (Z : C K) :
    nf α ρ μ ν β γ * (xa s * Z) =
      nf (α + s) ρ (μ + s * ρ) (ν + s * ρ ^ 2) (β + s * ρ ^ 3) (γ + s * β + s * ρ ^ 2 * μ) * Z := by
  simp only [nf_tail]
  simp only [tl_ca, tl_ba, tl_va, tl_ua, tl_ra, xa_tail_add, tl_bu, tl_vu, tl_bv, tl_cv, tl_cb,
    xu_tail_add, xv_tail_add, xb_tail_add, xc_tail_add]
  exact nf_tail_congr Z (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)

theorem nf_mul_xr (α ρ μ ν β γ s : K) (Z : C K) :
    nf α ρ μ ν β γ * (xr s * Z) =
      nf α (ρ + s) μ ν (β + s ^ 2 * μ + s * ν) (γ + s * μ ^ 2) * Z := by
  simp only [nf_tail]
  simp only [tl_br, tl_cr, tl_vr, tl_ur, xr_tail_add, tl_bv, tl_cv, tl_cb, xb_tail_add,
    xc_tail_add]
  exact nf_tail_congr Z (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)

theorem nf_mul_xu (α ρ μ ν β γ s : K) (Z : C K) :
    nf α ρ μ ν β γ * (xu s * Z) = nf α ρ (μ + s) ν β (γ + ν * s) * Z := by
  simp only [nf_tail]
  simp only [tl_bu, tl_cu, tl_vu, xu_tail_add, tl_cb, xc_tail_add]
  exact nf_tail_congr Z (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)

theorem nf_mul_xv (α ρ μ ν β γ s : K) (Z : C K) :
    nf α ρ μ ν β γ * (xv s * Z) = nf α ρ μ (ν + s) β γ * Z := by
  simp only [nf_tail]
  simp only [tl_bv, tl_cv, xv_tail_add]

theorem nf_mul_xb (α ρ μ ν β γ s : K) (Z : C K) :
    nf α ρ μ ν β γ * (xb s * Z) = nf α ρ μ ν (β + s) γ * Z := by
  simp only [nf_tail]
  simp only [tl_cb, xb_tail_add]

theorem nf_mul_xc (α ρ μ ν β γ s : K) (Z : C K) :
    nf α ρ μ ν β γ * (xc s * Z) = nf α ρ μ ν β (γ + s) * Z := by
  simp only [nf_tail]
  simp only [xc_tail_add]

theorem nf_mul_xc_one (α ρ μ ν β γ s : K) : nf α ρ μ ν β γ * xc s = nf α ρ μ ν β (γ + s) := by
  simpa using nf_mul_xc α ρ μ ν β γ s 1

theorem nf_congr {α α' ρ ρ' μ μ' ν ν' β β' γ γ' : K} (hα : α = α') (hρ : ρ = ρ') (hμ : μ = μ')
    (hν : ν = ν') (hβ : β = β') (hγ : γ = γ') : nf α ρ μ ν β γ = nf α' ρ' μ' ν' β' γ' := by
  subst hα hρ hμ hν hβ hγ
  rfl

theorem nf_mul (α ρ μ ν β γ a r u v b e : K) :
    nf α ρ μ ν β γ * nf a r u v b e =
      nf (α + a) (ρ + r) (μ + a * ρ + u) (ν + a * ρ ^ 2 + v)
        (β + a * ρ ^ 3 + r ^ 2 * (μ + a * ρ) + r * (ν + a * ρ ^ 2) + b)
        (γ + a * β + a * ρ ^ 2 * μ + r * (μ + a * ρ) ^ 2 + (ν + a * ρ ^ 2) * u + e) := by
  rw [nf_eq_tail a r u v b e, nf_mul_xa, nf_mul_xr, nf_mul_xu, nf_mul_xv, nf_mul_xb,
    nf_mul_xc_one]

end Collect

section Bijection

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [CharP K 2]

theorem nf_mem_U (α ρ μ ν β γ : K) : nf α ρ μ ν β γ ∈ U K :=
  mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (xa_mem_U α) (xr_mem_U ρ)) (xu_mem_U μ))
    (xv_mem_U ν)) (xb_mem_U β)) (xc_mem_U γ)

theorem posRoots_injective : Function.Injective ![rA, rR, rU, rV, rB, rC] := by decide

theorem posRoots_range :
    Set.range ![rA, rR, rU, rV, rB, rC] = {β | IsRoot Tag.G2 β ∧ 0 < height β} := by
  ext β
  show (∃ i, ![rA, rR, rU, rV, rB, rC] i = β) ↔ (IsRoot Tag.G2 β ∧ 0 < height β)
  rw [isRoot_pos_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩]

theorem bijOn_nf : Set.BijOn
    (fun c : Fin 6 → K =>
      (List.ofFn fun i => pinnedX Tag.G2 K (![rA, rR, rU, rV, rB, rC] i) (c i)).prod)
    Set.univ (posUnipotent Tag.G2 K) :=
  (positive_root_collection Tag.G2 K).2 ![rA, rR, rU, rV, rB, rC] posRoots_injective posRoots_range

theorem prod_ofFn_eq_nf (c : Fin 6 → K) :
    (List.ofFn fun i => pinnedX Tag.G2 K (![rA, rR, rU, rV, rB, rC] i) (c i)).prod =
      ((nf (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) : C K) : ModGL Tag.G2 K) := by
  simp [List.ofFn_succ, nf, mul_assoc, coe_xa, coe_xr, coe_xu, coe_xv, coe_xb, coe_xc]

theorem exists_nf {g : C K} (hg : g ∈ U K) : ∃ α ρ μ ν β γ : K, g = nf α ρ μ ν β γ := by
  obtain ⟨c, -, hc⟩ := (bijOn_nf (K := K)).surjOn
    (show (g : ModGL Tag.G2 K) ∈ posUnipotent Tag.G2 K from hg)
  refine ⟨c 0, c 1, c 2, c 3, c 4, c 5, Subtype.ext ?_⟩
  rw [← prod_ofFn_eq_nf c]
  exact hc.symm

theorem nf_injective {α ρ μ ν β γ α' ρ' μ' ν' β' γ' : K}
    (h : nf α ρ μ ν β γ = nf α' ρ' μ' ν' β' γ') :
    α = α' ∧ ρ = ρ' ∧ μ = μ' ∧ ν = ν' ∧ β = β' ∧ γ = γ' := by
  have h1 := (bijOn_nf (K := K)).injOn (Set.mem_univ ![α, ρ, μ, ν, β, γ])
    (Set.mem_univ ![α', ρ', μ', ν', β', γ']) (by
      simp only [prod_ofFn_eq_nf]
      simpa using congrArg Subtype.val h)
  exact ⟨by simpa using congrFun h1 0, by simpa using congrFun h1 1,
    by simpa using congrFun h1 2, by simpa using congrFun h1 3, by simpa using congrFun h1 4,
    by simpa using congrFun h1 5⟩

theorem nf_eq_iff {α ρ μ ν β γ α' ρ' μ' ν' β' γ' : K} :
    nf α ρ μ ν β γ = nf α' ρ' μ' ν' β' γ' ↔
      α = α' ∧ ρ = ρ' ∧ μ = μ' ∧ ν = ν' ∧ β = β' ∧ γ = γ' :=
  ⟨nf_injective, fun h => nf_congr h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2⟩

@[expose] def nfU (c : K × K × K × K × K × K) : U K :=
  ⟨nf c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2, nf_mem_U _ _ _ _ _ _⟩

theorem coe_nfU (c : K × K × K × K × K × K) :
    ((nfU c : U K) : C K) = nf c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2 := rfl

theorem nfU_injective : Function.Injective (nfU (K := K)) := by
  rintro ⟨a1, a2, a3, a4, a5, a6⟩ ⟨b1, b2, b3, b4, b5, b6⟩ h
  have h' := congrArg Subtype.val h
  rw [coe_nfU, coe_nfU] at h'
  dsimp only at h'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := nf_injective h'
  rw [h1, h2, h3, h4, h5, h6]

theorem nfU_surjective : Function.Surjective (nfU (K := K)) := by
  intro u
  obtain ⟨α, ρ, μ, ν, β, γ, h⟩ := exists_nf u.2
  refine ⟨(α, ρ, μ, ν, β, γ), Subtype.ext ?_⟩
  rw [coe_nfU]
  exact h.symm

theorem card_U : Nat.card (U K) = Nat.card K ^ 6 := by
  have h := Nat.card_congr (Equiv.ofBijective _ ⟨nfU_injective (K := K), nfU_surjective⟩)
  rw [← h]
  simp only [Nat.card_prod]
  ring

theorem xa_eq_nf (s : K) : xa s = nf s 0 0 0 0 0 := by
  simp [nf, xr_zero, xu_zero, xv_zero, xb_zero, xc_zero]

theorem xr_eq_nf (s : K) : xr s = nf 0 s 0 0 0 0 := by
  simp [nf, xa_zero, xu_zero, xv_zero, xb_zero, xc_zero]

theorem xu_eq_nf (s : K) : xu s = nf 0 0 s 0 0 0 := by
  simp [nf, xa_zero, xr_zero, xv_zero, xb_zero, xc_zero]

theorem xv_eq_nf (s : K) : xv s = nf 0 0 0 s 0 0 := by
  simp [nf, xa_zero, xr_zero, xu_zero, xb_zero, xc_zero]

theorem xb_eq_nf (s : K) : xb s = nf 0 0 0 0 s 0 := by
  simp [nf, xa_zero, xr_zero, xu_zero, xv_zero, xc_zero]

theorem xc_eq_nf (s : K) : xc s = nf 0 0 0 0 0 s := by
  simp [nf, xa_zero, xr_zero, xu_zero, xv_zero, xb_zero]

theorem nf_inv (α ρ μ ν β γ : K) :
    (nf α ρ μ ν β γ)⁻¹ =
      nf α ρ (μ + α * ρ) (ν + α * ρ ^ 2) (β + ρ ^ 2 * μ + ρ * ν + α * ρ ^ 3)
        (γ + α * β + ρ * μ ^ 2 + μ * ν + α * ρ * ν) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine inv_eq_of_mul_eq_one_right ?_
  rw [nf_mul, ← nf_one]
  refine nf_congr ?_ ?_ ?_ ?_ ?_ ?_
  · exact CharTwo.add_self_eq_zero α
  · exact CharTwo.add_self_eq_zero ρ
  · linear_combination (μ + α * ρ) * h2
  · linear_combination (ν + α * ρ ^ 2) * h2
  · linear_combination (β + ρ ^ 2 * μ + ρ * ν + 2 * α * ρ ^ 3) * h2
  · linear_combination
      (γ + α * β + ρ * μ ^ 2 + μ * ν + α * ρ * ν + 2 * α * ρ ^ 2 * μ + α ^ 2 * ρ ^ 3) * h2

end Bijection

end CFSG.Quasithin.H13.F431.G2
