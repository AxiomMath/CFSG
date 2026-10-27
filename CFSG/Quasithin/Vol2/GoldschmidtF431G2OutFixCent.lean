module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2UNorm
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsG2Data

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
  CFSG.Quasithin.H13.Sec53F.G2 CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2

section Cent

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem pow_four_le_card_centralizer {g : C K} (F : K × K × K × K → C K)
    (hF : Function.Injective F) (hU : ∀ c, F c ∈ U K) (hg : ∀ c, F c * g = g * F c) :
    Nat.card K ^ 4 ≤ Nat.card ↥(U K ⊓ Subgroup.centralizer ({g} : Set (C K))) := by
  have hmem : ∀ c, F c ∈ U K ⊓ Subgroup.centralizer ({g} : Set (C K)) := fun c =>
    ⟨hU c, Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact (hg c).symm⟩
  have : Finite (C K) := Subtype.finite
  have h := Nat.card_le_card_of_injective (fun c => (⟨F c, hmem c⟩ :
    ↥(U K ⊓ Subgroup.centralizer ({g} : Set (C K))))) (fun a b hab => hF (congrArg Subtype.val hab))
  simp only [Nat.card_prod] at h
  calc Nat.card K ^ 4 = Nat.card K * (Nat.card K * (Nat.card K * Nat.card K)) := by ring
    _ ≤ _ := h

theorem nf_comm_xa (α μ ν γ : K) : nf α 0 μ ν 0 γ * xa 1 = xa 1 * nf α 0 μ ν 0 γ := by
  rw [xa_eq_nf, nf_mul, nf_mul]
  refine nf_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem nf_comm_xc (α μ ν γ : K) : nf α 0 μ ν 0 γ * xc 1 = xc 1 * nf α 0 μ ν 0 γ := by
  rw [xc_eq_nf, nf_mul, nf_mul]
  refine nf_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem nf_comm_xu (α μ β γ : K) : nf α 0 μ 0 β γ * xu 1 = xu 1 * nf α 0 μ 0 β γ := by
  rw [xu_eq_nf, nf_mul, nf_mul]
  refine nf_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem nf_comm_xv (α ν β γ : K) : nf α 0 0 ν β γ * xv 1 = xv 1 * nf α 0 0 ν β γ := by
  rw [xv_eq_nf, nf_mul, nf_mul]
  refine nf_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem nf_comm_xb (μ ν β γ : K) : nf 0 0 μ ν β γ * xb 1 = xb 1 * nf 0 0 μ ν β γ := by
  rw [xb_eq_nf, nf_mul, nf_mul]
  refine nf_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem pow_four_le_card_centralizer_xa :
    Nat.card K ^ 4 ≤ Nat.card ↥(U K ⊓ Subgroup.centralizer ({xa (1 : K)} : Set (C K))) :=
  pow_four_le_card_centralizer (fun c => nf c.1 0 c.2.1 c.2.2.1 0 c.2.2.2)
    (fun a b h => by
      obtain ⟨h1, -, h3, h4, -, h6⟩ := nf_injective h
      exact Prod.ext h1 (Prod.ext h3 (Prod.ext h4 h6)))
    (fun c => nf_mem_U _ _ _ _ _ _) (fun c => nf_comm_xa _ _ _ _)

theorem pow_four_le_card_centralizer_xc :
    Nat.card K ^ 4 ≤ Nat.card ↥(U K ⊓ Subgroup.centralizer ({xc (1 : K)} : Set (C K))) :=
  pow_four_le_card_centralizer (fun c => nf c.1 0 c.2.1 c.2.2.1 0 c.2.2.2)
    (fun a b h => by
      obtain ⟨h1, -, h3, h4, -, h6⟩ := nf_injective h
      exact Prod.ext h1 (Prod.ext h3 (Prod.ext h4 h6)))
    (fun c => nf_mem_U _ _ _ _ _ _) (fun c => nf_comm_xc _ _ _ _)

theorem pow_four_le_card_centralizer_xu :
    Nat.card K ^ 4 ≤ Nat.card ↥(U K ⊓ Subgroup.centralizer ({xu (1 : K)} : Set (C K))) :=
  pow_four_le_card_centralizer (fun c => nf c.1 0 c.2.1 0 c.2.2.1 c.2.2.2)
    (fun a b h => by
      obtain ⟨h1, -, h3, -, h5, h6⟩ := nf_injective h
      exact Prod.ext h1 (Prod.ext h3 (Prod.ext h5 h6)))
    (fun c => nf_mem_U _ _ _ _ _ _) (fun c => nf_comm_xu _ _ _ _)

theorem pow_four_le_card_centralizer_xv :
    Nat.card K ^ 4 ≤ Nat.card ↥(U K ⊓ Subgroup.centralizer ({xv (1 : K)} : Set (C K))) :=
  pow_four_le_card_centralizer (fun c => nf c.1 0 0 c.2.1 c.2.2.1 c.2.2.2)
    (fun a b h => by
      obtain ⟨h1, -, -, h4, h5, h6⟩ := nf_injective h
      exact Prod.ext h1 (Prod.ext h4 (Prod.ext h5 h6)))
    (fun c => nf_mem_U _ _ _ _ _ _) (fun c => nf_comm_xv _ _ _ _)

theorem pow_four_le_card_centralizer_xb :
    Nat.card K ^ 4 ≤ Nat.card ↥(U K ⊓ Subgroup.centralizer ({xb (1 : K)} : Set (C K))) :=
  pow_four_le_card_centralizer (fun c => nf 0 0 c.1 c.2.1 c.2.2.1 c.2.2.2)
    (fun a b h => by
      obtain ⟨-, -, h3, h4, h5, h6⟩ := nf_injective h
      exact Prod.ext h3 (Prod.ext h4 (Prod.ext h5 h6)))
    (fun c => nf_mem_U _ _ _ _ _ _) (fun c => nf_comm_xb _ _ _ _)

theorem xc_comm_of_mem_U {x : C K} (hx : x ∈ U K) (s : K) : xc s * x = x * xc s := by
  obtain ⟨α, ρ, μ, ν, β, γ, rfl⟩ := exists_nf hx
  rw [xc_eq_nf, nf_mul, nf_mul]
  refine nf_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem eq_xc_of_comm_xa_xr {x : C K} (hx : x ∈ U K) (ha : x * xa 1 = xa 1 * x)
    (hr : x * xr 1 = xr 1 * x) : ∃ γ : K, x = xc γ := by
  obtain ⟨α, ρ, μ, ν, β, γ, rfl⟩ := exists_nf hx
  rw [xa_eq_nf, nf_mul, nf_mul] at ha
  rw [xr_eq_nf, nf_mul, nf_mul] at hr
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := nf_injective ha
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := nf_injective hr
  have hρ : ρ = 0 := by linear_combination a3
  have hβ : β = 0 := by
    subst hρ
    linear_combination a6
  have hα : α = 0 := by linear_combination (-1 : K) * r3
  have hμ : μ = 0 := by
    subst hα
    have : μ ^ 2 = 0 := by linear_combination r6
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  have hν : ν = 0 := by
    subst hα hμ
    linear_combination r5
  refine ⟨γ, ?_⟩
  rw [xc_eq_nf]
  exact nf_congr hα hρ hμ hν hβ rfl

theorem central_of_comm_xa_xr {x : C K} (hx : x ∈ U K) (ha : x * xa 1 = xa 1 * x)
    (hr : x * xr 1 = xr 1 * x) {w : C K} (hw : w ∈ U K) : x * w = w * x := by
  obtain ⟨γ, rfl⟩ := eq_xc_of_comm_xa_xr hx ha hr
  exact xc_comm_of_mem_U hw γ

theorem xa_one_comm_xb_one : xa (1 : K) * xb 1 * (xa 1)⁻¹ * (xb 1)⁻¹ = xc 1 := by
  have h11 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rw [xa_inv, xb_inv, xa_eq_nf, xb_eq_nf, xc_eq_nf, nf_mul, nf_mul, nf_mul]
  refine nf_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> simp [h11]

end Cent

end CFSG.Quasithin.H13.F431.G2
