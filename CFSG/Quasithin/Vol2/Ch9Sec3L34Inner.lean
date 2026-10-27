module

public import CFSG.Quasithin.Vol2.Ch9Sec3L34Facts
public import CFSG.Quasithin.Vol2.Ch9Sec3L34Diag
public import CFSG.Quasithin.Vol2.Ch5Sec1M23L34Fact

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem factM23L34Inner_holds :
    FactM23L34Inner := by
  intro Γ _ _ L A R hL hAL hA hRL hRA hR r hr
  obtain ⟨e⟩ := M23Perm.nonempty_mulEquiv_H0 hL
  have hrL : r ∈ Subgroup.normalizer (L : Set Γ) := hRL hr
  have hrA : r ∈ Subgroup.normalizer (A : Set Γ) := hRA hr
  obtain ⟨m, hm⟩ := M23Perm.exists_intertwiner e hrL
  set l₀ : ↥L := e.symm m with hl₀
  have hconj : ∀ x ∈ L, r * x * r⁻¹ = (l₀ : Γ) * x * (l₀ : Γ)⁻¹ := by
    intro x hx
    have hx' : r * x * r⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hrL x).mp hx
    have h1 := hm ⟨x, hx⟩ ⟨r * x * r⁻¹, hx'⟩ rfl
    have h2 : e ⟨r * x * r⁻¹, hx'⟩ = e (l₀ * ⟨x, hx⟩ * l₀⁻¹) := by
      rw [h1, map_mul, map_mul, map_inv, hl₀, MulEquiv.apply_symm_apply]
    exact congrArg Subtype.val (e.injective h2)
  have hpow : ∀ n : ℕ, ∀ x ∈ L,
      r ^ n * x * (r ^ n)⁻¹ = (l₀ : Γ) ^ n * x * ((l₀ : Γ) ^ n)⁻¹ := by
    intro n
    induction n with
    | zero =>
      intro x _
      rw [pow_zero, pow_zero]
    | succ n ih =>
      intro x hx
      have hxn : (l₀ : Γ) ^ n * x * ((l₀ : Γ) ^ n)⁻¹ ∈ L :=
        L.mul_mem (L.mul_mem (L.pow_mem l₀.2 n) hx) (L.inv_mem (L.pow_mem l₀.2 n))
      calc r ^ (n + 1) * x * (r ^ (n + 1))⁻¹ = r * (r ^ n * x * (r ^ n)⁻¹) * r⁻¹ := by group
        _ = r * ((l₀ : Γ) ^ n * x * ((l₀ : Γ) ^ n)⁻¹) * r⁻¹ := by rw [ih x hx]
        _ = (l₀ : Γ) * ((l₀ : Γ) ^ n * x * ((l₀ : Γ) ^ n)⁻¹) * (l₀ : Γ)⁻¹ := hconj _ hxn
        _ = (l₀ : Γ) ^ (n + 1) * x * ((l₀ : Γ) ^ (n + 1))⁻¹ := by group
  have hl₀N : (l₀ : Γ) ∈ Subgroup.normalizer (A : Set Γ) := by
    refine L34.mem_normalizer_of_forall fun x hx => ?_
    rw [← hconj x (hAL hx)]
    exact (Subgroup.mem_normalizer_iff.mp hrA x).mp hx
  have hidx : (A.subgroupOf (L ⊓ Subgroup.normalizer (A : Set Γ))).index = 2 :=
    m23_l34_relIndex_normalizer hL hAL hA
  have hsq : (l₀ : Γ) * l₀ ∈ A :=
    Subgroup.mem_subgroupOf.mp (Subgroup.mul_self_mem_of_index_two hidx
      ⟨l₀, Subgroup.mem_inf.mpr ⟨l₀.2, hl₀N⟩⟩)
  obtain ⟨j, hj⟩ : Odd (orderOf r) := hR.of_dvd_nat (R.orderOf_dvd_natCard hr)
  refine ⟨((l₀ : Γ) * l₀) ^ (j + 1), A.pow_mem hsq _, fun x hx => ?_⟩
  have h1 := hpow (2 * (j + 1)) x (hAL hx)
  have h2 : r ^ (2 * (j + 1)) = r := by
    rw [show 2 * (j + 1) = orderOf r + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
  have h3 : (l₀ : Γ) ^ (2 * (j + 1)) = ((l₀ : Γ) * l₀) ^ (j + 1) := by
    rw [pow_mul, sq]
  rw [h2, h3] at h1
  exact h1

end CFSG.Quasithin.H13.Ch9
