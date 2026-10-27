module

public import CFSG.Quasithin.H13.L32A773g

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem gamma_pow_cases : ∀ x : H6.Γ, x ^ 4 = 1 ∨ x ^ 3 = 1 ∨ x ^ 7 = 1 := by
  decide +kernel

theorem gamma_pow_four {x : H6.Γ} {n : ℕ} (hx : x ^ 2 ^ n = 1) : x ^ 4 = 1 := by
  rcases gamma_pow_cases x with h | h | h
  · exact h
  · have h1 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2)) (orderOf_dvd_of_pow_eq_one h)
      (orderOf_dvd_of_pow_eq_one hx)
    rw [orderOf_eq_one_iff.mp h1, one_pow]
  · have h1 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 7 2)) (orderOf_dvd_of_pow_eq_one h)
      (orderOf_dvd_of_pow_eq_one hx)
    rw [orderOf_eq_one_iff.mp h1, one_pow]

theorem ll_o2 : ∀ g : H6.Γ, g ∈ H6.Ll →
    (∀ h : H6.Γ, h ∈ H6.Ll → (g * h * g⁻¹ * h⁻¹) ^ 4 = 1) →
    stG1⁻¹ * g ∈ H6.Ll ∧ (stG1⁻¹ * g) ^ 3 = 1 := by
  decide +kernel

namespace Ctx73

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx73 G T L V l₀)
include C

theorem exists_theta1 : ∃ θ : ↥L →* H6.Γ, Function.Surjective θ ∧
    θ.ker = (sL T L V).subgroupOf L ∧
    ∀ l : ↥L, θ l ∈ H6.Ll ↔ (l : G) ∈ Subgroup.normalizer (fsuV1 T V : Set G) := by
  obtain ⟨-, -, hLTV, hV1, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hLTV
  have h1281 := C.hyp.hyp1281One C.h13322 C.hMod
  obtain ⟨hcard, hsq, -⟩ := h1281.card_sq
  have : IsMulCommutative ↥V := (C.hMod G T L V C.hyp.hyp C.hyp.fsu).1.1
  obtain ⟨e⟩ : Nonempty (↥V ≃* Multiplicative (Fin 3 → ZMod 2)) :=
    Vol2.Ch10.SecA.nonempty_mulEquiv_pi_of_sq_eq_one
      (fun x => Subtype.ext (by simpa using hsq x x.2)) hcard
  have hρs := repV_surjective hLV e (autOn_eq_top_of_hyp1281One h1281)
  obtain ⟨z, hzV1, hz1, hgen⟩ := exists_gen_of_card_two hV1
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hzV1).1
  obtain ⟨A₀, hA₀⟩ := exists_sl3_e1 (Multiplicative.toAdd (e ⟨z, hzV⟩)) (by
    intro h0
    apply hz1
    have h1 : e ⟨z, hzV⟩ = 1 := by
      rw [← ofAdd_toAdd (e ⟨z, hzV⟩), h0]
      rfl
    exact congrArg Subtype.val (e.injective (h1.trans (map_one e).symm)))
  refine ⟨theta1 hLV e A₀, theta1_surjective hLV e A₀ hρs, ?_, fun l =>
    (theta1_mem_Ll_iff hLV e A₀ hzV hA₀ l).trans (mem_normalizer_iff_of_gen hzV1 hz1 hgen).symm⟩
  ext l
  rw [MonoidHom.mem_ker, theta1_eq_one_iff hLV e A₀, Subgroup.mem_subgroupOf,
    ← C.pCoreOf_eq_sL, C.pCoreOf_eq, Subgroup.mem_inf]
  exact ⟨fun h => ⟨l.2, h⟩, fun h => h.2⟩

theorem QH_le_l1 : pCoreOf 2 (hz T V) ≤ L₁Of L (fsuV1 T V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hV1, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  obtain ⟨θ, hθs, hθk, hθLl⟩ := C.exists_theta1
  have hTH : T ≤ hz T V := le_sup_right.trans C.hF.L₁T_le_H
  have hQL : pCoreOf 2 (hz T V) ≤ L := (pCoreOf_le_of_le C.hyp hTH).trans C.T_le_L
  have hNC := normalizer_eq_centralizer_of_card_two hV1
  intro q hq
  set lq : ↥L := ⟨q, hQL hq⟩ with hlq
  have hqH : q ∈ hz T V := pCoreOf_le 2 _ hq
  have hθq : θ lq ∈ H6.Ll := (hθLl lq).mpr (by rw [hNC]; exact hqH)
  have hcomm : ∀ h : H6.Γ, h ∈ H6.Ll → (θ lq * h * (θ lq)⁻¹ * h⁻¹) ^ 4 = 1 := by
    intro h hh
    obtain ⟨l, rfl⟩ := hθs h
    have hlH : (l : G) ∈ hz T V := by
      have := (hθLl l).mp hh
      rwa [hNC] at this
    have hc : (lq * l * lq⁻¹ * l⁻¹ : ↥L) ∈ (pCoreOf 2 (hz T V)).subgroupOf L := by
      rw [Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show q * (l : G) * q⁻¹ * (l : G)⁻¹ = q * ((l : G) * q⁻¹ * (l : G)⁻¹) by group]
      exact mul_mem hq ((Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCoreOf 2 (hz T V) hlH) _).mp (inv_mem hq))
    obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 (hz T V)) ⟨_, Subgroup.mem_subgroupOf.mp hc⟩
    have h1 : (lq * l * lq⁻¹ * l⁻¹) ^ 2 ^ n = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hn
      simpa using this
    have h2 := congrArg θ h1
    rw [map_pow, map_one, map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    exact gamma_pow_four h2
  obtain ⟨ha, ha3⟩ := ll_o2 (θ lq) hθq hcomm
  obtain ⟨x₁, hx₁, hθx₁⟩ := exists_mem_l1_of hθs (fun l hl => (hθLl l).mp hl) stG1_mem.1
    stG1_mem.2
  obtain ⟨x₂, hx₂, hθx₂⟩ := exists_mem_l1_of hθs (fun l hl => (hθLl l).mp hl) ha ha3
  have hk : (x₁ * x₂)⁻¹ * lq ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, hθx₁, hθx₂]
    group
  rw [hθk, Subgroup.mem_subgroupOf] at hk
  have e : q = ((x₁ : G) * x₂) * ((((x₁ * x₂)⁻¹ * lq : ↥L)) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hlq]
    group
  rw [e]
  exact mul_mem (mul_mem hx₁ hx₂) (C.sL_le_l1 hk)

theorem pCoreOf_hz_eq : pCoreOf 2 (hz T V) = pCoreOf 2 (kz T V) := by
  refine le_antisymm (fun q hq => mem_pCoreOf_kz.mpr
    ⟨l1_le_kz C.hyp C.hMod (C.QH_le_l1 hq), hq⟩) fun q hq => (mem_pCoreOf_kz.mp hq).2

end Ctx73

end CFSG.Quasithin.H13.L32A
