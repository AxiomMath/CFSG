module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2TBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL2S

namespace F6

namespace GoldAmL2T

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

section Cyclic

variable [Finite D] {x a a₁ a₂ : D} (g : Gen A B z V x a a₁ a₂)

include g

theorem kerK_eq_zpowers_c : kerK B V = Subgroup.zpowers (a * a₁ * a₂) := by
  have h1 : kerK B V = centerOf (conjClosure V B) := g.hyp.kerK_eq_center_U
  obtain ⟨h2, -⟩ := g.center_U_eq
  have hzc : Subgroup.zpowers z ≤ Subgroup.zpowers (a * a₁ * a₂) := by
    refine Subgroup.zpowers_le.mpr ?_
    rw [← c_sq g, ← pow_two]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
  rw [h1, h2]
  exact sup_eq_right.mpr hzc

theorem c_mem_kerK : a * a₁ * a₂ ∈ kerK B V := by
  rw [kerK_eq_zpowers_c g]; exact Subgroup.mem_zpowers _

omit [Finite D] in
theorem even_of_zpow_eq_one {j : ℤ} (hj : z ^ j = 1) : ∃ m : ℤ, j = 2 * m := by
  have h1 : orderOf z = 2 := orderOf_eq_prime (by simpa [pow_two] using g.z_mul_z)
    g.hyp.natural.z_ne
  have h2 : (orderOf z : ℤ) ∣ j := orderOf_dvd_iff_zpow_eq_one.mpr hj
  rw [h1] at h2
  obtain ⟨m, hm⟩ := h2
  exact ⟨m, by simpa using hm⟩


theorem U_eq_centralizer (hT : Nat.card ↥(A ⊓ B) = 64) :
    conjClosure V B = pCoreOf 2 B ⊓ Subgroup.centralizer ({a * a₁ * a₂} : Set D) := by
  obtain ⟨q₀, hq₀, hcomm⟩ := exists_q0 g hT
  have hQ := card_QB_of_card_T g hT
  have hUC : conjClosure V B ≤
      pCoreOf 2 B ⊓ Subgroup.centralizer ({a * a₁ * a₂} : Set D) := by
    intro u hu
    refine ⟨g.hyp.U_le hu, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact g.c_central u hu
  have hlt : pCoreOf 2 B ⊓ Subgroup.centralizer ({a * a₁ * a₂} : Set D) < pCoreOf 2 B := by
    refine lt_of_le_of_ne inf_le_left fun e => ?_
    have hq₀C : q₀ ∈ pCoreOf 2 B ⊓ Subgroup.centralizer ({a * a₁ * a₂} : Set D) := by
      rw [e]; exact hq₀
    have h1 : (a * a₁ * a₂) * q₀ = q₀ * (a * a₁ * a₂) :=
      Subgroup.mem_centralizer_iff.mp hq₀C.2 _ rfl
    have h2 : (a * a₁ * a₂) * q₀ * (a * a₁ * a₂)⁻¹ * q₀⁻¹ = 1 := by rw [h1]; group
    rw [h2] at hcomm
    exact g.hyp.natural.z_ne hcomm.symm
  have hCp : IsPGroup 2 ↥(pCoreOf 2 B ⊓ Subgroup.centralizer ({a * a₁ * a₂} : Set D)) :=
    g.hyp.isPGroup_T.to_le (inf_le_left.trans g.hyp.QB_le_T)
  obtain ⟨n, hn⟩ := hCp.exists_card_eq
  have hlt' := card_lt_of_lt' hlt
  rw [hQ, hn] at hlt'
  have hn4 : n ≤ 4 := by
    by_contra hc
    push Not at hc
    have : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hc
    omega
  have hle : Nat.card ↥(pCoreOf 2 B ⊓ Subgroup.centralizer ({a * a₁ * a₂} : Set D)) ≤
      Nat.card ↥(conjClosure V B) := by
    rw [hn, g.hyp.card_U]
    calc 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hn4
      _ = 16 := by norm_num
  exact Subgroup.eq_of_le_of_card_ge hUC hle

theorem comm_c_of_not_mem (hT : Nat.card ↥(A ⊓ B) = 64) {q : D} (hq : q ∈ pCoreOf 2 B)
    (hqU : q ∉ conjClosure V B) : (a * a₁ * a₂) * q * (a * a₁ * a₂)⁻¹ * q⁻¹ = z := by
  have hmem := g.hyp.comm_UQ g.c_mem_U hq
  rcases g.hyp.mem_zpowers hmem with h1 | h1
  · exfalso
    apply hqU
    rw [U_eq_centralizer g hT]
    refine ⟨hq, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    calc (a * a₁ * a₂) * q = ((a * a₁ * a₂) * q * (a * a₁ * a₂)⁻¹ * q⁻¹) * (q * (a * a₁ * a₂)) := by
          group
      _ = q * (a * a₁ * a₂) := by rw [h1, one_mul]
  · exact h1

theorem conj_zpow_c (hT : Nat.card ↥(A ⊓ B) = 64) {q : D} (hq : q ∈ pCoreOf 2 B)
    (hqU : q ∉ conjClosure V B) (j : ℤ) :
    q * (a * a₁ * a₂) ^ j * q⁻¹ = z ^ j * (a * a₁ * a₂) ^ j := by
  have hcomm := comm_c_of_not_mem g hT hq hqU
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right g.z_mul_z
  have h1 : q * (a * a₁ * a₂) * q⁻¹ * (a * a₁ * a₂)⁻¹ = z := by
    calc q * (a * a₁ * a₂) * q⁻¹ * (a * a₁ * a₂)⁻¹
        = ((a * a₁ * a₂) * q * (a * a₁ * a₂)⁻¹ * q⁻¹)⁻¹ := by group
      _ = z := by rw [hcomm, hzinv]
  have h2 : q * (a * a₁ * a₂) * q⁻¹ = z * (a * a₁ * a₂) := by
    calc q * (a * a₁ * a₂) * q⁻¹
        = (q * (a * a₁ * a₂) * q⁻¹ * (a * a₁ * a₂)⁻¹) * (a * a₁ * a₂) := by group
      _ = z * (a * a₁ * a₂) := by rw [h1]
  have hc : Commute z (a * a₁ * a₂) := (g.c_central z g.hyp.z_mem_U).symm
  rw [← conj_zpow, h2, hc.mul_zpow]

theorem zpow_c_mem_of_comm (hT : Nat.card ↥(A ⊓ B) = 64) {q : D} (hq : q ∈ pCoreOf 2 B)
    (hqU : q ∉ conjClosure V B) {j : ℤ}
    (hcomm : q * (a * a₁ * a₂) ^ j * q⁻¹ = (a * a₁ * a₂) ^ j) :
    (a * a₁ * a₂) ^ j ∈ Subgroup.zpowers z := by
  rw [conj_zpow_c g hT hq hqU j] at hcomm
  have hzj : z ^ j = 1 := by
    have : z ^ j * (a * a₁ * a₂) ^ j = 1 * (a * a₁ * a₂) ^ j := by rw [hcomm, one_mul]
    exact mul_right_cancel this
  obtain ⟨m, hm⟩ := even_of_zpow_eq_one g hzj
  have h2 : (a * a₁ * a₂) ^ (2 : ℤ) = z := by rw [zpow_two, c_sq g]
  rw [hm, zpow_mul, h2]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) m

theorem sq_mem_zpowers_QB (hT : Nat.card ↥(A ⊓ B) = 64) {q : D} (hq : q ∈ pCoreOf 2 B) :
    q * q ∈ Subgroup.zpowers z := by
  by_cases hqU : q ∈ conjClosure V B
  · exact g.hyp.sq_U q hqU
  · have hK : q * q ∈ Subgroup.zpowers (a * a₁ * a₂) := by
      rw [← kerK_eq_zpowers_c g]; exact g.hyp.sq_mem_K hq
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hK
    have h1 : q * (q * q) * q⁻¹ = q * q := by group
    rw [← hj] at h1 ⊢
    exact zpow_c_mem_of_comm g hT hq hqU h1

theorem mul_mem_U_of_not_mem (hT : Nat.card ↥(A ⊓ B) = 64) {p q : D} (hp : p ∈ pCoreOf 2 B)
    (hq : q ∈ pCoreOf 2 B) (hpU : p ∉ conjClosure V B) (hqU : q ∉ conjClosure V B) :
    p * q ∈ conjClosure V B := by
  rw [U_eq_centralizer g hT]
  refine ⟨(pCoreOf 2 B).mul_mem hp hq, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  rw [Set.mem_singleton_iff] at hy
  subst hy
  have h1 := conj_zpow_c g hT hp hpU 1
  have h2 := conj_zpow_c g hT hq hqU 1
  simp only [zpow_one] at h1 h2
  have hzp : z * p = p * z := (g.hyp.z_comm (g.hyp.QB_le_T hp).2).symm
  have key : p * q * (a * a₁ * a₂) * (p * q)⁻¹ = a * a₁ * a₂ := by
    calc p * q * (a * a₁ * a₂) * (p * q)⁻¹ = p * (q * (a * a₁ * a₂) * q⁻¹) * p⁻¹ := by group
      _ = p * (z * (a * a₁ * a₂)) * p⁻¹ := by rw [h2]
      _ = z * (p * (a * a₁ * a₂) * p⁻¹) := conj_z_mul hzp _
      _ = z * (z * (a * a₁ * a₂)) := by rw [h1]
      _ = a * a₁ * a₂ := by rw [← mul_assoc, g.z_mul_z, one_mul]
  exact (mul_inv_eq_iff_eq_mul.mp key).symm

theorem comm_mem_zpowers_QB (hT : Nat.card ↥(A ⊓ B) = 64) {p q : D} (hp : p ∈ pCoreOf 2 B)
    (hq : q ∈ pCoreOf 2 B) : p * q * p⁻¹ * q⁻¹ ∈ Subgroup.zpowers z := by
  by_cases hpU : p ∈ conjClosure V B
  · exact g.hyp.comm_UQ hpU hq
  by_cases hqU : q ∈ conjClosure V B
  · have h := g.hyp.comm_UQ hqU hp
    have e : p * q * p⁻¹ * q⁻¹ = (q * p * q⁻¹ * p⁻¹)⁻¹ := by group
    rw [e]
    exact (Subgroup.zpowers z).inv_mem h
  · have hpq := mul_mem_U_of_not_mem g hT hp hq hpU hqU
    have h := g.hyp.comm_UQ hpq ((pCoreOf 2 B).inv_mem hp)
    have e : p * q * p⁻¹ * q⁻¹ = (p * q) * p⁻¹ * (p * q)⁻¹ * (p⁻¹)⁻¹ := by group
    rw [e]
    exact h

theorem center_QB_le (hT : Nat.card ↥(A ⊓ B) = 64) {x : D} (hx : x ∈ pCoreOf 2 B)
    (hcent : ∀ y ∈ pCoreOf 2 B, x * y = y * x) : x ∈ Subgroup.zpowers z := by
  obtain ⟨q₀, hq₀, hcomm⟩ := exists_q0 g hT
  have hq₀U : q₀ ∉ conjClosure V B := fun hU => by
    have h1 : (a * a₁ * a₂) * q₀ = q₀ * (a * a₁ * a₂) := g.c_central q₀ hU
    have h2 : (a * a₁ * a₂) * q₀ * (a * a₁ * a₂)⁻¹ * q₀⁻¹ = 1 := by rw [h1]; group
    rw [h2] at hcomm
    exact g.hyp.natural.z_ne hcomm.symm
  have hxK : x ∈ kerK B V :=
    ⟨hx, Subgroup.mem_centralizer_iff.mpr fun u hu => (hcent u (g.hyp.U_le hu)).symm⟩
  rw [kerK_eq_zpowers_c g] at hxK
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxK
  refine zpow_c_mem_of_comm g hT hq₀ hq₀U ?_
  have := hcent q₀ hq₀
  calc q₀ * (a * a₁ * a₂) ^ j * q₀⁻¹ = (q₀ * (a * a₁ * a₂) ^ j) * q₀⁻¹ := rfl
    _ = ((a * a₁ * a₂) ^ j * q₀) * q₀⁻¹ := by rw [← this]
    _ = (a * a₁ * a₂) ^ j := by group

end Cyclic

end GoldAmL2T

end F6

end CFSG.Quasithin
