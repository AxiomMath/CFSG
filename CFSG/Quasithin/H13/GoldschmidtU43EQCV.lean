module

public import CFSG.Quasithin.H13.GoldschmidtU43EAbel2
public import CFSG.Quasithin.H13.GoldschmidtU43EQOdd

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)

theorem Vg_inf_Hz (hAU : (S.A : G) ∈ Uz z) {x : G} (hxV : x ∈ S.Vg) (hxH : x ∈ Hz z) :
    x ∈ Subgroup.zpowers (S.σ₁ : G) := by
  have hxC : x ∈ S.Cg1 := S.Vg_le_Cg1 hxV
  obtain ⟨r, hr, k, hk, hrk⟩ := S.exists_RY (n := ⟨x, hxH⟩) hxC
  have hx_eq : x = (r : G) * (k : G) := congrArg Subtype.val hrk
  have hxs : x * (S.σ₁ : G) = (S.σ₁ : G) * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
  have hxs' : x⁻¹ * (S.σ₁ : G) = (S.σ₁ : G) * x⁻¹ := by
    calc x⁻¹ * (S.σ₁ : G) = x⁻¹ * ((S.σ₁ : G) * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * (S.σ₁ : G)) * x⁻¹ := by rw [hxs]
      _ = (S.σ₁ : G) * x⁻¹ := by group
  have hcomm : ∀ y ∈ S.Yg, x * y = y * x := by
    intro y hy
    have hyC : y ∈ S.Cg1 := hy.2
    have hys : y * (S.σ₁ : G) = (S.σ₁ : G) * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
    have h1 : y * x⁻¹ * y⁻¹ ∈ S.Vg := S.conj_mem_Vg hyC (S.Vg.inv_mem hxV)
    have h2 : x * y * x⁻¹ * y⁻¹ ∈ S.Vg := by
      have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
      rw [e]
      exact S.Vg.mul_mem hxV h1
    have hxyx : x * y * x⁻¹ ∈ S.Yg := by
      refine ⟨conj_mem_Uz (x := (⟨x, hxH⟩ : ↥(Hz z))) hy.1,
        Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc x * y * x⁻¹ * (S.σ₁ : G) = x * y * (x⁻¹ * (S.σ₁ : G)) := by group
        _ = x * y * ((S.σ₁ : G) * x⁻¹) := by rw [hxs']
        _ = x * (y * (S.σ₁ : G)) * x⁻¹ := by group
        _ = x * ((S.σ₁ : G) * y) * x⁻¹ := by rw [hys]
        _ = (x * (S.σ₁ : G)) * y * x⁻¹ := by group
        _ = ((S.σ₁ : G) * x) * y * x⁻¹ := by rw [hxs]
        _ = (S.σ₁ : G) * (x * y * x⁻¹) := by group
    have h3 : x * y * x⁻¹ * y⁻¹ ∈ S.Yg := S.Yg.mul_mem hxyx (S.Yg.inv_mem hy)
    have h4 : x * y * x⁻¹ * y⁻¹ = 1 := S.Vg_inf_Yg hAU h2 h3
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [h4, one_mul]
  have hconj : ∀ y ∈ S.Yg, (r : G) * y * (r : G)⁻¹ = (k : G)⁻¹ * y * k := by
    intro y hy
    have hy' : (k : G)⁻¹ * y * k ∈ S.Yg := S.Yg.mul_mem (S.Yg.mul_mem (S.Yg.inv_mem hk) hy) hk
    have hc := hcomm _ hy'
    have hrx : (r : G) = x * (k : G)⁻¹ := by
      rw [hx_eq]
      group
    calc (r : G) * y * (r : G)⁻¹ = x * ((k : G)⁻¹ * y * k) * x⁻¹ := by
          rw [hrx]
          group
      _ = (k : G)⁻¹ * y * k := by rw [hc]; group
  have hk2 : ∀ y ∈ S.Yg, y * ((k : G) * k) = ((k : G) * k) * y := by
    intro y hy
    have hsq : (k : G) * k = 1 ∨ (k : G) * k = z := by
      rcases S.hyp.sq_cases ⟨(k : G), hk.1⟩ with ⟨-, h⟩ | ⟨-, h⟩
      · left
        rw [← pow_two]
        exact h
      · right
        rw [← pow_two]
        exact h
    rcases hsq with h | h
    · rw [h]
      simp
    · rw [h]
      exact z_comm_H (⟨y, Uz_le_Hz z hy.1⟩ : ↥(Hz z))
  have hr3 : (r : G) * r * r = 1 := by
    have := congrArg Subtype.val (S.hR.pow_three hr)
    rw [← pow_three']
    simpa using this
  have hcommA : (r : G) * ((S.a₂ : ↥(Hz z)) : G) = ((S.a₂ : ↥(Hz z)) : G) * (r : G) := by
    set a : G := ((S.a₂ : ↥(Hz z)) : G) with ha
    have haY : a ∈ S.Yg := ⟨S.a₂_mem_U hAU, S.a₂_mem_Cg1⟩
    have hy1 : (k : G)⁻¹ * a * k ∈ S.Yg :=
      S.Yg.mul_mem (S.Yg.mul_mem (S.Yg.inv_mem hk) haY) hk
    have h2 : (r : G) * ((r : G) * a * (r : G)⁻¹) * (r : G)⁻¹ = a := by
      rw [hconj a haY, hconj _ hy1]
      have hc2 := hk2 a haY
      calc (k : G)⁻¹ * ((k : G)⁻¹ * a * k) * k = ((k : G) * k)⁻¹ * (a * ((k : G) * k)) := by
            group
        _ = ((k : G) * k)⁻¹ * (((k : G) * k) * a) := by rw [hc2]
        _ = a := by group
    have h3 : (r : G) * ((r : G) * ((r : G) * a * (r : G)⁻¹) * (r : G)⁻¹) * (r : G)⁻¹ = a := by
      calc (r : G) * ((r : G) * ((r : G) * a * (r : G)⁻¹) * (r : G)⁻¹) * (r : G)⁻¹
          = ((r : G) * r * r) * a * ((r : G) * r * r)⁻¹ := by group
        _ = a := by rw [hr3]; group
    rw [h2] at h3
    calc (r : G) * a = ((r : G) * a * (r : G)⁻¹) * (r : G) := by group
      _ = a * (r : G) := by rw [h3]
  have hrσ : r ∈ Subgroup.zpowers S.σ₁ :=
    S.mem_zpowers_σ₁_of_comm_a₂ hr (Subtype.ext hcommA)
  have hrG : (r : G) ∈ Subgroup.zpowers (S.σ₁ : G) := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hrσ
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
    rw [← hm]
    simp
  have hrV : (r : G) ∈ S.Vg := (Subgroup.zpowers_le.mpr S.σ₁_mem_Vg) hrG
  have hkV : (k : G) ∈ S.Vg := by
    have := S.Vg.mul_mem (S.Vg.inv_mem hrV) hxV
    rw [hx_eq] at this
    simpa using this
  have hk1 : (k : G) = 1 := S.Vg_inf_Yg hAU hkV hk
  rw [hx_eq, hk1, mul_one]
  exact hrG

theorem σ₂_not_mem_Vg (hAU : (S.A : G) ∈ Uz z) : ((S.σ₂ : ↥(Hz z)) : G) ∉ S.Vg := by
  intro h
  have hH : ((S.σ₂ : ↥(Hz z)) : G) ∈ Hz z := (S.σ₂ : ↥(Hz z)).2
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (S.Vg_inf_Hz hAU h hH)
  have hmem : S.σ₂ ∈ Subgroup.zpowers S.σ₁ :=
    Subgroup.mem_zpowers_iff.mpr ⟨m, Subtype.ext (by simpa using hm)⟩
  rcases mem_zpowers_of_pow_three S.jw.r1 hmem with h1 | h1 | h1
  · exact S.σ₂_ne_one h1
  · exact S.σ₂_ne_σ₁ h1
  · exact S.σ₂_ne_σ₁_inv h1

end JWSetup

end CFSG.Quasithin.H13.U43
