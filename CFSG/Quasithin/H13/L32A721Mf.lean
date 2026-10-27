module

public import CFSG.Quasithin.H13.L32A721Me

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (E : Ctx7153 G T L V (hz T V))
include E

omit [Finite G] E in
theorem conj_upsilon_sq {Γ : Type*} [Group Γ] {R : Subgroup Γ} {υ : Γ} (hυR : υ ∈ R)
    (hυ2 : υ ^ 2 ≠ 1) (hυ4 : υ ^ 4 = 1) (huniq : ∀ r ∈ R, r ^ 2 = 1 → r ≠ 1 → r = υ ^ 2)
    {g : Γ} (hg : g ∈ Subgroup.normalizer (R : Set Γ)) : g * υ ^ 2 * g⁻¹ = υ ^ 2 := by
  refine huniq _ ((Subgroup.mem_normalizer_iff.mp hg _).mp (R.pow_mem hυR 2)) ?_ ?_
  · rw [conj_pow, ← pow_mul, hυ4, mul_one, mul_inv_cancel]
  · intro h1
    apply hυ2
    calc υ ^ 2 = g⁻¹ * (g * υ ^ 2 * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group

theorem mem_l1bar_of_mem_kbar (hO : pCoreOf 2 (mK T V) = pCoreOf 2 (hz T V))
    {g : ↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)} (hgK : g ∈ modO2Image (mK T V) (kz T V))
    (hg : g ∈ Subgroup.normalizer
      ((modO2Image (mK T V) (pCoreOf 2 (l1 T L V ⊔ T)) :
        Subgroup (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) :
          Set (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)))) :
    g ∈ modO2Image (mK T V) (l1 T L V) := by
  obtain ⟨υ, hυR, hυ2, hυ4, huniq, hinv⟩ := E.exists_upsilon hO
  have hX := E.isPOnePlusTwo_kbar
  have hc := conj_upsilon_sq hυR hυ2 hυ4 huniq hg
  have h1 := hinv g hgK
  have hcomm : υ ^ 2 * g * (υ ^ 2)⁻¹ = g := by
    calc υ ^ 2 * g * (υ ^ 2)⁻¹ = (g * υ ^ 2 * g⁻¹) * g * (υ ^ 2)⁻¹ := by rw [hc]
      _ = g := by group
  rw [hcomm, ← E.center_kbar_eq hO] at h1
  rw [← E.center_kbar_eq hO]
  obtain ⟨z, hz, hze⟩ := h1
  have hsq : (⟨g, hgK⟩ : ↥(modO2Image (mK T V) (kz T V))) ^ 2 ∈
      Subgroup.center ↥(modO2Image (mK T V) (kz T V)) := by
    have e : (⟨g, hgK⟩ : ↥(modO2Image (mK T V) (kz T V))) ^ 2 = z :=
      Subtype.ext (by rw [Subgroup.coe_pow, sq, ← hze]; rfl)
    rw [e]
    exact hz
  exact ⟨_, Heis.mem_center_of_sq hX hsq, rfl⟩

theorem mem_l1bar_of_pow_three (hO : pCoreOf 2 (mK T V) = pCoreOf 2 (hz T V))
    {g : ↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)}
    (hg : g ∈ Subgroup.normalizer
      ((modO2Image (mK T V) (pCoreOf 2 (l1 T L V ⊔ T)) :
        Subgroup (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) :
          Set (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))))
    (hg3 : g ^ 3 = 1) : g ∈ modO2Image (mK T V) (l1 T L V) := by
  by_cases hgK : g ∈ modO2Image (mK T V) (kz T V)
  · exact E.mem_l1bar_of_mem_kbar hO hgK hg
  exfalso
  obtain ⟨υ, hυR, hυ2, hυ4, huniq, hinv⟩ := E.exists_upsilon hO
  have hX := E.isPOnePlusTwo_kbar
  have : (modO2Image (mK T V) (kz T V)).Normal := kbar_normal
  set X := modO2Image (mK T V) (kz T V) with hXdef
  have hc := conj_upsilon_sq hυR hυ2 hυ4 huniq hg
  have hυC : υ ∈ Subgroup.centralizer (modO2Image (mK T V) (l1 T L V) :
      Set (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) := by
    rw [E.r1bar_eq hO] at hυR
    exact (Subgroup.mem_inf.mp hυR).2
  set φ : MulAut ↥X := MulAut.conjNormal (υ ^ 2) with hφ
  set ψ : MulAut ↥X := MulAut.conjNormal g with hψ
  have hφZ : ∀ z ∈ Subgroup.center ↥X, φ z = z := by
    intro z hz
    have hzL : (z : ↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)) ∈ modO2Image (mK T V) (l1 T L V) := by
      rw [← E.center_kbar_eq hO]
      exact ⟨z, hz, rfl⟩
    apply Subtype.ext
    rw [hφ, MulAut.conjNormal_apply]
    have e := Subgroup.mem_centralizer_iff.mp (Subgroup.pow_mem _ hυC 2) _ hzL
    rw [← e, mul_inv_cancel_right]
  have hφinv : ∀ x : ↥X, φ x * x ∈ Subgroup.center ↥X := by
    intro x
    have h1 := hinv x x.2
    rw [← E.center_kbar_eq hO] at h1
    obtain ⟨w, hw, hwe⟩ := h1
    have e : φ x * x = w := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, hφ, MulAut.conjNormal_apply, ← hwe]
      rfl
    rw [e]
    exact hw
  have hψ3 : ψ ^ 3 ^ 1 = 1 := by rw [pow_one, hψ, ← map_pow, hg3, map_one]
  have hcomm : ∀ x, φ (ψ x) = ψ (φ x) := by
    intro x
    apply Subtype.ext
    simp only [hφ, hψ, MulAut.conjNormal_apply]
    have e : υ ^ 2 * g = g * υ ^ 2 := by
      calc υ ^ 2 * g = (g * υ ^ 2 * g⁻¹) * g := by rw [hc]
        _ = g * υ ^ 2 := by group
    calc υ ^ 2 * (g * (x : ↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)) * g⁻¹) * (υ ^ 2)⁻¹ =
        (υ ^ 2 * g) * x * (υ ^ 2 * g)⁻¹ := by group
      _ = (g * υ ^ 2) * x * (g * υ ^ 2)⁻¹ := by rw [e]
      _ = g * (υ ^ 2 * x * (υ ^ 2)⁻¹) * g⁻¹ := by group
  obtain ⟨a, haZ, hψa⟩ := Heis.exists_fixed_of_comm hX hφZ hφinv hψ3 hcomm
  obtain ⟨c₀, hc₀Z, hc₀1⟩ := Heis.exists_center_ne_one hX
  have ha3 : (a : ↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, Heis.pow_three_eq hX, Subgroup.coe_one]
  have hc3 : (c₀ : ↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, Heis.pow_three_eq hX, Subgroup.coe_one]
  have hga : g * a = a * g := by
    have e := congrArg Subtype.val hψa
    rw [hψ, MulAut.conjNormal_apply] at e
    calc g * (a : ↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)) = g * a * g⁻¹ * g := by group
      _ = a * g := by rw [e]
  have hgc : g * c₀ = c₀ * g := by
    have e : g * (c₀ : ↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)) * g⁻¹ = c₀ :=
      conj_center_of_pow_odd hX (by decide : Odd 3) hg3 ⟨c₀, hc₀Z, rfl⟩
    calc g * (c₀ : ↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)) = g * c₀ * g⁻¹ * g := by group
      _ = c₀ * g := by rw [e]
  have hac : (a : ↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)) * c₀ = c₀ * a :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hc₀Z a)
  have hg2 : g ^ 2 ∉ X := fun h2 => hgK (by
    have e : g = (g ^ 2) ^ 2 := by
      rw [← pow_mul]
      calc g = g ^ 3 * g := by rw [hg3, one_mul]
        _ = g ^ (2 * 2) := by rw [← pow_succ]
    rw [e]
    exact X.pow_mem h2 2)
  refine absurd (three_le_pRank hg3 ha3 hc3 hga hgc hac ?_) (by have := E.pRank_gamma_le; omega)
  intro i j l hi hj hl h
  have hgi : g ^ i ∈ X := by
    have e : g ^ i = ((a ^ j * c₀ ^ l)⁻¹ : ↥X) := by
      rw [Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]
      calc g ^ i = g ^ i * (a : ↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)) ^ j *
            (c₀ : ↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)) ^ l *
            ((c₀ : ↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)) ^ l)⁻¹ *
            ((a : ↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)) ^ j)⁻¹ := by group
        _ = ((a : ↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)) ^ j *
            (c₀ : ↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)) ^ l)⁻¹ := by rw [h]; group
    rw [e]
    exact Subtype.coe_prop _
  have hi0 : i = 0 := by
    interval_cases i
    · rfl
    · exact (hgK (by rw [← pow_one g]; exact hgi)).elim
    · exact (hg2 hgi).elim
  subst hi0
  rw [pow_zero, one_mul] at h
  have hacZ : a ^ j ∈ Subgroup.center ↥X := by
    have e : a ^ j = (c₀ ^ l)⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_inv, Subgroup.coe_pow]
      exact eq_inv_of_mul_eq_one_left h
    rw [e]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hc₀Z l)
  have hj0 : j = 0 := by
    interval_cases j
    · rfl
    · exact (haZ (by simpa using hacZ)).elim
    · exact (haZ (Heis.mem_center_of_sq hX hacZ)).elim
  subst hj0
  rw [pow_zero, one_mul] at h
  refine ⟨rfl, rfl, ?_⟩
  interval_cases l
  · rfl
  · exact (hc₀1 (Subtype.ext (by simpa using h))).elim
  · exfalso
    apply hc₀1
    apply Subtype.ext
    have e : (c₀ : ↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)) =
        (c₀ : ↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)) ^ 3 *
          ((c₀ : ↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)) ^ 2)⁻¹ := by group
    rw [e, hc3, h]
    simp

end Ctx7153

end CFSG.Quasithin.H13.L32A
