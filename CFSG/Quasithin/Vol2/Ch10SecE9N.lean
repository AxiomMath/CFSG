module

public import CFSG.Quasithin.Vol2.Ch10SecBSetup
public import CFSG.Quasithin.Vol2.Ch10SecBXi
public import CFSG.Quasithin.Vol2.Ch10SecE9I

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {t : G}
  {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {c : L32.Γ}

theorem isU_pow_eight : ∀ g : L32.Γ, L32.IsU g → g ^ 8 = 1 := by
  decide +kernel

theorem not_mem_sup_of_orderOf_three (h : MaxCtx T L I t Ψ c) {y : G} (hy3 : orderOf y = 3)
    (hyT : y ∈ Subgroup.normalizer (T1 T L : Set G)) : y ∉ fsuL0 T L ⊔ T := by
  intro hyLT
  have hloc := h.hyp.fsu.maximal.1
  have hT2 : IsPGroup 2 T := h.hyp.fsu.sylow.1
  have hTL0 : T ≤ Subgroup.normalizer (fsuL0 T L : Set G) := le_fsuM T L
  have hyO : y ∈ oTwoUpper (fsuL0 T L ⊔ T) :=
    mem_oTwoUpper_of_odd hyLT (by rw [hy3]; decide)
  rw [oTwoUpper_sup_eq hT2 hTL0] at hyO
  have hyL : y ∈ fsuL0 T L := oTwoUpper_le _ hyO
  have hT0 : ∀ x ∈ T0 T L, y * x * y⁻¹ ∈ T0 T L := by
    intro x hx
    have hx1 : x ∈ T1 T L := SecA.T0_le_T1 hloc hx
    have h1 : y * x * y⁻¹ ∈ T1 T L := (Subgroup.mem_normalizer_iff.mp hyT x).mp hx1
    have h2 : y * x * y⁻¹ ∈ fsuL0 T L :=
      (fsuL0 T L).mul_mem ((fsuL0 T L).mul_mem hyL hx.2) ((fsuL0 T L).inv_mem hyL)
    exact ⟨h1.1, h2⟩
  have hT0img := h.hC.T0
  have hU : ∀ u : L32.Γ × L32.Γ, u ∈ L32.U3.prod L32.U3 →
      Ψ ⟨y, hyL⟩ * u * (Ψ ⟨y, hyL⟩)⁻¹ ∈ L32.U3.prod L32.U3 := by
    intro u hu
    rw [← hT0img] at hu ⊢
    obtain ⟨⟨x, hxL⟩, hx, rfl⟩ := hu
    have hx' := hT0 x (Subgroup.mem_subgroupOf.mp hx)
    refine ⟨⟨y * x * y⁻¹, hx'.2⟩, hx', ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hy1 : L32.IsU (Ψ ⟨y, hyL⟩).1 := by
    refine L32.isU_of_normalizes _ fun u hu => ?_
    have := hU (u, 1) ⟨hu, L32.U3.one_mem⟩
    have h1 : (Ψ ⟨y, hyL⟩).1 * u * ((Ψ ⟨y, hyL⟩).1)⁻¹ ∈ L32.U3 := by simpa using this.1
    exact h1
  have hy2 : L32.IsU (Ψ ⟨y, hyL⟩).2 := by
    refine L32.isU_of_normalizes _ fun u hu => ?_
    have := hU (1, u) ⟨L32.U3.one_mem, hu⟩
    have h1 : (Ψ ⟨y, hyL⟩).2 * u * ((Ψ ⟨y, hyL⟩).2)⁻¹ ∈ L32.U3 := by simpa using this.2
    exact h1
  have hΨ3 : Ψ ⟨y, hyL⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨y, hyL⟩ : ↥(fsuL0 T L)) ^ 3 = 1 := Subtype.ext (by simp [← hy3, pow_orderOf_eq_one])
    rw [this, map_one]
  have hΨ8 : Ψ ⟨y, hyL⟩ ^ 8 = 1 :=
    Prod.ext (by simpa using isU_pow_eight _ hy1)
      (by simpa using isU_pow_eight _ hy2)
  have hΨ1 : Ψ ⟨y, hyL⟩ = 1 := by
    have e : Ψ ⟨y, hyL⟩ = (Ψ ⟨y, hyL⟩ ^ 3) ^ 3 * (Ψ ⟨y, hyL⟩ ^ 8)⁻¹ := by group
    rw [e, hΨ3, hΨ8]; group
  have hyO2 : y ∈ pCoreOf 2 (fsuL0 T L) := (h.hC.ker ⟨y, hyL⟩).mp hΨ1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (fsuL0 T L)) ⟨y, hyO2⟩
  have hk' : y ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h3 : 3 ∣ 2 ^ k := hy3 ▸ orderOf_dvd_of_pow_eq_one hk'
  exact absurd ((Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)) (by decide)

end CFSG.Quasithin.Vol2.Ch10.SecB.E9
