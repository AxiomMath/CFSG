module

public import CFSG.Quasithin.H13.GoldschmidtU43EQCV

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)

theorem Cg1_eq_mul (hAU : (S.A : G) ∈ Uz z) {g : G} (hg : g ∈ S.Cg1) :
    ∃ c ∈ S.Cg1, c ∈ Hz z ∧ ∃ v ∈ S.Vg, g = c * v := by
  obtain ⟨c, hc, k, hk, hgk⟩ := S.frattini_Cg1 hAU ⟨g, hg⟩
  refine ⟨(c : G), c.2, ?_, (k : G), ⟨k, hk, rfl⟩, congrArg Subtype.val hgk⟩
  have := Subgroup.mem_centralizer_singleton_iff.mp hc
  exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val this)

theorem Vg_comm_mem (hAU : (S.A : G) ∈ Uz z) :
    (∀ y ∈ S.Vg, z * y * z⁻¹ * y ∈ Subgroup.zpowers (S.σ₁ : G)) ∧
      ∀ x ∈ S.Vg, ∀ y ∈ S.Vg, x⁻¹ * y⁻¹ * x * y ∈ Subgroup.zpowers (S.σ₁ : G) := by
  set s : ↥S.Cg1 := ⟨(S.σ₁ : G), S.σ₁_mem_Cg1⟩ with hs
  set zC : ↥S.Cg1 := ⟨z, S.z_mem_Cg1⟩ with hzC
  have hcen : ∀ g : ↥S.Cg1, Commute g s := fun g =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  have hN : (Subgroup.zpowers s).Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hc : Commute g (s ^ k) := (hcen g).zpow_right k
    have e : g * s ^ k * g⁻¹ = s ^ k := by
      rw [hc.eq]
      group
    rw [e]
    exact hn⟩
  have hzz : zC * zC = 1 := Subtype.ext S.hyp.sq_z
  have hV : ∀ y ∈ CFSG.oddCore ↥S.Cg1, zC * y * zC⁻¹ ∈ CFSG.oddCore ↥S.Cg1 := fun y hy =>
    (inferInstance : (CFSG.oddCore ↥S.Cg1).Normal).conj_mem y hy zC
  have h3 : (S.σ₁ : G) ^ 3 = 1 := by
    have := congrArg Subtype.val S.jw.r1
    simpa using this
  have hs3 : s ^ 3 = 1 := Subtype.ext (by simpa using h3)
  have hs3' : s ^ (3 : ℤ) = 1 := by
    rw [zpow_ofNat]
    exact hs3
  have hf : ∀ y ∈ CFSG.oddCore ↥S.Cg1, zC * y * zC⁻¹ * y⁻¹ ∈ Subgroup.zpowers s →
      y ∈ Subgroup.zpowers s := by
    intro y hy hmem
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hszC : Commute zC s := hcen zC
    have e1 : zC * y * zC⁻¹ = s ^ i * y := by
      calc zC * y * zC⁻¹ = (zC * y * zC⁻¹ * y⁻¹) * y := by group
        _ = s ^ i * y := by rw [← hi]
    have e3 : zC * s ^ i * zC⁻¹ = s ^ i := by
      rw [(hszC.zpow_right i).eq]
      group
    have e2 : y = s ^ (2 * i) * y := by
      calc y = (zC * zC) * y * (zC * zC)⁻¹ := by rw [hzz]; group
        _ = zC * (zC * y * zC⁻¹) * zC⁻¹ := by group
        _ = zC * (s ^ i * y) * zC⁻¹ := by rw [e1]
        _ = (zC * s ^ i * zC⁻¹) * (zC * y * zC⁻¹) := by group
        _ = s ^ i * (s ^ i * y) := by rw [e3, e1]
        _ = s ^ (2 * i) * y := by group
    have hsi : s ^ (2 * i) = 1 := by
      have : s ^ (2 * i) * y = 1 * y := by
        rw [one_mul]
        exact e2.symm
      exact mul_right_cancel this
    have hsi1 : s ^ i = 1 := by
      calc s ^ i = s ^ (3 * i) * (s ^ (2 * i))⁻¹ := by group
        _ = 1 := by rw [hsi, zpow_mul, hs3', one_zpow]; simp
    rw [hsi1, one_mul] at e1
    have hyc : zC * y = y * zC := by
      calc zC * y = (zC * y * zC⁻¹) * zC := by group
        _ = y * zC := by rw [e1]
    have hvV : (y : G) ∈ S.Vg := S.mem_Vg.mpr ⟨y.2, hy⟩
    have hvH : (y : G) ∈ Hz z := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (congrArg Subtype.val hyc).symm
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (S.Vg_inf_Hz hAU hvV hvH)
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, Subtype.ext (by simpa using hm)⟩
  have key := u43_commutator_mem (Subgroup.zpowers s) (CFSG.oddCore ↥S.Cg1) (z := zC) hzz hV hf
  refine ⟨fun y hy => ?_, fun x hx y hy => ?_⟩
  · obtain ⟨hyC, hy'⟩ := S.mem_Vg.mp hy
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (key.1 ⟨y, hyC⟩ hy')
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
    have := congrArg Subtype.val hm
    simpa using this
  · obtain ⟨hxC, hx'⟩ := S.mem_Vg.mp hx
    obtain ⟨hyC, hy'⟩ := S.mem_Vg.mp hy
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (key.2 ⟨x, hxC⟩ hx' ⟨y, hyC⟩ hy')
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
    have := congrArg Subtype.val hm
    simpa using this

end JWSetup

end CFSG.Quasithin.H13.U43
