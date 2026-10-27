module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType

namespace E6Dep

namespace ZL

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

theorem ggAut_eq_one_or_isTransvection {Bs : Subgroup G} {y : G} (hyBs : y ∈ Bs) (hy1 : y ≠ 1)
    (hBs : CFSG.Open.IsElemAbelian 3 Bs) {ψ : MulAut ↥Bs}
    (hψy : ψ ⟨y, hyBs⟩ = ⟨y, hyBs⟩)
    (hψ : ∀ b : ↥Bs, ((b⁻¹ * ψ b : ↥Bs) : G) ∈ Subgroup.zpowers y) :
    ψ = 1 ∨ GGIsTransvection 3 ψ := by
  classical
  haveI : IsMulCommutative ↥Bs := hBs.1
  let c : ↥Bs := ⟨y, hyBs⟩
  have hψc : ψ c = c := by simpa only [c] using hψy
  have hc3 : c ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    change (y : G) ^ 3 = 1
    exact hBs.2 y hyBs
  have hc1 : c ≠ 1 := by
    intro h
    exact hy1 (by simpa [c] using congrArg Subtype.val h)
  have hc_ord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  let D : ↥Bs →* ↥Bs :=
    { toFun := fun b => b⁻¹ * ψ b
      map_one' := by simp
      map_mul' := by
        intro a b
        show (a * b)⁻¹ * ψ (a * b) = (a⁻¹ * ψ a) * (b⁻¹ * ψ b)
        rw [map_mul, mul_inv_rev]
        ac_rfl }
  have hD_apply : ∀ b : ↥Bs, D b = b⁻¹ * ψ b := fun b => rfl
  have hfix : ∀ b : ↥Bs, ψ (b⁻¹ * ψ b) = b⁻¹ * ψ b := by
    intro b
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hψ b)
    have hck : c ^ k = b⁻¹ * ψ b := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      change (y : G) ^ k = ((b⁻¹ * ψ b : ↥Bs) : G)
      exact hk
    calc ψ (b⁻¹ * ψ b) = ψ (c ^ k) := by rw [hck]
      _ = (ψ c) ^ k := map_zpow ψ c k
      _ = c ^ k := by rw [hψc]
      _ = b⁻¹ * ψ b := hck
  have hD_ker : Nat.card {b : ↥Bs // ψ b = b} = Nat.card D.ker := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight (fun b => ?_)
    show ψ b = b ↔ b ∈ D.ker
    rw [MonoidHom.mem_ker, hD_apply]
    exact eq_comm.trans inv_mul_eq_one.symm
  have hD_range_le : D.range ≤ Subgroup.zpowers c := by
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_zpowers_iff]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hψ b)
    refine ⟨k, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_zpow]
    change (y : G) ^ k = ((b⁻¹ * ψ b : ↥Bs) : G)
    exact hk
  have hcard_zp : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers, hc_ord]
  have hcardD : Nat.card D.ker * Nat.card D.range = Nat.card ↥Bs :=
    Subgroup.card_ker_mul_card_range D
  have hdvd : Nat.card D.range ∣ 3 := by
    have h := Subgroup.card_dvd_of_le hD_range_le
    rwa [hcard_zp] at h
  by_cases hψ1 : ψ = 1
  · exact Or.inl hψ1
  · right
    refine ⟨?_, hfix⟩
    rw [hD_ker]
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three (Nat.card D.range) hdvd with h1 | h3
    · exfalso
      have hbot : D.range = ⊥ := Subgroup.eq_bot_of_card_eq D.range h1
      have hD1 : D = 1 := by
        ext b
        have hmem : D b ∈ D.range := MonoidHom.mem_range.mpr ⟨b, rfl⟩
        rw [hbot] at hmem
        simpa using hmem
      apply hψ1
      ext b
      have hb : D b = 1 := by rw [hD1]; rfl
      have hb' : b⁻¹ * ψ b = 1 := by rw [← hD_apply]; exact hb
      exact congrArg Subtype.val (inv_mul_eq_one.mp hb').symm
    · rw [h3] at hcardD
      exact hcardD

end ZL

end E6Dep

end CFSG.StandardType

end
