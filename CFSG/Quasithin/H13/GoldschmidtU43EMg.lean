module

public import CFSG.Quasithin.H13.GoldschmidtU43ESyl2

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable {z : G} (S : JWSetup z)
include S

theorem conj_mem_Cg {g : G} (hg : g ∈ Subgroup.normalizer (S.Tg : Set G)) {x : G}
    (hx : x ∈ S.Cg) : g * x * g⁻¹ ∈ S.Cg := by
  rw [S.mem_Cg]
  intro t ht
  have ht' : g⁻¹ * t * g ∈ S.Tg := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (S.Tg : Set G)).inv_mem hg) t).mp
      ht
    simpa using this
  have hc := (S.mem_Cg).1 hx _ ht'
  calc t * (g * x * g⁻¹) = g * ((g⁻¹ * t * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * t * g)) * g⁻¹ := by rw [hc]
    _ = (g * x * g⁻¹) * t := by group

theorem normalizer_Tg {n : ↥(Hz z)} (hn : n ∈ Subgroup.normalizer (S.R : Set ↥(Hz z))) :
    (n : G) ∈ Subgroup.normalizer (S.Tg : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨r, hr, rfl⟩ := (S.mem_Tg).1 hh
    exact S.coe_mem_Tg ((Subgroup.mem_normalizer_iff.mp hn r).mp hr)
  · intro hh
    obtain ⟨s, hs, hsh⟩ := (S.mem_Tg).1 hh
    have hs' : n⁻¹ * s * n ∈ S.R := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (S.R : Set ↥(Hz z))).inv_mem hn)
        s).mp hs
      simpa using this
    have e : h = ((n⁻¹ * s * n : ↥(Hz z)) : G) := by
      have : (n : G) * h * (n : G)⁻¹ = (s : G) := hsh.symm
      calc h = (n : G)⁻¹ * ((n : G) * h * (n : G)⁻¹) * n := by group
        _ = ((n⁻¹ * s * n : ↥(Hz z)) : G) := by rw [this]; rfl
    rw [e]
    exact S.coe_mem_Tg hs'

theorem z_normalizer_Tg : z ∈ Subgroup.normalizer (S.Tg : Set G) := by
  have : (zK z : G) ∈ Subgroup.normalizer (S.Tg : Set G) :=
    S.normalizer_Tg (by
      rw [Subgroup.mem_normalizer_iff]
      intro r
      have e : zK z * r * (zK z)⁻¹ = r := by rw [zK_comm r]; group
      rw [e])
  exact this

end JWSetup

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)
include S

noncomputable def Mg : Subgroup G := Classical.choose S.exists_Mg

theorem Mg_le_Cg : S.Mg ≤ S.Cg := (Classical.choose_spec S.exists_Mg).1

theorem mem_Mg {x : G} : x ∈ S.Mg ↔ x ∈ S.Cg ∧ Odd (orderOf x) :=
  (Classical.choose_spec S.exists_Mg).2.1 x

theorem odd_card_Mg : Odd (Nat.card S.Mg) := (Classical.choose_spec S.exists_Mg).2.2.1

theorem Cg_cases {x : G} (hx : x ∈ S.Cg) : x ∈ S.Mg ∨ z * x ∈ S.Mg :=
  (Classical.choose_spec S.exists_Mg).2.2.2 x hx

theorem Tg_le_Mg : S.Tg ≤ S.Mg := by
  intro x hx
  refine (S.mem_Mg).2 ⟨S.Tg_le_Cg hx, ?_⟩
  exact Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one (S.pow_three_Tg hx))

theorem Mg_inf_Hz : S.Mg ⊓ Hz z = S.Tg := by
  apply le_antisymm
  · rintro x ⟨hxM, hxH⟩
    obtain ⟨hxC, hxodd⟩ := (S.mem_Mg).1 hxM
    obtain ⟨r, hr, h⟩ := S.cent_Hz hxC hxH
    rcases h with rfl | rfl
    · exact hr
    · exfalso
      have hzr : z * r = r * z := (z_comm_H (⟨r, S.Tg_le_Hz hr⟩ : ↥(Hz z))).symm
      have hr3 := S.pow_three_Tg hr
      have h3 : (z * r) ^ 3 = z := by
        rw [Commute.mul_pow hzr, hr3, mul_one]
        calc z ^ 3 = (z * z) * z := pow_three' z
          _ = z := by rw [S.z_sq, one_mul]
      have hdvd : orderOf z ∣ orderOf (z * r) := by
        apply orderOf_dvd_of_pow_eq_one
        calc z ^ orderOf (z * r) = ((z * r) ^ 3) ^ orderOf (z * r) := by rw [h3]
          _ = ((z * r) ^ orderOf (z * r)) ^ 3 := by rw [← pow_mul, ← pow_mul, mul_comm]
          _ = 1 := by rw [pow_orderOf_eq_one, one_pow]
      have hz2 : orderOf z = 2 :=
        orderOf_eq_prime (by rw [pow_two]; exact S.z_sq) S.hyp.z_ne_one
      rw [hz2] at hdvd
      exact absurd (Odd.of_dvd_nat hxodd hdvd) (by decide)
  · exact le_inf S.Tg_le_Mg S.Tg_le_Hz

theorem conj_mem_Mg {g : G} (hg : g ∈ Subgroup.normalizer (S.Tg : Set G)) {x : G}
    (hx : x ∈ S.Mg) : g * x * g⁻¹ ∈ S.Mg := by
  obtain ⟨hxC, hxodd⟩ := (S.mem_Mg).1 hx
  refine (S.mem_Mg).2 ⟨S.conj_mem_Cg hg hxC, ?_⟩
  have : orderOf (g * x * g⁻¹) = orderOf x := by
    have := (MulEquiv.orderOf_eq (MulAut.conj g) x)
    simpa using this
  rwa [this]

end JWSetup

end CFSG.Quasithin.H13.U43
