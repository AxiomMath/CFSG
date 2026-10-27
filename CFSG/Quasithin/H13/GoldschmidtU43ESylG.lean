module

public import CFSG.Quasithin.H13.GoldschmidtU43EMg

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

open scoped Pointwise in
theorem exists_conj_sylow [Finite G] {p : ℕ} [Fact p.Prime] (P Q : Sylow p G) :
    ∃ g : G, ∀ x, x ∈ (Q : Subgroup G) ↔ g⁻¹ * x * g ∈ (P : Subgroup G) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  refine ⟨g, fun x => ?_⟩
  have h1 : (Q : Set G) = MulAut.conj g • ((P : Subgroup G) : Set G) := by
    rw [← hg, Sylow.coe_smul]
    rfl
  have hQ : x ∈ (Q : Subgroup G) ↔ x ∈ (Q : Set G) := Iff.rfl
  rw [hQ, h1, Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : g⁻¹ * (MulAut.conj g • y) * g = y := by
      simp [MulAut.smul_def, MulAut.conj_apply]
      group
    rw [this]
    exact hy
  · intro h
    refine ⟨g⁻¹ * x * g, h, ?_⟩
    simp [MulAut.smul_def, MulAut.conj_apply]
    group

theorem card_sylow_three_of_card {H : Type} [Group H] [Finite H] (hH : Nat.card H = 5760)
    (P : Sylow 3 H) : Nat.card P = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Sylow.card_eq_multiplicity, hH, Nat.factorization_def _ Nat.prime_three,
    show (5760 : ℕ) = 3 ^ 2 * 640 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  norm_num

namespace JWSetup

variable {z : G} (S : JWSetup z)
include S

theorem mem_R_iff {r : ↥(Hz z)} : r ∈ S.R ↔ (r : G) ∈ S.Tg := by
  constructor
  · exact S.coe_mem_Tg
  · intro h
    obtain ⟨r', hr', e⟩ := (S.mem_Tg).1 h
    have : r' = r := Subtype.ext e
    rwa [← this]

theorem mem_normalizer_R_of {n : ↥(Hz z)}
    (hn : (n : G) ∈ Subgroup.normalizer (S.Tg : Set G)) :
    n ∈ Subgroup.normalizer (S.R : Set ↥(Hz z)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro r
  rw [S.mem_R_iff, S.mem_R_iff]
  exact (Subgroup.mem_normalizer_iff.mp hn (r : G))

variable [Finite G]

theorem sq_mem_Cg {n : G} (hn : n ∈ Subgroup.normalizer (S.Tg : Set G)) (hH : n ∈ Hz z) :
    n * n ∈ S.Cg := by
  obtain ⟨r, hr, h⟩ := S.sq_mem (S.mem_normalizer_R_of (n := ⟨n, hH⟩) hn)
  have hrC : (r : G) ∈ S.Cg := S.Tg_le_Cg (S.coe_mem_Tg hr)
  rcases h with h | h
  · have : n * n = (r : G) := congrArg Subtype.val h
    rw [this]
    exact hrC
  · have : n * n = z * (r : G) := congrArg Subtype.val h
    rw [this]
    exact mul_mem S.z_mem_Cg hrC

section NineCase

variable (h9 : Nat.card S.Mg = 9)
include h9

theorem Tg_eq_Mg : S.Tg = S.Mg :=
  Subgroup.eq_of_le_of_card_ge S.Tg_le_Mg (by rw [h9, S.card_Tg])

theorem Cg_cases_Tg {x : G} (hx : x ∈ S.Cg) : x ∈ S.Tg ∨ z * x ∈ S.Tg := by
  rw [S.Tg_eq_Mg h9]
  exact S.Cg_cases hx

theorem involution_Cg {x : G} (hx : x ∈ S.Cg) (hx2 : x * x = 1) : x = 1 ∨ x = z := by
  have key : ∀ t ∈ S.Tg, t * t = 1 → t = 1 := by
    intro t ht h2
    have h3 : t ^ 3 = 1 := S.pow_three_Tg ht
    calc t = t ^ 3 * (t * t)⁻¹ := by rw [pow_three', ← pow_three']; group
      _ = 1 := by rw [h3, h2]; simp
  rcases S.Cg_cases_Tg h9 hx with h | h
  · left
    exact key x h hx2
  · right
    have hzt : z * (z * x) = (z * x) * z :=
      (z_comm_H (⟨z * x, S.Tg_le_Hz h⟩ : ↥(Hz z))).symm
    have hzzx : z * x = x * z := by
      have := S.z_sq
      calc z * x = z * (z * (z * x)) := by rw [← mul_assoc, this, one_mul]
        _ = z * ((z * x) * z) := by rw [hzt]
        _ = (z * z) * (x * z) := by group
        _ = x * z := by rw [this, one_mul]
    have h2 : (z * x) * (z * x) = 1 := by
      calc (z * x) * (z * x) = z * x * (x * z) := by rw [← hzzx]
        _ = z * (x * x) * z := by group
        _ = 1 := by rw [hx2, mul_one, S.z_sq]
    have := key _ h h2
    calc x = z⁻¹ * (z * x) := by group
      _ = z := by rw [this, mul_one, inv_eq_of_mul_eq_one_right S.z_sq]

theorem normalizer_Tg_le_Hz {g : G} (hg : g ∈ Subgroup.normalizer (S.Tg : Set G)) :
    g ∈ Hz z := by
  have hC := S.conj_mem_Cg hg S.z_mem_Cg
  have h2 : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
    calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [S.z_sq]; group
  rcases S.involution_Cg h9 hC h2 with h | h
  · exfalso
    apply S.hyp.z_ne_one
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [h]

theorem exists_sylow_Tg : ∃ P : Sylow 3 G, (P : Subgroup G) = S.Tg := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT3 : IsPGroup 3 S.Tg := IsPGroup.of_card (n := 2) (by rw [S.card_Tg]; norm_num)
  obtain ⟨P, hP⟩ := hT3.exists_le_sylow
  refine ⟨P, le_antisymm ?_ hP⟩
  by_contra hnot
  have hIlt : S.Tg.subgroupOf (P : Subgroup G) < ⊤ := by
    refine lt_top_iff_ne_top.mpr (fun htop => hnot ?_)
    intro y hy
    have : (⟨y, hy⟩ : ↥(P : Subgroup G)) ∈ S.Tg.subgroupOf (P : Subgroup G) := by
      rw [htop]
      trivial
    exact this
  have : Group.IsNilpotent ↥(P : Subgroup G) := P.isPGroup'.isNilpotent
  have hnc : NormalizerCondition ↥(P : Subgroup G) :=
    Group.normalizerCondition_of_isNilpotent (G := ↥(P : Subgroup G))
  obtain ⟨x, hxN, hxn⟩ := IsConcreteLE.exists_of_lt (hnc _ hIlt)
  have hxNorm : (x : G) ∈ Subgroup.normalizer (S.Tg : Set G) := by
    have : x ∈ (Subgroup.normalizer (S.Tg : Set G)).subgroupOf (P : Subgroup G) := by
      rw [Subgroup.subgroupOf_normalizer_eq hP]
      exact hxN
    exact Subgroup.mem_subgroupOf.mp this
  have hxT : (x : G) ∉ S.Tg := fun hx => hxn (Subgroup.mem_subgroupOf.mpr hx)
  have hxH : (x : G) ∈ Hz z := S.normalizer_Tg_le_Hz h9 hxNorm
  set Q : Subgroup G := S.Tg ⊔ Subgroup.zpowers (x : G) with hQ
  have hQP : Q ≤ (P : Subgroup G) := sup_le hP (Subgroup.zpowers_le.mpr x.2)
  have hQ3 : IsPGroup 3 Q := P.isPGroup'.to_le hQP
  have hQH : Q ≤ Hz z := sup_le S.Tg_le_Hz (Subgroup.zpowers_le.mpr hxH)
  have hdvd : Nat.card Q ∣ 1152 := S.hyp.card_H ▸ Subgroup.card_dvd_of_le hQH
  obtain ⟨k, hk⟩ := hQ3.exists_card_eq
  have hk2 : k ≤ 2 := by
    by_contra hk3
    have h27 : 27 ∣ 3 ^ k := by
      have := Nat.pow_dvd_pow 3 (show 3 ≤ k by omega)
      simpa using this
    rw [hk] at hdvd
    have := h27.trans hdvd
    omega
  have hle : Nat.card Q ≤ 9 := by
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 9 := by norm_num
  have hTQ : S.Tg ≤ Q := le_sup_left
  have heq : S.Tg = Q := Subgroup.eq_of_le_of_card_ge hTQ (by rw [S.card_Tg]; exact hle)
  exact hxT (heq ▸ (le_sup_right : Subgroup.zpowers (x : G) ≤ Q) (Subgroup.mem_zpowers _))

end NineCase

end JWSetup

end CFSG.Quasithin.H13.U43
