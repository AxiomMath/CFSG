module

public import CFSG.Quasithin.Recognition.RuTypeJ42

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped MatrixGroups

namespace SL3

@[expose] def zP0 : SL(3, ZMod 2) := ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by decide⟩

@[expose] def x0 : SL(3, ZMod 2) := ⟨!![0, 1, 0; 1, 1, 0; 0, 0, 1], by decide⟩

theorem zP0_mem_R0 : zP0 ∈ R0 := by decide

theorem zP0_mem_R2m : zP0 ∈ R2m := by decide

theorem zP0_ne_one : zP0 ≠ 1 := by decide

theorem x0_mem_Pl : x0 ∈ Pl := by decide

theorem x0_pow_three : x0 ^ 3 = 1 := by decide

theorem R2m_elems : ∀ g ∈ R2m, g = 1 ∨ g = zP0 ∨ g = x0 * zP0 * x0⁻¹ ∨
    g = x0 ^ 2 * zP0 * (x0 ^ 2)⁻¹ := by
  decide +kernel

theorem prod_conj_zP0 : zP0 * (x0 * zP0 * x0⁻¹) * (x0 ^ 2 * zP0 * (x0 ^ 2)⁻¹) = 1 := by decide

theorem P0_conj_x0 : ∀ t ∈ P0, (t * x0 * t⁻¹) * x0⁻¹ ∈ R2m ∨
    (t * x0 * t⁻¹) * (x0 ^ 2)⁻¹ ∈ R2m := by
  decide +kernel

theorem P0_conj_zP0 : ∀ t ∈ P0, t * zP0 * t⁻¹ = zP0 := by decide +kernel

theorem x0_fpf_M2 : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), IsTraceZero A →
    IsM2 (stAct x0 A + A) → IsM2 A := by
  decide +kernel

theorem P0_eq_R0_mul_R2m : ∀ t ∈ P0, ∃ r ∈ R0, ∃ s ∈ R2m, t = r * s := by decide +kernel

end SL3

namespace RuDataM

variable {G : Type} [Group G] (M : RuDataM G) [Finite G]

omit [Finite G] in
theorem exists_xel : ∃ l : M.L, M.θ l = SL3.x0 ∧ (l : G) ^ 3 = 1 :=
  M.exists_lift SL3.x0_pow_three (by norm_num)

@[expose] noncomputable def xel : M.L := M.exists_xel.choose

omit [Finite G] in
theorem θ_xel : M.θ M.xel = SL3.x0 := M.exists_xel.choose_spec.1

omit [Finite G] in
theorem xel_pow_three : (M.xel : G) ^ 3 = 1 := M.exists_xel.choose_spec.2

omit [Finite G] in
theorem xel_mem_G2 : (M.xel : G) ∈ M.G2 :=
  mem_pullL.mpr ⟨M.xel.2, by rw [M.θ_xel]; exact SL3.x0_mem_Pl⟩

theorem exists_Q5_θ
    {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5) {r : SL(3, ZMod 2)}
    (hr : r ∈ SL3.R0) : ∃ a ∈ M.Q5 hbH, ∃ ha : a ∈ M.L, M.θ ⟨a, ha⟩ = r := by
  rw [← M.θQ_eq] at hr
  obtain ⟨y, hy, rfl⟩ := hr
  obtain ⟨a, ha, c, hc, hac⟩ := exists_Q5_mul_HC hbH hb5 (Subgroup.mem_subgroupOf.mp hy)
  have hcL : c ∈ M.L := M.toRuData.S_le_L (M.HC_le_S hc)
  have hc1 : M.θ ⟨c, hcL⟩ = 1 := by
    have : (⟨c, hcL⟩ : M.L) ∈ M.θ.ker := by
      rw [M.θ_ker, Subgroup.mem_subgroupOf]
      exact M.HC_le_S hc
    exact this
  refine ⟨a, ha, M.Q5_le_L hbH ha, ?_⟩
  have e : y = ⟨a, M.Q5_le_L hbH ha⟩ * ⟨c, hcL⟩ := Subtype.ext hac
  rw [e, map_mul, hc1, mul_one]

theorem exists_ael :
    ∃ a ∈ M.Q5 M.b5el_mem_H, ∃ ha : a ∈ M.L, M.θ ⟨a, ha⟩ = SL3.zP0 :=
  M.exists_Q5_θ M.b5el_mem_H M.orderOf_b5el SL3.zP0_mem_R0

@[expose] noncomputable def ael : G := M.exists_ael.choose

theorem ael_mem_Q5 :
    M.ael ∈ M.Q5 M.b5el_mem_H := M.exists_ael.choose_spec.1

theorem ael_mem_L : M.ael ∈ M.L := M.exists_ael.choose_spec.2.choose

theorem θ_ael :
    M.θ ⟨M.ael, M.ael_mem_L⟩ = SL3.zP0 := M.exists_ael.choose_spec.2.choose_spec

theorem ael_mem_R2 : M.ael ∈ M.R2 :=
  mem_pullL.mpr ⟨M.ael_mem_L, by rw [M.θ_ael]; exact SL3.zP0_mem_R2m⟩

omit [Finite G] in
theorem mem_S_iff_θ {g : G} (hg : g ∈ M.L) : g ∈ ruS M.L ↔ M.θ ⟨g, hg⟩ = 1 := by
  have : M.θ ⟨g, hg⟩ = 1 ↔ (⟨g, hg⟩ : M.L) ∈ M.θ.ker := Iff.rfl
  rw [this, M.θ_ker, Subgroup.mem_subgroupOf]

theorem ael_not_mem_S : M.ael ∉ ruS M.L := by
  rw [M.mem_S_iff_θ M.ael_mem_L, M.θ_ael]
  exact SL3.zP0_ne_one

theorem ael_sq_mem_W : M.ael ^ 2 ∈ M.W := by
  have hS : M.ael ^ 2 ∈ ruS M.L := by
    rw [M.mem_S_iff_θ (pow_mem M.ael_mem_L 2)]
    have : (⟨M.ael ^ 2, pow_mem M.ael_mem_L 2⟩ : M.L) = ⟨M.ael, M.ael_mem_L⟩ ^ 2 := rfl
    rw [this, map_pow, M.θ_ael]
    decide
  exact M.Q5_inf_S_le_W ⟨pow_mem M.ael_mem_Q5 2, hS⟩

omit [Finite G] in
theorem conj_mem_R2 {g r : G} (hg : g ∈ M.G2) (hr : r ∈ M.R2) : g * r * g⁻¹ ∈ M.R2 := by
  obtain ⟨hgL, hgP⟩ := mem_pullL.mp hg
  obtain ⟨hrL, hrP⟩ := mem_pullL.mp hr
  refine mem_pullL.mpr ⟨mul_mem (mul_mem hgL hrL) (inv_mem hgL), ?_⟩
  have e : (⟨g * r * g⁻¹, mul_mem (mul_mem hgL hrL) (inv_mem hgL)⟩ : M.L) =
      ⟨g, hgL⟩ * ⟨r, hrL⟩ * ⟨g, hgL⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv]
  exact SL3.conj_mem_R2m _ hgP _ hrP

@[expose] noncomputable def cak
    (k : ℕ) : G := (M.xel : G) ^ k * M.ael * ((M.xel : G) ^ k)⁻¹

omit [Finite G] in
theorem xel_pow_mem_G2 (k : ℕ) : (M.xel : G) ^ k ∈ M.G2 := pow_mem M.xel_mem_G2 k

theorem cak_mem_R2
    (k : ℕ) : M.cak k ∈ M.R2 := M.conj_mem_R2 (M.xel_pow_mem_G2 k) M.ael_mem_R2

theorem cak_mem_L
    (k : ℕ) : M.cak k ∈ M.L := (mem_pullL.mp (M.cak_mem_R2 k)).1

theorem θ_cak
    (k : ℕ) : M.θ ⟨M.cak k, M.cak_mem_L k⟩ = SL3.x0 ^ k * SL3.zP0 * (SL3.x0 ^ k)⁻¹ := by
  have e : (⟨M.cak k, M.cak_mem_L k⟩ : M.L) = M.xel ^ k * ⟨M.ael, M.ael_mem_L⟩ * (M.xel ^ k)⁻¹ :=
    Subtype.ext (by simp [cak])
  rw [e, map_mul, map_mul, map_inv, map_pow, M.θ_xel, M.θ_ael]

theorem cak_sq_mem_W (k : ℕ) : M.cak k ^ 2 ∈ M.W := by
  have e : M.cak k ^ 2 = (M.xel : G) ^ k * M.ael ^ 2 * ((M.xel : G) ^ k)⁻¹ := by
    simp only [cak, pow_two]
    group
  rw [e]
  exact M.conj_mem_W (M.xel_pow_mem_G2 k) M.ael_sq_mem_W

theorem sq_mem_W_of_R2 {r : G} (hr : r ∈ M.R2) : r ^ 2 ∈ M.W := by
  obtain ⟨hrL, hrP⟩ := mem_pullL.mp hr
  have key : ∀ c, c ∈ M.R2 → c ^ 2 ∈ M.W → ∀ (hcL : c ∈ M.L), M.θ ⟨c, hcL⟩ = M.θ ⟨r, hrL⟩ →
      r ^ 2 ∈ M.W := by
    intro c hc hc2 hcL hθ
    have hs : c⁻¹ * r ∈ ruS M.L := by
      rw [M.mem_S_iff_θ (mul_mem (inv_mem hcL) hrL)]
      have : (⟨c⁻¹ * r, mul_mem (inv_mem hcL) hrL⟩ : M.L) = ⟨c, hcL⟩⁻¹ * ⟨r, hrL⟩ := rfl
      rw [this, map_mul, map_inv, hθ, inv_mul_cancel]
    set s := c⁻¹ * r
    have hr' : r = c * s := by simp only [s]; group
    have h1 := M.comm_mem_W (inv_mem hc) hs
    have h2 : s ^ 2 ∈ M.W := M.U_le_W (M.V_le_U (M.sq_mem_V hs))
    have e : r ^ 2 = c ^ 2 * (c⁻¹ * s * c⁻¹⁻¹ * s⁻¹) * s ^ 2 := by
      rw [hr']
      simp only [pow_two]
      group
    rw [e]
    exact mul_mem (mul_mem hc2 h1) h2
  rcases SL3.R2m_elems _ hrP with h | h | h | h
  · have hS : r ∈ ruS M.L := (M.mem_S_iff_θ hrL).mpr h
    exact M.U_le_W (M.V_le_U (M.sq_mem_V hS))
  · exact key _ (M.cak_mem_R2 0) (M.cak_sq_mem_W 0) (M.cak_mem_L 0) (by rw [M.θ_cak, h]; simp)
  · exact key _ (M.cak_mem_R2 1) (M.cak_sq_mem_W 1) (M.cak_mem_L 1) (by rw [M.θ_cak, h]; simp)
  · exact key _ (M.cak_mem_R2 2) (M.cak_sq_mem_W 2) (M.cak_mem_L 2) (by rw [M.θ_cak, h])

theorem comm_mem_W_of_R2
    {r r' : G} (hr : r ∈ M.R2) (hr' : r' ∈ M.R2) :
    r * r' * r⁻¹ * r'⁻¹ ∈ M.W := by
  have e : r * r' * r⁻¹ * r'⁻¹ = (r * r') ^ 2 * (r'⁻¹ * (r ^ 2)⁻¹ * r'⁻¹⁻¹) * (r' ^ 2)⁻¹ := by
    simp only [pow_two]
    group
  rw [e]
  refine mul_mem (mul_mem (M.sq_mem_W_of_R2 (mul_mem hr hr')) ?_) (inv_mem (M.sq_mem_W_of_R2 hr'))
  exact M.conj_mem_W (M.R2_le_G2 (inv_mem hr')) (inv_mem (M.sq_mem_W_of_R2 hr))

theorem prod_cak_mem_W : M.cak 0 * M.cak 1 * M.cak 2 ∈ M.W := by
  set c := M.cak 0 * M.cak 1 * M.cak 2
  have hcL : c ∈ M.L := mul_mem (mul_mem (M.cak_mem_L 0) (M.cak_mem_L 1)) (M.cak_mem_L 2)
  have hcS : c ∈ ruS M.L := by
    rw [M.mem_S_iff_θ hcL]
    have : (⟨c, hcL⟩ : M.L) = ⟨M.cak 0, M.cak_mem_L 0⟩ * ⟨M.cak 1, M.cak_mem_L 1⟩ *
        ⟨M.cak 2, M.cak_mem_L 2⟩ := rfl
    rw [this, map_mul, map_mul, M.θ_cak, M.θ_cak, M.θ_cak]
    simpa using SL3.prod_conj_zP0
  have hx3 := M.xel_pow_three
  have hxc : (M.xel : G) * c * (M.xel : G)⁻¹ * c⁻¹ ∈ M.W := by
    have e1 : (M.xel : G) * M.cak 2 * (M.xel : G)⁻¹ = M.cak 0 := by
      simp only [cak]
      rw [show (M.xel : G) * ((M.xel : G) ^ 2 * M.ael * ((M.xel : G) ^ 2)⁻¹) * (M.xel : G)⁻¹ =
        (M.xel : G) ^ 3 * M.ael * ((M.xel : G) ^ 3)⁻¹ by group, hx3]
      group
    have e2 : (M.xel : G) * c * (M.xel : G)⁻¹ * c⁻¹ =
        (M.cak 1 * M.cak 2) * M.cak 0 * (M.cak 1 * M.cak 2)⁻¹ * (M.cak 0)⁻¹ := by
      have e0 : (M.xel : G) * M.cak 0 * (M.xel : G)⁻¹ = M.cak 1 := by simp [cak]
      have e1' : (M.xel : G) * M.cak 1 * (M.xel : G)⁻¹ = M.cak 2 := by
        simp only [cak]
        group
      calc (M.xel : G) * c * (M.xel : G)⁻¹ * c⁻¹ =
          ((M.xel : G) * M.cak 0 * (M.xel : G)⁻¹) * ((M.xel : G) * M.cak 1 * (M.xel : G)⁻¹) *
            ((M.xel : G) * M.cak 2 * (M.xel : G)⁻¹) * c⁻¹ := by simp only [c]; group
        _ = M.cak 1 * M.cak 2 * M.cak 0 * c⁻¹ := by rw [e0, e1', e1]
        _ = _ := by simp only [c]; group
    rw [e2]
    exact M.comm_mem_W_of_R2 (mul_mem (M.cak_mem_R2 1) (M.cak_mem_R2 2)) (M.cak_mem_R2 0)
  obtain ⟨hS1, hM1⟩ := hxc
  refine ⟨hcS, SL3.x0_fpf_M2 _ (M.χ_trace _) ?_⟩
  have hxcS : (M.xel : G) * c * (M.xel : G)⁻¹ ∈ ruS M.L :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L M.xel.2) _).mp hcS
  rw [show (⟨(M.xel : G) * c * (M.xel : G)⁻¹ * c⁻¹, hS1⟩ : ruS M.L) =
    ⟨_, hxcS⟩ * (⟨c, hcS⟩ : ruS M.L)⁻¹ from rfl, M.toAdd_χ_mul, M.toAdd_χ_inv] at hM1
  have h := M.χ_conj M.xel ⟨c, hcS⟩
  simp only at h
  rw [h, M.θ_xel] at hM1
  exact hM1

theorem comm_ael_T_mem_W {t : G} (ht : t ∈ (M.T : Subgroup G)) :
    t * M.ael * t⁻¹ * M.ael⁻¹ ∈ M.W := by
  have htL := M.toRuData.T_le_L ht
  obtain ⟨r0, hr0, s0, hs0, hrs⟩ := SL3.P0_eq_R0_mul_R2m _ (M.θ_mem_P0 ht)
  obtain ⟨q, hq, hqL, hqθ⟩ := M.exists_Q5_θ M.b5el_mem_H M.orderOf_b5el hr0
  set r := q⁻¹ * t
  have hrR : r ∈ M.R2 := by
    refine mem_pullL.mpr ⟨mul_mem (inv_mem hqL) htL, ?_⟩
    have : (⟨q⁻¹ * t, mul_mem (inv_mem hqL) htL⟩ : M.L) = ⟨q, hqL⟩⁻¹ * ⟨t, htL⟩ := rfl
    rw [this, map_mul, map_inv, hqθ, hrs, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hs0
  have ht' : t = q * r := by simp only [r]; group
  have hqaS : q * M.ael * q⁻¹ * M.ael⁻¹ ∈ ruS M.L := by
    have hm : q * M.ael * q⁻¹ * M.ael⁻¹ ∈ M.L :=
      mul_mem (mul_mem (mul_mem hqL M.ael_mem_L) (inv_mem hqL)) (inv_mem M.ael_mem_L)
    rw [M.mem_S_iff_θ hm]
    have : (⟨q * M.ael * q⁻¹ * M.ael⁻¹, hm⟩ : M.L) =
        ⟨q, hqL⟩ * ⟨M.ael, M.ael_mem_L⟩ * ⟨q, hqL⟩⁻¹ * ⟨M.ael, M.ael_mem_L⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_mul, map_inv, map_inv, hqθ, M.θ_ael,
      SL3.P0_conj_zP0 _ (SL3.R0_le_P0 hr0), mul_inv_cancel]
  have hqa : q * M.ael * q⁻¹ * M.ael⁻¹ ∈ M.W := M.Q5_inf_S_le_W (Subgroup.mem_inf.mpr
    ⟨mul_mem (mul_mem (mul_mem hq M.ael_mem_Q5) (inv_mem hq)) (inv_mem M.ael_mem_Q5), hqaS⟩)
  have hra := M.comm_mem_W_of_R2 hrR M.ael_mem_R2
  have hqG : q ∈ M.G2 := (M.T_le_G2) ((M.Q5_le_Q _).trans M.toRuDataN.Q_le_T hq)
  have e : t * M.ael * t⁻¹ * M.ael⁻¹ =
      q * (r * M.ael * r⁻¹ * M.ael⁻¹) * q⁻¹ * (q * M.ael * q⁻¹ * M.ael⁻¹) := by
    rw [ht']; group
  rw [e]
  exact mul_mem (M.conj_mem_W hqG hra) hqa

end RuDataM

end CFSG.Quasithin.RuType
