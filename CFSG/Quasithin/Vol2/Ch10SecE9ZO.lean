module

public import CFSG.Quasithin.Vol2.Ch10SecE9T
public import CFSG.Quasithin.Vol2.Ch10SecE9W
public import CFSG.Quasithin.Vol2.Ch10SecE9ZH

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem card_fsuUL_eq (h3 : Case10_1_1Three T L I) :
    Nat.card ↥(fsuUL T L I) =
      8 * Nat.card ↥(Subgroup.centralizer (fsuL0 T L : Set G) ⊓ fsuUL T L I) := by
  obtain ⟨-, hcV1, hnat⟩ := h3
  obtain ⟨K, _, _, hK, π₁, hπ₁⟩ := hnat
  have h := G64.RealizesVia.card_eq hπ₁
  rw [G64.card_natMod, hK, Subgroup.card_top] at h
  have hc : Nat.card ↥(cV1 T L I) =
      Nat.card ↥(Subgroup.centralizer (fsuL0 T L : Set G) ⊓ fsuUL T L I) := by
    rw [← Subgroup.card_map_of_injective (f := (fsuUL T L I).subtype)
      (Subgroup.subtype_injective _), Subgroup.subgroupOf_map_subtype]
  rw [h, hc]
  norm_num

@[expose] def u0 : L32.Γ := ⟨!![1, 1, 0; 0, 1, 1; 0, 0, 1], by decide⟩

theorem u0_mem : u0 ∈ L32.U3 := by
  show L32.IsU u0
  unfold L32.IsU L32.ent u0
  decide

theorem orderOf_u0 : orderOf u0 = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by unfold u0; decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> unfold u0 <;> decide

theorem pCoreOf_fsuL0_facts :
    pCoreOf 2 (fsuL0 T L) ≤ pCoreOf 2 (fsuL0 T L ⊔ T) ∧
      pCoreOf 2 (fsuL0 T L ⊔ T) ⊓ fsuL0 T L ≤ pCoreOf 2 (fsuL0 T L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuL0 T L : Set G) :=
    sup_le Subgroup.le_normalizer (SecA.le_fsuM T L)
  refine ⟨CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans le_sup_left)
    (hN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _), ?_⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right (fun x hx => ?_)
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hx),
      Subgroup.le_normalizer hx⟩

theorem exists_order_four (h3228 : TmpL6_3_2_2_eight)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I)
    (h3 : Case10_1_1Three T L I) :
    ∃ g ∈ autI (isElemAbelian_ZQ T L I) L, g ∈ autI (isElemAbelian_ZQ T L I) (T1 T L) ∧
      orderOf g = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, Ψ, c, h⟩ := exists_maxCtx h37 h38 hyp h3
  set hZ := isElemAbelian_ZQ T L I
  have hN := le_normalizer_ZQ h37 h38 hyp
  obtain ⟨hO₁, hO₂⟩ := pCoreOf_fsuL0_facts (T := T) (L := L)
  have hmem : (u0, (1 : L32.Γ)) ∈ ((T0 T L).subgroupOf (fsuL0 T L)).map Ψ := by
    rw [h.hC.T0]
    exact ⟨u0_mem, L32.U3.one_mem⟩
  obtain ⟨y, hyT, hyΨ⟩ := Subgroup.mem_map.mp hmem
  obtain ⟨l, hl, hlΨ⟩ := exists_mem_L_fst h u0
  have hyL0 : (y : G) ∈ fsuL0 T L := y.2
  have hyH : (y : G) ∈ fsuL0 T L ⊔ T := Subgroup.mem_sup_left hyL0
  have hlH : l ∈ fsuL0 T L ⊔ T := Subgroup.mem_sup_left (SecA.le_fsuL0 T L hl)
  have hker : ∀ z : ↥(fsuL0 T L), Ψ z = 1 →
      convI hZ ⟨(z : G), hN (Subgroup.mem_sup_left z.2)⟩ = 1 := fun z hz => by
    rw [convI_eq_one_iff]
    exact (mem_centralizer_ZQ_iff h3228 h37 h38 hyp h3 (Subgroup.mem_sup_left z.2)).mpr
      (hO₁ ((h.hC.ker z).mp hz))
  set g := convI hZ ⟨(y : G), hN hyH⟩ with hg
  have hgl : g = convI hZ ⟨l, hN hlH⟩ := by
    have e : (⟨(y : G), hN hyH⟩ : Subgroup.normalizer (ZQ T L I : Set G)) =
        ⟨(y : G) * l⁻¹, hN ((fsuL0 T L ⊔ T).mul_mem hyH ((fsuL0 T L ⊔ T).inv_mem hlH))⟩ *
          ⟨l, hN hlH⟩ := Subtype.ext (by simp)
    have h1 := hker (y * (⟨l, SecA.le_fsuL0 T L hl⟩ : ↥(fsuL0 T L))⁻¹) (by
      rw [map_mul, map_inv, hyΨ, hlΨ, mul_inv_cancel])
    rw [hg, e, map_mul]
    have e2 : (⟨(y : G) * l⁻¹, hN ((fsuL0 T L ⊔ T).mul_mem hyH ((fsuL0 T L ⊔ T).inv_mem hlH))⟩ :
        Subgroup.normalizer (ZQ T L I : Set G)) =
        ⟨((y * (⟨l, SecA.le_fsuL0 T L hl⟩ : ↥(fsuL0 T L))⁻¹ : ↥(fsuL0 T L)) : G),
          hN (Subgroup.mem_sup_left (y * (⟨l, SecA.le_fsuL0 T L hl⟩ : ↥(fsuL0 T L))⁻¹).2)⟩ :=
      Subtype.ext rfl
    rw [e2, h1, one_mul]
  have hyT1 : (y : G) ∈ T1 T L := SecA.T0_le_T1 hyp.fsu.maximal.1 (Subgroup.mem_subgroupOf.mp hyT)
  refine ⟨g, hgl ▸ convI_mem_autI hZ hl _, convI_mem_autI hZ hyT1 _, ?_⟩
  have hpow : ∀ n : ℕ, g ^ n = convI hZ ⟨(y : G) ^ n, hN ((fsuL0 T L ⊔ T).pow_mem hyH n)⟩ :=
    fun n => by rw [hg, ← map_pow]; rfl
  have hΨpow : ∀ n : ℕ, Ψ (y ^ n) = (u0 ^ n, 1) := fun n => by rw [map_pow, hyΨ]; simp
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
  refine orderOf_eq_prime_pow (fun h2 => ?_) ?_
  · rw [pow_one, hpow, convI_eq_one_iff] at h2
    have h4 := (mem_centralizer_ZQ_iff h3228 h37 h38 hyp h3
      ((fsuL0 T L ⊔ T).pow_mem hyH 2)).mp h2
    have h5 : ((y ^ 2 : ↥(fsuL0 T L)) : G) ∈ pCoreOf 2 (fsuL0 T L) := hO₂ ⟨h4, (y ^ 2).2⟩
    have h6 := (h.hC.ker (y ^ 2)).mpr h5
    rw [hΨpow] at h6
    have h7 : u0 ^ 2 = 1 := congrArg Prod.fst h6
    have := orderOf_le_of_pow_eq_one (by norm_num) h7
    rw [orderOf_u0] at this
    omega
  · rw [hpow]
    have h1 := hker (y ^ 4) (by rw [hΨpow, ← orderOf_u0, pow_orderOf_eq_one]; rfl)
    exact h1

end CFSG.Quasithin.Vol2.Ch10.SecB.E9
