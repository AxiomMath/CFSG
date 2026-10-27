module

public import CFSG.Quasithin.Recognition.RuTypeJ44b

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped MatrixGroups

theorem card_sup_mul_inf_of_normalizes {X : Type*} [Group X] {A B : Subgroup X}
    (h : A ≤ Subgroup.normalizer (B : Set X)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  have e := Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A B h).toEquiv
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf A)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf (A ⊔ B))
  have h3 : Nat.card (B.subgroupOf A) = Nat.card ↥(A ⊓ B) :=
    Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have h4 : Nat.card (B.subgroupOf (A ⊔ B)) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h3] at h1
  rw [h4, ← e] at h2
  rw [h1, h2]
  ring

theorem relIndex_normalizer_modEq_one {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (P : Sylow p X) {K : Subgroup X} (hK : Subgroup.normalizer (P : Set X) ≤ K) :
    (Subgroup.normalizer (P : Set X)).relIndex K ≡ 1 [MOD p] := by
  have hPK : (P : Subgroup X) ≤ K := Subgroup.le_normalizer.trans hK
  have h := card_sylow_modEq_one p K
  rw [(P.subtype hPK).card_eq_index_normalizer] at h
  have e : Subgroup.normalizer ((P.subtype hPK : Set K)) =
      (Subgroup.normalizer (P : Set X)).subgroupOf K :=
    (Subgroup.subgroupOf_normalizer_eq hPK).symm
  rw [e] at h
  exact h

theorem eq_one_or_six_of_dvd_24 : ∀ n < 25, n ∣ 24 → n % 5 = 1 → n = 1 ∨ n = 6 := by decide

theorem perm5_normalizer_maximal {β : Equiv.Perm (Fin 5)} (hβ : orderOf β = 5)
    {X : Subgroup (Equiv.Perm (Fin 5))}
    (hX : Subgroup.normalizer (Subgroup.zpowers β : Set (Equiv.Perm (Fin 5))) ≤ X) :
    X ≤ Subgroup.normalizer (Subgroup.zpowers β : Set (Equiv.Perm (Fin 5))) ∨ X = ⊤ := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcard : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_perm, Nat.card_fin]
    rfl
  have hP : Nat.card (Subgroup.zpowers β) = 5 ^ 1 := by rw [Nat.card_zpowers, hβ, pow_one]
  have hidx : (Subgroup.zpowers β).index = 24 := by
    have h := (Subgroup.zpowers β).card_mul_index
    rw [hP, hcard] at h
    omega
  let P : Sylow 5 (Equiv.Perm (Fin 5)) :=
    (IsPGroup.of_card hP).toSylow (by rw [hidx]; decide)
  set N := Subgroup.normalizer (Subgroup.zpowers β : Set (Equiv.Perm (Fin 5)))
  have hr : N.relIndex X ≡ 1 [MOD 5] := relIndex_normalizer_modEq_one P (K := X) hX
  have hn : N.relIndex ⊤ ≡ 1 [MOD 5] := relIndex_normalizer_modEq_one P (K := ⊤) le_top
  rw [Subgroup.relIndex_top_right] at hn
  have hNdvd : N.index ∣ 24 := hidx ▸ Subgroup.index_dvd_of_le Subgroup.le_normalizer
  have hmul := Subgroup.relIndex_mul_index hX
  have hr' : N.relIndex X % 5 = 1 := hr
  have hn' : N.index % 5 = 1 := hn
  have hN1 : N.index = 1 ∨ N.index = 6 :=
    eq_one_or_six_of_dvd_24 _ (Nat.lt_succ_of_le (Nat.le_of_dvd (by norm_num) hNdvd)) hNdvd hn'
  have hrdvd : N.relIndex X ∣ 24 := (Dvd.intro _ hmul).trans hNdvd
  have hr1 : N.relIndex X = 1 ∨ N.relIndex X = 6 :=
    eq_one_or_six_of_dvd_24 _ (Nat.lt_succ_of_le (Nat.le_of_dvd (by norm_num) hrdvd)) hrdvd hr'
  rcases hr1 with h1 | h6
  · exact Or.inl (Subgroup.relIndex_eq_one.mp h1)
  · right
    rw [h6] at hmul
    apply Subgroup.index_eq_one.mp
    rcases hN1 with h | h <;> omega

theorem conj_mem_sup_of {X : Type*} [Group X] {A B C : Subgroup X} {g : X}
    (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ C) (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ C) {x : X}
    (hx : x ∈ A ⊔ B) : g * x * g⁻¹ ∈ C := by
  have hle : A ⊔ B ≤ C.comap (MulAut.conj g).toMonoidHom := sup_le hA hB
  exact hle hx

namespace SL3

theorem comm_P0_R2m : ∀ g ∈ P0, ∀ r ∈ R2m, g * r * g⁻¹ * r⁻¹ = 1 ∨ g * r * g⁻¹ * r⁻¹ = zP0 := by
  decide +kernel

@[expose] def gs1 : SL(3, ZMod 2) := ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], by decide⟩

@[expose] def gs2 : SL(3, ZMod 2) := ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 1], by decide⟩

theorem gs1_mem_Stab0 : gs1 ∈ Stab0 := by decide

theorem gs2_mem_Stab0 : gs2 ∈ Stab0 := by decide

abbrev IsCoreM2 (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Prop :=
  IsM2 A ∧ IsM2 (stAct gs1 A) ∧ IsM2 (stAct gs2 A)

theorem IsCoreM2.add {A B : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : IsCoreM2 A)
    (hB : IsCoreM2 B) : IsCoreM2 (A + B) := by
  obtain ⟨h1, h2, h3⟩ := hA
  obtain ⟨h4, h5, h6⟩ := hB
  refine ⟨h1.add h4, ?_, ?_⟩
  · rw [stAct_add]
    exact h2.add h5
  · rw [stAct_add]
    exact h3.add h6

theorem isCoreM2_zero : IsCoreM2 0 := by decide

theorem card_coreM2 :
    Fintype.card {A : Matrix (Fin 3) (Fin 3) (ZMod 2) // IsCoreM2 A ∧ IsTraceZero A} = 8 := by
  decide +kernel

end SL3

namespace RuDataM

variable {G : Type} [Group G] (M : RuDataM G)

@[expose] def WcM2 : Subgroup G where
  carrier := {x | ∃ hx : x ∈ ruS M.L, SL3.IsCoreM2 (Multiplicative.toAdd (M.χ ⟨x, hx⟩))}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    rw [show (⟨a * b, mul_mem ha hb⟩ : ruS M.L) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl, M.toAdd_χ_mul]
    exact ha'.add hb'
  one_mem' := ⟨(ruS M.L).one_mem, by
    rw [show (⟨1, (ruS M.L).one_mem⟩ : ruS M.L) = 1 from rfl, map_one, toAdd_one]
    exact SL3.isCoreM2_zero⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    rw [show (⟨a⁻¹, inv_mem ha⟩ : ruS M.L) = (⟨a, ha⟩ : ruS M.L)⁻¹ from rfl, M.toAdd_χ_inv]
    exact ha'

variable [Finite G]

noncomputable abbrev Q5W : Subgroup G := M.Q5 M.b5el_mem_H ⊔ M.W

noncomputable abbrev Ygrp : Subgroup G := M.Q5 M.b5el_mem_H ⊔ M.Q0

theorem conj_mem_Y {h : G} (hh : h ∈ ruH M.T) {k : ℕ} {q : G} (hq : q ∈ ruQ M.T)
    (hhb : h * M.b5el * h⁻¹ = M.b5el ^ k * q) {x : G} (hx : x ∈ M.Ygrp) :
    h * x * h⁻¹ ∈ M.Ygrp :=
  conj_mem_sup_of (fun _ ha => Subgroup.mem_sup_left (M.conj_mem_Q5 M.b5el_mem_H hh hq hhb ha))
    (fun _ hb => Subgroup.mem_sup_right (M.conj_mem_Q0 hh hb)) hx

theorem exists_conj_b5el {h : G} (hh : h ∈ ruH M.T)
    (hn : M.σ5 ⟨h, hh⟩ ∈ Subgroup.normalizer
      (Subgroup.zpowers (M.σ5 ⟨M.b5el, M.b5el_mem_H⟩) : Set (Equiv.Perm (Fin 5)))) :
    ∃ k : ℕ, ∃ q ∈ ruQ M.T, h * M.b5el * h⁻¹ = M.b5el ^ k * q := by
  have h1 : M.σ5 ⟨h, hh⟩ * M.σ5 ⟨M.b5el, M.b5el_mem_H⟩ * (M.σ5 ⟨h, hh⟩)⁻¹ ∈
      Subgroup.zpowers (M.σ5 ⟨M.b5el, M.b5el_mem_H⟩) :=
    (Subgroup.mem_normalizer_iff.mp hn _).mp (Subgroup.mem_zpowers _)
  obtain ⟨k, hk⟩ := mem_powers_iff_mem_zpowers.mpr h1
  have hmem : (M.b5el ^ k)⁻¹ * (h * M.b5el * h⁻¹) ∈ ruH M.T :=
    mul_mem (inv_mem (pow_mem M.b5el_mem_H k)) (mul_mem (mul_mem hh M.b5el_mem_H) (inv_mem hh))
  refine ⟨k, (M.b5el ^ k)⁻¹ * (h * M.b5el * h⁻¹), ?_, (mul_inv_cancel_left _ _).symm⟩
  have hker : (⟨(M.b5el ^ k)⁻¹ * (h * M.b5el * h⁻¹), hmem⟩ : ruH M.T) ∈ M.σ5.ker := by
    rw [MonoidHom.mem_ker]
    have e : (⟨(M.b5el ^ k)⁻¹ * (h * M.b5el * h⁻¹), hmem⟩ : ruH M.T) =
        ((⟨M.b5el, M.b5el_mem_H⟩ : ruH M.T) ^ k)⁻¹ *
          (⟨h, hh⟩ * ⟨M.b5el, M.b5el_mem_H⟩ * (⟨h, hh⟩ : ruH M.T)⁻¹) := rfl
    rw [e]
    simp only [map_mul, map_inv, map_pow]
    rw [← hk, inv_mul_cancel]
  rw [M.σ5_ker, Subgroup.mem_subgroupOf] at hker
  exact hker

theorem card_WcM2 : Nat.card M.WcM2 = 2 ^ 6 := by
  rw [M.card_preimage M.WcM2 (fun A => SL3.IsCoreM2 A ∧ IsTraceZero A) (fun _ ⟨hx, _⟩ => hx)
    (fun x hx => ⟨fun ⟨_, h⟩ => ⟨h, M.χ_trace _⟩, fun h => ⟨hx, h.1⟩⟩) (fun A hA => hA.2),
    Nat.card_eq_fintype_card, SL3.card_coreM2]
  norm_num

theorem R2_le_T : M.R2 ≤ (M.T : Subgroup G) := by
  intro r hr
  obtain ⟨hrL, hrP⟩ := mem_pullL.mp hr
  have h0 : M.θ ⟨r, hrL⟩ ∈ SL3.P0 := SL3.R2m_le_P0 hrP
  rw [← M.hP0] at h0
  obtain ⟨t1, ht1, ht1θ⟩ := h0
  have ht1T : (t1 : G) ∈ (M.T : Subgroup G) := Subgroup.mem_subgroupOf.mp ht1
  have hsL : (t1 : G)⁻¹ * r ∈ M.L := mul_mem (inv_mem t1.2) hrL
  have hsS : (t1 : G)⁻¹ * r ∈ ruS M.L := by
    rw [M.mem_S_iff_θ hsL]
    have e : (⟨(t1 : G)⁻¹ * r, hsL⟩ : M.L) = t1⁻¹ * ⟨r, hrL⟩ := rfl
    rw [e, map_mul, map_inv, ht1θ, inv_mul_cancel]
  have e : r = (t1 : G) * ((t1 : G)⁻¹ * r) := by group
  rw [e]
  exact mul_mem ht1T (M.toRuData.S_le_T hsS)

theorem Agrp_le_T : M.Agrp ≤ (M.T : Subgroup G) :=
  M.Agrp_le_R2.trans M.R2_le_T

theorem Agrp_le_H : M.Agrp ≤ ruH M.T :=
  M.Agrp_le_T.trans M.toRuData.T_le_H

theorem Agrp_le_G2 : M.Agrp ≤ M.G2 :=
  M.Agrp_le_R2.trans M.R2_le_G2

theorem comm_T_Agrp {t y : G} (ht : t ∈ (M.T : Subgroup G))
    (hy : y ∈ M.Agrp) :
    t * y * t⁻¹ * y⁻¹ ∈ M.W ∨ M.ael⁻¹ * (t * y * t⁻¹ * y⁻¹) ∈ M.W := by
  have hc : t * y * t⁻¹ * y⁻¹ ∈ M.Agrp := mul_mem (M.T_conj_mem_Agrp ht hy) (inv_mem hy)
  have hcL := M.Agrp_le_L hc
  have htL := M.toRuData.T_le_L ht
  obtain ⟨hyL, hyR⟩ := mem_pullL.mp (M.Agrp_le_R2 hy)
  have e : (⟨t * y * t⁻¹ * y⁻¹, hcL⟩ : M.L) =
      ⟨t, htL⟩ * ⟨y, hyL⟩ * (⟨t, htL⟩ : M.L)⁻¹ * (⟨y, hyL⟩ : M.L)⁻¹ := rfl
  have hθ : M.θ ⟨t * y * t⁻¹ * y⁻¹, hcL⟩ = 1 ∨ M.θ ⟨t * y * t⁻¹ * y⁻¹, hcL⟩ = SL3.zP0 := by
    rw [e]
    simp only [map_mul, map_inv]
    exact SL3.comm_P0_R2m _ (M.θ_mem_P0 ht) _ hyR
  rcases hθ with h | h
  · left
    rw [← M.Agrp_inf_S]
    exact ⟨hc, (M.mem_S_iff_θ hcL).mpr h⟩
  · right
    rw [← M.Agrp_inf_S]
    have hL : M.ael⁻¹ * (t * y * t⁻¹ * y⁻¹) ∈ M.L := mul_mem (inv_mem M.ael_mem_L) hcL
    have hA : M.ael⁻¹ * (t * y * t⁻¹ * y⁻¹) ∈ M.Agrp := mul_mem (inv_mem M.ael_mem_Agrp) hc
    refine ⟨hA, (M.mem_S_iff_θ hL).mpr ?_⟩
    have e2 : (⟨M.ael⁻¹ * (t * y * t⁻¹ * y⁻¹), hL⟩ : M.L) =
        (⟨M.ael, M.ael_mem_L⟩ : M.L)⁻¹ * ⟨t * y * t⁻¹ * y⁻¹, hcL⟩ := rfl
    rw [e2, map_mul, map_inv, h, M.θ_ael, inv_mul_cancel]

theorem Q5_le_T : M.Q5 M.b5el_mem_H ≤ (M.T : Subgroup G) :=
  (M.Q5_le_Q _).trans M.Q_le_T

theorem Q5_le_H : M.Q5 M.b5el_mem_H ≤ ruH M.T :=
  (M.Q5_le_Q _).trans (pCoreOf_le 2 _)

theorem Q5_le_normalizer_W : M.Q5 M.b5el_mem_H ≤ Subgroup.normalizer (M.W : Set G) :=
  fun _ hq => mem_normalizer_of_conj_mem fun _ hw => M.conj_mem_W (M.T_le_G2 (M.Q5_le_T hq)) hw

theorem Q5_le_normalizer_Q0 : M.Q5 M.b5el_mem_H ≤ Subgroup.normalizer (M.Q0 : Set G) :=
  fun _ hq => mem_normalizer_of_conj_mem fun _ hx => M.conj_mem_Q0 (M.Q5_le_H hq) hx

theorem Q5_inf_W :
    M.Q5 M.b5el_mem_H ⊓ M.W = M.Q5 M.b5el_mem_H ⊓ ruS M.L :=
  le_antisymm (inf_le_inf_left _ M.W_le_S) (le_inf inf_le_left M.Q5_inf_S_le_W)

theorem card_Q5W : Nat.card M.Q5W = 2 ^ 11 := by
  have h := card_sup_mul_inf_of_normalizes M.Q5_le_normalizer_W
  rw [M.Q5_inf_W, M.card_Q5_inf_S M.b5el_mem_H M.orderOf_b5el,
    card_Q5 M.b5el_mem_H M.orderOf_b5el, M.card_W] at h
  have h' : Nat.card ↥(M.Q5 M.b5el_mem_H ⊔ M.W) * 2 ^ 7 = 2 ^ 11 * 2 ^ 7 := by
    rw [h]
    norm_num
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

theorem card_Y : Nat.card M.Ygrp = 2 ^ 10 := by
  have h := card_sup_mul_inf_of_normalizes M.Q5_le_normalizer_Q0
  rw [show M.Q5 M.b5el_mem_H ⊓ M.Q0 = M.Q0 ⊓ M.Q5 M.b5el_mem_H from inf_comm _ _,
    M.Q0_inf_Q5 M.b5el_mem_H M.orderOf_b5el, M.toRuData.card_U,
    card_Q5 M.b5el_mem_H M.orderOf_b5el, M.card_Q0] at h
  have h' : Nat.card ↥(M.Q5 M.b5el_mem_H ⊔ M.Q0) * 32 = 2 ^ 10 * 32 := by
    rw [h]
    norm_num
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

theorem Y_le_Q5W_inf_Q : M.Ygrp ≤ M.Q5W ⊓ ruQ M.T :=
  sup_le (le_inf le_sup_left (M.Q5_le_Q _)) (le_inf (M.Q0_le_W.trans le_sup_right) M.Q0_le_Q)

theorem Q5W_inf_Q : M.Q5W ⊓ ruQ M.T = M.Ygrp := by
  symm
  refine Subgroup.eq_of_le_of_card_ge M.Y_le_Q5W_inf_Q ?_
  rw [M.card_Y]
  obtain ⟨k, hk, hcard⟩ := RuDataN.exists_card_eq_two_pow
    (inf_le_left : M.Q5W ⊓ ruQ M.T ≤ M.Q5W) M.card_Q5W
  rw [hcard]
  have hk' : k ≠ 11 := by
    rintro rfl
    have heq : M.Q5W ⊓ ruQ M.T = M.Q5W :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard, M.card_Q5W])
    have hv : M.vel ∈ M.Q5W ⊓ ruQ M.T := by
      rw [heq]
      exact Subgroup.mem_sup_right (M.Ual_le_W M.vel_mem_Ual)
    exact M.vel_not_mem_Q hv.2
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem Agrp_conj_Q5_mem_Q5W {y q : G} (hy : y ∈ M.Agrp)
    (hq : q ∈ M.Q5 M.b5el_mem_H) : y * q * y⁻¹ ∈ M.Q5W := by
  rcases M.comm_T_Agrp (M.Q5_le_T hq) hy with h | h
  · have e : y * q * y⁻¹ = (q * y * q⁻¹ * y⁻¹)⁻¹ * q := by group
    rw [e]
    exact mul_mem (inv_mem (Subgroup.mem_sup_right h)) (Subgroup.mem_sup_left hq)
  · have e : y * q * y⁻¹ = (M.ael⁻¹ * (q * y * q⁻¹ * y⁻¹))⁻¹ * M.ael⁻¹ * q := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (Subgroup.mem_sup_right h))
      (inv_mem (Subgroup.mem_sup_left M.ael_mem_Q5))) (Subgroup.mem_sup_left hq)

theorem Agrp_conj_Q5W {y x : G} (hy : y ∈ M.Agrp)
    (hx : x ∈ M.Q5W) : y * x * y⁻¹ ∈ M.Q5W :=
  conj_mem_sup_of (fun _ hq => M.Agrp_conj_Q5_mem_Q5W hy hq)
    (fun _ hw => Subgroup.mem_sup_right (M.conj_mem_W (M.Agrp_le_G2 hy) hw)) hx

theorem Agrp_conj_Y {y x : G} (hy : y ∈ M.Agrp)
    (hx : x ∈ M.Ygrp) : y * x * y⁻¹ ∈ M.Ygrp := by
  rw [← M.Q5W_inf_Q] at hx ⊢
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  exact Subgroup.mem_inf.mpr ⟨M.Agrp_conj_Q5W hy hx1, M.conj_mem_Q (M.Agrp_le_H hy) hx2⟩

theorem Y_inf_S_le_W : M.Ygrp ⊓ ruS M.L ≤ M.W := by
  rintro x ⟨hxY, hxS⟩
  have hx : x ∈ ((M.Q5 M.b5el_mem_H ⊔ M.W : Subgroup G) : Set G) :=
    (Subgroup.mem_inf.mp (M.Y_le_Q5W_inf_Q hxY)).1
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ M.Q5_le_normalizer_W] at hx
  obtain ⟨q, hq, w, hw, rfl⟩ := hx
  have hqS : q ∈ ruS M.L := by
    have e : q = (q * w) * w⁻¹ := by group
    rw [e]
    exact mul_mem hxS (inv_mem (M.W_le_S hw))
  exact mul_mem (M.Q5_inf_S_le_W ⟨hq, hqS⟩) hw

theorem not_LT1_normalizes_Y
    (h : ∀ l ∈ M.LT1, ∀ y ∈ M.Ygrp, l * y * l⁻¹ ∈ M.Ygrp) : False := by
  have key : ∀ g ∈ SL3.Stab0, ∀ x (hxS : x ∈ ruS M.L), x ∈ M.Ygrp →
      SL3.IsM2 (stAct g (Multiplicative.toAdd (M.χ ⟨x, hxS⟩))) := by
    intro g hg x hxS hxY
    obtain ⟨l, hl⟩ := M.θ_surj g
    have hlLT1 : (l : G) ∈ M.LT1 := mem_pullL.mpr ⟨l.2, by
      show M.θ l ∈ SL3.Stab0
      rw [hl]
      exact hg⟩
    have hlxS : (l : G) * x * (l : G)⁻¹ ∈ ruS M.L :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L l.2) x).mp hxS
    obtain ⟨_, hM2⟩ := M.Y_inf_S_le_W ⟨h _ hlLT1 x hxY, hlxS⟩
    have hχ := M.χ_conj l ⟨x, hxS⟩
    rw [hl] at hχ
    rw [← hχ]
    exact hM2
  have hle : M.Q5 M.b5el_mem_H ⊓ ruS M.L ≤ M.WcM2 := by
    rintro x ⟨hx5, hxS⟩
    have hxY : x ∈ M.Ygrp := Subgroup.mem_sup_left hx5
    have h1 := key 1 (one_mem _) x hxS hxY
    rw [SL3.stAct_one] at h1
    exact ⟨hxS, h1, key _ SL3.gs1_mem_Stab0 x hxS hxY, key _ SL3.gs2_mem_Stab0 x hxS hxY⟩
  have hcard := Subgroup.card_le_of_le hle
  rw [M.card_Q5_inf_S M.b5el_mem_H M.orderOf_b5el, M.card_WcM2] at hcard
  norm_num at hcard

theorem orderOf_σ5_b5el : orderOf (M.σ5 ⟨M.b5el, M.b5el_mem_H⟩) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  apply orderOf_eq_prime
  · rw [← map_pow]
    have e : (⟨M.b5el, M.b5el_mem_H⟩ : ruH M.T) ^ 5 = 1 := Subtype.ext (by
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact pow_five_of_orderOf M.orderOf_b5el)
    rw [e, map_one]
  · intro h1
    have hQ : M.b5el ∈ ruQ M.T := by
      have hk : (⟨M.b5el, M.b5el_mem_H⟩ : ruH M.T) ∈ M.σ5.ker := h1
      rw [M.σ5_ker, Subgroup.mem_subgroupOf] at hk
      exact hk
    have hdvd := Subgroup.orderOf_dvd_natCard _ hQ
    rw [M.orderOf_b5el, M.toRuData.card_Q] at hdvd
    norm_num at hdvd

theorem σ5_mem_normalizer_of_conj_Y {h : G}
    (hh : h ∈ ruH M.T) (hY : ∀ x ∈ M.Ygrp, h * x * h⁻¹ ∈ M.Ygrp) :
    M.σ5 ⟨h, hh⟩ ∈ Subgroup.normalizer
      (Subgroup.zpowers (M.σ5 ⟨M.b5el, M.b5el_mem_H⟩) : Set (Equiv.Perm (Fin 5))) := by
  let NY : Subgroup (ruH M.T) := (Subgroup.normalizer (M.Ygrp : Set G)).subgroupOf (ruH M.T)
  have hle : Subgroup.normalizer (Subgroup.zpowers (M.σ5 ⟨M.b5el, M.b5el_mem_H⟩) :
      Set (Equiv.Perm (Fin 5))) ≤ NY.map M.σ5 := by
    intro π hπ
    obtain ⟨h', rfl⟩ := M.σ5_surj π
    obtain ⟨k, q, hq, hk⟩ := M.exists_conj_b5el h'.2 hπ
    have hN : (h' : G) ∈ Subgroup.normalizer (M.Ygrp : Set G) :=
      mem_normalizer_of_conj_mem fun x hx => M.conj_mem_Y h'.2 hq hk hx
    exact ⟨h', hN, rfl⟩
  rcases perm5_normalizer_maximal M.orderOf_σ5_b5el hle with hX | hX
  · have hN : h ∈ Subgroup.normalizer (M.Ygrp : Set G) := mem_normalizer_of_conj_mem hY
    exact hX ⟨⟨h, hh⟩, hN, rfl⟩
  · exfalso
    apply M.not_LT1_normalizes_Y
    intro l hl x hx
    have hlH : l ∈ ruH M.T := M.LT1_le_H hl
    have hmem : M.σ5 ⟨l, hlH⟩ ∈ NY.map M.σ5 := by
      rw [hX]
      exact Subgroup.mem_top _
    obtain ⟨n, hn, hnl⟩ := hmem
    have hn' : (n : G) ∈ Subgroup.normalizer (M.Ygrp : Set G) := hn
    have hqH : (n : G)⁻¹ * l ∈ ruH M.T := mul_mem (inv_mem n.2) hlH
    have hσ : M.σ5 ⟨(n : G)⁻¹ * l, hqH⟩ = 1 := by
      have e : (⟨(n : G)⁻¹ * l, hqH⟩ : ruH M.T) = n⁻¹ * ⟨l, hlH⟩ := rfl
      rw [e, map_mul, map_inv, hnl, inv_mul_cancel]
    obtain ⟨k, q, hq, hk⟩ := M.exists_conj_b5el hqH (by rw [hσ]; exact one_mem _)
    have hqY := M.conj_mem_Y hqH hq hk hx
    have hnY := (Subgroup.mem_normalizer_iff.mp hn' _).mp hqY
    have e : l * x * l⁻¹ =
        (n : G) * ((n : G)⁻¹ * l * x * ((n : G)⁻¹ * l)⁻¹) * (n : G)⁻¹ := by group
    rw [e]
    exact hnY

theorem Agrp_conj_b5el {y : G} (hy : y ∈ M.Agrp) :
    ∃ k : ℕ, ∃ q ∈ ruQ M.T, y * M.b5el * y⁻¹ = M.b5el ^ k * q :=
  M.exists_conj_b5el (M.Agrp_le_H hy)
    (M.σ5_mem_normalizer_of_conj_Y (M.Agrp_le_H hy) fun _ hx => M.Agrp_conj_Y hy hx)

theorem Agrp_conj_Q5 {y x : G} (hy : y ∈ M.Agrp)
    (hx : x ∈ M.Q5 M.b5el_mem_H) : y * x * y⁻¹ ∈ M.Q5 M.b5el_mem_H := by
  obtain ⟨k, q, hq, hk⟩ := M.Agrp_conj_b5el hy
  exact M.conj_mem_Q5 M.b5el_mem_H (M.Agrp_le_H hy) hq hk hx

end RuDataM

end CFSG.Quasithin.RuType
