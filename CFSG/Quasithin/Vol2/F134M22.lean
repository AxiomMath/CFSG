module

public import CFSG.Quasithin.Vol2.F134M22Check
public import CFSG.Quasithin.Vol2.F134Overgroup

public section

namespace CFSG.Quasithin.F134

open Equiv CFSG.Blueprint CFSG.Quasithin.P134
open scoped Pointwise

theorem permCode_m22Word (w : List ℕ) : permCode (m22Word w) = m22WordC w := by
  induction w with
  | nil => exact m22_code_one
  | cons c w ih =>
    by_cases hc : c = 0
    · simp only [m22Word, m22WordC, hc, ite_true, permCode_mul22, ih, m22_code_a]
    · simp only [m22Word, m22WordC, hc, ite_false, permCode_mul22, ih, m22_code_b]

theorem m22Word_mem (w : List ℕ) : m22Word w ∈ NativeSporadic.M22 := by
  induction w with
  | nil => exact one_mem _
  | cons c w ih =>
    refine mul_mem ?_ ih
    rw [m22_eq_closure]
    split_ifs
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem eq_of_permCode {σ τ : Perm (Fin 22)} (h : permCode σ = permCode τ) : σ = τ :=
  permCode_injective (by norm_num) h

@[expose] def m22TGen (k : ℕ) : Perm (Fin 22) := m22Word (m22TGenW.getD k [])

@[expose] def m22T : Subgroup (Perm (Fin 22)) := Subgroup.closure {x | ∃ k < 3, m22TGen k = x}

theorem permCode_m22TGen {k : ℕ} (hk : k < 3) : permCode (m22TGen k) = m22TG k := by
  rw [m22TGen, permCode_m22Word]
  exact m22_tgen_check k hk

theorem m22T_le : m22T ≤ NativeSporadic.M22 := by
  rw [m22T, Subgroup.closure_le]
  rintro _ ⟨k, -, rfl⟩
  exact m22Word_mem _

theorem m22T_sub {x : Perm (Fin 22)} (hx : x ∈ m22T) : ∃ i < 128, permCode x = m22Tel i := by
  refine closure_subset_of_right_closed (S := {x | ∃ k < 3, m22TGen k = x})
    (P := {x | ∃ i < 128, permCode x = m22Tel i})
    (fun s _ => ⟨orderOf s, orderOf_pos s, pow_orderOf_eq_one s⟩)
    ⟨0, by norm_num, by rw [m22_code_one, m22_tel_zero]⟩ ?_ hx
  rintro p ⟨i, hi, hp⟩ s ⟨k, hk, rfl⟩
  obtain ⟨h1, h2⟩ := m22_nxt_check i hi k hk
  exact ⟨_, h1, by rw [permCode_mul22, hp, permCode_m22TGen hk, h2]⟩

theorem m22T_sup : ∀ i < 128, ∃ x ∈ m22T, permCode x = m22Tel i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact ⟨1, one_mem _, by rw [m22_code_one, m22_tel_zero]⟩
    · obtain ⟨h1, h2, h3⟩ := m22_par_check i hi hpos
      obtain ⟨y, hy, hyc⟩ := ih _ h1 (h1.trans hi)
      refine ⟨y * m22TGen (m22Par i % 4), mul_mem hy (Subgroup.subset_closure ⟨_, h2, rfl⟩), ?_⟩
      rw [permCode_mul22, hyc, permCode_m22TGen h2, h3]

theorem m22T_isPGroup : IsPGroup 2 m22T := by
  intro x
  obtain ⟨i, hi, hx⟩ := m22T_sub x.2
  refine ⟨7, Subtype.ext (eq_of_permCode ?_)⟩
  rw [Subgroup.coe_pow, permCode_pow_two_pow, hx, Subgroup.coe_one, m22_code_one]
  exact m22_pow_check i hi

@[expose] def m22DP (j : ℕ) : Perm (Fin 22) := m22Word (m22DW.getD j [])

theorem permCode_m22DP {j : ℕ} (hj : j < 60) : permCode (m22DP j) = m22D j := by
  rw [m22DP, permCode_m22Word]
  exact m22_d_check j hj

theorem m22DP_zero : m22DP 0 = 1 := by
  rw [m22DP, m22_dw_zero]
  rfl

@[expose] def m22U : Set (Perm (Fin 22)) :=
  {x | ∃ j < 60, ∃ t ∈ m22T, ∃ t' ∈ m22T, x = t * m22DP j * t'}

theorem one_mem_m22U : (1 : Perm (Fin 22)) ∈ m22U :=
  ⟨0, by norm_num, 1, one_mem _, 1, one_mem _, by rw [m22DP_zero]; group⟩

theorem m22U_mul_T {x s : Perm (Fin 22)} (hx : x ∈ m22U) (hs : s ∈ m22T) : x * s ∈ m22U := by
  obtain ⟨j, hj, t, ht, t', ht', rfl⟩ := hx
  exact ⟨j, hj, t, ht, t' * s, mul_mem ht' hs, by group⟩

theorem m22U_mul_b {x : Perm (Fin 22)} (hx : x ∈ m22U) : x * m22PermB ∈ m22U := by
  obtain ⟨j, hj, t, ht, t', ht', rfl⟩ := hx
  obtain ⟨i, hi, hc⟩ := m22T_sub ht'
  obtain ⟨hk, heq⟩ := m22_dec_spec hj hi
  obtain ⟨u, hu, huc⟩ := m22T_sup (m22Dec j i / 128 % 128) (Nat.mod_lt _ (by norm_num))
  obtain ⟨v, hv, hvc⟩ := m22T_sup (m22Dec j i % 128) (Nat.mod_lt _ (by norm_num))
  have key : m22DP j * (t' * m22PermB) = u * m22DP (m22Dec j i / 16384) * v := by
    apply eq_of_permCode
    rw [permCode_mul22, permCode_mul22, permCode_mul22, permCode_mul22, permCode_m22DP hj, hc,
      m22_code_b, huc, hvc, permCode_m22DP hk]
    exact heq
  refine ⟨_, hk, t * u, mul_mem ht hu, v, hv, ?_⟩
  calc t * m22DP j * t' * m22PermB = t * (m22DP j * (t' * m22PermB)) := by group
    _ = t * (u * m22DP (m22Dec j i / 16384) * v) := by rw [key]
    _ = t * u * m22DP (m22Dec j i / 16384) * v := by group

theorem m22U_mul_a {x : Perm (Fin 22)} (hx : x ∈ m22U) : x * m22PermA ∈ m22U := by
  obtain ⟨u, hu, huc⟩ := m22T_sup 7 (by norm_num)
  obtain ⟨v, hv, hvc⟩ := m22T_sup 33 (by norm_num)
  have key : m22PermA = u * m22PermB * m22PermB * v := by
    apply eq_of_permCode
    rw [permCode_mul22, permCode_mul22, permCode_mul22, huc, hvc, m22_code_b, m22_code_a]
    exact m22_a_check.symm
  rw [key, ← mul_assoc, ← mul_assoc, ← mul_assoc]
  exact m22U_mul_T (m22U_mul_b (m22U_mul_b (m22U_mul_T hx hu))) hv

theorem m22_subset_U : (NativeSporadic.M22 : Set (Perm (Fin 22))) ⊆ m22U := by
  rw [m22_eq_closure]
  refine closure_subset_of_right_closed
    (fun s _ => ⟨orderOf s, orderOf_pos s, pow_orderOf_eq_one s⟩) one_mem_m22U ?_
  rintro p hp s (rfl | rfl)
  · exact m22U_mul_a hp
  · exact m22U_mul_b hp

theorem m22_good_of_mem {H : Subgroup (Perm (Fin 22))} (hTH : m22T ≤ H)
    (hp : ∀ p, p = 5 ∨ p = 7 ∨ p = 11 → ¬ p ∣ Nat.card H) {j : ℕ} (hj : 0 < j) (hj' : j < 58)
    (hD : m22DP j ∈ H) : False := by
  obtain ⟨hp', hi, hpow, hne⟩ := m22_bad_check j hj' hj
  obtain ⟨u, hu, huc⟩ := m22T_sup _ hi
  set p := m22Bad j % 16 with hpdef
  have hprime : p.Prime := by
    rcases hp' with h | h | h <;> rw [h] <;> norm_num
  have : Fact p.Prime := ⟨hprime⟩
  have hjD : j < 60 := by omega
  let x : H := ⟨m22DP j * u, mul_mem hD (hTH hu)⟩
  have hcode : permCode ((x : Perm (Fin 22))) = mul22 (m22D j) (m22Tel (m22Bad j / 16)) := by
    show permCode (m22DP j * u) = _
    rw [permCode_mul22, permCode_m22DP hjD, huc]
  have hxp : x ^ p = 1 := by
    apply Subtype.ext
    apply eq_of_permCode
    rw [Subgroup.coe_pow, permCode_pow, hcode, Subgroup.coe_one, m22_code_one]
    exact hpow
  have hx1 : x ≠ 1 := by
    intro h
    apply hne
    rw [← hcode, h, Subgroup.coe_one, m22_code_one]
  have hdvd : p ∣ Nat.card H := orderOf_eq_prime hxp hx1 ▸ orderOf_dvd_natCard x
  exact hp p hp' hdvd

theorem m22_card_le {H : Subgroup (Perm (Fin 22))} (hTH : m22T ≤ H)
    (hH : H ≤ NativeSporadic.M22) (hp : ∀ p, p = 5 ∨ p = 7 ∨ p = 11 → ¬ p ∣ Nat.card H) :
    Nat.card H ≤ 5 * Nat.card m22T := by
  obtain ⟨r₁, hr₁, hr₁c⟩ := m22T_sup 3 (by norm_num)
  obtain ⟨r₂, hr₂, hr₂c⟩ := m22T_sup 1 (by norm_num)
  obtain ⟨r₀, hr₀, hr₀c⟩ := m22T_sup 0 (by norm_num)
  have hr₀1 : r₀ = 1 := eq_of_permCode (by rw [hr₀c, m22_tel_zero, m22_code_one])
  let c : Fin 5 → Perm (Fin 22) := ![1, m22DP 58, r₁ * m22DP 58, m22DP 59, r₂ * m22DP 59]
  have hcov : ∀ h ∈ H, ∃ s : Fin 5, ∃ t ∈ m22T, h = c s * t := by
    intro h hh
    obtain ⟨j, hj, t, ht, t', ht', rfl⟩ := m22_subset_U (hH hh)
    have hD : m22DP j ∈ H := by
      have e : m22DP j = t⁻¹ * (t * m22DP j * t') * t'⁻¹ := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem (hTH ht)) hh) (inv_mem (hTH ht'))
    obtain ⟨i, hi, htc⟩ := m22T_sub ht
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact ⟨0, t * t', mul_mem ht ht', by rw [m22DP_zero]; simp [c]⟩
    rcases Nat.lt_or_ge j 58 with hj58 | hj58
    · exact (m22_good_of_mem hTH hp hj0 hj58 hD).elim
    rcases Nat.lt_or_ge j 59 with hj59 | hj59
    · have hj : j = 58 := by omega
      subst hj
      obtain ⟨hs, hcos⟩ := m22_cos58_check i hi
      obtain ⟨w, hw, hwc⟩ := m22T_sup _ (Nat.mod_lt (m22Cos58 i) (by norm_num))
      by_cases hs0 : m22Cos58 i / 128 = 0
      · rw [ite_eq_left hs0] at hcos
        have key : t * m22DP 58 = r₀ * m22DP 58 * w := by
          apply eq_of_permCode
          rw [permCode_mul22, permCode_mul22, permCode_mul22, htc, hr₀c, hwc,
            permCode_m22DP (by norm_num)]
          exact hcos
        refine ⟨1, w * t', mul_mem hw ht', ?_⟩
        rw [key, hr₀1]
        simp [c, mul_assoc]
      · rw [ite_eq_right hs0] at hcos
        have key : t * m22DP 58 = r₁ * m22DP 58 * w := by
          apply eq_of_permCode
          rw [permCode_mul22, permCode_mul22, permCode_mul22, htc, hr₁c, hwc,
            permCode_m22DP (by norm_num)]
          exact hcos
        refine ⟨2, w * t', mul_mem hw ht', ?_⟩
        rw [key]
        simp [c, mul_assoc]
    · have hj : j = 59 := by omega
      subst hj
      obtain ⟨hs, hcos⟩ := m22_cos59_check i hi
      obtain ⟨w, hw, hwc⟩ := m22T_sup _ (Nat.mod_lt (m22Cos59 i) (by norm_num))
      by_cases hs0 : m22Cos59 i / 128 = 0
      · rw [ite_eq_left hs0] at hcos
        have key : t * m22DP 59 = r₀ * m22DP 59 * w := by
          apply eq_of_permCode
          rw [permCode_mul22, permCode_mul22, permCode_mul22, htc, hr₀c, hwc,
            permCode_m22DP (by norm_num)]
          exact hcos
        refine ⟨3, w * t', mul_mem hw ht', ?_⟩
        rw [key, hr₀1]
        simp [c, mul_assoc]
      · rw [ite_eq_right hs0] at hcos
        have key : t * m22DP 59 = r₂ * m22DP 59 * w := by
          apply eq_of_permCode
          rw [permCode_mul22, permCode_mul22, permCode_mul22, htc, hr₂c, hwc,
            permCode_m22DP (by norm_num)]
          exact hcos
        refine ⟨4, w * t', mul_mem hw ht', ?_⟩
        rw [key]
        simp [c, mul_assoc]
  choose s t ht hst using fun h : H => hcov h h.2
  have hinj : Function.Injective fun h : H => ((s h, ⟨t h, ht h⟩) : Fin 5 × m22T) := by
    intro h h' e
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at e
    exact Subtype.ext ((hst h).trans (e.1 ▸ e.2 ▸ (hst h').symm))
  calc Nat.card H ≤ Nat.card (Fin 5 × m22T) := Nat.card_le_card_of_injective _ hinj
    _ = 5 * Nat.card m22T := by rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin]

@[expose] def carrierM22Equiv : NativeSporadic.Carrier .M22 ≃* ↥NativeSporadic.M22 :=
  MulEquiv.refl _

theorem noE9Config_m22 :
    NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M22) := by
  intro A _ _ L P T ⟨e⟩ hcfg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨H, S, hS, hSi, hSH, hH⟩ := E9Config.exists_model_sylow hcfg (e.trans carrierM22Equiv)
  have hT' : IsPGroup 2 (m22T.subgroupOf NativeSporadic.M22) :=
    m22T_isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe m22T_le).symm
  obtain ⟨Q, hQ⟩ := hT'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥NativeSporadic.M22) (hS.toSylow hSi) Q
  have hQS : ∀ x ∈ (Q : Subgroup ↥NativeSporadic.M22), (MulAut.conj g)⁻¹ x ∈ S := by
    intro x hx
    have hx' : x ∈ ((g • hS.toSylow hSi : Sylow 2 ↥NativeSporadic.M22) :
        Subgroup ↥NativeSporadic.M22) := by
      rw [hg]
      exact hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx'
    exact hx'
  have hcardS : Nat.card S = Nat.card (Q : Subgroup ↥NativeSporadic.M22) := by
    have := congrArg (fun R : Sylow 2 ↥NativeSporadic.M22 =>
      Nat.card (R : Subgroup ↥NativeSporadic.M22)) hg
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow] at this
    rw [← this, Subgroup.pointwise_smul_def]
    exact Nat.card_congr (S.equivMapOfInjective _ (MulAut.conj g).injective).toEquiv
  set H' := H.map (MulAut.conj g).toMonoidHom with hH'def
  have hH' : Nat.card H' = Nat.card H :=
    (Nat.card_congr (H.equivMapOfInjective _ (MulAut.conj g).injective).toEquiv).symm
  have hQH' : (Q : Subgroup ↥NativeSporadic.M22) ≤ H' := by
    intro x hx
    refine ⟨(MulAut.conj g)⁻¹ x, hSH (hQS x hx), ?_⟩
    change (MulAut.conj g) ((MulAut.conj g)⁻¹ x) = x
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  set H'' := H'.map NativeSporadic.M22.subtype with hH''def
  have hH'' : Nat.card H'' = Nat.card H' :=
    (Nat.card_congr (H'.equivMapOfInjective _ NativeSporadic.M22.subtype_injective).toEquiv).symm
  have hTH'' : m22T ≤ H'' := by
    intro x hx
    refine ⟨⟨x, m22T_le hx⟩, hQH' (hQ ?_), rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact hx
  have hH''M : H'' ≤ NativeSporadic.M22 := Subgroup.map_subtype_le H'
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS
  have hcard'' : Nat.card H'' = 9 * 2 ^ k := by rw [hH'', hH', hH, hk]
  have hle := m22_card_le hTH'' hH''M (fun p hp => hcard'' ▸ not_dvd_nine_mul_two_pow hp)
  have hT : Nat.card m22T ≤ Nat.card S := by
    rw [hcardS, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe m22T_le).toEquiv]
    exact Subgroup.card_le_of_le hQ
  have hpos : 0 < Nat.card S := Nat.card_pos
  rw [hcard'', ← hk] at hle
  omega

theorem orderThree_m22 :
    OrderThree fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M22) := by
  intro X _ ⟨e⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let x : ↥NativeSporadic.M22 := ⟨m22Word m22ThreeW, m22Word_mem _⟩
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    apply eq_of_permCode
    rw [Subgroup.coe_pow, permCode_pow, Subgroup.coe_one, m22_code_one]
    show powC m22oneC 3 (permCode (m22Word m22ThreeW)) = m22oneC
    rw [permCode_m22Word]
    exact m22_three_check.1
  have hx1 : x ≠ 1 := by
    intro h
    apply m22_three_check.2
    have := congrArg (fun y : ↥NativeSporadic.M22 => permCode (y : Perm (Fin 22))) h
    simp only [x, Subgroup.coe_one, m22_code_one, permCode_m22Word] at this
    exact this
  rw [Nat.card_congr (e.trans carrierM22Equiv).toEquiv, ← orderOf_eq_prime hx3 hx1]
  exact orderOf_dvd_natCard x

end CFSG.Quasithin.F134
