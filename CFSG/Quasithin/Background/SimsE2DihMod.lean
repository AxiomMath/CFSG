module

public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Vol2.Ch3E213MKer

public section

namespace CFSG.Quasithin.SimsE2

namespace Dih

theorem dParam_dvd_of_dvd {q m : ℕ} (h : q ∣ 2 ^ m - 1) : E2.dParam q ∣ m := by
  unfold E2.dParam
  apply orderOf_dvd_of_pow_eq_one
  have h1 : ((2 ^ m - 1 : ℕ) : ZMod q) = 0 := (CharP.cast_eq_zero_iff (ZMod q) q _).2 h
  rw [Nat.cast_sub Nat.one_le_two_pow] at h1
  push_cast at h1
  exact sub_eq_zero.1 h1

theorem two_mul_dParamPrime_le {q m : ℕ} (hd : E2.dParam q ∣ m) (h2 : 2 ∣ m) (hm : 0 < m) :
    2 * E2.dParamPrime q ≤ m := by
  unfold E2.dParamPrime
  split_ifs with hev
  · obtain ⟨k, hk⟩ := hev
    have hle := Nat.le_of_dvd hm hd
    rw [hk] at hle ⊢
    omega
  · have hcop : Nat.Coprime 2 (E2.dParam q) :=
      Nat.coprime_two_left.2 (Nat.not_even_iff_odd.1 hev)
    exact Nat.le_of_dvd hm (hcop.mul_dvd_of_dvd_of_dvd h2 hd)

variable {N : Type*} [Group N]

@[expose] def fixSub (σ : MulAut N) : Subgroup N where
  carrier := {x | σ x = x}
  mul_mem' {x y} hx hy := by
    have hx' : σ x = x := hx
    have hy' : σ y = y := hy
    change σ (x * y) = x * y
    rw [map_mul, hx', hy']
  one_mem' := map_one σ
  inv_mem' {x} hx := by
    have hx' : σ x = x := hx
    change σ x⁻¹ = x⁻¹
    rw [map_inv, hx']

theorem mem_fixSub {σ : MulAut N} {x : N} : x ∈ fixSub σ ↔ σ x = x := Iff.rfl

@[expose] def commHom (hc : ∀ x y : N, x * y = y * x) (σ : MulAut N) : N →* N where
  toFun x := x⁻¹ * σ x
  map_one' := by rw [inv_one, map_one, one_mul]
  map_mul' x y := by
    change (x * y)⁻¹ * σ (x * y) = x⁻¹ * σ x * (y⁻¹ * σ y)
    calc (x * y)⁻¹ * σ (x * y) = x⁻¹ * (y⁻¹ * σ x) * σ y := by
          rw [map_mul, mul_inv_rev, hc y⁻¹ x⁻¹]
          simp only [mul_assoc]
      _ = x⁻¹ * σ x * (y⁻¹ * σ y) := by
          rw [hc y⁻¹ (σ x)]
          simp only [mul_assoc]

theorem commHom_apply (hc : ∀ x y : N, x * y = y * x) (σ : MulAut N) (x : N) :
    commHom hc σ x = x⁻¹ * σ x := rfl

theorem card_le_sq_card_fixSub [Finite N] (hc : ∀ x y : N, x * y = y * x)
    (hsq : ∀ x : N, x * x = 1) {s : MulAut N} (hs : s * s = 1) {U : Subgroup N}
    (hU : ∀ u ∈ U, s u ∈ U) : Nat.card U ≤ Nat.card ↥(U ⊓ fixSub s) ^ 2 := by
  set φ : ↥U →* N := (commHom hc s).comp U.subtype with hφ
  have hss : ∀ x : N, s (s x) = x := fun x => by
    rw [← MulAut.mul_apply, hs, MulAut.one_apply]
  have hinv : ∀ x : N, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hsq x)
  have hker : Nat.card φ.ker ≤ Nat.card ↥(U ⊓ fixSub s) := by
    rw [← Subgroup.card_map_of_injective (K := φ.ker) U.subtype_injective]
    apply Subgroup.card_le_of_le
    rintro _ ⟨u, hu, rfl⟩
    have hu' : (u : N)⁻¹ * s u = 1 := hu
    exact ⟨u.2, (inv_mul_eq_one.1 hu').symm⟩
  have hrange : Nat.card φ.range ≤ Nat.card ↥(U ⊓ fixSub s) := by
    apply Subgroup.card_le_of_le
    intro y hy
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 hy
    have e : φ u = (u : N)⁻¹ * s u := rfl
    rw [e]
    refine ⟨U.mul_mem (U.inv_mem u.2) (hU u u.2), ?_⟩
    show s ((u : N)⁻¹ * s u) = (u : N)⁻¹ * s u
    rw [map_mul, map_inv, hss, hinv (s u), hinv (u : N)]
    exact hc _ _
  have hcard : Nat.card φ.ker * Nat.card φ.range = Nat.card U := by
    rw [← Subgroup.index_ker]
    exact Subgroup.card_mul_index φ.ker
  calc Nat.card U = Nat.card φ.ker * Nat.card φ.range := hcard.symm
    _ ≤ Nat.card ↥(U ⊓ fixSub s) * Nat.card ↥(U ⊓ fixSub s) := Nat.mul_le_mul hker hrange
    _ = Nat.card ↥(U ⊓ fixSub s) ^ 2 := (sq _).symm

theorem card_mul_card_le {H K U : Subgroup N} [Finite U] (hHU : H ≤ U) (hKU : K ≤ U)
    (hHK : H ⊓ K = ⊥) : Nat.card H * Nat.card K ≤ Nat.card U := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun x : ↥H × ↥K => (⟨(x.1 : N) * x.2, U.mul_mem (hHU x.1.2) (hKU x.2.2)⟩ : U)) ?_
  rintro ⟨h₁, k₁⟩ ⟨h₂, k₂⟩ heq
  have heq' : (h₁ : N) * k₁ = h₂ * k₂ := congrArg Subtype.val heq
  have hmem : (h₂ : N)⁻¹ * h₁ ∈ H ⊓ K := by
    refine ⟨H.mul_mem (H.inv_mem h₂.2) h₁.2, ?_⟩
    have e : (h₂ : N)⁻¹ * h₁ = k₂ * (k₁ : N)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← heq', mul_inv_cancel_right]
    rw [e]
    exact K.mul_mem k₂.2 (K.inv_mem k₁.2)
  rw [hHK, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  have hk : (k₁ : N) = k₂ := by
    rw [hmem] at heq'
    exact mul_left_cancel heq'
  exact Prod.ext (Subtype.ext hmem.symm) (Subtype.ext hk)

theorem pow_apply_mem {γ : MulAut N} {U : Subgroup N} (hU : ∀ u ∈ U, γ u ∈ U) (n : ℕ) :
    ∀ u ∈ U, (γ ^ n) u ∈ U := by
  induction n with
  | zero => intro u hu; simpa using hu
  | succ n ih =>
    intro u hu
    rw [pow_succ', MulAut.mul_apply]
    exact hU _ (ih u hu)

theorem pow_apply_eq {γ : MulAut N} {x : N} (hx : γ x = x) (n : ℕ) : (γ ^ n) x = x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, hx]

theorem dvd_card_sub_one [Finite N] {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) {γ : MulAut N}
    (hγ : orderOf γ = p ^ a) {U : Subgroup N} (hU : ∀ u ∈ U, γ u ∈ U)
    (hfree : U ⊓ fixSub (γ ^ p ^ (a - 1)) = ⊥) : p ^ a ∣ Nat.card U - 1 := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hfree
  have hfo : IsOfFinOrder γ := by
    rw [← orderOf_pos_iff, hγ]
    exact pow_pos hp.pos _
  have hK : ∀ k ∈ Subgroup.zpowers γ, ∀ u ∈ U, k u ∈ U := by
    intro k hk u hu
    obtain ⟨n, rfl⟩ := hfo.mem_powers_iff_mem_zpowers.2 hk
    exact pow_apply_mem hU n u hu
  set K := Subgroup.zpowers γ with hKdef
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [Nat.card_zpowers, hγ]
    exact pow_ne_zero _ hp.ne_zero)
  letI act : MulAction K U :=
    { smul := fun k u => ⟨(k : MulAut N) u, hK k k.2 u u.2⟩
      one_smul := fun u => rfl
      mul_smul := fun k k' u => rfl }
  have hsmul : ∀ (k : K) (u : U), ((k • u : U) : N) = (k : MulAut N) u := fun k u => rfl
  have hC : ∀ k : K, ∀ x ∈ ({1} : Set U), k • x ∈ ({1} : Set U) := by
    intro k x hx
    rw [Set.mem_singleton_iff] at hx ⊢
    subst hx
    exact Subtype.ext (by rw [hsmul]; exact map_one _)
  have hfix : ∀ k : K, k ≠ 1 → ∀ x : U, k • x = x → x ∈ ({1} : Set U) := by
    intro k hk x hkx
    have hk' : (k : MulAut N) ≠ 1 := fun h => hk (Subtype.ext h)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp
      (Ch3E213M.pow_mem_zpowers_of_ne_one hp hγ k.2 hk')
    have hkx' : (k : MulAut N) ∈ MulAction.stabilizer (MulAut N) (x : N) := by
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      have := congrArg Subtype.val hkx
      rwa [hsmul] at this
    have h1 := (MulAction.stabilizer (MulAut N) (x : N)).zpow_mem hkx' j
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, hj] at h1
    have h2 : (x : N) ∈ U ⊓ fixSub (γ ^ p ^ b) := ⟨x.2, h1⟩
    rw [hfree, Subgroup.mem_bot] at h2
    exact Set.mem_singleton_iff.2 (Subtype.ext h2)
  have h := Ch3E213M.card_dvd_card_sub_of_fixed_subset hC hfix
  rwa [Nat.card_zpowers, hγ, Nat.card_coe_set_eq, Set.ncard_singleton] at h

theorem two_pow_le_card_of_free [Finite N] (hc : ∀ x y : N, x * y = y * x)
    (hsq : ∀ x : N, x * x = 1) {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) {γ τ : MulAut N}
    (hγ : orderOf γ = p ^ a) (hτ : τ * τ = 1) (hτγ : τ * γ * τ⁻¹ = γ⁻¹) {U : Subgroup N}
    (hU1 : U ≠ ⊥) (hγU : ∀ u ∈ U, γ u ∈ U) (hτU : ∀ u ∈ U, τ u ∈ U)
    (hfree : U ⊓ fixSub (γ ^ p ^ (a - 1)) = ⊥) :
    2 ^ (2 * E2.dParamPrime (p ^ a)) ≤ Nat.card U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2N : IsPGroup 2 N := fun x => ⟨1, by rw [pow_one, pow_two]; exact hsq x⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (h2N.to_subgroup U)
  have hdvd := dvd_card_sub_one hp ha hγ hγU hfree
  rw [hm] at hdvd
  have hd : E2.dParam (p ^ a) ∣ m := dParam_dvd_of_dvd hdvd
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  have hτγ2 : (τ * γ) * (τ * γ) = 1 := by
    have e : (τ * γ) * (τ * γ) = (τ * γ * τ⁻¹) * γ := by
      rw [hτinv]
      simp only [mul_assoc]
    rw [e, hτγ, inv_mul_cancel]
  have hτγU : ∀ u ∈ U, (τ * γ) u ∈ U := fun u hu => by
    rw [MulAut.mul_apply]
    exact hτU _ (hγU u hu)
  have h1 := card_le_sq_card_fixSub hc hsq hτ hτU
  have h2 := card_le_sq_card_fixSub hc hsq hτγ2 hτγU
  have hF : (U ⊓ fixSub τ) ⊓ (U ⊓ fixSub (τ * γ)) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨hxU, hx1⟩, -, hx2⟩
    replace hx1 : τ x = x := hx1
    replace hx2 : τ (γ x) = x := hx2
    have hγx : γ x = x := by
      calc γ x = (τ * τ) (γ x) := by rw [hτ, MulAut.one_apply]
        _ = τ (τ (γ x)) := by rw [MulAut.mul_apply]
        _ = x := by rw [hx2, hx1]
    have hx : x ∈ U ⊓ fixSub (γ ^ p ^ (a - 1)) := ⟨hxU, pow_apply_eq hγx _⟩
    rwa [hfree] at hx
  have h3 := card_mul_card_le (inf_le_left : U ⊓ fixSub τ ≤ U)
    (inf_le_left : U ⊓ fixSub (τ * γ) ≤ U) hF
  obtain ⟨f₁, hf₁⟩ := IsPGroup.iff_card.mp (h2N.to_subgroup (U ⊓ fixSub τ))
  obtain ⟨f₂, hf₂⟩ := IsPGroup.iff_card.mp (h2N.to_subgroup (U ⊓ fixSub (τ * γ)))
  rw [hm, hf₁, ← pow_mul] at h1
  rw [hm, hf₂, ← pow_mul] at h2
  rw [hm, hf₁, hf₂, ← pow_add] at h3
  have e1 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h1
  have e2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2
  have e3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h3
  have hm2 : 2 ∣ m := ⟨f₁, by omega⟩
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hm
      exact hU1 (Subgroup.card_eq_one.1 hm)
    · exact h0
  rw [hm]
  exact Nat.pow_le_pow_right (by norm_num) (two_mul_dParamPrime_le hd hm2 hm0)

theorem two_pow_le_card [Finite N] (hc : ∀ x y : N, x * y = y * x) (hsq : ∀ x : N, x * x = 1)
    {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 1 ≤ a) {γ τ : MulAut N}
    (hγ : orderOf γ = p ^ a) (hτ : τ * τ = 1) (hτγ : τ * γ * τ⁻¹ = γ⁻¹) :
    2 ^ (2 * E2.dParamPrime (p ^ a)) ≤ Nat.card N := by
  set γ₀ := γ ^ p ^ (a - 1) with hγ₀
  set U := (commHom hc γ₀).range with hUdef
  have hγ₀p : γ₀ ^ p = 1 := by
    rw [hγ₀, ← pow_mul, ← pow_succ, Nat.sub_add_cancel ha, ← hγ, pow_orderOf_eq_one]
  have hγ₀1 : γ₀ ≠ 1 := by
    refine pow_ne_one_of_lt_orderOf (pow_ne_zero _ hp.ne_zero) ?_
    rw [hγ]
    exact Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hU1 : U ≠ ⊥ := by
    intro hU
    apply hγ₀1
    ext x
    have hx : commHom hc γ₀ x ∈ U := MonoidHom.mem_range.2 ⟨x, rfl⟩
    rw [hU, Subgroup.mem_bot, commHom_apply, inv_mul_eq_one] at hx
    rw [MulAut.one_apply]
    exact hx.symm
  have hγU : ∀ u ∈ U, γ u ∈ U := by
    intro u hu
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hu
    refine MonoidHom.mem_range.2 ⟨γ x, ?_⟩
    have hcomm : γ * γ₀ = γ₀ * γ := (Commute.self_pow γ _).eq
    rw [commHom_apply, commHom_apply, map_mul, map_inv, ← MulAut.mul_apply, ← hcomm,
      MulAut.mul_apply]
  have hτγ₀ : τ * γ₀ * τ⁻¹ = γ₀⁻¹ := by
    rw [hγ₀, ← conj_pow, hτγ, inv_pow]
  have hτU : ∀ u ∈ U, τ u ∈ U := by
    intro u hu
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hu
    have e : τ (γ₀ x) = γ₀⁻¹ (τ x) := by
      rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← hτγ₀, inv_mul_cancel_right]
    have key : τ (commHom hc γ₀ x) = (commHom hc γ₀ (γ₀⁻¹ (τ x)))⁻¹ := by
      rw [commHom_apply, commHom_apply, map_mul, map_inv, e, MulAut.apply_inv_self, mul_inv_rev,
        inv_inv]
    rw [key]
    exact U.inv_mem (MonoidHom.mem_range.2 ⟨_, rfl⟩)
  have hfree : U ⊓ fixSub γ₀ = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvU, hv⟩
    replace hv : γ₀ v = v := hv
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hvU
    rw [Subgroup.mem_bot]
    set v := commHom hc γ₀ x with hvdef
    have hxv : γ₀ x = x * v := by rw [hvdef, commHom_apply, mul_inv_cancel_left]
    have hpow : ∀ n : ℕ, (γ₀ ^ n) x = x * v ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hxv, hv, pow_succ',
          mul_assoc]
    have hvp : v ^ p = 1 := by
      have := hpow p
      rw [hγ₀p, MulAut.one_apply] at this
      exact (mul_eq_left.1 this.symm)
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    have hv2 : v ^ 2 = 1 := by rw [pow_two]; exact hsq v
    rw [hk, pow_succ, pow_mul, hv2, one_pow, one_mul] at hvp
    exact hvp
  exact (two_pow_le_card_of_free hc hsq hp ha hγ hτ hτγ hU1 hγU hτU hfree).trans
    (Subgroup.card_le_card_group U)

end Dih

end CFSG.Quasithin.SimsE2
