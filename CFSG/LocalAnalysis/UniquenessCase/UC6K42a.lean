module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K47d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UCK (fixV)

section GenNorm

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V]
  {E : Type} [CommGroup E] [Fintype E]

@[expose] noncomputable def nrmG (σ : E →* Module.End k V) : Module.End k V := ∑ e : E, σ e

theorem σ_mul_nrmG_uc6 (σ : E →* Module.End k V) (g : E) : σ g * nrmG σ = nrmG σ := by
  unfold nrmG
  rw [Finset.mul_sum]
  have := Fintype.sum_equiv (Equiv.mulLeft g) (fun e : E => σ (g * e)) (fun e : E => σ e)
    (fun e => rfl)
  rw [← this]
  exact Finset.sum_congr rfl fun e _ => (map_mul σ g e).symm

theorem nrmG_mul_σ_uc6 (σ : E →* Module.End k V) (g : E) : nrmG σ * σ g = nrmG σ := by
  unfold nrmG
  rw [Finset.sum_mul]
  have := Fintype.sum_equiv (Equiv.mulRight g) (fun e : E => σ (e * g)) (fun e : E => σ e)
    (fun e => rfl)
  rw [← this]
  exact Finset.sum_congr rfl fun e _ => (map_mul σ e g).symm

theorem nrmG_mul_nrmG_uc6 (σ : E →* Module.End k V) :
    nrmG σ * nrmG σ = (Fintype.card E : Module.End k V) * nrmG σ := by
  have h1 : nrmG σ * nrmG σ = nrmG σ * ∑ e : E, σ e := rfl
  rw [h1, Finset.mul_sum]
  simp only [nrmG_mul_σ_uc6, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem σ_comm_nrmG_uc6 (σ : E →* Module.End k V) (g : E) (v : V) :
    nrmG σ (σ g v) = σ g (nrmG σ v) := by
  have h1 := congrArg (fun f : Module.End k V => f v) (nrmG_mul_σ_uc6 σ g)
  have h2 := congrArg (fun f : Module.End k V => f v) (σ_mul_nrmG_uc6 σ g)
  simp only [Module.End.mul_apply] at h1 h2
  rw [h1, h2]

theorem T_comm_nrmG_uc6 (σ : E →* Module.End k V) (T : Module.End k V) (α : MulAut E)
    (hTα : ∀ e, T * σ e = σ (α e) * T) (v : V) : nrmG σ (T v) = T (nrmG σ v) := by
  unfold nrmG
  simp only [LinearMap.sum_apply]
  have h : ∀ e : E, σ (α e) (T v) = T (σ e v) := fun e => by
    have := congrArg (fun f : Module.End k V => f v) (hTα e)
    simpa using this.symm
  have h2 : ∑ e : E, σ e (T v) = ∑ e : E, σ (α e) (T v) :=
    (Fintype.sum_equiv α.toEquiv (fun e => σ (α e) (T v)) (fun e => σ e (T v)) (fun e => rfl)).symm
  rw [h2, map_sum]
  exact Finset.sum_congr rfl fun e _ => h e

theorem pow_mul_σ_gen_uc6 (σ : E →* Module.End k V) (T : Module.End k V) (α : MulAut E)
    (hTα : ∀ e, T * σ e = σ (α e) * T) (i : ℕ) (e : E) :
    T ^ i * σ e = σ ((α ^ i) e) * T ^ i := by
  induction i generalizing e with
  | zero => simp
  | succ i ih =>
    have e1 : (α ^ (i + 1)) e = α ((α ^ i) e) := by rw [pow_succ']; rfl
    calc T ^ (i + 1) * σ e = T * (T ^ i * σ e) := by rw [pow_succ', mul_assoc]
      _ = T * (σ ((α ^ i) e) * T ^ i) := by rw [ih]
      _ = (T * σ ((α ^ i) e)) * T ^ i := by rw [mul_assoc]
      _ = (σ (α ((α ^ i) e)) * T) * T ^ i := by rw [hTα]
      _ = σ (α ((α ^ i) e)) * T ^ (i + 1) := by rw [mul_assoc, pow_succ']
      _ = σ ((α ^ (i + 1)) e) * T ^ (i + 1) := by rw [e1]

theorem frobenius_identity_gen_uc6 (σ : E →* Module.End k V) (T : Module.End k V) (α : MulAut E)
    (r : ℕ) (hr : 0 < r) (hTα : ∀ e, T * σ e = σ (α e) * T)
    (hfix : ∀ i, 0 < i → i < r → ∀ y, (α ^ i) y = y → y = 1) :
    ∑ y : E, σ y * (∑ i ∈ Finset.range r, T ^ i) * σ y⁻¹ =
      (Fintype.card E : Module.End k V) + nrmG σ * (∑ i ∈ Finset.range r, T ^ i - 1) := by
  have hA : ∀ y : E, σ y * (∑ i ∈ Finset.range r, T ^ i) * σ y⁻¹ =
      ∑ i ∈ Finset.range r, σ (y * ((α ^ i) y)⁻¹) * T ^ i := by
    intro y
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    calc σ y * T ^ i * σ y⁻¹ = σ y * (T ^ i * σ y⁻¹) := by rw [mul_assoc]
      _ = σ y * (σ ((α ^ i) y⁻¹) * T ^ i) := by rw [pow_mul_σ_gen_uc6 σ T α hTα i y⁻¹]
      _ = σ (y * ((α ^ i) y)⁻¹) * T ^ i := by
        rw [map_inv (α ^ i) y, ← mul_assoc, ← map_mul]
  have hsum : ∑ y : E, σ y * (∑ i ∈ Finset.range r, T ^ i) * σ y⁻¹ =
      ∑ i ∈ Finset.range r, ∑ y : E, σ (y * ((α ^ i) y)⁻¹) * T ^ i := by
    rw [Finset.sum_congr rfl (fun y _ => hA y), Finset.sum_comm]
  have hB : ∀ i ∈ Finset.range r, ∑ y : E, σ (y * ((α ^ i) y)⁻¹) * T ^ i =
      if i = 0 then (Fintype.card E : Module.End k V) else nrmG σ * T ^ i := by
    intro i hi
    rw [← Finset.sum_mul]
    split_ifs with h0
    · subst h0
      simp only [pow_zero, MulAut.one_apply, mul_inv_cancel, map_one, mul_one, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    · have hbij := bijective_div_uc6 (α ^ i)
        (hfix i (Nat.pos_of_ne_zero h0) (Finset.mem_range.1 hi))
      rw [Function.Bijective.sum_comp hbij (fun u => σ u)]
      rfl
  rw [hsum, Finset.sum_congr rfl hB]
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [Finset.sum_range_succ' (fun i => if i = 0 then (Fintype.card E : Module.End k V)
      else nrmG σ * T ^ i), Finset.sum_range_succ' (fun i => T ^ i)]
  simp only [Nat.succ_ne_zero, if_false, if_true, pow_zero, add_sub_cancel_right]
  rw [Finset.mul_sum, add_comm]

theorem exists_fixed_vector_gen_uc6 (σ : E →* Module.End k V) (hE : (Fintype.card E : k) ≠ 0)
    (T : Module.End k V) (α : MulAut E) (r : ℕ) (hr : 0 < r) (hTr : T ^ r = 1)
    (hTα : ∀ e, T * σ e = σ (α e) * T)
    (hfix : ∀ i, 0 < i → i < r → ∀ y, (α ^ i) y = y → y = 1)
    (W : Submodule k V) (hWσ : ∀ e, ∀ w ∈ W, σ e w ∈ W) (hWT : ∀ w ∈ W, T w ∈ W)
    (hW0 : ∀ w ∈ W, nrmG σ w = 0) (hne : W ≠ ⊥) : ∃ a ∈ W, a ≠ 0 ∧ T a = a := by
  obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).1 hne
  obtain ⟨ND, hND⟩ : ∃ ND : Module.End k V, ND = ∑ i ∈ Finset.range r, T ^ i := ⟨_, rfl⟩
  have hmemT : ∀ i : ℕ, ∀ v ∈ W, (T ^ i) v ∈ W := by
    intro i
    induction i with
    | zero => intro v hv; simpa using hv
    | succ i ih =>
      intro v hv
      rw [pow_succ', Module.End.mul_apply]
      exact hWT _ (ih v hv)
  have hNDW : ∀ v ∈ W, ND v ∈ W := by
    intro v hv
    rw [hND, LinearMap.sum_apply]
    exact W.sum_mem fun i _ => hmemT i v hv
  have hTND : ∀ v, T (ND v) = ND v := by
    intro v
    have h1 : T * ND = ND := by
      have h1 : T * ∑ i ∈ Finset.range r, T ^ i = ∑ i ∈ Finset.range r, T ^ (i + 1) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => (pow_succ' T i).symm
      have h2 := Finset.sum_range_succ (fun i => T ^ i) r
      have h3 := Finset.sum_range_succ' (fun i => T ^ i) r
      rw [hTr] at h2
      simp only [pow_zero] at h3
      rw [hND, h1]
      exact (add_right_cancel (h2.symm.trans h3)).symm
    have := congrArg (fun f : Module.End k V => f v) h1
    simpa using this
  have hid := congrArg (fun f : Module.End k V => f w)
    (frobenius_identity_gen_uc6 σ T α r hr hTα hfix)
  rw [← hND] at hid
  simp only [LinearMap.sum_apply, Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply,
    LinearMap.sub_apply] at hid
  have hzero : nrmG σ (ND w - w) = 0 := hW0 _ (W.sub_mem (hNDW w hwW) hwW)
  rw [hzero, add_zero] at hid
  by_contra hcon
  push Not at hcon
  have hall : ∀ y : E, σ y (ND (σ y⁻¹ w)) = 0 := by
    intro y
    have hmem : ND (σ y⁻¹ w) ∈ W := hNDW _ (hWσ _ w hwW)
    have h0 : ND (σ y⁻¹ w) = 0 := by
      by_contra hne0
      exact hcon _ hmem hne0 (hTND _)
    rw [h0, map_zero]
  simp only [hall, Finset.sum_const_zero] at hid
  have h5 : (Fintype.card E : Module.End k V) w = (Fintype.card E : k) • w := by
    simp only [Module.End.natCast_apply]
    exact (Nat.cast_smul_eq_nsmul k _ w).symm
  rw [h5] at hid
  exact hw0 ((smul_eq_zero.1 hid.symm).resolve_left hE)

end GenNorm

section Abelian

variable {G : Type} [Group G] [Finite G] {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]

theorem mem_fixV_zpowers_uc6 (ρ : Representation (ZMod p) G V) (x : G) (v : V) :
    v ∈ fixV ρ (Subgroup.zpowers x) ↔ ρ x v = v := by
  refine ⟨fun h => h x (Subgroup.mem_zpowers x), fun hx a ha => ?_⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  clear ha
  induction n using Int.induction_on with
  | zero => simp
  | succ i ih => rw [zpow_add_one, map_mul, Module.End.mul_apply, hx, ih]
  | pred i ih =>
    have hinv : ρ x⁻¹ v = v := by
      have := congrArg (ρ x⁻¹) hx
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one] at this
      simpa using this.symm
    rw [zpow_sub_one, map_mul, Module.End.mul_apply, hinv, ih]

theorem abelian_false_uc6 [Fact p.Prime] (ρ : Representation (ZMod p) G V)
    (hρ : Function.Injective ρ) {q r : ℕ} (hq : q.Prime) (hpq : q ≠ p) (hr : r.Prime)
    (D : Subgroup G) (hD : Nat.card D = r) (hfix : fixV ρ D = ⊥) (Q : Subgroup G)
    (hQp : IsPGroup q Q) (hQne : Q ≠ ⊥) (hQab : IsMulCommutative ↥Q)
    (hDQ : D ≤ normalizer (Q : Set G)) (hcomm : ⁅D, Q⁆ = Q) : False := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨x, hxD, hxord⟩ := exists_generator_uc6 hr hD
  have hx0 : x ∈ D := hxD ▸ Subgroup.mem_zpowers x
  have hfpf := fixedPointFree_of_commutator_eq_uc6 hxD hQab hDQ hcomm
  have hxN : x ∈ normalizer (Q : Set G) := hDQ hx0
  have hxr : x ^ r = 1 := hxord ▸ pow_orderOf_eq_one x
  haveI : Fintype ↥Q := Fintype.ofFinite _
  letI : CommGroup ↥Q := IsMulCommutative.instCommGroup
  let σ : Representation (ZMod p) ↥Q V := ρ.comp Q.subtype
  let α : MulAut ↥Q := Q.normalizerMonoidHom ⟨x, hxN⟩
  have hαe : ∀ e : ↥Q, ((α e : ↥Q) : G) = x * (e : G) * x⁻¹ := fun e => rfl
  have hαr : α ^ r = 1 := by
    have h1 : (⟨x, hxN⟩ : normalizer (Q : Set G)) ^ r = 1 := Subtype.ext (by simpa using hxr)
    rw [show α = Q.normalizerMonoidHom ⟨x, hxN⟩ from rfl, ← map_pow, h1, map_one]
  have hTα : ∀ e : ↥Q, ρ x * σ e = σ (α e) * ρ x := fun e => by
    show ρ x * ρ (e : G) = ρ ((α e : ↥Q) : G) * ρ x
    rw [hαe, ← map_mul, ← map_mul]
    congr 1
    group
  have hfix1 : ∀ e : ↥Q, α e = e → e = 1 := fun e he => by
    have h1 : x * (e : G) * x⁻¹ = (e : G) := by
      have := congrArg Subtype.val he
      rwa [hαe] at this
    have h2 : x * (e : G) = (e : G) * x := by
      calc x * (e : G) = (x * (e : G) * x⁻¹) * x := by group
        _ = (e : G) * x := by rw [h1]
    exact Subtype.ext (hfpf e e.2 h2)
  have hfixi : ∀ i, 0 < i → i < r → ∀ y, (α ^ i) y = y → y = 1 := by
    intro i hi0 hir y hy
    apply hfix1
    obtain ⟨j, hj⟩ := exists_pow_pow_eq_uc6 α hr hαr hi0 hir
    have hall : ∀ n : ℕ, ((α ^ i) ^ n) y = y := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, hy]
    rw [← hj]
    exact hall j
  have hE : (Fintype.card ↥Q : ZMod p) ≠ 0 := by
    intro h
    have hdvd := (ZMod.natCast_eq_zero_iff (Fintype.card ↥Q) p).1 h
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQp
    rw [← Nat.card_eq_fintype_card, hn] at hdvd
    exact hpq (((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hq).1
      ((Fact.out : p.Prime).dvd_of_dvd_pow hdvd)).symm)
  let W : Submodule (ZMod p) V := LinearMap.ker (nrmG σ)
  have hWne : W ≠ ⊥ := by
    obtain ⟨e, he1⟩ : ∃ e : ↥Q, e ≠ 1 := by
      by_contra h
      push Not at h
      exact hQne (eq_bot_iff.2 fun y hy => Subgroup.mem_bot.2 (congrArg Subtype.val (h ⟨y, hy⟩)))
    have hσe : σ e ≠ 1 := fun h => he1 (hρ.comp Q.subtype_injective (by
      show ρ (Q.subtype e) = ρ (Q.subtype 1)
      have : σ e = σ 1 := by rw [h, map_one]
      exact this))
    obtain ⟨v, hv⟩ : ∃ v, σ e v ≠ v := by
      by_contra h
      push Not at h
      exact hσe (LinearMap.ext fun w => by simpa using h w)
    have hNN : ∀ w, nrmG σ (nrmG σ w) = (Fintype.card ↥Q : ZMod p) • nrmG σ w := by
      intro w
      have := congrArg (fun f : Module.End (ZMod p) V => f w) (nrmG_mul_nrmG_uc6 σ)
      simp only [Module.End.mul_apply, Module.End.natCast_apply] at this
      rw [this, Nat.cast_smul_eq_nsmul]
    obtain ⟨c, hc⟩ : ∃ c : ZMod p, c * (Fintype.card ↥Q : ZMod p) = 1 :=
      ⟨(Fintype.card ↥Q : ZMod p)⁻¹, inv_mul_cancel₀ hE⟩
    have hv'0 : nrmG σ (v - c • nrmG σ v) = 0 := by
      rw [map_sub, map_smul, hNN, smul_smul, hc, one_smul, sub_self]
    have hv'ne : v - c • nrmG σ v ≠ 0 := by
      intro h0
      have h1 : v = c • nrmG σ v := sub_eq_zero.1 h0
      apply hv
      have hfixN : σ e (nrmG σ v) = nrmG σ v := by
        have := congrArg (fun f : Module.End (ZMod p) V => f v) (σ_mul_nrmG_uc6 σ e)
        simpa using this
      calc σ e v = σ e (c • nrmG σ v) := by rw [← h1]
        _ = c • σ e (nrmG σ v) := map_smul _ _ _
        _ = c • nrmG σ v := by rw [hfixN]
        _ = v := h1.symm
    intro hbot
    have : v - c • nrmG σ v ∈ W := hv'0
    rw [hbot] at this
    exact hv'ne ((Submodule.mem_bot _).1 this)
  obtain ⟨a, haW, ha0, hTa⟩ := exists_fixed_vector_gen_uc6 σ hE (ρ x) α r hr.pos
    (by rw [← map_pow, hxr, map_one]) hTα hfixi W
    (fun e w hw => by
      show nrmG σ (σ e w) = 0
      rw [σ_comm_nrmG_uc6, show nrmG σ w = 0 from hw, map_zero])
    (fun w hw => by
      show nrmG σ (ρ x w) = 0
      have := T_comm_nrmG_uc6 σ (ρ x) α hTα w
      rw [this, show nrmG σ w = 0 from hw, map_zero])
    (fun w hw => hw) hWne
  have haD : a ∈ fixV ρ D := by
    rw [hxD]
    exact (mem_fixV_zpowers_uc6 ρ x a).2 hTa
  rw [hfix] at haD
  exact ha0 ((Submodule.mem_bot _).1 haD)

end Abelian

end CFSG.LocalAnalysis.UniquenessCase.UC6
