module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.FixedRankModules
public import CFSG.RankThree.PartOne.S9.MinTwoAction.FixedRankFrattini
import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
public import CFSG.GroupTheory.FrattiniQuotient

public section

open scoped commutatorElement IsMulCommutative

namespace CFSG.RankThree.PartOne.FixedRank36

open CFSG SemidirectProduct

section Helpers

theorem natCast_ne_zero_zmod {q n : ℕ} (hq : q.Prime) (hn : n.Prime) (h : q ≠ n) :
    (n : ZMod q) ≠ 0 := by
  intro h0
  rw [ZMod.natCast_eq_zero_iff] at h0
  exact h ((Nat.prime_dvd_prime_iff_eq hq hn).1 h0)

theorem isPGroup_zpowers_two {M : Type*} [Group M] {x : M} {n : ℕ} (hx : x ^ 2 ^ n = 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  rintro ⟨g, hg⟩
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  refine ⟨n, Subtype.ext ?_⟩
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem isPGroup_zpowers_map {S M : Type*} [Group S] [Group M] (hS : IsPGroup 2 S)
    (f : S →* M) (s : S) : IsPGroup 2 (Subgroup.zpowers (f s)) := by
  obtain ⟨k, hk⟩ := hS s
  refine isPGroup_zpowers_two (n := k) ?_
  rw [← map_pow, hk, map_one]

end Helpers


section Module

variable {q : ℕ} [hq : Fact q.Prime] {P : Type*} [Group P] [Finite P]
  {S A : Type*} [Group S] [Finite S] [Group A] [Finite A]
  {φ : A →* MulAut S} {z : S} {a₀ : A}

theorem core_module (hq2 : q ≠ 2) (hq5 : q ≠ 5) [IsElementaryAbelian q (P ⧸ frattini P)]
    (hPq : IsPGroup q P) (hexp : ∀ x : P, x ^ q = 1) (hclass : commutator P ≤ Subgroup.center P)
    (hD : SAData S A φ z a₀) (ρ : S ⋊[φ] A →* MulAut P)
    (hfaith : ∀ s : S, ρ (inl s) = 1 → s = 1)
    (hrank : ∀ s : S, s ≠ 1 → CFSG.pRank q ↥(fixedSub (ρ (inl s))) ≤ 2) :
    IsMinInv (frattiniRep q ρ) ⊤ ∧ frattiniRep q ρ (inl z) = -1 ∧
      Module.finrank (ZMod q) (Additive (P ⧸ frattini P)) = 4 ∧
      ∀ s : S, s ∉ Subgroup.center S → orderOf s = 2 →
        Module.finrank (ZMod q) (Module.End.eigenspace (frattiniRep q ρ (inl s)) 1) = 2 := by
  have h2 : (2 : ZMod q) ≠ 0 := by
    have := natCast_ne_zero_zmod hq.out Nat.prime_two hq2
    exact_mod_cast this
  have h5 : (5 : ZMod q) ≠ 0 := by
    have := natCast_ne_zero_zmod hq.out (by norm_num : Nat.Prime 5) hq5
    exact_mod_cast this
  have : FiniteDimensional (ZMod q) (Additive (P ⧸ frattini P)) := Module.Finite.of_finite
  refine module_core h2 h5 hD (frattiniRep q ρ) ?_ ?_
  · intro h
    have h1 := frattiniRep_eq_one hPq hq2 ρ (inl z) (isPGroup_zpowers_map hD.ext.1 (ρ.comp inl) z) h
    exact hD.ne_one (hfaith z h1)
  · intro s hs1
    exact finrank_fixed_le hPq hq2 hexp hclass ρ (inl s)
      (isPGroup_zpowers_map hD.ext.1 (ρ.comp inl) s) (hrank s hs1)

end Module


section Restrict

variable {L P : Type*} [Group L] [Group P]

@[expose] def restrictAutHom (ρ : L →* MulAut P) (U : Subgroup P)
    (hU : ∀ (l : L) (x : P), x ∈ U ↔ ρ l x ∈ U) : L →* MulAut U where
  toFun l :=
    { toFun := fun x => ⟨ρ l x, (hU l x).1 x.2⟩
      invFun := fun x => ⟨ρ l⁻¹ x, (hU l⁻¹ x).1 x.2⟩
      left_inv := fun x => Subtype.ext (by
        show ρ l⁻¹ (ρ l x) = x
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl)
      right_inv := fun x => Subtype.ext (by
        show ρ l (ρ l⁻¹ x) = x
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl)
      map_mul' := fun x y => Subtype.ext (map_mul (ρ l) _ _) }
  map_one' := MulEquiv.ext fun x => Subtype.ext (by
    show ρ 1 x = x
    rw [map_one]
    rfl)
  map_mul' l l' := MulEquiv.ext fun x => Subtype.ext (by
    show ρ (l * l') x = ρ l (ρ l' x)
    rw [map_mul]
    rfl)

theorem restrictAutHom_apply (ρ : L →* MulAut P) (U : Subgroup P)
    (hU : ∀ (l : L) (x : P), x ∈ U ↔ ρ l x ∈ U) (l : L) (x : U) :
    ((restrictAutHom ρ U hU l x : U) : P) = ρ l x := rfl

theorem mem_iff_of_characteristic (U : Subgroup P) [U.Characteristic] (σ : MulAut P) (x : P) :
    x ∈ U ↔ σ x ∈ U := by
  have h := Subgroup.characteristic_iff_map_eq.1 (inferInstance : U.Characteristic) σ
  constructor
  · intro hx
    rw [← h]
    exact Subgroup.mem_map_of_mem _ hx
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
    have : y = x := σ.injective hyx
    rwa [this] at hy

end Restrict

section Ranks

variable {q : ℕ} {P : Type*} [Group P]

theorem isElementaryAbelian_of_comm (hexp : ∀ x : P, x ^ q = 1) (E : Subgroup P)
    (hE : IsMulCommutative E) : IsElementaryAbelian q E :=
  { toIsMulCommutative := hE
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
      Subtype.ext (by rw [Subgroup.coe_pow, hexp, Subgroup.coe_one]) }

theorem le_pRank_of_elem {p : ℕ} (hp : 1 < p) {H : Type*} [Group H] [Finite H] {E : Subgroup H}
    (hE : IsElementaryAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) : k ≤ CFSG.pRank p H := by
  refine le_csSup ⟨Nat.card H, ?_⟩ ⟨E, hE, hk⟩
  rintro r ⟨B, -, hB⟩
  calc r ≤ p ^ r := (Nat.lt_pow_self hp).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card H := Subgroup.card_le_card_group B

theorem le_pRank_fixedSub [Finite P] (hq : 1 < q) (hexp : ∀ x : P, x ^ q = 1) (σ : MulAut P)
    {E : Subgroup P} (hE : IsMulCommutative E) (hEσ : ∀ x ∈ E, σ x = x) {k : ℕ}
    (hk : Nat.card E = q ^ k) : k ≤ CFSG.pRank q ↥(fixedSub σ) := by
  have hle : E ≤ fixedSub σ := hEσ
  have hcomm : IsMulCommutative (E.subgroupOf (fixedSub σ)) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    apply (Subgroup.subgroupOfEquivOfLe hle).injective
    rw [map_mul, map_mul]
    exact hE.is_comm.comm _ _
  have hE' : IsElementaryAbelian q (E.subgroupOf (fixedSub σ)) :=
    { toIsMulCommutative := hcomm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (Subtype.ext (by
          rw [Subgroup.coe_pow, Subgroup.coe_pow, hexp, Subgroup.coe_one, Subgroup.coe_one])) }
  refine le_pRank_of_elem hq hE' ?_
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hk]

end Ranks


section Sub

variable {q : ℕ} [hq : Fact q.Prime] {P : Type*} [Group P] [Finite P]

@[expose] def subgroupOfSubmodule (U : Subgroup P) [IsElementaryAbelian q U]
    (C : Submodule (ZMod q) (Additive U)) : Subgroup P where
  carrier := {x | ∃ h : x ∈ U, Additive.ofMul (⟨x, h⟩ : U) ∈ C}
  one_mem' := ⟨U.one_mem, by
    show Additive.ofMul (1 : U) ∈ C
    rw [ofMul_one]
    exact C.zero_mem⟩
  mul_mem' := by
    rintro x y ⟨hx, hxC⟩ ⟨hy, hyC⟩
    refine ⟨U.mul_mem hx hy, ?_⟩
    show Additive.ofMul ((⟨x, hx⟩ : U) * ⟨y, hy⟩) ∈ C
    rw [ofMul_mul]
    exact C.add_mem hxC hyC
  inv_mem' := by
    rintro x ⟨hx, hxC⟩
    refine ⟨U.inv_mem hx, ?_⟩
    show Additive.ofMul ((⟨x, hx⟩ : U)⁻¹) ∈ C
    rw [ofMul_inv]
    exact C.neg_mem hxC

omit [Finite P] in
theorem subgroupOfSubmodule_le (U : Subgroup P) [IsElementaryAbelian q U]
    (C : Submodule (ZMod q) (Additive U)) : subgroupOfSubmodule U C ≤ U :=
  fun _ hx => hx.1

theorem card_subgroupOfSubmodule (U : Subgroup P) [IsElementaryAbelian q U]
    (C : Submodule (ZMod q) (Additive U)) :
    Nat.card (subgroupOfSubmodule U C) = q ^ Module.finrank (ZMod q) C := by
  have e : subgroupOfSubmodule U C ≃ C :=
    { toFun := fun x => ⟨Additive.ofMul (⟨x.1, x.2.1⟩ : U), x.2.2⟩
      invFun := fun c => ⟨(Additive.toMul c.1 : U).1, (Additive.toMul c.1 : U).2, by simp⟩
      left_inv := fun x => rfl
      right_inv := fun c => rfl }
  rw [Nat.card_congr e]
  have : Fintype C := Fintype.ofFinite _
  have hpow := Module.card_eq_pow_finrank (K := ZMod q) (V := C)
  rw [ZMod.card, ← Nat.card_eq_fintype_card] at hpow
  exact hpow

theorem finrank_le_pRank_fixedSub (hexp : ∀ x : P, x ^ q = 1) (U : Subgroup P)
    [IsElementaryAbelian q U] (hU : U ≤ Subgroup.center P) (σ : MulAut P)
    (C : Submodule (ZMod q) (Additive U))
    (hC : ∀ c ∈ C, σ ((Additive.toMul c : U) : P) = ((Additive.toMul c : U) : P)) :
    Module.finrank (ZMod q) C ≤ CFSG.pRank q ↥(fixedSub σ) := by
  have hcomm : IsMulCommutative (subgroupOfSubmodule U C) :=
    ⟨⟨fun a b => Subtype.ext
      ((Subgroup.mem_center_iff.1 (hU (subgroupOfSubmodule_le U C a.2)) b).symm)⟩⟩
  refine le_pRank_fixedSub hq.out.one_lt hexp σ hcomm ?_ (card_subgroupOfSubmodule U C)
  rintro x ⟨hx, hxC⟩
  exact hC _ hxC

theorem finrank_succ_le_pRank_fixedSub (hexp : ∀ x : P, x ^ q = 1) (U : Subgroup P)
    [IsElementaryAbelian q U] (hU : U ≤ Subgroup.center P) (σ : MulAut P)
    (C : Submodule (ZMod q) (Additive U))
    (hC : ∀ c ∈ C, σ ((Additive.toMul c : U) : P) = ((Additive.toMul c : U) : P)) {x : P}
    (hx : σ x = x) (hxU : x ∉ U) :
    Module.finrank (ZMod q) C + 1 ≤ CFSG.pRank q ↥(fixedSub σ) := by
  set E := subgroupOfSubmodule U C with hE
  have hEU : E ≤ U := subgroupOfSubmodule_le U C
  have hcomm : IsMulCommutative E :=
    ⟨⟨fun a b => Subtype.ext
      ((Subgroup.mem_center_iff.1 (hU (hEU a.2)) b).symm)⟩⟩
  have hxE : x ∉ E := fun h => hxU (hEU h)
  obtain ⟨hcomm', hcard⟩ := CFSG.RankThree.PartTwo.sup_zpowers_card hcomm hxE (hexp x)
    (fun a ha => (Subgroup.mem_center_iff.1 (hU (hEU ha)) x).symm)
  refine le_pRank_fixedSub hq.out.one_lt hexp σ hcomm' ?_
    (k := Module.finrank (ZMod q) C + 1) ?_
  · intro y hy
    have hle : E ⊔ Subgroup.zpowers x ≤ fixedSub σ := by
      refine sup_le ?_ ?_
      · rintro w ⟨hw, hwC⟩
        exact hC _ hwC
      · rw [Subgroup.zpowers_le]
        exact hx
    exact hle hy
  · rw [hcard, hE, card_subgroupOfSubmodule U C, pow_succ]

end Sub


section Lift

variable {q : ℕ} [hq : Fact q.Prime] {P : Type*} [Group P] [Finite P] {L : Type*} [Group L]

theorem exists_fixed_not_mem_frattini [IsElementaryAbelian q (P ⧸ frattini P)] (hPq : IsPGroup q P)
    (hq2 : q ≠ 2) (ρ : L →* MulAut P) (l : L) (hl : IsPGroup 2 (Subgroup.zpowers (ρ l)))
    (hpos : 0 < Module.finrank (ZMod q) (Module.End.eigenspace (frattiniRep q ρ l) 1)) :
    ∃ x : P, ρ l x = x ∧ x ∉ frattini P := by
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  obtain ⟨x, hx, hxv⟩ := exists_fixed_lift hPq hq2 ρ l hl v.1 v.2
  refine ⟨x, hx, fun hxf => hv ?_⟩
  apply Subtype.ext
  rw [← hxv]
  show Additive.ofMul (x : P ⧸ frattini P) = 0
  rw [(QuotientGroup.eq_one_iff x).2 hxf]
  rfl

end Lift

section Commutator

variable {q : ℕ} [hq : Fact q.Prime] {P : Type*} [Group P] [Finite P]
  {S A : Type*} [Group S] [Finite S] [Group A] [Finite A]
  {φ : A →* MulAut S} {z : S} {a₀ : A}

omit [Finite S] [Finite A] in
theorem exists_inl_mul (g : S ⋊[φ] A) (s : S) : ∃ s' : S, g * inl s = inl s' * g :=
  ⟨g.left * φ g.right s * g.left⁻¹, by
    apply SemidirectProduct.ext
    · simp [mul_assoc]
    · simp⟩

theorem eq_zero_of_mem_span_of_fixed {K : Type*} [Field K] {E : Type*} [AddCommGroup E]
    [Module K E] (h32 : (Nat.card S : K) ≠ 0) (τ : S →* Module.End K E) {v : E}
    (hv : v ∈ Submodule.span K {w | ∃ (s : S) (e : E), w = τ s e - e})
    (hfix : ∀ s : S, τ s v = v) : v = 0 := by
  classical
  have : Fintype S := Fintype.ofFinite S
  have hsum : ∀ w ∈ Submodule.span K {w | ∃ (s : S) (e : E), w = τ s e - e},
      ∑ s : S, τ s w = 0 := by
    intro w hw
    refine Submodule.span_induction (p := fun w _ => ∑ s : S, τ s w = 0) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨s₀, e, rfl⟩
      rw [Finset.sum_congr rfl fun s _ => map_sub (τ s) (τ s₀ e) e]
      rw [Finset.sum_sub_distrib, sub_eq_zero]
      refine Fintype.sum_equiv (Equiv.mulRight s₀) _ _ fun s => ?_
      show τ s (τ s₀ e) = τ (s * s₀) e
      rw [map_mul]
      rfl
    · simp
    · intro x y _ _ hx hy
      rw [Finset.sum_congr rfl fun s _ => map_add (τ s) x y, Finset.sum_add_distrib, hx, hy,
        add_zero]
    · intro c x _ hx
      rw [Finset.sum_congr rfl fun s _ => map_smul (τ s) c x, ← Finset.smul_sum, hx, smul_zero]
  have h1 := hsum v hv
  rw [Finset.sum_congr rfl fun s _ => hfix s, Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card] at h1
  have h2 : (Nat.card S : K) • v = 0 := by
    rw [Nat.cast_smul_eq_nsmul]
    exact h1
  exact (smul_eq_zero.1 h2).resolve_left h32


theorem commutator_fixed [IsElementaryAbelian q (P ⧸ frattini P)]
    [IsElementaryAbelian q (commutator P)] (hq2 : q ≠ 2) (hPq : IsPGroup q P)
    (hexp : ∀ x : P, x ^ q = 1) (hclass : commutator P ≤ Subgroup.center P)
    (hD : SAData S A φ z a₀) (ρ : S ⋊[φ] A →* MulAut P)
    (hrank : ∀ s : S, s ≠ 1 → CFSG.pRank q ↥(fixedSub (ρ (inl s))) ≤ 2) (h2 : (2 : ZMod q) ≠ 0)
    (hC2 : ∀ s : S, s ∉ Subgroup.center S → orderOf s = 2 →
      Module.finrank (ZMod q) (Module.End.eigenspace (frattiniRep q ρ (inl s)) 1) = 2) :
    ∀ s : S, ∀ u ∈ commutator P, ρ (inl s) u = u := by
  classical
  have : Fact (IsPGroup q P) := ⟨hPq⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨s₁, u₁, hu₁, hne⟩ := hcon
  set U := commutator P with hUdef
  have hUinv : ∀ (g : S ⋊[φ] A) (x : P), x ∈ U ↔ ρ g x ∈ U := fun g x =>
    mem_iff_of_characteristic U (ρ g) x
  let ρU : Representation (ZMod q) (S ⋊[φ] A) (Additive U) :=
    elemRep q (restrictAutHom ρ U hUinv)
  have hρU : ∀ (g : S ⋊[φ] A) (v : Additive U),
      ((Additive.toMul (ρU g v) : U) : P) = ρ g ((Additive.toMul v : U) : P) := fun g v => rfl
  have : FiniteDimensional (ZMod q) (Additive U) := Module.Finite.of_finite
  set N : Submodule (ZMod q) (Additive U) :=
    Submodule.span (ZMod q) {w | ∃ (s : S) (e : Additive U), w = ρU (inl s) e - e} with hN
  have hNinv : IsInv ρU N := by
    intro g w hw
    refine Submodule.span_induction (p := fun w _ => ρU g w ∈ N) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨s, e, rfl⟩
      obtain ⟨s', hs'⟩ := exists_inl_mul g s
      have h1 : ρU g (ρU (inl s) e - e) = ρU (inl s') (ρU g e) - ρU g e := by
        rw [map_sub]
        congr 1
        calc ρU g (ρU (inl s) e) = ρU (g * inl s) e := by rw [map_mul]; rfl
          _ = ρU (inl s' * g) e := by rw [hs']
          _ = ρU (inl s') (ρU g e) := by rw [map_mul]; rfl
      rw [h1]
      exact Submodule.subset_span ⟨s', ρU g e, rfl⟩
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact N.add_mem hx hy
    · intro c x _ hx
      rw [map_smul]
      exact N.smul_mem c hx
  have h32 : (Nat.card S : ZMod q) ≠ 0 := by
    rw [hD.card]
    have h32' : ((32 : ℕ) : ZMod q) = 2 ^ 5 := by norm_num
    rw [h32']
    exact pow_ne_zero _ h2
  have hN0 : N ≠ ⊥ := by
    intro hN0
    have hmem : ρU (inl s₁) (Additive.ofMul (⟨u₁, hu₁⟩ : U)) - Additive.ofMul (⟨u₁, hu₁⟩ : U) ∈ N :=
      Submodule.subset_span ⟨s₁, _, rfl⟩
    rw [hN0, Submodule.mem_bot, sub_eq_zero] at hmem
    exact hne (congrArg (fun w : Additive U => ((Additive.toMul w : U) : P)) hmem)
  obtain ⟨Y, hYN, hY⟩ := exists_isMinInv_le hNinv hN0
  have hnt : ¬ ∀ s : S, ∀ y ∈ Y, ρU (inl s) y = y := by
    intro hall
    apply hY.2.1
    rw [eq_bot_iff]
    intro y hy
    exact (Submodule.mem_bot _).2 (eq_zero_of_mem_span_of_fixed (K := ZMod q) h32
      (ρU.comp inl) (hYN hy) (fun s => hall s y hy))
  have hfixedC : ∀ (s : S) (C : Submodule (ZMod q) (Additive U)),
      C ≤ Module.End.eigenspace (ρU (inl s)) 1 →
      ∀ c ∈ C, (ρ (inl s)) ((Additive.toMul c : U) : P) = ((Additive.toMul c : U) : P) := by
    intro s C hC c hc
    have h := hC hc
    rw [Module.End.mem_eigenspace_iff, one_smul] at h
    have := congrArg (fun w : Additive U => ((Additive.toMul w : U) : P)) h
    simpa [hρU] using this
  rcases lemmaY_sign hD ρU hY with hzY | hzY
  · rcases lemmaY_plus h2 hD ρU hY hzY with hall | ⟨s', hs', h3⟩
    · exact hnt hall
    · have hs'1 : s' ≠ 1 := fun h => hs' (h ▸ Subgroup.one_mem _)
      have h4 := finrank_le_pRank_fixedSub hexp U hclass (ρ (inl s'))
        (Module.End.eigenspace (ρU (inl s')) 1 ⊓ Y) (hfixedC s' _ inf_le_left)
      have h5 := hrank s' hs'1
      omega
  · obtain ⟨hY4, hYs⟩ := lemmaY_minus h2 hD ρU hY hzY
    obtain ⟨s₀, hs₀c, hs₀o⟩ := exists_noncentral_involution hD.ext hD.card
    have hs₀1 : s₀ ≠ 1 := fun h => hs₀c (h ▸ Subgroup.one_mem _)
    have hY2 := hYs s₀ hs₀c hs₀o
    obtain ⟨x, hx, hxF⟩ := exists_fixed_not_mem_frattini hPq hq2 ρ (inl s₀)
      (isPGroup_zpowers_map hD.ext.1 (ρ.comp inl) s₀) (by rw [hC2 s₀ hs₀c hs₀o]; norm_num)
    have hxU : x ∉ U := fun h => hxF (CFSG.commutator_le_frattini_of_isPGroup (p := q) h)
    have h4 := finrank_succ_le_pRank_fixedSub hexp U hclass (ρ (inl s₀))
      (Module.End.eigenspace (ρU (inl s₀)) 1 ⊓ Y) (hfixedC s₀ _ inf_le_left) hx hxU
    have h5 := hrank s₀ hs₀1
    omega


omit [Finite A] in
theorem card_commutator_le [IsElementaryAbelian q (P ⧸ frattini P)] (hq2 : q ≠ 2)
    (hPq : IsPGroup q P) (hexp : ∀ x : P, x ^ q = 1) (hclass : commutator P ≤ Subgroup.center P)
    (hD : SAData S A φ z a₀) (ρ : S ⋊[φ] A →* MulAut P)
    (hrank : ∀ s : S, s ≠ 1 → CFSG.pRank q ↥(fixedSub (ρ (inl s))) ≤ 2)
    (hC2 : ∀ s : S, s ∉ Subgroup.center S → orderOf s = 2 →
      Module.finrank (ZMod q) (Module.End.eigenspace (frattiniRep q ρ (inl s)) 1) = 2)
    (hfix : ∀ s : S, ∀ u ∈ commutator P, ρ (inl s) u = u) : Nat.card (commutator P) ≤ q := by
  have : Fact (IsPGroup q P) := ⟨hPq⟩
  set U := commutator P with hUdef
  obtain ⟨k, hk⟩ := (hPq.to_subgroup U).exists_card_eq
  by_contra hlt
  push Not at hlt
  have hq1 : 1 < q := hq.out.one_lt
  have hk2 : 2 ≤ k := by
    by_contra h
    push Not at h
    interval_cases k
    · rw [pow_zero] at hk
      omega
    · rw [pow_one] at hk
      omega
  obtain ⟨s₀, hs₀c, hs₀o⟩ := exists_noncentral_involution hD.ext hD.card
  have hs₀1 : s₀ ≠ 1 := fun h => hs₀c (h ▸ Subgroup.one_mem _)
  obtain ⟨x, hx, hxF⟩ := exists_fixed_not_mem_frattini hPq hq2 ρ (inl s₀)
    (isPGroup_zpowers_map hD.ext.1 (ρ.comp inl) s₀) (by rw [hC2 s₀ hs₀c hs₀o]; norm_num)
  have hxU : x ∉ U := fun h => hxF (CFSG.commutator_le_frattini_of_isPGroup (p := q) h)
  have hcomm : IsMulCommutative U :=
    ⟨⟨fun a b => Subtype.ext ((Subgroup.mem_center_iff.1 (hclass a.2) b).symm)⟩⟩
  obtain ⟨hcomm', hcard⟩ := CFSG.RankThree.PartTwo.sup_zpowers_card hcomm hxU (hexp x)
    (fun a ha => (Subgroup.mem_center_iff.1 (hclass ha) x).symm)
  have hle : U ⊔ Subgroup.zpowers x ≤ fixedSub (ρ (inl s₀)) := by
    refine sup_le (fun u hu => hfix s₀ u hu) ?_
    rw [Subgroup.zpowers_le]
    exact hx
  have h1 := le_pRank_fixedSub hq.out.one_lt hexp (ρ (inl s₀)) hcomm' (fun y hy => hle hy)
    (k := k + 1) (by rw [hcard, hk, pow_succ])
  have h2 := hrank s₀ hs₀1
  omega

end Commutator


section Assembly

variable {q : ℕ} [hq : Fact q.Prime] {P : Type*} [Group P] [Finite P]
  {S A : Type*} [Group S] [Finite S] [Group A] [Finite A]
  {φ : A →* MulAut S} {z : S} {a₀ : A}

theorem fixedRank_core (hq2 : q ≠ 2) (hq5 : q ≠ 5) (hPq : IsPGroup q P)
    (hexp : ∀ x : P, x ^ q = 1) (hclass : commutator P ≤ Subgroup.center P)
    (hD : SAData S A φ z a₀) (ρ : S ⋊[φ] A →* MulAut P)
    (hfaith : ∀ s : S, ρ (inl s) = 1 → s = 1)
    (hrank : ∀ s : S, s ≠ 1 → CFSG.pRank q ↥(fixedSub (ρ (inl s))) ≤ 2) :
    Subgroup.closure {x : P | ∃ (d : P) (s : S), x = d⁻¹ * ρ (inl s) d} = ⊤ ∧
      Nat.card (P ⧸ frattini P) = q ^ 4 ∧
      ((IsElementaryAbelian q P ∧ Nat.card P = q ^ 4) ∨
        (Nat.card P = q ^ 5 ∧ Nat.card (commutator P) = q ∧
          Subgroup.center P = commutator P ∧ frattini P = commutator P)) := by
  classical
  have : Fact (IsPGroup q P) := ⟨hPq⟩
  obtain ⟨-, -, hVexp, hVelem, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hPq
  have h2 : (2 : ZMod q) ≠ 0 := by
    have := natCast_ne_zero_zmod hq.out Nat.prime_two hq2
    exact_mod_cast this
  obtain ⟨hmin, hzV, hdim, hC2⟩ := core_module hq2 hq5 hPq hexp hclass hD ρ hfaith hrank
  have hUcomm : IsMulCommutative (commutator P) :=
    ⟨⟨fun a b => Subtype.ext ((Subgroup.mem_center_iff.1 (hclass a.2) b).symm)⟩⟩
  have hUel : IsElementaryAbelian q (commutator P) := isElementaryAbelian_of_comm hexp _ hUcomm
  have hfixU := commutator_fixed hq2 hPq hexp hclass hD ρ hrank h2 hC2
  have hUq := card_commutator_le hq2 hPq hexp hclass hD ρ hrank hC2 hfixU
  have hcard4 : Nat.card (P ⧸ frattini P) = q ^ 4 := by
    have : Fintype (Additive (P ⧸ frattini P)) := Fintype.ofFinite _
    have hpow := Module.card_eq_pow_finrank (K := ZMod q) (V := Additive (P ⧸ frattini P))
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hdim] at hpow
    exact hpow
  have hq1 : 1 < q := hq.out.one_lt
  have hgen : Subgroup.closure {x : P | ∃ (d : P) (s : S), x = d⁻¹ * ρ (inl s) d} = ⊤ := by
    set C := Subgroup.closure {x : P | ∃ (d : P) (s : S), x = d⁻¹ * ρ (inl s) d} with hCdef
    apply frattini_nongenerating
    rw [eq_top_iff]
    intro y _
    set c : P := y⁻¹ * ρ (inl z) y with hc
    have hcC : c ∈ C := Subgroup.subset_closure ⟨y, z, rfl⟩
    have hmkc : (c : P ⧸ frattini P) = ((y : P ⧸ frattini P))⁻¹ * ((y : P ⧸ frattini P))⁻¹ := by
      have h := congrArg (fun f : Module.End (ZMod q) (Additive (P ⧸ frattini P)) =>
        f (Additive.ofMul (y : P ⧸ frattini P))) hzV
      simp only [frattiniRep_apply, LinearMap.neg_apply, Module.End.one_apply] at h
      have h' : ((ρ (inl z) y : P) : P ⧸ frattini P) = ((y : P ⧸ frattini P))⁻¹ :=
        congrArg Additive.toMul h
      rw [hc, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h']
    have hqodd : q % 2 = 1 := by
      rcases hq.out.eq_two_or_odd with h | h
      · exact absurd h hq2
      · exact h
    have hpow : ((c ^ ((q - 1) / 2) : P) : P ⧸ frattini P) = (y : P ⧸ frattini P) := by
      set u : P ⧸ frattini P := (y : P ⧸ frattini P) with hu
      rw [QuotientGroup.mk_pow, hmkc, ← sq, ← pow_mul, show 2 * ((q - 1) / 2) = q - 1 by omega]
      have h1 : u ^ (q - 1) * u = 1 := by
        rw [← pow_succ, Nat.sub_add_cancel hq1.le]
        exact hVexp u
      have h2' : u ^ (q - 1) = u⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [inv_pow, h2', inv_inv]
    have hmem : (c ^ ((q - 1) / 2))⁻¹ * y ∈ frattini P := QuotientGroup.eq.1 hpow
    have hy : y = c ^ ((q - 1) / 2) * ((c ^ ((q - 1) / 2))⁻¹ * y) := by group
    rw [hy]
    exact Subgroup.mul_mem_sup (Subgroup.pow_mem C hcC _) hmem
  refine ⟨hgen, hcard4, ?_⟩
  have hΦ : frattini P = commutator P := by
    rw [CFSG.frattini_eq_closure_commutator_union_powers (p := q)]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro x (hx | ⟨y, rfl⟩)
      · exact hx
      · show y ^ q ∈ commutator P
        rw [hexp y]
        exact one_mem _
    · exact fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hcardP := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini P)
  obtain ⟨k, hk⟩ := (hPq.to_subgroup (commutator P)).exists_card_eq
  have hk1 : k ≤ 1 := by
    by_contra h
    push Not at h
    have : q ^ 2 ≤ q ^ k := Nat.pow_le_pow_right hq.out.pos h
    nlinarith
  interval_cases k
  ·
    left
    have hU0 : commutator P = ⊥ := Subgroup.card_eq_one.1 (by rw [hk, pow_zero])
    have hΦ0 : Nat.card (frattini P) = 1 := by
      rw [hΦ, hU0]
      exact Subgroup.card_bot
    rw [hΦ0, hcard4, mul_one] at hcardP
    have hcommP : IsMulCommutative P := by
      refine ⟨⟨fun a b => ?_⟩⟩
      have : ⁅a, b⁆ ∈ commutator P := by
        rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      rw [hU0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    exact ⟨{ toIsMulCommutative := hcommP
             exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hexp }, hcardP⟩
  ·
    right
    rw [pow_one] at hk
    have hΦq : Nat.card (frattini P) = q := by rw [hΦ]; exact hk
    rw [hΦq, hcard4, ← pow_succ] at hcardP
    refine ⟨hcardP, hk, ?_, hΦ⟩
    refine le_antisymm ?_ hclass
    let Wz : Submodule (ZMod q) (Additive (P ⧸ frattini P)) :=
      AddSubgroup.toZModSubmodule q (Subgroup.toAddSubgroup
        ((Subgroup.center P).map (QuotientGroup.mk' (frattini P))))
    have hWzmem : ∀ v : Additive (P ⧸ frattini P), v ∈ Wz ↔
        ∃ x ∈ Subgroup.center P, (x : P ⧸ frattini P) = Additive.toMul v := by
      intro v
      constructor
      · rintro ⟨x, hx, hxv⟩
        exact ⟨x, hx, hxv⟩
      · rintro ⟨x, hx, hxv⟩
        exact ⟨x, hx, hxv⟩
    have hWzinv : IsInv (frattiniRep q ρ) Wz := by
      intro g v hv
      obtain ⟨x, hx, hxv⟩ := (hWzmem v).1 hv
      refine (hWzmem _).2 ⟨ρ g x, (mem_iff_of_characteristic _ (ρ g) x).1 hx, ?_⟩
      have : v = Additive.ofMul (x : P ⧸ frattini P) := by rw [hxv]; rfl
      rw [this, frattiniRep_apply]
      rfl
    rcases hmin.2.2 Wz le_top hWzinv with h0 | htop
    · intro x hx
      have hxW : Additive.ofMul (x : P ⧸ frattini P) ∈ Wz := (hWzmem _).2 ⟨x, hx, rfl⟩
      rw [h0, Submodule.mem_bot] at hxW
      have hx1 : (x : P ⧸ frattini P) = 1 := hxW
      rw [← hΦ]
      exact (QuotientGroup.eq_one_iff x).1 hx1
    · exfalso
      have hZtop : Subgroup.center P = ⊤ := by
        apply frattini_nongenerating
        rw [eq_top_iff]
        intro y _
        have hyW : Additive.ofMul (y : P ⧸ frattini P) ∈ Wz := by rw [htop]; exact Submodule.mem_top
        obtain ⟨x, hx, hxy⟩ := (hWzmem _).1 hyW
        have hmem : x⁻¹ * y ∈ frattini P := QuotientGroup.eq.1 hxy
        have hy : y = x * (x⁻¹ * y) := by group
        rw [hy]
        exact Subgroup.mul_mem_sup hx hmem
      have hU0 : commutator P = ⊥ := by
        rw [eq_bot_iff, commutator_def, Subgroup.commutator_le]
        intro a _ b _
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_center_iff.1 (hZtop ▸ Subgroup.mem_top a) b).symm
      rw [hU0, Subgroup.card_bot] at hk
      omega

end Assembly

end CFSG.RankThree.PartOne.FixedRank36
