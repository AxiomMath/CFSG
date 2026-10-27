module

public import CFSG.RankThree.PartTwo.ClassTwoEightActionInverting
public import CFSG.RankThree.GroupTheory.SteinbergCEExtraspecialMinusModule
public import CFSG.Assembly.OrderReductions.FrattiniAutomorphisms
import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
import CFSG.GroupTheory.FrattiniQuotient
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup CFSG CFSG.RankThree.PartTwo CFSG.OrderReductions.FrattiniAutomorphisms
open scoped commutatorElement IsMulCommutative

theorem card_fixedSubgroupOf_frattini_quotient_le {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup p P) (σ : MulAut P) (hσ : σ ^ 2 = 1) :
    Nat.card (fixedSubgroupOf (quotientAutomorphism (frattini P) σ)) ≤
      Nat.card (fixedSubgroupOf σ ⧸ commutator (fixedSubgroupOf σ)) := by
  obtain ⟨hchar, hVcomm, -, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hP
  set C := fixedSubgroupOf σ with hC
  let Z := zpowers σ
  have hZ2 : IsPGroup 2 Z := fun g => ⟨1, by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp g.2
    apply Subtype.ext
    rw [coe_pow, ← hk, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hσ,
      one_zpow, coe_one]⟩
  let α : Z →* MulAut P := Z.subtype
  have hN : ∀ b : Z, ∀ n ∈ frattini P, α b n ∈ frattini P := by
    intro b n hn
    have h := characteristic_iff_map_eq.mp hchar (α b)
    rw [← h]
    exact mem_map_of_mem _ hn
  have hcop : ¬ 2 ∣ Nat.card (frattini P) := not_two_dvd_card_of_odd hp2 (hP.to_subgroup _)
  have hset := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 2 hZ2 α (frattini P) hN
    hcop
  let f : C →* P ⧸ frattini P := (QuotientGroup.mk' (frattini P)).comp C.subtype
  have hle : fixedSubgroupOf (quotientAutomorphism (frattini P) σ) ≤ f.range := by
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hfixσ : CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α (frattini P) hN
        ⟨σ, mem_zpowers σ⟩ (x : P ⧸ frattini P) = (x : P ⧸ frattini P) := by
      rw [CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk]
      have h : quotientAutomorphism (frattini P) σ (QuotientGroup.mk' (frattini P) x) =
          QuotientGroup.mk' (frattini P) x := hy
      rw [quotientAutomorphism_apply] at h
      exact h
    have hmem : (x : P ⧸ frattini P) ∈ {q : P ⧸ frattini P | ∀ b : Z,
        CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α (frattini P) hN b q =
          q} := by
      rintro ⟨b, hb⟩
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
      have hb' : (⟨σ ^ k, hb⟩ : Z) = ⟨σ, mem_zpowers σ⟩ ^ k := Subtype.ext (by simp)
      rw [hb', map_zpow]
      exact zpow_apply_eq_self_of_apply_eq_self hfixσ k
    rw [hset] at hmem
    obtain ⟨c, hc, hcx⟩ := hmem
    exact ⟨⟨c, hc ⟨σ, mem_zpowers σ⟩⟩, hcx⟩
  have hcomm_ker : commutator C ≤ f.ker := by
    rw [commutator_def, commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hVcomm.is_comm.comm _ _
  have hrange : Nat.card f.range ≤ Nat.card (C ⧸ commutator C) := by
    have h1 := card_ker_mul_card_range f
    have h2 := card_eq_card_quotient_mul_card_subgroup (commutator C)
    have h3 := card_le_of_le hcomm_ker
    have hpos : 0 < Nat.card f.ker := Nat.card_pos
    have h4 : Nat.card f.range * Nat.card f.ker ≤
        Nat.card (C ⧸ commutator C) * Nat.card f.ker := by
      calc Nat.card f.range * Nat.card f.ker = Nat.card C := by rw [← h1, mul_comm]
        _ = Nat.card (C ⧸ commutator C) * Nat.card (commutator C) := h2
        _ ≤ Nat.card (C ⧸ commutator C) * Nat.card f.ker := Nat.mul_le_mul_left _ h3
    exact Nat.le_of_mul_le_mul_right h4 hpos
  exact (card_le_of_le hle).trans hrange

theorem exists_noncentral_involution {S : Type*} [Group S] [Finite S] {n : ℕ}
    (hS : IsExtraspecialPGroup 2 S) (hcard : Nat.card S = 2 ^ (1 + 2 * n)) (hn : 2 ≤ n) {z : S}
    (hz : center S = zpowers z) :
    ∃ s : S, s ∉ center S ∧ orderOf s = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hz2, hcomm⟩ := extraspecial_commutator_eq_one_or hS hz
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hzc : z ∈ center S := hz ▸ mem_zpowers z
  have hZ : ∀ w ∈ center S, w = 1 ∨ w = z := by
    intro w hw
    rw [hz] at hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    rw [← zpow_mod_orderOf, hz2]
    have h : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
    rcases h with h | h
    · left
      rw [h, zpow_zero]
    · right
      rw [h, zpow_one]
  have hsq : ∀ g : S, g * g ∈ center S := fun g => by
    rw [← hS.2.2.1, ← pow_two]
    exact CFSG.OrderReductions.FrattiniElementary.pow_mem_frattini 2 hS.1 g
  have hinv2 : ∀ g : S, g⁻¹ = g ∨ g⁻¹ = g * z := by
    intro g
    rcases hZ _ (hsq g) with h | h
    · left
      exact inv_eq_of_mul_eq_one_right h
    · right
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← mul_assoc, h, hzz]
  have hord : ∀ g : S, g ∉ center S → g * g = 1 → orderOf g = 2 := fun g hg h =>
    orderOf_eq_prime (by rw [pow_two, h]) fun h1 => hg (h1 ▸ one_mem _)
  have hlarge : 2 ^ 5 ≤ Nat.card S := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨x, hx⟩ : ∃ x : S, x ∉ center S := by
    by_contra h
    push Not at h
    have htop : center S = ⊤ := eq_top_iff.mpr fun g _ => h g
    have h1 := hS.2.2.2
    rw [htop, card_top] at h1
    omega
  have hcen : ∀ y : S, ⁅x, y⁆ ∈ center S := fun y => by
    rcases hcomm x y with h | h <;> rw [h]
    · exact one_mem _
    · exact hzc
  let cx : S →* center S :=
    { toFun := fun y => ⟨⁅x, y⁆, hcen y⟩
      map_one' := Subtype.ext (by simp [commutatorElement_def])
      map_mul' := fun y₁ y₂ => Subtype.ext (by
        change ⁅x, y₁ * y₂⁆ = ⁅x, y₁⁆ * ⁅x, y₂⁆
        have h2 := mem_center_iff.mp (hcen y₂) y₁
        calc ⁅x, y₁ * y₂⁆ = x * y₁ * x⁻¹ * ⁅x, y₂⁆ * y₁⁻¹ := by
              simp only [commutatorElement_def]
              group
          _ = x * y₁ * x⁻¹ * y₁⁻¹ * (y₁ * ⁅x, y₂⁆) * y₁⁻¹ := by group
          _ = x * y₁ * x⁻¹ * y₁⁻¹ * (⁅x, y₂⁆ * y₁) * y₁⁻¹ := by rw [h2]
          _ = ⁅x, y₁⁆ * ⁅x, y₂⁆ := by
              rw [commutatorElement_def x y₁]
              group) }
  have hkercard : 2 ^ 4 ≤ Nat.card cx.ker := by
    have h1 := card_ker_mul_card_range cx
    have h2 : Nat.card cx.range ≤ 2 := by
      calc Nat.card cx.range ≤ Nat.card (center S) := Nat.card_le_card_of_injective
            (fun w => (w : center S)) Subtype.val_injective
        _ = 2 := hS.2.2.2
    have h3 : 2 ^ 5 ≤ Nat.card cx.ker * 2 := by
      calc 2 ^ 5 ≤ Nat.card S := hlarge
        _ = Nat.card cx.ker * Nat.card cx.range := h1.symm
        _ ≤ Nat.card cx.ker * 2 := Nat.mul_le_mul_left _ h2
    omega
  obtain ⟨y, hyk, hy⟩ : ∃ y ∈ cx.ker, y ∉ ({1, z, x, x * z} : Set S) := by
    by_contra h
    push Not at h
    have hsub : (cx.ker : Set S) ⊆ ({1, z, x, x * z} : Set S) := fun y hy => h y hy
    have h4 : Nat.card cx.ker ≤ 4 := by
      calc Nat.card cx.ker = ((cx.ker : Set S)).ncard := Nat.card_coe_set_eq _
        _ ≤ ({1, z, x, x * z} : Set S).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ 4 := by
            refine (Set.ncard_insert_le _ _).trans ?_
            refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
            refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
            rw [Set.ncard_singleton]
    omega
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hy
  obtain ⟨hy1, hyz, hyx, hyxz⟩ := hy
  have hxy : x * y = y * x := commutatorElement_eq_one_iff_mul_comm.mp
    (congrArg Subtype.val (MonoidHom.mem_ker.mp hyk))
  have hyc : y ∉ center S := fun h => by
    rcases hZ y h with h | h
    · exact hy1 h
    · exact hyz h
  have hxyc : x * y ∉ center S := by
    intro h
    have hyeq : y = x⁻¹ * (x * y) := by group
    rcases hZ _ h with h | h <;> rcases hinv2 x with hi | hi
    · exact hyx (by rw [hyeq, h, mul_one, hi])
    · exact hyxz (by rw [hyeq, h, mul_one, hi])
    · exact hyxz (by rw [hyeq, h, hi])
    · exact hyx (by rw [hyeq, h, hi, mul_assoc, hzz, mul_one])
  rcases hZ _ (hsq x) with hx2 | hx2
  · exact ⟨x, hx, hord x hx hx2⟩
  rcases hZ _ (hsq y) with hy2 | hy2
  · exact ⟨y, hyc, hord y hyc hy2⟩
  refine ⟨x * y, hxyc, hord _ hxyc ?_⟩
  calc x * y * (x * y) = x * x * (y * y) := by
        rw [mul_assoc, ← mul_assoc y x y, ← hxy]
        group
    _ = 1 := by rw [hx2, hy2, hzz]

theorem class_two_extraspecial_action_bound {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup p P) (hexp : ∀ x : P, x ^ p = 1)
    (hclass : commutator P ≤ center P) {S : Type*} [Group S] {n : ℕ}
    (hS : IsExtraspecialPGroup 2 S) (hcard : Nat.card S = 2 ^ (1 + 2 * n)) {z : S}
    (hz : center S = zpowers z) (ρ : S →* MulAut P) (hρ : Function.Injective ρ)
    (hfix : ∀ s : S, s ≠ 1 → CFSG.pRank p (fixedSubgroupOf (ρ s)) ≤ 3) :
    n ≤ 3 ∧
      (n = 3 → ∀ s : S, s ∉ center S → orderOf s = 2 →
        CFSG.pRank p (fixedSubgroupOf (ρ s)) = 3) ∧
      (closure {y : P | ∃ x : P, ∃ s ∈ center S, y = x⁻¹ * ρ s x} = ⊤ →
        ∀ s : S, s ∉ center S → orderOf s = 2 →
          ∃ d : ℕ, Nat.card (fixedSubgroupOf (quotientAutomorphism (frattini P) (ρ s))) = p ^ d ∧
            Nat.card (P ⧸ frattini P) = p ^ (2 * d) ∧ 2 ^ (n - 1) ≤ d) := by
  classical
  have hp' : p.Prime := hp.out
  have : Finite S := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  obtain ⟨hchar, hVcomm, hVexp, hVelem, -, -, -⟩ :=
    CFSG.GroupTheory.frattini_elementary_quotient hP
  have : Finite (Additive (P ⧸ frattini P)) := inferInstanceAs (Finite (P ⧸ frattini P))
  have : FiniteDimensional (ZMod p) (Additive (P ⧸ frattini P)) := Module.Finite.of_finite
  let E : MulAut (P ⧸ frattini P) →* Module.End (ZMod p) (Additive (P ⧸ frattini P)) :=
    { toFun := fun σ => (MonoidHom.toAdditive σ.toMonoidHom).toZModLinearMap p
      map_one' := LinearMap.ext fun _ => rfl
      map_mul' := fun _ _ => LinearMap.ext fun _ => rfl }
  let q := quotientAutomorphism (frattini P)
  let ρV : Representation (ZMod p) S (Additive (P ⧸ frattini P)) := E.comp (q.comp ρ)
  have hρV : ∀ (s : S) (x : P), ρV s (Additive.ofMul (x : P ⧸ frattini P)) =
      Additive.ofMul ((ρ s x : P) : P ⧸ frattini P) := fun s x => by
    change Additive.ofMul (q (ρ s) (QuotientGroup.mk' (frattini P) x)) = _
    rw [quotientAutomorphism_apply]
    rfl
  have hcardpow : ∀ W : Submodule (ZMod p) (Additive (P ⧸ frattini P)),
      Nat.card W = p ^ Module.finrank (ZMod p) W := by
    intro W
    have : Fintype W := Fintype.ofFinite _
    have hpow := Module.card_eq_pow_finrank (K := ZMod p) (V := W)
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at hpow
    exact hpow
  have hcardV : Nat.card (P ⧸ frattini P) =
      p ^ Module.finrank (ZMod p) (Additive (P ⧸ frattini P)) := by
    have : Fintype (Additive (P ⧸ frattini P)) := Fintype.ofFinite _
    have hpow := Module.card_eq_pow_finrank (K := ZMod p) (V := Additive (P ⧸ frattini P))
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at hpow
    exact hpow
  have hcardfix : ∀ s : S, Nat.card (Module.End.eigenspace (ρV s) 1) =
      Nat.card (fixedSubgroupOf (q (ρ s))) := by
    intro s
    refine Nat.card_congr
      { toFun := fun w => ⟨Additive.toMul (w : Additive (P ⧸ frattini P)), ?_⟩
        invFun := fun y => ⟨Additive.ofMul (y : P ⧸ frattini P), ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · have h := Module.End.mem_eigenspace_iff.mp w.2
      rw [one_smul] at h
      exact congrArg Additive.toMul h
    · rw [Module.End.mem_eigenspace_iff, one_smul]
      exact congrArg Additive.ofMul y.2
  have hbound : ∀ s : S, s ^ 2 = 1 → ∀ k : ℕ,
      CFSG.pRank p (fixedSubgroupOf (ρ s) ⧸ commutator (fixedSubgroupOf (ρ s))) ≤ k →
      Module.finrank (ZMod p) (Module.End.eigenspace (ρV s) 1) ≤ k := by
    intro s hs k hk
    set C := fixedSubgroupOf (ρ s)
    have hC : IsPGroup p C := hP.to_subgroup C
    obtain ⟨j, hj⟩ := (hC.to_quotient (commutator C)).exists_card_eq
    have hj' := (quotient_commutator_rank hp' (subgroup_pow_eq_one hexp C) hj).2
    have hle := card_fixedSubgroupOf_frattini_quotient_le hp2 hP (ρ s)
      (by rw [← map_pow, hs, map_one])
    rw [← hcardfix, hcardpow, hj] at hle
    have h1 := (Nat.pow_le_pow_iff_right hp'.one_lt).mp hle
    omega
  have hrank_bound : ∀ s : S, s ≠ 1 → s ^ 2 = 1 →
      Module.finrank (ZMod p) (Module.End.eigenspace (ρV s) 1) ≤ 4 := by
    intro s hs1 hs
    refine hbound s hs 4 ?_
    exact (class_two_small_rank_order_bounds (hP.to_subgroup _) (subgroup_pow_eq_one hexp _)
      (subgroup_commutator_le_center hclass _)).2.2 (hfix s hs1)
  obtain ⟨hz2, -⟩ := extraspecial_commutator_eq_one_or hS hz
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hzc : z ∈ center S := hz ▸ mem_zpowers z
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; omega
  have hK : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp' hp2
  have hρVzz : ρV z * ρV z = 1 := by rw [← map_mul, hzz, map_one]
  have hρVz1 : ρV z ≠ 1 := by
    intro h
    have hordz : orderOf (ρ z) = 2 := by rw [orderOf_injective ρ hρ z, hz2]
    refine hz1 (hρ ((prime_order_frattini_kernel_trivial 2 (ρ z) hordz
      (not_two_dvd_card_of_odd hp2 hP) ?_).trans (map_one ρ).symm))
    rw [mem_quotientAutomorphism_kernel]
    intro x
    have h' := congrArg (fun f : Module.End (ZMod p) (Additive (P ⧸ frattini P)) =>
      f (Additive.ofMul (x : P ⧸ frattini P))) h
    simp only [hρV, Module.End.one_apply] at h'
    exact congrArg Additive.toMul h'
  have hneg : ∀ v : Additive (P ⧸ frattini P), (-1 : ZMod p) • v = -v := fun v =>
    neg_one_smul (ZMod p) v
  set Vm := Module.End.eigenspace (ρV z) (-1) with hVm
  have hdiff : ∀ v, -v + ρV z v ∈ Vm := by
    intro v
    rw [Module.End.mem_eigenspace_iff, map_add, map_neg, ← Module.End.mul_apply, hρVzz,
      Module.End.one_apply, hneg, neg_add, neg_neg, add_comm]
  have hVm_ne : Vm ≠ ⊥ := by
    intro h
    apply hρVz1
    apply LinearMap.ext
    intro v
    have hw := hdiff v
    rw [h, Submodule.mem_bot] at hw
    rw [Module.End.one_apply]
    exact (neg_add_eq_zero.mp hw).symm
  have hcommz : ∀ s : S, ρV s * ρV z = ρV z * ρV s := fun s => by
    rw [← map_mul, ← map_mul, mem_center_iff.mp hzc s]
  have hmaps : ∀ s : S, ∀ v ∈ Vm, ρV s v ∈ Vm := by
    intro s v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    rw [← Module.End.mul_apply, ← hcommz, Module.End.mul_apply, hv, map_smul]
  let ρm : Representation (ZMod p) S Vm :=
    { toFun := fun s => (ρV s).restrict (hmaps s)
      map_one' := LinearMap.ext fun v => Subtype.ext (by
        change ρV 1 (v : Additive (P ⧸ frattini P)) = v
        rw [map_one, Module.End.one_apply])
      map_mul' := fun s t => LinearMap.ext fun v => Subtype.ext (by
        change ρV (s * t) (v : Additive (P ⧸ frattini P)) = ρV s (ρV t v)
        rw [map_mul, Module.End.mul_apply]) }
  have hρmz : ρm z = -1 := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change ρV z (v : Additive (P ⧸ frattini P)) = -(v : Additive (P ⧸ frattini P))
    rw [(Module.End.mem_eigenspace_iff.mp v.2), hneg]
  have : Nontrivial Vm := Submodule.nontrivial_iff_ne_bot.mpr hVm_ne
  obtain ⟨-, hminus⟩ := extraspecial_two_minus_module_bound hS hcard hz hK ρm hρmz
  have hsubfix : ∀ s : S, Module.finrank (ZMod p) (Module.End.eigenspace (ρm s) 1) ≤
      Module.finrank (ZMod p) (Module.End.eigenspace (ρV s) 1) := by
    intro s
    have hinj : Function.Injective fun w : Module.End.eigenspace (ρm s) 1 =>
        (⟨((w : Vm) : Additive (P ⧸ frattini P)), by
          rw [Module.End.mem_eigenspace_iff, one_smul]
          have h := congrArg Subtype.val ((Module.End.mem_eigenspace_iff.mp w.2).trans
            (one_smul _ _))
          exact h⟩ : Module.End.eigenspace (ρV s) 1) := by
      intro w₁ w₂ h
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')
    have hc := Nat.card_le_card_of_injective _ hinj
    have : Finite Vm := inferInstance
    have hW : Nat.card (Module.End.eigenspace (ρm s) 1) =
        p ^ Module.finrank (ZMod p) (Module.End.eigenspace (ρm s) 1) := by
      have : Fintype (Module.End.eigenspace (ρm s) 1) := Fintype.ofFinite _
      have hpow := Module.card_eq_pow_finrank (K := ZMod p) (V := Module.End.eigenspace (ρm s) 1)
      rw [ZMod.card, ← Nat.card_eq_fintype_card] at hpow
      exact hpow
    rw [hW, hcardpow] at hc
    exact (Nat.pow_le_pow_iff_right hp'.one_lt).mp hc
  have hs2 : ∀ s : S, orderOf s = 2 → s ^ 2 = 1 := fun s hs => by
    rw [← hs, pow_orderOf_eq_one]
  have hs1 : ∀ s : S, s ∉ center S → s ≠ 1 := fun s hs h => hs (h ▸ one_mem _)
  refine ⟨?_, ?_, ?_⟩
  ·
    by_contra hn
    push Not at hn
    obtain ⟨s, hs, hso⟩ := exists_noncentral_involution hS hcard (by omega) hz
    have h1 := (hminus s hs hso).2.trans ((hsubfix s).trans (hrank_bound s (hs1 s hs) (hs2 s hso)))
    have h2 : 2 ^ 3 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  ·
    intro hn s hs hso
    refine le_antisymm (hfix s (hs1 s hs)) ?_
    by_contra hlt
    push Not at hlt
    have h2 : CFSG.pRank p (fixedSubgroupOf (ρ s)) ≤ 2 := by omega
    have hsmall := hbound s (hs2 s hso) 2
      ((class_two_small_rank_order_bounds (hP.to_subgroup _) (subgroup_pow_eq_one hexp _)
        (subgroup_commutator_le_center hclass _)).1 h2)
    have h1 := (hminus s hs hso).2.trans (hsubfix s)
    rw [hn] at h1
    norm_num at h1
    omega
  ·
    intro hgen s hs hso
    have hall : ∀ x : P, Additive.ofMul (x : P ⧸ frattini P) ∈ Vm := by
      intro x
      have hx : x ∈ closure {y : P | ∃ x : P, ∃ s ∈ center S, y = x⁻¹ * ρ s x} := by
        rw [hgen]
        exact mem_top x
      induction hx using closure_induction with
      | mem y hy =>
        obtain ⟨x, t, ht, rfl⟩ := hy
        have e : Additive.ofMul ((x⁻¹ * ρ t x : P) : P ⧸ frattini P) =
            -Additive.ofMul (x : P ⧸ frattini P) + ρV t (Additive.ofMul (x : P ⧸ frattini P)) := by
          rw [hρV]
          rfl
        rw [e]
        obtain ⟨hz2', -⟩ := extraspecial_commutator_eq_one_or hS hz
        have ht' : t = 1 ∨ t = z := by
          rw [hz] at ht
          obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ht
          rw [← zpow_mod_orderOf, hz2']
          have h : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
          rcases h with h | h
          · left
            rw [h, zpow_zero]
          · right
            rw [h, zpow_one]
        rcases ht' with rfl | rfl
        · rw [map_one, Module.End.one_apply, neg_add_cancel]
          exact Vm.zero_mem
        · exact hdiff _
      | one => exact Vm.zero_mem
      | mul a b _ _ ha hb => exact Vm.add_mem ha hb
      | inv a _ ha => exact Vm.neg_mem ha
    have hρVz : ρV z = -1 := by
      apply LinearMap.ext
      intro w
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
      have hwx : w = Additive.ofMul (x : P ⧸ frattini P) := by
        rw [hx]
        rfl
      rw [hwx, (Module.End.mem_eigenspace_iff.mp (hall x)), hneg, LinearMap.neg_apply,
        Module.End.one_apply]
    have : Nontrivial (Additive (P ⧸ frattini P)) := by
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVm_ne
      exact ⟨⟨v, 0, hv0⟩⟩
    obtain ⟨-, hplus⟩ := extraspecial_two_minus_module_bound hS hcard hz hK ρV hρVz
    obtain ⟨hhalf, hge⟩ := hplus s hs hso
    refine ⟨Module.finrank (ZMod p) (Module.End.eigenspace (ρV s) 1), ?_, ?_, hge⟩
    · rw [← hcardfix, hcardpow]
    · rw [hcardV, hhalf]

end CFSG.RankThree.GroupTheory.SteinbergBM
