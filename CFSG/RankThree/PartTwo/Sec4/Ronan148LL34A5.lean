module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Core

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open Equiv

section A5

@[expose] def kleinFinset : Finset (Perm (Fin 5)) :=
  {1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2}

@[expose] def cyc123P : Perm (Fin 5) := swap 1 2 * swap 2 3

theorem mem_kleinFinset {a : Perm (Fin 5)} :
    a ∈ kleinFinset ↔ a = 1 ∨ a = swap 0 1 * swap 2 3 ∨ a = swap 0 2 * swap 1 3 ∨
      a = swap 0 3 * swap 1 2 := by
  simp only [kleinFinset, Finset.mem_insert, Finset.mem_singleton]

theorem kleinFinset_mul : ∀ a ∈ kleinFinset, ∀ b ∈ kleinFinset, a * b ∈ kleinFinset := by
  intro a ha b hb
  rw [mem_kleinFinset] at ha hb
  rw [mem_kleinFinset]
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;> decide

theorem kleinFinset_inv : ∀ a ∈ kleinFinset, a⁻¹ ∈ kleinFinset := by
  intro a ha
  rw [mem_kleinFinset] at ha
  rw [mem_kleinFinset]
  rcases ha with rfl | rfl | rfl | rfl <;> decide

theorem kleinFinset_conj : ∀ a ∈ kleinFinset, cyc123P * a * cyc123P⁻¹ ∈ kleinFinset := by
  intro a ha
  rw [mem_kleinFinset] at ha
  rw [mem_kleinFinset]
  rcases ha with rfl | rfl | rfl | rfl <;> decide

theorem kleinFinset_conj_inv : ∀ a ∈ kleinFinset, cyc123P⁻¹ * a * cyc123P ∈ kleinFinset := by
  intro a ha
  rw [mem_kleinFinset] at ha
  rw [mem_kleinFinset]
  rcases ha with rfl | rfl | rfl | rfl <;> decide

theorem kleinFinset_card : kleinFinset.card = 4 := by
  rw [kleinFinset, Finset.card_insert_of_notMem (by decide),
    Finset.card_insert_of_notMem (by decide),
    Finset.card_pair (by decide)]

theorem kleinFinset_sign : ∀ a ∈ kleinFinset, Perm.sign a = 1 := by
  intro a ha
  simp only [kleinFinset, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl <;>
    simp [Perm.sign_mul, Perm.sign_swap]

theorem cyc123P_sign : Perm.sign cyc123P = 1 := by
  simp [cyc123P, Perm.sign_mul, Perm.sign_swap]

theorem cyc123P_pow_three : cyc123P ^ 3 = 1 := by
  decide

theorem cyc123P_ne_one : cyc123P ≠ 1 := by
  decide

@[expose] def kleinPerm : Subgroup (Perm (Fin 5)) where
  carrier := {x | x ∈ kleinFinset}
  mul_mem' {a b} ha hb := kleinFinset_mul a ha b hb
  one_mem' := by
    show (1 : Perm (Fin 5)) ∈ kleinFinset
    rw [mem_kleinFinset]
    exact Or.inl rfl
  inv_mem' {a} ha := kleinFinset_inv a ha

theorem kleinPerm_le : kleinPerm ≤ alternatingGroup (Fin 5) := fun a ha =>
  Perm.mem_alternatingGroup.mpr (kleinFinset_sign a ha)

theorem card_kleinPerm : Nat.card kleinPerm = 4 := by
  rw [← kleinFinset_card, ← Nat.card_eq_finsetCard]
  rfl

@[expose] def kleinA5 : Subgroup (alternatingGroup (Fin 5)) :=
  kleinPerm.subgroupOf (alternatingGroup (Fin 5))

theorem card_kleinA5 : Nat.card kleinA5 = 4 := by
  rw [kleinA5, Nat.card_congr (Subgroup.subgroupOfEquivOfLe kleinPerm_le).toEquiv, card_kleinPerm]

@[expose] def cyc123 : alternatingGroup (Fin 5) :=
  ⟨cyc123P, Perm.mem_alternatingGroup.mpr cyc123P_sign⟩

theorem orderOf_cyc123 : orderOf cyc123 = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (Subtype.ext ?_) (fun h => cyc123P_ne_one (congrArg Subtype.val h))
  change cyc123P ^ 3 = 1
  exact cyc123P_pow_three

theorem cyc123_mem_normalizer :
    cyc123 ∈ Subgroup.normalizer (kleinA5 : Set (alternatingGroup (Fin 5))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  change (h : Perm (Fin 5)) ∈ kleinFinset ↔ (cyc123P * h * cyc123P⁻¹ : Perm (Fin 5)) ∈ kleinFinset
  constructor
  · exact kleinFinset_conj _
  · intro hh
    have := kleinFinset_conj_inv _ hh
    rwa [show cyc123P⁻¹ * (cyc123P * (h : Perm (Fin 5)) * cyc123P⁻¹) * cyc123P = h by group] at this

end A5

section Sylow

theorem card_map_mul_card_inf_ker {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (H : Subgroup X) : Nat.card H = Nat.card (H.map f) * Nat.card (H ⊓ f.ker : Subgroup X) := by
  have h := Subgroup.relIndex_mul_card f.ker H
  rw [Subgroup.relIndex_ker, inf_comm] at h
  exact h.symm

variable {H : Type} [Group H] [Finite H]

theorem card_eq_sixty_mul_pCore (φ : H ⧸ CFSG.pCore 2 H ≃* alternatingGroup (Fin 5)) :
    ∃ a : ℕ, Nat.card (CFSG.pCore 2 H) = 2 ^ a ∧ Nat.card H = 60 * 2 ^ a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 H)).exists_card_eq
  refine ⟨a, ha, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 H), ha,
    Nat.card_congr φ.toEquiv, Ronan148R.card_alternatingGroup_five]

theorem exists_sylow_two_three_dvd (φ : H ⧸ CFSG.pCore 2 H ≃* alternatingGroup (Fin 5)) :
    ∃ S : Sylow 2 H, 3 ∣ Nat.card (Subgroup.normalizer ((S : Subgroup H) : Set H)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, hO, hH⟩ := card_eq_sixty_mul_pCore φ
  set π : H →* H ⧸ CFSG.pCore 2 H := QuotientGroup.mk' (CFSG.pCore 2 H) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = CFSG.pCore 2 H := QuotientGroup.ker_mk' _
  set V : Subgroup (H ⧸ CFSG.pCore 2 H) := kleinA5.comap φ.toMonoidHom with hV
  have hVc : Nat.card V = 4 := by
    rw [hV, ← card_kleinA5]
    exact Nat.card_congr ((kleinA5.equivMapOfInjective φ.symm.toMonoidHom φ.symm.injective).trans
      (MulEquiv.subgroupCongr (by
        ext x
        simp only [Subgroup.mem_map, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
        constructor
        · rintro ⟨y, hy, rfl⟩
          simpa using hy
        · intro hx
          exact ⟨φ x, hx, by simp⟩))).toEquiv.symm
  set S₀ : Subgroup H := V.comap π with hS₀
  have hkS : CFSG.pCore 2 H ≤ S₀ := by
    intro x hx
    show π x ∈ V
    rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact V.one_mem
  have hS₀c : Nat.card S₀ = 2 ^ (a + 2) := by
    have h := card_map_mul_card_inf_ker π S₀
    rw [hS₀, Subgroup.map_comap_eq_self_of_surjective hπs, hker, ← hS₀,
      inf_eq_right.mpr hkS, hVc, hO] at h
    rw [h, pow_add]
    ring
  have hfac : (Nat.card H).factorization 2 = a + 2 := by
    rw [hH, show 60 * 2 ^ a = 2 ^ (a + 2) * 15 by ring,
      Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  let S : Sylow 2 H := Sylow.ofCard S₀ (by rw [hS₀c, hfac])
  refine ⟨S, ?_⟩
  obtain ⟨f, hf⟩ := hπs (φ.symm cyc123)
  have hfN : f ∈ Subgroup.normalizer ((S : Subgroup H) : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    change π h ∈ V ↔ π (f * h * f⁻¹) ∈ V
    rw [map_mul, map_mul, map_inv, hf]
    change φ (π h) ∈ kleinA5 ↔ φ (φ.symm cyc123 * π h * (φ.symm cyc123)⁻¹) ∈ kleinA5
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact (Subgroup.mem_normalizer_iff.mp cyc123_mem_normalizer (φ (π h)))
  have h3f : 3 ∣ orderOf f := by
    have h1 : orderOf (π f) ∣ orderOf f := orderOf_map_dvd π f
    rw [hf, MulEquiv.orderOf_eq, orderOf_cyc123] at h1
    exact h1
  have h3 : orderOf (⟨f, hfN⟩ : Subgroup.normalizer ((S : Subgroup H) : Set H)) =
      orderOf f := Subgroup.orderOf_mk f hfN
  exact (h3 ▸ h3f).trans (orderOf_dvd_natCard _)

theorem not_three_dvd_card_sylow_two (φ : H ⧸ CFSG.pCore 2 H ≃* alternatingGroup (Fin 5)) :
    ¬ 3 ∣ Nat.card (Sylow 2 H) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, -, hH⟩ := card_eq_sixty_mul_pCore φ
  obtain ⟨S, hS⟩ := exists_sylow_two_three_dvd φ
  rw [Sylow.card_eq_index_normalizer]
  intro h3
  have hmul := (Subgroup.normalizer ((S : Subgroup H) : Set H)).card_mul_index
  rw [hH] at hmul
  have h9 : 9 ∣ 60 * 2 ^ a := by
    rw [← hmul, show (9 : ℕ) = 3 * 3 by norm_num]
    exact Nat.mul_dvd_mul hS h3
  have hcop : Nat.Coprime 9 (2 ^ a) := Nat.Coprime.pow_right a (by norm_num)
  have : 9 ∣ 60 := by
    have := (Nat.Coprime.dvd_mul_right hcop).mp h9
    exact this
  omega

end Sylow

section Fixed

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_two_normalized {K A : Subgroup G}
    (φ : K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 5))
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hA : IsPGroup 3 A) :
    ∃ U : Subgroup G, U ≤ K ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ A ≤ Subgroup.normalizer (U : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup G := Subgroup.normalizer (K : Set G) with hN
  set A' : Subgroup N := A.subgroupOf N with hA'
  have hA'p : IsPGroup 3 A' := hA.comap_subtype (K := N)
  have hcong := hA'p.card_modEq_card_fixedPoints (Sylow 2 K)
  have hnd := not_three_dvd_card_sylow_two φ
  have hfix : (MulAction.fixedPoints A' (Sylow 2 K)).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have h0 : Nat.card (MulAction.fixedPoints A' (Sylow 2 K)) = 0 := by
      rw [hemp]; simp
    rw [h0] at hcong
    exact hnd (Nat.dvd_of_mod_eq_zero hcong)
  obtain ⟨S, hS⟩ := hfix
  obtain ⟨b, hb⟩ := (show ∃ b, Nat.card K = 60 * 2 ^ b from by
    obtain ⟨b, -, hb⟩ := card_eq_sixty_mul_pCore φ
    exact ⟨b, hb⟩)
  refine ⟨(S : Subgroup K).map K.subtype, Subgroup.map_subtype_le _, ?_, S.isPGroup'.map _, ?_⟩
  · intro h0
    have hc : Nat.card ((S : Subgroup K).map K.subtype) = 1 := by rw [h0, Subgroup.card_bot]
    rw [Subgroup.card_map_of_injective K.subtype_injective, Sylow.card_eq_multiplicity, hb,
      show 60 * 2 ^ b = 2 ^ (b + 2) * 15 by ring,
      Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero] at hc
    have : 2 ^ 2 ≤ 2 ^ (b + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · intro x hx
    have hxN : x ∈ N := hAK hx
    have hxA' : (⟨x, hxN⟩ : N) ∈ A' := hx
    have hxi : (⟨x, hxN⟩ : N)⁻¹ ∈ A' := A'.inv_mem hxA'
    have h1 := hS ⟨⟨x, hxN⟩, hxA'⟩
    have h2 := hS ⟨(⟨x, hxN⟩ : N)⁻¹, hxi⟩
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hmem : (⟨x, hxN⟩ : N) • s ∈ (S : Subgroup K) := by
        rw [← Sylow.ext_iff.mp h1]
        exact Subgroup.smul_mem_pointwise_smul s _ _ hs
      exact ⟨_, hmem, rfl⟩
    · rintro ⟨s, hs, hsx⟩
      have hmem : (⟨x, hxN⟩ : N)⁻¹ • s ∈ (S : Subgroup K) := by
        rw [← Sylow.ext_iff.mp h2]
        exact Subgroup.smul_mem_pointwise_smul s _ _ hs
      refine ⟨_, hmem, ?_⟩
      change x⁻¹ * (s : G) * x⁻¹⁻¹ = g
      rw [inv_inv]
      have : (s : G) = x * g * x⁻¹ := hsx
      rw [this]
      group

end Fixed

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
