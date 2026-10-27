module

public import CFSG.RankThree.PartTwo.Sec14.Item148HJProofCover

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148J

open Equiv CFSG.RankThree.PartTwo.Sec14.Item148HJ
open scoped commutatorElement

set_option maxHeartbeats 1000000 in
theorem rel_A : ∀ k : Fin 3, Perm.sign (repA k) = 1 ∧ repA k * repA k = 1 ∧
    repA k * (cA * repA k * cA⁻¹) = cA * repA k * cA⁻¹ * repA k ∧
    cA * (cA * repA k * cA⁻¹) * cA⁻¹ = repA k * (cA * repA k * cA⁻¹) := by
  decide +kernel

set_option maxHeartbeats 1000000 in
theorem rel_B : ∀ k : Fin 3, Perm.sign (repB k) = 1 ∧ repB k * repB k = 1 ∧
    repB k * (cB * repB k * cB⁻¹) = cB * repB k * cB⁻¹ * repB k ∧
    cB * (cB * repB k * cB⁻¹) * cB⁻¹ = repB k * (cB * repB k * cB⁻¹) := by
  decide +kernel

@[expose] def genSet (c : Perm (Fin 6)) (r : Fin 3 → Perm (Fin 6)) : Finset (Perm (Fin 6)) :=
  {1, ⁅r 0, c⁆, ⁅c * r 0 * c⁻¹, c⁆, ⁅r 0, c⁆ * ⁅c * r 0 * c⁻¹, c⁆,
    ⁅r 1, c⁆, ⁅c * r 1 * c⁻¹, c⁆, ⁅r 1, c⁆ * ⁅c * r 1 * c⁻¹, c⁆,
    ⁅r 2, c⁆, ⁅c * r 2 * c⁻¹, c⁆, ⁅r 2, c⁆ * ⁅c * r 2 * c⁻¹, c⁆}

@[expose] def prodGenSet (c : Perm (Fin 6)) (r : Fin 3 → Perm (Fin 6)) : Finset (Perm (Fin 6)) :=
  (genSet c r ×ˢ genSet c r).image (fun q => q.1 * q.2)

set_option maxHeartbeats 4000000 in
theorem card_prod_genSet_A : (prodGenSet cA repA).card = 64 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem card_prod_genSet_B : (prodGenSet cB repB).card = 64 := by
  decide +kernel

theorem mem_of_mem_genSet {c : Perm (Fin 6)} {r : Fin 3 → Perm (Fin 6)}
    {M : Subgroup (Perm (Fin 6))} (hM : ∀ k, ⁅r k, c⁆ ∈ M ∧ ⁅c * r k * c⁻¹, c⁆ ∈ M)
    (g : Perm (Fin 6)) (hg : g ∈ genSet c r) : g ∈ M := by
  unfold genSet at hg
  simp only [Finset.mem_insert, Finset.mem_singleton] at hg
  obtain ⟨h0, h0'⟩ := hM 0
  obtain ⟨h1, h1'⟩ := hM 1
  obtain ⟨h2, h2'⟩ := hM 2
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> rw [h]
  · exact M.one_mem
  · exact h0
  · exact h0'
  · exact M.mul_mem h0 h0'
  · exact h1
  · exact h1'
  · exact M.mul_mem h1 h1'
  · exact h2
  · exact h2'
  · exact M.mul_mem h2 h2'

set_option linter.constructorNameAsVariable false in
theorem mem_of_mem_prodGenSet {c : Perm (Fin 6)} {r : Fin 3 → Perm (Fin 6)}
    {M : Subgroup (Perm (Fin 6))} (hM : ∀ k, ⁅r k, c⁆ ∈ M ∧ ⁅c * r k * c⁻¹, c⁆ ∈ M) :
    ∀ s ∈ prodGenSet c r, s ∈ M := by
  unfold prodGenSet
  rw [Finset.forall_mem_image]
  rintro ⟨a, b⟩ hab
  rw [Finset.mem_product] at hab
  exact M.mul_mem (mem_of_mem_genSet hM a hab.1) (mem_of_mem_genSet hM b hab.2)

theorem card_le_of_forall_mem {F : Finset (Perm (Fin 6))} {M : Subgroup (Perm (Fin 6))}
    (hmem : ∀ s ∈ F, s ∈ M) : F.card ≤ Nat.card M := by
  let f : {s // s ∈ F} → M := fun s => ⟨s.1, hmem s.1 s.2⟩
  have hf : Function.Injective f := fun a b h => by
    have h1 : (f a : Perm (Fin 6)) = f b := congrArg Subtype.val h
    exact Subtype.ext h1
  exact (Nat.card_eq_finsetCard F).symm.le.trans (Nat.card_le_card_of_injective f hf)

theorem card_prodGenSet_le {c : Perm (Fin 6)} {r : Fin 3 → Perm (Fin 6)}
    {M : Subgroup (Perm (Fin 6))} (hM : ∀ k, ⁅r k, c⁆ ∈ M ∧ ⁅c * r k * c⁻¹, c⁆ ∈ M) :
    (prodGenSet c r).card ≤ Nat.card M :=
  card_le_of_forall_mem (mem_of_mem_prodGenSet hM)

section Lift

variable {X : Type*} [Group X] [Finite X]

theorem mem_map_of_rep (p : X →* Perm (Fin 6))
    (hpker : ∀ g : X, p g = 1 ↔ g ∈ Subgroup.center X)
    (hpsurj : ∀ y ∈ alternatingGroup (Fin 6), ∃ g : X, p g = y)
    (hz3 : ∀ z ∈ Subgroup.center X, z ^ 3 = 1) {x : X} {T : Subgroup X}
    (hT : ∀ V : Subgroup X, ¬ 3 ∣ Nat.card V → x ∈ Subgroup.normalizer (V : Set X) →
      ⁅V, Subgroup.zpowers x⁆ ≤ T)
    {σ c r : Perm (Fin 6)} (hσ : σ * p x * σ⁻¹ = c)
    (hr : Perm.sign r = 1 ∧ r * r = 1 ∧ r * (c * r * c⁻¹) = c * r * c⁻¹ * r ∧
      c * (c * r * c⁻¹) * c⁻¹ = r * (c * r * c⁻¹)) :
    ⁅r, c⁆ ∈ (T.map p).map (MulAut.conj σ).toMonoidHom ∧
      ⁅c * r * c⁻¹, c⁆ ∈ (T.map p).map (MulAut.conj σ).toMonoidHom := by
  classical
  obtain ⟨hrs, hr2, hrc, hrcc⟩ := hr
  set φ : Perm (Fin 6) →* Perm (Fin 6) := (MulAut.conj σ).toMonoidHom with hφ
  have hφapp : ∀ g, φ g = σ * g * σ⁻¹ := fun g => MulAut.conj_apply σ g
  have hφinj : Function.Injective φ := (MulAut.conj σ).injective
  obtain ⟨ub, hub⟩ : ∃ ub : Perm (Fin 6), ub = σ⁻¹ * r * σ := ⟨_, rfl⟩
  have hφub : φ ub = r := by rw [hφapp, hub]; group
  have hubA : ub ∈ alternatingGroup (Fin 6) := by
    rw [Perm.mem_alternatingGroup, hub, Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, hrs,
      mul_one, Int.units_mul_self]
  have hub2 : ub * ub = 1 := by
    apply hφinj
    rw [map_mul, hφub, hr2, map_one]
  obtain ⟨w, hw⟩ := hpsurj ub hubA
  obtain ⟨u, hu⟩ : ∃ u : X, u = w ^ 3 := ⟨_, rfl⟩
  have hpu : p u = ub := by
    rw [hu, map_pow, hw, pow_succ, sq, hub2, one_mul]
  have hw2 : w ^ 2 ∈ Subgroup.center X := (hpker _).mp (by rw [map_pow, hw, sq, hub2])
  have hu2 : u * u = 1 := by
    rw [hu, ← pow_add, show 3 + 3 = 2 * 3 by norm_num, pow_mul]
    exact hz3 _ hw2
  have hpx : φ (p x) = c := by rw [hφapp]; exact hσ
  obtain ⟨v, hv⟩ : ∃ v : X, v = x * u * x⁻¹ := ⟨_, rfl⟩
  have hv2 : v * v = 1 := by
    rw [hv]
    calc x * u * x⁻¹ * (x * u * x⁻¹) = x * (u * u) * x⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have hφv : φ (p v) = c * r * c⁻¹ := by
    rw [hv]
    simp only [map_mul, map_inv, hpu, hφub, hpx]
  have huv : u * v = v * u := by
    have hz : ⁅u, v⁆ ∈ Subgroup.center X := by
      refine (hpker _).mp (hφinj ?_)
      rw [map_commutatorElement, map_commutatorElement, hpu, hφub, hφv, map_one,
        commutatorElement_def]
      calc r * (c * r * c⁻¹) * r⁻¹ * (c * r * c⁻¹)⁻¹
          = c * r * c⁻¹ * r * r⁻¹ * (c * r * c⁻¹)⁻¹ := by rw [hrc]
        _ = 1 := by group
    set z := ⁅u, v⁆ with hzdef
    have hzc := Subgroup.mem_center_iff.mp hz
    have hz3' := hz3 z hz
    have huinv : u⁻¹ = u := (eq_inv_of_mul_eq_one_left hu2).symm
    have hvinv : v⁻¹ = v := (eq_inv_of_mul_eq_one_left hv2).symm
    have e1 : u * v * u = z * v := by
      rw [hzdef, commutatorElement_def, huinv, hvinv]
      calc u * v * u = u * v * u * v * v := by rw [mul_assoc (u * v * u), hv2, mul_one]
        _ = u * v * u * v * v := rfl
    have e2 : v = z * z * v := by
      calc v = u * (u * v * u) * u := by
            calc v = (u * u) * v * (u * u) := by rw [hu2]; group
              _ = u * (u * v * u) * u := by group
        _ = u * (z * v) * u := by rw [e1]
        _ = z * (u * v * u) := by
            calc u * (z * v) * u = (u * z) * v * u := by group
              _ = (z * u) * v * u := by rw [hzc u]
              _ = z * (u * v * u) := by group
        _ = z * (z * v) := by rw [e1]
        _ = z * z * v := by group
    have hz2 : z * z = 1 := by
      have := congrArg (· * v⁻¹) e2
      simpa using this.symm
    have hz1 : z = 1 := by
      have h1 : z ^ 2 = 1 := by rw [sq]; exact hz2
      calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
        _ = 1 := by rw [hz3', h1, inv_one, mul_one]
    have := hz1
    rw [hzdef, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  have hxv : x * v * x⁻¹ = u * v := by
    have hz : (u * v)⁻¹ * (x * v * x⁻¹) ∈ Subgroup.center X := by
      refine (hpker _).mp (hφinj ?_)
      simp only [map_mul, map_inv, hpu, hφub, hφv, hpx, map_one]
      rw [hrcc, inv_mul_cancel]
    set z := (u * v)⁻¹ * (x * v * x⁻¹) with hzdef
    have hzc := Subgroup.mem_center_iff.mp hz
    have hz3' := hz3 z hz
    have heq : x * v * x⁻¹ = u * v * z := by rw [hzdef]; group
    have hsq1 : (x * v * x⁻¹) * (x * v * x⁻¹) = 1 := by
      calc (x * v * x⁻¹) * (x * v * x⁻¹) = x * (v * v) * x⁻¹ := by group
        _ = 1 := by rw [hv2]; group
    have huv2 : (u * v) * (u * v) = 1 := by
      calc (u * v) * (u * v) = u * (v * u) * v := by group
        _ = u * (u * v) * v := by rw [huv]
        _ = (u * u) * (v * v) := by group
        _ = 1 := by rw [hu2, hv2, mul_one]
    have hz2 : z * z = 1 := by
      rw [heq] at hsq1
      calc z * z = (u * v) * (u * v) * (z * z) := by rw [huv2, one_mul]
        _ = (u * v) * ((u * v) * z) * z := by group
        _ = (u * v) * (z * (u * v)) * z := by rw [hzc (u * v)]
        _ = u * v * z * (u * v * z) := by group
        _ = 1 := hsq1
    have hz1 : z = 1 := by
      have h1 : z ^ 2 = 1 := by rw [sq]; exact hz2
      calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
        _ = 1 := by rw [hz3', h1, inv_one, mul_one]
    rw [heq, hz1, mul_one]
  set V : Subgroup X := Subgroup.closure ({u, v} : Set X) with hV
  have hVmem : ∀ g ∈ V, g = 1 ∨ g = u ∨ g = v ∨ g = u * v := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with hg | hg
      · exact Or.inr (Or.inl hg)
      · exact Or.inr (Or.inr (Or.inl hg))
    | one => exact Or.inl rfl
    | mul g h _ _ hg hh =>
      have e3 : u * v * u = v := by
        calc u * v * u = u * (u * v) := by rw [mul_assoc, ← huv]
          _ = v := by rw [← mul_assoc, hu2, one_mul]
      have e4 : u * v * v = u := by rw [mul_assoc, hv2, mul_one]
      have e5 : v * (u * v) = u := by rw [← mul_assoc, ← huv, mul_assoc, hv2, mul_one]
      have e6 : u * v * (u * v) = 1 := by
        calc u * v * (u * v) = u * (v * u) * v := by group
          _ = u * (u * v) * v := by rw [huv]
          _ = (u * u) * (v * v) := by group
          _ = 1 := by rw [hu2, hv2, mul_one]
      have e7 : v * u = u * v := huv.symm
      have e8 : u * (u * v) = v := by rw [← mul_assoc, hu2, one_mul]
      rcases hg with rfl | rfl | rfl | rfl <;> rcases hh with rfl | rfl | rfl | rfl <;>
        simp only [one_mul, mul_one, hu2, hv2, e3, e4, e5, e6, e7, e8, true_or, or_true]
    | inv g _ hg =>
      have huinv : u⁻¹ = u := (eq_inv_of_mul_eq_one_left hu2).symm
      have hvinv : v⁻¹ = v := (eq_inv_of_mul_eq_one_left hv2).symm
      have huvinv : (u * v)⁻¹ = u * v := by rw [mul_inv_rev, huinv, hvinv, huv]
      rcases hg with rfl | rfl | rfl | rfl
      · exact Or.inl inv_one
      · exact Or.inr (Or.inl huinv)
      · exact Or.inr (Or.inr (Or.inl hvinv))
      · exact Or.inr (Or.inr (Or.inr huvinv))
  have hV2 : ∀ g ∈ V, g ^ 2 = 1 := by
    intro g hg
    have huv2 : (u * v) * (u * v) = 1 := by
      calc (u * v) * (u * v) = u * (v * u) * v := by group
        _ = u * (u * v) * v := by rw [huv]
        _ = (u * u) * (v * v) := by group
        _ = 1 := by rw [hu2, hv2, mul_one]
    rcases hVmem g hg with rfl | rfl | rfl | rfl
    · exact one_pow 2
    · rw [sq]; exact hu2
    · rw [sq]; exact hv2
    · rw [sq]; exact huv2
  have hV3 : ¬ 3 ∣ Nat.card V := by
    intro h3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := V) 3 h3
    have h2 : (g : X) ^ 2 = 1 := hV2 g g.2
    have h2' : g ^ 2 = 1 := Subtype.ext (by simpa using h2)
    have := orderOf_dvd_of_pow_eq_one h2'
    rw [hg] at this
    omega
  have huV : u ∈ V := Subgroup.subset_closure (Set.mem_insert u _)
  have hvV : v ∈ V := Subgroup.subset_closure (Set.mem_insert_of_mem u (Set.mem_singleton v))
  have hxV : x ∈ Subgroup.normalizer (V : Set X) := by
    refine mem_normalizer_of_conj_mem fun g hg => ?_
    rcases hVmem g hg with h | h | h | h <;> rw [h]
    · rw [mul_one, mul_inv_cancel]; exact V.one_mem
    · rw [← hv]; exact hvV
    · rw [hxv]; exact V.mul_mem huV hvV
    · have : x * (u * v) * x⁻¹ = v * (u * v) := by
        calc x * (u * v) * x⁻¹ = (x * u * x⁻¹) * (x * v * x⁻¹) := by group
          _ = v * (u * v) := by rw [hxv, ← hv]
      rw [this]
      exact V.mul_mem hvV (V.mul_mem huV hvV)
  have hc := hT V hV3 hxV
  have h1 : ⁅u, x⁆ ∈ T := hc (Subgroup.commutator_mem_commutator huV (Subgroup.mem_zpowers x))
  have h2 : ⁅v, x⁆ ∈ T := hc (Subgroup.commutator_mem_commutator hvV (Subgroup.mem_zpowers x))
  refine ⟨⟨p ⁅u, x⁆, ⟨_, h1, rfl⟩, ?_⟩, ⟨p ⁅v, x⁆, ⟨_, h2, rfl⟩, ?_⟩⟩
  · change φ (p ⁅u, x⁆) = ⁅r, c⁆
    rw [map_commutatorElement, map_commutatorElement, hpu, hφub, hpx]
  · change φ (p ⁅v, x⁆) = ⁅c * r * c⁻¹, c⁆
    rw [map_commutatorElement, map_commutatorElement, hφv, hpx]

end Lift

theorem eq_top_of_forall_commutator_le_tripleCover {X : Type*} [Group X] [Finite X]
    (hX : Sec4.IsTripleCover X (alternatingGroup (Fin 6))) (hXp : Group.IsPerfect X) {x : X}
    (hx3 : x ^ 3 = 1) (hxZ : x ∉ Subgroup.center X) {T : Subgroup X}
    (hT : ∀ V : Subgroup X, ¬ 3 ∣ Nat.card V → x ∈ Subgroup.normalizer (V : Set X) →
      ⁅V, Subgroup.zpowers x⁆ ≤ T) : T = ⊤ := by
  classical
  obtain ⟨hZ3, ⟨e⟩⟩ := hX
  set Z := Subgroup.center X with hZdef
  set p : X →* Perm (Fin 6) :=
    (alternatingGroup (Fin 6)).subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' Z)) with hp
  have hpker : ∀ g : X, p g = 1 ↔ g ∈ Z := by
    intro g
    simp only [hp, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom, OneMemClass.coe_eq_one, map_eq_one_iff _ e.injective,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hpA : ∀ g : X, p g ∈ alternatingGroup (Fin 6) := fun g => (e (QuotientGroup.mk g)).2
  have hpsurj : ∀ y ∈ alternatingGroup (Fin 6), ∃ g : X, p g = y := by
    intro y hy
    obtain ⟨q, hq⟩ := e.surjective ⟨y, hy⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z q
    exact ⟨g, congrArg Subtype.val hq⟩
  have hz3 : ∀ z ∈ Z, z ^ 3 = 1 := fun z hz => by
    have := Subgroup.orderOf_dvd_natCard Z hz
    rw [hZ3] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have hfib : ∀ g h : X, p g = p h → h⁻¹ * g ∈ Z := fun g h hgh => by
    rw [← hpker, map_mul, map_inv, hgh, inv_mul_cancel]
  have hx1 : p x ≠ 1 := fun h => hxZ ((hpker x).mp h)
  have hxb3 : p x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  obtain ⟨σ, hσ⟩ := exists_conj_eq_rep hxb3 hx1
  set M := (T.map p).map (MulAut.conj σ).toMonoidHom with hM
  have h64 : 64 ≤ Nat.card M := by
    rcases hσ with hσ | hσ
    · have h := card_prodGenSet_le (M := M) fun k =>
        mem_map_of_rep p hpker hpsurj hz3 hT hσ (rel_A k)
      rwa [card_prod_genSet_A] at h
    · have h := card_prodGenSet_le (M := M) fun k =>
        mem_map_of_rep p hpker hpsurj hz3 hT hσ (rel_B k)
      rwa [card_prod_genSet_B] at h
  have hMA : M ≤ alternatingGroup (Fin 6) := by
    rintro _ ⟨_, ⟨t, -, rfl⟩, rfl⟩
    have hs := Perm.mem_alternatingGroup.mp (hpA t)
    rw [Perm.mem_alternatingGroup]
    change Perm.sign (σ * p t * σ⁻¹) = 1
    rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, hs, mul_one, Int.units_mul_self]
  have hMeq : M = alternatingGroup (Fin 6) := by
    by_contra hne
    have := card_le_sixty_of_lt hMA hne
    omega
  have hcardT : Nat.card (T.map p) = 360 := by
    have h1 : Nat.card M = Nat.card (T.map p) :=
      Subgroup.card_map_of_injective (MulAut.conj σ).injective
    rw [← h1, hMeq, card_alternatingGroup_six]
  have hTA : T.map p = alternatingGroup (Fin 6) := by
    refine Subgroup.eq_of_le_of_card_ge (fun _ ⟨t, _, ht⟩ => ht ▸ hpA t) ?_
    rw [hcardT, card_alternatingGroup_six]
  have hdecomp : ∀ g : X, ∃ q ∈ T, q⁻¹ * g ∈ Z := fun g => by
    have : p g ∈ T.map p := hTA ▸ hpA g
    obtain ⟨q, hq, hqg⟩ := this
    exact ⟨q, hq, hfib g q hqg.symm⟩
  have hcomm : commutator X ≤ T := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g _ h _
    obtain ⟨q, hq, hqz⟩ := hdecomp g
    obtain ⟨q', hq', hq'z⟩ := hdecomp h
    have hg : g = q * (q⁻¹ * g) := by group
    have hh : h = q' * (q'⁻¹ * h) := by group
    rw [hg, hh, commutatorElement_mul_central hqz hq'z]
    exact T.mul_mem (T.mul_mem (T.mul_mem hq hq') (T.inv_mem hq)) (T.inv_mem hq')
  exact top_le_iff.mp (hXp.commutator_eq_top ▸ hcomm)

theorem le_of_forall_commutator_le_tripleCover {Γ : Type*} [Group Γ] {K : Subgroup Γ}
    [Finite K] (hK : Sec4.IsTripleCover ↥K (alternatingGroup (Fin 6)))
    (hKp : Group.IsPerfect ↥K) {x : Γ} (hxK : x ∈ K) (hx3 : x ^ 3 = 1)
    (hxZ : ∃ y ∈ K, x * y ≠ y * x) {H : Subgroup Γ}
    (hH : ∀ V : Subgroup Γ, V ≤ K → ¬ 3 ∣ Nat.card V →
      x ∈ Subgroup.normalizer (V : Set Γ) → ⁅V, Subgroup.zpowers x⁆ ≤ H) : K ≤ H := by
  set x' : K := ⟨x, hxK⟩ with hx'
  have hx'3 : x' ^ 3 = 1 := Subtype.ext (by simpa [hx'] using hx3)
  have hx'Z : x' ∉ Subgroup.center K := by
    intro hc
    obtain ⟨y, hy, hxy⟩ := hxZ
    exact hxy (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hc ⟨y, hy⟩).symm))
  have htop := eq_top_of_forall_commutator_le_tripleCover hK hKp hx'3 hx'Z
    (T := H.subgroupOf K) fun V hV3 hxV => by
      set W : Subgroup Γ := V.map K.subtype with hW
      have hWK : W ≤ K := Subgroup.map_subtype_le V
      have hW3 : ¬ 3 ∣ Nat.card W := by
        rwa [hW, Subgroup.card_map_of_injective K.subtype_injective]
      have hxW : x ∈ Subgroup.normalizer (W : Set Γ) := by
        rw [Subgroup.mem_normalizer_iff]
        intro g
        constructor
        · rintro ⟨v, hv, rfl⟩
          exact ⟨x' * v * x'⁻¹, (Subgroup.mem_normalizer_iff.mp hxV v).mp hv, rfl⟩
        · rintro ⟨v, hv, hveq⟩
          have hgK : g ∈ K := by
            have h1 : x⁻¹ * (x * g * x⁻¹) * x ∈ K :=
              K.mul_mem (K.mul_mem (K.inv_mem hxK) (hveq ▸ v.2)) hxK
            simpa [mul_assoc] using h1
          refine ⟨⟨g, hgK⟩, ?_, rfl⟩
          have h2 : x' * ⟨g, hgK⟩ * x'⁻¹ = v := Subtype.ext hveq.symm
          exact (Subgroup.mem_normalizer_iff.mp hxV ⟨g, hgK⟩).mpr (by rw [h2]; exact hv)
      have hc := hH W hWK hW3 hxW
      intro y hy
      rw [Subgroup.mem_subgroupOf]
      have hmap : (⁅V, Subgroup.zpowers x'⁆).map K.subtype = ⁅W, Subgroup.zpowers x⁆ := by
        rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
        rfl
      exact hc (hmap ▸ ⟨y, hy, rfl⟩)
  intro g hg
  have : (⟨g, hg⟩ : K) ∈ H.subgroupOf K := htop ▸ Subgroup.mem_top _
  exact this

end CFSG.RankThree.PartTwo.Sec14.Ronan148J
