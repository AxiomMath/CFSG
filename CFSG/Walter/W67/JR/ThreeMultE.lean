module

public import CFSG.Walter.W67.JR.ThreeMultLayers
public import CFSG.Assembly.OrderReductions.FixedPointLifting
public import CFSG.Walter.W67.W1Basic
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Walter.W67

namespace ThreeMult

open scoped commutatorElement Pointwise

variable {E L : Type*} [Group E] [Group L]

theorem map_comap_eq_of_surjective {π : E →* L} (hπ : Function.Surjective π) (P : Subgroup L) :
    (P.comap π).map π = P :=
  Subgroup.map_comap_eq_self_of_surjective hπ P

theorem map_γ {π : E →* L} (hπ : Function.Surjective π) (P : Subgroup L) (i : ℕ) :
    (γ (P.comap π) i).map π = P.lowerCentralSeries i := by
  rw [Subgroup.map_lowerCentralSeries, map_comap_eq_of_surjective hπ]

theorem mem_γ_of_map_mem {π : E →* L} (hπ : Function.Surjective π) {P : Subgroup L} {i : ℕ}
    (hker : π.ker ≤ γ (P.comap π) i) {x : E} (hx : π x ∈ P.lowerCentralSeries i) :
    x ∈ γ (P.comap π) i := by
  rw [← map_γ hπ P i] at hx
  obtain ⟨c, hc, hcx⟩ := hx
  have : c⁻¹ * x ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcx, inv_mul_cancel]
  have h2 := Subgroup.mul_mem _ hc (hker this)
  rwa [mul_inv_cancel_left] at h2

theorem le_commutator_of_perfect [Finite E] {Z H : Subgroup E} (hZc : Z ≤ Subgroup.center E)
    (hZ3 : IsPGroup 3 Z) (hZH : Z ≤ H) (hidx : ¬ 3 ∣ H.index) (hperf : commutator E = ⊤) :
    Z ≤ ⁅H, H⁆ := by
  intro z hz
  have hzc : z ∈ Subgroup.center E := hZc hz
  let φ : ↥H →* Abelianization ↥H := Abelianization.of
  let τ : E →* Abelianization ↥H := MonoidHom.transfer φ
  have hτ1 : τ z = 1 := by
    have hker : commutator E ≤ τ.ker := Abelianization.commutator_subset_ker τ
    rw [hperf] at hker
    exact hker (Subgroup.mem_top z)
  have hτ2 := MonoidHom.transfer_eq_pow φ z (fun k g₀ _ => by
    have hk : z ^ k ∈ Subgroup.center E := Subgroup.pow_mem _ hzc k
    rw [Subgroup.mem_center_iff] at hk
    rw [mul_assoc, ← hk g₀, ← mul_assoc, inv_mul_cancel, one_mul])
  have hmem : (⟨z ^ H.index, Subgroup.pow_mem _ (hZH hz) _⟩ : ↥H) ∈ commutator ↥H := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    exact hτ2.symm.trans hτ1
  have hmap : (commutator ↥H).map H.subtype = ⁅H, H⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hzi : z ^ H.index ∈ ⁅H, H⁆ := by
    rw [← hmap]
    exact ⟨_, hmem, rfl⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hZ3) ⟨z, hz⟩
  rw [Subgroup.orderOf_mk] at hk
  have hcop : Nat.Coprime H.index (orderOf z) := by
    rw [hk]
    exact Nat.Coprime.pow_right k
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hidx).symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact Subgroup.pow_mem _ hzi m

section Aut

variable (P : Subgroup E)

theorem conjγ_inv (g : Subgroup.normalizer (P : Set E)) (i : ℕ) (x : γ P i) :
    conjγ ((g⁻¹ : Subgroup.normalizer (P : Set E)) : E) (g⁻¹).2 i (conjγ (g : E) g.2 i x) = x := by
  apply Subtype.ext
  change (g : E)⁻¹ * ((g : E) * x * (g : E)⁻¹) * ((g : E)⁻¹)⁻¹ = x
  group

theorem conjγ_inv' (g : Subgroup.normalizer (P : Set E)) (i : ℕ) (x : γ P i) :
    conjγ (g : E) g.2 i (conjγ ((g⁻¹ : Subgroup.normalizer (P : Set E)) : E) (g⁻¹).2 i x) = x := by
  apply Subtype.ext
  change (g : E) * ((g : E)⁻¹ * x * ((g : E)⁻¹)⁻¹) * (g : E)⁻¹ = x
  group

@[expose] noncomputable def γAut (i : ℕ) : Subgroup.normalizer (P : Set E) →* MulAut ↥(γ P i) where
  toFun g :=
    { toFun := conjγ (g : E) g.2 i
      invFun := conjγ ((g⁻¹ : Subgroup.normalizer (P : Set E)) : E) (g⁻¹).2 i
      left_inv := conjγ_inv P g i
      right_inv := conjγ_inv' P g i
      map_mul' := map_mul _ }
  map_one' := by
    ext x
    change (1 : E) * x * (1 : E)⁻¹ = x
    group
  map_mul' g h := by
    ext x
    change ((g : E) * h) * x * ((g : E) * h)⁻¹ = (g : E) * ((h : E) * x * (h : E)⁻¹) * (g : E)⁻¹
    group

theorem γAut_apply (i : ℕ) (g : Subgroup.normalizer (P : Set E)) (x : γ P i) :
    ((γAut P i g x : γ P i) : E) = g * x * (g : E)⁻¹ := rfl

theorem layerConj_inv (g : Subgroup.normalizer (P : Set E)) (i : ℕ) (x : LayerQ P i) :
    layerConj ((g⁻¹ : Subgroup.normalizer (P : Set E)) : E) (g⁻¹).2 i
      (layerConj (g : E) g.2 i x) = x := by
  induction x using QuotientGroup.induction_on with
  | H x =>
  change lmk P _ = lmk P x
  congr 1
  exact conjγ_inv P g i x

theorem layerConj_inv' (g : Subgroup.normalizer (P : Set E)) (i : ℕ) (x : LayerQ P i) :
    layerConj (g : E) g.2 i
      (layerConj ((g⁻¹ : Subgroup.normalizer (P : Set E)) : E) (g⁻¹).2 i x) = x := by
  induction x using QuotientGroup.induction_on with
  | H x =>
  change lmk P _ = lmk P x
  congr 1
  exact conjγ_inv' P g i x

@[expose] noncomputable def layerAut (i : ℕ) :
    Subgroup.normalizer (P : Set E) →* MulAut (LayerQ P i) where
  toFun g :=
    { toFun := layerConj (g : E) g.2 i
      invFun := layerConj ((g⁻¹ : Subgroup.normalizer (P : Set E)) : E) (g⁻¹).2 i
      left_inv := layerConj_inv P g i
      right_inv := layerConj_inv' P g i
      map_mul' := map_mul _ }
  map_one' := by
    ext x
    exact layerConj_of_mem_center (P := P) _ (Subgroup.one_mem _) i x
  map_mul' g h := by
    ext x
    exact layerConj_mul (P := P) g.2 h.2 i x

theorem layerAut_apply (i : ℕ) (g : Subgroup.normalizer (P : Set E)) (x : LayerQ P i) :
    layerAut P i g x = layerConj (g : E) g.2 i x := rfl

end Aut

theorem zpow_apply_eq_of_apply_eq {X : Type*} [Group X] {σ : MulAut X} {x : X} (h : σ x = x)
    (k : ℤ) : (σ ^ k) x = x := by
  have hinv : σ⁻¹ x = x := by
    conv_lhs => rw [← h]
    exact σ.symm_apply_apply x
  induction k using Int.induction_on with
  | zero => rfl
  | succ k ih =>
    rw [zpow_add, zpow_one, MulAut.mul_apply, h, ih]
  | pred k ih =>
    rw [zpow_sub, zpow_one, MulAut.mul_apply, hinv, ih]

theorem layerConj_free [Finite E] [Finite L] {π : E →* L} (hπ : Function.Surjective π)
    {Z : Subgroup E} (hker : π.ker = Z) (hZ3 : IsPGroup 3 Z)
    {P : Subgroup L} (hP3 : IsPGroup 3 P) (hZγ : Z ≤ γ (P.comap π) 1)
    {a : L} (ha3 : ¬ 3 ∣ orderOf a)
    (hodd : ∀ w ∈ Subgroup.zpowers a, w ≠ 1 → Odd (orderOf w) → ∀ x ∈ P, w * x * w⁻¹ = x → x = 1)
    (hinv : ∀ w ∈ Subgroup.zpowers a, orderOf w = 2 → ∀ x ∈ P, w * x * w⁻¹ = x → x ∈ ⁅P, P⁆)
    {g : E} (hg : g ∈ Subgroup.normalizer ((P.comap π : Subgroup E) : Set E)) (hga : π g = a)
    {j : ℕ} (hj : a ^ j ≠ 1) (v : LayerQ (P.comap π) 0)
    (hv : (layerConj g hg 0)^[j] v = v) : v = 1 := by
  have hd1 : orderOf (a ^ j) ≠ 1 := fun h => hj (orderOf_eq_one_iff.mp h)
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hd1
  have : Fact r.Prime := ⟨hr⟩
  have hd0 : orderOf (a ^ j) ≠ 0 := (orderOf_pos (a ^ j)).ne'
  have hr3 : r ≠ 3 := fun h => ha3 (h ▸ hrd.trans (orderOf_pow_dvd j))
  set e₁ := orderOf (a ^ j) / r with he₁
  have hw₁o : orderOf ((a ^ j) ^ e₁) = r := orderOf_pow_orderOf_div hd0 hrd
  obtain ⟨s, hs⟩ := hZ3.exists_card_eq
  set u := (g ^ (j * e₁)) ^ (3 ^ s) with hu
  have hπu : π u = ((a ^ j) ^ e₁) ^ (3 ^ s) := by
    rw [hu, map_pow, map_pow, hga, pow_mul]
  have hcop3 : Nat.Coprime r (3 ^ s) :=
    Nat.Coprime.pow_right s ((Nat.coprime_primes hr Nat.prime_three).mpr hr3)
  have hπuo : orderOf (π u) = r := by
    rw [hπu, Nat.Coprime.orderOf_pow (by rw [hw₁o]; exact hcop3), hw₁o]
  have hur : u ^ r = 1 := by
    have h1 : (g ^ (j * e₁)) ^ r ∈ Z := by
      rw [← hker, MonoidHom.mem_ker, map_pow, map_pow, hga, pow_mul, ← hw₁o, pow_orderOf_eq_one]
    have h2 : orderOf ((g ^ (j * e₁)) ^ r) ∣ 3 ^ s := by
      rw [← hs, ← Subgroup.orderOf_mk _ h1]
      exact orderOf_dvd_natCard _
    show ((g ^ (j * e₁)) ^ (3 ^ s)) ^ r = 1
    rw [← pow_mul, mul_comm (3 ^ s) r, pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.mp h2
  have hu1 : u ≠ 1 := by
    intro h
    have : orderOf (π u) = 1 := by rw [h, map_one, orderOf_one]
    rw [hπuo] at this
    exact hr.one_lt.ne' this
  have huo : orderOf u = r := orderOf_eq_prime hur hu1
  have huN : u ∈ Subgroup.normalizer ((P.comap π : Subgroup E) : Set E) :=
    Subgroup.pow_mem _ (Subgroup.pow_mem _ hg _) _
  have hvu : layerConj u huN 0 v = v := by
    have h1 : layerConj u huN 0 v = (layerConj g hg 0)^[j * e₁ * 3 ^ s] v := by
      have key : ∀ (b c : E) (hb : b ∈ Subgroup.normalizer ((P.comap π : Subgroup E) : Set E))
          (hc : c ∈ Subgroup.normalizer ((P.comap π : Subgroup E) : Set E)), b = c →
          layerConj b hb 0 v = layerConj c hc 0 v := by
        intro b c hb hc hbc
        subst hbc
        rfl
      rw [key u (g ^ (j * e₁ * 3 ^ s)) huN (Subgroup.pow_mem _ hg _) (by rw [hu, ← pow_mul])]
      exact layerConj_pow hg 0 _ v
    rw [h1, mul_assoc, Function.iterate_mul]
    exact Function.IsFixedPt.iterate hv _
  let N := Subgroup.normalizer ((P.comap π : Subgroup E) : Set E)
  let actor : Subgroup N := Subgroup.zpowers ⟨u, huN⟩
  have hactor : IsPGroup r actor := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, huo, pow_one])
  have hPtcard : ∃ m, Nat.card ↥(γ (P.comap π) 0) = 3 ^ m := by
    obtain ⟨t, ht⟩ := hP3.exists_card_eq
    refine ⟨t + s, ?_⟩
    have h1 := card_eq_card_map_mul_card_inf_ker π (γ (P.comap π) 0)
    have h2 : (γ (P.comap π) 0).map π = P := map_γ hπ P 0
    have h3 : γ (P.comap π) 0 ⊓ π.ker = Z := by
      rw [hker]
      refine inf_eq_right.mpr fun z hz => ?_
      change π z ∈ P
      have : π z = 1 := by rw [← MonoidHom.mem_ker, hker]; exact hz
      rw [this]
      exact P.one_mem
    rw [h1, h2, h3, ht, hs, pow_add]
  have hcoprime : ¬ r ∣ Nat.card ↥(γ (P.comap π) 0) := by
    obtain ⟨m, hm⟩ := hPtcard
    rw [hm]
    intro h
    exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hr.dvd_of_dvd_pow h))
  obtain ⟨x, hxv, hxfix⟩ := CFSG.OrderReductions.FixedPointLifting.exists_fixed_lift_of_coprime
    r hactor ((γAut (P.comap π) 0).comp actor.subtype)
    ((layerAut (P.comap π) 0).comp actor.subtype) (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) hcoprime (fun _ _ => rfl) v (fun acting => by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp acting.2
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, ← hk, map_zpow]
      exact zpow_apply_eq_of_apply_eq hvu k)
  have hux : u * (x : E) * u⁻¹ = x := by
    have := hxfix ⟨⟨u, huN⟩, Subgroup.mem_zpowers _⟩
    exact congrArg Subtype.val this
  have hxP : π x ∈ P := γ_le (P.comap π) 0 x.2
  have hπux : π u * π x * (π u)⁻¹ = π x := by
    rw [← map_mul, ← map_inv, ← map_mul, hux]
  have hπua : π u ∈ Subgroup.zpowers a := by
    rw [hπu]
    exact Subgroup.pow_mem _ (Subgroup.pow_mem _ (Subgroup.pow_mem _
      (Subgroup.mem_zpowers a) _) _) _
  have hxγ : (x : E) ∈ γ (P.comap π) 1 := by
    by_cases hr2 : r = 2
    · have h := hinv (π u) hπua (hπuo.trans hr2) (π x) hxP hπux
      exact mem_γ_of_map_mem hπ (hker ▸ hZγ) h
    · have hodd' : Odd (orderOf (π u)) := by
        rw [hπuo]
        exact hr.odd_of_ne_two hr2
      have hπu1 : π u ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hπuo
        exact hr.one_lt.ne hπuo
      have h := hodd (π u) hπua hπu1 hodd' (π x) hxP hπux
      exact hZγ (by rw [← hker, MonoidHom.mem_ker]; exact h)
  rw [← hxv]
  exact (QuotientGroup.eq_one_iff _).mpr (by rw [Subgroup.mem_subgroupOf]; exact hxγ)

end ThreeMult

end CFSG.Walter.W67
