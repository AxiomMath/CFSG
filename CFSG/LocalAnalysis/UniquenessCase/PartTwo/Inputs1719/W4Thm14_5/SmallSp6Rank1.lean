module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RepresentationTheory.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open Module

variable {G : Type*} [Group G] {k : Type*} [Field k] [CharP k 2] {V : Type*} [AddCommGroup V]
  [Module k V] {K : Type*} [Field K] [Fintype K] [CharP K 2]

omit [CharP K 2] in
theorem sum_univ_eq_zero_of_four_le (hK : 4 ≤ Fintype.card K) : ∑ c : K, c = 0 := by
  have h := FiniteField.sum_pow_lt_card_sub_one (K := K) 1 (by omega)
  simpa using h

omit [CharP k 2] [CharP K 2] in
theorem sum_additive_eq_zero (hK : 4 ≤ Fintype.card K) (B : K →+ k) : ∑ c : K, B c = 0 := by
  rw [← map_sum, sum_univ_eq_zero_of_four_le hK, map_zero]

theorem natCast_card_eq_zero_charTwo : (Fintype.card K : k) = 0 := by
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [hn, Nat.cast_pow, Nat.cast_ofNat, CharTwo.two_eq_zero, zero_pow (PNat.ne_zero n)]

theorem eq_one_of_sq_eq_one_charTwo {a : k} (ha : a ^ 2 = 1) : a = 1 :=
  CharTwo.sq_inj.mp (ha.trans (one_pow 2).symm)

theorem exists_units_sq_eq {b : K} (hb : b ≠ 0) : ∃ a : Kˣ, (a : K) ^ 2 = b := by
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' b
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr
    exact hb hr
  exact ⟨Units.mk0 r hr0, by rw [Units.val_mk0, sq, hr]⟩

omit [CharP k 2] in
theorem eq_of_pair {y w : V} (hli : LinearIndependent k ![y, w]) {a b c d : k}
    (h : a • y + b • w = c • y + d • w) : a = c ∧ b = d := by
  have h1 := LinearIndependent.pair_iff.mp hli (a - c) (b - d) (by
    rw [sub_smul, sub_smul]
    calc a • y - c • y + (b • w - d • w) = (a • y + b • w) - (c • y + d • w) := by abel
      _ = 0 := by rw [h, sub_self])
  exact ⟨sub_eq_zero.mp h1.1, sub_eq_zero.mp h1.2⟩

theorem exists_apply_eq_add_smul {y w : V} (hli : LinearIndependent k ![y, w])
    {u : V →ₗ[k] V} (huS : u w ∈ Submodule.span k {y, w}) (huy : u y = y)
    (huu : u (u w) = w) : ∃ β : k, u w = w + β • y := by
  obtain ⟨α, β', hαβ⟩ := Submodule.mem_span_pair.mp huS
  rw [← hαβ, map_add, map_smul, map_smul, huy, ← hαβ] at huu
  have hcoef : (α + β' * α) • y + (β' * β') • w = (0 : k) • y + (1 : k) • w := by
    rw [zero_smul, one_smul, zero_add]
    conv_rhs => rw [← huu]
    rw [smul_add, add_smul, mul_smul, mul_smul]
    abel
  have hb : β' * β' = 1 := (eq_of_pair hli hcoef).2
  have hb1 : β' = 1 := eq_one_of_sq_eq_one_charTwo (by rw [sq, hb])
  exact ⟨α, by rw [← hαβ, hb1, one_smul, add_comm]⟩

omit [CharP k 2] in
theorem mem_of_inv_stable [FiniteDimensional k V] (ρ : Representation k G V) (S : Submodule k V)
    {g : G} (hS : ∀ v ∈ S, ρ g v ∈ S) {v : V} (hv : v ∈ S) : ρ g⁻¹ v ∈ S := by
  have hinj : Function.Injective (ρ g) := fun a b hab => by
    have := congrArg (ρ g⁻¹) hab
    rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply, Module.End.one_apply] at this
  have hle : S.map (ρ g) ≤ S := by
    rintro _ ⟨u, hu, rfl⟩
    exact hS u hu
  have hfr : finrank k (S.map (ρ g)) = finrank k S :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (ρ g) hinj S)).symm
  have heq := Submodule.eq_of_le_of_finrank_eq hle hfr
  rw [← heq] at hv
  obtain ⟨u, hu, rfl⟩ := hv
  rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem hecke_eq_zero_and_char (hK : 4 ≤ Fintype.card K) (ρ : Representation k G V)
    [FiniteDimensional k V] (S : Submodule k V) (hdim : finrank k S ≤ 2) (x : K → G)
    (hxadd : ∀ c d, x (c + d) = x c * x d) (h : Kˣ →* G) (n₀ : G)
    (hxh : ∀ (a : Kˣ) (c : K), h a * x c * (h a)⁻¹ = x ((a : K) ^ 2 * c))
    (hnh : ∀ a : Kˣ, n₀ * h a * n₀⁻¹ = h a⁻¹)
    (hn2 : ∃ a₀ : Kˣ, n₀ * n₀ = h a₀)
    (hhX : ∀ a : Kˣ, h a ∈ Subgroup.closure
      (Set.range x ∪ (fun g => n₀ * g * n₀⁻¹) '' Set.range x))
    (hSx : ∀ c, ∀ v ∈ S, ρ (x c) v ∈ S) (hSn : ∀ v ∈ S, ρ n₀ v ∈ S)
    (hirr : ∀ T : Submodule k V, T ≤ S → (∀ c, ∀ v ∈ T, ρ (x c) v ∈ T) →
      (∀ v ∈ T, ρ n₀ v ∈ T) → T = ⊥ ∨ T = S)
    {y₀ : V} (hy₀S : y₀ ∈ S) (hy₀ : y₀ ≠ 0) (hfix : ∀ c, ρ (x c) y₀ = y₀) (lam : Kˣ → k)
    (hlam : ∀ a, ρ (h a) y₀ = lam a • y₀) :
    (∑ c : K, ρ (x c * n₀) y₀ = 0) ∧
      ((∀ a, lam a = 1) ∨ ∃ φ : K →+* k, ∀ a : Kˣ, lam a = φ a) := by
  classical
  have hρmul : ∀ g g' v, ρ (g * g') v = ρ g (ρ g' v) := fun g g' v => by
    rw [map_mul, Module.End.mul_apply]
  have hρone : ∀ v, ρ 1 v = v := fun v => by rw [map_one, Module.End.one_apply]
  have hρinv : ∀ g v, ρ g⁻¹ (ρ g v) = v := fun g v => by
    rw [← hρmul, inv_mul_cancel, hρone]
  have hinj := smul_left_injective k hy₀
  have hx0 : x 0 = 1 := mul_eq_left.mp ((hxadd 0 0).symm.trans (by rw [add_zero]))
  have hlam1 : lam 1 = 1 := by
    apply hinj
    change lam 1 • y₀ = (1 : k) • y₀
    rw [← hlam, map_one, hρone, one_smul]
  have hlammul : ∀ a b, lam (a * b) = lam a * lam b := fun a b => by
    apply hinj
    change lam (a * b) • y₀ = (lam a * lam b) • y₀
    rw [← hlam, map_mul h, hρmul, hlam b, map_smul, hlam a, smul_smul, mul_comm]
  have hlaminv : ∀ a, lam a * lam a⁻¹ = 1 := fun a => by
    rw [← hlammul, mul_inv_cancel, hlam1]
  set w₀ := ρ n₀ y₀ with hw₀
  have hw₀S : w₀ ∈ S := hSn y₀ hy₀S
  have hhw : ∀ a, ρ (h a) w₀ = lam a⁻¹ • w₀ := fun a => by
    have e : h a * n₀ = n₀ * h a⁻¹ := by
      have := hnh a⁻¹
      rw [inv_inv] at this
      calc h a * n₀ = n₀ * h a⁻¹ * n₀⁻¹ * n₀ := by rw [this]
        _ = n₀ * h a⁻¹ := by group
    rw [hw₀, ← hρmul, e, hρmul, hlam, map_smul]
  by_cases hw : w₀ ∈ Submodule.span k {y₀}
  ·
    obtain ⟨c₀, hc₀⟩ := Submodule.mem_span_singleton.mp hw
    refine ⟨?_, Or.inl fun a => ?_⟩
    · have hterm : ∀ c, ρ (x c * n₀) y₀ = c₀ • y₀ := fun c => by
        rw [hρmul, ← hw₀, ← hc₀, map_smul, hfix]
      simp_rw [hterm, Finset.sum_const, Finset.card_univ]
      rw [← Nat.cast_smul_eq_nsmul k, natCast_card_eq_zero_charTwo, zero_smul]
    · have hc0 : c₀ ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hc₀
        apply hy₀
        have := hρinv n₀ y₀
        rw [← hw₀, ← hc₀, map_zero] at this
        exact this.symm
      have h1 := hhw a
      rw [← hc₀, map_smul, hlam, smul_smul, smul_smul] at h1
      have h2 : c₀ * lam a = lam a⁻¹ * c₀ := hinj h1
      have h4 : lam a = lam a⁻¹ := by
        rw [mul_comm (lam a⁻¹)] at h2
        exact mul_left_cancel₀ hc0 h2
      have h5 := hlaminv a
      rw [← h4, ← sq] at h5
      exact eq_one_of_sq_eq_one_charTwo h5
  ·
    have hli : LinearIndependent k ![y₀, w₀] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      by_cases ht : t = 0
      · subst ht
        rw [zero_smul, add_zero] at hst
        exact ⟨(smul_eq_zero.mp hst).resolve_right hy₀, rfl⟩
      · exfalso
        apply hw
        rw [Submodule.mem_span_singleton]
        refine ⟨-(t⁻¹ * s), ?_⟩
        have h1 : t • w₀ = -(s • y₀) := eq_neg_of_add_eq_zero_right hst
        calc -(t⁻¹ * s) • y₀ = t⁻¹ • -(s • y₀) := by rw [smul_neg, smul_smul, neg_smul]
          _ = t⁻¹ • (t • w₀) := by rw [h1]
          _ = w₀ := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
    have hfr2 : finrank k (Submodule.span k {y₀, w₀}) = 2 := by
      have := finrank_span_eq_card hli
      rw [Fintype.card_fin] at this
      rwa [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union] at this
    have hspan : Submodule.span k {y₀, w₀} = S := by
      have hle : Submodule.span k {y₀, w₀} ≤ S := by
        rw [Submodule.span_le]
        rintro v (rfl | rfl)
        · exact hy₀S
        · exact hw₀S
      exact Submodule.eq_of_le_of_finrank_le hle (by omega)
    have hN : ∀ c, ∃ β : k, ρ (x c) w₀ = w₀ + β • y₀ := fun c => by
      refine exists_apply_eq_add_smul hli ?_ (hfix c) ?_
      · rw [hspan]; exact hSx c w₀ hw₀S
      · rw [← hρmul, ← hxadd, CharTwo.add_self_eq_zero, hx0, hρone]
    choose B hB using hN
    have hBadd : ∀ c d, B (c + d) = B c + B d := fun c d => by
      apply hinj
      have h1 := hB (c + d)
      rw [hxadd, hρmul, hB d, map_add, map_smul, hfix, hB c, add_assoc, ← add_smul] at h1
      exact (add_left_cancel h1).symm
    have hB0 : B 0 = 0 := by
      have := hBadd 0 0
      rw [add_zero] at this
      exact (left_eq_add.mp this)
    let Bhom : K →+ k := { toFun := B, map_zero' := hB0, map_add' := hBadd }
    have hsum : ∑ c : K, ρ (x c * n₀) y₀ = 0 := by
      have hterm : ∀ c, ρ (x c * n₀) y₀ = w₀ + B c • y₀ := fun c => by
        rw [hρmul, ← hw₀, hB]
      simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        ← Finset.sum_smul]
      rw [← Nat.cast_smul_eq_nsmul k, natCast_card_eq_zero_charTwo, zero_smul, zero_add]
      have := sum_additive_eq_zero hK Bhom
      change (∑ c : K, Bhom c) • y₀ = 0
      rw [this, zero_smul]
    refine ⟨hsum, Or.inr ?_⟩
    have hBtor : ∀ (a : Kˣ) (c : K), B ((a : K) ^ 2 * c) = lam a ^ 2 * B c := fun a c => by
      apply hinj
      have hinv : ρ (h a)⁻¹ w₀ = lam a • w₀ := by rw [← map_inv h, hhw, inv_inv]
      have h1 : ρ (x ((a : K) ^ 2 * c)) w₀ = w₀ + (lam a ^ 2 * B c) • y₀ := by
        rw [← hxh a c, hρmul, hρmul, hinv, map_smul, hB c, map_smul, map_add, map_smul, hhw,
          hlam, smul_add, smul_smul, smul_smul, smul_smul, hlaminv, one_smul]
        congr 2
        ring
      have h2 := (hB ((a : K) ^ 2 * c)).symm.trans h1
      exact add_left_cancel h2
    have hB1 : B 1 ≠ 0 := by
      intro hB1
      have hBz : ∀ c, B c = 0 := fun c => by
        by_cases hc : c = 0
        · subst hc; exact hB0
        · obtain ⟨a, ha⟩ := exists_units_sq_eq hc
          have := hBtor a 1
          rwa [mul_one, ha, hB1, mul_zero] at this
      have hxS : ∀ c, ∀ v ∈ S, ρ (x c) v = v := fun c v hv => by
        rw [← hspan] at hv
        obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hv
        rw [map_add, map_smul, map_smul, hfix, hB c, hBz c, zero_smul, add_zero]
      have hclos : ∀ g ∈ Subgroup.closure
          (Set.range x ∪ (fun g => n₀ * g * n₀⁻¹) '' Set.range x), ∀ v ∈ S, ρ g v = v := by
        intro g hg
        induction hg using Subgroup.closure_induction with
        | mem g hg =>
          rcases hg with ⟨c, rfl⟩ | ⟨_, ⟨c, rfl⟩, rfl⟩
          · exact hxS c
          · intro v hv
            have hv' := mem_of_inv_stable ρ S hSn hv
            rw [hρmul, hρmul, hxS c _ hv', ← hρmul, mul_inv_cancel, hρone]
        | one => exact fun v _ => hρone v
        | mul g g' _ _ hg hg' => exact fun v hv => by rw [hρmul, hg' v hv, hg v hv]
        | inv g _ hg =>
          intro v hv
          have := hρinv g v
          rwa [hg v hv] at this
      obtain ⟨a₀, ha₀⟩ := hn2
      have hnn : ρ n₀ w₀ = y₀ := by
        rw [hw₀, ← hρmul, ha₀, hclos _ (hhX a₀) y₀ hy₀S]
      have hfixv : ρ n₀ (y₀ + w₀) = y₀ + w₀ := by
        rw [map_add, hnn, ← hw₀, add_comm]
      have hv0 : y₀ + w₀ ≠ 0 := by
        intro h0
        have := (LinearIndependent.pair_iff.mp hli) 1 1 (by rw [one_smul, one_smul, h0])
        exact one_ne_zero this.1
      have hvS : y₀ + w₀ ∈ S := S.add_mem hy₀S hw₀S
      rcases hirr (Submodule.span k {y₀ + w₀}) (by
          rw [Submodule.span_le, Set.singleton_subset_iff]; exact hvS)
        (fun c u hu => by
          rw [hxS c u (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvS) hu)]
          exact hu)
        (fun u hu => by
          obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hu
          rw [map_smul, hfixv]
          exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)) with hb | ht
      · apply hv0
        have := Submodule.mem_span_singleton_self (R := k) (y₀ + w₀)
        rw [hb] at this
        exact (Submodule.mem_bot k).mp this
      · have h1 := finrank_span_singleton (K := k) hv0
        rw [ht, ← hspan, hfr2] at h1
        omega
    set φ₀ : K → k := fun c => (B 1)⁻¹ * B c with hφ₀
    have hφadd : ∀ c d, φ₀ (c + d) = φ₀ c + φ₀ d := fun c d => by
      simp only [hφ₀, hBadd, mul_add]
    have hφ0 : φ₀ 0 = 0 := by simp only [hφ₀, hB0, mul_zero]
    have hφ1 : φ₀ 1 = 1 := by simp only [hφ₀, inv_mul_cancel₀ hB1]
    have hφsq : ∀ (a : Kˣ) (c : K), φ₀ ((a : K) ^ 2 * c) = lam a ^ 2 * φ₀ c := fun a c => by
      simp only [hφ₀, hBtor]; ring
    have hφsq1 : ∀ a : Kˣ, φ₀ ((a : K) ^ 2) = lam a ^ 2 := fun a => by
      have := hφsq a 1
      rwa [mul_one, hφ1, mul_one] at this
    have hφmul : ∀ b c, φ₀ (b * c) = φ₀ b * φ₀ c := fun b c => by
      by_cases hb : b = 0
      · subst hb
        rw [zero_mul, hφ0, zero_mul]
      · obtain ⟨a, ha⟩ := exists_units_sq_eq hb
        rw [← ha, hφsq, hφsq1]
    let φ : K →+* k :=
      { toFun := φ₀, map_one' := hφ1, map_mul' := hφmul, map_zero' := hφ0, map_add' := hφadd }
    refine ⟨φ, fun a => ?_⟩
    have h1 := hφsq1 a
    rw [sq, hφmul, ← sq] at h1
    exact (CharTwo.sq_inj.mp h1).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
