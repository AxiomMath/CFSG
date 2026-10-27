module

public import CFSG.Walter.Ree.Thompson3.Stab

public section

namespace CFSG.Walter.Ree.T2

variable {k : Type} [Field k] [CharP k 3]

omit [CharP k 3] in
theorem units_eq_sq_or_neg_sq [Finite k] (hneg : ¬IsSquare (-1 : k)) (t : kˣ) :
    ∃ r : kˣ, t = r * r ∨ t = -(r * r) := by
  classical
  have := Fintype.ofFinite k
  by_cases h : IsSquare (t : k)
  · obtain ⟨r, hr⟩ := h
    have hr0 : r ≠ 0 := by rintro rfl; exact t.ne_zero (by simp at hr)
    exact ⟨Units.mk0 r hr0, Or.inl (Units.ext (by simpa using hr))⟩
  · have h1 : quadraticChar k (t : k) = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr h
    have h2 : quadraticChar k (-1 : k) = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hneg
    have h3 : quadraticChar k (-(t : k)) = 1 := by
      rw [neg_eq_neg_one_mul, map_mul, h1, h2]; norm_num
    obtain ⟨r, hr⟩ := (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr t.ne_zero)).mp h3
    have hr0 : r ≠ 0 := by rintro rfl; exact t.ne_zero (by simp at hr)
    exact ⟨Units.mk0 r hr0, Or.inr (Units.ext (by simp; linear_combination -hr))⟩

namespace RType

variable [Finite k] {σ : k ≃+* k} {d : k}
variable {G : Type} [Group G] [Finite G] (R : RType G k σ d)

include R in
theorem neg_one_not_square :
    ¬IsSquare (-1 : k) := by
  have := Fintype.ofFinite k
  rw [FiniteField.isSquare_neg_one_iff, not_not, Fintype.card_eq_nat_card, R.card_k]
  obtain ⟨n, -, hn⟩ := R.q_eq
  rw [hn, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

omit [Finite k] in
theorem Jg_mul_Jg : R.Jg * R.Jg = 1 := by
  rw [Jg, ← map_mul]
  have : ThompsonN.J σ * ThompsonN.J σ = 1 := by
    rw [ThompsonN.J, ← map_mul]; simp
  rw [this, map_one]

omit [Finite k] in
theorem Jg_comm_torus (t : kˣ) :
    R.Jg * R.ι (ThompsonN.torus σ t) = R.ι (ThompsonN.torus σ t) * R.Jg := by
  rw [Jg, ThompsonN.J, ← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm]

omit [Finite k] in
theorem JK_mul_JK : R.Jg * R.K * (R.Jg * R.K) = 1 := by
  rw [show R.Jg * R.K * (R.Jg * R.K) = R.Jg * (R.K * R.Jg) * R.K by group, ← R.Jg_mul_K,
    show R.Jg * (R.Jg * R.K) * R.K = (R.Jg * R.Jg) * (R.K * R.K) by group, R.Jg_mul_Jg,
    R.K_mul_K, one_mul]

omit [Finite k] in
theorem JK_ne_one : R.Jg * R.K ≠ 1 := by
  intro h
  apply R.K_not_mem
  have : R.K = R.Jg⁻¹ := by
    calc R.K = R.Jg⁻¹ * (R.Jg * R.K) := by group
      _ = R.Jg⁻¹ := by rw [h, mul_one]
  rw [this]
  exact R.N.inv_mem (R.ι_mem _)

omit [Finite k] in
theorem K_ne_one : R.K ≠ 1 := fun h => R.K_not_mem (h ▸ R.N.one_mem)

theorem invol_classify
    {x : G} (hx : x * x = 1) (hx1 : x ≠ 1) :
    ∃ c : ThompsonN k σ, x = (R.ι c)⁻¹ * R.Jg * R.ι c ∨ x = (R.ι c)⁻¹ * R.K * R.ι c ∨
      x = (R.ι c)⁻¹ * (R.Jg * R.K) * R.ι c := by
  by_cases hxN : x ∈ R.N
  · obtain ⟨n, rfl⟩ := R.exists_ι hxN
    have hn : n * n = 1 := R.ι_injective (by rw [map_mul, hx, map_one])
    have hn1 : n ≠ 1 := fun h => hx1 (by rw [h, map_one])
    obtain ⟨c, hc⟩ := thompsonN_invol hn hn1
    exact ⟨c, Or.inl (by rw [hc, map_mul, map_mul, map_inv]; rfl)⟩
  · obtain ⟨v, hv⟩ : ∃ v, R.act none x = some v := by
      rcases h : R.act none x with _ | v
      · exact absurd ((R.act_none_eq_none_iff x).mp h) hxN
      · exact ⟨v, rfl⟩
    have hvx : R.act (some v) x = none := by
      rw [← hv, ← act_mul, hx, act_one]
    set p := ppv σ v
    have h1 : R.act none (R.ι p * x * R.ι p⁻¹) = some (0, 0, 0) := by
      rw [act_mul, act_mul, act_none_ι, hv, act_ppv_inv]
    have h2 : R.act (some (0, 0, 0)) (R.ι p * x * R.ι p⁻¹) = none := by
      rw [act_mul, act_mul, act_ι, ppv_zero, one_mul, coords_ppv, hvx, act_none_ι]
    obtain ⟨t, ht⟩ := R.eq_torus_mul_K_of_swap h1 h2
    have hx' : x = (R.ι p)⁻¹ * (R.ι (ThompsonN.torus σ t) * R.K) * R.ι p := by
      rw [← ht, map_inv]; group
    obtain ⟨r, hr | hr⟩ := units_eq_sq_or_neg_sq R.neg_one_not_square t
    · refine ⟨ThompsonN.torus σ r⁻¹ * p, Or.inr (Or.inl ?_)⟩
      have e : R.ι (ThompsonN.torus σ t) * R.K =
          (R.ι (ThompsonN.torus σ r⁻¹))⁻¹ * R.K * R.ι (ThompsonN.torus σ r⁻¹) := by
        rw [hr, map_mul, map_mul, mul_assoc, R.torus_mul_K r, ← mul_assoc, map_inv, map_inv,
          inv_inv]
      rw [hx', e, map_mul]; group
    · refine ⟨ThompsonN.torus σ r⁻¹ * p, Or.inr (Or.inr ?_)⟩
      have htJ : R.ι (ThompsonN.torus σ t) =
          R.Jg * R.ι (ThompsonN.torus σ r) * R.ι (ThompsonN.torus σ r) := by
        rw [hr, Jg, ThompsonN.J, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
        simp
      have e : R.ι (ThompsonN.torus σ t) * R.K =
          (R.ι (ThompsonN.torus σ r⁻¹))⁻¹ * (R.Jg * R.K) * R.ι (ThompsonN.torus σ r⁻¹) := by
        calc R.ι (ThompsonN.torus σ t) * R.K
            = R.Jg * R.ι (ThompsonN.torus σ r) * (R.ι (ThompsonN.torus σ r) * R.K) := by
              rw [htJ]; group
          _ = R.Jg * R.ι (ThompsonN.torus σ r) * (R.K * R.ι (ThompsonN.torus σ r⁻¹)) := by
              rw [R.torus_mul_K r]
          _ = (R.ι (ThompsonN.torus σ r) * R.Jg) * R.K * R.ι (ThompsonN.torus σ r⁻¹) := by
              rw [← R.Jg_comm_torus r]; group
          _ = _ := by rw [map_inv, map_inv, inv_inv]; group
      rw [hx', e, map_mul]; group

theorem conj_J_of_fix
    {x : G} (hx : x * x = 1) (hx1 : x ≠ 1) {ω : Option (k × k × k)}
    (hω : R.act ω x = ω) : ∃ g : G, x = g⁻¹ * R.Jg * g := by
  have hy := (R.fix_iff_mem_N ω x).mp hω
  obtain ⟨n, hn⟩ := R.exists_ι hy
  have hnn : n * n = 1 := by
    apply R.ι_injective
    rw [map_mul, ← hn, map_one]
    calc R.rep ω * x * (R.rep ω)⁻¹ * (R.rep ω * x * (R.rep ω)⁻¹) =
        R.rep ω * (x * x) * (R.rep ω)⁻¹ := by group
      _ = 1 := by rw [hx]; group
  have hn1 : n ≠ 1 := by
    rintro rfl
    apply hx1
    rw [map_one] at hn
    calc x = (R.rep ω)⁻¹ * (R.rep ω * x * (R.rep ω)⁻¹) * R.rep ω := by group
      _ = 1 := by rw [hn]; group
  obtain ⟨c, hc⟩ := thompsonN_invol hnn hn1
  refine ⟨R.ι c * R.rep ω, ?_⟩
  have : R.rep ω * x * (R.rep ω)⁻¹ = (R.ι c)⁻¹ * R.Jg * R.ι c := by
    rw [hn, hc, map_mul, map_mul, map_inv]; rfl
  calc x = (R.rep ω)⁻¹ * (R.rep ω * x * (R.rep ω)⁻¹) * R.rep ω := by group
    _ = _ := by rw [this]; group

theorem ncard_fixSet_of_conj_J
    {x g : G} (h : x = g⁻¹ * R.Jg * g) :
    (R.fixSet x).ncard = Nat.card k + 1 := by
  rw [h, ncard_fixSet_conj, ncard_fixSet_J]

theorem ncard_fixSet_K :
    (R.fixSet R.K).ncard = Nat.card k + 1 := by
  obtain ⟨g, hg⟩ := R.conj_J_of_fix R.K_mul_K R.K_ne_one R.K_fixes_a
  exact R.ncard_fixSet_of_conj_J hg

theorem ncard_fixSet_JK :
    (R.fixSet (R.Jg * R.K)).ncard = Nat.card k + 1 := by
  obtain ⟨g, hg⟩ := R.conj_J_of_fix R.JK_mul_JK R.JK_ne_one R.JK_fixes_b
  exact R.ncard_fixSet_of_conj_J hg

theorem ncard_fixSet_invol
    {x : G} (hx : x * x = 1) (hx1 : x ≠ 1) :
    (R.fixSet x).ncard = Nat.card k + 1 := by
  obtain ⟨c, h | h | h⟩ := R.invol_classify hx hx1 <;> rw [h, ncard_fixSet_conj]
  · exact R.ncard_fixSet_J
  · exact R.ncard_fixSet_K
  · exact R.ncard_fixSet_JK

@[expose] def invSet
    (ω : Option (k × k × k)) : Set G :=
  {x | x * x = 1 ∧ x ≠ 1 ∧ R.act ω x = ω}

theorem ncard_invSet_none_le :
    (R.invSet none).ncard ≤ Nat.card k ^ 2 := by
  have hsub : R.invSet none ⊆ R.ι '' Set.range (fun v : k × k => (⟨-1, v.1, 0, v.2⟩ :
      ThompsonN k σ)) := by
    rintro x ⟨hx, hx1, hfix⟩
    obtain ⟨n, rfl⟩ := R.exists_ι ((R.act_none_eq_none_iff _).mp hfix)
    have hn : n * n = 1 := R.ι_injective (by rw [map_mul, hx, map_one])
    have hn1 : n ≠ 1 := fun h => hx1 (by rw [h, map_one])
    obtain ⟨hk, hb⟩ := thompsonN_invol_form hn hn1
    exact ⟨n, ⟨(n.α, n.γ), by ext <;> simp [hk, hb]⟩, rfl⟩
  calc (R.invSet none).ncard ≤ (R.ι '' Set.range (fun v : k × k => (⟨-1, v.1, 0, v.2⟩ :
        ThompsonN k σ))).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (Set.range (fun v : k × k => (⟨-1, v.1, 0, v.2⟩ : ThompsonN k σ))).ncard :=
        Set.ncard_image_le (Set.toFinite _)
    _ ≤ (Set.univ : Set (k × k)).ncard := by
        rw [← Set.image_univ]; exact Set.ncard_image_le (Set.toFinite _)
    _ = Nat.card k ^ 2 := by rw [Set.ncard_univ, Nat.card_prod, sq]

theorem mem_invSet_iff
    (ω : Option (k × k × k)) (x : G) :
    x ∈ R.invSet ω ↔ R.rep ω * x * (R.rep ω)⁻¹ ∈ R.invSet none := by
  simp only [invSet, Set.mem_ofPred_eq]
  rw [R.fix_iff_mem_N ω x, ← R.act_none_eq_none_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, h3⟩
    · calc R.rep ω * x * (R.rep ω)⁻¹ * (R.rep ω * x * (R.rep ω)⁻¹) =
          R.rep ω * (x * x) * (R.rep ω)⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · intro h; apply h2
      calc x = (R.rep ω)⁻¹ * (R.rep ω * x * (R.rep ω)⁻¹) * R.rep ω := by group
        _ = 1 := by rw [h]; group
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, h3⟩
    · have : R.rep ω * (x * x) * (R.rep ω)⁻¹ = 1 := by rw [← h1]; group
      calc x * x = (R.rep ω)⁻¹ * (R.rep ω * (x * x) * (R.rep ω)⁻¹) * R.rep ω := by group
        _ = 1 := by rw [this]; group
    · rintro rfl; apply h2; group

theorem ncard_invSet_le
    (ω : Option (k × k × k)) : (R.invSet ω).ncard ≤ Nat.card k ^ 2 := by
  have : R.invSet ω = (fun y => (R.rep ω)⁻¹ * y * R.rep ω) '' R.invSet none := by
    ext x
    rw [mem_invSet_iff, Set.mem_image]
    constructor
    · intro h; exact ⟨_, h, by group⟩
    · rintro ⟨y, hy, rfl⟩
      convert hy using 1; group
  rw [this]
  exact (Set.ncard_image_le (Set.toFinite _)).trans R.ncard_invSet_none_le

theorem act_zc_torus (γ : k) (t : kˣ) :
    R.act (some (0, 0, γ)) (R.ι (ThompsonN.torus σ t)) =
      some (0, 0, γ * ((t : k) ^ 2 * σ t)) := by
  rw [act_ι]
  simp [coords, ThompsonN.mul_def, thompsonMul, pp]

include R in
theorem sigmaTwo_injective
    {t : kˣ} (ht : σ t * (t : k) ^ 2 = 1) : t = 1 := by
  have hJ : R.act (some (0, 0, 1)) R.Jg ≠ some (0, 0, 1) := by
    rw [act_J]
    simp only [neg_zero, ne_eq, Option.some.injEq, Prod.mk.injEq, true_and]
    intro h
    exact two_ne_zero' (by linear_combination -h)
  have hfix : R.act (some (0, 0, 1)) (R.ι (ThompsonN.torus σ t)) = some (0, 0, 1) := by
    rw [act_zc_torus, one_mul, mul_comm, ht]
  have hsq := R.sq_eq_one_of_fix_comm_J hJ hfix (R.Jg_comm_torus t).symm
  have htt : t * t = 1 := R.ι_torus_injective (by simpa only [map_mul, map_one] using hsq)
  rcases units_sq_eq_one htt with h | h
  · exact h
  · exfalso
    rw [h] at ht
    simp only [Units.val_neg, Units.val_one, map_neg, map_one, even_two, Even.neg_pow, one_pow,
      mul_one] at ht
    exact two_ne_zero' (by linear_combination -ht)

include R in
theorem sigmaTwo_surjective
    (y : kˣ) : ∃ t : kˣ, σ t * (t : k) ^ 2 = y := by
  let f : kˣ →* kˣ := Units.map (σ : k →* k) * powMonoidHom 2
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro t ht
    apply R.sigmaTwo_injective
    have := congrArg Units.val ht
    simpa [f] using this
  obtain ⟨t, ht⟩ := Finite.surjective_of_injective hf y
  exact ⟨t, by have := congrArg Units.val ht; simpa [f] using this⟩

end RType

end CFSG.Walter.Ree.T2
