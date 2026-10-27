module

public import CFSG.RankThree.GF2n.Smith81.Orth213ClassDefs
import CFSG.GroupTheory.WeirSylow.OrthogonalModels
import CFSG.RankThree.GF2n.Smith81.OrthRootLA
import CFSG.Timmesfeld.Orders.ClassicalOrthogonal

public section

namespace CFSG.RankThree.GF2n.Smith81.OrthClass

open QuadraticMap

section Coset

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem card_mul_card_singular_shift (q : V → K) (P : V → Prop) (w : V)
    (hP : ∀ v, P v → ∀ μ : K, P (v + μ • w))
    (hq : ∀ v, P v → Function.Bijective fun μ : K => q (v + μ • w)) :
    Nat.card K * Nat.card {v // P v ∧ q v = 0} = Nat.card {v // P v} := by
  rw [mul_comm, ← Nat.card_prod]
  refine Nat.card_congr (Equiv.ofBijective
    (fun p : {v // P v ∧ q v = 0} × K => (⟨p.1.1 + p.2 • w, hP _ p.1.2.1 p.2⟩ : {v // P v}))
    ⟨?_, ?_⟩)
  · rintro ⟨⟨v₁, hv₁, hq₁⟩, μ₁⟩ ⟨⟨v₂, _, hq₂⟩, μ₂⟩ h
    have h' : v₁ + μ₁ • w = v₂ + μ₂ • w := congrArg Subtype.val h
    have hv₂' : v₂ = v₁ + (μ₁ - μ₂) • w := by
      rw [sub_smul, ← add_sub_assoc, h']
      abel
    have hμ : μ₁ - μ₂ = 0 := by
      apply (hq v₁ hv₁).1
      show q (v₁ + (μ₁ - μ₂) • w) = q (v₁ + (0 : K) • w)
      rw [← hv₂', zero_smul, add_zero, hq₁, hq₂]
    have hμ' : μ₁ = μ₂ := sub_eq_zero.mp hμ
    subst hμ'
    have hv : v₁ = v₂ := add_right_cancel h'
    subst hv
    rfl
  · rintro ⟨v', hv'⟩
    obtain ⟨μ, hμ⟩ := (hq v' hv').2 0
    refine ⟨(⟨v' + μ • w, hP _ hv' μ, hμ⟩, -μ), Subtype.ext ?_⟩
    show v' + μ • w + (-μ) • w = v'
    rw [neg_smul, add_neg_cancel_right]

private theorem map_add_smul_eq (Q : QuadraticForm K V) (v w : V) (μ : K) :
    Q (v + μ • w) = Q v + μ * polar Q v w + μ ^ 2 * Q w := by
  rw [QuadraticMap.map_add Q v (μ • w), QuadraticMap.map_smul, polar_smul_right]
  simp only [smul_eq_mul]
  ring

private theorem bijective_add_mul {a b : K} (hb : b ≠ 0) :
    Function.Bijective fun μ : K => a + μ * b :=
  ((Equiv.mulRight₀ b hb).trans (Equiv.addLeft a)).bijective

end Coset

section Square

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem bijective_add_sq_mul {a b : K} (hb : b ≠ 0) :
    Function.Bijective fun μ : K => a + μ ^ 2 * b := by
  rw [← Finite.injective_iff_bijective]
  intro μ₁ μ₂ h
  exact CharTwo.sq_injective (mul_right_cancel₀ hb (add_left_cancel h))

end Square

section Split

private theorem card_split_aux {α : Type*} [Finite α] (A B : α → Prop) :
    Nat.card {a // A a ∧ B a} + Nat.card {a // A a ∧ ¬ B a} = Nat.card {a // A a} :=
  Set.ncard_inter_add_ncard_sdiff_eq_ncard {a | A a} {a | B a}

private theorem card_compl_aux {α : Type*} [Finite α] (B : α → Prop) :
    Nat.card {a // B a} + Nat.card {a // ¬ B a} = Nat.card α := by
  classical
  rw [← Nat.card_sum]
  exact Nat.card_congr (Equiv.sumCompl B)

variable {K : Type} [Field K] [Finite K] {ι : Type} [Fintype ι]

theorem nSing_split (qU : QuadraticForm K (ι → K)) (P R : (ι → K) → Prop) :
    nSing qU (fun s => P s ∧ R s) + nSing qU (fun s => P s ∧ ¬ R s) = nSing qU P := by
  have h := card_split_aux (fun s => P s ∧ qU s = 0) R
  have e1 : Nat.card {a // (P a ∧ qU a = 0) ∧ R a} = nSing qU (fun s => P s ∧ R s) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun a => by tauto)
  have e2 : Nat.card {a // (P a ∧ qU a = 0) ∧ ¬ R a} = nSing qU (fun s => P s ∧ ¬ R s) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun a => by tauto)
  rw [e1, e2] at h
  exact h

end Split

section Perp

variable {K : Type} [Field K] [CharP K 2] {ι : Type} [Fintype ι] {qU : QuadraticForm K (ι → K)}

theorem natCard_perp_eq_pow (hnd : ∀ v, (∀ w, polar qU v w = 0) → v = 0)
    (W : Submodule K (ι → K)) :
    Nat.card {s : ι → K // ∀ x ∈ W, polar qU x s = 0} =
      Nat.card K ^ (Fintype.card ι - Module.finrank K W) := by
  have hB := polarBilin_nondegenerate_of_hnd hnd
  have h1 := LinearMap.BilinForm.finrank_orthogonal hB W
  rw [Module.finrank_fintype_fun_eq_card] at h1
  rw [← h1, ← Module.natCard_eq_pow_finrank (K := K)]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun s => by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    exact Iff.rfl)

theorem natCard_perp_one (hnd : ∀ v, (∀ w, polar qU v w = 0) → v = 0) {u : ι → K} (hu0 : u ≠ 0) :
    Nat.card {s : ι → K // polar qU s u = 0} = Nat.card K ^ (Fintype.card ι - 1) := by
  have h := natCard_perp_eq_pow hnd (K ∙ u)
  rw [finrank_span_singleton hu0] at h
  rw [← h]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun s => ?_)
  constructor
  · intro hs x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [polar_smul_left, polar_comm qU u s, hs, smul_zero]
  · intro h'
    rw [polar_comm qU s u]
    exact h' u (Submodule.mem_span_singleton_self u)

theorem natCard_perp_two (hnd : ∀ v, (∀ w, polar qU v w = 0) → v = 0) {u w : ι → K}
    (hind : ∀ a b : K, a • u + b • w = 0 → a = 0 ∧ b = 0) :
    Nat.card {s : ι → K // polar qU s u = 0 ∧ polar qU s w = 0} =
      Nat.card K ^ (Fintype.card ι - 2) := by
  have hli : LinearIndependent K ![u, w] := LinearIndependent.pair_iff.mpr hind
  have hfr := finrank_span_eq_card hli
  rw [Matrix.range_cons_cons_empty, Fintype.card_fin] at hfr
  have h := natCard_perp_eq_pow hnd (Submodule.span K {u, w})
  rw [hfr] at h
  rw [← h]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun s => ?_)
  constructor
  · rintro ⟨hu, hw⟩ x hx
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
    rw [polar_add_left, polar_smul_left, polar_smul_left, polar_comm qU u s, polar_comm qU w s,
      hu, hw]
    simp
  · intro h'
    exact ⟨by rw [polar_comm qU s u]; exact h' u (Submodule.subset_span (by simp)),
      by rw [polar_comm qU s w]; exact h' w (Submodule.subset_span (by simp))⟩

end Perp

section Counts

variable {K : Type} [Field K] [Finite K] [CharP K 2] {ι : Type} [Fintype ι]
  {qU : QuadraticForm K (ι → K)}

theorem nSing_perp_one (hnd : ∀ v, (∀ w, polar qU v w = 0) → v = 0) {u : ι → K} (hu0 : u ≠ 0)
    (hqu : qU u = 0) (hn : 2 ≤ Fintype.card ι) :
    nSing qU (fun s => polar qU s u = 0) +
        (Nat.card K - 1) * Nat.card K ^ (Fintype.card ι - 2) = nSing qU (fun _ => True) := by
  have hP : ∀ v, ¬ polar qU v u = 0 → ∀ μ : K, ¬ polar qU (v + μ • u) u = 0 := by
    intro v hv μ
    rw [polar_add_left, polar_smul_left,
      CFSG.ComponentClassification.UnbalancedCatalog.polar_self_charTwo, smul_zero, add_zero]
    exact hv
  have hq : ∀ v, ¬ polar qU v u = 0 → Function.Bijective fun μ : K => qU (v + μ • u) := by
    intro v hv
    have hform : (fun μ : K => qU (v + μ • u)) = fun μ => qU v + μ * polar qU v u := by
      funext μ
      rw [map_add_smul_eq qU, hqu]
      ring
    rw [hform]
    exact bijective_add_mul hv
  have hshift := card_mul_card_singular_shift (fun v => qU v) (fun v => ¬ polar qU v u = 0) u hP hq
  have hsplit := nSing_split qU (fun _ => True) (fun s => polar qU s u = 0)
  simp only [true_and] at hsplit
  rw [← hsplit]
  congr 1
  have hcount := card_compl_aux (fun s : ι → K => polar qU s u = 0)
  rw [natCard_perp_one hnd hu0, CFSG.Timmesfeld.ClassicalOrders.card_coord_fun ι] at hcount
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card ι = k + 2 := ⟨Fintype.card ι - 2, by omega⟩
  obtain ⟨r, hr⟩ : ∃ r, Nat.card K = r + 1 :=
    ⟨Nat.card K - 1, by have := Finite.one_lt_card (α := K); omega⟩
  have e1 : k + 2 - 1 = k + 1 := by omega
  rw [hk, e1] at hcount
  rw [hk, Nat.add_sub_cancel]
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := K))
  change Nat.card K * ((Nat.card K - 1) * Nat.card K ^ k) =
    Nat.card K * Nat.card {v // ¬ polar qU v u = 0 ∧ qU v = 0}
  rw [hshift]
  rw [hr] at hcount ⊢
  rw [Nat.add_sub_cancel]
  have h1 : (r + 1) ^ (k + 2) = (r + 1) ^ k * (r + 1) * (r + 1) := by ring
  have h2 : (r + 1) ^ (k + 1) = (r + 1) ^ k * (r + 1) := by ring
  rw [h1, h2] at hcount
  nlinarith [hcount]

theorem nSing_perp_two (hnd : ∀ v, (∀ w, polar qU v w = 0) → v = 0) {u w : ι → K} (hu0 : u ≠ 0)
    (_hqu : qU u = 0) (hqw : qU w = 0) (huw : polar qU u w = 0)
    (hind : ∀ a b : K, a • u + b • w = 0 → a = 0 ∧ b = 0) (hn : 3 ≤ Fintype.card ι) :
    nSing qU (fun s => polar qU s u = 0 ∧ polar qU s w = 0) +
        (Nat.card K - 1) * Nat.card K ^ (Fintype.card ι - 3) =
      nSing qU (fun s => polar qU s u = 0) := by
  have hwu : polar qU w u = 0 := by rw [polar_comm]; exact huw
  have hP : ∀ v, (polar qU v u = 0 ∧ ¬ polar qU v w = 0) → ∀ μ : K,
      (polar qU (v + μ • w) u = 0 ∧ ¬ polar qU (v + μ • w) w = 0) := by
    rintro v ⟨hv1, hv2⟩ μ
    refine ⟨?_, ?_⟩
    · rw [polar_add_left, polar_smul_left, hwu, hv1]
      simp
    · rw [polar_add_left, polar_smul_left,
        CFSG.ComponentClassification.UnbalancedCatalog.polar_self_charTwo, smul_zero, add_zero]
      exact hv2
  have hq : ∀ v, (polar qU v u = 0 ∧ ¬ polar qU v w = 0) →
      Function.Bijective fun μ : K => qU (v + μ • w) := by
    rintro v ⟨-, hv2⟩
    have hform : (fun μ : K => qU (v + μ • w)) = fun μ => qU v + μ * polar qU v w := by
      funext μ
      rw [map_add_smul_eq qU, hqw]
      ring
    rw [hform]
    exact bijective_add_mul hv2
  have hshift := card_mul_card_singular_shift (fun v => qU v)
    (fun v => polar qU v u = 0 ∧ ¬ polar qU v w = 0) w hP hq
  have hsplit := nSing_split qU (fun s => polar qU s u = 0) (fun s => polar qU s w = 0)
  rw [← hsplit]
  congr 1
  have hcount := card_split_aux (fun s : ι → K => polar qU s u = 0)
    (fun s => polar qU s w = 0)
  rw [natCard_perp_one hnd hu0, natCard_perp_two hnd hind] at hcount
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card ι = k + 3 := ⟨Fintype.card ι - 3, by omega⟩
  obtain ⟨r, hr⟩ : ∃ r, Nat.card K = r + 1 :=
    ⟨Nat.card K - 1, by have := Finite.one_lt_card (α := K); omega⟩
  have e1 : k + 3 - 1 = k + 2 := by omega
  have e2 : k + 3 - 2 = k + 1 := by omega
  rw [hk, e1, e2] at hcount
  rw [hk, Nat.add_sub_cancel]
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := K))
  change Nat.card K * ((Nat.card K - 1) * Nat.card K ^ k) =
    Nat.card K * Nat.card {v // (polar qU v u = 0 ∧ ¬ polar qU v w = 0) ∧ qU v = 0}
  rw [hshift]
  rw [hr] at hcount ⊢
  rw [Nat.add_sub_cancel]
  have h1 : (r + 1) ^ (k + 2) = (r + 1) ^ k * (r + 1) * (r + 1) := by ring
  have h2 : (r + 1) ^ (k + 1) = (r + 1) ^ k * (r + 1) := by ring
  rw [h1, h2] at hcount
  nlinarith [hcount]

theorem nSing_perp_two_nonsing (hnd : ∀ v, (∀ w, polar qU v w = 0) → v = 0) {u w : ι → K}
    (hu0 : u ≠ 0) (hqu : qU u = 0) (huw : polar qU u w = 0) (hqw : qU w ≠ 0)
    (hn : 3 ≤ Fintype.card ι) :
    nSing qU (fun s => polar qU s u = 0 ∧ polar qU s w = 0) =
      Nat.card K ^ (Fintype.card ι - 3) := by
  have hwu : polar qU w u = 0 := by rw [polar_comm]; exact huw
  have hind : ∀ a b : K, a • u + b • w = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    have hb : b = 0 := by
      by_contra hb
      have hbw : b • w = -(a • u) := eq_neg_of_add_eq_zero_right hab
      have hw : w = (-(a / b)) • u := by
        calc w = b⁻¹ • (b • w) := (inv_smul_smul₀ hb w).symm
          _ = b⁻¹ • (-(a • u)) := by rw [hbw]
          _ = (-(a / b)) • u := by
            rw [smul_neg, smul_smul, ← neg_smul, div_eq_mul_inv, mul_comm]
      apply hqw
      rw [hw, QuadraticMap.map_smul, hqu, smul_zero]
    subst hb
    rw [zero_smul, add_zero] at hab
    exact ⟨(smul_eq_zero.mp hab).resolve_right hu0, rfl⟩
  have hP : ∀ v, (polar qU v u = 0 ∧ polar qU v w = 0) → ∀ μ : K,
      (polar qU (v + μ • w) u = 0 ∧ polar qU (v + μ • w) w = 0) := by
    rintro v ⟨hv1, hv2⟩ μ
    refine ⟨?_, ?_⟩
    · rw [polar_add_left, polar_smul_left, hwu, hv1]
      simp
    · rw [polar_add_left, polar_smul_left,
        CFSG.ComponentClassification.UnbalancedCatalog.polar_self_charTwo, hv2]
      simp
  have hq : ∀ v, (polar qU v u = 0 ∧ polar qU v w = 0) →
      Function.Bijective fun μ : K => qU (v + μ • w) := by
    rintro v ⟨-, hv2⟩
    have hform : (fun μ : K => qU (v + μ • w)) = fun μ => qU v + μ ^ 2 * qU w := by
      funext μ
      rw [map_add_smul_eq qU, hv2]
      ring
    rw [hform]
    exact bijective_add_sq_mul hqw
  have hshift := card_mul_card_singular_shift (fun v => qU v)
    (fun v => polar qU v u = 0 ∧ polar qU v w = 0) w hP hq
  rw [natCard_perp_two hnd hind] at hshift
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card ι = k + 3 := ⟨Fintype.card ι - 3, by omega⟩
  have e2 : k + 3 - 2 = k + 1 := by omega
  rw [hk, e2] at hshift
  rw [hk, Nat.add_sub_cancel]
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := K))
  change Nat.card K * Nat.card {v // (polar qU v u = 0 ∧ polar qU v w = 0) ∧ qU v = 0} =
    Nat.card K * Nat.card K ^ k
  rw [hshift, pow_succ']

theorem nSing_total (hnd : ∀ v, (∀ w, polar qU v w = 0) → v = 0) (hn : 2 ≤ Fintype.card ι) :
    Even (Fintype.card ι) ∧ ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      (nSing qU (fun _ => True) : ℤ) = (Nat.card K : ℤ) ^ (Fintype.card ι - 1) +
        ε * (Nat.card K : ℤ) ^ (Fintype.card ι / 2 - 1) * ((Nat.card K : ℤ) - 1) := by
  have hQ := polarBilin_nondegenerate_of_hnd hnd
  have hev : Even (Fintype.card ι) := by
    have h := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo qU hQ
    rwa [Module.finrank_fintype_fun_eq_card] at h
  refine ⟨hev, ?_⟩
  obtain ⟨m', hm'⟩ := hev
  obtain ⟨m, rfl⟩ : ∃ m, m' = m + 1 := ⟨m' - 1, by omega⟩
  have hdim : Module.finrank K (ι → K) = 2 * (m + 1) := by
    rw [Module.finrank_fintype_fun_eq_card]
    omega
  have hcard : nSing qU (fun _ => True) = Nat.card {v : ι → K // qU v = 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun v => by simp)
  have e1 : Fintype.card ι - 1 = 2 * m + 1 := by omega
  have e2 : Fintype.card ι / 2 - 1 = m := by omega
  rw [e1, e2]
  rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus qU hQ (n := m + 1)
    (by omega) hdim with ⟨⟨e⟩⟩ | ⟨_, _, hirr, ⟨e⟩⟩
  · refine ⟨1, Or.inl rfl, ?_⟩
    have h1 := (CFSG.Timmesfeld.ClassicalOrders.card_quadPlus (K := K) m).1
    rw [hcard, CFSG.Timmesfeld.ClassicalOrders.card_singular_congr e, h1]
    ring
  · refine ⟨-1, Or.inr rfl, ?_⟩
    have h1 := (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus (K := K) m hirr).1
    rw [hcard, CFSG.Timmesfeld.ClassicalOrders.card_singular_congr e, h1]
    ring

theorem nSing_numeric (hnd : ∀ v, (∀ w, polar qU v w = 0) → v = 0) (hq : 4 ≤ Nat.card K)
    (hn : 4 ≤ Fintype.card ι) :
    nSing qU (fun _ => True) + Nat.card K ≠
        (Nat.card K - 1) * Nat.card K ^ (Fintype.card ι - 2) + Nat.card K ^ (Fintype.card ι - 3) +
          Nat.card K ^ 2 ∧
      nSing qU (fun _ => True) ≠ (Nat.card K - 1) * (Nat.card K ^ (Fintype.card ι - 2) +
        Nat.card K ^ (Fintype.card ι - 3)) + Nat.card K ^ (Fintype.card ι - 3) := by
  obtain ⟨hev, ε, hε, hN⟩ := nSing_total hnd (by omega)
  obtain ⟨m', hm'⟩ := hev
  obtain ⟨m, rfl⟩ : ∃ m, m' = m + 2 := ⟨m' - 2, by omega⟩
  have e1 : Fintype.card ι - 1 = 2 * m + 3 := by omega
  have e2 : Fintype.card ι / 2 - 1 = m + 1 := by omega
  have e3 : Fintype.card ι - 2 = 2 * m + 2 := by omega
  have e4 : Fintype.card ι - 3 = 2 * m + 1 := by omega
  rw [e1, e2] at hN
  rw [e3, e4]
  generalize nSing qU (fun _ => True) = N at hN ⊢
  generalize Nat.card K = q at hN hq ⊢
  have hq1 : 1 ≤ q := by omega
  have hqZ : (1 : ℤ) < q := by exact_mod_cast (by omega : 1 < q)
  have hy1 : (1 : ℤ) ≤ (q : ℤ) ^ m := one_le_pow₀ (by exact_mod_cast hq1)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : (N : ℤ) + q =
        ((q : ℤ) - 1) * (q : ℤ) ^ (2 * m + 2) + (q : ℤ) ^ (2 * m + 1) + (q : ℤ) ^ 2 := by
      have := congrArg (Nat.cast : ℕ → ℤ) h
      push_cast [Nat.cast_sub hq1] at this
      exact this
    have key : ((q : ℤ) - 1) * ((q : ℤ) ^ (2 * m + 1) + ε * (q : ℤ) ^ (m + 1) - q) = 0 := by
      linear_combination h' - hN
    have hk2 : (q : ℤ) ^ (2 * m + 1) + ε * (q : ℤ) ^ (m + 1) - q = 0 := by
      rcases mul_eq_zero.mp key with h0 | h0
      · exfalso
        linarith
      · exact h0
    generalize hy : (q : ℤ) ^ m = y at hy1
    have e5 : (q : ℤ) ^ (2 * m + 1) = y * y * q := by rw [← hy]; ring
    have e6 : (q : ℤ) ^ (m + 1) = y * q := by rw [← hy]; ring
    rw [e5, e6] at hk2
    have hk3 : (q : ℤ) * (y * y + ε * y - 1) = 0 := by linear_combination hk2
    have hk4 : y * y + ε * y = 1 := by
      rcases mul_eq_zero.mp hk3 with h0 | h0
      · exfalso
        linarith
      · linarith
    rcases hε with rfl | rfl
    · nlinarith
    · rcases (by omega : y = 1 ∨ 2 ≤ y) with h1 | h1
      · subst h1
        norm_num at hk4
      · nlinarith
  · have h' : (N : ℤ) = ((q : ℤ) - 1) * ((q : ℤ) ^ (2 * m + 2) + (q : ℤ) ^ (2 * m + 1)) +
        (q : ℤ) ^ (2 * m + 1) := by
      have := congrArg (Nat.cast : ℕ → ℤ) h
      push_cast [Nat.cast_sub hq1] at this
      exact this
    have key : ε * (q : ℤ) ^ (m + 1) * ((q : ℤ) - 1) = 0 := by
      linear_combination h' - hN
    have hqpos : (q : ℤ) ^ (m + 1) ≠ 0 := by positivity
    have hq1' : (q : ℤ) - 1 ≠ 0 := by linarith
    have hε0 : ε ≠ 0 := by
      rcases hε with rfl | rfl <;> norm_num
    exact mul_ne_zero (mul_ne_zero hε0 hqpos) hq1' key

end Counts

end CFSG.RankThree.GF2n.Smith81.OrthClass
