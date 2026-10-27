module

public import CFSG.Open.StatedDefs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural

open Matrix CFSG.Open

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] {Γ : Type*} [Group Γ]

structure IsQuatType (ρ : Γ →* GL ι K) (N : Subgroup Γ) : Prop where
  normal : N.Normal
  scalars_le : (StatedScalars ι K).comap ρ ≤ N
  sq_mem : ∀ x ∈ N, x * x ∈ (StatedScalars ι K).comap ρ
  comm_or_anticomm : ∀ x ∈ N, ∀ y ∈ N,
    x * y = y * x ∨ (ρ (x * y) : Matrix ι ι K) = -(ρ (y * x) : Matrix ι ι K)
  mem_of_comm : ∀ x ∈ N, (∀ y ∈ N, x * y = y * x) → x ∈ (StatedScalars ι K).comap ρ

private abbrev scalSub (ρ : Γ →* GL ι K) : Subgroup Γ :=
  (StatedScalars ι K).comap ρ

private lemma trace_eq_zero_of_anticomm {ρ : Γ →* GL ι K} {x y : Γ}
    (hK : ringChar K ≠ 2)
    (hxy : (ρ (x * y) : Matrix ι ι K) = -(ρ (y * x) : Matrix ι ι K)) :
    Matrix.trace (ρ x : Matrix ι ι K) = 0 := by
  have hm : (ρ x : Matrix ι ι K) * (ρ y : Matrix ι ι K) =
      -((ρ y : Matrix ι ι K) * (ρ x : Matrix ι ι K)) := by
    simpa only [map_mul, Units.val_mul] using hxy
  have hconj : (↑((ρ y)⁻¹) : Matrix ι ι K) * (ρ x : Matrix ι ι K) * (ρ y : Matrix ι ι K) =
      -(ρ x : Matrix ι ι K) := by
    calc (↑((ρ y)⁻¹) : Matrix ι ι K) * (ρ x : Matrix ι ι K) * (ρ y : Matrix ι ι K)
        = (↑((ρ y)⁻¹) : Matrix ι ι K) *
            ((ρ x : Matrix ι ι K) * (ρ y : Matrix ι ι K)) := by rw [mul_assoc]
      _ = (↑((ρ y)⁻¹) : Matrix ι ι K) *
            (-((ρ y : Matrix ι ι K) * (ρ x : Matrix ι ι K))) := by rw [hm]
      _ = -((↑((ρ y)⁻¹) : Matrix ι ι K) *
            ((ρ y : Matrix ι ι K) * (ρ x : Matrix ι ι K))) := by rw [mul_neg]
      _ = -(((↑((ρ y)⁻¹) : Matrix ι ι K) * (ρ y : Matrix ι ι K)) *
            (ρ x : Matrix ι ι K)) := by rw [mul_assoc]
      _ = -((↑((ρ y)⁻¹ * ρ y) : Matrix ι ι K) * (ρ x : Matrix ι ι K)) := by
            rw [← Units.val_mul]
      _ = -((↑(1 : GL ι K) : Matrix ι ι K) * (ρ x : Matrix ι ι K)) := by
            rw [inv_mul_cancel]
      _ = -(ρ x : Matrix ι ι K) := by rw [Units.val_one, one_mul]
  have ht := Matrix.trace_units_conj' (ρ y) (ρ x : Matrix ι ι K)
  rw [hconj, Matrix.trace_neg] at ht
  have h2 : (2 : K) * Matrix.trace (ρ x : Matrix ι ι K) = 0 := by
    have h3 : Matrix.trace (ρ x : Matrix ι ι K) + Matrix.trace (ρ x : Matrix ι ι K) = 0 :=
      neg_eq_iff_add_eq_zero.mp ht
    simpa only [two_mul] using h3
  exact (mul_eq_zero.mp h2).resolve_left (Ring.two_ne_zero hK)

private lemma trace_eq_zero_of_not_mem_scalSub (hK : ringChar K ≠ 2)
    {ρ : Γ →* GL ι K} {N : Subgroup Γ} (hN : IsQuatType ρ N) {x : Γ} (hx : x ∈ N)
    (hxZ : x ∉ scalSub ρ) : Matrix.trace (ρ x : Matrix ι ι K) = 0 := by
  have hex : ∃ y ∈ N, x * y ≠ y * x := by
    by_contra h
    push Not at h
    exact hxZ (hN.mem_of_comm x hx h)
  obtain ⟨y, hyN, hxy⟩ := hex
  rcases hN.comm_or_anticomm x hx y hyN with hcomm | hanti
  · exact absurd hcomm hxy
  · exact trace_eq_zero_of_anticomm hK hanti

private noncomputable def qreps (N Z : Subgroup Γ) (q : N ⧸ Z.subgroupOf N) : N :=
  Quotient.out q

private noncomputable def qunit (ρ : Γ →* GL ι K) (N Z : Subgroup Γ)
    (q : N ⧸ Z.subgroupOf N) : GL ι K :=
  ρ ((qreps N Z q : N) : Γ)

private noncomputable def qmat (ρ : Γ →* GL ι K) (N Z : Subgroup Γ)
    (q : N ⧸ Z.subgroupOf N) : Matrix ι ι K :=
  (qunit ρ N Z q : Matrix ι ι K)

private lemma qreps_mk (N Z : Subgroup Γ) (q : N ⧸ Z.subgroupOf N) :
    ((qreps N Z q : N) : N ⧸ Z.subgroupOf N) = q :=
  QuotientGroup.out_eq' q

private noncomputable instance fintypeQuotientSubgroup [Finite Γ] (N Z : Subgroup Γ) :
    Fintype (N ⧸ Z.subgroupOf N) :=
  Fintype.ofFinite _

private lemma qreps_inv_mul_not_mem (N Z : Subgroup Γ)
    {q q' : N ⧸ Z.subgroupOf N} (hqq' : q ≠ q') :
    (qreps N Z q)⁻¹ * qreps N Z q' ∉ Z.subgroupOf N := by
  intro hmem
  apply hqq'
  have heq : ((qreps N Z q : N) : N ⧸ Z.subgroupOf N) =
      ((qreps N Z q' : N) : N ⧸ Z.subgroupOf N) := QuotientGroup.eq.mpr hmem
  rwa [qreps_mk, qreps_mk] at heq

private lemma trace_qunit_inv_mul_eq_zero [Finite Γ] (hK : ringChar K ≠ 2)
    {ρ : Γ →* GL ι K} {N : Subgroup Γ} (hN : IsQuatType ρ N)
    {q q' : N ⧸ (scalSub ρ).subgroupOf N} (hqq' : q ≠ q') :
    Matrix.trace ((↑((qunit ρ N (scalSub ρ) q)⁻¹) : Matrix ι ι K) *
      (↑(qunit ρ N (scalSub ρ) q') : Matrix ι ι K)) = 0 := by
  let s : Γ := ((qreps N (scalSub ρ) q : N) : Γ)⁻¹ * ((qreps N (scalSub ρ) q' : N) : Γ)
  have hsN : s ∈ N :=
    N.mul_mem (N.inv_mem (qreps N (scalSub ρ) q).2) (qreps N (scalSub ρ) q').2
  have hsZ : s ∉ scalSub ρ := by
    intro hmem
    apply qreps_inv_mul_not_mem (N := N) (Z := scalSub ρ) hqq'
    rw [Subgroup.mem_subgroupOf]
    simpa only [s, Subgroup.coe_mul, Subgroup.coe_inv] using hmem
  have hzero := trace_eq_zero_of_not_mem_scalSub (ρ := ρ) hK hN hsN hsZ
  have hmat : (↑((qunit ρ N (scalSub ρ) q)⁻¹) : Matrix ι ι K) *
      (↑(qunit ρ N (scalSub ρ) q') : Matrix ι ι K) = (ρ s : Matrix ι ι K) := by
    simp only [qunit, s, map_mul, map_inv, Units.val_mul]
  rw [hmat, hzero]

private lemma qmat_linearIndependent [Finite Γ] (hK : ringChar K ≠ 2)
    (hι : (Fintype.card ι : K) ≠ 0) {ρ : Γ →* GL ι K} {N : Subgroup Γ}
    (hN : IsQuatType ρ N) :
    LinearIndependent K (qmat ρ N (scalSub ρ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc q0
  have htrace : Matrix.trace ((↑((qunit ρ N (scalSub ρ) q0)⁻¹) : Matrix ι ι K) *
      (∑ q, c q • qmat ρ N (scalSub ρ) q)) = 0 := by
    rw [hc, Matrix.mul_zero, Matrix.trace_zero]
  have hcalc : Matrix.trace ((↑((qunit ρ N (scalSub ρ) q0)⁻¹) : Matrix ι ι K) *
      (∑ q, c q • qmat ρ N (scalSub ρ) q)) =
      ∑ q, c q * Matrix.trace ((↑((qunit ρ N (scalSub ρ) q0)⁻¹) : Matrix ι ι K) *
        qmat ρ N (scalSub ρ) q) := by
    rw [Matrix.mul_sum, Matrix.trace_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  rw [hcalc] at htrace
  have hsingle : ∑ q, c q * Matrix.trace
      ((↑((qunit ρ N (scalSub ρ) q0)⁻¹) : Matrix ι ι K) * qmat ρ N (scalSub ρ) q) =
      c q0 * (Fintype.card ι : K) := by
    rw [Fintype.sum_eq_single q0]
    · have hdiag : Matrix.trace ((↑((qunit ρ N (scalSub ρ) q0)⁻¹) : Matrix ι ι K) *
          qmat ρ N (scalSub ρ) q0) = (Fintype.card ι : K) := by
        simp only [qmat]
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.trace_one]
      rw [hdiag]
    · intro q hq
      have hzero := trace_qunit_inv_mul_eq_zero (ρ := ρ) (N := N) hK hN
        (q := q0) (q' := q) (Ne.symm hq)
      simp only [qmat]
      rw [hzero, mul_zero]
  rw [hsingle] at htrace
  exact (mul_eq_zero.mp htrace).resolve_right hι

private lemma natCard_quotient_eq [Finite Γ] {ρ : Γ →* GL ι K} {N : Subgroup Γ}
    (hN : IsQuatType ρ N)
    (hcard : Nat.card N = Fintype.card ι ^ 2 * Nat.card (scalSub ρ)) :
    Nat.card (N ⧸ (scalSub ρ).subgroupOf N) = Fintype.card ι ^ 2 := by
  have hZpos : 0 < Nat.card (scalSub ρ) := Nat.card_pos
  have h1 : Nat.card N = Nat.card (N ⧸ (scalSub ρ).subgroupOf N) *
      Nat.card ((scalSub ρ).subgroupOf N) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h2 : Nat.card ((scalSub ρ).subgroupOf N) = Nat.card (scalSub ρ) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN.scalars_le).toEquiv
  apply Nat.eq_of_mul_eq_mul_right hZpos
  calc Nat.card (N ⧸ (scalSub ρ).subgroupOf N) * Nat.card (scalSub ρ)
      = Nat.card (N ⧸ (scalSub ρ).subgroupOf N) *
          Nat.card ((scalSub ρ).subgroupOf N) := by rw [← h2]
    _ = Nat.card N := h1.symm
    _ = Fintype.card ι ^ 2 * Nat.card (scalSub ρ) := hcard

theorem card_le_of_isQuatType [Finite Γ] (hK : ringChar K ≠ 2)
    (hι : (Fintype.card ι : K) ≠ 0) (ρ : Γ →* GL ι K) (hρ : Function.Injective ρ)
    {N : Subgroup Γ} (hN : IsQuatType ρ N) :
    Nat.card N ≤ Fintype.card ι ^ 2 * Nat.card ((StatedScalars ι K).comap ρ) := by
  classical
  let Q := N ⧸ (scalSub ρ).subgroupOf N
  have _ := hρ
  have hli : LinearIndependent K (qmat ρ N (scalSub ρ)) :=
    qmat_linearIndependent hK hι hN
  have hcardQ : Fintype.card Q ≤ Fintype.card ι ^ 2 := by
    have hfin : Module.finrank K (Matrix ι ι K) = Fintype.card ι ^ 2 := by
      rw [Module.finrank_matrix, Module.finrank_self, mul_one, pow_two]
    calc Fintype.card Q ≤ Module.finrank K (Matrix ι ι K) :=
          LinearIndependent.fintype_card_le_finrank hli
      _ = Fintype.card ι ^ 2 := hfin
  have hNcard : Nat.card N = Nat.card Q * Nat.card ((scalSub ρ).subgroupOf N) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hZcard : Nat.card ((scalSub ρ).subgroupOf N) = Nat.card (scalSub ρ) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN.scalars_le).toEquiv
  have hQcard : Nat.card Q ≤ Fintype.card ι ^ 2 := by
    rw [Nat.card_eq_fintype_card]
    exact hcardQ
  calc Nat.card N = Nat.card Q * Nat.card ((scalSub ρ).subgroupOf N) := hNcard
    _ = Nat.card Q * Nat.card (scalSub ρ) := by rw [hZcard]
    _ ≤ Fintype.card ι ^ 2 * Nat.card (scalSub ρ) := Nat.mul_le_mul_right _ hQcard

theorem span_eq_top_of_isQuatType [Finite Γ] (hK : ringChar K ≠ 2)
    (hι : (Fintype.card ι : K) ≠ 0) (ρ : Γ →* GL ι K) (hρ : Function.Injective ρ)
    {N : Subgroup Γ} (hN : IsQuatType ρ N)
    (hcard : Nat.card N = Fintype.card ι ^ 2 * Nat.card ((StatedScalars ι K).comap ρ)) :
    Submodule.span K (Set.range fun x : N => (ρ x : Matrix ι ι K)) = ⊤ := by
  classical
  let Q := N ⧸ (scalSub ρ).subgroupOf N
  have _ := hρ
  have hfin : Module.finrank K (Matrix ι ι K) = Fintype.card ι ^ 2 := by
    rw [Module.finrank_matrix, Module.finrank_self, mul_one, pow_two]
  have hQnat : Nat.card Q = Fintype.card ι ^ 2 := natCard_quotient_eq hN hcard
  have hQcard : Fintype.card Q = Module.finrank K (Matrix ι ι K) := by
    rw [show Fintype.card Q = Nat.card Q from (Nat.card_eq_fintype_card).symm, hQnat, hfin]
  have hli : LinearIndependent K (qmat ρ N (scalSub ρ)) :=
    qmat_linearIndependent hK hι hN
  have hspanM : Submodule.span K (Set.range (qmat ρ N (scalSub ρ))) = ⊤ :=
    LinearIndependent.span_eq_top_of_card_eq_finrank' hli hQcard
  have hle : Submodule.span K (Set.range (qmat ρ N (scalSub ρ))) ≤
      Submodule.span K (Set.range fun x : N => (ρ x : Matrix ι ι K)) := by
    apply Submodule.span_mono
    rintro A ⟨q, rfl⟩
    exact ⟨qreps N (scalSub ρ) q, rfl⟩
  rw [eq_top_iff, ← hspanM]
  exact hle

private lemma scalSub_scalar {ρ : Γ →* GL ι K} {z : Γ} (hz : z ∈ scalSub ρ) :
    ∃ c : Kˣ, ρ z = Matrix.GeneralLinearGroup.scalar ι c := by
  have hz' : ρ z ∈ StatedScalars ι K := hz
  rw [StatedScalars] at hz'
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hz'
  exact ⟨c, hc.symm⟩

private lemma qmat_span_eq_top [Finite Γ] {ρ : Γ →* GL ι K} {N : Subgroup Γ}
    (hspan : Submodule.span K (Set.range fun x : N => (ρ x : Matrix ι ι K)) = ⊤) :
    Submodule.span K (Set.range (qmat ρ N (scalSub ρ))) = ⊤ := by
  classical
  rw [eq_top_iff, ← hspan, Submodule.span_le]
  rintro A ⟨x, rfl⟩
  let q : N ⧸ (scalSub ρ).subgroupOf N := QuotientGroup.mk x
  have hxq : ((x : N) : N ⧸ (scalSub ρ).subgroupOf N) = q := rfl
  have hdiv : x / qreps N (scalSub ρ) q ∈ (scalSub ρ).subgroupOf N :=
    (QuotientGroup.eq_iff_div_mem (N := (scalSub ρ).subgroupOf N)).mp
      (by rw [hxq, qreps_mk])
  have hdiv' : ((x / qreps N (scalSub ρ) q : N) : Γ) ∈ scalSub ρ := by
    rwa [Subgroup.mem_subgroupOf] at hdiv
  let t : Γ := ((qreps N (scalSub ρ) q : N) : Γ)
  let z : Γ := ((x / qreps N (scalSub ρ) q : N) : Γ)
  have hz : z ∈ scalSub ρ := hdiv'
  have hxzt : ((x : N) : Γ) = z * t := by
    simp only [z, t, Subgroup.coe_div]
    rw [div_mul_cancel]
  obtain ⟨c, hc⟩ := scalSub_scalar (ρ := ρ) hz
  have hxmat : (ρ ((x : N) : Γ) : Matrix ι ι K) =
      (c : K) • qmat ρ N (scalSub ρ) q := by
    calc (ρ ((x : N) : Γ) : Matrix ι ι K)
        = (ρ (z * t) : Matrix ι ι K) := by rw [hxzt]
      _ = ((ρ z * ρ t : GL ι K) : Matrix ι ι K) := by rw [map_mul]
      _ = ((Matrix.GeneralLinearGroup.scalar ι c * ρ t : GL ι K) : Matrix ι ι K) := by
            rw [hc]
      _ = (Matrix.GeneralLinearGroup.scalar ι c : Matrix ι ι K) *
            (ρ t : Matrix ι ι K) := by rw [Units.val_mul]
      _ = (Matrix.scalar ι (c : K)) * (qmat ρ N (scalSub ρ) q) := by
            rw [Matrix.GeneralLinearGroup.coe_scalar]
            simp only [qmat, qunit, t]
      _ = ((c : K) • (1 : Matrix ι ι K)) * (qmat ρ N (scalSub ρ) q) := by
            rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
      _ = (c : K) • ((1 : Matrix ι ι K) * (qmat ρ N (scalSub ρ) q)) := by
            rw [Matrix.smul_mul]
      _ = (c : K) • (qmat ρ N (scalSub ρ) q) := by rw [one_mul]
  change (ρ ((x : N) : Γ) : Matrix ι ι K) ∈
    Submodule.span K (Set.range (qmat ρ N (scalSub ρ)))
  rw [hxmat]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)

private lemma conj_qmat_eq_or {ρ : Γ →* GL ι K} {N : Subgroup Γ} (hN : IsQuatType ρ N)
    (x : N) (q : N ⧸ (scalSub ρ).subgroupOf N) :
    (ρ ((x : N) : Γ) : Matrix ι ι K) * qmat ρ N (scalSub ρ) q *
        (↑((ρ ((x : N) : Γ))⁻¹) : Matrix ι ι K) = qmat ρ N (scalSub ρ) q ∨
    (ρ ((x : N) : Γ) : Matrix ι ι K) * qmat ρ N (scalSub ρ) q *
        (↑((ρ ((x : N) : Γ))⁻¹) : Matrix ι ι K) = -qmat ρ N (scalSub ρ) q := by
  rcases hN.comm_or_anticomm ((x : N) : Γ) x.2
      ((qreps N (scalSub ρ) q : N) : Γ) (qreps N (scalSub ρ) q).2 with hcomm | hanti
  · left
    have h1 : (ρ ((x : N) : Γ) : Matrix ι ι K) * qmat ρ N (scalSub ρ) q =
        qmat ρ N (scalSub ρ) q * (ρ ((x : N) : Γ) : Matrix ι ι K) := by
      simpa only [qmat, qunit, map_mul, Units.val_mul] using
        congrArg (fun g : Γ => (ρ g : Matrix ι ι K)) hcomm
    calc (ρ ((x : N) : Γ) : Matrix ι ι K) * qmat ρ N (scalSub ρ) q *
          (↑((ρ ((x : N) : Γ))⁻¹) : Matrix ι ι K)
        = (qmat ρ N (scalSub ρ) q * (ρ ((x : N) : Γ) : Matrix ι ι K)) *
            (↑((ρ ((x : N) : Γ))⁻¹) : Matrix ι ι K) := by rw [h1]
      _ = qmat ρ N (scalSub ρ) q := by
            rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  · right
    have h1 : (ρ ((x : N) : Γ) : Matrix ι ι K) * qmat ρ N (scalSub ρ) q =
        -(qmat ρ N (scalSub ρ) q * (ρ ((x : N) : Γ) : Matrix ι ι K)) := by
      simpa only [qmat, qunit, map_mul, Units.val_mul] using hanti
    calc (ρ ((x : N) : Γ) : Matrix ι ι K) * qmat ρ N (scalSub ρ) q *
          (↑((ρ ((x : N) : Γ))⁻¹) : Matrix ι ι K)
        = (-(qmat ρ N (scalSub ρ) q * (ρ ((x : N) : Γ) : Matrix ι ι K))) *
            (↑((ρ ((x : N) : Γ))⁻¹) : Matrix ι ι K) := by rw [h1]
      _ = -(qmat ρ N (scalSub ρ) q) := by
            rw [neg_mul, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

private noncomputable def chi (u : GL ι K) (M : Matrix ι ι K) : K := by
  classical
  exact if (u : Matrix ι ι K) * M * (↑(u⁻¹) : Matrix ι ι K) = M then 1 else -1

private lemma chi_spec {u : GL ι K} {M : Matrix ι ι K}
    (h : (u : Matrix ι ι K) * M * (↑(u⁻¹) : Matrix ι ι K) = M ∨
      (u : Matrix ι ι K) * M * (↑(u⁻¹) : Matrix ι ι K) = -M) :
    (chi u M = 1 ∨ chi u M = -1) ∧
      (u : Matrix ι ι K) * M * (↑(u⁻¹) : Matrix ι ι K) = chi u M • M := by
  classical
  unfold chi
  by_cases hM : (u : Matrix ι ι K) * M * (↑(u⁻¹) : Matrix ι ι K) = M
  · rw [if_pos hM]
    exact ⟨Or.inl rfl, by rw [hM, one_smul]⟩
  · rw [if_neg hM]
    refine ⟨Or.inr rfl, ?_⟩
    rcases h with h1 | h2
    · exact absurd h1 hM
    · rw [h2, neg_smul, one_smul]

private lemma conj_mul_inv_of_conj {G : Type*} [Group G] (z g h k : G)
    (hz : ∀ a : G, z * a = a * z)
    (hh : g * h * g⁻¹ = z * h) (hk : g * k * g⁻¹ = z * k) :
    g * (h * k⁻¹) * g⁻¹ = h * k⁻¹ := by
  calc g * (h * k⁻¹) * g⁻¹
      = (g * h * g⁻¹) * (g * k * g⁻¹)⁻¹ := by group
    _ = (z * h) * (z * k)⁻¹ := by rw [hh, hk]
    _ = z * (h * k⁻¹) * z⁻¹ := by group
    _ = (h * k⁻¹) * z * z⁻¹ := by rw [hz (h * k⁻¹)]
    _ = h * k⁻¹ := by group

private lemma qunit_conj_eq {u v : GL ι K} {c : Kˣ}
    (h : (u : Matrix ι ι K) * (v : Matrix ι ι K) * (↑(u⁻¹) : Matrix ι ι K) =
      ((c : K)⁻¹) • (v : Matrix ι ι K)) :
    u * v * u⁻¹ = Matrix.GeneralLinearGroup.scalar ι c⁻¹ * v := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, h]
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, one_mul, Units.val_inv_eq_inv_val c]

theorem exists_mem_mul_inv_mem_scalars [Finite Γ] (hK : ringChar K ≠ 2)
    (hι : (Fintype.card ι : K) ≠ 0) (ρ : Γ →* GL ι K) (hρ : Function.Injective ρ)
    {N : Subgroup Γ} (hN : IsQuatType ρ N)
    (hspan : Submodule.span K (Set.range fun x : N => (ρ x : Matrix ι ι K)) = ⊤)
    (A : GL ι K) (hA : ∀ x ∈ N, A * ρ x * A⁻¹ * (ρ x)⁻¹ ∈ StatedScalars ι K) :
    ∃ y ∈ N, A * (ρ y)⁻¹ ∈ StatedScalars ι K := by
  classical
  have hne : Nonempty ι := by
    have h0 : Fintype.card ι ≠ 0 := by
      intro hc
      apply hι
      rw [hc]
      exact Nat.cast_zero
    exact Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero h0)
  let Q := N ⧸ (scalSub ρ).subgroupOf N
  have hspanM : Submodule.span K (Set.range (qmat ρ N (scalSub ρ))) = ⊤ :=
    qmat_span_eq_top hspan
  have hli : LinearIndependent K (qmat ρ N (scalSub ρ)) :=
    qmat_linearIndependent hK hι hN
  have hqcard : Fintype.card Q = Module.finrank K (Matrix ι ι K) := by
    have h1 := finrank_span_eq_card hli
    rw [hspanM, finrank_top] at h1
    exact h1.symm
  let b : Module.Basis Q K (Matrix ι ι K) :=
    basisOfLinearIndependentOfCardEqFinrank' (qmat ρ N (scalSub ρ)) hli hqcard
  have hb : (b : Q → Matrix ι ι K) = qmat ρ N (scalSub ρ) :=
    coe_basisOfLinearIndependentOfCardEqFinrank' (qmat ρ N (scalSub ρ)) hli hqcard
  let a : Q → K := fun q => b.repr A q
  have hA_sum : (A : Matrix ι ι K) = ∑ q, a q • qmat ρ N (scalSub ρ) q := by
    rw [← Module.Basis.sum_repr b A]
    simp only [a, hb]
  have hA_ne : (A : Matrix ι ι K) ≠ 0 := by
    intro h0
    obtain ⟨i⟩ := hne
    have h1 : (1 : Matrix ι ι K) = 0 := by
      calc (1 : Matrix ι ι K) = ↑(A⁻¹ * A) := by rw [inv_mul_cancel, Units.val_one]
        _ = (↑(A⁻¹) : Matrix ι ι K) * (↑A : Matrix ι ι K) := by rw [Units.val_mul]
        _ = (↑(A⁻¹) : Matrix ι ι K) * 0 := by rw [h0]
        _ = 0 := by rw [mul_zero]
    have h2 := congrFun (congrFun h1 i) i
    rw [Matrix.one_apply_eq, Matrix.zero_apply] at h2
    exact one_ne_zero h2
  have hcoeff : ∀ x : N, ∃ c : Kˣ, ∀ q : Q, a q ≠ 0 →
      ρ ((x : N) : Γ) * qunit ρ N (scalSub ρ) q * (ρ ((x : N) : Γ))⁻¹ =
        Matrix.GeneralLinearGroup.scalar ι c⁻¹ * qunit ρ N (scalSub ρ) q := by
    intro x
    obtain ⟨c, hc⟩ : ∃ c : Kˣ,
        Matrix.GeneralLinearGroup.scalar ι c =
          A * ρ ((x : N) : Γ) * A⁻¹ * (ρ ((x : N) : Γ))⁻¹ := by
      have hmem := hA ((x : N) : Γ) x.2
      rw [StatedScalars] at hmem
      exact MonoidHom.mem_range.mp hmem
    have h1 : A * ρ ((x : N) : Γ) =
        Matrix.GeneralLinearGroup.scalar ι c * (ρ ((x : N) : Γ) * A) := by
      rw [hc]
      group
    have hconj : ρ ((x : N) : Γ) * A * (ρ ((x : N) : Γ))⁻¹ =
        Matrix.GeneralLinearGroup.scalar ι c⁻¹ * A := by
      have h1' : (Matrix.GeneralLinearGroup.scalar ι c)⁻¹ *
          (A * ρ ((x : N) : Γ)) = ρ ((x : N) : Γ) * A := by
        rw [h1]
        group
      calc ρ ((x : N) : Γ) * A * (ρ ((x : N) : Γ))⁻¹
          = ((Matrix.GeneralLinearGroup.scalar ι c)⁻¹ *
              (A * ρ ((x : N) : Γ))) * (ρ ((x : N) : Γ))⁻¹ := by rw [h1']
        _ = (Matrix.GeneralLinearGroup.scalar ι c)⁻¹ * A := by group
        _ = Matrix.GeneralLinearGroup.scalar ι c⁻¹ * A := by rw [← map_inv]
    have hconjMat : (ρ ((x : N) : Γ) : Matrix ι ι K) * (A : Matrix ι ι K) *
        (↑((ρ ((x : N) : Γ))⁻¹) : Matrix ι ι K) =
        ((c : K)⁻¹) • (A : Matrix ι ι K) := by
      have h := congrArg (fun u : GL ι K => (u : Matrix ι ι K)) hconj
      rw [Units.val_mul, Units.val_mul] at h
      rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, one_mul, Units.val_inv_eq_inv_val c] at h
      exact h
    refine ⟨c, fun q haq => ?_⟩
    have hchi : chi (ρ ((x : N) : Γ)) (qmat ρ N (scalSub ρ) q) = ((c : K)⁻¹) := by
      have hsum1 : (ρ ((x : N) : Γ) : Matrix ι ι K) * (A : Matrix ι ι K) *
          (↑((ρ ((x : N) : Γ))⁻¹) : Matrix ι ι K) =
          ∑ r, (a r * chi (ρ ((x : N) : Γ)) (qmat ρ N (scalSub ρ) r)) •
            qmat ρ N (scalSub ρ) r := by
        rw [hA_sum, Matrix.mul_sum, Matrix.sum_mul]
        apply Finset.sum_congr rfl
        intro r _
        rw [Matrix.mul_smul, Matrix.smul_mul]
        rw [(chi_spec (conj_qmat_eq_or (ρ := ρ) (N := N) hN x r)).2]
        rw [smul_smul]
      have hsum2 : ((c : K)⁻¹) • (A : Matrix ι ι K) =
          ∑ r, (((c : K)⁻¹) * a r) • qmat ρ N (scalSub ρ) r := by
        rw [hA_sum, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro r _
        rw [smul_smul]
      have heq : ∑ r, (a r * chi (ρ ((x : N) : Γ)) (qmat ρ N (scalSub ρ) r)) •
            qmat ρ N (scalSub ρ) r =
          ∑ r, (((c : K)⁻¹) * a r) • qmat ρ N (scalSub ρ) r := by
        rw [← hsum1, hconjMat, hsum2]
      have hcoeff_eq := LinearIndependent.eq_coords_of_eq hli heq q
      have hcoeff_eq' : a q * chi (ρ ((x : N) : Γ)) (qmat ρ N (scalSub ρ) q) =
          a q * ((c : K)⁻¹) := by
        rw [mul_comm ((c : K)⁻¹) (a q)] at hcoeff_eq
        exact hcoeff_eq
      exact mul_left_cancel₀ haq hcoeff_eq'
    have hconjMat' : (ρ ((x : N) : Γ) : Matrix ι ι K) *
        (qunit ρ N (scalSub ρ) q : Matrix ι ι K) *
        (↑((ρ ((x : N) : Γ))⁻¹) : Matrix ι ι K) =
        ((c : K)⁻¹) • (qunit ρ N (scalSub ρ) q : Matrix ι ι K) := by
      rw [← hchi]
      simpa only [qmat] using (chi_spec (conj_qmat_eq_or (ρ := ρ) (N := N) hN x q)).2
    exact qunit_conj_eq hconjMat'
  have hsupport : ∀ q q' : Q, a q ≠ 0 → a q' ≠ 0 → q = q' := by
    intro q q' haq haq'
    by_contra hne
    have hcomm_all : ∀ x : N,
        ((x : N) : Γ) * ((qreps N (scalSub ρ) q * (qreps N (scalSub ρ) q')⁻¹ : N) : Γ) =
        ((qreps N (scalSub ρ) q * (qreps N (scalSub ρ) q')⁻¹ : N) : Γ) * ((x : N) : Γ) := by
      intro x
      obtain ⟨c, hc⟩ := hcoeff x
      have hq := hc q haq
      have hq' := hc q' haq'
      let z : GL ι K := Matrix.GeneralLinearGroup.scalar ι c⁻¹
      have hz : ∀ w : GL ι K, z * w = w * z :=
        fun w => Matrix.GeneralLinearGroup.scalar_commute c⁻¹ w
      have hmain := conj_mul_inv_of_conj z (ρ ((x : N) : Γ))
        (qunit ρ N (scalSub ρ) q) (qunit ρ N (scalSub ρ) q') hz hq hq'
      let s : N := qreps N (scalSub ρ) q * (qreps N (scalSub ρ) q')⁻¹
      have hqs : qunit ρ N (scalSub ρ) q * (qunit ρ N (scalSub ρ) q')⁻¹ =
          ρ ((s : N) : Γ) := by
        simp only [qunit, s, Subgroup.coe_mul, Subgroup.coe_inv]
        rw [map_mul, map_inv]
      rw [hqs] at hmain
      have h1 : ρ (((x : N) : Γ) * ((s : N) : Γ) * ((x : N) : Γ)⁻¹) =
          ρ ((s : N) : Γ) := by
        rw [map_mul, map_mul, map_inv]
        exact hmain
      have h2 : ((x : N) : Γ) * ((s : N) : Γ) * ((x : N) : Γ)⁻¹ = ((s : N) : Γ) :=
        hρ h1
      calc ((x : N) : Γ) * ((s : N) : Γ)
          = ((((x : N) : Γ) * ((s : N) : Γ) * ((x : N) : Γ)⁻¹) *
              ((x : N) : Γ)) := by group
        _ = ((s : N) : Γ) * ((x : N) : Γ) := by rw [h2]
    have hsZ : (((qreps N (scalSub ρ) q * (qreps N (scalSub ρ) q')⁻¹ : N) : Γ)) ∈
        scalSub ρ := by
      apply hN.mem_of_comm
      · exact (qreps N (scalSub ρ) q * (qreps N (scalSub ρ) q')⁻¹).2
      · intro y hy
        exact (hcomm_all ⟨y, hy⟩).symm
    have hsub : qreps N (scalSub ρ) q * (qreps N (scalSub ρ) q')⁻¹ ∈
        (scalSub ρ).subgroupOf N := by
      rw [Subgroup.mem_subgroupOf]
      exact hsZ
    have heq : ((qreps N (scalSub ρ) q : N) : Q) =
        ((qreps N (scalSub ρ) q' : N) : Q) := by
      rw [QuotientGroup.eq_iff_div_mem]
      simpa only [div_eq_mul_inv] using hsub
    rw [qreps_mk, qreps_mk] at heq
    exact hne heq
  have hex : ∃ q : Q, a q ≠ 0 := by
    by_contra h
    push Not at h
    apply hA_ne
    rw [hA_sum]
    exact Finset.sum_eq_zero (fun q _ => by rw [h q, zero_smul])
  obtain ⟨q0, hq0⟩ := hex
  have hA_single : (A : Matrix ι ι K) = a q0 • qmat ρ N (scalSub ρ) q0 := by
    rw [hA_sum, Fintype.sum_eq_single q0]
    intro q hq
    have hzero : a q = 0 := by
      by_contra ha
      exact hq (hsupport q q0 ha hq0)
    rw [hzero, zero_smul]
  have hfinal : (A : Matrix ι ι K) *
      (↑((ρ (((qreps N (scalSub ρ) q0 : N) : Γ)))⁻¹) : Matrix ι ι K) =
      a q0 • (1 : Matrix ι ι K) := by
    rw [hA_single, Matrix.smul_mul]
    congr 1
    simp only [qmat, qunit]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine ⟨qreps N (scalSub ρ) q0, (qreps N (scalSub ρ) q0).2, ?_⟩
  rw [StatedScalars]
  refine MonoidHom.mem_range.mpr ⟨Units.mk0 (a q0) hq0, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mul, Units.val_mk0]
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
  exact hfinal.symm

end CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural
