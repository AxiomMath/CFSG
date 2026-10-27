module

public import CFSG.RankThree.PartTwo.Sec14.Item148StepKFacts
public import CFSG.RankThree.PartTwo.Sec14.Item148RankProofFieldTools
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
public import CFSG.RankThree.PartTwo.KFacts.K72L3Linear

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank

namespace Item148Rank

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts
open Matrix

theorem mul_pow_mem_of_mod148 {G M : Type*} [Group G] [Group M] {N : Subgroup G} [N.Normal]
    (φ : M →* G) {α β : G} {σ σ' : M} (hα : α * (φ σ)⁻¹ ∈ N) (hβ : β * (φ σ')⁻¹ ∈ N) {k : ℕ}
    (hk : σ' * σ ^ k = 1) : β * α ^ k ∈ N := by
  have e1 : QuotientGroup.mk' N α = QuotientGroup.mk' N (φ σ) := by
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hα
  have e2 : QuotientGroup.mk' N β = QuotientGroup.mk' N (φ σ') := by
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hβ
  have h : QuotientGroup.mk' N (β * α ^ k) = 1 := by
    rw [map_mul, map_pow, e1, e2, ← map_pow, ← map_mul, ← map_pow, ← map_mul, hk, map_one,
      map_one]
  rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h

theorem conj_mul_inv_mem148 {G : Type*} [Group G] {N : Subgroup G} [hN : N.Normal] {d : G}
    (hd : d ∈ N) (φ : G) : d * φ * d⁻¹ * φ⁻¹ ∈ N := by
  have h1 : φ * d⁻¹ * φ⁻¹ ∈ N := hN.conj_mem _ (inv_mem hd) φ
  rw [show d * φ * d⁻¹ * φ⁻¹ = d * (φ * d⁻¹ * φ⁻¹) by group]
  exact mul_mem hd h1

theorem exists_isInnerAut_mul_pow_congr148 {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hY : ∀ α β : MulAut Y, α ^ 3 = 1 → β ^ 3 = 1 → α * β = β * α → ¬ IsInnerAut α →
      ∃ k : ℕ, IsInnerAut (β * α ^ k))
    {α β : MulAut X} (hα3 : α ^ 3 = 1) (hβ3 : β ^ 3 = 1) (hαβ : α * β = β * α)
    (hα : ¬ IsInnerAut α) : ∃ k : ℕ, IsInnerAut (β * α ^ k) := by
  obtain ⟨k, hk⟩ := hY (MulAut.congr e α) (MulAut.congr e β)
    (by rw [← map_pow, hα3, map_one]) (by rw [← map_pow, hβ3, map_one])
    (by rw [← map_mul, ← map_mul, hαβ]) (fun h => hα ((isInnerAut_congr e α).mp h))
  refine ⟨k, (isInnerAut_congr e _).mp ?_⟩
  rwa [map_mul, map_pow]

section Linear

variable {K : Type} [Field K] [Finite K]

theorem isInnerAut_of_commute_field148 {p F : ℕ} (hp : p.Prime) (hF : 1 ≤ F)
    (hcard : Nat.card K = p ^ F) (hK : p ^ F % 3 = 1) {γ : MulAut (projectiveSL 3 K)}
    (hγ : γ ∈ linearAutGroup 3 K) {σ : K ≃+* K} (hσ : orderOf σ = 3) (H : GL (Fin 3) K)
    (hc : γ * (conjAut 3 K H * fieldAut 3 K σ * (conjAut 3 K H)⁻¹) =
      (conjAut 3 K H * fieldAut 3 K σ * (conjAut 3 K H)⁻¹) * γ) :
    IsInnerAut γ := by
  obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hγ
  have hc' : conjAut 3 K (H⁻¹ * A * H) * fieldAut 3 K σ =
      fieldAut 3 K σ * conjAut 3 K (H⁻¹ * A * H) := by
    rw [map_mul, map_mul, map_inv]
    calc (conjAut 3 K H)⁻¹ * conjAut 3 K A * conjAut 3 K H * fieldAut 3 K σ =
        (conjAut 3 K H)⁻¹ * (conjAut 3 K A *
          (conjAut 3 K H * fieldAut 3 K σ * (conjAut 3 K H)⁻¹)) * conjAut 3 K H := by group
      _ = (conjAut 3 K H)⁻¹ * ((conjAut 3 K H * fieldAut 3 K σ * (conjAut 3 K H)⁻¹) *
          conjAut 3 K A) * conjAut 3 K H := by rw [hc]
      _ = fieldAut 3 K σ * ((conjAut 3 K H)⁻¹ * conjAut 3 K A * conjAut 3 K H) := by group
  obtain ⟨u, hu⟩ := exists_cube_det_of_commute148 hp hF hcard hK hσ _ hc'
  refine isInnerAut_conjAut_of_det_eq_cube148 A (u := u) ?_
  rw [hu, map_mul, map_mul, map_inv, mul_comm (GeneralLinearGroup.det H)⁻¹,
    inv_mul_cancel_right]

theorem exists_isInnerAut_mul_pow_linear148 {p F : ℕ} (hp : p.Prime) (hF : 1 ≤ F)
    (hcard : Nat.card K = p ^ F) (hK : p ^ F % 3 = 1) {α β : MulAut (projectiveSL 3 K)}
    (hα3 : α ^ 3 = 1) (hβ3 : β ^ 3 = 1) (hαβ : α * β = β * α) (hα : ¬ IsInnerAut α) :
    ∃ k : ℕ, IsInnerAut (β * α ^ k) := by
  have hN : (linearAutGroup 3 K).Normal := (stdPinnedPSL_stable (n := 3) (K := K) le_rfl).normal
  have hcardU : Nat.card Kˣ = p ^ F - 1 := by rw [Nat.card_units, hcard]
  have hm3 : 3 ∣ p ^ F - 1 := by
    have := Nat.one_le_pow F p hp.pos
    omega
  by_cases hD : α ∈ linearAutGroup 3 K
  · obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hD
    have hnd : ¬ ∃ u : Kˣ, u ^ (p ^ F - 1) = 1 ∧ u ^ 3 = GeneralLinearGroup.det A :=
      fun ⟨u, _, hu⟩ => hα (isInnerAut_conjAut_of_det_eq_cube148 A hu)
    by_cases hβD : β ∈ linearAutGroup 3 K
    · obtain ⟨B, rfl⟩ := mem_linearAutGroup_iff.mp hβD
      obtain ⟨k, -, u, -, hu⟩ := exists_mul_pow_cube148 (G := Kˣ)
        (d := GeneralLinearGroup.det A) (b := GeneralLinearGroup.det B) (by rw [hcardU]) hm3
        (by rw [← hcardU]; exact pow_card_eq_one') (by rw [← hcardU]; exact pow_card_eq_one')
        hnd
      refine ⟨k, ?_⟩
      rw [← map_pow, ← map_mul]
      refine isInnerAut_conjAut_of_det_eq_cube148 _ (u := u) ?_
      rw [hu, map_mul, map_pow]
    · obtain ⟨σ, hσ, H, hβH⟩ := linear_order_three_field_descent le_rfl β hβ3 hβD
      exact (hα (isInnerAut_of_commute_field148 hp hF hcard hK hD hσ H (hβH ▸ hαβ))).elim
  · obtain ⟨σ, hσ, H, hαH⟩ := linear_order_three_field_descent le_rfl α hα3 hD
    by_cases hβD : β ∈ linearAutGroup 3 K
    · refine ⟨0, ?_⟩
      rw [pow_zero, mul_one]
      exact isInnerAut_of_commute_field148 hp hF hcard hK hβD hσ H (hαH ▸ hαβ.symm)
    · obtain ⟨σ', hσ', H', hβH'⟩ := linear_order_three_field_descent le_rfl β hβ3 hβD
      have hαmod : α * (fieldAut 3 K σ)⁻¹ ∈ linearAutGroup 3 K := by
        rw [hαH]
        exact conj_mul_inv_mem148 (conjAut_mem_linearAutGroup H) _
      have hβmod : β * (fieldAut 3 K σ')⁻¹ ∈ linearAutGroup 3 K := by
        rw [hβH']
        exact conj_mul_inv_mem148 (conjAut_mem_linearAutGroup H') _
      have hσ3 : σ ^ 3 = 1 := by rw [← hσ, pow_orderOf_eq_one]
      obtain ⟨k, hk⟩ : ∃ k : ℕ, σ' * σ ^ k = 1 := by
        rcases ringAut_eq_or_mul_eq_one148 hp hF hcard hσ hσ' with h | h
        · exact ⟨2, by rw [h, ← pow_succ', hσ3]⟩
        · exact ⟨1, by rw [pow_one, h]⟩
      refine ⟨k, isInnerAut_of_commute_field148 hp hF hcard hK
        (mul_pow_mem_of_mod148 (fieldAut 3 K) hαmod hβmod hk) hσ H ?_⟩
      rw [← hαH]
      have h1 : Commute β α := (show Commute α β from hαβ).symm
      exact ((h1.mul_left (Commute.pow_left (Commute.refl α) k)).eq)

end Linear

section Unitary

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem isInnerAut_of_commute_field_psu148 (hq : p ^ f % 3 = 2)
    {γ : MulAut (unitaryPSU h 3)} (hγ : γ ∈ (psuConj h).range) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) (H : unitaryIsom3 h)
    (hc : γ * (psuConj h H * psuField h σ * (psuConj h H)⁻¹) =
      (psuConj h H * psuField h σ * (psuConj h H)⁻¹) * γ) :
    IsInnerAut γ := by
  obtain ⟨A, rfl⟩ := hγ
  have hc' : psuConj h (H⁻¹ * A * H) * psuField h σ =
      psuField h σ * psuConj h (H⁻¹ * A * H) := by
    rw [map_mul, map_mul, map_inv]
    calc (psuConj h H)⁻¹ * psuConj h A * psuConj h H * psuField h σ =
        (psuConj h H)⁻¹ * (psuConj h A *
          (psuConj h H * psuField h σ * (psuConj h H)⁻¹)) * psuConj h H := by group
      _ = (psuConj h H)⁻¹ * ((psuConj h H * psuField h σ * (psuConj h H)⁻¹) *
          psuConj h A) * psuConj h H := by rw [hc]
      _ = psuField h σ * ((psuConj h H)⁻¹ * psuConj h A * psuConj h H) := by group
  obtain ⟨u, hu1, hu⟩ := exists_cube_det_of_commute_psu148 hq hσ _ hc'
  refine isInnerAut_psuConj_of_det_eq_cube148 A (u := u) ?_ hu1
  rw [hu]
  change GeneralLinearGroup.det ((H : GL (Fin 3) K)⁻¹ * (A : GL (Fin 3) K) * (H : GL (Fin 3) K)) =
    GeneralLinearGroup.det (A : GL (Fin 3) K)
  rw [map_mul, map_mul, map_inv, mul_comm (GeneralLinearGroup.det (H : GL (Fin 3) K))⁻¹,
    inv_mul_cancel_right]

theorem exists_isInnerAut_mul_pow_unitary148 (hq : p ^ f % 3 = 2) (hq2 : 2 < p ^ f)
    {α β : MulAut (unitaryPSU h 3)} (hα3 : α ^ 3 = 1) (hβ3 : β ^ 3 = 1) (hαβ : α * β = β * α)
    (hα : ¬ IsInnerAut α) : ∃ k : ℕ, IsInnerAut (β * α ^ k) := by
  have := h.finite
  have hN : (psuConj h).range.Normal := (stdPinnedPSU3_stable (h := h) hq2).normal
  have hpow2 : p ^ (2 * f) = (p ^ f) ^ 2 := by rw [pow_mul']
  have hcardU : Nat.card Kˣ = (p ^ f) ^ 2 - 1 := by rw [Nat.card_units, h.card, hpow2]
  have hm : p ^ f + 1 ∣ Nat.card Kˣ := by
    rw [hcardU]
    refine ⟨p ^ f - 1, ?_⟩
    obtain ⟨s, hs⟩ : ∃ s, p ^ f = s + 1 := ⟨p ^ f - 1, by omega⟩
    rw [hs, Nat.add_sub_cancel]
    have : (s + 1) ^ 2 = (s + 1 + 1) * s + 1 := by ring
    omega
  have hm3 : 3 ∣ p ^ f + 1 := by omega
  by_cases hD : α ∈ (psuConj h).range
  · obtain ⟨A, rfl⟩ := hD
    have hnd : ¬ ∃ u : Kˣ, u ^ (p ^ f + 1) = 1 ∧ u ^ 3 = GeneralLinearGroup.det
        (A : GL (Fin 3) K) :=
      fun ⟨u, hu1, hu⟩ => hα (isInnerAut_psuConj_of_det_eq_cube148 A hu hu1)
    by_cases hβD : β ∈ (psuConj h).range
    · obtain ⟨B, rfl⟩ := hβD
      obtain ⟨k, -, u, hu1, hu⟩ := exists_mul_pow_cube148 (G := Kˣ) hm hm3
        (det_pow_succ_eq_one_of_mem_unitaryIsom3 h A.2)
        (det_pow_succ_eq_one_of_mem_unitaryIsom3 h B.2) hnd
      refine ⟨k, ?_⟩
      rw [← map_pow, ← map_mul]
      refine isInnerAut_psuConj_of_det_eq_cube148 _ (u := u) ?_ hu1
      rw [hu]
      change _ = GeneralLinearGroup.det ((B : GL (Fin 3) K) * (A : GL (Fin 3) K) ^ k)
      rw [map_mul, map_pow]
    · obtain ⟨σ, hσ, H, hβH⟩ := unitary_order_three_field_descent hq2 β hβ3 hβD
      exact (hα (isInnerAut_of_commute_field_psu148 hq (MonoidHom.mem_range.mpr ⟨A, rfl⟩) hσ H
        (hβH ▸ hαβ))).elim
  · obtain ⟨σ, hσ, H, hαH⟩ := unitary_order_three_field_descent hq2 α hα3 hD
    by_cases hβD : β ∈ (psuConj h).range
    · refine ⟨0, ?_⟩
      rw [pow_zero, mul_one]
      exact isInnerAut_of_commute_field_psu148 hq hβD hσ H (hαH ▸ hαβ.symm)
    · obtain ⟨σ', hσ', H', hβH'⟩ := unitary_order_three_field_descent hq2 β hβ3 hβD
      have hαmod : α * (psuField h σ)⁻¹ ∈ (psuConj h).range := by
        rw [hαH]
        exact conj_mul_inv_mem148 (MonoidHom.mem_range.mpr ⟨H, rfl⟩) _
      have hβmod : β * (psuField h σ')⁻¹ ∈ (psuConj h).range := by
        rw [hβH']
        exact conj_mul_inv_mem148 (MonoidHom.mem_range.mpr ⟨H', rfl⟩) _
      have hσ3 : σ ^ 3 = 1 := by rw [← hσ, pow_orderOf_eq_one]
      obtain ⟨k, hk⟩ : ∃ k : ℕ, σ' * σ ^ k = 1 := by
        rcases ringAut_eq_or_mul_eq_one148 h.prime (by have := h.one_le; omega) h.card hσ hσ'
          with h1 | h1
        · exact ⟨2, by rw [h1, ← pow_succ', hσ3]⟩
        · exact ⟨1, by rw [pow_one, h1]⟩
      refine ⟨k, isInnerAut_of_commute_field_psu148 hq
        (mul_pow_mem_of_mod148 (psuField h) hαmod hβmod hk) hσ H ?_⟩
      rw [← hαH]
      have h1 : Commute β α := (show Commute α β from hαβ).symm
      exact ((h1.mul_left (Commute.pow_left (Commute.refl α) k)).eq)

end Unitary

theorem exists_isInnerAut_mul_pow_of_isoLThreePi148 {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (hX : Sec4.IsoLThreePi X 2 (3 * n)) {α β : MulAut X} (hα3 : α ^ 3 = 1) (hβ3 : β ^ 3 = 1)
    (hαβ : α * β = β * α) (hα : ¬ IsInnerAut α) : ∃ k : ℕ, IsInnerAut (β * α ^ k) := by
  rcases hX with ⟨hq, ⟨e⟩⟩ | ⟨hq, ⟨e⟩⟩
  · obtain ⟨φ⟩ := nonempty_projSL_mulEquiv 3 (GaloisField 2 (3 * n))
    exact exists_isInnerAut_mul_pow_congr148 (e.trans φ)
      (fun α' β' h1 h2 h3 h4 => exists_isInnerAut_mul_pow_linear148 Nat.prime_two (by omega)
        (GaloisField.card 2 (3 * n) (by omega)) hq h1 h2 h3 h4) hα3 hβ3 hαβ hα
  · have h : UnitaryFieldData 2 (3 * n) (GaloisField 2 (2 * (3 * n))) :=
      ⟨Nat.prime_two, by omega, GaloisField.card 2 _ (by omega)⟩
    obtain ⟨φ⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
    have hq2 : 2 < 2 ^ (3 * n) :=
      lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * n))
    exact exists_isInnerAut_mul_pow_congr148 (e.trans φ.symm)
      (fun α' β' h1 h2 h3 h4 => exists_isInnerAut_mul_pow_unitary148 (h := h) hq hq2 h1 h2 h3 h4)
      hα3 hβ3 hαβ hα

theorem innerOn148_of_isInnerAut148 {Γ : Type*} [Group Γ] {X : Subgroup Γ} {g : Γ}
    (hg : g ∈ Subgroup.normalizer (X : Set Γ))
    (h : IsInnerAut (X.normalizerMonoidHom ⟨g, hg⟩)) : InnerOn148 X g := by
  obtain ⟨w, hw⟩ := h
  refine ⟨w, w.2, fun y hy => ?_⟩
  have h1 := congrArg (fun τ : MulAut X => ((τ ⟨y, hy⟩ : X) : Γ)) hw
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
  rw [h1]
  rfl

end Item148Rank

open Item148Rank

section Field


theorem not_isInnerAut_of_inducesStdKind_field148 {Γ : Type} [Group Γ] [Finite Γ]
    {X : Subgroup Γ} {x : Γ} (hfield : KFacts.InducesStdKind X x .field)
    (hx : x ∈ Subgroup.normalizer (X : Set Γ)) :
    ¬ KFacts.IsInnerAut (X.normalizerMonoidHom ⟨x, hx⟩) := by
  obtain ⟨hx', hnot⟩ := KFacts.InducesStdKind.inducesOuterTheta X hfield (by decide)
  rintro ⟨w, hw⟩
  apply hnot
  refine ⟨((w : X) : ↥X ⧸ aschbacherSolvableCore 3 ↥X), ?_⟩
  have hc : Sec4.compAction X ⟨x, hx'⟩ = MulAut.conj w := hw.symm
  rw [hc]
  ext q
  induction q using QuotientGroup.induction_on with
  | H z =>
    rw [Sec4.thetaQuotMulAut_mk, MulAut.conj_apply, MulAut.conj_apply,
      ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]

theorem kf148Field_holds : KF148Field := by
  intro Γ _ _ X n x y hn hX hfield hx3 hy hy3 hxy
  have hx : x ∈ Subgroup.normalizer (X : Set Γ) := hfield.mem_normalizer
  set σx := X.normalizerMonoidHom ⟨x, hx⟩ with hσx
  set σy := X.normalizerMonoidHom ⟨y, hy⟩ with hσy
  have hpow : ∀ (g : Γ) (hg : g ∈ Subgroup.normalizer (X : Set Γ)), g ^ 3 = 1 →
      X.normalizerMonoidHom ⟨g, hg⟩ ^ 3 = 1 := by
    intro g hg hg3
    rw [← map_pow]
    have : (⟨g, hg⟩ : Subgroup.normalizer (X : Set Γ)) ^ 3 = 1 := Subtype.ext (by simpa using hg3)
    rw [this, map_one]
  have hcomm : σx * σy = σy * σx := by
    rw [hσx, hσy, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hxy
  obtain ⟨k, hk⟩ := exists_isInnerAut_mul_pow_of_isoLThreePi148 hn hX (hpow x hx hx3)
    (hpow y hy hy3) hcomm (not_isInnerAut_of_inducesStdKind_field148 hfield hx)
  have hyx : y * x ^ k ∈ Subgroup.normalizer (X : Set Γ) :=
    mul_mem hy (pow_mem hx k)
  refine ⟨k, innerOn148_of_isInnerAut148 hyx ?_⟩
  have he : X.normalizerMonoidHom ⟨y * x ^ k, hyx⟩ = σy * σx ^ k := by
    rw [hσx, hσy, ← map_pow, ← map_mul]
    rfl
  rw [he]
  exact hk

end Field

end CFSG.RankThree.PartTwo.Sec14
