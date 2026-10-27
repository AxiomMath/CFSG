module

public import CFSG.RankThree.PartOne.U5K.Kf.Core
public import CFSG.RankThree.PartOne.U5K.Kf.Comb
public import CFSG.RankThree.PartOne.U5K.Kf.Fixed2

public section

namespace CFSG.RankThree.PartOne.U5K.Kf

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ} [Fact p.Prime]

theorem ZetaData.minimal_support (Z : ZetaData h p) {Ã : Subgroup (VM p)}
    (hG : ∀ i j : Fin 5, i ≠ j → ∃ a : Fin 5 → ZMod p, Multiplicative.ofAdd a ∈ Ã ∧ a i ≠ a j)
    (R : Submodule K (Fin 5 → K)) (hR : R ≠ ⊥)
    (hinv : ∀ a : Fin 5 → ZMod p, Multiplicative.ofAdd a ∈ Ã → ∀ r ∈ R,
      (diagonal fun s => zp Z.ζ (a s)) *ᵥ r ∈ R)
    (hiso : ∀ r ∈ R, gramForm h (1 : Matrix (Fin 5) (Fin 5) K) r r = 0) : False := by
  classical
  obtain ⟨r₀, hr₀, hr₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hR
  have key : ∀ n : ℕ, ∀ r ∈ R, r ≠ 0 → (Finset.univ.filter fun s => r s ≠ 0).card = n →
      False := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro r hr hr0 hn
      obtain ⟨i, hi⟩ : ∃ i, r i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hr0 (funext hcon)
      by_cases hj : ∃ j, j ≠ i ∧ r j ≠ 0
      · obtain ⟨j, hji, hjr⟩ := hj
        obtain ⟨a, ha, hai⟩ := hG i j (Ne.symm hji)
        set r' : Fin 5 → K := (diagonal fun s => zp Z.ζ (a s)) *ᵥ r - zp Z.ζ (a i) • r with hr'
        have hr'R : r' ∈ R := R.sub_mem (hinv a ha r hr) (R.smul_mem _ hr)
        have hr's : ∀ s, r' s = (zp Z.ζ (a s) - zp Z.ζ (a i)) * r s := by
          intro s
          simp [hr', Matrix.mulVec_diagonal, sub_mul]
        have hr'j : r' j ≠ 0 := by
          rw [hr's j]
          refine mul_ne_zero (sub_ne_zero.2 fun hh => hai ?_) hjr
          exact ((zp_inj Z.prim).1 hh).symm
        refine ih _ ?_ r' hr'R (fun hz => hr'j (by rw [hz]; rfl)) rfl
        rw [← hn]
        apply Finset.card_lt_card
        refine ⟨fun s hs => ?_, fun hsub => ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
          intro hrs
          exact hs (by rw [hr's s, hrs, mul_zero])
        · have hiin : i ∈ Finset.univ.filter fun s => r s ≠ 0 := by simp [hi]
          have := hsub hiin
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
          apply this
          rw [hr's i, sub_self, zero_mul]
      · push Not at hj
        have hform : gramForm h (1 : Matrix (Fin 5) (Fin 5) K) r r = h.bar (r i) * r i := by
          rw [gramForm_apply, Matrix.one_mulVec]
          unfold dotProduct
          rw [Finset.sum_eq_single i]
          · intro s _ hs
            rw [hj s hs]
            simp
          · intro hi'
            exact absurd (Finset.mem_univ i) hi'
        have := hiso r hr
        rw [hform] at this
        exact mul_ne_zero ((map_ne_zero h.bar).2 hi) hi this
  exact key _ r₀ hr₀ hr₀ne rfl

@[expose] def sigmaSet (h : UnitaryFieldData 2 f K)
    (Q : Subgroup (MulAut (primeFormP h (idGram K 5)))) :
    Set (primeFormUnitary h (idGram K 5)) :=
  {y | y * y = 1 ∧ primeFormConjHom h (idGram K 5) y ∈ Q ∧
    ∀ q ∈ Q, primeFormConjHom h (idGram K 5) y * q = q * primeFormConjHom h (idGram K 5) y}

theorem ZetaData.sigma_comm (Z : ZetaData h p) {Q : Subgroup (MulAut (primeFormP h (idGram K 5)))}
    {y₁ y₂ : primeFormUnitary h (idGram K 5)} (h₁ : y₁ ∈ sigmaSet h Q) (h₂ : y₂ ∈ sigmaSet h Q) :
    y₁ * y₂ = y₂ * y₁ := by
  have hcomm : primeFormConjHom h (idGram K 5) (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) = 1 := by
    have := h₁.2.2 _ h₂.2.1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, this]
    group
  obtain ⟨κ, hκq, hκ⟩ := (Z.conj_eq_one_iff _).1 hcomm
  have hκ' : (y₁ : GL (Fin 5) K) * y₂ * (y₁ : GL (Fin 5) K)⁻¹ * (y₂ : GL (Fin 5) K)⁻¹ =
      GeneralLinearGroup.scalar (Fin 5) κ := by simpa using hκ
  have hy2 : (y₂ : GL (Fin 5) K) ^ 2 = GeneralLinearGroup.scalar (Fin 5) 1 := by
    have h' := congrArg (fun g : primeFormUnitary h (idGram K 5) => (g : GL (Fin 5) K)) h₂.1
    simp only [Subgroup.coe_mul, Subgroup.coe_one] at h'
    rw [pow_two, h', map_one]
  have hκ2 : κ ^ 2 = 1 := scalar_commutator_pow_p (p := 2) hκ' hy2
  have hodd : Odd (2 ^ f + 1) :=
    (Nat.even_pow.2 ⟨even_two, by have := h.one_le; omega⟩).add_one
  have hκ1 : κ = 1 := by
    have h1 : orderOf κ ∣ 2 := orderOf_dvd_of_pow_eq_one hκ2
    have h2 : orderOf κ ∣ 2 ^ f + 1 := orderOf_dvd_of_pow_eq_one hκq
    have h3 : orderOf κ ∣ Nat.gcd 2 (2 ^ f + 1) := Nat.dvd_gcd h1 h2
    rw [(Nat.coprime_two_left.2 hodd).gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3
    exact h3
  rw [hκ1, map_one] at hκ'
  apply Subtype.ext
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hκ'
  exact hκ'

theorem sigma_conj {Q : Subgroup (MulAut (primeFormP h (idGram K 5)))}
    {D y : primeFormUnitary h (idGram K 5)}
    (hD : primeFormConjHom h (idGram K 5) D ∈ Subgroup.normalizer (Q : Set _))
    (hy : y ∈ sigmaSet h Q) : D * y * D⁻¹ ∈ sigmaSet h Q := by
  refine ⟨?_, ?_, ?_⟩
  · calc D * y * D⁻¹ * (D * y * D⁻¹) = D * (y * y) * D⁻¹ := by group
      _ = 1 := by rw [hy.1]; group
  · rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 hD _).1 hy.2.1
  · intro q hq
    have hq' : (primeFormConjHom h (idGram K 5) D)⁻¹ * q *
        primeFormConjHom h (idGram K 5) D ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hD) q).1 hq
      simpa using this
    have := hy.2.2 _ hq'
    rw [map_mul, map_mul, map_inv]
    calc primeFormConjHom h (idGram K 5) D * primeFormConjHom h (idGram K 5) y *
          (primeFormConjHom h (idGram K 5) D)⁻¹ * q
        = primeFormConjHom h (idGram K 5) D * (primeFormConjHom h (idGram K 5) y *
            ((primeFormConjHom h (idGram K 5) D)⁻¹ * q * primeFormConjHom h (idGram K 5) D)) *
            (primeFormConjHom h (idGram K 5) D)⁻¹ := by group
      _ = primeFormConjHom h (idGram K 5) D * (((primeFormConjHom h (idGram K 5) D)⁻¹ * q *
            primeFormConjHom h (idGram K 5) D) * primeFormConjHom h (idGram K 5) y) *
            (primeFormConjHom h (idGram K 5) D)⁻¹ := by rw [this]
      _ = q * (primeFormConjHom h (idGram K 5) D * primeFormConjHom h (idGram K 5) y *
            (primeFormConjHom h (idGram K 5) D)⁻¹) := by group

theorem ZetaData.no_inner_core (Z : ZetaData h p) {Ã : Subgroup (VM p)}
    (hG : ∀ i j : Fin 5, i ≠ j → ∃ a : Fin 5 → ZMod p, Multiplicative.ofAdd a ∈ Ã ∧ a i ≠ a j)
    (Q : Subgroup (MulAut (primeFormP h (idGram K 5)))) (hQ2 : IsPGroup 2 Q) (hQne : Q ≠ ⊥)
    (hQinn : Q ≤ (MulAut.conj : primeFormP h (idGram K 5) →*
      MulAut (primeFormP h (idGram K 5))).range)
    (hQn : ∀ a : Fin 5 → ZMod p, Multiplicative.ofAdd a ∈ Ã →
      primeFormConjHom h (idGram K 5) (Z.dgU a) ∈ Subgroup.normalizer (Q : Set _)) : False := by
  classical
  have hfinK := h.finite
  have hcharK : CharP K 2 := h.charP
  obtain ⟨q, hqQ, hq1, hq2, hqc⟩ := exists_central_involution hQ2 hQne
  obtain ⟨y₀, hy₀2, hy₀q⟩ := Z.exists_lift_involution (hQinn hqQ) hq2
  have hy₀ : y₀ ∈ sigmaSet h Q := ⟨hy₀2, hy₀q ▸ hqQ, fun q' hq' => hy₀q ▸ hqc q' hq'⟩
  have hy₀ne : y₀ ≠ 1 := by
    intro h1
    rw [h1, map_one] at hy₀q
    exact hq1 hy₀q.symm
  let toM : primeFormUnitary h (idGram K 5) → Matrix (Fin 5) (Fin 5) K :=
    fun y => ((y : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
  have hfin : (toM '' sigmaSet h Q).Finite := Set.toFinite _
  set S : Finset (Matrix (Fin 5) (Fin 5) K) := hfin.toFinset with hS
  have hmemS : ∀ A, A ∈ S ↔ ∃ y ∈ sigmaSet h Q, toM y = A := by
    intro A
    rw [hS, Set.Finite.mem_toFinset]
    rfl
  have hcomm : ∀ A ∈ S, ∀ B ∈ S, A * B = B * A := by
    intro A hA B hB
    obtain ⟨y₁, h₁, rfl⟩ := (hmemS A).1 hA
    obtain ⟨y₂, h₂, rfl⟩ := (hmemS B).1 hB
    have := congrArg toM (Z.sigma_comm h₁ h₂)
    simpa [toM] using this
  have hsq : ∀ A ∈ S, A * A = 1 := by
    intro A hA
    obtain ⟨y, hy, rfl⟩ := (hmemS A).1 hA
    have := congrArg toM hy.1
    simpa [toM] using this
  have hunit : ∀ A ∈ S, ∀ u v : Fin 5 → K,
      gramForm h (1 : Matrix (Fin 5) (Fin 5) K) (A *ᵥ u) (A *ᵥ v) =
        gramForm h (1 : Matrix (Fin 5) (Fin 5) K) u v := by
    intro A hA
    obtain ⟨y, -, rfl⟩ := (hmemS A).1 hA
    refine (gramForm_isometry_iff h 1 _).2 ?_
    simpa [idGram] using mem_primeFormUnitary.1 y.2
  set W₀ : Submodule K (Fin 5 → K) :=
    Submodule.span K {w | ∃ A ∈ S, ∃ v : Fin 5 → K, w = A *ᵥ v - v} with hW₀
  have hW₀ne : W₀ ≠ ⊥ := by
    have hA₀ : toM y₀ ∈ S := (hmemS _).2 ⟨y₀, hy₀, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v : Fin 5 → K, toM y₀ *ᵥ v ≠ v := by
      by_contra hcon
      push Not at hcon
      apply hy₀ne
      apply Subtype.ext
      apply Units.ext
      ext i j
      have := congrFun (hcon (Pi.single j 1)) i
      simpa [toM, Matrix.mulVec_single, Pi.single_apply, Matrix.one_apply] using this
    refine (Submodule.ne_bot_iff _).2 ⟨toM y₀ *ᵥ v - v, Submodule.subset_span ⟨_, hA₀, v, rfl⟩, ?_⟩
    exact sub_ne_zero.2 hv
  have hinv₁ : ∀ A ∈ S, ∀ w ∈ W₀, A *ᵥ w ∈ W₀ := by
    intro A hA w hw
    refine Submodule.span_induction (p := fun w _ => A *ᵥ w ∈ W₀) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨B, hB, v, rfl⟩
      have : A *ᵥ (B *ᵥ v - v) = B *ᵥ (A *ᵥ v) - A *ᵥ v := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm A hA B hB]
      rw [this]
      exact Submodule.subset_span ⟨B, hB, A *ᵥ v, rfl⟩
    · simp
    · intro x y _ _ hx hy
      rw [Matrix.mulVec_add]
      exact W₀.add_mem hx hy
    · intro c x _ hx
      rw [Matrix.mulVec_smul]
      exact W₀.smul_mem c hx
  obtain ⟨w₀, hw₀W, hw₀ne, hw₀fix⟩ := exists_common_fixed S hcomm hsq W₀ hW₀ne hinv₁
  let Fix : Submodule K (Fin 5 → K) :=
    { carrier := {w | ∀ A ∈ S, A *ᵥ w = w}
      add_mem' := by
        intro x y hx hy A hA
        rw [Matrix.mulVec_add, hx A hA, hy A hA]
      zero_mem' := by intro A hA; simp
      smul_mem' := by
        intro c x hx A hA
        rw [Matrix.mulVec_smul, hx A hA] }
  set R : Submodule K (Fin 5 → K) := W₀ ⊓ Fix with hR
  have hRne : R ≠ ⊥ :=
    (Submodule.ne_bot_iff _).2 ⟨w₀, ⟨hw₀W, hw₀fix⟩, hw₀ne⟩
  have hconj : ∀ a : Fin 5 → ZMod p, Multiplicative.ofAdd a ∈ Ã → ∀ A ∈ S,
      (diagonal fun s => zp Z.ζ (a s)) * A * (diagonal fun s => zp Z.ζ (-(a s))) ∈ S := by
    intro a ha A hA
    obtain ⟨y, hy, rfl⟩ := (hmemS A).1 hA
    refine (hmemS _).2 ⟨Z.dgU a * y * (Z.dgU a)⁻¹, sigma_conj (hQn a ha) hy, ?_⟩
    have hinv : ((((Z.dgU a)⁻¹ : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K) = diagonal fun s => zp Z.ζ (-(a s)) := rfl
    simp only [toM, Subgroup.coe_mul, Units.val_mul, hinv, ZetaData.dgU_val]
  have hDD : ∀ a : Fin 5 → ZMod p, (diagonal fun s => zp Z.ζ (a s)) *
      (diagonal fun s => zp Z.ζ (-(a s))) = (1 : Matrix (Fin 5) (Fin 5) K) := fun a =>
    Z.dg_mul_neg a
  have hDD' : ∀ a : Fin 5 → ZMod p, (diagonal fun s => zp Z.ζ (-(a s))) *
      (diagonal fun s => zp Z.ζ (a s)) = (1 : Matrix (Fin 5) (Fin 5) K) := fun a =>
    Z.dg_neg_mul a
  have hRinv : ∀ a : Fin 5 → ZMod p, Multiplicative.ofAdd a ∈ Ã → ∀ r ∈ R,
      (diagonal fun s => zp Z.ζ (a s)) *ᵥ r ∈ R := by
    intro a ha r hr
    obtain ⟨hrW, hrF⟩ := hr
    set Dm : Matrix (Fin 5) (Fin 5) K := diagonal fun s => zp Z.ζ (a s) with hDm
    set Dm' : Matrix (Fin 5) (Fin 5) K := diagonal fun s => zp Z.ζ (-(a s)) with hDm'
    have h1 : Dm * Dm' = 1 := hDD a
    have h2 : Dm' * Dm = 1 := hDD' a
    refine ⟨?_, ?_⟩
    · refine Submodule.span_induction (p := fun w _ => Dm *ᵥ w ∈ W₀) ?_ ?_ ?_ ?_ hrW
      · rintro _ ⟨B, hB, v, rfl⟩
        have e1 : Dm * B * Dm' * Dm = Dm * B := by
          rw [Matrix.mul_assoc (Dm * B), h2, Matrix.mul_one]
        have : Dm *ᵥ (B *ᵥ v - v) = (Dm * B * Dm') *ᵥ (Dm *ᵥ v) - Dm *ᵥ v := by
          rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e1]
        rw [this]
        exact Submodule.subset_span ⟨_, hconj a ha B hB, _, rfl⟩
      · simp
      · intro x y _ _ hx hy
        rw [Matrix.mulVec_add]
        exact W₀.add_mem hx hy
      · intro c x _ hx
        rw [Matrix.mulVec_smul]
        exact W₀.smul_mem c hx
    · intro A hA
      have hc : Dm' * A * Dm ∈ S := by
        obtain ⟨y, hy, rfl⟩ := (hmemS A).1 hA
        refine (hmemS _).2 ⟨(Z.dgU a)⁻¹ * y * ((Z.dgU a)⁻¹)⁻¹, sigma_conj ?_ hy, ?_⟩
        · rw [map_inv]
          exact (Subgroup.normalizer _).inv_mem (hQn a ha)
        · have hinv : ((((Z.dgU a)⁻¹ : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) :
              Matrix (Fin 5) (Fin 5) K) = diagonal fun s => zp Z.ζ (-(a s)) := rfl
          simp only [toM, Subgroup.coe_mul, Units.val_mul, inv_inv, hinv, ZetaData.dgU_val, hDm,
            hDm']
      have e : A *ᵥ (Dm *ᵥ r) = Dm *ᵥ ((Dm' * A * Dm) *ᵥ r) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
          h1, Matrix.one_mul]
      rw [e, hrF _ hc]
  have hiso : ∀ r ∈ R, gramForm h (1 : Matrix (Fin 5) (Fin 5) K) r r = 0 := by
    intro r hr
    obtain ⟨hrW, hrF⟩ := hr
    have key : ∀ w ∈ W₀, gramForm h (1 : Matrix (Fin 5) (Fin 5) K) r w = 0 := by
      intro w hw
      refine Submodule.span_induction (p := fun w _ =>
        gramForm h (1 : Matrix (Fin 5) (Fin 5) K) r w = 0) ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨B, hB, v, rfl⟩
        have h1 := hunit B hB r v
        rw [hrF B hB] at h1
        rw [map_sub, h1, sub_self]
      · exact map_zero _
      · intro x y _ _ hx hy
        rw [map_add, hx, hy, add_zero]
      · intro c x _ hx
        rw [map_smul, hx, smul_zero]
    exact key r hrW
  exact Z.minimal_support hG R hRne hRinv hiso

end CFSG.RankThree.PartOne.U5K.Kf
