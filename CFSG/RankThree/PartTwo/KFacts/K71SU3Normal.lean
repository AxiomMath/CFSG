module

public import CFSG.RankThree.PartTwo.KFacts.K71SU3TwoFree
public import CFSG.RankThree.PartTwo.KFacts.K71Item83PSU3
import CFSG.RankThree.PartTwo.KFacts.AutKindsCentral

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.GH74.GLS.IVK (fixedField mem_fixedField_iff fixedField_apply)
open CFSG.ClassicalGroups.Unitary (IsUnitaryInvolution isUnitaryInvolution_unitaryInvolution)
open Matrix

theorem exists_pow_eq_of_pow_three_eq_one {Γ : Type*} [Group Γ] [Finite Γ] [IsCyclic Γ]
    {σ δ : Γ} (hσ : orderOf σ = 3) (hδ : δ ^ 3 = 1) : ∃ k : ℕ, k < 3 ∧ δ = σ ^ k := by
  classical
  have := Fintype.ofFinite Γ
  set S := Finset.univ.filter (fun x : Γ => x ^ 3 = 1) with hS
  have hle : S.card ≤ 3 := IsCyclic.card_pow_eq_one_le (by norm_num)
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  set T : Finset Γ := {1, σ, σ ^ 2} with hT
  have hσ1 : σ ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hσ; norm_num at hσ
  have hσ2 : σ ^ 2 ≠ 1 := fun h1 => by
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hσ] at this
    norm_num at this
  have hσσ : σ ≠ σ ^ 2 := fun h1 => by
    apply hσ1
    have h2 : σ * σ = σ * 1 := by rw [← sq, ← h1, mul_one]
    exact mul_left_cancel h2
  have hTc : T.card = 3 := by
    rw [hT, Finset.card_insert_of_notMem, Finset.card_pair hσσ]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hσ1, Ne.symm hσ2⟩
  have hTS : T ⊆ S := by
    intro x hx
    simp only [hT, Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact one_pow 3
    · exact hσ3
    · rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hσ3, one_pow]
  have hST : S = T := (Finset.eq_of_subset_of_card_le hTS (by rw [hTc]; exact hle)).symm
  have hδS : δ ∈ S := by simp [hS, hδ]
  rw [hST] at hδS
  simp only [hT, Finset.mem_insert, Finset.mem_singleton] at hδS
  rcases hδS with h | h | h
  · exact ⟨0, by norm_num, by rw [h, pow_zero]⟩
  · exact ⟨1, by norm_num, by rw [h, pow_one]⟩
  · exact ⟨2, by norm_num, h⟩

section NormalForm

variable {p f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def suDescend (h : UnitaryFieldData p f K) (hq : 2 < p ^ f) :
    MulAut (unitarySU p f K 3) →* MulAut (unitaryPSU h 3) :=
  (MulAut.congr (suCenterEquiv h hq)).toMonoidHom.comp (centerDescend _)

theorem suDescend_suConj (h : UnitaryFieldData p f K) (hq : 2 < p ^ f) (A : unitaryIsom3 h) :
    suDescend h hq (suConj h A) = psuConj h A :=
  congr_centerDescend_suConj h hq A

theorem suDescend_suField (h : UnitaryFieldData p f K) (hq : 2 < p ^ f) (σ : K ≃+* K) :
    suDescend h hq (suField h σ) = psuField h σ :=
  congr_centerDescend_suField h hq σ

theorem eq_of_suDescend_eq (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    {β γ : MulAut (unitarySU p f K 3)} (hβγ : suDescend h hq β = suDescend h hq γ) : β = γ := by
  have : Group.IsPerfect (unitarySU p f K 3) := isPerfect_unitarySU_three h hq
  have h' : centerDescend _ β = centerDescend _ γ := (MulAut.congr _).injective hβγ
  apply mulAut_eq_of_inv_mul_mem_center
  intro g
  have h1 := congrArg (fun τ : MulAut (unitarySU p f K 3 ⧸ Subgroup.center _) =>
    τ (g : unitarySU p f K 3 ⧸ Subgroup.center _)) h'
  simp only [centerDescend_mk] at h1
  exact QuotientGroup.eq.mp h1.symm

theorem exists_suConj_mul_suField_pow (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    {σ : K ≃+* K} (hσ : orderOf σ = 3) {β : MulAut (unitarySU p f K 3)} (hβ3 : β ^ 3 = 1)
    (hβσ : β * suField h σ = suField h σ * β) :
    ∃ (B : unitaryIsom3 h) (k : ℕ), k < 3 ∧ β = suConj h B * suField h σ ^ k ∧
      suConj h B * suField h σ = suField h σ * suConj h B ∧ suConj h B ^ 3 = 1 := by
  have := h.finite
  obtain ⟨B, δ, hBδ⟩ := exists_psuConj_mul_psuField hq (suDescend h hq β)
  have hδ3 : δ ^ 3 = 1 := by
    have h1 : (psuConj h B * psuField h δ) ^ 3 = 1 := by
      rw [← hBδ, ← map_pow, hβ3, map_one]
    rw [pow_succ, pow_two, psuConj_mul_psuField_mul, psuConj_mul_psuField_mul] at h1
    have h2 := (eq_one_of_psuConj_mul_psuField_eq_one _ _ h1).1
    rwa [← pow_two, ← pow_succ] at h2
  have hcyc : IsCyclic (K ≃+* K) := by
    have : Fact p.Prime := ⟨h.prime⟩
    exact (card_ringAut_and_isCyclic h.prime K (by rw [h.card])).2
  obtain ⟨k, hk3, rfl⟩ := exists_pow_eq_of_pow_three_eq_one hσ hδ3
  have hβ : β = suConj h B * suField h σ ^ k := by
    apply eq_of_suDescend_eq h hq
    rw [hBδ, map_mul, suDescend_suConj, map_pow (suDescend h hq), suDescend_suField, map_pow]
  refine ⟨B, k, hk3, hβ, ?_, ?_⟩
  · have hcomm : suField h σ ^ k * suField h σ = suField h σ * suField h σ ^ k := by
      rw [← pow_succ, ← pow_succ']
    have e : suConj h B = β * (suField h σ ^ k)⁻¹ := by rw [hβ, mul_inv_cancel_right]
    rw [e]
    calc β * (suField h σ ^ k)⁻¹ * suField h σ = β * suField h σ * (suField h σ ^ k)⁻¹ := by
          rw [mul_assoc, mul_assoc, ← (Commute.inv_left hcomm).eq]
      _ = suField h σ * (β * (suField h σ ^ k)⁻¹) := by rw [hβσ, mul_assoc]
  · have hcomm : Commute (suConj h B) (suField h σ ^ k) := by
      have h1 : suConj h B * suField h σ = suField h σ * suConj h B := by
        have e : suConj h B = β * (suField h σ ^ k)⁻¹ := by rw [hβ, mul_inv_cancel_right]
        have hcomm' : suField h σ ^ k * suField h σ = suField h σ * suField h σ ^ k := by
          rw [← pow_succ, ← pow_succ']
        rw [e]
        calc β * (suField h σ ^ k)⁻¹ * suField h σ =
            β * suField h σ * (suField h σ ^ k)⁻¹ := by
              rw [mul_assoc, mul_assoc, ← (Commute.inv_left hcomm').eq]
          _ = suField h σ * (β * (suField h σ ^ k)⁻¹) := by rw [hβσ, mul_assoc]
      exact (Commute.pow_right h1 k)
    have hσ3' : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
    have hσ3 : suField h σ ^ 3 = 1 := by
      rw [← map_pow, hσ3', map_one]
    have h1 := hβ3
    rw [hβ, hcomm.mul_pow, ← pow_mul, mul_comm k 3, pow_mul, hσ3, one_pow, mul_one] at h1
    exact h1

end NormalForm

section Scalars

variable {K : Type} [Field K]

theorem apply_eq_of_pow_three_eq_one {σ : K ≃+* K} (hσ3 : σ ^ 3 = 1) {w : K} (hw : w ^ 3 = 1) :
    σ w = w := by
  by_cases hw1 : w = 1
  · rw [hw1, map_one]
  have hw0 : w ≠ 0 := fun h0 => by rw [h0] at hw; norm_num at hw
  have hσw : σ w ^ 3 = 1 := by rw [← map_pow, hw, map_one]
  have hroot : (σ w - 1) * (σ w - w) * (σ w - w ^ 2) = 0 := by
    have hsum : 1 + w + w ^ 2 = 0 := by
      have h' : (w - 1) * (1 + w + w ^ 2) = 0 := by linear_combination hw
      exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 hw1)
    linear_combination hσw - hw + (-(σ w) ^ 2 + σ w * w) * hsum
  rcases mul_eq_zero.1 hroot with h12 | h3
  · rcases mul_eq_zero.1 h12 with h1 | h2
    · exfalso
      apply hw1
      apply σ.injective
      rw [map_one]
      exact sub_eq_zero.1 h1
    · exact sub_eq_zero.1 h2
  · exfalso
    have hw2 : σ w = w ^ 2 := sub_eq_zero.1 h3
    have hσ2 : σ (σ w) = w := by rw [hw2, map_pow, hw2, ← pow_mul,
      show w ^ (2 * 2) = w ^ 3 * w by ring, hw, one_mul]
    have hσ3w : σ (σ (σ w)) = w := by
      have := congrArg (fun τ : K ≃+* K => τ w) hσ3
      simpa [pow_succ] using this
    rw [hσ2, hw2] at hσ3w
    apply hw1
    have : w * w = w * 1 := by rw [← sq, hσ3w, mul_one]
    exact mul_left_cancel₀ hw0 this

theorem exists_cube_root_of_pow_three_eq_one [Finite K] (hK : Nat.card K = 64) {l : Kˣ}
    (hl : l ^ 3 = 1) : ∃ ν : Kˣ, ν ^ 3 = l ∧ ν ^ 9 = 1 := by
  have hcard : Nat.card Kˣ = 63 := by rw [Nat.card_units, hK]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hog : orderOf g = 63 := by
    rw [← hcard]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨ε, hε⟩ : ∃ ε : Kˣ, ε = g ^ 7 := ⟨_, rfl⟩
  have hε9 : orderOf ε = 9 := by
    rw [hε, orderOf_pow' g (by norm_num), hog]
    norm_num
  have hε3 : orderOf (ε ^ 3) = 3 := by
    rw [orderOf_pow' ε (by norm_num), hε9]
    norm_num
  obtain ⟨m, -, hm⟩ := exists_pow_eq_of_pow_three_eq_one hε3 hl
  refine ⟨ε ^ m, ?_, ?_⟩
  · rw [hm, ← pow_mul, ← pow_mul, mul_comm m 3]
  · rw [← pow_mul, mul_comm, pow_mul, ← hε9, pow_orderOf_eq_one, one_pow]

end Scalars

section Relations

variable {K : Type} [Field K] (h : UnitaryFieldData 2 3 K)

theorem two_lt_eight : 2 < 2 ^ 3 := by norm_num

theorem exists_glAut_eq_scalar_mul {σ : K ≃+* K} (B : unitaryIsom3 h)
    (hcomm : suConj h B * suField h σ = suField h σ * suConj h B) :
    ∃ z : Kˣ, h.norm (z : K) = 1 ∧
      glAut σ (B : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) z * B := by
  have h1 := congrArg (suDescend h two_lt_eight) hcomm
  rw [map_mul, map_mul, suDescend_suConj, suDescend_suField] at h1
  have h2 : psuConj h ⟨glAut σ B, glAut_mem_unitaryIsom3 σ B.2⟩ = psuConj h B := by
    rw [← psuField_mul_psuConj_mul_inv, ← h1, mul_inv_cancel_right]
  have h3 : psuConj h (⟨glAut σ B, glAut_mem_unitaryIsom3 σ B.2⟩ * B⁻¹) * psuField h 1 = 1 := by
    rw [map_one, mul_one, map_mul, h2, map_inv, mul_inv_cancel]
  obtain ⟨-, z, hz, hzB⟩ := eq_one_of_psuConj_mul_psuField_eq_one _ _ h3
  refine ⟨z, hz, ?_⟩
  rw [← hzB, Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]

theorem exists_pow_three_eq_scalar (B : unitaryIsom3 h) (hB3 : suConj h B ^ 3 = 1) :
    ∃ l : Kˣ, h.norm (l : K) = 1 ∧
      (B : GL (Fin 3) K) ^ 3 = GeneralLinearGroup.scalar (Fin 3) l := by
  have h1 := congrArg (suDescend h two_lt_eight) hB3
  rw [map_pow, suDescend_suConj, map_one, ← map_pow] at h1
  have h3 : psuConj h (B ^ 3) * psuField h 1 = 1 := by rw [map_one, mul_one, h1]
  obtain ⟨-, l, hl, hlB⟩ := eq_one_of_psuConj_mul_psuField_eq_one _ _ h3
  exact ⟨l, hl, by rw [← hlB, Subgroup.coe_pow]⟩

theorem norm_eq_pow_nine (x : K) : h.norm x = x ^ 9 := by
  rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply]
  ring

end Relations

section TypeTwo

variable {K : Type} [Field K] (h : UnitaryFieldData 2 3 K)

theorem trace_map_ringHom {k L : Type*} [Field k] [Field L] (φ : k →+* L)
    (M : Matrix (Fin 3) (Fin 3) k) : (M.map φ).trace = φ M.trace := by
  simp [Matrix.trace, Fin.sum_univ_three]

theorem exists_fixed_commuting_of_trace_ne_zero {σ : K ≃+* K} (hσ : orderOf σ = 3)
    {y : GL (Fin 3) K} (hyU : y ∈ unitaryIsom3 h) (hy3 : y ^ 3 = 1) (hyσ : glAut σ y = y)
    (htr : (y : Matrix (Fin 3) (Fin 3) K).trace ≠ 0)
    (hys : ∀ c : K, (y : Matrix (Fin 3) (Fin 3) K) ≠ c • 1) :
    ∃ x : unitarySU 2 3 K 3, x ^ 3 = 1 ∧
      (∀ c : K, ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ c • 1) ∧
      suField h σ x = x ∧ y * (x : GL (Fin 3) K) = (x : GL (Fin 3) K) * y := by
  have := h.finite
  have : CharP K 2 := h.charP
  obtain ⟨f₀, hf, hf₀, hcard⟩ := exists_card_fixedField_of_orderOf_eq_three h hσ
  have hf1 : f₀ = 1 := by omega
  subst hf1
  set k := fixedField σ with hkdef
  have h₀ : UnitaryFieldData 2 1 k := ⟨Nat.prime_two, le_rfl, hcard⟩
  have hbar := bar_coe_fixedField h hf h₀
  have hk : PiField false 2 1 k := ⟨Nat.prime_two, le_rfl, by rw [hcard]; rfl⟩
  have : Finite k := hk.finite
  have : CharP k 2 := hk.charP
  have h2k : (2 : k) = 0 := CharTwo.two_eq_zero
  have hfix : ∀ i j, σ ((y : Matrix (Fin 3) (Fin 3) K) i j) = (y : Matrix (Fin 3) (Fin 3) K) i j :=
    fun i j => by
      have h1 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) i j) hyσ
      simpa [coe_glAut] using h1
  set y₀ : Matrix (Fin 3) (Fin 3) k := fun i j =>
    ⟨(y : Matrix (Fin 3) (Fin 3) K) i j, (mem_fixedField_iff σ _).mpr (hfix i j)⟩ with hy₀
  have hy₀map : y₀.map k.subtype = (y : Matrix (Fin 3) (Fin 3) K) := rfl
  have hmapinj : Function.Injective (fun M : Matrix (Fin 3) (Fin 3) k => M.map k.subtype) :=
    Matrix.map_injective k.subtype_injective
  have hy₀3 : y₀ ^ 3 = 1 := by
    apply hmapinj
    change (y₀ ^ 3).map k.subtype = (1 : Matrix (Fin 3) (Fin 3) k).map k.subtype
    rw [Matrix.map_pow, hy₀map, Matrix.map_one _ (map_zero _) (map_one _),
      ← Units.val_pow_eq_pow_val, hy3, Units.val_one]
  have hy₀u : (y₀.map h₀.bar)ᵀ * y₀ = 1 := by
    apply hmapinj
    change ((y₀.map h₀.bar)ᵀ * y₀).map k.subtype = (1 : Matrix (Fin 3) (Fin 3) k).map k.subtype
    rw [Matrix.map_mul, Matrix.transpose_map, ← map_subtype_map_bar h h₀ hbar, hy₀map,
      Matrix.map_one _ (map_zero _) (map_one _)]
    exact hyU
  have hy₀s : ∀ c : k, y₀ ≠ c • 1 := by
    intro c hc
    apply hys (c : K)
    rw [← hy₀map, hc]
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  have hy₀tr : y₀.trace ≠ 0 := by
    intro h0
    apply htr
    rw [← hy₀map, trace_map_ringHom, h0, map_zero]
  obtain ⟨τ, hτ3, hτ1⟩ := exists_primitive_cube_root hk
  have hτ0 : τ ≠ 0 := fun h0 => by rw [h0] at hτ3; norm_num at hτ3
  have hτsq : τ ^ 2 + τ + 1 = 0 := by
    have h' : (τ - 1) * (τ ^ 2 + τ + 1) = 0 := by linear_combination hτ3
    exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 hτ1)
  have h3k : (3 : k) ≠ 0 := by
    rw [show (3 : k) = 1 by linear_combination h2k]
    exact one_ne_zero
  obtain ⟨g, j, hg, hform⟩ := exists_normal_form hτ3 hτ1 h3k hy₀3 hy₀s
  have hgdet : g.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det g).mp hg).ne_zero
  have htrD : ∀ {D : Matrix (Fin 3) (Fin 3) k}, (τ ^ (j : ℕ) • y₀) * g = g * D →
      τ ^ (j : ℕ) * y₀.trace = D.trace := by
    intro D hD
    have hD' : τ ^ (j : ℕ) • y₀ = g * D * g⁻¹ := by
      rw [← hD, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det g).mp hg),
        Matrix.mul_one]
    rw [← smul_eq_mul, ← Matrix.trace_smul, hD', Matrix.trace_mul_comm, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det g).mp hg), Matrix.one_mul]
  obtain ⟨e, he, hD⟩ : ∃ e : ℕ, (e = 1 ∨ e = 2) ∧
      (τ ^ (j : ℕ) • y₀) * g = g * diagonal ![τ ^ e, 1, 1] := by
    rcases hform with hD | hD | hD
    · exfalso
      have h1 := htrD hD
      rw [Matrix.trace_diagonal, Fin.sum_univ_three] at h1
      change τ ^ (j : ℕ) * y₀.trace = τ + τ ^ 2 + 1 at h1
      rw [show τ + τ ^ 2 + 1 = τ ^ 2 + τ + 1 by ring, hτsq] at h1
      exact hy₀tr ((mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ hτ0))
    · exact ⟨1, Or.inl rfl, by rw [pow_one]; exact hD⟩
    · exact ⟨2, Or.inr rfl, hD⟩
  set c : k := (τ ^ (j : ℕ))⁻¹ with hc
  have hc0 : c ≠ 0 := inv_ne_zero (pow_ne_zero _ hτ0)
  set d : Fin 3 → k := fun i => c * ![τ ^ e, 1, 1] i with hd
  have hyg : y₀ * g = g * diagonal d := by
    have h1 : y₀ * g = c • (g * diagonal ![τ ^ e, 1, 1]) := by
      rw [← hD, Matrix.smul_mul, smul_smul, hc, inv_mul_cancel₀ (pow_ne_zero _ hτ0), one_smul]
    rw [h1, ← Matrix.mul_smul, ← Matrix.diagonal_smul]
    rfl
  set σk := CFSG.LieType.BorelTits.unitaryInvolution k 2 1 with hσkdef
  have hσk : IsUnitaryInvolution σk :=
    isUnitaryInvolution_unitaryInvolution (by rw [hcard]; norm_num)
  have hσkx : ∀ x : k, σk x = x ^ 2 := fun x => by
    rw [hσkdef, CFSG.LieType.BorelTits.unitaryInvolution_apply, pow_one]
  have hc3 : c ^ 3 = 1 := by
    rw [hc, inv_pow, ← pow_mul, mul_comm, pow_mul, hτ3, one_pow, inv_one]
  have hdσ : ∀ i, σk (d i) * d i = 1 := by
    have key : ∀ x : k, x ^ 3 = 1 → σk x * x = 1 := fun x hx => by rw [hσkx, ← pow_succ, hx]
    intro i
    apply key
    fin_cases i
    · change (c * τ ^ e) ^ 3 = 1
      rw [mul_pow, hc3, one_mul, ← pow_mul, mul_comm, pow_mul, hτ3, one_pow]
    · change (c * 1) ^ 3 = 1
      rw [mul_one, hc3]
    · change (c * 1) ^ 3 = 1
      rw [mul_one, hc3]
  have hτe1 : τ ^ e ≠ 1 := by
    rcases he with rfl | rfl
    · rw [pow_one]; exact hτ1
    · intro h1; exact hτ1 (by linear_combination hτ3 - τ * h1)
  have hdd : d 0 ≠ d 1 ∧ d 1 = d 2 := by
    refine ⟨fun h01 => hτe1 ?_, rfl⟩
    have h' : c * τ ^ e = c * 1 := h01
    exact mul_left_cancel₀ hc0 h'
  have hy₀u' : CFSG.LieType.Universal.Unitary.conjTr σk y₀ * y₀ = 1 := by
    rw [conjTr_unitaryInvolution_eq hk]
    exact hy₀u
  obtain ⟨g', hg'u, hyg'⟩ := exists_unitary_conj hσk hdσ (Or.inr hdd) hy₀u' hg hyg
  have hg' : IsUnit g' :=
    (Matrix.isUnit_iff_isUnit_det g').mpr (Matrix.isUnit_det_of_left_inverse hg'u)
  set G₀ : GL (Fin 3) k := hg'.unit with hG₀
  have hG₀v : (G₀ : Matrix (Fin 3) (Fin 3) k) = g' := IsUnit.unit_spec hg'
  have hG₀U : G₀ ∈ unitaryIsom3 h₀ := by
    rw [mem_unitaryIsom3, hG₀v, ← conjTr_unitaryInvolution_eq hk]
    exact hg'u
  set τu : kˣ := Units.mk0 τ hτ0 with hτu
  have hτu3 : τu ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hτ3,
    Units.val_one])
  set D₁ : GL (Fin 3) k := diag3 1 τu (τu ^ 2) with hD₁
  have hnorm3 : ∀ u : kˣ, u ^ 3 = 1 → u ^ (2 ^ 1 + 1) = 1 := fun u hu => by
    rw [show 2 ^ 1 + 1 = 3 by norm_num]; exact hu
  have hD₁SU : D₁ ∈ unitarySU 2 1 k 3 :=
    diag3_mem_unitarySU h₀ (hnorm3 1 (one_pow 3)) (hnorm3 τu hτu3)
      (hnorm3 _ (by rw [← pow_mul, mul_comm, pow_mul, hτu3, one_pow]))
      (by rw [one_mul, ← pow_succ', hτu3])
  set x₀ : GL (Fin 3) k := G₀ * D₁ * G₀⁻¹ with hx₀
  have hx₀SU : x₀ ∈ unitarySU 2 1 k 3 := conj_mem_unitarySU hG₀U hD₁SU
  have hD₁3 : D₁ ^ 3 = 1 := by
    rw [hD₁, diag3_pow, one_pow, hτu3, ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hτu3,
      one_pow, diag3_one]
  have hx₀3 : x₀ ^ 3 = 1 := by rw [hx₀, conj_pow, hD₁3, mul_one, mul_inv_cancel]
  have hDd : (G₀⁻¹ : GL (Fin 3) k) * y₀ * (G₀ : Matrix (Fin 3) (Fin 3) k) = diagonal d := by
    rw [Matrix.mul_assoc, hG₀v, hyg', ← Matrix.mul_assoc, ← hG₀v, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul]
  have hy₀eq : y₀ = (G₀ : Matrix (Fin 3) (Fin 3) k) * diagonal d * (G₀⁻¹ : GL (Fin 3) k) := by
    rw [← hDd, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.mul_one]
  have hcomm₀ : y₀ * (x₀ : Matrix (Fin 3) (Fin 3) k) = (x₀ : Matrix (Fin 3) (Fin 3) k) * y₀ := by
    have hdiag : diagonal d * (D₁ : Matrix (Fin 3) (Fin 3) k) =
        (D₁ : Matrix (Fin 3) (Fin 3) k) * diagonal d := by
      rw [hD₁, coe_diag3, diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1
      funext i
      exact mul_comm _ _
    have hinv' : ∀ M : Matrix (Fin 3) (Fin 3) k,
        ((G₀⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * ((G₀ : Matrix (Fin 3) (Fin 3) k) * M) =
          M := fun M => by
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    rw [hy₀eq, hx₀, Units.val_mul, Units.val_mul]
    calc (G₀ : Matrix (Fin 3) (Fin 3) k) * diagonal d * ((G₀⁻¹ : GL (Fin 3) k) :
          Matrix (Fin 3) (Fin 3) k) * (G₀ * D₁ * ((G₀⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k))
        = (G₀ : Matrix (Fin 3) (Fin 3) k) * (diagonal d * D₁) *
            ((G₀⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
          simp only [Matrix.mul_assoc, hinv']
      _ = (G₀ : Matrix (Fin 3) (Fin 3) k) * (D₁ * diagonal d) *
            ((G₀⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by rw [hdiag]
      _ = (G₀ * D₁ * ((G₀⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) *
            ((G₀ : Matrix (Fin 3) (Fin 3) k) * diagonal d *
              ((G₀⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) := by
          simp only [Matrix.mul_assoc, hinv']
  have hx₀s : ∀ c' : k, (x₀ : Matrix (Fin 3) (Fin 3) k) ≠ c' • 1 := by
    intro c' hc'
    have h1 : (D₁ : Matrix (Fin 3) (Fin 3) k) = c' • 1 := by
      have e1 : (D₁ : Matrix (Fin 3) (Fin 3) k) =
          ((G₀⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * x₀ * G₀ := by
        rw [hx₀, Units.val_mul, Units.val_mul]
        simp only [Matrix.mul_assoc]
        rw [← Units.val_mul G₀⁻¹ G₀, inv_mul_cancel, Units.val_one, Matrix.mul_one,
          ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
      rw [e1, hc', Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Units.val_mul,
        inv_mul_cancel, Units.val_one]
    have e0 := congrFun (congrFun h1 0) 0
    have e1 := congrFun (congrFun h1 1) 1
    rw [hD₁, coe_diag3] at e0 e1
    simp at e0 e1
    exact hτ1 (e1.trans e0.symm)
  set x : unitarySU 2 3 K 3 := suIncl h h₀ hbar ⟨x₀, hx₀SU⟩ with hxdef
  have hxcoe : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (x₀ : Matrix (Fin 3) (Fin 3) k).map k.subtype := by
    ext i j
    rw [hxdef, coe_suIncl_apply]
    rfl
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  · rw [hxdef, ← map_pow]
    have : (⟨x₀, hx₀SU⟩ : unitarySU 2 1 k 3) ^ 3 = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow]; exact hx₀3)
    rw [this, map_one]
  · intro c' hc'
    have hc'' : (x₀ : Matrix (Fin 3) (Fin 3) k).map k.subtype =
        ((x₀ : Matrix (Fin 3) (Fin 3) k) 0 0 • (1 : Matrix (Fin 3) (Fin 3) k)).map k.subtype := by
      rw [← hxcoe, hc']
      have h00 : ((x₀ : Matrix (Fin 3) (Fin 3) k) 0 0 : K) = c' := by
        have := congrFun (congrFun (hxcoe.symm.trans hc') 0) 0
        simpa using this
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [h00]
      · simp [Matrix.one_apply_ne hij]
    exact hx₀s _ (hmapinj hc'')
  · exact (mem_range_suIncl_iff h h₀ hbar x).1 ⟨_, rfl⟩
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, hxcoe, ← hy₀map, ← Matrix.map_mul, ← Matrix.map_mul, hcomm₀]

end TypeTwo

section Dichotomy

variable {K : Type} [Field K] (h : UnitaryFieldData 2 3 K)

theorem suConj_scalar_eq_one {c : Kˣ}
    (hc : GeneralLinearGroup.scalar (Fin 3) c ∈ unitaryIsom3 h) : suConj h ⟨_, hc⟩ = 1 := by
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [MulAut.one_apply, coe_suConj]
  change GeneralLinearGroup.scalar (Fin 3) c * (g : GL (Fin 3) K) *
    (GeneralLinearGroup.scalar (Fin 3) c)⁻¹ = g
  rw [← (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c (g : GL (Fin 3) K)).eq,
    mul_inv_cancel_right]

theorem matrix_map_pow_ringEquiv (σ : K ≃+* K) (M : Matrix (Fin 3) (Fin 3) K) (n : ℕ) :
    (M ^ n).map σ = (M.map σ) ^ n := by
  have h1 := map_pow σ.mapMatrix M n
  simpa [RingEquiv.mapMatrix_apply] using h1

theorem su38_dichotomy {σ : K ≃+* K} (hσ : orderOf σ = 3) (B : unitaryIsom3 h)
    (hcomm : suConj h B * suField h σ = suField h σ * suConj h B)
    (hB3 : suConj h B ^ 3 = 1) (hB1 : suConj h B ≠ 1) :
    (∃ w : unitarySU 2 3 K 3, w ^ 3 = 1 ∧
        (∀ c : K, ((w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ c • 1) ∧
        suConj h B = MulAut.conj w) ∨
    (∃ x : unitarySU 2 3 K 3, x ^ 3 = 1 ∧
        (∀ c : K, ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ c • 1) ∧
        suField h σ x = x ∧ suConj h B x = x) := by
  have := h.finite
  have : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hK64 : Nat.card K = 64 := by rw [h.card]; norm_num
  have hPi : PiField false 2 3 K := ⟨Nat.prime_two, by norm_num, by rw [h.card]; rfl⟩
  obtain ⟨z, hzn, hzB⟩ := exists_glAut_eq_scalar_mul h B hcomm
  obtain ⟨l, hln, hlB⟩ := exists_pow_three_eq_scalar h B hB3
  have hz0 : (z : K) ≠ 0 := z.ne_zero
  have hBm : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ 0 := fun h0 => by
    have := (B : GL (Fin 3) K).isUnit
    rw [Matrix.isUnit_iff_isUnit_det, h0, Matrix.det_zero] at this
    exact not_isUnit_zero this
  have hBσ : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ =
      (z : K) • ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [← coe_glAut, hzB, coe_scalar_mul]
  have hN : σ (σ (z : K)) * σ (z : K) * z = 1 := by
    have h1 : ((((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ).map σ).map σ =
        (σ (σ (z : K)) * σ (z : K) * z) • ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [hBσ, Matrix.map_smul' _ _ _ (map_mul σ), hBσ, smul_smul,
        Matrix.map_smul' _ _ _ (map_mul σ), hBσ, smul_smul, map_mul]
    have h2' : ((((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ).map σ).map σ =
        ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      ext i j
      have := congrArg (fun τ : K ≃+* K => τ (((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j))
        hσ3
      simpa [pow_succ] using this
    exact eq_one_of_smul_eq_self hBm (h1.symm.trans h2')
  have hz9 : (z : K) ^ 9 = 1 := by rw [← norm_eq_pow_nine h]; exact hzn
  have hz3 : (z : K) ^ 3 = 1 := by
    have hw : ((z : K) ^ 3) ^ 3 = 1 := by rw [← pow_mul]; exact hz9
    have hσw : σ ((z : K) ^ 3) = (z : K) ^ 3 := apply_eq_of_pow_three_eq_one hσ3 hw
    set ε : K := σ (z : K) * (z : K)⁻¹ with hε
    have hε3 : ε ^ 3 = 1 := by
      rw [hε, mul_pow, ← map_pow, hσw, inv_pow, mul_inv_cancel₀ (pow_ne_zero 3 hz0)]
    have hσε : σ ε = ε := apply_eq_of_pow_three_eq_one hσ3 hε3
    have hσz : σ (z : K) = z * ε := by rw [hε]; field_simp
    have hσσz : σ (σ (z : K)) = z * ε * ε := by rw [hσz, map_mul, hσε, hσz]
    rw [hσσz, hσz] at hN
    linear_combination hN - (z : K) ^ 3 * hε3
  have hlm : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = (l : K) • 1 := by
    rw [← Units.val_pow_eq_pow_val, hlB, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  have hσl : σ (l : K) = l := by
    have h1 : (((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3).map σ =
        ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 := by
      rw [matrix_map_pow_ringEquiv, hBσ, smul_pow, hz3, one_smul]
    rw [hlm, Matrix.map_smul' _ _ _ (map_mul σ), Matrix.map_one _ (map_zero σ) (map_one σ)] at h1
    have := congrFun (congrFun h1 0) 0
    simpa using this
  have hl3 : l ^ 3 = 1 := by
    obtain ⟨f₀, hf, -, hcard⟩ := exists_card_fixedField_of_orderOf_eq_three h hσ
    have hf1 : f₀ = 1 := by omega
    subst hf1
    have : Finite (fixedField σ) := Subtype.finite
    have : Fintype (fixedField σ) := Fintype.ofFinite _
    set lk : fixedField σ := ⟨l, (mem_fixedField_iff σ _).mpr hσl⟩
    have hlk0 : lk ≠ 0 := fun h0 => l.ne_zero (congrArg Subtype.val h0)
    have h1 := FiniteField.pow_card_sub_one_eq_one lk hlk0
    rw [← Nat.card_eq_fintype_card, hcard] at h1
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    have := congrArg Subtype.val h1
    simpa using this
  obtain ⟨ν, hν3, hν9⟩ := exists_cube_root_of_pow_three_eq_one hK64 hl3
  have hsU := scalar_mem_unitaryIsom3 h (c := ν⁻¹) (by
    rw [show 2 ^ 3 + 1 = 9 by norm_num, inv_pow, hν9, inv_one])
  set Y : unitaryIsom3 h := ⟨_, hsU⟩ * B with hY
  set y : GL (Fin 3) K := (Y : GL (Fin 3) K) with hydef
  have hyB : y = GeneralLinearGroup.scalar (Fin 3) ν⁻¹ * B := rfl
  have hYB : suConj h Y = suConj h B := by rw [hY, map_mul, suConj_scalar_eq_one h hsU, one_mul]
  have hym : (y : Matrix (Fin 3) (Fin 3) K) =
      ((ν⁻¹ : Kˣ) : K) • ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [hyB, coe_scalar_mul]
  have hy3 : y ^ 3 = 1 := by
    rw [hyB, (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ν⁻¹ (B : GL (Fin 3) K)).symm.mul_pow,
      hlB, ← map_pow, inv_pow, hν3]
    apply Units.ext
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.scalar_apply, diagonal_mul_diagonal, Units.val_one,
      ← diagonal_one]
    congr 1
    funext i
    simp
  have hys : ∀ c : K, (y : Matrix (Fin 3) (Fin 3) K) ≠ c • 1 := by
    intro c hc
    apply hB1
    rw [← hYB]
    refine MulEquiv.ext fun g => Subtype.ext ?_
    rw [MulAut.one_apply, coe_suConj]
    change y * (g : GL (Fin 3) K) * y⁻¹ = g
    have hc0 : c ≠ 0 := by
      intro h0
      have := y.isUnit
      rw [Matrix.isUnit_iff_isUnit_det, hc, h0, zero_smul, Matrix.det_zero] at this
      exact not_isUnit_zero this
    have hyc : y = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) := by
      apply Units.ext
      rw [hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
      rfl
    rw [hyc, ← (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar _ (g : GL (Fin 3) K)).eq,
      mul_inv_cancel_right]
  obtain ⟨τ, hτ3, hτ1⟩ := exists_primitive_cube_root hPi
  have hτ0 : τ ≠ 0 := fun h0 => by rw [h0] at hτ3; norm_num at hτ3
  have h3 : (3 : K) ≠ 0 := by
    rw [show (3 : K) = 1 by linear_combination h2]
    exact one_ne_zero
  have hy3m : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hy3, Units.val_one]
  obtain ⟨g, j, hg, hform⟩ := exists_normal_form hτ3 hτ1 h3 hy3m hys
  have hgdet : g.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det g).mp hg).ne_zero
  rcases hform with hD | hD2
  ·
    left
    have hdet : (y : Matrix (Fin 3) (Fin 3) K).det = 1 := by
      have h1 := congrArg Matrix.det hD
      rw [det_mul, det_mul, det_smul, Fintype.card_fin, ← pow_mul, mul_comm (j : ℕ) 3, pow_mul,
        hτ3, one_pow, one_mul, det_diagonal, Fin.prod_univ_three] at h1
      change y.det * g.det = g.det * (τ * τ ^ 2 * 1) at h1
      rw [mul_one, ← pow_succ', hτ3, mul_one, mul_comm] at h1
      exact mul_left_cancel₀ hgdet (h1.trans (mul_one _).symm)
    have hyU : y ∈ unitaryIsom3 h := Y.2
    have hySU : y ∈ unitarySU 2 3 K 3 := (mem_unitarySU_iff h).mpr ⟨hdet, hyU⟩
    refine ⟨⟨y, hySU⟩, Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hy3), hys, ?_⟩
    rw [← hYB]
    ext g'
    rfl
  ·
    right
    obtain ⟨e, -, hD⟩ : ∃ e : ℕ, (e = 1 ∨ e = 2) ∧
        (τ ^ (j : ℕ) • (y : Matrix (Fin 3) (Fin 3) K)) * g = g * diagonal ![τ ^ e, 1, 1] := by
      rcases hD2 with hD | hD
      · exact ⟨1, Or.inl rfl, by rw [pow_one]; exact hD⟩
      · exact ⟨2, Or.inr rfl, hD⟩
    have hgu := (Matrix.isUnit_iff_isUnit_det g).mp hg
    have htrD : τ ^ (j : ℕ) * (y : Matrix (Fin 3) (Fin 3) K).trace = τ ^ e := by
      have hD' : τ ^ (j : ℕ) • (y : Matrix (Fin 3) (Fin 3) K) =
          g * diagonal ![τ ^ e, 1, 1] * g⁻¹ := by
        rw [← hD, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hgu, Matrix.mul_one]
      rw [← smul_eq_mul, ← Matrix.trace_smul, hD', Matrix.trace_mul_comm, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hgu, Matrix.one_mul, Matrix.trace_diagonal, Fin.sum_univ_three]
      change τ ^ e + 1 + 1 = τ ^ e
      rw [add_assoc, CharTwo.add_self_eq_zero (1 : K), add_zero]
    have htr : (y : Matrix (Fin 3) (Fin 3) K).trace = (τ ^ (j : ℕ))⁻¹ * τ ^ e := by
      rw [← htrD, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hτ0), one_mul]
    have htr0 : (y : Matrix (Fin 3) (Fin 3) K).trace ≠ 0 := by
      rw [htr]
      exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ hτ0)) (pow_ne_zero _ hτ0)
    have htr3 : (y : Matrix (Fin 3) (Fin 3) K).trace ^ 3 = 1 := by
      rw [htr, mul_pow, inv_pow, ← pow_mul, mul_comm (j : ℕ) 3, pow_mul, hτ3, one_pow, inv_one,
        one_mul, ← pow_mul, mul_comm e 3, pow_mul, hτ3, one_pow]
    have hσtr : σ (y : Matrix (Fin 3) (Fin 3) K).trace = (y : Matrix (Fin 3) (Fin 3) K).trace :=
      apply_eq_of_pow_three_eq_one hσ3 htr3
    set z' : K := σ ((ν⁻¹ : Kˣ) : K) * z * ν with hz'
    have hν0 : (ν : K) ≠ 0 := ν.ne_zero
    have hyσm : (y : Matrix (Fin 3) (Fin 3) K).map σ = z' • (y : Matrix (Fin 3) (Fin 3) K) := by
      rw [hym, Matrix.map_smul' _ _ _ (map_mul σ), hBσ, smul_smul, smul_smul]
      congr 1
      rw [hz', Units.val_inv_eq_inv_val, mul_assoc (σ (ν : K)⁻¹ * (z : K)), mul_inv_cancel₀ hν0,
        mul_one, map_inv₀]
    have htrσ : σ (y : Matrix (Fin 3) (Fin 3) K).trace =
        z' * (y : Matrix (Fin 3) (Fin 3) K).trace := by
      have h1 := trace_map_ringHom (σ : K →+* K) (y : Matrix (Fin 3) (Fin 3) K)
      change ((y : Matrix (Fin 3) (Fin 3) K).map σ).trace = σ (y : Matrix (Fin 3) (Fin 3) K).trace
        at h1
      rw [← h1, hyσm, Matrix.trace_smul, smul_eq_mul]
    have hz'1 : z' = 1 := by
      have h1 : z' * (y : Matrix (Fin 3) (Fin 3) K).trace = (y : Matrix (Fin 3) (Fin 3) K).trace :=
        htrσ.symm.trans hσtr
      exact (mul_left_eq_self₀.1 h1).resolve_right htr0
    have hyσ : glAut σ y = y := by
      apply Units.ext
      rw [coe_glAut, hyσm, hz'1, one_smul]
    obtain ⟨x, hx3, hxs, hxσ, hxy⟩ :=
      exists_fixed_commuting_of_trace_ne_zero h hσ Y.2 hy3 hyσ htr0 hys
    refine ⟨x, hx3, hxs, hxσ, ?_⟩
    rw [← hYB]
    apply Subtype.ext
    rw [coe_suConj]
    change y * (x : GL (Fin 3) K) * y⁻¹ = x
    rw [hxy, mul_inv_cancel_right]

end Dichotomy

end CFSG.RankThree.PartTwo.KFacts
