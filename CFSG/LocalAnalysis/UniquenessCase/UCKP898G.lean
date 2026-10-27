module

public import CFSG.LocalAnalysis.UniquenessCase.UCKP898A
public import CFSG.LocalAnalysis.UniquenessCase.UCKP898B
public import CFSG.LocalAnalysis.UniquenessCase.UCKP898C
public import CFSG.LocalAnalysis.UniquenessCase.UCKP898E
public import CFSG.LocalAnalysis.UniquenessCase.UCKPCenter

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Matrix Subgroup CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj

@[expose] def U3Fix3FieldTorus : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSU3 X 21 → ∀ α : MulAut X, α ^ 7 = 1 →
    α ∉ (MulAut.conj : X →* MulAut X).range →
      ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ (∀ e ∈ E, α e = e) ∧
        ∀ p : ℕ, p.Prime → p ∣ 2 ^ 21 + 1 → p ≠ 3 →
          ∃ P : Subgroup X, IsElemAbelian p P ∧ Nat.card P = p ^ 2 ∧ P ≤ centralizer (E : Set X)

section Generic

variable {G : Type*} [Group G]

theorem mul_comm_of_lift_of_coprime (hZ : Nat.card (center G) ∣ 3) {x y : G} {q : ℕ}
    (hq : q.Coprime 3) (hxq : x ^ q = 1)
    (hxy : (QuotientGroup.mk x : G ⧸ center G) * QuotientGroup.mk y =
      QuotientGroup.mk y * QuotientGroup.mk x) : x * y = y * x := by
  obtain ⟨c, hcdef⟩ : ∃ c : G, c = x * y * x⁻¹ * y⁻¹ := ⟨_, rfl⟩
  have hcZ : c ∈ center G := by
    refine (QuotientGroup.eq_one_iff _).1 ?_
    rw [hcdef, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, hxy]
    group
  have hconj : MulAut.conj x y = c * y := by
    rw [MulAut.conj_apply, hcdef]
    group
  have hconjc : MulAut.conj x c = c := by
    rw [MulAut.conj_apply, Subgroup.mem_center_iff.1 hcZ x, mul_inv_cancel_right]
  have key : ∀ k : ℕ, (MulAut.conj x ^ k) y = c ^ k * y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hconjc, hconj, pow_succ, mul_assoc]
  have h1 := key q
  rw [← map_pow, hxq, map_one, MulAut.one_apply] at h1
  have hcq : c ^ q = 1 := by
    have h2 : c ^ q * y = 1 * y := by rw [← h1, one_mul]
    exact mul_right_cancel h2
  have hc1 : c = 1 := eq_one_of_mem_center_of_pow_eq_one hZ hcZ hq hcq
  rw [hc1] at hcdef
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [← hcdef, one_mul]

theorem exists_lift_orderOf_prime [Finite G] (hZ : Nat.card (center G) ∣ 3) {q : ℕ} (hq : q.Prime)
    (hq3 : q ≠ 3) {zb : G ⧸ center G} (hzb : orderOf zb = q) :
    ∃ z : G, orderOf z = q ∧ (QuotientGroup.mk z : G ⧸ center G) = zb := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective zb
  have hzq : (QuotientGroup.mk x : G ⧸ center G) ^ q = 1 := hzb ▸ pow_orderOf_eq_one _
  have hxq : x ^ q ∈ center G :=
    (QuotientGroup.eq_one_iff _).1 (by rw [QuotientGroup.mk_pow]; exact hzq)
  have hxq3 : (x ^ q) ^ 3 = 1 := pow_three_eq_one_of_mem_center hZ hxq
  have hcop : Nat.Coprime 3 q := (Nat.coprime_primes Nat.prime_three hq).2 (Ne.symm hq3)
  obtain ⟨u, hu3, huq⟩ := Nat.chineseRemainder hcop 0 1
  obtain ⟨z, hzx, hzq1⟩ : ∃ z : G,
      (QuotientGroup.mk z : G ⧸ center G) = QuotientGroup.mk x ∧ z ^ q = 1 := by
    refine ⟨x ^ u, ?_, ?_⟩
    · have h1 : u % q = 1 := by
        have h2 : 1 % q = 1 := Nat.mod_eq_of_lt hq.one_lt
        exact (show u % q = 1 % q from huq).trans h2
      rw [QuotientGroup.mk_pow, pow_eq_pow_mod u hzq, h1, pow_one]
    · obtain ⟨k, hk⟩ := (Nat.modEq_zero_iff_dvd).1 hu3
      rw [pow_right_comm, hk, pow_mul, hxq3, one_pow]
  have hz1 : z ≠ 1 := by
    intro h
    have h1 : (QuotientGroup.mk x : G ⧸ center G) = 1 := by rw [← hzx, h, QuotientGroup.mk_one]
    rw [h1, orderOf_one] at hzb
    exact hq.ne_one hzb.symm
  exact ⟨z, orderOf_eq_prime hzq1 hz1, hzx⟩

theorem closure_pair_isElemAbelian_card_of_prime [Finite G] {q : ℕ} (hq : q.Prime) {a b : G}
    (ha : orderOf a = q) (hb : orderOf b = q) (hab : a * b = b * a) (hn : b ∉ zpowers a) :
    IsElemAbelian q (closure ({a, b} : Set G)) ∧ Nat.card (closure ({a, b} : Set G)) = q ^ 2 := by
  have haq : a ^ q = 1 := ha ▸ pow_orderOf_eq_one a
  have hbq : b ^ q = 1 := hb ▸ pow_orderOf_eq_one b
  refine ⟨IsElemAbelian.closure_of_commute ?_ ?_, ?_⟩
  · rintro x (rfl | rfl) y (rfl | rfl)
    · rfl
    · exact hab
    · exact hab.symm
    · rfl
  · rintro x (rfl | rfl)
    · exact haq
    · exact hbq
  · have hdisj : zpowers a ⊓ zpowers b = ⊥ := by
      have hle : zpowers a ⊓ zpowers b ≤ zpowers b := inf_le_right
      have hdvd : Nat.card ↥(zpowers a ⊓ zpowers b) ∣ q := by
        simpa [Nat.card_zpowers, hb] using Subgroup.card_dvd_of_le hle
      rcases (Nat.dvd_prime hq).1 hdvd with h1 | h3
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        have heq : zpowers a ⊓ zpowers b = zpowers b :=
          Subgroup.eq_of_le_of_card_ge hle (by rw [h3, Nat.card_zpowers, hb])
        apply hn
        have hbm : b ∈ zpowers a ⊓ zpowers b := by rw [heq]; exact mem_zpowers b
        exact hbm.1
    have hcomm : ∀ x ∈ zpowers a, ∀ y ∈ zpowers b, x * y = y * x := by
      intro x hx y hy
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hx
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hy
      exact (Commute.zpow_zpow (show Commute a b from hab) i j).eq
    have hcl : closure ({a, b} : Set G) = zpowers a ⊔ zpowers b := by
      rw [Set.insert_eq, Subgroup.closure_union, ← zpowers_eq_closure, ← zpowers_eq_closure]
    rw [hcl, card_sup_eq_mul_of_commute_of_inf_eq_bot hcomm hdisj, Nat.card_zpowers,
      Nat.card_zpowers, ha, hb]
    ring

end Generic

section Field

theorem exists_norm_one_orderOf_prime {K : Type} [Field K] {p f : ℕ} (h : UnitaryFieldData p f K)
    {d : ℕ} (hd : d.Prime) (hdvd : d ∣ p ^ f + 1) : ∃ μ : K, μ ≠ 0 ∧ orderOf μ = d ∧ h.norm μ = 1 := by
  classical
  have : Fact d.Prime := ⟨hd⟩
  have hfin : Finite K := h.finite
  have : Fintype K := Fintype.ofFinite K
  have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hunits : Nat.card Kˣ = (p ^ f) ^ 2 - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  have hdN : d ∣ Nat.card Kˣ := by
    rw [hunits]
    have e : (p ^ f) ^ 2 - 1 = (p ^ f + 1) * (p ^ f - 1) := by
      have := Nat.sq_sub_sq (p ^ f) 1
      simpa using this
    rw [e]
    exact Dvd.dvd.mul_right hdvd _
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) d hdN
  refine ⟨(g : K), g.ne_zero, by rw [orderOf_units, hg], ?_⟩
  have hpow : (g : K) ^ (p ^ f + 1) = 1 := by
    have : orderOf (g : K) ∣ p ^ f + 1 := by rw [orderOf_units, hg]; exact hdvd
    exact orderOf_dvd_iff_pow_eq_one.1 this
  rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, ← pow_succ']
  exact hpow

end Field

section Model

variable {K : Type} [Field K]

theorem toral_E9_torus_data {ν : ℕ} (h : UnitaryFieldData 2 ν K) {ζ : K} (hζ0 : ζ ≠ 0)
    (hζN : h.norm ζ = 1) (hζ9 : orderOf ζ = 9) :
    ∃ e f g : StatedProj (StatedSU 3 (2 ^ ν) K), orderOf e = 3 ∧ orderOf f = 3 ∧ e * f = f * e ∧
      f ∉ Subgroup.zpowers e ∧ g * e = e * g ∧ g * f = f⁻¹ * g ∧
      (∀ φ : K ≃+* K, φ ζ = ζ →
        uFieldAut h (by norm_num) φ e = e ∧ uFieldAut h (by norm_num) φ f = f) ∧
      ∀ (d : StatedSU 3 (2 ^ ν) K) (a : Fin 3 → K),
        ((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal a →
          projH _ d * e = e * projH _ d ∧ projH _ d * f = f * projH _ d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hζ9' : ζ ^ 9 = 1 := hζ9 ▸ pow_orderOf_eq_one ζ
  obtain ⟨ω, hω⟩ : ∃ ω : K, ω = ζ ^ 3 := ⟨_, rfl⟩
  have hω0 : ω ≠ 0 := by rw [hω]; exact pow_ne_zero 3 hζ0
  have hωN : h.norm ω = 1 := by
    have : h.norm ω = h.norm ζ ^ 3 := by
      simp only [UnitaryFieldData.norm, hω, map_pow, mul_pow]
    rw [this, hζN, one_pow]
  have hω3 : ω ^ 3 = 1 := by rw [hω, ← pow_mul]; exact hζ9'
  have hω1 : ω ≠ 1 := by
    intro h1
    have h3 : ζ ^ 3 = 1 := by rw [← hω]; exact h1
    have := orderOf_dvd_of_pow_eq_one h3
    rw [hζ9] at this
    omega
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h2
    exact hω1 (by linear_combination hω3 - ω * h2)
  have hζinv : (ζ⁻¹ * ζ⁻¹) ^ 3 = ω := by
    rw [hω]
    field_simp
    linear_combination -hζ9'
  obtain ⟨E, hEdef⟩ : ∃ E : StatedSU 3 (2 ^ ν) K,
      E = uDiag2 h (show (0 : Fin 3) ≠ 2 by decide) hζ0 hζN *
        uDiag2 h (show (1 : Fin 3) ≠ 2 by decide) hζ0 hζN := ⟨_, rfl⟩
  have hEm : ((E : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![ζ, ζ, ζ⁻¹ * ζ⁻¹] := by
    rw [hEdef]
    exact coe_uDiag2_mul h hζ0 hζN
  obtain ⟨F, hFdef⟩ : ∃ F : StatedSU 3 (2 ^ ν) K,
      F = uDiag2 h (show (0 : Fin 3) ≠ 1 by decide) hω0 hωN := ⟨_, rfl⟩
  have hFm : ((F : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![ω, ω⁻¹, 1] := by
    rw [hFdef]
    exact coe_uDiag2_zero_one h hω0 hωN
  obtain ⟨G, hGdef⟩ : ∃ G : StatedSU 3 (2 ^ ν) K,
      G = uRot h (show (0 : Fin 3) ≠ 1 by decide) := ⟨_, rfl⟩
  have hGm : ((G : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![0, 1, 0; 1, 0, 0; 0, 0, 1] := by
    rw [hGdef]
    exact coe_uRot_zero_one h
  have he3 : orderOf (projH _ E) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]
      refine projH_eq_one_of_diag_const (a := ![ζ, ζ, ζ⁻¹ * ζ⁻¹] ^ 3) hω0 ?_ ?_
      · simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hEm, diagonal_pow]
      · intro i
        fin_cases i
        · simpa using hω.symm
        · simpa using hω.symm
        · simpa using hζinv
    · intro h1
      obtain ⟨c, -, hc⟩ := diag_const_of_projH_eq_one hEm h1
      have h02 : ζ = ζ⁻¹ * ζ⁻¹ := by simpa using (hc 0).trans (hc 2).symm
      apply hω1
      rw [hω]
      field_simp at h02
      linear_combination h02
  have hf3 : orderOf (projH _ F) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]
      refine projH_eq_one_of_diag_const (a := ![ω, ω⁻¹, 1] ^ 3) one_ne_zero ?_ ?_
      · simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hFm, diagonal_pow]
      · intro i
        fin_cases i <;> simp [inv_pow, hω3]
    · intro h1
      obtain ⟨c, -, hc⟩ := diag_const_of_projH_eq_one hFm h1
      exact hω1 (by simpa using (hc 0).trans (hc 2).symm)
  have hne : ∀ m : ℕ, projH _ F ≠ projH _ E ^ m := by
    intro m hm
    rw [← map_pow] at hm
    obtain ⟨c, hc0, hc⟩ := diag_ratio_of_projH_eq (a := ![ω, ω⁻¹, 1])
      (a' := ![ζ, ζ, ζ⁻¹ * ζ⁻¹] ^ m) hFm
      (by simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hEm, diagonal_pow]) hm
    have h0 := hc 0
    have h1 := hc 1
    simp only [Pi.pow_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    apply hω2
    have h01 : ω * c = ω⁻¹ * c := h0.symm.trans h1
    have h02 := mul_right_cancel₀ hc0 h01
    field_simp at h02
    linear_combination h02
  have hdiag : ∀ (D : StatedSU 3 (2 ^ ν) K) (b : Fin 3 → K),
      ((D : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal b →
        ∀ (d : StatedSU 3 (2 ^ ν) K) (a : Fin 3 → K),
          ((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal a →
            projH _ d * projH _ D = projH _ D * projH _ d := by
    intro D b hD d a hd
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, hD, hd, diagonal_mul_diagonal]
    congr 1
    ext i
    exact mul_comm _ _
  refine ⟨projH _ E, projH _ F, projH _ G, he3, hf3, hdiag F _ hFm E _ hEm, ?_, ?_, ?_, ?_,
    fun d a hd => ⟨hdiag E _ hEm d a hd, hdiag F _ hFm d a hd⟩⟩
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    obtain ⟨m, hm⟩ : ∃ m : ℕ, projH _ E ^ k = projH _ E ^ m := by
      refine ⟨(k % 3).toNat, ?_⟩
      have h1 := zpow_mod_orderOf (projH _ E) k
      rw [he3] at h1
      have h3 : ((k % 3).toNat : ℤ) = k % ((3 : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg (by omega)]
        norm_num
      rw [← zpow_natCast, h3, h1]
    exact hne m (by rw [← hk, hm])
  · rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, hEm, hGm]
    exact swap_mul_diagonal ζ ζ (ζ⁻¹ * ζ⁻¹)
  · rw [← map_inv (projH (StatedSU 3 (2 ^ ν) K)), ← map_mul, ← map_mul]
    congr 1
    rw [eq_inv_mul_iff_mul_eq]
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, hFm, hGm]
    rw [swap_mul_diagonal, ← Matrix.mul_assoc, diagonal_mul_diagonal]
    have h1 : (diagonal fun i => (![ω, ω⁻¹, 1] : Fin 3 → K) i * (![ω⁻¹, ω, 1] : Fin 3 → K) i) =
        1 := by
      rw [← diagonal_one]
      congr 1
      ext k
      fin_cases k <;> simp [hω0]
    rw [h1, Matrix.one_mul]
  · intro φ hφ
    have hφω : φ ω = ω := by rw [hω, map_pow, hφ]
    constructor
    · apply uFieldAut_projH_eq_of_fix
      rw [hEm]
      refine map_diagonal_apply_fix (fun i => ?_)
      fin_cases i <;> simp [hφ]
    · apply uFieldAut_projH_eq_of_fix
      rw [hFm]
      refine map_diagonal_apply_fix (fun i => ?_)
      fin_cases i <;> simp [hφω]

theorem diag_pair_data {ν : ℕ} (h : UnitaryFieldData 2 ν K) {q : ℕ} (hq : q.Prime) (hq3 : q ≠ 3)
    {μ : K} (hμ0 : μ ≠ 0) (hμN : h.norm μ = 1) (hμq : orderOf μ = q) :
    ∃ d₁ d₂ : StatedSU 3 (2 ^ ν) K,
      (∃ a : Fin 3 → K, ((d₁ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal a) ∧
      (∃ a : Fin 3 → K, ((d₂ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal a) ∧
      orderOf (projH _ d₁) = q ∧ orderOf (projH _ d₂) = q ∧
      projH _ d₁ * projH _ d₂ = projH _ d₂ * projH _ d₁ ∧
      projH _ d₂ ∉ Subgroup.zpowers (projH _ d₁) := by
  have : Fact q.Prime := ⟨hq⟩
  have hμq1 : μ ^ q = 1 := hμq ▸ pow_orderOf_eq_one μ
  obtain ⟨D₁, hD₁⟩ : ∃ D₁ : StatedSU 3 (2 ^ ν) K,
      D₁ = uDiag2 h (show (0 : Fin 3) ≠ 1 by decide) hμ0 hμN := ⟨_, rfl⟩
  obtain ⟨D₂, hD₂⟩ : ∃ D₂ : StatedSU 3 (2 ^ ν) K,
      D₂ = uDiag2 h (show (1 : Fin 3) ≠ 2 by decide) hμ0 hμN := ⟨_, rfl⟩
  have hD₁m : ((D₁ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![μ, μ⁻¹, 1] := by
    rw [hD₁]
    exact coe_uDiag2_zero_one h hμ0 hμN
  have hD₂m : ((D₂ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![1, μ, μ⁻¹] := by
    rw [hD₂]
    exact coe_uDiag2_one_two h hμ0 hμN
  have ho₁ : orderOf (projH _ D₁) = q := by
    rw [hD₁]
    exact (diag_fixed_order h hq hμ0 hμN hμq).1
  have ho₂ : orderOf (projH _ D₂) = q := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]
      refine projH_eq_one_of_diag_const (a := ![1, μ, μ⁻¹] ^ q) one_ne_zero ?_ ?_
      · simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hD₂m, diagonal_pow]
      · intro i
        fin_cases i <;> simp [hμq1, inv_pow]
    · intro h1
      obtain ⟨c, -, hc⟩ := diag_const_of_projH_eq_one hD₂m h1
      have h01 : (1 : K) = μ := by simpa using (hc 0).trans (hc 1).symm
      have : orderOf μ = 1 := by rw [← h01, orderOf_one]
      rw [hμq] at this
      exact hq.ne_one this
  have hcomm : projH _ D₁ * projH _ D₂ = projH _ D₂ * projH _ D₁ := by
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, hD₁m, hD₂m, diagonal_mul_diagonal]
    congr 1
    ext i
    exact mul_comm _ _
  have hne : ∀ m : ℕ, projH _ D₂ ≠ projH _ D₁ ^ m := by
    intro m hm
    rw [← map_pow] at hm
    obtain ⟨c, hc0, hc⟩ := diag_ratio_of_projH_eq (a := ![1, μ, μ⁻¹])
      (a' := ![μ, μ⁻¹, 1] ^ m) hD₂m
      (by simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hD₁m, diagonal_pow]) hm
    have h0 := hc 0
    have h1 := hc 1
    have h2 := hc 2
    simp only [Pi.pow_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, one_pow, one_mul] at h0 h1 h2
    have hcμ : c = μ := ((inv_mul_eq_one₀ hμ0).1 h2.symm).symm
    rw [hcμ] at h0 h1
    rw [inv_pow, h0] at h1
    have h3 : μ ^ 3 = 1 := by
      calc μ ^ 3 = μ * (μ * μ) := by ring
        _ = μ * μ⁻¹ := by rw [h1]
        _ = 1 := mul_inv_cancel₀ hμ0
    have hdvd : q ∣ 3 := hμq ▸ orderOf_dvd_of_pow_eq_one h3
    exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 hdvd)
  refine ⟨D₁, D₂, ⟨_, hD₁m⟩, ⟨_, hD₂m⟩, ho₁, ho₂, hcomm, ?_⟩
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  obtain ⟨m, hm⟩ : ∃ m : ℕ, projH _ D₁ ^ k = projH _ D₁ ^ m := by
    refine ⟨(k % q).toNat, ?_⟩
    have h1 := zpow_mod_orderOf (projH _ D₁) k
    rw [ho₁] at h1
    have h3 : ((k % q).toNat : ℤ) = k % (q : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg k hq0)
    rw [← zpow_natCast, h3, h1]
  exact hne m (by rw [← hk, hm])

end Model

section Main

variable {X : Type} [Group X] [Finite X]

theorem lift_E9_fixed_mem (hZ : Nat.card (center X) ∣ 3)
    {e f g : X ⧸ center X} (he : orderOf e = 3) (hf : orderOf f = 3) (hef : e * f = f * e)
    (hn : f ∉ Subgroup.zpowers e) (hge : g * e = e * g) (hgf : g * f = f⁻¹ * g)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) (α : MulAut X) (hα : α ^ r = 1)
    (hαe : autQuot α e = e) (hαf : autQuot α f = f) :
    ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ (∀ x ∈ E, α x = x) ∧
      ∀ x ∈ E, (QuotientGroup.mk x : X ⧸ center X) ∈ closure ({e, f} : Set (X ⧸ center X)) := by
  have hcl : ∀ y ∈ closure ({e, f} : Set (X ⧸ center X)), autQuot α y = y := fun y hy =>
    apply_eq_of_mem_closure (autQuot α) (s := {e, f}) (by rintro y (rfl | rfl); exacts [hαe, hαf]) hy
  rcases (Nat.dvd_prime Nat.prime_three).1 hZ with h1 | h3
  · have hcen : center X = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    obtain ⟨φ, hφ⟩ := exists_mulEquiv_of_center_eq_bot hcen
    obtain ⟨hel, hcard⟩ := closure_pair_isElemAbelian_card he hf hef hn
    have hmk : ∀ b : X ⧸ center X, (QuotientGroup.mk (φ.symm b) : X ⧸ center X) = b := fun b => by
      rw [← hφ]; exact φ.apply_symm_apply b
    refine ⟨(closure ({e, f} : Set (X ⧸ center X))).map φ.symm.toMonoidHom, hel.map _, ?_, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective φ.symm.injective, hcard]
    · rintro _ ⟨b, hb, rfl⟩
      apply φ.injective
      calc φ (α (φ.symm b)) = QuotientGroup.mk (α (φ.symm b)) := hφ _
        _ = autQuot α (QuotientGroup.mk (φ.symm b)) := (autQuot_mk _ _).symm
        _ = autQuot α b := by rw [hmk b]
        _ = b := hcl b hb
        _ = φ (φ.symm b) := (φ.apply_symm_apply b).symm
    · rintro _ ⟨b, hb, rfl⟩
      change (QuotientGroup.mk (φ.symm b) : X ⧸ center X) ∈ _
      rw [hmk b]
      exact hb
  · obtain ⟨ζ, hζ, hζ3⟩ := exists_central_order_three h3
    obtain ⟨w, hw3, hwc, hwmem, -⟩ := exists_cube_one_lift_mem hZ he hf hef hn hge hgf
    have hw : orderOf w = 3 := orderOf_eq_prime hw3 (fun h => hwc (h ▸ one_mem _))
    obtain ⟨hel, hcard⟩ := closure_pair_central_isElemAbelian_card hw hζ3 hwc hζ
    have hodd : r % 2 = 1 := hr.eq_two_or_odd.resolve_left hr2
    have hζf : α ζ = ζ := apply_central_order_three h3 hζ hζ3 hodd α hα
    have hwf : α w = w :=
      apply_eq_of_autQuot_fixed h3 hζ hζ3 hr hr3 α hα hζf (hcl _ hwmem)
    have hle : closure ({w, ζ} : Set X) ≤
        (closure ({e, f} : Set (X ⧸ center X))).comap (QuotientGroup.mk' (center X)) := by
      rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨hwmem, ?_⟩
      show (QuotientGroup.mk ζ : X ⧸ center X) ∈ closure ({e, f} : Set (X ⧸ center X))
      rw [(QuotientGroup.eq_one_iff _).2 hζ]
      exact one_mem _
    refine ⟨closure ({w, ζ} : Set X), hel, hcard, fun x hx => ?_, fun x hx => hle hx⟩
    exact apply_eq_of_mem_closure α (s := {w, ζ}) (by rintro y (rfl | rfl); exacts [hwf, hζf]) hx

theorem u3Fix3FieldTorus_of_center (hCen : U3Center) : U3Fix3FieldTorus := by
  intro X _ _ hX α hα hni
  have hZ := hCen X 21 hX
  obtain ⟨K, _, h, e, M, φ, hφord, hrn, hcard, hbar, hfix⟩ :=
    u3_prime_descent hX (r := 7) (by norm_num) (by norm_num) (by norm_num) hα hni
  have h37 : (21 : ℕ) / 7 = 3 := by norm_num
  rw [h37] at hcard hbar
  obtain ⟨ζ, hζ0, hζ9, hφζ, hζN⟩ := exists_fixed_norm_one_order h hcard hbar (d := 9) (by norm_num)
  obtain ⟨e', f', g', he3, hf3, hef, hfn, hge, hgf, hfix', htor⟩ := toral_E9_torus_data h hζ0 hζN hζ9
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : StatedProj (StatedSU 3 (2 ^ 21) K) ≃* (X ⧸ center X),
      ∀ y, Φ y = e.symm (uConjAut h (by norm_num) M y) :=
    ⟨(uConjAut h (by norm_num) M).trans e.symm, fun y => rfl⟩
  obtain ⟨E, hEel, hEc, hEfix, hEmem⟩ := lift_E9_fixed_mem hZ (e := Φ e') (f := Φ f') (g := Φ g')
    (by rw [MulEquiv.orderOf_eq]; exact he3) (by rw [MulEquiv.orderOf_eq]; exact hf3)
    (by rw [← map_mul, ← map_mul, hef])
    (by
      intro hmem
      apply hfn
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
      rw [← map_zpow] at hk
      exact Subgroup.mem_zpowers_iff.2 ⟨k, Φ.injective hk⟩)
    (by rw [← map_mul, ← map_mul, hge]) (by rw [← map_mul, ← map_inv, ← map_mul, hgf])
    (r := 7) (by norm_num) (by norm_num) (by norm_num) α hα
    (by rw [hΦ]; exact hfix e' (hfix' φ hφζ).1) (by rw [hΦ]; exact hfix f' (hfix' φ hφζ).2)
  refine ⟨E, hEel, hEc, hEfix, fun p hp hpd hp3 => ?_⟩
  have hcop : p.Coprime 3 := (Nat.coprime_primes hp Nat.prime_three).2 hp3
  obtain ⟨μ, hμ0, hμp, hμN⟩ := exists_norm_one_orderOf_prime h hp hpd
  obtain ⟨d₁, d₂, ⟨a₁, hd₁⟩, ⟨a₂, hd₂⟩, ho₁, ho₂, hd₁₂, hd₂n⟩ := diag_pair_data h hp hp3 hμ0 hμN hμp
  obtain ⟨x, hxo, hxmk⟩ := exists_lift_orderOf_prime hZ hp hp3 (zb := Φ (projH _ d₁))
    (by rw [MulEquiv.orderOf_eq]; exact ho₁)
  obtain ⟨y, hyo, hymk⟩ := exists_lift_orderOf_prime hZ hp hp3 (zb := Φ (projH _ d₂))
    (by rw [MulEquiv.orderOf_eq]; exact ho₂)
  have hxp : x ^ p = 1 := hxo ▸ pow_orderOf_eq_one x
  have hxy : x * y = y * x := mul_comm_of_lift_of_coprime hZ hcop hxp
    (by rw [hxmk, hymk, ← map_mul Φ, ← map_mul Φ, hd₁₂])
  have hyn : y ∉ Subgroup.zpowers x := by
    intro hmem
    apply hd₂n
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have h1 : Φ (projH _ d₁ ^ k) = Φ (projH _ d₂) := by
      rw [map_zpow, ← hxmk, ← hymk, ← hk, QuotientGroup.mk_zpow]
    exact Subgroup.mem_zpowers_iff.2 ⟨k, Φ.injective h1⟩
  obtain ⟨hPel, hPc⟩ := closure_pair_isElemAbelian_card_of_prime hp hxo hyo hxy hyn
  refine ⟨closure ({x, y} : Set X), hPel, hPc, ?_⟩
  have hcent : ∀ (d : StatedSU 3 (2 ^ 21) K) (a : Fin 3 → K),
      ((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal a →
        closure ({Φ e', Φ f'} : Set (X ⧸ center X)) ≤ centralizer ({Φ (projH _ d)} : Set _) := by
    intro d a hd
    obtain ⟨he', hf'⟩ := htor d a hd
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (by rw [← map_mul Φ, ← map_mul Φ, he'])
    · exact Subgroup.mem_centralizer_singleton_iff.2 (by rw [← map_mul Φ, ← map_mul Φ, hf'])
  have hlift : ∀ z : X, z ^ p = 1 → ∀ (d : StatedSU 3 (2 ^ 21) K) (a : Fin 3 → K),
      ((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal a →
        (QuotientGroup.mk z : X ⧸ center X) = Φ (projH _ d) → z ∈ centralizer (E : Set X) := by
    intro z hzp d a hd hzmk
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hwc := Subgroup.mem_centralizer_singleton_iff.1 (hcent d a hd (hEmem w hw))
    exact (mul_comm_of_lift_of_coprime hZ hcop hzp (by rw [hzmk]; exact hwc.symm)).symm
  have hyp : y ^ p = 1 := hyo ▸ pow_orderOf_eq_one y
  rw [Subgroup.closure_le]
  rintro z (rfl | rfl)
  · exact hlift z hxp d₁ a₁ hd₁ hxmk
  · exact hlift z hyp d₂ a₂ hd₂ hymk

theorem u3Fix3FieldTorus_holds (hG : CFSG.Open.GriessAllModelsStatement) : U3Fix3FieldTorus :=
  u3Fix3FieldTorus_of_center (u3Center_of_griess hG)

end Main

end CFSG.LocalAnalysis.UniquenessCase.UCK
