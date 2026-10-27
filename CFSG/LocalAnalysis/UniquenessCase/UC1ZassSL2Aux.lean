module

public import CFSG.GH74.Uniqueness.Bender.Core
public import CFSG.Walter.ReeOrder.Ward.Quaternion

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Zass

open CFSG.PSL2Table
open scoped MatrixGroups

section Matrices

variable {F : Type} [Field F]

theorem unip_pow (t : F) (n : ℕ) : unip t ^ n = unip ((n : F) * t) := by
  induction n with
  | zero => simp [unip_zero]
  | succ n ih => rw [pow_succ, ih, ← unip_add]; push_cast; ring_nf

theorem diag_pow (a : Fˣ) (n : ℕ) : diag a ^ n = diag (a ^ n) := by
  induction n with
  | zero => simp [diag_one]
  | succ n ih => rw [pow_succ, ih, pow_succ, diag_mul]

theorem diag_injective : Function.Injective (diag : Fˣ → SL(2, F)) := by
  intro a b h
  have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  exact Units.ext (by simpa [diag] using this)

theorem unip_injective : Function.Injective (unip : F → SL(2, F)) := by
  intro s t h
  have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa [unip] using this

theorem diag_zpow (a : Fˣ) (k : ℤ) : diag a ^ k = diag (a ^ k) := by
  cases k with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast, diag_pow]
  | negSucc n => rw [zpow_negSucc, zpow_negSucc, diag_pow, diag_inv]

theorem eq_unip_of_mem_unipSL {u : SL(2, F)} (hu : u ∈ unipSL F) :
    u = unip ((u : Matrix (Fin 2) (Fin 2) F) 0 1) := by
  obtain ⟨h10, h00, h11⟩ := hu
  apply SL_ext <;> simp [unip, h10, h00, h11]

theorem diag_conj_mem_unipSL (a : Fˣ) {u : SL(2, F)} (hu : u ∈ unipSL F) :
    diag a * u * (diag a)⁻¹ ∈ unipSL F := by
  rw [eq_unip_of_mem_unipSL hu, diag_conj_unip]
  exact unip_mem_unipSL _

theorem neg_mul_SL (A B : SL(2, F)) : (-A) * B = -(A * B) := by
  ext i j
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg]

theorem mul_neg_SL (A B : SL(2, F)) : A * (-B) = -(A * B) := by
  ext i j
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg]

theorem neg_neg_SL (A : SL(2, F)) : -(-A) = A := by
  ext i j
  simp [Matrix.SpecialLinearGroup.coe_neg]

theorem exists_quaternion_relations [Fintype F] (hF : ringChar F ≠ 2) :
    ∃ i j w z : SL(2, F), z ^ 2 = 1 ∧ z ≠ 1 ∧ i ^ 2 = z ∧ j ^ 2 = z ∧ j * i * j⁻¹ = i⁻¹ ∧
      w ^ 3 = 1 ∧ w * i * w⁻¹ = j ∧ w * j * w⁻¹ = i * j := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  obtain ⟨a, b, hab⟩ := exists_normForm_eq hF (ν := -1) (by norm_num) (-1)
  have h : a ^ 2 + b ^ 2 = -1 := by linear_combination hab
  have hinv : (CFSG.Walter.Ward.Quaternion.qi : SL(2, F))⁻¹ = -CFSG.Walter.Ward.Quaternion.qi :=
    inv_eq_of_mul_eq_one_right (by
      rw [mul_neg_SL, CFSG.Walter.Ward.Quaternion.qi_mul_qi, neg_neg_SL])
  refine ⟨CFSG.Walter.Ward.Quaternion.qi, CFSG.Walter.Ward.Quaternion.qj a b h,
    CFSG.Walter.Ward.Quaternion.qw a b h2 h, -1, ?_, neg_one_ne_one_SL h2, ?_, ?_, ?_,
    CFSG.Walter.Ward.Quaternion.qw_cube h2 h, ?_, ?_⟩
  · rw [← diag_neg_one, diag_pow]
    simp [diag_one]
  · rw [pow_two, CFSG.Walter.Ward.Quaternion.qi_mul_qi]
  · rw [pow_two, CFSG.Walter.Ward.Quaternion.qj_mul_qj]
  · rw [hinv, CFSG.Walter.Ward.Quaternion.qj_mul_qi, neg_mul_SL, mul_inv_cancel_right]
  · exact mul_inv_eq_iff_eq_mul.mpr (CFSG.Walter.Ward.Quaternion.qw_mul_qi h2 h)
  · exact mul_inv_eq_iff_eq_mul.mpr (CFSG.Walter.Ward.Quaternion.qw_mul_qj h2 h)

theorem false_of_odd_prime_dvd [Fintype F] {r ℓ : ℕ} (hr : r.Prime) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hcard : Fintype.card F = r) (hℓr : ℓ ∣ r - 1)
    (hcyc : ∀ H : Subgroup SL(2, F), Nat.card H = r * ℓ → IsCyclic H) : False := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hdvd : ℓ ∣ Nat.card Fˣ := by
    rw [Nat.card_units, Nat.card_eq_fintype_card, hcard]
    exact hℓr
  obtain ⟨lam, hlam⟩ := exists_prime_orderOf_dvd_card' ℓ hdvd
  set t : SL(2, F) := diag lam with ht
  have hlam1 : lam ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hlam
    exact hℓ.one_lt.ne hlam
  have ht1 : t ^ ℓ = 1 := by rw [ht, diag_pow, ← hlam, pow_orderOf_eq_one, diag_one]
  have htne : t ≠ 1 := fun h => hlam1 (diag_injective (h.trans diag_one.symm))
  have hto : orderOf t = ℓ := orderOf_eq_prime ht1 htne
  set A := unipSL F with hAdef
  set B := Subgroup.zpowers t with hBdef
  have hA : Nat.card A = r := by rw [hAdef, card_unipSL, hcard]
  have hB : Nat.card B = ℓ := by rw [hBdef, Nat.card_zpowers, hto]
  have hlt : ℓ < r := by
    have h2 := hr.two_le
    have := Nat.le_of_dvd (by omega) hℓr
    omega
  have hinf : A ⊓ B = ⊥ :=
    Subgroup.inf_eq_bot_of_coprime (by rw [hA, hB]; exact (Nat.coprime_primes hr hℓ).2 hlt.ne')
  have hnorm : B ≤ Subgroup.normalizer (A : Set SL(2, F)) := by
    intro b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [ht, diag_zpow, Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨fun hu => diag_conj_mem_unipSL _ hu, fun hu => ?_⟩
    have h := diag_conj_mem_unipSL (lam ^ k)⁻¹ hu
    rw [← diag_inv, inv_inv] at h
    have h' : (diag (lam ^ k))⁻¹ * (diag (lam ^ k) * u * (diag (lam ^ k))⁻¹) * diag (lam ^ k) = u :=
      by group
    rwa [h'] at h
  have hsup : Nat.card (A ⊔ B : Subgroup SL(2, F)) = r * ℓ :=
    (CFSG.GH74.Uniqueness.Bender.card_sup_eq_mul_of_le_normalizer hnorm hinf).trans
      (by rw [hA, hB])
  haveI := hcyc _ hsup
  have huH : unip (1 : F) ∈ (A ⊔ B : Subgroup SL(2, F)) := Subgroup.mem_sup_left (unip_mem_unipSL 1)
  have htH : t ∈ (A ⊔ B : Subgroup SL(2, F)) := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hcomm := congrArg Subtype.val
    (IsMulCommutative.is_comm.comm (⟨unip (1 : F), huH⟩ : (A ⊔ B : Subgroup SL(2, F)))
      ⟨t, htH⟩)
  have h1 : t * unip (1 : F) * t⁻¹ = unip 1 := by
    have : t * unip (1 : F) = unip 1 * t := hcomm.symm
    rw [this, mul_inv_cancel_right]
  rw [ht, diag_conj_unip] at h1
  have h2 : (lam : F) ^ 2 * 1 = 1 := unip_injective h1
  have h3 : lam ^ 2 = 1 := Units.ext (by simpa using h2)
  have h4 : ℓ ∣ 2 := hlam ▸ orderOf_dvd_of_pow_eq_one h3
  exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h4)

end Matrices

section Group

variable {G : Type*} [Group G]

theorem isPGroup_closure_of_quaternion {i j z : G} (hz : z ^ 2 = 1) (hi : i ^ 2 = z)
    (hj : j ^ 2 = z) (hji : j * i * j⁻¹ = i⁻¹) : IsPGroup 2 (Subgroup.closure {i, j}) := by
  set A := Subgroup.zpowers i with hA
  have hzA : z ∈ A := hi ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers i) 2
  have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq, hz])
  have hjinv : j⁻¹ = j * z := inv_eq_of_mul_eq_one_right (by
    rw [← mul_assoc, ← sq, hj, ← sq, hz])
  have hconj : ∀ a ∈ A, j * a * j⁻¹ = a⁻¹ := by
    intro a ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← conj_zpow, hji, inv_zpow]
  have key : ∀ x ∈ Subgroup.closure ({i, j} : Set G), x ∈ A ∨ ∃ a ∈ A, x = a * j := by
    intro x hx
    refine Subgroup.closure_induction (p := fun x _ => x ∈ A ∨ ∃ a ∈ A, x = a * j) ?_ ?_ ?_ ?_ hx
    · rintro x (rfl | rfl)
      · exact Or.inl (Subgroup.mem_zpowers _)
      · exact Or.inr ⟨1, A.one_mem, (one_mul _).symm⟩
    · exact Or.inl A.one_mem
    · rintro x y - - (hx | ⟨a, ha, rfl⟩) (hy | ⟨b, hb, rfl⟩)
      · exact Or.inl (A.mul_mem hx hy)
      · exact Or.inr ⟨x * b, A.mul_mem hx hb, by rw [mul_assoc]⟩
      · refine Or.inr ⟨a * y⁻¹, A.mul_mem ha (A.inv_mem hy), ?_⟩
        calc a * j * y = a * (j * y * j⁻¹) * j := by group
          _ = a * y⁻¹ * j := by rw [hconj y hy]
      · refine Or.inl ?_
        have h1 : a * j * (b * j) = a * b⁻¹ * z := by
          calc a * j * (b * j) = a * (j * b * j⁻¹) * (j * j) := by group
            _ = a * b⁻¹ * z := by rw [hconj b hb, ← sq, hj]
        rw [h1]
        exact A.mul_mem (A.mul_mem ha (A.inv_mem hb)) hzA
    · rintro x - (hx | ⟨a, ha, rfl⟩)
      · exact Or.inl (A.inv_mem hx)
      · refine Or.inr ⟨a * z, A.mul_mem ha hzA, ?_⟩
        have h1 := hconj (z * a⁻¹) (A.mul_mem hzA (A.inv_mem ha))
        rw [mul_inv_rev, inv_inv, hz'] at h1
        calc (a * j)⁻¹ = j⁻¹ * a⁻¹ := mul_inv_rev _ _
          _ = j * (z * a⁻¹) := by rw [hjinv, mul_assoc]
          _ = (j * (z * a⁻¹) * j⁻¹) * j := (inv_mul_cancel_right _ _).symm
          _ = a * z * j := by rw [h1]
  have hi4 : i ^ 4 = 1 := by rw [show 4 = 2 * 2 from rfl, pow_mul, hi, hz]
  intro x
  refine ⟨2, Subtype.ext ?_⟩
  have h4 : (x : G) ^ 4 = 1 := by
    rcases key x x.2 with hx | ⟨a, ha, hx⟩
    · obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hi4, one_zpow]
    · have h2 : (a * j) ^ 2 = z := by
        calc (a * j) ^ 2 = a * (j * a * j⁻¹) * (j * j) := by rw [sq]; group
          _ = z := by rw [hconj a ha, ← sq, hj]; group
      rw [hx, show 4 = 2 * 2 from rfl, pow_mul, h2, hz]
  simpa using h4

end Group

end CFSG.LocalAnalysis.UniquenessCase.UCK.Zass
