module

public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley

namespace TableB

section Cokernel

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (K : Type) [Field K]

theorem mem_torusSubgroup_of_row {m w : Fin r → ℤ} (hw : ∀ j', ∑ i, m i * A i j' = w j')
    (s : Kˣ) : (fun j' => s ^ w j') ∈ torusSubgroup A K := by
  have h := zpow_sum_mem_torusSubgroup A K m s
  simp only [hw] at h
  exact h

theorem torusSubgroup_eq_top_of_mul_eq_smul {M : Matrix (Fin r) (Fin r) ℤ} {d : ℕ}
    (hM : M * A = (d : ℤ) • (1 : Matrix (Fin r) (Fin r) ℤ))
    (hroot : ∀ s : Kˣ, ∃ u : Kˣ, u ^ d = s) :
    torusSubgroup A K = ⊤ := by
  rw [eq_top_iff]
  intro a _
  rw [← Finset.univ_prod_mulSingle a]
  refine Subgroup.prod_mem _ fun j _ => ?_
  obtain ⟨u, hu⟩ := hroot (a j)
  rw [← hu, ← zpow_natCast]
  exact mulSingle_pow_mem_torusSubgroup A K hM j u

end Cokernel

theorem exists_pow_eq_of_zpowers_three {Q : Type*} [Group Q] [Finite Q] {q₀ : Q}
    (hgen : ∀ x : Q, x ∈ Subgroup.zpowers q₀) (h3 : q₀ ^ 3 = 1) {y : Q} (hy : y ≠ 1) (x : Q) :
    ∃ k : ℕ, y ^ k = x := by
  have hcard : Nat.card Q = 3 := by
    rw [← orderOf_eq_card_of_forall_mem_zpowers hgen]
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h3) with h | h
    · exfalso
      rw [orderOf_eq_one_iff] at h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen y)
      rw [h, one_zpow] at hk
      exact hy hk.symm
    · exact h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx : x ∈ Subgroup.zpowers y := by
    rw [zpowers_eq_top_of_prime_card hcard hy]
    exact Subgroup.mem_top x
  rw [← mem_powers_iff_mem_zpowers] at hx
  exact hx

theorem cartanG2_inv : (!![2, 1; 3, 2] : Matrix (Fin 2) (Fin 2) ℤ) * LargeEvenCartanG2 =
    ((1 : ℕ) : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  decide

theorem cartanF4_inv : (!![2, 3, 2, 1; 3, 6, 4, 2; 4, 8, 6, 3; 2, 4, 3, 2] :
    Matrix (Fin 4) (Fin 4) ℤ) * LargeEvenCartanF4 =
    ((1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  decide

theorem cartanE8_inv : (!![4, 5, 7, 10, 8, 6, 4, 2; 5, 8, 10, 15, 12, 9, 6, 3;
    7, 10, 14, 20, 16, 12, 8, 4; 10, 15, 20, 30, 24, 18, 12, 6; 8, 12, 16, 24, 20, 15, 10, 5;
    6, 9, 12, 18, 15, 12, 8, 4; 4, 6, 8, 12, 10, 8, 6, 3; 2, 3, 4, 6, 5, 4, 3, 2] :
    Matrix (Fin 8) (Fin 8) ℤ) * LargeEvenCartanE 8 =
    ((1 : ℕ) : ℤ) • (1 : Matrix (Fin 8) (Fin 8) ℤ) := by
  decide

theorem cartanE7_adj : (!![4, 4, 6, 8, 6, 4, 2; 4, 7, 8, 12, 9, 6, 3; 6, 8, 12, 16, 12, 8, 4;
    8, 12, 16, 24, 18, 12, 6; 6, 9, 12, 18, 15, 10, 5; 4, 6, 8, 12, 10, 8, 4;
    2, 3, 4, 6, 5, 4, 3] : Matrix (Fin 7) (Fin 7) ℤ) * LargeEvenCartanE 7 =
    ((2 : ℕ) : ℤ) • (1 : Matrix (Fin 7) (Fin 7) ℤ) := by
  decide

theorem cartanE6_adj : (!![4, 3, 5, 6, 4, 2; 3, 6, 6, 9, 6, 3; 5, 6, 10, 12, 8, 4;
    6, 9, 12, 18, 12, 6; 4, 6, 8, 12, 10, 5; 2, 3, 4, 6, 5, 4] : Matrix (Fin 6) (Fin 6) ℤ) *
    LargeEvenCartanE 6 = ((3 : ℕ) : ℤ) • (1 : Matrix (Fin 6) (Fin 6) ℤ) := by
  decide

@[expose] def e6Coeff : Fin 6 → ℤ :=
  ![1, 0, 2, 0, 1, 2]

theorem cartanE6_rel : (!![0, 0, 0, 0, 0, 0; 1, 2, 2, 3, 2, 1; -1, 0, 0, 0, 0, 0;
    2, 3, 4, 6, 4, 2; 0, 1, 1, 2, 2, 1; -2, -1, -2, -2, -1, 0] : Matrix (Fin 6) (Fin 6) ℤ) *
    LargeEvenCartanE 6 = 1 - Matrix.of fun j j' => if j' = 0 then e6Coeff j else 0 := by
  decide

section E6

variable (K : Type) [Field K]

theorem mulSingle_mul_inv_mem_torusE6 (j : Fin 6) (s : Kˣ) :
    Pi.mulSingle j s * (Pi.mulSingle 0 (s ^ e6Coeff j))⁻¹ ∈
      torusSubgroup (LargeEvenCartanE 6) K := by
  have h := mem_torusSubgroup_of_row (LargeEvenCartanE 6) K
    (m := (!![0, 0, 0, 0, 0, 0; 1, 2, 2, 3, 2, 1; -1, 0, 0, 0, 0, 0;
      2, 3, 4, 6, 4, 2; 0, 1, 1, 2, 2, 1; -2, -1, -2, -2, -1, 0] : Matrix (Fin 6) (Fin 6) ℤ) j)
    (w := fun j' => (1 - Matrix.of fun j j' => if j' = 0 then e6Coeff j else 0 :
      Matrix (Fin 6) (Fin 6) ℤ) j j')
    (fun j' => by
      have := congrFun (congrFun cartanE6_rel j) j'
      rw [Matrix.mul_apply] at this
      exact this) s
  convert h using 1
  funext j'
  simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.of_apply]
  rcases eq_or_ne j' j with rfl | h1 <;> rcases eq_or_ne j' 0 with rfl | h2
  · simp [e6Coeff]
  · simp [h2]
  · simp [h1, Ne.symm h1, zpow_neg]
  · simp [h1, Ne.symm h1, h2]

variable [Finite K]

theorem exists_pow_mem_torusE6 (a a' : Fin 6 → Kˣ)
    (ha' : a' ∉ torusSubgroup (LargeEvenCartanE 6) K) :
    ∃ k : ℕ, a * (a' ^ k)⁻¹ ∈ torusSubgroup (LargeEvenCartanE 6) K := by
  set T := torusSubgroup (LargeEvenCartanE 6) K with hT
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  set q₀ : (Fin 6 → Kˣ) ⧸ T := ((Pi.mulSingle 0 g : Fin 6 → Kˣ) : (Fin 6 → Kˣ) ⧸ T) with hq₀
  have h0 : ∀ s : Kˣ, ((Pi.mulSingle 0 s : Fin 6 → Kˣ) : (Fin 6 → Kˣ) ⧸ T) ∈
      Subgroup.zpowers q₀ := by
    intro s
    obtain ⟨v, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg s)
    exact Subgroup.mem_zpowers_iff.mpr
      ⟨v, by rw [hq₀, ← QuotientGroup.mk_zpow, ← Pi.mulSingle_zpow]⟩
  have hj : ∀ (j : Fin 6) (s : Kˣ), ((Pi.mulSingle j s : Fin 6 → Kˣ) : (Fin 6 → Kˣ) ⧸ T) ∈
      Subgroup.zpowers q₀ := by
    intro j s
    have heq : ((Pi.mulSingle j s : Fin 6 → Kˣ) : (Fin 6 → Kˣ) ⧸ T) =
        ((Pi.mulSingle 0 (s ^ e6Coeff j) : Fin 6 → Kˣ) : (Fin 6 → Kˣ) ⧸ T) := by
      rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
      exact mulSingle_mul_inv_mem_torusE6 K j s
    rw [heq]
    exact h0 _
  have hgen : ∀ x : (Fin 6 → Kˣ) ⧸ T, x ∈ Subgroup.zpowers q₀ := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H a =>
      rw [← Finset.univ_prod_mulSingle a, QuotientGroup.mk_prod]
      exact Subgroup.prod_mem (Subgroup.zpowers q₀) fun j _ => hj j (a j)
  have h3 : q₀ ^ 3 = 1 := by
    rw [hq₀, ← QuotientGroup.mk_pow, ← Pi.mulSingle_pow, QuotientGroup.eq_one_iff,
      ← zpow_natCast]
    exact mulSingle_pow_mem_torusSubgroup (LargeEvenCartanE 6) K cartanE6_adj 0 g
  obtain ⟨k, hk⟩ := exists_pow_eq_of_zpowers_three hgen h3
    (y := ((a' : Fin 6 → Kˣ) : (Fin 6 → Kˣ) ⧸ T)) (by rwa [Ne, QuotientGroup.eq_one_iff])
    (a : (Fin 6 → Kˣ) ⧸ T)
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    QuotientGroup.mk_pow, hk, mul_inv_cancel]

end E6

section Untwisted

variable (K : Type) [Field K]

theorem ggOutdiagCyclic_chevalley_of_top {τ : Tag} (hT : torusSubgroup τ.cartan K = ⊤) :
    GGOutdiagCyclic (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false))
      (LargeEvenChevIDImage τ.cartan K (LargeEvenChevH τ.cartan K false)) :=
  ggOutdiagCyclic_chevID (torusSubgroup τ.cartan K)
    (fun _ ht => diagHom_mem_of_mem_torusSubgroup τ K ht)
    (fun _ a' _ _ h => absurd (by rw [hT]; exact Subgroup.mem_top a') h)

theorem ggOutdiagCyclic_G2 :
    GGOutdiagCyclic (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K false))
      (LargeEvenChevIDImage LargeEvenCartanG2 K (LargeEvenChevH LargeEvenCartanG2 K false)) :=
  ggOutdiagCyclic_chevalley_of_top (τ := .G2) K
    (torusSubgroup_eq_top_of_mul_eq_smul _ K cartanG2_inv fun s => ⟨s, pow_one s⟩)

theorem ggOutdiagCyclic_F4 :
    GGOutdiagCyclic (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanF4 K false))
      (LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenChevH LargeEvenCartanF4 K false)) :=
  ggOutdiagCyclic_chevalley_of_top (τ := .F4) K
    (torusSubgroup_eq_top_of_mul_eq_smul _ K cartanF4_inv fun s => ⟨s, pow_one s⟩)

theorem ggOutdiagCyclic_E8 :
    GGOutdiagCyclic (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 8) K false))
      (LargeEvenChevIDImage (LargeEvenCartanE 8) K (LargeEvenChevH (LargeEvenCartanE 8) K false)) :=
  ggOutdiagCyclic_chevalley_of_top (τ := .E8) K
    (torusSubgroup_eq_top_of_mul_eq_smul _ K cartanE8_inv fun s => ⟨s, pow_one s⟩)

theorem exists_sq_eq_of_charTwo [Finite K] [CharP K 2] (s : Kˣ) : ∃ u : Kˣ, u ^ 2 = s := by
  obtain ⟨t, ht⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (s : K)
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact s.ne_zero (by rw [ht, mul_zero])
  exact ⟨Units.mk0 t ht0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, ht, sq])⟩

theorem ggOutdiagCyclic_E7 [Finite K] [CharP K 2] :
    GGOutdiagCyclic (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) K false))
      (LargeEvenChevIDImage (LargeEvenCartanE 7) K (LargeEvenChevH (LargeEvenCartanE 7) K false)) :=
  ggOutdiagCyclic_chevalley_of_top (τ := .E7) K
    (torusSubgroup_eq_top_of_mul_eq_smul _ K cartanE7_adj (exists_sq_eq_of_charTwo K))

theorem ggOutdiagCyclic_E6 [Finite K] :
    GGOutdiagCyclic (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false))
      (LargeEvenChevIDImage (LargeEvenCartanE 6) K (LargeEvenChevH (LargeEvenCartanE 6) K false)) :=
  ggOutdiagCyclic_chevID (torusSubgroup (LargeEvenCartanE 6) K)
    (fun _ ht => diagHom_mem_of_mem_torusSubgroup .E6 K ht)
    (fun a a' _ _ h => exists_pow_mem_torusE6 K a a' h)

end Untwisted

end TableB

end CFSG.StandardType
