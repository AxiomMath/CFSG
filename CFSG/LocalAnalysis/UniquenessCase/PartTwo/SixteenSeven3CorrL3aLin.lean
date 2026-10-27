module

public import CFSG.Quasithin.Background.Module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

private lemma mem_fixV_zpowers_iff {W : Type} [CommGroup W] {f : MulAut W} {x : W} :
    x ∈ fixV (Subgroup.zpowers f) ↔ f x = x := by
  rw [mem_fixV]
  constructor
  · intro h
    exact h f (Subgroup.mem_zpowers f)
  · intro h g hg
    have hle : Subgroup.zpowers f ≤ MulAction.stabilizer (MulAut W) x := by
      rw [Subgroup.zpowers_le]
      simpa [MulAction.mem_stabilizer_iff, MulAut.smul_def] using h
    simpa [MulAut.smul_def] using hle hg

private lemma card_sup_mul_card_inf {W : Type} [CommGroup W] (H K : Subgroup W) :
    Nat.card (H ⊔ K : Subgroup W) * Nat.card (H ⊓ K : Subgroup W) =
      Nat.card H * Nat.card K := by
  have h1 := Subgroup.relIndex_mul_card (H := H) (K := H ⊔ K)
  have h2 := Subgroup.relIndex_mul_card (H := H) (K := K)
  have h3 : H.relIndex (H ⊔ K) = H.relIndex K :=
    Subgroup.relIndex_sup_left (H := K) (K := H)
  have h4 : H ⊓ (H ⊔ K) = H := inf_eq_left.mpr le_sup_left
  rw [h4, h3] at h1
  rw [← h1, mul_comm (H.relIndex K) (Nat.card H), mul_assoc, h2]

theorem s16c167_fixV_sup_index_le_two {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ x : W, x * x = 1) (hcard : Nat.card W = 2 ^ 6) {z c d : MulAut W}
    (hz3 : z * z * z = 1) (hzfix : ∀ x : W, z x = x → x = 1)
    (hc2 : c * c = 1) (hc1 : c ≠ 1) (hcz : c * z = z * c)
    (hd2 : d * d = 1) (hdz : d * z = z⁻¹ * d) :
    (fixV (Subgroup.zpowers c) ⊔ fixV (Subgroup.zpowers d)).index ≤ 2 := by
  classical
  haveI : Fintype W := Fintype.ofFinite W
  have hz3w : ∀ w : W, z (z (z w)) = w := by
    intro w
    have h := congrArg (fun g : MulAut W => g w) hz3
    simpa [MulAut.mul_apply] using h
  have hz_inv : z⁻¹ = z * z := by
    have h : z * (z * z) = 1 := by rw [← mul_assoc]; exact hz3
    exact inv_eq_of_mul_eq_one_right h
  have hz_inv_w : ∀ w : W, z⁻¹ w = z (z w) := by
    intro w
    simp [hz_inv]
  have hWinv : ∀ w : W, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_right (hW w)
  have hc_apply : ∀ w : W, c (c w) = w := by
    intro w
    have h := congrArg (fun g : MulAut W => g w) hc2
    simpa [MulAut.mul_apply] using h
  have hcz_apply : ∀ w : W, c (z w) = z (c w) := by
    intro w
    have h := congrArg (fun g : MulAut W => g w) hcz
    simpa [MulAut.mul_apply] using h
  have hN : ∀ w : W, z w * z (z w) = w := by
    intro w
    have hfix : z (w * z w * z (z w)) = w * z w * z (z w) := by
      simp only [map_mul, hz3w w]
      ac_rfl
    have h1 : w * z w * z (z w) = 1 := hzfix _ hfix
    rw [mul_assoc] at h1
    exact mul_left_cancel (h1.trans (hW w).symm)
  set C : Subgroup W := fixV (Subgroup.zpowers c) with hC
  set K : Subgroup W := fixV (Subgroup.zpowers d) with hK
  have memC : ∀ x : W, x ∈ C ↔ c x = x := by
    intro x; rw [hC]; exact mem_fixV_zpowers_iff
  have memK : ∀ x : W, x ∈ K ↔ d x = x := by
    intro x; rw [hK]; exact mem_fixV_zpowers_iff
  let φ : W →* W := MonoidHom.id W * (c : W →* W)
  have hφx : ∀ x : W, φ x = x * c x := fun x => rfl
  set R : Subgroup W := φ.range with hR
  have hker : φ.ker = C := by
    ext x
    rw [MonoidHom.mem_ker, hφx, memC]
    constructor
    · intro h
      have hx : x⁻¹ = c x := mul_eq_one_iff_inv_eq.mp h
      rw [← hx, hWinv x]
    · intro hc
      rw [hc]
      exact hW x
  have hCR : Nat.card C * Nat.card R = 2 ^ 6 := by
    have h := Subgroup.card_ker_mul_card_range φ
    rwa [hker, ← hR, hcard] at h
  have hRleC : R ≤ C := by
    intro y hy
    rw [hR, MonoidHom.mem_range] at hy
    obtain ⟨x, rfl⟩ := hy
    rw [memC, hφx, map_mul, hc_apply x]
    exact mul_comm (c x) x
  have hRC : Nat.card R ≤ Nat.card C := Subgroup.card_le_of_le hRleC
  have hR8 : Nat.card R ≤ 8 := by
    have hsq : Nat.card R ^ 2 ≤ 8 ^ 2 := by
      rw [show (8 : ℕ) ^ 2 = 2 ^ 6 by norm_num]
      calc Nat.card R ^ 2 = Nat.card R * Nat.card R := by rw [pow_two]
        _ ≤ Nat.card C * Nat.card R := Nat.mul_le_mul_right _ hRC
        _ = 2 ^ 6 := hCR
    exact (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  have hzR : ∀ y ∈ R, z y ∈ R := by
    intro y hy
    rw [hR, MonoidHom.mem_range] at hy ⊢
    obtain ⟨x, rfl⟩ := hy
    exact ⟨z x, by rw [hφx, hφx, map_mul, hcz_apply x]⟩
  let f : Function.End R := fun y => ⟨z y.1, hzR y.1 y.2⟩
  have hf3 : f ^ 3 = 1 := by
    funext y
    apply Subtype.ext
    show z (z (z y.1)) = y.1
    exact hz3w y.1
  have hfixF : Fintype.card (Function.fixedPoints f) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨(1 : R), ?_⟩, fun y => ?_⟩
    · show f (1 : R) = 1
      apply Subtype.ext
      show z (1 : W) = 1
      simp
    · apply Subtype.ext
      apply Subtype.ext
      simpa using hzfix (y.1).1 (congrArg Subtype.val y.2)
  have hmodR : Nat.card R ≡ 1 [MOD 3] := by
    have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) hf3
    rw [hfixF] at hmod
    rwa [Fintype.card_eq_nat_card] at hmod
  have hdvdR : Nat.card R ∣ 2 ^ 6 := by
    rw [← hcard]
    exact Subgroup.card_subgroup_dvd_card R
  have hR4 : Nat.card R ≤ 4 := by
    obtain ⟨k, hk6, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvdR
    have hm : 2 ^ k ≡ 1 [MOD 3] := hk ▸ hmodR
    have h8 : 2 ^ k ≤ 8 := hk ▸ hR8
    interval_cases k
    · rw [hk]; norm_num
    · exact absurd hm (by decide)
    · rw [hk]; norm_num
    · exact absurd hm (by decide)
    · exact absurd h8 (by norm_num)
    · exact absurd h8 (by norm_num)
    · exact absurd h8 (by norm_num)
  have hC16 : 16 ≤ Nat.card C := by
    have h4 : Nat.card C * Nat.card R ≤ Nat.card C * 4 := Nat.mul_le_mul_left _ hR4
    rw [hCR, show (2 : ℕ) ^ 6 = 64 by norm_num] at h4
    omega
  let e : MulAut W := z * z
  have he_apply : ∀ w : W, e w = z (z w) := fun w => rfl
  have he_eq_inv : e = z⁻¹ := hz_inv.symm
  have hd_apply : ∀ w : W, d (d w) = w := by
    intro w
    have h := congrArg (fun g : MulAut W => g w) hd2
    simpa [MulAut.mul_apply] using h
  have hdz_apply : ∀ w : W, d (z w) = z⁻¹ (d w) := by
    intro w
    have h := congrArg (fun g : MulAut W => g w) hdz
    simpa [MulAut.mul_apply] using h
  have hzder : z * d = d * z⁻¹ := by
    have h : z * d * z = d := by
      calc z * d * z = z * (d * z) := by rw [mul_assoc]
        _ = z * (z⁻¹ * d) := by rw [hdz]
        _ = z * z⁻¹ * d := by rw [mul_assoc]
        _ = d := by rw [mul_inv_cancel, one_mul]
    calc z * d = z * d * 1 := (mul_one _).symm
      _ = z * d * (z * z⁻¹) := by rw [mul_inv_cancel, mul_one]
      _ = z * d * z * z⁻¹ := by ac_rfl
      _ = d * z⁻¹ := by rw [h]
  have hdze : d * z⁻¹ = z * d := hzder.symm
  have hdze_apply : ∀ w : W, d (z⁻¹ w) = z (d w) := by
    intro w
    have h := congrArg (fun g : MulAut W => g w) hdze
    simpa [MulAut.mul_apply] using h
  have hde : ∀ w : W, d (e w) = z (d w) := by
    intro w
    rw [he_eq_inv]
    exact hdze_apply w
  have hdze' : ∀ w : W, d (z w) = e (d w) := by
    intro w
    rw [hdz_apply w, ← he_eq_inv]
  have hda : ∀ w : W, w * d w ∈ K := by
    intro w
    rw [memK, map_mul, hd_apply w, mul_comm]
  have hdb : ∀ w : W, z w * d (z w) ∈ K := by
    intro w
    rw [memK, map_mul, hd_apply (z w), mul_comm]
  have hdc : ∀ w : W, e (w * d w) * (z w * d (z w)) = w := by
    intro w
    have hY : e (d w) * e (d w) = 1 := hW (e (d w))
    calc e (w * d w) * (z w * d (z w))
        = e w * e (d w) * (z w * e (d w)) := by rw [map_mul, hdze' w]
      _ = e w * z w := by
            rw [← mul_one (e w * z w), ← hY]
            ac_rfl
      _ = w := by rw [he_apply w, mul_comm, hN w]
  have hdecomp : ∀ w : W, ∃ a ∈ K, ∃ b ∈ K, e a * b = w :=
    fun w => ⟨w * d w, hda w, z w * d (z w), hdb w, hdc w⟩
  set K' : Subgroup W := K.map (e : W →* W) with hK'
  have hK'card : Nat.card K' = Nat.card K := by
    rw [hK']
    exact Subgroup.card_map_of_injective (K := K) (f := (e : W →* W)) e.injective
  have hsup : K' ⊔ K = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨a, haK, b, hbK, hw⟩ := hdecomp w
    rw [← hw]
    refine mul_mem (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right hbK)
    rw [hK']
    exact Subgroup.mem_map.mpr ⟨a, haK, rfl⟩
  have hdisj : K' ⊓ K = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro u hu
    rw [Subgroup.mem_inf] at hu
    obtain ⟨huK', huK⟩ := hu
    rw [memK] at huK
    rw [hK', Subgroup.mem_map] at huK'
    obtain ⟨k, hkK, hkEq⟩ := huK'
    rw [memK] at hkK
    rw [← hkEq] at huK
    change d (e k) = e k at huK
    have h1 : d (e k) = z k := by rw [hde k, hkK]
    rw [h1] at huK
    have hzk : z k = z (z k) := by
      rwa [he_eq_inv, hz_inv_w k] at huK
    have hzz : z (z k) = k := by
      have h := congrArg z hzk
      rwa [hz3w k] at h
    rw [← hkEq, hzfix k (hzk.trans hzz)]
    simp
  have hK8 : Nat.card K = 8 := by
    have hprod := card_sup_mul_card_inf K' K
    rw [hsup, hdisj] at hprod
    rw [Subgroup.card_top, Subgroup.card_bot, hcard, hK'card] at hprod
    rw [mul_one] at hprod
    have hsq : Nat.card K ^ 2 = 8 ^ 2 := by
      rw [show (8 : ℕ) ^ 2 = 2 ^ 6 by norm_num, hprod, pow_two]
    exact Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) hsq
  have hKC : ¬ K ≤ C := by
    intro hKC'
    have hcea : ∀ a ∈ K, c (e a) = e a := by
      intro a haK
      have hca : c a = a := (memC a).mp (hKC' haK)
      rw [he_apply a, hcz_apply (z a), hcz_apply a, hca]
    have hcb : ∀ b ∈ K, c b = b := fun b hbK => (memC b).mp (hKC' hbK)
    have hcone : c = 1 := by
      ext w
      rw [MulAut.one_apply]
      obtain ⟨a, haK, b, hbK, hw⟩ := hdecomp w
      rw [← hw, map_mul, hcea a haK, hcb b hbK]
    exact hc1 hcone
  have hCK4 : Nat.card (C ⊓ K : Subgroup W) ≤ 4 := by
    have hdvd : Nat.card (C ⊓ K : Subgroup W) ∣ 2 ^ 3 := by
      rw [show (2 : ℕ) ^ 3 = Nat.card K by rw [hK8]; norm_num]
      exact Subgroup.card_dvd_of_le (inf_le_right : C ⊓ K ≤ K)
    obtain ⟨j, hj3, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hj]
    interval_cases j
    · norm_num
    · norm_num
    · norm_num
    · exfalso
      have hEq : C ⊓ K = K := by
        apply Subgroup.eq_of_le_of_card_ge (inf_le_right : C ⊓ K ≤ K)
        rw [hj, hK8]
        norm_num
      exact hKC (hEq ▸ inf_le_left)
  have hA32 : 32 ≤ Nat.card (C ⊔ K : Subgroup W) := by
    have h3 : 16 * 8 ≤ Nat.card (C ⊔ K : Subgroup W) * Nat.card (C ⊓ K : Subgroup W) := by
      rw [card_sup_mul_card_inf C K, hK8]
      nlinarith [hC16]
    have h4 : Nat.card (C ⊔ K : Subgroup W) * Nat.card (C ⊓ K : Subgroup W) ≤
        Nat.card (C ⊔ K : Subgroup W) * 4 :=
      Nat.mul_le_mul_left _ hCK4
    have h5 : 16 * 8 ≤ Nat.card (C ⊔ K : Subgroup W) * 4 := h3.trans h4
    omega
  have hindex : Nat.card (C ⊔ K : Subgroup W) * (C ⊔ K).index = 2 ^ 6 := by
    rw [Subgroup.card_mul_index, hcard]
  have hfin : 32 * (C ⊔ K).index ≤ 64 := by
    calc 32 * (C ⊔ K).index ≤ Nat.card (C ⊔ K : Subgroup W) * (C ⊔ K).index :=
          Nat.mul_le_mul_right _ hA32
      _ = 2 ^ 6 := hindex
      _ = 64 := by norm_num
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
