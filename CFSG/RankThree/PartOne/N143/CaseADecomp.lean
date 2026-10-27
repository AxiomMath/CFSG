module

public import CFSG.RankThree.PartOne.N143.CaseALines

public section

namespace CFSG.RankThree.PartOne.N143

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {J : Subgroup G}
  {Ps : Subgroup (MulAut A)} {zs : MulAut A}

omit [Finite G] in
theorem Aline_decomp (hspec : HessianSpec p A Ps zs) {y : G}
    (hy : y ∈ Subgroup.normalizer (A : Set G))
    (hmem : A.normalizerMonoidHom ⟨y, hy⟩ ∈ Aline A J Ps zs) :
    ∃ (w : G) (_ : w ∈ J) (hw : w ∈ Subgroup.normalizer (A : Set G)) (n : ℕ),
      A.normalizerMonoidHom ⟨w, hw⟩ ∈ Ps ∧
      A.normalizerMonoidHom ⟨y, hy⟩ = A.normalizerMonoidHom ⟨w, hw⟩ * zs ^ n := by
  obtain ⟨j, hj, n, hjn⟩ := mem_Aline hspec hmem
  obtain ⟨w, hwJ, hw, rfl⟩ := Sec12Three.mem_torusImage_iff.1 hj.1
  exact ⟨w, hwJ, hw, n, hj.2, hjn⟩

omit [Finite G] in
theorem action_of_decomp {k : ℕ} (hk : ∀ a : A, zs a = a ^ k) {y w : G}
    (hy : y ∈ Subgroup.normalizer (A : Set G)) (hw : w ∈ Subgroup.normalizer (A : Set G)) (n : ℕ)
    (hyw : A.normalizerMonoidHom ⟨y, hy⟩ = A.normalizerMonoidHom ⟨w, hw⟩ * zs ^ n) :
    ∀ a ∈ A, y * a * y⁻¹ = w * a ^ (k ^ n) * w⁻¹ := by
  intro a ha
  have h1 := congrArg (fun φ : MulAut A => ((φ ⟨a, ha⟩ : A) : G)) hyw
  have e1 : ((A.normalizerMonoidHom ⟨y, hy⟩ ⟨a, ha⟩ : A) : G) = y * a * y⁻¹ := rfl
  have e2 : (((A.normalizerMonoidHom ⟨w, hw⟩ * zs ^ n) ⟨a, ha⟩ : A) : G) =
      w * (((zs ^ n) ⟨a, ha⟩ : A) : G) * w⁻¹ := rfl
  simp only [e1, e2] at h1
  rw [h1, pow_apply_of_apply hk n ⟨a, ha⟩]
  rfl

theorem JGood.mem_normalizer_of_decomp (h : JGood p A c J) {k : ℕ} (hk : ∀ a : A, zs a = a ^ k)
    {y w : G} (hy : y ∈ Subgroup.normalizer (A : Set G)) (hw : w ∈ Subgroup.normalizer (A : Set G))
    (hwJ : w ∈ J) (n : ℕ)
    (hyw : A.normalizerMonoidHom ⟨y, hy⟩ = A.normalizerMonoidHom ⟨w, hw⟩ * zs ^ n) :
    y ∈ Subgroup.normalizer (J : Set G) := by
  have hu : w⁻¹ * y ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hw) hy
  have hπu : A.normalizerMonoidHom ⟨w⁻¹ * y, hu⟩ = zs ^ n := by
    have : (⟨w⁻¹ * y, hu⟩ : Subgroup.normalizer (A : Set G)) = ⟨w, hw⟩⁻¹ * ⟨y, hy⟩ := rfl
    rw [this, map_mul, map_inv, hyw, inv_mul_cancel_left]
  have hs : IsScalarOn A (w⁻¹ * y) := ⟨k ^ n, fun a ha => by
    have h2 := congrArg (fun φ : MulAut A => ((φ ⟨a, ha⟩ : A) : G)) hπu
    have e1 : ((A.normalizerMonoidHom ⟨w⁻¹ * y, hu⟩ ⟨a, ha⟩ : A) : G) =
        (w⁻¹ * y) * a * (w⁻¹ * y)⁻¹ := rfl
    simp only [e1] at h2
    rw [h2, pow_apply_of_apply hk n ⟨a, ha⟩]
    rfl⟩
  have := h.mem_normalizer_mul_of_scalar hwJ hu hs
  simpa using this

theorem nine_dvd_two_pow_sub_one {f : ℕ} (h3 : 3 ∣ f) (hq : 2 ^ f % 3 = 1) : 9 ∣ 2 ^ f - 1 := by
  obtain ⟨m, rfl⟩ := h3
  have h8 : 2 ^ (3 * m) = 8 ^ m := by rw [pow_mul]; norm_num
  rw [h8] at hq ⊢
  rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have h64 : 8 ^ (k + k) = 64 ^ k := by rw [← two_mul, pow_mul]; norm_num
    rw [h64]
    have h63 : 64 - 1 ∣ 64 ^ k - 1 ^ k := Nat.sub_dvd_pow_sub_pow 64 1 k
    simp only [one_pow] at h63
    exact (show 9 ∣ 64 - 1 by norm_num).trans h63
  · exfalso
    have h64 : 8 ^ (2 * k + 1) = 8 * 64 ^ k := by rw [pow_succ, pow_mul]; norm_num; ring
    rw [h64, Nat.mul_mod, Nat.pow_mod] at hq
    norm_num at hq

end CFSG.RankThree.PartOne.N143
