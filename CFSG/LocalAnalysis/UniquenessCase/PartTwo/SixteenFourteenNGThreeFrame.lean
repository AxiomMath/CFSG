module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGThreeLines
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGThreeBlocks
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGThreeStab

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open

theorem s1614_torus_frame {W : Type} [CommGroup W] [Finite W] (hW : ∀ x : W, x * x = 1)
    (hcard : Nat.card W = 2 ^ 6) {L M : Subgroup (MulAut W)} (hL : IsPOnePlusTwo 3 ↥L)
    (hMN : M ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hA : ∃ A : Subgroup (MulAut W), A ≤ M ∧ IsElemAbelian 3 A ∧ Nat.card ↥A = 27)
    {t : MulAut W} (ht : t ∈ M) (ht2 : t * t = 1) :
    ∃ Y : Fin 3 → Subgroup W, iSupIndep Y ∧ Function.Injective Y ∧ ⨆ i, Y i = ⊤ ∧
      (∀ i, rk ↥(Y i) = 2) ∧ (∀ i, ∃ j, (Y i).map t.toMonoidHom = Y j) ∧
      ∀ i, ∃ B : Subgroup (MulAut W), B ≤ M ∧ IsPGroup 3 ↥B ∧ ¬ IsCyclic ↥B ∧
        ∀ y ∈ Y i, y ∈ fixV B := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hext : CFSG.IsExtraspecial 3 ↥L := hL.1
  have hLcard : Nat.card ↥L = 27 := by
    rw [hL.2.1]
    norm_num
  haveI : Finite ↥L := Nat.finite_of_card_ne_zero (by rw [hLcard]; norm_num)
  have hZcard : Nat.card (Subgroup.center ↥L) = 3 := CFSG.IsExtraspecial.center_order_p 3 ↥L
  obtain ⟨ℓ, hℓ, hℓ1⟩ : ∃ ℓ : ↥L, ℓ ∈ Subgroup.center ↥L ∧ ℓ ≠ 1 := by
    have hnt : Nontrivial (Subgroup.center ↥L) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hZcard]
      norm_num
    obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne (1 : Subgroup.center ↥L)
    exact ⟨x, hx, fun h => hx1 (Subtype.ext h)⟩
  have hnc : ∃ a b : ↥L, a * b ≠ b * a := by
    by_contra h
    have hall : ∀ a b : ↥L, a * b = b * a := fun a b => by
      by_contra hab
      exact h ⟨a, b, hab⟩
    have htop : Subgroup.center ↥L = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact Subgroup.mem_center_iff.2 fun g => hall g x
    rw [htop, Subgroup.card_top, hLcard] at hZcard
    omega
  obtain ⟨⟨e, he3, htℓ⟩, A, hAM, hAab, hA27, hℓA, g, hgA, hgL, hgℓ, a, b, ha, htg⟩ :=
    s1614_lines hW hcard hL hMN hℓ hℓ1 hA ht ht2
  have hℓ3 : ℓ ^ 3 = 1 := hL.2.2 ℓ
  have hℓord : orderOf ℓ = 3 := orderOf_eq_prime hℓ3 hℓ1
  have hZeq : Subgroup.center ↥L = Subgroup.zpowers ℓ := by
    refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
    · rw [Subgroup.zpowers_le]
      exact hℓ
    · rw [hZcard, Nat.card_zpowers, hℓord]
  have hz3 : (ℓ : MulAut W) * (ℓ : MulAut W) * (ℓ : MulAut W) = 1 := by
    have h := congrArg (fun y : ↥L => (y : MulAut W)) hℓ3
    simpa [Subgroup.coe_pow, pow_three'] using h
  have hg3 : g * g * g = 1 := by
    have h := congrArg (fun y : ↥L => (y : MulAut W)) (hL.2.2 ⟨g, hgL⟩)
    simpa [Subgroup.coe_pow, pow_three'] using h
  have hgz : g * (ℓ : MulAut W) = (ℓ : MulAut W) * g := by
    have h := congrArg (fun y : ↥L => (y : MulAut W))
      (Subgroup.mem_center_iff.1 hℓ ⟨g, hgL⟩)
    simpa [Subgroup.coe_mul] using h
  have hzfix : ∀ x : W, (ℓ : MulAut W) x = x → x = 1 := fun x hx =>
    s16c167_central_fixed_point_free hW hcard hL hℓ hℓ1 hx
  have hg'nc : (⟨g, hgL⟩ : ↥L) ∉ Subgroup.center ↥L := by
    intro hmem
    rw [hZeq] at hmem
    apply hgℓ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have h := congrArg (fun y : ↥L => (y : MulAut W)) hk
    simp only [Subgroup.coe_zpow] at h
    exact Subgroup.mem_zpowers_iff.2 ⟨k, h⟩
  obtain ⟨y, hy⟩ : ∃ y : ↥L, y * ⟨g, hgL⟩ ≠ ⟨g, hgL⟩ * y := by
    by_contra h
    apply hg'nc
    rw [Subgroup.mem_center_iff]
    intro y
    by_contra hy
    exact h ⟨y, hy⟩
  obtain ⟨c, hcc, hc3, hyc⟩ :=
    CFSG.RankThree.PartTwo.Sec4.RonanK432.exists_commutator_data hLcard hnc ⟨g, hgL⟩ y
  have hc1 : c ≠ 1 := by
    rintro rfl
    exact hy (by simpa using hyc)
  have hcZ : c ∈ Subgroup.center ↥L := Subgroup.mem_center_iff.2 hcc
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hZeq ▸ hcZ)
  obtain ⟨s, hcs⟩ : ∃ s : ℕ, c = ℓ ^ s := by
    refine ⟨(k % 3).toNat, ?_⟩
    have hnn : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
    rw [← hk, zpow_eq_zpow_emod' k hℓ3, ← zpow_natCast, Int.toNat_of_nonneg hnn]
    norm_num
  have hs : ¬ 3 ∣ s := by
    rintro ⟨m, hm⟩
    apply hc1
    rw [hcs, hm, pow_mul, hℓ3, one_pow]
  have hyz : (y : MulAut W) * (ℓ : MulAut W) = (ℓ : MulAut W) * (y : MulAut W) := by
    have h := congrArg (fun x : ↥L => (x : MulAut W)) (Subgroup.mem_center_iff.1 hℓ y)
    simpa [Subgroup.coe_mul] using h
  have hyg' : (y : MulAut W) * g = g * (y : MulAut W) * (ℓ : MulAut W) ^ s := by
    have h := congrArg (fun x : ↥L => (x : MulAut W)) hyc
    rw [hcs] at h
    simpa [Subgroup.coe_mul, Subgroup.coe_pow] using h
  have hyg : (y : MulAut W) * g * (y : MulAut W)⁻¹ = g * (ℓ : MulAut W) ^ s := by
    rw [mul_inv_eq_iff_eq_mul, hyg', mul_assoc g, (Commute.pow_right hyz s).eq, ← mul_assoc]
  have hweights := s1614_weights hW hz3 hg3 hgz hzfix
  have hrank : ∀ j : Fin 3,
      rk ↥(fixV (Subgroup.zpowers (g * (ℓ : MulAut W) ^ (j : ℕ)))) = 2 :=
    fun j => s1614_blocks_rank hW hcard hz3 hg3 hgz hzfix hyz hs hyg j
  have hh : ∀ j : Fin 3, g * (ℓ : MulAut W) ^ (j : ℕ) ∈ A := fun j =>
    A.mul_mem hgA (A.pow_mem hℓA j)
  refine ⟨fun j : Fin 3 => fixV (Subgroup.zpowers (g * (ℓ : MulAut W) ^ (j : ℕ))),
    hweights.1, ?_, hweights.2, hrank, ?_, ?_⟩
  · refine hweights.1.injective fun j hbot => ?_
    have h := hrank j
    rw [hbot, rk_bot] at h
    omega
  · intro j
    exact s1614_blocks_perm hz3 hg3 hgz ha htg htℓ j
  · intro j
    obtain ⟨B, hBA, hB3, hBnc, hBfix⟩ := s1614_blocks_stab hW hAab hA27 (hh j) (hrank j)
    exact ⟨B, hBA.trans hAM, hB3, hBnc, hBfix⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
