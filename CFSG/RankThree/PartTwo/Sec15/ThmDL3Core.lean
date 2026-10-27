module

public import CFSG.RankThree.PartTwo.Sec15.ThmDFrattini
public import CFSG.RankThree.PartTwo.Sec15.ThmDA10Core

public section

namespace CFSG.RankThree.PartTwo.Sec15.ThmD

open Subgroup

theorem l3_fusion_core {M : Type*} [Group M] [Finite M] (N Y A : Subgroup M) [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) (hNY : N ≤ Y) (hA3 : IsPGroup 3 A)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (c : M) (hc : c ∈ A)
    (hAdec : ∀ a ∈ A, ∃ a₁ ∈ A ⊓ Y, ∃ i : ℕ, a = a₁ * c ^ i)
    (Ω : Set (Subgroup M)) (hcΩ : zpowers c ∈ Ω)
    (hΩinv : ∀ m ∈ normalizer (A : Set M), ∀ F ∈ Ω, F.map (MulAut.conj m).toMonoidHom ∈ Ω)
    (hfus : ∃ r ∈ (A ⊓ Y).map (QuotientGroup.mk' N),
      (∀ k : ℕ, ∃ y ∈ Y.map (QuotientGroup.mk' N),
        (∀ a ∈ (A ⊓ Y).map (QuotientGroup.mk' N), y * a = a * y) ∧
          y * QuotientGroup.mk' N c * y⁻¹ = QuotientGroup.mk' N c * r ^ k) ∧
      ∀ B' : Subgroup (M ⧸ N), B' ≤ (A ⊓ Y).map (QuotientGroup.mk' N) ⊔ zpowers (QuotientGroup.mk' N c) →
        Nat.card B' = 9 →
        (∃ t ∈ Y.map (QuotientGroup.mk' N), orderOf t = 2 ∧ ∀ b ∈ B', t * b = b * t) →
        ∃ k : ℕ, QuotientGroup.mk' N c * r ^ k ∈ B')
    (B : Subgroup M) (hBA : B ≤ A) (hB9 : Nat.card B = 9) (hBΩ : ∀ F ∈ Ω, ¬ F ≤ B)
    (p : M) (hpY : p ∈ Y) (hpB : ∀ b ∈ B, p * b = b * p) (hp2 : ∃ k : ℕ, p ^ 2 ^ k = 1) :
    p ∈ N := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hp2
  have hAN : A ⊓ N = ⊥ := inf_eq_bot_of_isPGroup_of_not_dvd hN hA3
  have hinj : ∀ a ∈ A, QuotientGroup.mk' N a = 1 → a = 1 := by
    intro a ha h
    have : a ∈ A ⊓ N := ⟨ha, (QuotientGroup.eq_one_iff a).mp h⟩
    rw [hAN] at this
    exact this
  have hinj2 : ∀ a ∈ A, ∀ b ∈ A, QuotientGroup.mk' N a = QuotientGroup.mk' N b → a = b := by
    intro a ha b hb h
    have h1 : QuotientGroup.mk' N (a⁻¹ * b) = 1 := by
      rw [map_mul, map_inv, h, inv_mul_cancel]
    exact inv_mul_eq_one.mp (hinj _ (A.mul_mem (A.inv_mem ha) hb) h1)
  by_contra hpN
  have hqne : QuotientGroup.mk' N p ≠ 1 := fun h => hpN ((QuotientGroup.eq_one_iff p).mp h)
  have hq2 : (QuotientGroup.mk' N p) ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hq2)
  have hj0 : j ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hj
    exact hqne (orderOf_eq_one_iff.mp hj)
  have hdvd : 2 ^ (j - 1) ∣ orderOf (QuotientGroup.mk' N p) := by
    rw [hj]
    exact pow_dvd_pow 2 (Nat.sub_le j 1 |>.trans (le_refl _) |> fun _ => Nat.pred_le j)
  have ht : orderOf ((QuotientGroup.mk' N p) ^ 2 ^ (j - 1)) = 2 := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num)) hdvd, hj]
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    simp [pow_succ]
  set mk := QuotientGroup.mk' N with hmk
  set q := mk p with hq
  set t := q ^ 2 ^ (j - 1) with htdef
  have htK : t ∈ Y.map mk := (Y.map mk).pow_mem (Subgroup.mem_map_of_mem mk hpY) _
  have htcomm : ∀ b ∈ B.map mk, t * b = b * t := by
    rintro _ ⟨b, hb, rfl⟩
    have h1 : q * mk b = mk b * q := by rw [hq, ← map_mul, ← map_mul, hpB b hb]
    exact (Commute.pow_left (show Commute q (mk b) from h1) _).eq
  have hBle : B.map mk ≤ (A ⊓ Y).map mk ⊔ zpowers (mk c) := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨a₁, ha₁, i, rfl⟩ := hAdec b (hBA hb)
    rw [map_mul, map_pow]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem mk ha₁))
      (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) i))
  have hcardB : Nat.card (B.map mk) = 9 := (card_map_of_injOn mk hBA hinj).trans hB9
  obtain ⟨r, hr, hfa, hfb⟩ := hfus
  obtain ⟨k', hk'⟩ := hfb (B.map mk) hBle hcardB ⟨t, htK, ht, htcomm⟩
  obtain ⟨y, hyK, hyc, hyx⟩ := hfa k'
  obtain ⟨y₀, hy₀Y, hy₀⟩ := hyK
  have hxr : mk c * r ^ k' ∈ A.map mk := by
    refine (A.map mk).mul_mem (Subgroup.mem_map_of_mem mk hc) ((A.map mk).pow_mem ?_ _)
    exact Subgroup.map_mono inf_le_left hr
  have hy : ∀ a ∈ A, mk (y₀ * a * y₀⁻¹) ∈ A.map mk := by
    intro a ha
    obtain ⟨a₁, ha₁, i, rfl⟩ := hAdec a ha
    have hc1 : y * mk a₁ = mk a₁ * y := hyc (mk a₁) (Subgroup.mem_map_of_mem mk ha₁)
    have hc2 : y * mk a₁ * y⁻¹ = mk a₁ := by rw [hc1]; group
    have e1 : mk (y₀ * (a₁ * c ^ i) * y₀⁻¹) = mk a₁ * (mk c * r ^ k') ^ i := by
      rw [map_mul, map_mul, map_inv, map_mul, map_pow, hy₀]
      calc y * (mk a₁ * mk c ^ i) * y⁻¹ = (y * mk a₁ * y⁻¹) * (y * mk c ^ i * y⁻¹) := by group
        _ = mk a₁ * (y * mk c ^ i * y⁻¹) := by rw [hc2]
        _ = mk a₁ * (y * mk c * y⁻¹) ^ i := by rw [conj_pow]
        _ = mk a₁ * (mk c * r ^ k') ^ i := by rw [hyx]
    rw [e1]
    exact (A.map mk).mul_mem (Subgroup.mem_map_of_mem mk ha₁.1) ((A.map mk).pow_mem hxr i)
  obtain ⟨m', hm', hm'k⟩ := exists_normalizer_lift hN hA3 hAab y₀ hy
  obtain ⟨rt, hrt, hrtr⟩ := hr
  have hc''A : c * rt ^ k' ∈ A := A.mul_mem hc (A.pow_mem hrt.1 _)
  have hmkc'' : mk (c * rt ^ k') = mk c * r ^ k' := by rw [map_mul, map_pow, hrtr]
  have hc'A : m' * c * m'⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hm' c).mp hc
  have hmkc' : mk (m' * c * m'⁻¹) = mk c * r ^ k' := by
    rw [hm'k c hc, map_mul, map_mul, map_inv, hy₀, hyx]
  have hcc : m' * c * m'⁻¹ = c * rt ^ k' := hinj2 _ hc'A _ hc''A (by rw [hmkc', hmkc''])
  obtain ⟨b, hb, hbk⟩ := hk'
  have hbc : b = c * rt ^ k' := hinj2 b (hBA hb) _ hc''A (by rw [hbk, hmkc''])
  have hΩ' : zpowers (m' * c * m'⁻¹) ∈ Ω := by
    have : zpowers (m' * c * m'⁻¹) = (zpowers c).map (MulAut.conj m').toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      simp [MulAut.conj_apply]
    rw [this]
    exact hΩinv m' hm' _ hcΩ
  exact hBΩ _ hΩ' (Subgroup.zpowers_le.mpr (by rw [hcc, ← hbc]; exact hb))

end CFSG.RankThree.PartTwo.Sec15.ThmD
