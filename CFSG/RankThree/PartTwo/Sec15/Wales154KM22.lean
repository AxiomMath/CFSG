module

public import CFSG.RankThree.PartTwo.Sec15.Wales154KFacts
import CFSG.GH74.Generic.S45.LSporMathB
import CFSG.RankThree.PartTwo.Sec16.Item16Res9ProofA10
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22

public section

namespace CFSG.RankThree.PartTwo.Sec15.Wales154

open Subgroup CFSG.Blueprint CFSG.ComponentClassification

private theorem card_fix_congr {Q R : Type*} [Group Q] [Group R] (e : Q ≃* R) (α : MulAut Q) :
    Nat.card {q : Q // α q = q} = Nat.card {r : R // MulAut.congr e α r = r} :=
  Nat.card_congr (e.toEquiv.subtypeEquiv fun q => by simp)

private theorem card_fix_m22
    {Q : Type*} [Group Q] (e : Q ≃* NativeSporadic.M22) {α : MulAut Q} (hα : α * α = 1)
    (hα1 : α ≠ 1) :
    Nat.card {q : Q // α q = q} = 384 ∨ Nat.card {q : Q // α q = q} = 320 ∨
      Nat.card {q : Q // α q = q} = 1344 := by
  rw [card_fix_congr e α]
  refine GH74.Generic.S45.m22_fixed_card _ ?_ ?_
  · rw [← map_mul, hα, map_one]
  · intro h
    exact hα1 ((MulAut.congr e).injective (h.trans (map_one _).symm))

private theorem card_fix_conj_m22
    {Q : Type*} [Group Q] (e : Q ≃* NativeSporadic.M22) {t : Q} (ht : orderOf t = 2) :
    Nat.card {q : Q // MulAut.conj t q = q} = 384 := by
  rw [card_fix_congr e, OuterAutomorphisms.congr_conj]
  have ht2 : e t * e t = 1 := by rw [← map_mul, ← sq, ← ht, pow_orderOf_eq_one, map_one]
  refine GH74.Generic.S45.m22_inner_fixed_card _ ?_ ?_ (MonoidHom.mem_range.mpr ⟨e t, rfl⟩)
  · rw [← map_mul, ht2, map_one]
  · intro h
    have hZ : e t ∈ Subgroup.center NativeSporadic.M22 := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun σ : MulAut NativeSporadic.M22 => σ g) h
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc g * e t = e t * g * (e t)⁻¹ * e t := by rw [h1]
        _ = e t * g := by group
    rw [Sporadic.Schreier.m22_center_eq_bot', Subgroup.mem_bot, map_eq_one_iff _ e.injective]
      at hZ
    rw [hZ, orderOf_one] at ht
    exact absurd ht (by norm_num)

theorem ks154M22A7 :
    KS154M22A7 := by
  intro Q _ hQ K _ h35 P hP hKP
  obtain ⟨e⟩ := hQ
  classical
  have : Finite Q := Finite.of_equiv _ e.toEquiv.symm
  have : Finite (MulAut Q) :=
    Finite.of_injective (fun f : MulAut Q => (f : Q → Q)) DFunLike.coe_injective
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hcard : Nat.card Q = 443520 :=
    (Nat.card_congr e.toEquiv).trans Sporadic.Schreier.m22_card
  set c : Q →* MulAut Q := MulAut.conj with hc
  have hcZ : ∀ q : Q, c q = 1 → q = 1 := by
    intro q hq
    have hqZ : q ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun σ : MulAut Q => σ g) hq
      simp only [hc, MulAut.conj_apply, MulAut.one_apply] at h1
      calc g * q = q * g * q⁻¹ * q := by rw [h1]
        _ = q * g := by group
    have hZ := OuterAutomorphisms.center_map_equiv e
    rw [Sporadic.Schreier.m22_center_eq_bot'] at hZ
    rw [(Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hZ, Subgroup.mem_bot] at hqZ
    exact hqZ
  have hinv : ∀ t g : Q, orderOf t = 2 → t * g = g * t → orderOf g ∣ 384 := by
    intro t g ht htg
    have h384 := card_fix_conj_m22 e ht
    have hg : g ∈ Sporadic.Schreier.fixSub (MulAut.conj t) := by
      rw [Sporadic.Schreier.mem_fixSub, MulAut.conj_apply, htg, mul_inv_cancel_right]
    have hF : Nat.card (Sporadic.Schreier.fixSub (MulAut.conj t)) = 384 :=
      (Nat.card_congr (Equiv.subtypeEquivRight fun _ => Sporadic.Schreier.mem_fixSub)).trans
        h384
    exact hF ▸ Subgroup.orderOf_dvd_natCard _ hg
  obtain ⟨⟨y, hyK⟩, hy⟩ := exists_prime_orderOf_dvd_card' (G := K) 7 (dvd_trans (by norm_num) h35)
  obtain ⟨⟨x, hxK⟩, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 5 (dvd_trans (by norm_num) h35)
  rw [Subgroup.orderOf_mk] at hy hx
  set S : Subgroup Q := (P ⊓ c.range).comap c with hS
  have hS2 : IsPGroup 2 S := by
    rintro ⟨s, hs⟩
    rw [hS, Subgroup.mem_comap] at hs
    obtain ⟨n, hn⟩ := hP ⟨c s, (Subgroup.mem_inf.mp hs).1⟩
    refine ⟨n, Subtype.ext ?_⟩
    have h1 : c (s ^ 2 ^ n) = 1 := by
      rw [map_pow]
      simpa using congrArg Subtype.val hn
    simpa using hcZ _ h1
  have hKS : K ≤ normalizer (S : Set Q) := by
    rw [Subgroup.le_normalizer_iff]
    intro k hk s hs
    rw [hS, Subgroup.mem_comap] at hs ⊢
    refine Subgroup.mem_inf.mpr ⟨?_, ⟨k * s * k⁻¹, rfl⟩⟩
    rw [map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp (hKP k hk) (c s)).mp (Subgroup.mem_inf.mp hs).1
  have hmod : ∀ g ∈ K, ∀ p : ℕ, p.Prime → orderOf g = p → ¬ p ∣ 384 →
      Nat.card S ≡ 1 [MOD p] := by
    intro g hgK p hp hgp hp384
    have : Fact p.Prime := ⟨hp⟩
    have hD : IsPGroup p (zpowers g) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hgp, pow_one])
    have hDS : zpowers g ≤ normalizer (S : Set Q) := zpowers_le.mpr (hKS hgK)
    have h1 := Sec16.Res9A10.card_modEq_card_inf_centralizer hD hDS
    have h2 : S ⊓ centralizer ((zpowers g : Subgroup Q) : Set Q) = ⊥ := by
      by_contra hne
      have hW2 : IsPGroup 2 (S ⊓ centralizer ((zpowers g : Subgroup Q) : Set Q) :
          Subgroup Q) := hS2.to_le inf_le_left
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hW2
      have hm0 : m ≠ 0 := by
        rintro rfl
        exact hne (Subgroup.eq_bot_of_card_eq _ (by rw [hm, pow_zero]))
      obtain ⟨⟨t, htW⟩, ht⟩ := exists_prime_orderOf_dvd_card' 2
        (by rw [hm]; exact dvd_pow_self 2 hm0)
      rw [Subgroup.orderOf_mk] at ht
      have htg : t * g = g * t :=
        Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp htW).2 g (mem_zpowers g) |>.symm
      exact hp384 (hgp ▸ hinv t g ht htg)
    rwa [h2, Subgroup.card_bot] at h1
  have hSbot : S = ⊥ := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS2
    have h7 := hmod y hyK 7 (by norm_num) hy (by norm_num)
    have h5 := hmod x hxK 5 (by norm_num) hx (by norm_num)
    have hdvd : 2 ^ n ∣ 443520 := hn ▸ hcard ▸ Subgroup.card_subgroup_dvd_card S
    have hn7 : n ≤ 7 := by
      by_contra h
      push Not at h
      have h8 : 2 ^ 8 ∣ 443520 := (pow_dvd_pow 2 h).trans hdvd
      norm_num at h8
    rw [hn] at h7 h5
    have hn0 : n = 0 := by
      interval_cases n <;> first | rfl | (exfalso; revert h7 h5; decide)
    exact Subgroup.eq_bot_of_card_eq _ (by rw [hn, hn0, pow_zero])
  have hfix : ∀ σ ∈ P, ∀ k ∈ K, σ k = k := by
    intro σ hσ k hk
    have h1 : c (σ k * k⁻¹) ∈ P := by
      have h : c (σ k * k⁻¹) = σ * (c k * σ⁻¹ * (c k)⁻¹) := by
        ext z
        simp [hc, MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, mul_assoc]
      rw [h]
      exact P.mul_mem hσ ((mem_normalizer_iff.mp (hKP k hk) σ⁻¹).mp (P.inv_mem hσ))
    have h2 : σ k * k⁻¹ ∈ S := by
      rw [hS, Subgroup.mem_comap]
      exact Subgroup.mem_inf.mpr ⟨h1, ⟨σ k * k⁻¹, rfl⟩⟩
    rw [hSbot, Subgroup.mem_bot, mul_inv_eq_one] at h2
    exact h2
  by_contra hne
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.eq_bot_of_card_eq _ (by rw [hm, pow_zero]))
  obtain ⟨⟨τ, hτP⟩, hτ⟩ := exists_prime_orderOf_dvd_card' 2
    (by rw [hm]; exact dvd_pow_self 2 hm0)
  rw [Subgroup.orderOf_mk] at hτ
  have hτ2 : τ * τ = 1 := by rw [← sq, ← hτ, pow_orderOf_eq_one]
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hτ
    exact absurd hτ (by norm_num)
  have hKF : K ≤ Sporadic.Schreier.fixSub τ := fun k hk =>
    Sporadic.Schreier.mem_fixSub.mpr (hfix τ hτP k hk)
  have hF : Nat.card (Sporadic.Schreier.fixSub τ) = Nat.card {q : Q // τ q = q} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => Sporadic.Schreier.mem_fixSub)
  have h := dvd_trans h35 (Subgroup.card_dvd_of_le hKF)
  rw [hF] at h
  rcases card_fix_m22 e hτ2 hτ1 with h' | h' | h' <;> rw [h'] at h <;> norm_num at h

end CFSG.RankThree.PartTwo.Sec15.Wales154
