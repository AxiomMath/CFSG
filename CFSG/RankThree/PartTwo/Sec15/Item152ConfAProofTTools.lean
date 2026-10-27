module

import CFSG.RankThree.PartTwo.Sec10.Item109
public import CFSG.RankThree.PartTwo.Sec15.Item152Proof
public import CFSG.RankThree.PartTwo.Sec6.Item612Basic
import CFSG.RankThree.Native.DerivedGenerators
import Certificates.Data.A5

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

namespace Proof152ConfA

set_option maxRecDepth 100000 in
theorem alt5_not_normalizes_five : ∀ x y : alternatingGroup (Fin 5), x ≠ 1 → x ^ 3 = 1 →
    y ≠ 1 → y ^ 5 = 1 →
      x * y * x⁻¹ ≠ y ∧ x * y * x⁻¹ ≠ y ^ 2 ∧ x * y * x⁻¹ ≠ y ^ 3 ∧ x * y * x⁻¹ ≠ y ^ 4 := by
  decide

theorem not_normalizes_five_of_mulEquiv {Γ : Type*} [Group Γ]
    (e : Γ ≃* alternatingGroup (Fin 5)) {x y : Γ} (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hy1 : y ≠ 1)
    (hy5 : y ^ 5 = 1) : x * y * x⁻¹ ∉ Subgroup.zpowers y := by
  intro hmem
  have hyo : orderOf y = 5 := orderOf_eq_prime hy5 hy1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hk' : y ^ (k % 5) = x * y * x⁻¹ := by
    rw [← hk, show (5 : ℤ) = (orderOf y : ℤ) by rw [hyo]; rfl, zpow_mod_orderOf]
  have h0 : 0 ≤ k % 5 := Int.emod_nonneg _ (by norm_num)
  have h5 : k % 5 < 5 := Int.emod_lt_of_pos _ (by norm_num)
  obtain ⟨j, hj⟩ : ∃ j : ℕ, k % 5 = j := ⟨(k % 5).toNat, (Int.toNat_of_nonneg h0).symm⟩
  rw [hj, zpow_natCast] at hk'
  obtain ⟨h1, h2, h3, h4⟩ := alt5_not_normalizes_five (e x) (e y) (by simpa using hx1)
    (by rw [← map_pow, hx3, map_one]) (by simpa using hy1) (by rw [← map_pow, hy5, map_one])
  have hj5 : j < 5 := by omega
  have he : e (x * y * x⁻¹) = e y ^ j := by rw [← hk', map_pow]
  rw [map_mul, map_mul, map_inv] at he
  interval_cases j
  · rw [pow_zero] at he
    apply hy1
    have : e x * e y = e x := by
      calc e x * e y = e x * e y * (e x)⁻¹ * e x := by group
        _ = e x := by rw [he, one_mul]
    exact e.injective (by rw [map_one]; exact mul_eq_left.mp this)
  · exact h1 (he.trans (pow_one _))
  · exact h2 he
  · exact h3 he
  · exact h4 he

variable {G : Type} [Group G] [Finite G]

theorem oTwoOddIn_le_theta {X : Subgroup G}
    (hXs : IsSimpleGroup (↥X ⧸ aschbacherSolvableCore 3 ↥X))
    (hX60 : Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) = 60) :
    oTwoOddIn X ≤ inSubgroup (aschbacherSolvableCore 3) X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 ↥X with hθ
  obtain ⟨-, -, -, -, -, -, hθO⟩ :=
    solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three
  have hO2θ : CFSG.pCore 2 ↥X ≤ θ := hθO 2 Nat.prime_two (by norm_num)
  set φ : ↥X ⧸ CFSG.pCore 2 ↥X →* ↥X ⧸ θ :=
    QuotientGroup.map (CFSG.pCore 2 ↥X) θ (MonoidHom.id _) hO2θ with hφ
  have hφs : Function.Surjective φ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective θ q
    exact ⟨QuotientGroup.mk x, rfl⟩
  set F := CFSG.oddCore (↥X ⧸ CFSG.pCore 2 ↥X) with hF
  have hFn : (F.map φ).Normal := (CFSG.oddCore_normal _).map φ hφs
  have hFodd : Odd (Nat.card (F.map φ)) :=
    Odd.of_dvd_nat Sec10.odd_card_oddCore (Subgroup.card_map_dvd _ _)
  have hbot : F.map φ = ⊥ := by
    rcases hFn.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      rw [h, Subgroup.card_top, hX60] at hFodd
      exact (Nat.not_odd_iff_even.mpr (by decide)) hFodd
  rintro _ ⟨y, hy, rfl⟩
  have hy' : φ (QuotientGroup.mk' (CFSG.pCore 2 ↥X) y) ∈ F.map φ := ⟨_, hy, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hy'
  exact ⟨y, (QuotientGroup.eq_one_iff y).mp hy', rfl⟩

theorem oTwoP_le_oTwoOddIn {X : Subgroup G} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (Sec4.oTwoP p ↥X).map X.subtype ≤ oTwoOddIn X := by
  refine Subgroup.map_mono (Subgroup.comap_mono (le_sSup ⟨CFSG.pCore_normal, ?_⟩))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
    (CFSG.pCore_isPGroup (p := p) (G := ↥X ⧸ CFSG.pCore 2 ↥X))
  rw [hk]
  exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow

theorem le_theta_of_le_sylow {X R P : Subgroup G} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hXs : IsSimpleGroup (↥X ⧸ aschbacherSolvableCore 3 ↥X))
    (hX60 : Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) = 60)
    (hR : CFSG.ABGLocalTools.IsSylowOf p R ((Sec4.oTwoP p ↥X).map X.subtype)) (hPR : P ≤ R) :
    P ≤ inSubgroup (aschbacherSolvableCore 3) X := by
  obtain ⟨S, rfl⟩ := hR
  exact hPR.trans ((Subgroup.map_subtype_le _).trans
    ((oTwoP_le_oTwoOddIn hp2).trans (oTwoOddIn_le_theta hXs hX60)))

omit [Finite G] in
theorem inf_eq_bot_of_isPGroup {T P : Subgroup G} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hT : IsPGroup 2 T) (hP : IsPGroup p P) : T ⊓ P = ⊥ := by
  rw [eq_bot_iff]
  intro g ⟨hg2, hgp⟩
  rw [Subgroup.mem_bot]
  obtain ⟨a, ha⟩ := hT ⟨g, hg2⟩
  obtain ⟨b, hb⟩ := hP ⟨g, hgp⟩
  have ha' : g ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hb' : g ^ p ^ b = 1 := by simpa using congrArg Subtype.val hb
  have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ha') (orderOf_dvd_of_pow_eq_one hb')
  rw [(Nat.coprime_pow_primes a b Nat.prime_two Fact.out (Ne.symm hp2)).gcd_eq_one, Nat.dvd_one,
    orderOf_eq_one_iff] at h1
  exact h1

omit [Finite G] in
theorem card_coe_mul_eq {T P : Subgroup G} (hTP : T ⊓ P = ⊥) :
    Nat.card ((T : Set G) * (P : Set G)) = Nat.card T * Nat.card P := by
  rw [Subgroup.card_mul_eq_card_subgroup_mul_card_quotient P (T : Set G), mul_comm]
  congr 1
  rw [Nat.card_image_of_injOn]
  · rfl
  · intro a ha b hb hab
    have h1 : a⁻¹ * b ∈ P := QuotientGroup.eq.mp hab
    have h2 : a⁻¹ * b ∈ T := T.mul_mem (T.inv_mem ha) hb
    have h3 : a⁻¹ * b ∈ T ⊓ P := ⟨h2, h1⟩
    rw [hTP, Subgroup.mem_bot] at h3
    exact (eq_of_inv_mul_eq_one h3)

theorem exists_mem_normalizer_not_mem_theta {X T P : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hTX : T ≤ X) (hT2 : IsPGroup 2 T) (hPp : IsPGroup p P)
    (hPθ : P ≤ inSubgroup (aschbacherSolvableCore 3) X)
    (hTP : ((T ⊔ P : Subgroup G) : Set G) = (T : Set G) * (P : Set G))
    {t : G} (htT : t ∈ T) (htθ : t ∉ inSubgroup (aschbacherSolvableCore 3) X) :
    ∃ n ∈ T ⊓ Subgroup.normalizer (P : Set G), n ∉ inSubgroup (aschbacherSolvableCore 3) X := by
  set θX := inSubgroup (aschbacherSolvableCore 3) X with hθX
  set H := T ⊔ P with hH
  have hTP1 := inf_eq_bot_of_isPGroup hp2 hT2 hPp
  have hHcard : Nat.card H = Nat.card T * Nat.card P := by
    rw [← card_coe_mul_eq hTP1, ← hTP]
    rfl
  set M := H ⊓ θX with hM
  have hPM : P ≤ M := le_inf le_sup_right hPθ
  have htH : t ∈ H := (le_sup_left : T ≤ H) htT
  have htX : t ∈ X := hTX htT
  set P₁ := P.map (MulAut.conj t).toMonoidHom with hP₁
  have hP₁M : P₁ ≤ M := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨H.mul_mem (H.mul_mem htH ((le_sup_right : P ≤ H) hy)) (H.inv_mem htH), ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta X htX) y).mp (hPθ hy)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hPp
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hT2
  have hMfac : (Nat.card M).factorization p = n := by
    have h1 : p ^ n ∣ Nat.card M := hn ▸ Subgroup.card_dvd_of_le hPM
    have h2 : Nat.card M ∣ 2 ^ m * p ^ n := by
      rw [← hm, ← hn, ← hHcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hp : p.Prime := Fact.out
    have hM0 : Nat.card M ≠ 0 := Nat.card_pos.ne'
    refine le_antisymm ?_ ((Nat.Prime.pow_dvd_iff_le_factorization hp hM0).mp h1)
    have hne : 2 ^ m * p ^ n ≠ 0 :=
      Nat.mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hp.ne_zero)
    have h3 := (Nat.factorization_le_iff_dvd hM0 hne).mpr h2 p
    have hfac2 : (2 ^ m * p ^ n).factorization p = n := by
      rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hp.ne_zero),
        Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
        Nat.Prime.factorization_pow hp]
      simp [Ne.symm hp2]
    rw [hfac2] at h3
    exact h3
  have hcard : Nat.card (P.subgroupOf M) = p ^ (Nat.card M).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv, hn, hMfac]
  have hcard₁ : Nat.card (P₁.subgroupOf M) = p ^ (Nat.card M).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₁M).toEquiv, hP₁,
      Subgroup.card_map_of_injective (MulAut.conj t).injective, hn, hMfac]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M (Sylow.ofCard _ hcard) (Sylow.ofCard _ hcard₁)
  have hgH : (g : G) ∈ ((H : Set G)) := g.2.1
  rw [hTP] at hgH
  obtain ⟨t'', ht'', y, hy, hgy⟩ := hgH
  have hle : P.map (MulAut.conj (t''⁻¹ * t)).toMonoidHom ≤ P := by
    rintro _ ⟨z, hz, rfl⟩
    have hz₁ : (⟨t * z * t⁻¹, hP₁M ⟨z, hz, rfl⟩⟩ : M) ∈
        ((Sylow.ofCard _ hcard₁ : Sylow p M) : Subgroup M) :=
      Subgroup.mem_subgroupOf.mpr ⟨z, hz, rfl⟩
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hz₁
    have h1 := Subgroup.mem_subgroupOf.mp hz₁
    have h2 : (((MulAut.conj g)⁻¹ • (⟨t * z * t⁻¹, hP₁M ⟨z, hz, rfl⟩⟩ : M) : M) : G) =
        (g : G)⁻¹ * (t * z * t⁻¹) * g := by
      rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply]
      simp
    rw [h2, ← hgy] at h1
    have h3 : y * ((t'' * y)⁻¹ * (t * z * t⁻¹) * (t'' * y)) * y⁻¹ ∈ P :=
      P.mul_mem (P.mul_mem hy h1) (P.inv_mem hy)
    have h4 : y * ((t'' * y)⁻¹ * (t * z * t⁻¹) * (t'' * y)) * y⁻¹ =
        (t''⁻¹ * t) * z * (t''⁻¹ * t)⁻¹ := by group
    rw [h4] at h3
    exact h3
  have hN : t''⁻¹ * t ∈ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj _).injective]
  refine ⟨t''⁻¹ * t, ⟨T.mul_mem (T.inv_mem ht'') htT, hN⟩, fun hθ => htθ ?_⟩
  have hgθ : (g : G) ∈ θX := g.2.2
  have ht''θ : t'' ∈ θX := by
    have : t'' = (g : G) * y⁻¹ := by rw [← hgy]; group
    rw [this]
    exact θX.mul_mem hgθ (θX.inv_mem (hPθ hy))
  have : t = t'' * (t''⁻¹ * t) := by group
  rw [this]
  exact θX.mul_mem ht''θ hθ

theorem card_frattini_quotient_eq {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (h : (CFSG.IsElementaryAbelian p P ∧ Nat.card P = p ^ 2) ∨
      (CFSG.IsExtraspecialPGroup p P ∧ Nat.card P = p ^ 3)) :
    Nat.card (P ⧸ frattini P) = p ^ 2 := by
  rcases h with ⟨hE, hc⟩ | ⟨hX, hc⟩
  · have : Fact (IsPGroup p P) := ⟨IsPGroup.of_card hc⟩
    have hbot : frattini P = ⊥ := CFSG.frattini_eq_bot_of_isElementaryAbelian (p := p)
    rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hbot).toEquiv,
      Nat.card_congr (QuotientGroup.quotientBot (G := P)).toEquiv, hc]
  · have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini P)
    rw [hX.2.2.1, hX.2.2.2, hc] at h1
    rw [hX.2.2.1]
    have hp : 0 < p := (Fact.out : p.Prime).pos
    have h2 : Nat.card (P ⧸ Subgroup.center P) * p = p ^ 2 * p := by rw [← h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hp h2

end Proof152ConfA

end CFSG.RankThree.PartTwo.Sec15
