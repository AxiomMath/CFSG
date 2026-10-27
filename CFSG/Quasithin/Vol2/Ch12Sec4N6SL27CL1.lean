module

public import CFSG.Quasithin.Vol2.Ch12Sec4N6SL27Gamma
public import CFSG.Quasithin.Vol2.Ch12Sec4N6L1

public section

namespace CFSG.Quasithin.H13

namespace N1246

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.L3 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem card_sl_three_two : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem conjAct_mul_mem {V : Subgroup G} {x y : G} (hx : x ∈ Subgroup.normalizer (V : Set G))
    (hy : y ∈ Subgroup.normalizer (V : Set G)) :
    conjAct V ⟨x * y, Subgroup.mul_mem _ hx hy⟩ = conjAct V ⟨x, hx⟩ * conjAct V ⟨y, hy⟩ :=
  map_mul (conjAct V) ⟨x, hx⟩ ⟨y, hy⟩

theorem inv_mul_mem_pCore {V L : Subgroup G} [IsMulCommutative ↥V] {x y : G}
    (hxL : x ∈ L) (hyL : y ∈ L) (hx : x ∈ Subgroup.normalizer (V : Set G))
    (hy : y ∈ Subgroup.normalizer (V : Set G))
    (h : conjAct V ⟨x, hx⟩ = conjAct V ⟨y, hy⟩)
    (hO : L ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 L) :
    x⁻¹ * y ∈ pCoreOf 2 L := by
  have hN : x⁻¹ * y ∈ Subgroup.normalizer (V : Set G) := Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hy
  have h1 : conjAct V ⟨x⁻¹ * y, hN⟩ = 1 := by
    have e : (⟨x⁻¹ * y, hN⟩ : Subgroup.normalizer (V : Set G)) = ⟨x, hx⟩⁻¹ * ⟨y, hy⟩ := rfl
    rw [e, map_mul, map_inv, ← h, inv_mul_cancel]
  have h2 : x⁻¹ * y ∈ Subgroup.centralizer (V : Set G) := A4.conjAct_eq_one_iff.1 h1
  exact hO ⟨L.mul_mem (L.inv_mem hxL) hyL, h2⟩

namespace Ctx

variable {T L V E : Subgroup G} {z v : G} [IsMulCommutative ↥V] (c : Ctx T L V E z v)
include c

theorem two_elt_mem_L1_mul (w : G) (hw : w ∈ L ⊓ Subgroup.centralizer (E : Set G)) {k : ℕ}
    (hwk : w ^ 2 ^ k = 1) : ∃ n ∈ c.L1, ∃ p ∈ pCoreOf 2 L, w = n * p := by
  classical
  obtain ⟨D⟩ := c.nat.toL3Coord
  have hwL : w ∈ L := (Subgroup.mem_inf.1 hw).1
  have hwN : w ∈ Subgroup.normalizer (V : Set G) := c.f.normalizes hwL
  obtain ⟨τ, hτ, hτc, hτ3⟩ := c.image_CLE D hw
  have hcv : c.cv D ≠ 0 := c.cv_ne D
  have hτpow : τ ^ 2 ^ k = 1 := by
    apply D.rho_injective
    rw [map_pow, hτ, map_one, ← map_pow]
    have h1 : (⟨w, hwN⟩ : Subgroup.normalizer (V : Set G)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using hwk)
    rw [h1, map_one]
  have hτ8 : τ ^ 8 = 1 := by
    have h1 : orderOf τ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hτpow
    have h2 : orderOf τ ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
      orderOf_dvd_natCard τ
    rw [card_sl_three_two] at h2
    have h3 : orderOf τ ∣ 8 := by
      refine (Nat.dvd_gcd h1 h2).trans ?_
      obtain ⟨i, hi, hg⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Nat.gcd_dvd_left (2 ^ k) 168)
      rw [hg]
      have hi3 : i ≤ 3 := by
        by_contra hcon
        push Not at hcon
        have h4 : 2 ^ 4 ∣ 2 ^ i := pow_dvd_pow 2 hcon
        have h5 : 2 ^ i ∣ 168 := hg ▸ Nat.gcd_dvd_right (2 ^ k) 168
        exact absurd (h4.trans h5) (by norm_num)
      exact (pow_dvd_pow 2 hi3 : 2 ^ i ∣ 2 ^ 3)
    exact orderOf_dvd_iff_pow_eq_one.1 h3
  by_cases hτ1 : τ = 1
  · have hC : conjAct V ⟨w, hwN⟩ = 1 := by rw [← hτ, hτ1, map_one]
    have hwC : w ∈ Subgroup.centralizer (V : Set G) := A4.conjAct_eq_one_iff.1 hC
    exact ⟨1, Subgroup.one_mem _, w, c.inf_centralizer_le_pCore ⟨hwL, hwC⟩, (one_mul w).symm⟩
  obtain ⟨a, haL1, ha3, haV⟩ := c.exists_a
  have haC : a ∈ L ⊓ Subgroup.centralizer (E : Set G) := c.L1_le haL1
  have haL : a ∈ L := (Subgroup.mem_inf.1 haC).1
  have haN : a ∈ Subgroup.normalizer (V : Set G) := c.f.normalizes haL
  obtain ⟨δ, hδ, hδc, -⟩ := c.image_CLE D haC
  have hδ3 : δ * δ * δ = 1 := by
    apply D.rho_injective
    rw [map_mul, map_mul, hδ, ← map_mul, ← map_mul, map_one]
    have hA : (⟨a, haN⟩ : Subgroup.normalizer (V : Set G)) * ⟨a, haN⟩ * ⟨a, haN⟩ = 1 :=
      Subtype.ext ha3
    rw [hA, map_one]
  have hδ1 : δ ≠ 1 := by
    intro h
    apply haV
    have h1 : conjAct V ⟨a, haN⟩ = 1 := by rw [← hδ, h, map_one]
    exact A4.conjAct_eq_one_iff.1 h1
  have hτAS : τ ∈ L3.AS {0, c.cv D} := SL27.gamma_two_mem_AS (c.cv D) hcv τ hτ8 hτc hτ3
  have hτS : τ ∈ ASsub (c.cv D) hcv := mem_ASsub.2 hτAS
  have hwC : w ∈ Subgroup.centralizer (E : Set G) := (Subgroup.mem_inf.1 hw).2
  have hwa : w * a * w⁻¹ ∈ c.L1 :=
    (Subgroup.mem_normalizer_iff.1 (c.CE_le_N_L1 hwC) a).1 haL1
  have hn1L1 : w * a * w⁻¹ * a⁻¹ ∈ c.L1 := c.L1.mul_mem hwa (c.L1.inv_mem haL1)
  have hn1N : w * a * w⁻¹ * a⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hwN haN) (Subgroup.inv_mem _ hwN))
      (Subgroup.inv_mem _ haN)
  obtain ⟨t, ht⟩ : ∃ t : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      t = τ * δ * τ⁻¹ * δ⁻¹ := ⟨_, rfl⟩
  have hD1 : D.rho t = conjAct V ⟨w * a * w⁻¹ * a⁻¹, hn1N⟩ := by
    have e : (⟨w * a * w⁻¹ * a⁻¹, hn1N⟩ : Subgroup.normalizer (V : Set G)) =
        ⟨w, hwN⟩ * ⟨a, haN⟩ * ⟨w, hwN⟩⁻¹ * ⟨a, haN⟩⁻¹ := rfl
    rw [ht, e]
    simp only [map_mul, map_inv]
    rw [hτ, hδ]
  have htS : t ∈ ASsub (c.cv D) hcv := by
    have h1 : δ * τ⁻¹ * δ⁻¹ ∈ ASsub (c.cv D) hcv :=
      mem_ASsub.2 (as_normal (c.cv D) hcv δ hδc τ⁻¹ (mem_ASsub.1 ((ASsub (c.cv D) hcv).inv_mem hτS)))
    have e : t = τ * (δ * τ⁻¹ * δ⁻¹) := by rw [ht]; group
    rw [e]
    exact (ASsub (c.cv D) hcv).mul_mem hτS h1
  have htAS : t ∈ L3.AS {0, c.cv D} := mem_ASsub.1 htS
  have ht1 : t ≠ 1 := by
    intro h
    apply SL27.gamma_AS_noncomm (c.cv D) hcv δ hδc hδ3 hδ1 τ hτAS hτ1
    calc τ * δ = t * (δ * τ) := by rw [ht]; group
      _ = δ * τ := by rw [h, one_mul]
  obtain ⟨t', ht'⟩ : ∃ t' : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), t' = δ * t * δ⁻¹ :=
    ⟨_, rfl⟩
  have ht'S : t' ∈ ASsub (c.cv D) hcv :=
    mem_ASsub.2 (by rw [ht']; exact as_normal (c.cv D) hcv δ hδc t htAS)
  have ht'AS : t' ∈ L3.AS {0, c.cv D} := mem_ASsub.1 ht'S
  have ht'1 : t' ≠ 1 := by
    intro h
    apply ht1
    calc t = δ⁻¹ * (δ * t * δ⁻¹) * δ := by group
      _ = 1 := by rw [← ht', h]; group
  have hne : t ≠ t' := by
    intro h
    apply SL27.gamma_AS_noncomm (c.cv D) hcv δ hδc hδ3 hδ1 t htAS ht1
    calc t * δ = t' * δ := by rw [← h]
      _ = δ * t := by rw [ht']; group
  have hn2L1 : a * (w * a * w⁻¹ * a⁻¹) * a⁻¹ ∈ c.L1 :=
    c.L1.mul_mem (c.L1.mul_mem haL1 hn1L1) (c.L1.inv_mem haL1)
  have hn2N : a * (w * a * w⁻¹ * a⁻¹) * a⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ haN hn1N) (Subgroup.inv_mem _ haN)
  have hD2 : D.rho t' = conjAct V ⟨a * (w * a * w⁻¹ * a⁻¹) * a⁻¹, hn2N⟩ := by
    have e : (⟨a * (w * a * w⁻¹ * a⁻¹) * a⁻¹, hn2N⟩ : Subgroup.normalizer (V : Set G)) =
        ⟨a, haN⟩ * ⟨w * a * w⁻¹ * a⁻¹, hn1N⟩ * ⟨a, haN⟩⁻¹ := rfl
    rw [ht', e]
    simp only [map_mul, map_inv]
    rw [hδ, hD1]
  have final : ∀ n : G, n ∈ c.L1 → ∀ hn : n ∈ Subgroup.normalizer (V : Set G),
      D.rho τ = conjAct V ⟨n, hn⟩ → ∃ n ∈ c.L1, ∃ p ∈ pCoreOf 2 L, w = n * p := by
    intro n hnL1 hn hD
    have hnL : n ∈ L := (Subgroup.mem_inf.1 (c.L1_le hnL1)).1
    have hc : conjAct V ⟨n, hn⟩ = conjAct V ⟨w, hwN⟩ := hD.symm.trans hτ
    exact ⟨n, hnL1, n⁻¹ * w,
      inv_mul_mem_pCore hnL hwL hn hwN hc c.inf_centralizer_le_pCore,
      (mul_inv_cancel_left n w).symm⟩
  have hcase := SL27.gamma_AS_three (c.cv D) hcv t htAS t' ht'AS τ hτAS ht1 ht'1 hne hτ1
  rcases hcase with h | h | h
  · exact final _ hn1L1 hn1N (by rw [h]; exact hD1)
  · exact final _ hn2L1 hn2N (by rw [h]; exact hD2)
  · refine final _ (c.L1.mul_mem hn1L1 hn2L1) (Subgroup.mul_mem _ hn1N hn2N) ?_
    rw [h, map_mul, hD1, hD2]
    exact (conjAct_mul_mem hn1N hn2N).symm

theorem inf_centralizer_E_mem_L1_mul {x : G} (hx : x ∈ L ⊓ Subgroup.centralizer (E : Set G)) :
    ∃ n ∈ c.L1, ∃ p ∈ pCoreOf 2 L, x = n * p := by
  obtain ⟨D⟩ := c.nat.toL3Coord
  obtain ⟨a, haL1, ha3, haV⟩ := c.exists_a
  have haC : a ∈ L ⊓ Subgroup.centralizer (E : Set G) := c.L1_le haL1
  obtain ⟨i, k, hk⟩ := c.L1_gen D haC ha3 haV hx
  have hw : a⁻¹ ^ i * x ∈ L ⊓ Subgroup.centralizer (E : Set G) :=
    (L ⊓ Subgroup.centralizer (E : Set G)).mul_mem
      ((L ⊓ Subgroup.centralizer (E : Set G)).pow_mem
        ((L ⊓ Subgroup.centralizer (E : Set G)).inv_mem haC) i) hx
  obtain ⟨n, hn, p, hp, hw'⟩ := c.two_elt_mem_L1_mul (a⁻¹ ^ i * x) hw hk
  refine ⟨a ^ i * n, c.L1.mul_mem (c.L1.pow_mem haL1 i) hn, p, hp, ?_⟩
  calc x = a ^ i * (a⁻¹ ^ i * x) := by group
    _ = a ^ i * (n * p) := by rw [hw']
    _ = a ^ i * n * p := (mul_assoc _ _ _).symm

end Ctx

end N1246

end CFSG.Quasithin.H13
