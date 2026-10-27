module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKR
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBOddLA

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph
open scoped commutatorElement Pointwise

private theorem fixesA_of_centralizes_nsbodd {G : Type} [Group G] {T L I K : Subgroup G}
    {m n j : ℕ} {α : ↥K →* GL (Fin n) (ZMod 2)}
    {β : ↥(uZero I K) →* Multiplicative (Fin j → Fin n → ZMod 2)}
    (hequi : ∀ (x : ↥K) (u v : ↥(uZero I K)), (v : G) = x * u * (x : G)⁻¹ → ∀ i : Fin j,
      Multiplicative.toAdd (β v) i =
        ((α x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
          (Multiplicative.toAdd (β u) i))
    (hV2 : ∀ a : Fin n, a.val < m → ∃ v : ↥(uZero I K), (v : G) ∈ vV T L ∧
      ∃ i : Fin j, Multiplicative.toAdd (β v) i = Pi.single a 1)
    (y : ↥K) (hy : ∀ v ∈ vV T L, v * (y : G) = (y : G) * v) :
    FixesA m ((α y : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  intro a ha
  obtain ⟨v, hvV, i, hi⟩ := hV2 a ha
  have hconj : (v : G) = (y : G) * (v : G) * (y : G)⁻¹ := by
    rw [← hy (v : G) hvV, mul_inv_cancel_right]
  have h := hequi y v v hconj i
  rw [hi] at h
  exact h.symm

private theorem lowerBlock2_pow_nsbodd {n m : ℕ} (h : n = m + 2) (g : GL (Fin n) (ZMod 2))
    (hg : FixesA m (g : Matrix (Fin n) (Fin n) (ZMod 2))) (k : ℕ) :
    FixesA m ((g ^ k : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) ∧
      lowerBlock2 h ((g ^ k : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
        lowerBlock2 h (g : Matrix (Fin n) (Fin n) (ZMod 2)) ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero, Units.val_one]
    exact ⟨fixesA_one m, lowerBlock2_one h⟩
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hmul : ((g ^ (k + 1) : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
        ((g ^ k : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *
          (g : Matrix (Fin n) (Fin n) (ZMod 2)) := by
      rw [pow_succ, Units.val_mul]
    rw [hmul]
    exact ⟨fixesA_mul ih1 hg, by rw [lowerBlock2_mul h ih1 hg, ih2, pow_succ]⟩

private theorem eq_one_of_sq_pow_odd_nsbodd {D : Matrix (Fin 2) (Fin 2) (ZMod 2)} {d : ℕ}
    (hD : D * D = 1) (hd : Odd d) (hpow : D ^ d = 1) : D = 1 := by
  obtain ⟨e, rfl⟩ := hd
  have h1 : D ^ (2 * e + 1) = D := by
    rw [pow_succ, pow_mul, sq, hD, one_pow, one_mul]
  exact h1.symm.trans hpow

private theorem comm_of_conj_nsbodd {D E τ : Matrix (Fin 2) (Fin 2) (ZMod 2)} (hED : E * D = 1)
    (hτ1 : τ ≠ 1) (hor : D * τ * E = 1 ∨ D * τ * E = τ) : D * τ = τ * D := by
  have hτE : D * τ * E = τ := by
    rcases hor with h1 | h1
    · exfalso
      apply hτ1
      calc τ = (E * D) * τ * (E * D) := by rw [hED, one_mul, mul_one]
        _ = E * (D * τ * E) * D := by simp only [mul_assoc]
        _ = 1 := by rw [h1, mul_one, hED]
    · exact h1
  calc D * τ = D * τ * E * D := by simp only [mul_assoc, hED, mul_one]
    _ = τ * D := by rw [hτE]

private theorem eq_one_of_block_nsbodd {n m : ℕ} (h : n = m + 2) (g : GL (Fin n) (ZMod 2))
    (hg : FixesA m (g : Matrix (Fin n) (Fin n) (ZMod 2))) (hodd : Odd (orderOf g))
    (τ : Matrix (Fin 2) (Fin 2) (ZMod 2)) (hτ1 : τ ≠ 1) (hττ : τ * τ = 1)
    (S : GL (Fin n) (ZMod 2) → Prop)
    (hS : ∀ r, S r → FixesA m (r : Matrix (Fin n) (Fin n) (ZMod 2)))
    (hSconj : ∀ r, S r → S (g * r * g⁻¹))
    (hSblock : ∀ r, S r → lowerBlock2 h (r : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 ∨
      lowerBlock2 h (r : Matrix (Fin n) (Fin n) (ZMod 2)) = τ)
    (r₀ : GL (Fin n) (ZMod 2)) (hr₀ : S r₀)
    (hr₀τ : lowerBlock2 h (r₀ : Matrix (Fin n) (Fin n) (ZMod 2)) = τ) :
    g = 1 := by
  have hFixinv : FixesA m ((g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) :=
    fixesA_inv g hg
  have hmat : (g : Matrix (Fin n) (Fin n) (ZMod 2)) *
      ((g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hmat' : ((g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hDE : lowerBlock2 h (g : Matrix (Fin n) (Fin n) (ZMod 2)) *
      lowerBlock2 h ((g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    rw [← lowerBlock2_mul h hg hFixinv, hmat, lowerBlock2_one h]
  have hED : lowerBlock2 h ((g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *
      lowerBlock2 h (g : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    rw [← lowerBlock2_mul h hFixinv hg, hmat', lowerBlock2_one h]
  have hconj_eq : ∀ r : GL (Fin n) (ZMod 2), FixesA m (r : Matrix (Fin n) (Fin n) (ZMod 2)) →
      lowerBlock2 h ((g * r * g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
        lowerBlock2 h (g : Matrix (Fin n) (Fin n) (ZMod 2)) *
          lowerBlock2 h (r : Matrix (Fin n) (Fin n) (ZMod 2)) *
          lowerBlock2 h ((g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
    intro r hr
    rw [Units.val_mul, Units.val_mul, lowerBlock2_mul h (fixesA_mul hg hr) hFixinv,
      lowerBlock2_mul h hg hr]
  have hor : lowerBlock2 h (g : Matrix (Fin n) (Fin n) (ZMod 2)) * τ *
      lowerBlock2 h ((g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 ∨
      lowerBlock2 h (g : Matrix (Fin n) (Fin n) (ZMod 2)) * τ *
      lowerBlock2 h ((g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = τ := by
    have h1 := hSblock _ (hSconj r₀ hr₀)
    rw [hconj_eq r₀ (hS r₀ hr₀), hr₀τ] at h1
    exact h1
  have hcomm := comm_of_conj_nsbodd hED hτ1 hor
  have hDD := block_two_commute _ τ hττ hτ1 ⟨_, hDE⟩ hcomm
  have hDpow : lowerBlock2 h (g : Matrix (Fin n) (Fin n) (ZMod 2)) ^ orderOf g = 1 := by
    have h1 := (lowerBlock2_pow_nsbodd h g hg (orderOf g)).2
    rw [pow_orderOf_eq_one, Units.val_one, lowerBlock2_one h] at h1
    exact h1.symm
  have hD1 := eq_one_of_sq_pow_odd_nsbodd hDD hodd hDpow
  exact eq_one_of_sq_eq_one_of_odd g (sq_eq_one_of_lower_one h g hg hD1) hodd

private theorem coe_eq_one_of_pCore_nsbodd {G : Type} [Group G] {K : Subgroup G} (y : ↥K)
    (hk : y ∈ CFSG.pCore 2 ↥K) (hodd : Odd (orderOf (y : G))) : (y : G) = 1 := by
  obtain ⟨k, hk'⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) ⟨y, hk⟩
  have hyk : (y : G) ^ 2 ^ k = 1 := by
    have := congrArg (fun z : ↥(CFSG.pCore 2 ↥K) => ((z : ↥K) : G)) hk'
    simpa using this
  have hcop : Nat.Coprime (orderOf (y : G)) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hyk))

theorem oddKGamma_of (h31 : Lemma31) (h35 : Lemma35KR) : OddKGamma := by
  intro G _ _ T M L Mm I H K m k hch _ x hx hodd
  have hd : NoSumBigData G T M L Mm I H K m k := hch.1
  obtain ⟨n, j, α, β, hn, hker, hequi, hV2, hτ⟩ := h35 G T M L Mm I H K m k hd
  obtain ⟨hRlt, hRC⟩ := h31 G T M L Mm I H K m k hd
  have hxK : x ∈ K := hx.1
  have hxC : ∀ v ∈ vV T L, v * x = x * v := Subgroup.mem_centralizer_iff.mp hx.2.2
  have hxN := Subgroup.mem_set_normalizer_iff.mp hx.2.1.2
  obtain ⟨y, hyx⟩ : ∃ y : ↥K, (y : G) = x := ⟨⟨x, hxK⟩, rfl⟩
  have hyC : ∀ v ∈ vV T L, v * (y : G) = (y : G) * v := fun v hv => by
    rw [hyx]; exact hxC v hv
  have hFixg : FixesA m ((α y : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) :=
    fixesA_of_centralizes_nsbodd hequi hV2 y hyC
  have hoddg : Odd (orderOf (α y : GL (Fin n) (ZMod 2))) := by
    have hoy : orderOf y = orderOf x := by
      rw [← hyx]; exact (Subgroup.orderOf_coe y).symm
    have h1 := orderOf_map_dvd α y
    rw [hoy] at h1
    exact Odd.of_dvd_nat hodd h1
  have hfinal : α y = 1 → x = 1 := by
    intro h1
    have hmem : y ∈ CFSG.pCore 2 ↥K := by
      rw [← hker]
      exact MonoidHom.mem_ker.mpr h1
    have hodd' : Odd (orderOf (y : G)) := by
      rw [hyx]; exact hodd
    rw [← hyx]
    exact coe_eq_one_of_pCore_nsbodd y hmem hodd'
  rcases hn with hn1 | ⟨hn5, hm3⟩
  ·
    have hsq : (α y : GL (Fin n) (ZMod 2)) * (α y : GL (Fin n) (ZMod 2)) = 1 :=
      sq_eq_one_of_succ hn1 (α y) hFixg
    exact hfinal (eq_one_of_sq_eq_one_of_odd (α y) hsq hoddg)
  ·
    have h : n = m + 2 := by omega
    obtain ⟨τ, hτ1, hττ, hτle, s₀, hs₀R, hs₀τ⟩ := hτ h
    have hSF : ∀ r : GL (Fin n) (ZMod 2),
        (∃ s : ↥K, (s : G) ∈ pCoreOf 2 I ∧ α s = r) →
          FixesA m (r : Matrix (Fin n) (Fin n) (ZMod 2)) := by
      rintro r ⟨s, hs, rfl⟩
      exact fixesA_of_centralizes_nsbodd hequi hV2 s
        (Subgroup.mem_centralizer_iff.mp (hRC (hRlt.le hs)))
    have hSC : ∀ r : GL (Fin n) (ZMod 2),
        (∃ s : ↥K, (s : G) ∈ pCoreOf 2 I ∧ α s = r) →
          ∃ s : ↥K, (s : G) ∈ pCoreOf 2 I ∧
            α s = (α y : GL (Fin n) (ZMod 2)) * r * (α y : GL (Fin n) (ZMod 2))⁻¹ := by
      rintro r ⟨s, hs, rfl⟩
      refine ⟨y * s * y⁻¹, ?_, ?_⟩
      · have hc : ((y * s * y⁻¹ : ↥K) : G) = x * (s : G) * x⁻¹ := by
          rw [← hyx]; simp
        rw [hc]
        exact (hxN (s : G)).mp hs
      · rw [map_mul, map_mul, map_inv]
    have hSB : ∀ r : GL (Fin n) (ZMod 2),
        (∃ s : ↥K, (s : G) ∈ pCoreOf 2 I ∧ α s = r) →
          lowerBlock2 h (r : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 ∨
            lowerBlock2 h (r : Matrix (Fin n) (Fin n) (ZMod 2)) = τ := by
      rintro r ⟨s, hs, rfl⟩
      exact hτle s hs
    exact hfinal (eq_one_of_block_nsbodd h (α y) hFixg hoddg τ hτ1 hττ
      (fun r => ∃ s : ↥K, (s : G) ∈ pCoreOf 2 I ∧ α s = r) hSF hSC hSB (α s₀)
      ⟨s₀, hs₀R, rfl⟩ hs₀τ)

theorem kRInfGammaZero_of_module (h31 : Lemma31) (h32 : Lemma32) (h35 : Lemma35KR) :
    KRInfGammaZero :=
  kRInfGammaZero_of h31 h32 (oddKGamma_of h31 h35)

end CFSG.Quasithin.H13.Ch4.NSB
