module

public import CFSG.Quasithin.Background.HSL3PairNPrime

public section

namespace CFSG.Quasithin

namespace H

namespace SL3Pair

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix
open scoped Matrix

variable {K : Type} [Field K]

variable [Finite K]

theorem card_fixV_le_of_involution [CharP K 2] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {t : MulAut (PairMod K)} (htN : t ∈ pairNorm K) (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    Nat.card ↥(fixV (Subgroup.zpowers t)) ≤ Nat.card K ^ 4 := by
  classical
  by_cases hts : t ∈ pairSub K
  · obtain ⟨a, b, σ, hte, -, -⟩ := exists_semilinear_of_mem htN hts
    have hab : a * a = 1 ∧ b * b = 1 := by
      rw [hte, pairAut_mul] at ht2
      exact pairAut_injective (ht2.trans pairAut_one.symm)
    have ha1 : a ≠ 1 := by
      rintro rfl
      have hb1 := eq_one_of_pairAut_one (hte ▸ htN) hab.2
      exact ht1 (by rw [hte, hb1, pairAut_one])
    have hb1 : b ≠ 1 := by
      rintro rfl
      have h1 : pairAut 1 a ∈ pairNorm K := by
        have h2 : swapAut K * t * (swapAut K)⁻¹ ∈ pairNorm K :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ swapAut_mem_pairNorm htN)
            (Subgroup.inv_mem _ swapAut_mem_pairNorm)
        rwa [hte, swapAut_mul_pairAut, swapAut_inv, mul_assoc, swapAut_mul_self, mul_one] at h2
      have ha1' := eq_one_of_pairAut_one h1 hab.1
      exact ha1 ha1'
    have hz : (⟨t, hts⟩ : ↥(pairSub K)) = ⟨pairAut a b, pairAut_mem_pairSub a b⟩ :=
      Subtype.ext hte
    obtain ⟨hna, hnb⟩ := fstHom_mem_natNorm (x := ⟨t, hts⟩) htN
    rw [hz, fstHom_pairAut] at hna
    rw [hz, sndHom_pairAut] at hnb
    have hfa := card_fix_le_sq hn hK hna (by rw [sq]; exact hab.1) ha1
    have hfb := card_fix_le_sq hn hK hnb (by rw [sq]; exact hab.2) hb1
    calc Nat.card ↥(fixV (Subgroup.zpowers t))
        ≤ Nat.card {v : StdMod (Fin 3) K // a v = v} * Nat.card {w : StdMod (Fin 3) K // b w = w} :=
          card_fix_pairAut_le a b _ (by rw [← hte]; exact Subgroup.mem_zpowers t)
      _ ≤ Nat.card K ^ 2 * Nat.card K ^ 2 := Nat.mul_le_mul hfa hfb
      _ = Nat.card K ^ 4 := by rw [← pow_add]
  ·
    have hV₂ := SL3One.map_V₁_eq_V₂ htN hts
    have hinj : Function.Injective
        (fun x : ↥(fixV (Subgroup.zpowers t)) => ((x : PairMod K)).2) := by
      intro x y hxy
      have hx := mem_fixV_zpowers_iff.mp x.2
      have hy := mem_fixV_zpowers_iff.mp y.2
      set z : PairMod K := (x : PairMod K) * (y : PairMod K)⁻¹ with hzdef
      have hz : t z = z := by rw [hzdef, map_mul, map_inv, hx, hy]
      have hz1 : z ∈ V₁ K := by
        rw [mem_V₁, hzdef, Prod.snd_mul, Prod.snd_inv]
        exact mul_inv_eq_one.mpr hxy
      have hz2 : z ∈ V₂ K := by
        have : t z ∈ (V₁ K).map t.toMonoidHom := ⟨z, hz1, rfl⟩
        rw [hV₂, hz] at this
        exact this
      have hz' : z = 1 := by
        have : z ∈ V₁ K ⊓ V₂ K := ⟨hz1, hz2⟩
        rwa [V₁_inf_V₂, Subgroup.mem_bot] at this
      apply Subtype.ext
      exact mul_inv_eq_one.mp hz'
    calc Nat.card ↥(fixV (Subgroup.zpowers t)) ≤ Nat.card (StdMod (Fin 3) K) :=
          Nat.card_le_card_of_injective _ hinj
      _ = Nat.card K ^ 3 := by rw [card_stdMod, Fintype.card_fin]
      _ ≤ Nat.card K ^ 4 := Nat.pow_le_pow_right Nat.card_pos (by norm_num)

theorem le_mParam [CharP K 2] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {X : Subgroup (MulAut (PairMod K))} (hXN : X ≤ pairNorm K) : 2 * n ≤ E3.mParam X := by
  classical
  have : Finite (MulAut (PairMod K)) := MulEquiv.finite_left
  have hV : Nat.card (PairMod K) = 2 ^ (6 * n) := by
    rw [card_pairMod, hK, ← pow_mul, mul_comm]
  unfold E3.mParam
  split_ifs with hev
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 2 (even_iff_two_dvd.mp hev)
    refine le_csInf ⟨_, (t : MulAut (PairMod K)), t.2,
      (Subgroup.orderOf_coe t).trans ht, rfl⟩ ?_
    rintro k ⟨s, hsX, hs2, rfl⟩
    have hss : s * s = 1 := by
      have h := pow_orderOf_eq_one s
      rw [hs2, sq] at h
      exact h
    have hs1 : s ≠ 1 := fun h => by rw [h, orderOf_one] at hs2; omega
    have hq4 := card_fixV_le_of_involution hn hK (hXN hsX) hss hs1
    refine le_rkIdx_of_card_mul_le hV _ ?_
    calc Nat.card ↥(fixV (Subgroup.zpowers s)) * 2 ^ (2 * n) ≤
          Nat.card K ^ 4 * 2 ^ (2 * n) := Nat.mul_le_mul_right _ hq4
      _ = 2 ^ (6 * n) := by
          rw [hK, ← pow_mul, ← pow_add]
          congr 1
          ring
  · rw [rk, hV]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [padicValNat.prime_pow]
    omega

theorem H4_SL3Pair_mParam {V : Type*} [CommGroup V] [Finite V] {H M : Subgroup (MulAut V)}
    {V₁ : Subgroup V} {n : ℕ} (hreal : BinaryNaturalSL H V₁ ⊥ 3 n) {φ : MulAut V}
    (hφ : φ ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hinf : V₁ ⊓ V₁.map φ.toMonoidHom = ⊥) (hsup : V₁ ⊔ V₁.map φ.toMonoidHom = ⊤)
    (hniso : ¬ Pair.IsoMod H V₁ (V₁.map φ.toMonoidHom))
    (hMN : M ≤ Subgroup.normalizer (H : Set (MulAut V))) : 2 * n ≤ E3.mParam M := by
  obtain ⟨K, _, _, hK, hreal'⟩ := hreal
  have hn : 1 ≤ n := by
    by_contra h
    have h0 : n = 0 := by omega
    have h1 := Finite.one_lt_card (α := K)
    rw [hK, h0, pow_zero] at h1
    exact lt_irrefl _ h1
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two hn hK
  obtain ⟨e, he⟩ := exists_pair_model hreal' hφ hinf hsup hniso
  have h2 : M.map (congrHom e) ≤ pairNorm K := by
    have h3 : (Subgroup.normalizer (H : Set (MulAut V))).map (congrHom e) =
        Subgroup.normalizer ((H.map (congrHom e) : Subgroup (MulAut (PairMod K))) :
          Set (MulAut (PairMod K))) :=
      Subgroup.map_equiv_normalizer_eq H (MulAut.congr e)
    rw [pairNorm, ← he, ← h3]
    exact Subgroup.map_mono hMN
  rw [← mParam_map_congrHom e M]
  exact le_mParam hn hK h2

end SL3Pair

end H

end CFSG.Quasithin
