module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R899C4Pow
public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.UniquenessCase.UC22R899C4Lin
import CFSG.GH74.Uniqueness.SU.SU1Normal2
import CFSG.Quasithin.Background.A1cRank
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCRankOneCenter

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem uc22r899c4_cast_pow_eq_one {r : ℕ} {t x : Γ} (hto : orderOf t = r) {f n : ℕ}
    (hf : x * t * x⁻¹ = t ^ f) (hx : x ^ n = 1) : (f : ZMod r) ^ n = 1 := by
  have h1 := uc22r899c4_conj_pow_pow (U := zpowers t)
    (fun u hu => CFSG.GH74.Uniqueness.SU.SU1.conj_of_mem_zpowers hf hu) n t (mem_zpowers t)
  rw [hx, one_mul, inv_one, mul_one] at h1
  have h2 : f ^ n ≡ 1 [MOD r] := by
    rw [← hto]
    exact pow_eq_pow_iff_modEq.1 (by rw [pow_one]; exact h1.symm)
  rw [← Nat.cast_pow, (ZMod.natCast_eq_natCast_iff _ _ _).2 h2, Nat.cast_one]

theorem uc22r899c4_exists_common_pow {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hp3 : p % 3 ≠ 1)
    {K S : Fin 3 → Subgroup Γ} {t : Fin 3 → Γ} (hSc : ∀ i, IsCyclic (S i)) (ht : ∀ i, t i ∈ S i)
    (hto : ∀ i, orderOf (t i) = r) {w : Γ}
    (hwK : ∀ i, (K i).map (MulAut.conj w).toMonoidHom = K (i + 1))
    (hwS : ∀ i, (S i).map (MulAut.conj w).toMonoidHom = S (i + 1)) {d : Γ} (hd : orderOf d = p)
    (hdK : ∀ i, d ∈ normalizer (K i : Set Γ)) (hdS : ∀ i, d ∈ normalizer (S i : Set Γ)) :
    ∃ g ∈ normalizer (K 2 : Set Γ) ⊓ normalizer (S 2 : Set Γ), orderOf g = p ∧
      ∃ k : ℕ, g * t 0 * g⁻¹ = t 0 ^ k ∧ g * t 1 * g⁻¹ = t 1 ^ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hpow : ∀ i {a b : ℕ}, (a : ZMod r) = (b : ZMod r) → t i ^ a = t i ^ b := fun i a b h =>
    pow_eq_pow_iff_modEq.2 (by rw [hto i]; exact (ZMod.natCast_eq_natCast_iff _ _ _).1 h)
  choose e he using fun i => @uc22r899c4_exists_pow_of_isCyclic Γ _ _ (S i) (hSc i) d (hdS i)
  set d' := w * d * w⁻¹ with hd'def
  have hd'S : ∀ i, ∀ u ∈ S (i + 1), d' * u * d'⁻¹ = u ^ e i := fun i u hu => by
    rw [← hwS i] at hu
    exact uc22r899c4_conj_pow_conj (he i) w u hu
  have hd'0 : ∀ u ∈ S 0, d' * u * d'⁻¹ = u ^ e 2 := hd'S 2
  have hd'1 : ∀ u ∈ S 1, d' * u * d'⁻¹ = u ^ e 0 := hd'S 0
  have hd'2 : ∀ u ∈ S 2, d' * u * d'⁻¹ = u ^ e 1 := hd'S 1
  set Q : Subgroup Γ := normalizer (K 2 : Set Γ) ⊓ normalizer (S 2 : Set Γ) with hQ
  have hdQ : d ∈ Q := ⟨hdK 2, hdS 2⟩
  have hd'Q : d' ∈ Q := by
    have h1 : (K 1).map (MulAut.conj w).toMonoidHom = K 2 := hwK 1
    have h2 : (S 1).map (MulAut.conj w).toMonoidHom = S 2 := hwS 1
    refine ⟨?_, ?_⟩
    · rw [← h1, ← Subgroup.map_equiv_normalizer_eq]
      exact ⟨d, hdK 1, rfl⟩
    · rw [← h2, ← Subgroup.map_equiv_normalizer_eq]
      exact ⟨d, hdS 1, rfl⟩
  have hdp : d ^ p = 1 := hd ▸ pow_orderOf_eq_one d
  have hE : ∀ i, (e i : ZMod r) ^ p = 1 := fun i =>
    uc22r899c4_cast_pow_eq_one (hto i) (he i (t i) (ht i)) hdp
  by_cases h01 : (e 0 : ZMod r) = (e 1 : ZMod r)
  · exact ⟨d, hdQ, hd, e 0, he 0 (t 0) (ht 0), (he 1 (t 1) (ht 1)).trans (hpow 1 h01.symm)⟩
  obtain ⟨ζ, hζo⟩ : ∃ ζ : ZMod r, orderOf ζ = p := by
    by_cases h0 : (e 0 : ZMod r) = 1
    · exact ⟨_, orderOf_eq_prime (hE 1) fun h => h01 (h0.trans h.symm)⟩
    · exact ⟨_, orderOf_eq_prime (hE 0) h0⟩
  have hprim : IsPrimitiveRoot ζ p := hζo ▸ IsPrimitiveRoot.orderOf ζ
  choose a ha haζ using fun i => hprim.eq_pow_of_pow_eq_one (hE i)
  have hab : (a 0 : ZMod p) ≠ (a 1 : ZMod p) := by
    intro h
    have h' := (ZMod.natCast_eq_natCast_iff' _ _ _).1 h
    rw [Nat.mod_eq_of_lt (ha 0), Nat.mod_eq_of_lt (ha 1)] at h'
    exact h01 (by rw [← haζ 0, ← haζ 1, h'])
  obtain ⟨x, y, hxy, hne⟩ := uc22r899c4_exists_coord (c := (a 2 : ZMod p)) hp3 hab
  set h₀ := d ^ x.val * d' ^ y.val with hh₀
  have hh0 := uc22r899c4_conj_pow_mul (uc22r899c4_conj_pow_pow (he 0) x.val)
    (uc22r899c4_conj_pow_pow hd'0 y.val)
  have hh1 := uc22r899c4_conj_pow_mul (uc22r899c4_conj_pow_pow (he 1) x.val)
    (uc22r899c4_conj_pow_pow hd'1 y.val)
  have hh2 := uc22r899c4_conj_pow_mul (uc22r899c4_conj_pow_pow (he 2) x.val)
    (uc22r899c4_conj_pow_pow hd'2 y.val)
  have hcast : ∀ i j, ((e i ^ x.val * e j ^ y.val : ℕ) : ZMod r) =
      ζ ^ (a i * x.val + a j * y.val) := fun i j => by
    push_cast
    rw [← haζ i, ← haζ j, ← pow_mul, ← pow_mul, ← pow_add]
  have hmod : ∀ i j, ((a i * x.val + a j * y.val : ℕ) : ZMod p) =
      x * (a i : ZMod p) + y * (a j : ZMod p) := fun i j => by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring
  have hagree : ((e 0 ^ x.val * e 2 ^ y.val : ℕ) : ZMod r) =
      ((e 1 ^ x.val * e 0 ^ y.val : ℕ) : ZMod r) := by
    rw [hcast, hcast]
    refine (orderOf_pos_iff.1 (by rw [hζo]; exact hp.pos)).pow_eq_pow_iff_modEq.2 ?_
    rw [hζo, ← ZMod.natCast_eq_natCast_iff, hmod, hmod]
    exact hxy
  have hnd : ∀ i j, x * (a i : ZMod p) + y * (a j : ZMod p) ≠ 0 →
      ¬ p ∣ a i * x.val + a j * y.val := fun i j hne' hdvd =>
    hne' (by rw [← hmod]; exact (ZMod.natCast_eq_zero_iff _ _).2 hdvd)
  have hph : p ∣ orderOf h₀ := by
    rcases hne with hne | hne
    · exact uc22r899c4_dvd_orderOf hp (hto 0) (hh0 (t 0) (ht 0)) hζo (hcast 0 2) (hnd 0 2 hne)
    · exact uc22r899c4_dvd_orderOf hp (hto 2) (hh2 (t 2) (ht 2)) hζo (hcast 2 1) (hnd 2 1 hne)
  refine ⟨h₀ ^ (orderOf h₀ / p), Q.pow_mem (Q.mul_mem (Q.pow_mem hdQ _) (Q.pow_mem hd'Q _)) _,
    orderOf_pow_orderOf_div (orderOf_pos h₀).ne' hph,
    (e 0 ^ x.val * e 2 ^ y.val) ^ (orderOf h₀ / p),
    uc22r899c4_conj_pow_pow hh0 _ (t 0) (ht 0), ?_⟩
  rw [uc22r899c4_conj_pow_pow hh1 _ (t 1) (ht 1)]
  exact hpow 1 (by rw [Nat.cast_pow, Nat.cast_pow, hagree])

theorem uc22r899c4_exists_scalar {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hp3 : p % 3 ≠ 1)
    {K S : Fin 3 → Subgroup Γ} {t : Fin 3 → Γ} (hSc : ∀ i, IsCyclic (S i))
    (hSK : ∀ i, S i ≤ K i) (ht : ∀ i, t i ∈ S i) (hto : ∀ i, orderOf (t i) = r)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x) {w : Γ}
    (hwK : ∀ i, (K i).map (MulAut.conj w).toMonoidHom = K (i + 1))
    (hwS : ∀ i, (S i).map (MulAut.conj w).toMonoidHom = S (i + 1)) {d : Γ} (hd : orderOf d = p)
    (hdK : ∀ i, d ∈ normalizer (K i : Set Γ)) (hdS : ∀ i, d ∈ normalizer (S i : Set Γ))
    (hKS : ∀ y ∈ K 2, y ∈ normalizer (S 2 : Set Γ) → orderOf y ≠ p)
    (hpK : p ∣ Nat.card (K 2)) :
    ∃ B : Subgroup Γ, IsElemAbelian p B ∧ Nat.card B = p ^ 2 ∧
      (∀ b ∈ B, ∃ k : ℕ, ∀ u ∈ zpowers (t 0) ⊔ zpowers (t 1), b * u * b⁻¹ = u ^ k) ∧
      ∃ z ∈ B, z ≠ 1 ∧ ∀ u ∈ zpowers (t 0) ⊔ zpowers (t 1), z * u = u * z := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, ⟨hgK, hgS⟩, hgo, k, hk0, hk1⟩ :=
    uc22r899c4_exists_common_pow hp hr hp3 hSc ht hto hwK hwS hd hdK hdS
  have hgK2 : g ∉ K 2 := fun h => hKS g h hgS hgo
  have hgP : IsPGroup p (zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hgo, pow_one])
  obtain ⟨z, hzK, hzo, hzc⟩ :=
    CFSG.Quasithin.exists_orderOf_eq_of_isPGroup_normalizer hgP (zpowers_le.2 hgK) hpK
  have hgz : g * z = z * g := Subgroup.mem_centralizer_iff.1 hzc g (mem_zpowers g)
  have hzg : z ∉ zpowers g := by
    intro hz
    have hle : zpowers z ≤ zpowers g := zpowers_le.2 hz
    have heq : zpowers z = zpowers g := Subgroup.eq_of_le_of_card_ge hle
      (le_of_eq (by rw [Nat.card_zpowers, Nat.card_zpowers, hgo, hzo]))
    have hgz' : g ∈ zpowers z := by
      rw [heq]
      exact mem_zpowers g
    exact hgK2 (zpowers_le.2 hzK hgz')
  obtain ⟨hBel, hBc⟩ :=
    CFSG.ComponentClassification.UnbalancedGS.RankOneCenter.pair_isElementaryAbelian_card hgo
      hzo hgz hzg
  have ht01 : t 0 * t 1 = t 1 * t 0 :=
    hcomm 0 1 (by decide) (t 0) (hSK 0 (ht 0)) (t 1) (hSK 1 (ht 1))
  have hzU : zpowers (t 0) ⊔ zpowers (t 1) ≤ centralizer ({z} : Set Γ) :=
    sup_le (zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2
        (hcomm 2 0 (by decide) z hzK (t 0) (hSK 0 (ht 0))).symm))
      (zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2
        (hcomm 2 1 (by decide) z hzK (t 1) (hSK 1 (ht 1))).symm))
  have hzc' : ∀ u ∈ zpowers (t 0) ⊔ zpowers (t 1), z * u = u * z := fun u hu =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hzU hu)).symm
  have hBp : zpowers g ⊔ zpowers z ≤ uc22r899c4_powSub (zpowers (t 0) ⊔ zpowers (t 1)) :=
    sup_le (zpowers_le.2 (uc22r899c4_mem_powSub.2 ⟨k, uc22r899c4_conj_pow_sup ht01 hk0 hk1⟩))
      (zpowers_le.2 (uc22r899c4_mem_powSub.2
        ⟨1, fun u hu => by rw [pow_one, hzc' u hu, mul_inv_cancel_right]⟩))
  refine ⟨zpowers g ⊔ zpowers z, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1
    hBel, hBc, fun b hb => uc22r899c4_mem_powSub.1 (hBp hb), z,
    Subgroup.mem_sup_right (mem_zpowers z), fun h1 => ?_, hzc'⟩
  rw [h1, orderOf_one] at hzo
  exact hp.one_lt.ne hzo

end CFSG.LocalAnalysis.UniquenessCase.UC22
