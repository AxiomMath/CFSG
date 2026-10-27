module

public import CFSG.Quasithin.Vol2.Ch10SecB5EvL2
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL unipSL_mul_self unipSL_zero)

theorem five_dvd_four_pow_sub_one {n : ℕ} (hn : Even n) : 5 ∣ 4 ^ n - 1 := by
  obtain ⟨k, rfl⟩ := hn
  have h : 4 ^ (k + k) = 16 ^ k := by rw [← two_mul, pow_mul]; norm_num
  rw [h]
  have h1 : 1 ≡ 16 ^ k [MOD 5] := by
    simpa using (Nat.ModEq.pow k (show 16 ≡ 1 [MOD 5] by decide)).symm
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp h1

variable {Q : Type} [Group Q] [Finite Q] {F : Type} [Field F] [Finite F] {n : ℕ}

theorem charP_two_of_card (hF : Nat.card F = 2 ^ n) : CharP F 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])

omit [Finite Q] in
theorem exists_unip_equiv (hF : Nat.card F = 2 ^ n)
    (e : Q ≃* Matrix.SpecialLinearGroup (Fin 2) F) {S : Subgroup Q} (hS : IsSylowTwoOf S ⊤) :
    ∃ ψ : Q ≃* Matrix.SpecialLinearGroup (Fin 2) F, (∀ s ∈ S, ∃ b : F, ψ s = unipSL b) ∧
      ∀ b : F, ψ.symm (unipSL b) ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 ↥(S.map e.toMonoidHom) := hS.2.1.map e.toMonoidHom
  have hidx : ¬ 2 ∣ (S.map e.toMonoidHom).index := by
    have h := hS.2.2
    rw [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right _] at h
    rwa [MulEquiv.toMonoidHom_eq_coe, Subgroup.index_map_equiv]
  obtain ⟨g, hg1, hg2⟩ := SecA.exists_conj_unip hF hP2 hidx
  refine ⟨e.trans (MulAut.conj g), fun s hs => ?_, fun b => ?_⟩
  · obtain ⟨b, hb⟩ := hg1 (e s) (Subgroup.mem_map_of_mem _ hs)
    exact ⟨b, by simpa [MulAut.conj_apply] using hb⟩
  · obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp (hg2 b)
    have : (e.trans (MulAut.conj g)).symm (unipSL b) = s := by
      rw [MulEquiv.symm_apply_eq]
      simp only [MulEquiv.trans_apply, MulAut.conj_apply]
      rw [show e s = g⁻¹ * unipSL b * g from hse]
      group
    rw [this]
    exact hs

variable {S : Subgroup Q} {ψ : Q ≃* Matrix.SpecialLinearGroup (Fin 2) F}

omit [Finite Q] [Finite F] in
theorem upper_of_mem_normalizer (hψ1 : ∀ s ∈ S, ∃ b : F, ψ s = unipSL b)
    (hψ2 : ∀ b : F, ψ.symm (unipSL b) ∈ S) {z : Q} (hz : z ∈ Subgroup.normalizer (S : Set Q)) :
    ((ψ z : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  have hm : z * ψ.symm (unipSL 1) * z⁻¹ ∈ S :=
    (Subgroup.mem_normalizer_iff.mp hz _).mp (hψ2 1)
  obtain ⟨b, hb⟩ := hψ1 _ hm
  refine SecA.lower_left_eq_zero (b := b) ?_
  rw [← hb]
  simp

omit [Finite Q] in
theorem eq_one_of_conj_eq_of_mulEquiv (hF : Nat.card F = 2 ^ n)
    (e : Q ≃* Matrix.SpecialLinearGroup (Fin 2) F) (hS : IsSylowTwoOf S ⊤) {z : Q}
    (hz : z ∈ Subgroup.normalizer (S : Set Q)) (h3 : orderOf z = 3) {s : Q} (hs : s ∈ S)
    (hzs : z * s * z⁻¹ = s) : s = 1 := by
  have := charP_two_of_card hF
  obtain ⟨ψ, hψ1, hψ2⟩ := exists_unip_equiv hF e hS
  obtain ⟨b, hb⟩ := hψ1 s hs
  have hzu := upper_of_mem_normalizer hψ1 hψ2 hz
  have h3' : orderOf (ψ z) = 3 := by
    rw [show ψ z = ψ.toMonoidHom z from rfl, orderOf_injective _ ψ.injective]
    exact h3
  have h : ψ z * unipSL b * (ψ z)⁻¹ = unipSL b := by
    rw [← hb, ← map_inv, ← map_mul, ← map_mul, hzs]
  have hb0 := eq_zero_of_upper_conj hzu h3' h
  rw [hb0, unipSL_zero] at hb
  exact ψ.injective (by rw [hb, map_one])

omit [Finite Q] in
theorem exists_pow_mul_of_pow_three (hF : Nat.card F = 2 ^ n)
    (e : Q ≃* Matrix.SpecialLinearGroup (Fin 2) F) (hS : IsSylowTwoOf S ⊤) {z g : Q}
    (hz : z ∈ Subgroup.normalizer (S : Set Q)) (h3 : orderOf z = 3)
    (hg : g ∈ Subgroup.normalizer (S : Set Q)) (hg3 : g ^ 3 = 1) :
    ∃ a : ℕ, ∃ s ∈ S, g = z ^ a * s := by
  have := charP_two_of_card hF
  obtain ⟨ψ, hψ1, hψ2⟩ := exists_unip_equiv hF e hS
  have h3' : orderOf (ψ z) = 3 := by
    rw [show ψ z = ψ.toMonoidHom z from rfl, orderOf_injective _ ψ.injective]
    exact h3
  have hg3' : ψ g ^ 3 = 1 := by rw [← map_pow, hg3, map_one]
  obtain ⟨a, c, hac⟩ := exists_pow_mul_unipSL (upper_of_mem_normalizer hψ1 hψ2 hz) h3'
    (upper_of_mem_normalizer hψ1 hψ2 hg) hg3'
  refine ⟨a, ψ.symm (unipSL c), hψ2 c, ?_⟩
  apply ψ.injective
  rw [map_mul, map_pow, MulEquiv.apply_symm_apply, hac]

theorem le_normalizer_of_not_five_dvd
    (hn : 2 ≤ n) (hne : Even n) (hF : Nat.card F = 2 ^ n)
    (e : Q ≃* Matrix.SpecialLinearGroup (Fin 2) F) (hS : IsSylowTwoOf S ⊤) {X : Subgroup Q}
    (hSX : S ≤ X) (h5 : ¬ 5 ∣ Nat.card X) : X ≤ Subgroup.normalizer (S : Set Q) := by
  rcases SecA.le_normalizer_or_eq_top_of_mulEquiv hn hF e hS hSX with h | h
  · exact h
  · exfalso
    rw [h, Subgroup.card_top, Nat.card_congr e.toEquiv, SecA.card_SL_two_pow hF] at h5
    exact h5 (Dvd.dvd.mul_left (five_dvd_four_pow_sub_one hne) _)

omit [Finite Q] in
theorem center_eq_bot_of_mulEquiv (hF : Nat.card F = 2 ^ n)
    (e : Q ≃* Matrix.SpecialLinearGroup (Fin 2) F) : Subgroup.center Q = ⊥ := by
  have := charP_two_of_card hF
  rw [eq_bot_iff]
  intro z hz
  have hez : e z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
  rw [SecA.center_SL_two_eq_bot, Subgroup.mem_bot] at hez
  rw [Subgroup.mem_bot]
  exact e.injective (by rw [hez, map_one])

end CFSG.Quasithin.Vol2.Ch10.SecB
