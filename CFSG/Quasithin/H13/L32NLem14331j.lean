module

public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.H13.L32NSet14

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14331

variable {X : Type} [Group X] [Finite X]

theorem normal_of_mem_cComp {N : Subgroup X} [N.Normal] (hN : Group.IsSolvable ↥N)
    {L₀ : Subgroup X} (hL : L₀ ∈ cComp (⊤ : Subgroup X))
    (hn : (L₀.map (QuotientGroup.mk' N)).Normal) : L₀.Normal := by
  set π := QuotientGroup.mk' N with hπ
  have hbij := cComp_quotient_bijOn N hN
  refine ⟨fun l hl h => ?_⟩
  set e := MulAut.conj h with he
  have hL'' : L₀.map e.toMonoidHom ∈ cComp (⊤ : Subgroup X) := by
    have := cComp_map_mulEquiv e hL
    rwa [Subgroup.map_top_of_surjective _ e.surjective] at this
  have himg : (L₀.map e.toMonoidHom).map π = L₀.map π := by
    have hcomp : π.comp e.toMonoidHom = (MulAut.conj (π h)).toMonoidHom.comp π := by
      ext x
      simp [he, MulAut.conj_apply, map_mul, map_inv]
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]
    apply le_antisymm
    · rintro _ ⟨k, hk, rfl⟩
      exact hn.conj_mem k hk (π h)
    · intro k hk
      refine ⟨(π h)⁻¹ * k * (π h)⁻¹⁻¹, hn.conj_mem k hk _, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  have heq : L₀.map e.toMonoidHom = L₀ := hbij.2.1 hL'' hL himg
  rw [← heq]
  exact ⟨l, hl, rfl⟩

omit [Finite X] in
theorem subgroupOf_le_pCore_of_simple {N : Subgroup X} [N.Normal]
    (hN : Nat.Coprime 3 (Nat.card N)) (L : Subgroup X)
    (hs : IsSimpleGroup (↥L ⧸ CFSG.Open.pCore 2 ↥L))
    (h3 : 3 ∣ Nat.card (↥L ⧸ CFSG.Open.pCore 2 ↥L)) :
    N.subgroupOf L ≤ CFSG.Open.pCore 2 ↥L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L) with hφ
  have hM : (N.subgroupOf L).Normal := Subgroup.Normal.subgroupOf inferInstance L
  have hn : ((N.subgroupOf L).map φ).Normal := hM.map φ (QuotientGroup.mk'_surjective _)
  have hM3 : Nat.Coprime 3 (Nat.card ↥(N.subgroupOf L)) := by
    have h1 : Nat.card ↥(N.subgroupOf L) ∣ Nat.card ↥N := by
      rw [← Subgroup.card_map_of_injective L.subtype_injective, Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_dvd_of_le inf_le_left
    exact Nat.Coprime.coprime_dvd_right h1 hN
  rcases hn.eq_bot_or_eq_top with h | h
  · intro x hx
    have : φ x ∈ (N.subgroupOf L).map φ := Subgroup.mem_map_of_mem φ hx
    rw [h, Subgroup.mem_bot, hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact this
  · exfalso
    have h1 : Nat.card ↥((N.subgroupOf L).map φ) ∣ Nat.card ↥(N.subgroupOf L) :=
      Subgroup.card_map_dvd _ φ
    rw [h, Subgroup.card_top] at h1
    have := Nat.Coprime.coprime_dvd_right h1 hM3
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp this h3

theorem card_map_of_simple {N : Subgroup X} [N.Normal] (hN : Nat.Coprime 3 (Nat.card N))
    (L : Subgroup X) (hs : IsSimpleGroup (↥L ⧸ CFSG.Open.pCore 2 ↥L))
    (h3 : 3 ∣ Nat.card (↥L ⧸ CFSG.Open.pCore 2 ↥L)) :
    ∃ b : ℕ, Nat.card ↥(L.map (QuotientGroup.mk' N)) =
      Nat.card (↥L ⧸ CFSG.Open.pCore 2 ↥L) * 2 ^ b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : ↥L →* X ⧸ N := (QuotientGroup.mk' N).comp L.subtype with hf
  have hrange : f.range = L.map (QuotientGroup.mk' N) := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : f.ker = N.subgroupOf L := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hf, MonoidHom.comp_apply,
      Subgroup.coe_subtype, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hKO := subgroupOf_le_pCore_of_simple hN L hs h3
  obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥L) 2).exists_card_eq
  obtain ⟨c, hc⟩ := ((CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥L) 2).to_le hKO).exists_card_eq
  have hca : c ≤ a := by
    have h1 := Subgroup.card_dvd_of_le hKO
    rw [hc, ha] at h1
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1
  have hL : Nat.card ↥L = Nat.card (↥L ⧸ CFSG.Open.pCore 2 ↥L) * 2 ^ a := by
    rw [← ha, ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange, hL, hker, hc] at h2
  refine ⟨a - c, ?_⟩
  have h3' : (2 : ℕ) ^ a = 2 ^ (a - c) * 2 ^ c := by rw [← pow_add, Nat.sub_add_cancel hca]
  rw [h3', ← mul_assoc] at h2
  exact (Nat.eq_of_mul_eq_mul_right (pow_pos two_pos c) h2).symm

theorem odd_mul_two_pow_eq {r m d c : ℕ} (hr : Odd r) (hm : Odd m) (h : r * 2 ^ d = m * 2 ^ c) :
    r = m := by
  have key : ∀ {r m d c : ℕ}, Odd r → d ≤ c → r * 2 ^ d = m * 2 ^ c → r = m := by
    intro r m d c hr hdc h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hdc
    have h' : r * 2 ^ d = 2 ^ k * m * 2 ^ d := by rw [h, pow_add]; ring
    have h1 : r = 2 ^ k * m := Nat.eq_of_mul_eq_mul_right (pow_pos two_pos d) h'
    rcases k with _ | k
    · simpa using h1
    · exfalso
      rw [h1, pow_succ, mul_comm (2 ^ k) 2, mul_assoc] at hr
      exact (Nat.not_even_iff_odd.mpr hr) (even_two_mul _)
  rcases le_total d c with hdc | hcd
  · exact key hr hdc h
  · exact (key hm hcd h.symm).symm

theorem card_eq_odd_mul {M S : Subgroup X} (hM : M.Normal) (hS2 : IsPGroup 2 ↥S)
    (hSi : ¬ 2 ∣ S.index) (hMS : M ⊔ S = ⊤) {m c : ℕ} (hm : Odd m)
    (hMc : Nat.card ↥M = m * 2 ^ c) : Nat.card X = m * Nat.card ↥S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSM : S ≤ Subgroup.normalizer (M : Set X) :=
    le_top.trans (Subgroup.normalizer_eq_top_iff.mpr hM).ge
  have h1 := L32NSet14.card_sup_mul_card_inf hSM
  rw [sup_comm, hMS, Subgroup.card_top] at h1
  obtain ⟨d, hd⟩ := (hS2.to_le (inf_le_left : S ⊓ M ≤ S)).exists_card_eq
  have h2 := S.card_mul_index
  rw [hd, hMc, ← h2] at h1
  have hodd : Odd S.index := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hSi)
  have h3 : S.index * 2 ^ d = m * 2 ^ c := by
    have hpos : 0 < Nat.card ↥S := Nat.card_pos
    have : Nat.card ↥S * (S.index * 2 ^ d) = Nat.card ↥S * (m * 2 ^ c) := by
      calc Nat.card ↥S * (S.index * 2 ^ d) = Nat.card ↥S * S.index * 2 ^ d := by ring
        _ = Nat.card ↥S * (m * 2 ^ c) := by rw [h1]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  rw [← h2, odd_mul_two_pow_eq hodd hm h3, mul_comm]

end L14331

end CFSG.Quasithin.H13
