module

public import CFSG.Quasithin.Background.HSU3

public section

namespace CFSG.Quasithin.H13.A6.A6S20

open CFSG.Open CFSG.Quasithin

theorem card_le_two_mul_card_fixV_mul_index {V : Type} [CommGroup V] [Finite V]
    (hV2 : ∀ v : V, v ^ 2 = 1) (a : MulAut V) {D : Subgroup V} (a₁ : V)
    (hDa : ∀ d ∈ D, a d * d⁻¹ ∈ Subgroup.zpowers a₁) :
    Nat.card V ≤ 2 * Nat.card (fixV (Subgroup.zpowers a)) * D.index := by
  classical
  let f : V →* V :=
    { toFun := fun v => a v * v⁻¹
      map_one' := by simp
      map_mul' := fun x y => by
        rw [map_mul]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel }
  have hf : ∀ v, f v = a v * v⁻¹ := fun v => rfl
  have hker : f.ker = fixV (Subgroup.zpowers a) := by
    ext v
    rw [MonoidHom.mem_ker, hf, mul_inv_eq_one]
    constructor
    · intro h g hg
      have hinv : a⁻¹ v = v := by
        have := MulAut.inv_apply_self V a v
        rwa [h] at this
      have hpow : ∀ k : ℤ, (a ^ k) v = v := by
        intro k
        induction k using Int.induction_on with
        | zero => rfl
        | succ k ih => rw [zpow_add_one, MulAut.mul_apply, h, ih]
        | pred k ih => rw [zpow_sub_one, MulAut.mul_apply, hinv, ih]
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact hpow k
    · intro h
      exact h a (Subgroup.mem_zpowers a)
  set P := (Subgroup.zpowers a₁).comap f with hP
  have hDP : D ≤ P := fun d hd => hDa d hd
  have hkP : f.ker ≤ P := fun v hv => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hv]
    exact Subgroup.one_mem _
  have hrel : f.ker.relIndex P ≤ 2 := by
    have e : (f.comp P.subtype).ker = f.ker.subgroupOf P := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      rfl
    rw [Subgroup.relIndex, ← e, Subgroup.index_ker]
    calc Nat.card (Set.range (f.comp P.subtype))
        ≤ Nat.card (Subgroup.zpowers a₁ : Set V) :=
          Nat.card_mono (Set.toFinite _) (by rintro _ ⟨x, rfl⟩; exact x.2)
      _ = Nat.card (Subgroup.zpowers a₁) := rfl
      _ = orderOf a₁ := Nat.card_zpowers a₁
      _ ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) (hV2 a₁)
  have hmul := Subgroup.relIndex_mul_index hkP
  have hPD : P.index ≤ D.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hDP)
  have hcard := f.ker.card_mul_index
  rw [hker] at hcard hmul hrel
  calc Nat.card V
      = Nat.card (fixV (Subgroup.zpowers a)) * (fixV (Subgroup.zpowers a)).index := hcard.symm
    _ = Nat.card (fixV (Subgroup.zpowers a)) *
          ((fixV (Subgroup.zpowers a)).relIndex P * P.index) := by rw [hmul]
    _ ≤ Nat.card (fixV (Subgroup.zpowers a)) * (2 * D.index) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hrel hPD)
    _ = 2 * Nat.card (fixV (Subgroup.zpowers a)) * D.index := by ring

theorem false_of_su3_quad {V : Type} [CommGroup V] [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1)
    {L A : Subgroup (MulAut V)} {n : ℕ} (hn : 3 ≤ n) (hL : BinaryNaturalSU3 L ⊤ ⊥ n)
    (hAL : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L) (hA : IsElemAbelian2 A) (hA1 : A ≠ ⊥)
    {D : Subgroup V} (hD : D.index ≤ Nat.card A) (a₁ : V)
    (hDA : ∀ d ∈ D, ∀ a ∈ A, a d * d⁻¹ ∈ Subgroup.zpowers a₁) : False := by
  classical
  have hMN : L ⊔ A ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    sup_le Subgroup.le_normalizer fun a ha => Subgroup.mem_normalizer_fintype fun l hl =>
      hAL a ha l hl
  obtain ⟨hm, hrk, -⟩ := H.H2_SU3 (by omega) hL le_sup_left hMN
  have hAc : Nat.card A ≤ 2 ^ (n + 1) :=
    (H.card_le_two_pow_pRank le_sup_right (H.isElemAbelian2_iff.mp hA)).trans
      (Nat.pow_le_pow_right (by norm_num) hrk)
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra h
    push Not at h
    exact hA1 (eq_bot_iff.mpr fun a ha => Subgroup.mem_bot.mpr (h a ha))
  have hzA : Subgroup.zpowers a ≤ L ⊔ A :=
    (Subgroup.zpowers_le).mpr (Subgroup.mem_sup_right haA)
  have hz2 : IsPGroup 2 ↥(Subgroup.zpowers a) :=
    IsPGroup.to_le hA.isPGroup ((Subgroup.zpowers_le).mpr haA)
  have hz1 : Subgroup.zpowers a ≠ ⊥ := by
    intro h
    apply ha1
    have : a ∈ Subgroup.zpowers a := Subgroup.mem_zpowers a
    rw [h] at this
    exact Subgroup.mem_bot.mp this
  have hidx : 2 * n ≤ rkIdx (fixV (Subgroup.zpowers a)) :=
    hm ▸ E3.mParam_le_rkIdx_fixV hzA hz2 hz1
  have hb := card_le_two_mul_card_fixV_mul_index hV2 a a₁ fun d hd => hDA d hd a haA
  have hpow : 2 ^ rkIdx (fixV (Subgroup.zpowers a)) ≤ (fixV (Subgroup.zpowers a)).index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) pow_padicValNat_dvd
  have hcard := (fixV (Subgroup.zpowers a)).card_mul_index
  have hC : 0 < Nat.card (fixV (Subgroup.zpowers a)) := Nat.card_pos
  have h1 : Nat.card (fixV (Subgroup.zpowers a)) * 2 ^ (2 * n) ≤
      Nat.card (fixV (Subgroup.zpowers a)) * 2 ^ (n + 2) :=
    calc Nat.card (fixV (Subgroup.zpowers a)) * 2 ^ (2 * n)
        ≤ Nat.card (fixV (Subgroup.zpowers a)) * 2 ^ rkIdx (fixV (Subgroup.zpowers a)) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hidx)
      _ ≤ Nat.card (fixV (Subgroup.zpowers a)) * (fixV (Subgroup.zpowers a)).index :=
          Nat.mul_le_mul_left _ hpow
      _ = Nat.card V := hcard
      _ ≤ 2 * Nat.card (fixV (Subgroup.zpowers a)) * D.index := hb
      _ ≤ 2 * Nat.card (fixV (Subgroup.zpowers a)) * 2 ^ (n + 1) :=
          Nat.mul_le_mul_left _ (hD.trans hAc)
      _ = Nat.card (fixV (Subgroup.zpowers a)) * 2 ^ (n + 2) := by ring
  have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
    (Nat.le_of_mul_le_mul_left h1 hC)
  omega

end CFSG.Quasithin.H13.A6.A6S20
