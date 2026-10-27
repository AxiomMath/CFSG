module

public import CFSG.Quasithin.Background.E2Dihedral

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

namespace E2

variable {G : Type*} [Group G] {V : Subgroup G} {hV : IsElemAbelian 2 V}

theorem map_valHom_commSub_le_of {A : Subgroup G} {W : Subgroup (IntMod V hV)}
    {W' : Subgroup G} (hW : W.map (valHom hV) ≤ W') :
    (commSub W (autI hV A)).map (valHom hV) ≤ ⁅W', A⁆ := by
  rw [Subgroup.map_le_iff_le_comap, commSub, Subgroup.closure_le]
  rintro _ ⟨φ, hφ, w, hw, rfl⟩
  obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hφ
  show (convI hV g w * w⁻¹).val ∈ ⁅W', A⁆
  rw [IntMod.val_mul, IntMod.val_inv, convI_apply_val, Subgroup.commutator_comm,
    ← commutatorElement_def]
  exact Subgroup.commutator_mem_commutator hg (hW ⟨w, hw, rfl⟩)

theorem valHom_injective : Function.Injective (valHom hV) := IntMod.val_injective

theorem commSeries_two_autI_eq_bot {A : Subgroup G} (h : ⁅⁅V, A⁆, A⁆ = ⊥) :
    commSeries (autI hV A) 2 = ⊥ := by
  have h1 : (commSub (⊤ : Subgroup (IntMod V hV)) (autI hV A)).map (valHom hV) ≤ ⁅V, A⁆ :=
    map_valHom_commSub_le_of map_valHom_top.le
  have h2 : (commSub (commSub (⊤ : Subgroup (IntMod V hV)) (autI hV A)) (autI hV A)).map
      (valHom hV) ≤ ⁅⁅V, A⁆, A⁆ := map_valHom_commSub_le_of h1
  rw [h] at h2
  exact (Subgroup.map_eq_bot_iff_of_injective _ valHom_injective).1 (le_bot_iff.1 h2)

theorem commSeries_autI_eq_bot_of_cubic {A : Subgroup G} (h : ⁅⁅⁅V, A⁆, A⁆, A⁆ = ⊥) :
    commSeries (autI hV A) 3 = ⊥ := by
  have h1 : (commSub (⊤ : Subgroup (IntMod V hV)) (autI hV A)).map (valHom hV) ≤ ⁅V, A⁆ :=
    map_valHom_commSub_le_of map_valHom_top.le
  have h2 : (commSub (commSub (⊤ : Subgroup (IntMod V hV)) (autI hV A)) (autI hV A)).map
      (valHom hV) ≤ ⁅⁅V, A⁆, A⁆ := map_valHom_commSub_le_of h1
  have h3 : (commSub (commSub (commSub (⊤ : Subgroup (IntMod V hV)) (autI hV A)) (autI hV A))
      (autI hV A)).map (valHom hV) ≤ ⁅⁅⁅V, A⁆, A⁆, A⁆ := map_valHom_commSub_le_of h2
  rw [h] at h3
  exact (Subgroup.map_eq_bot_iff_of_injective _ valHom_injective).1 (le_bot_iff.1 h3)

variable [Finite G]

theorem index_fixV_autI {A : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G)) :
    (fixV (autI hV A)).index = (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V := by
  have h1 := (fixV (autI hV A)).card_mul_index
  rw [card_fixV_autI hV hA] at h1
  have h2 := Subgroup.relIndex_mul_card (V ⊓ Subgroup.centralizer (A : Set G)) V
  rw [inf_eq_left.2 (inf_le_left.trans (le_refl V))] at h2
  have h3 : Nat.card (IntMod V hV) = Nat.card V := rfl
  have hpos : 0 < Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [h1, h3, ← h2, mul_comm]

theorem rAV_autI {A : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G)) :
    rAV (autI hV A) =
      (padicValNat 2 ((V ⊓ Subgroup.centralizer (A : Set G)).relIndex V) : ℚ) /
        (padicValNat 2 ((A ⊓ Subgroup.centralizer (V : Set G)).relIndex A) : ℚ) := by
  unfold rAV rkIdx rk
  rw [index_fixV_autI hA, card_autI_eq hV hA]

omit [Finite G] in
theorem ratio_lt_two {x y k l : ℕ} (hx : x ∣ 2 ^ k) (hy : y ∣ 2 ^ l) (hy1 : 1 < y)
    (hxy : x < y ^ 2) : (padicValNat 2 x : ℚ) / (padicValNat 2 y : ℚ) < 2 := by
  obtain ⟨β, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hx
  obtain ⟨α, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hy
  rw [padicValNat.prime_pow, padicValNat.prime_pow]
  have hα : 0 < α := by
    rcases Nat.eq_zero_or_pos α with h0 | h0
    · rw [h0, pow_zero] at hy1
      exact absurd hy1 (lt_irrefl 1)
    · exact h0
  have hβ : β < 2 * α := by
    rw [← pow_mul, mul_comm] at hxy
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 hxy
  rw [div_lt_iff₀ (by exact_mod_cast hα)]
  exact_mod_cast hβ

omit [Finite G] in
theorem ratio_le_one {x y k l : ℕ} (hx : x ∣ 2 ^ k) (hy : y ∣ 2 ^ l) (hy1 : 1 < y)
    (hxy : x ≤ y) : (padicValNat 2 x : ℚ) / (padicValNat 2 y : ℚ) ≤ 1 := by
  obtain ⟨β, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hx
  obtain ⟨α, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hy
  rw [padicValNat.prime_pow, padicValNat.prime_pow]
  have hα : 0 < α := by
    rcases Nat.eq_zero_or_pos α with h0 | h0
    · rw [h0, pow_zero] at hy1
      exact absurd hy1 (lt_irrefl 1)
    · exact h0
  have hβ : β ≤ α := (Nat.pow_le_pow_iff_right (by norm_num)).1 hxy
  rw [div_le_one (by exact_mod_cast hα)]
  exact_mod_cast hβ

omit [Finite G] in
theorem relIndex_dvd_card (X Y : Subgroup G) (hXY : X ≤ Y) : X.relIndex Y ∣ Nat.card Y := by
  have h := Subgroup.relIndex_mul_card X Y
  rw [inf_eq_left.2 hXY] at h
  exact Dvd.intro _ h

theorem qhatOf_lt_two_of_cubic {X A : Subgroup G} (hAX : A ≤ X)
    (hAN : A ≤ Subgroup.normalizer (V : Set G)) (hAel : IsElemAbelian 2 A)
    (hcub : ⁅⁅⁅V, A⁆, A⁆, A⁆ = ⊥)
    (hAV : ¬ A ≤ Subgroup.centralizer (V : Set G))
    (hcount : (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V <
      ((A ⊓ Subgroup.centralizer (V : Set G)).relIndex A) ^ 2) :
    qhatOf (autI hV X) < ((2 : ℚ) : WithTop ℚ) := by
  refine kq_lt_iff.2 ⟨autI hV A, ⟨autI_mono hV hAX, (autI_eq_bot_iff hV hAN).not.2 hAV,
    isElemAbelian2_autI hV hAel hAN⟩, commSeries_autI_eq_bot_of_cubic hcub, ?_⟩
  rw [rAV_autI hAN]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (isPGroup_of_isElemAbelian hV)
  obtain ⟨l, hl⟩ := IsPGroup.iff_card.1 (isPGroup_of_isElemAbelian hAel)
  have hy1 : 1 < (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A := by
    have h0 : (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A ≠ 0 := by
      intro h0
      have h := Subgroup.relIndex_mul_card (A ⊓ Subgroup.centralizer (V : Set G)) A
      rw [h0, zero_mul] at h
      exact (Nat.card_pos (α := A)).ne' h.symm
    have h1 : (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A ≠ 1 := fun h1 =>
      hAV ((Subgroup.relIndex_eq_one.1 h1).trans inf_le_right)
    omega
  exact ratio_lt_two (hk ▸ relIndex_dvd_card _ _ inf_le_left)
    (hl ▸ relIndex_dvd_card _ _ inf_le_left) hy1 hcount

theorem qhatOf_le_two_of_cubic {X A : Subgroup G} (hAX : A ≤ X)
    (hAN : A ≤ Subgroup.normalizer (V : Set G)) (hAel : IsElemAbelian 2 A)
    (hcub : ⁅⁅⁅V, A⁆, A⁆, A⁆ = ⊥)
    (hAV : ¬ A ≤ Subgroup.centralizer (V : Set G))
    (hcount : (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V ≤
      ((A ⊓ Subgroup.centralizer (V : Set G)).relIndex A) ^ 2) :
    qhatOf (autI hV X) ≤ ((2 : ℚ) : WithTop ℚ) := by
  refine kq_le_iff.2 ⟨autI hV A, ⟨autI_mono hV hAX, (autI_eq_bot_iff hV hAN).not.2 hAV,
    isElemAbelian2_autI hV hAel hAN⟩, commSeries_autI_eq_bot_of_cubic hcub, ?_⟩
  rw [rAV_autI hAN]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (isPGroup_of_isElemAbelian hV)
  obtain ⟨l, hl⟩ := IsPGroup.iff_card.1 (isPGroup_of_isElemAbelian hAel)
  have hy1 : 1 < (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A := by
    have h0 : (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A ≠ 0 := by
      intro h0
      have h := Subgroup.relIndex_mul_card (A ⊓ Subgroup.centralizer (V : Set G)) A
      rw [h0, zero_mul] at h
      exact (Nat.card_pos (α := A)).ne' h.symm
    have h1 : (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A ≠ 1 := fun h1 =>
      hAV ((Subgroup.relIndex_eq_one.1 h1).trans inf_le_right)
    omega
  have hdx := hk ▸ relIndex_dvd_card (V ⊓ Subgroup.centralizer (A : Set G)) V inf_le_left
  have hdy := hl ▸ relIndex_dvd_card (A ⊓ Subgroup.centralizer (V : Set G)) A inf_le_left
  obtain ⟨β, -, hβ⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdx
  obtain ⟨α, -, hα⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdy
  rw [hβ, hα] at hcount ⊢
  rw [hα] at hy1
  rw [padicValNat.prime_pow, padicValNat.prime_pow]
  have hα0 : 0 < α := by
    rcases Nat.eq_zero_or_pos α with h0 | h0
    · rw [h0, pow_zero] at hy1
      exact absurd hy1 (lt_irrefl 1)
    · exact h0
  have hle : β ≤ 2 * α := by
    rw [← pow_mul, mul_comm] at hcount
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hcount
  rw [div_le_iff₀ (by exact_mod_cast hα0)]
  exact_mod_cast hle

end E2

open E2 in
theorem E2_13_three_of_isSolvable {G : Type*} [Group G] [Finite G] {H T M V : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : MinParabolic H T M) (hsolv : Group.IsSolvable H)
    (hchar : CharTwo H) (hVT : V ≤ T) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hVJ : ¬ V ≤ kerIn M H) :
    qhatOf (autI hV H) ≤ ((2 : ℚ) : WithTop ℚ) := by
  obtain ⟨-, -, A, hAT, -, hAel, hcub, hAV, -, hcount⟩ :=
    E2_13_two_of_isSolvable h hsolv hchar hVT hTV hV hVJ
  exact qhatOf_le_two_of_cubic (hAT.trans h.isSylow.1) (hAT.trans hTV) hAel hcub hAV hcount

open E2 in
theorem E2_15_of_isSolvable {G : Type*} [Group G] [Finite G] {H T M V : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : MinParabolic H T M) (hsolv : Group.IsSolvable H)
    (hchar : CharTwo H) (hVT : V ≤ T) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hVJ : ¬ V ≤ kerIn M H) :
    qhatOf (autI hV H) < ((2 : ℚ) : WithTop ℚ) := by
  have hT := h.isSylow
  have hVQ : ¬ V ≤ pCoreOf 2 H := fun hle => hVJ (hle.trans h.pCoreOf_le_kerIn)
  obtain ⟨U, hUV, hVQU, x, hxV, hxU, hU2, z, hzH, hzo, hz1, hxz, hzU⟩ :=
    exists_dihedral_pair h hsolv hVT hTV hV hVQ
  obtain ⟨A, hAT, -, hAel, hcub, hAV, -, hlt, -⟩ := exists_cubic_of_dihedral_pair hT.2.1 hT.1
    (B6.pCoreOf_two_le_of_isSylowTwoOf hT) hchar hVT hTV hV hUV hVQU hxV hxU hU2 hzH hzo hz1 hxz
    hzU
  exact qhatOf_lt_two_of_cubic (hAT.trans hT.1) (hAT.trans hTV) hAel hcub hAV hlt

end CFSG.Quasithin
