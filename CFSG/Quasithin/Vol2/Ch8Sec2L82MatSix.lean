module

public import CFSG.Quasithin.Background.HMathieuM21
public import CFSG.Quasithin.Background.HModelType
public import CFSG.Quasithin.Background.HSporLatMathieu
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch8Sec2L822M22FSylow

public section

namespace CFSG.Quasithin.H13.Mat

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.M22F
open CFSG.Quasithin.H.NPrimeHall CFSG.Quasithin.H.MathieuLat
open scoped Pointwise

@[expose] def Code22SixNoPerm2_m22f : Prop :=
  ∀ X S F : Subgroup (MulAut W10),
    (rhoC10 mog22 mog22_le_mog22plus).range < X → X ≤ (rhoC10 mog22plus le_rfl).range →
    S ≤ X → IsPGroup 2 ↥S → rk ↥S = rk ↥X → F ≤ X → (∀ x ∈ F, Nat.Coprime (orderOf x) 6) →
    (F : Set (MulAut W10)) * (S : Set (MulAut W10)) =
      ((F ⊔ S : Subgroup (MulAut W10)) : Set (MulAut W10)) → F = ⊥

section Generic

variable {G : Type*} [Group G] [Finite G]

private theorem card_set_mul_six {R Y : Subgroup G} (hRY : R ⊓ Y = ⊥) :
    Nat.card ((R : Set G) * (Y : Set G)) = Nat.card R * Nat.card Y := by
  rw [Subgroup.card_mul_eq_card_subgroup_mul_card_quotient, mul_comm]
  congr 1
  rw [Nat.card_image_of_injOn]
  · rfl
  · intro a ha b hb hab
    have h := QuotientGroup.eq.mp hab
    have hmem : a⁻¹ * b ∈ R ⊓ Y := ⟨R.mul_mem (R.inv_mem ha) hb, h⟩
    rw [hRY, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact hmem

theorem six_of_indexThree {L X S F : Subgroup G} (hL : IndexThree L) (hLX : L ≤ X)
    (hX : Nat.card X = 2 * Nat.card L) (hLc : Nat.card L = 443520) (hSX : S ≤ X)
    (hSp : IsPGroup 2 ↥S) (hSc : Nat.card S = 256) (hFX : F ≤ X)
    (hcop : ∀ x ∈ F, Nat.Coprime (orderOf x) 6)
    (hset : (F : Set G) * (S : Set G) = ((F ⊔ S : Subgroup G) : Set G)) : F = ⊥ := by
  classical
  have hrelX : L.relIndex X = 2 := by
    have h := Subgroup.relIndex_mul_card (H := L) (K := X)
    rw [inf_of_le_left hLX, hX] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hrel_le : ∀ K : Subgroup G, K ≤ X → L.relIndex K ≤ 2 := fun K hK => by
    have := Subgroup.relIndex_le_of_le_right (H := L) hK (by rw [hrelX]; norm_num)
    rwa [hrelX] at this
  have hSL : Nat.card ↥(L ⊓ S) = 128 := by
    have h1 := Subgroup.relIndex_mul_card (H := L) (K := S)
    have h2 : L.relIndex S ≤ 2 := hrel_le S hSX
    have h3 : Nat.card ↥(L ⊓ S) ∣ Nat.card L := Subgroup.card_dvd_of_le inf_le_left
    rw [hSc] at h1
    rw [hLc] at h3
    generalize L.relIndex S = r at h1 h2
    generalize Nat.card ↥(L ⊓ S) = c at h1 h3 ⊢
    interval_cases r
    · omega
    · have hc : c = 256 := by omega
      subst hc
      exact absurd h3 (by norm_num)
    · omega
  have hPL : IsSylowIn 2 (L ⊓ S) L := by
    refine ⟨inf_le_left, hSp.to_le inf_le_right, ?_⟩
    have h := Subgroup.relIndex_mul_card (H := L ⊓ S) (K := L)
    rw [inf_of_le_left (inf_le_left : L ⊓ S ≤ L), hSL, hLc] at h
    omega
  have hFS : F ⊓ S = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨hxF, hxS⟩ := hx
    obtain ⟨k, hk⟩ := hSp ⟨x, hxS⟩
    have hk' : x ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hc2 : Nat.Coprime (orderOf x) 2 :=
      Nat.Coprime.coprime_dvd_right (by norm_num : 2 ∣ 6) (hcop x hxF)
    have h1 : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hc2) hd
    exact orderOf_eq_one_iff.mp h1
  have hY : Nat.card ↥(F ⊔ S) = Nat.card F * 256 := by
    have h := card_set_mul_six hFS
    rw [hset, hSc] at h
    exact h
  have hYX : F ⊔ S ≤ X := sup_le hFX hSX
  have hPH : L ⊓ S ≤ L ⊓ (F ⊔ S) := inf_le_inf_left L le_sup_right
  have hidx := hL (L ⊓ S) (L ⊓ (F ⊔ S)) hPL hPH inf_le_left
  have h1 := Subgroup.relIndex_mul_card (H := L) (K := F ⊔ S)
  have h2 : L.relIndex (F ⊔ S) ≤ 2 := hrel_le _ hYX
  rw [hY] at h1
  have hFpos : 0 < Nat.card F := Nat.card_pos
  rcases hidx with hA | hB
  · rw [hSL] at hA
    rw [hA] at h1
    have hf1 : Nat.card F = 1 := by omega
    exact Subgroup.eq_bot_of_card_eq F hf1
  · rw [hSL] at hB
    have h3 : 3 ∣ Nat.card F := by
      have := dvd_trans hB (Dvd.intro_left _ h1)
      omega
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥F) 3 h3
    have hox : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe, hx]
    have := hcop (x : G) x.2
    rw [hox] at this
    exact absurd this (by norm_num)

end Generic

theorem indexThree_range_m22 :
    IndexThree (rhoC10 mog22 mog22_le_mog22plus).range := by
  have hinj : Function.Injective
      ((rhoC10 mog22 mog22_le_mog22plus).comp
        (mog22EquivM22.symm.toMonoidHom : CFSG.Blueprint.NativeSporadic.M22 →* ↥mog22)) :=
    (CFSG.Quasithin.H.ModelType.rhoC10_mog22_injective).comp mog22EquivM22.symm.injective
  have h := indexThree_map hinj m22_indexThree
  have hr : (⊤ : Subgroup CFSG.Blueprint.NativeSporadic.M22).map
      ((rhoC10 mog22 mog22_le_mog22plus).comp
        (mog22EquivM22.symm.toMonoidHom : CFSG.Blueprint.NativeSporadic.M22 →* ↥mog22)) =
      (rhoC10 mog22 mog22_le_mog22plus).range := by
    rw [← MonoidHom.range_eq_map, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr mog22EquivM22.symm.surjective, ← MonoidHom.range_eq_map]
  rwa [hr] at h

theorem code22SixNoPerm2_m22f_proved :
    Code22SixNoPerm2_m22f := by
  intro X S F hLX hXp hSX hSp hrk hFX hcop hset
  have hcardXp : Nat.card ↥(rhoC10 mog22plus le_rfl).range = 887040 :=
    (Nat.card_congr (MonoidHom.ofInjective rhoC10_mog22plus_injective).toEquiv).symm.trans
      card_mog22plus
  have hcardL : Nat.card ↥(rhoC10 mog22 mog22_le_mog22plus).range = 443520 :=
    ((Nat.card_congr (MonoidHom.ofInjective (CFSG.Quasithin.H.ModelType.rhoC10_mog22_injective)).toEquiv).symm).trans
      card_mog22
  have hLle := hLX.le
  have hXc : Nat.card ↥X = 887040 := by
    have h1 : Nat.card ↥(rhoC10 mog22 mog22_le_mog22plus).range ∣ Nat.card ↥X :=
      Subgroup.card_dvd_of_le hLle
    have h2 : Nat.card ↥X ∣ Nat.card ↥(rhoC10 mog22plus le_rfl).range :=
      Subgroup.card_dvd_of_le hXp
    rw [hcardXp] at h2
    rw [hcardL] at h1
    have hne : Nat.card ↥X ≠ 443520 := by
      intro h
      have : (rhoC10 mog22 mog22_le_mog22plus).range = X :=
        Subgroup.eq_of_le_of_card_ge hLle (by rw [h, hcardL])
      exact hLX.ne this
    obtain ⟨m, hm⟩ := h1
    have hle := Nat.le_of_dvd (by norm_num) h2
    have hpos : 0 < Nat.card ↥X := Nat.card_pos
    omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hSp
  have hrkS : rk ↥S = n := by
    unfold rk
    rw [hn]
    exact padicValNat.prime_pow n
  have hrkX : rk ↥X = 8 := by
    unfold rk
    rw [hXc, show (887040 : ℕ) = 2 ^ 8 * 3465 by norm_num,
      padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have hSc : Nat.card ↥S = 256 := by
    have : n = 8 := by rw [← hrkS, hrk, hrkX]
    rw [hn, this]
    norm_num
  exact six_of_indexThree indexThree_range_m22 hLle (by rw [hXc, hcardL]) hcardL hSX hSp hSc hFX
    hcop hset

end CFSG.Quasithin.H13.Mat
