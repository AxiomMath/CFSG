module

public import CFSG.Quasithin.Background.E217Full.QRankTwoIdx
public import CFSG.Quasithin.Background.D2Params

public section

namespace CFSG.Quasithin.E217Full.LemmaQ

open CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem qr2_rkIdx_eq_two {G : Type*} [Group G] {H : Subgroup G} (h : H.index = 4) :
    rkIdx H = 2 := by
  unfold rkIdx
  rw [h, show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]

theorem qr2_two_le_rk [Finite V] {A : Subgroup (MulAut V)} (hA : IsElemAbelian2 A)
    (h4 : 4 ≤ Nat.card ↥A) : 2 ≤ rk A := by
  have : Finite (MulAut V) := MulEquiv.finite_left
  have hcard : Nat.card ↥A = 2 ^ rk A := card_eq_two_pow_of_isPGroup hA.isPGroup
  by_contra h
  have h1 : 2 ^ rk A ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_one] at h1
  omega

theorem qr2_rAV_le_one {A : Subgroup (MulAut V)} (hfix : rkIdx (fixV A) ≤ 2)
    (hrk : 2 ≤ rk A) : rAV A ≤ 1 := by
  have hpos : (0 : ℚ) < (rk A : ℚ) := by exact_mod_cast (show 0 < rk A by omega)
  unfold rAV
  rw [div_le_one₀ hpos]
  exact_mod_cast hfix.trans hrk

theorem rAV_inf_centSub_le_one [Finite V] {X : Subgroup (MulAut V)} {z : MulAut V}
    (hidx : (fixV (Subgroup.zpowers z)).index = 4)
    (hA2 : IsElemAbelian2 (X ⊓ centSub (fixV (Subgroup.zpowers z))))
    (hA4 : 4 ≤ Nat.card ↥(X ⊓ centSub (fixV (Subgroup.zpowers z)))) :
    rAV (X ⊓ centSub (fixV (Subgroup.zpowers z))) ≤ 1 := by
  have hWA : fixV (Subgroup.zpowers z) ≤ fixV (X ⊓ centSub (fixV (Subgroup.zpowers z))) := by
    intro v hv
    rw [mem_fixV]
    intro g hg
    exact (mem_centSub.mp (Subgroup.mem_inf.mp hg).2) v hv
  have hfix : rkIdx (fixV (X ⊓ centSub (fixV (Subgroup.zpowers z)))) ≤ 2 :=
    (rkIdx_anti hWA).trans (qr2_rkIdx_eq_two hidx).le
  exact qr2_rAV_le_one hfix (qr2_two_le_rk hA2 hA4)

theorem qhatOf_le_one_of_index_four [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hV16 : Nat.card V = 16)
    {X : Subgroup (MulAut V)} (hX : IsPGroup 2 X) (h8 : 8 ≤ Nat.card X) {z : MulAut V}
    (hz : z * z = 1) (hzc : ∀ x ∈ X, x * z = z * x)
    (hidx : (fixV (Subgroup.zpowers z)).index = 4) : qhatOf X ≤ ((1 : ℚ) : WithTop ℚ) := by
  have hA2 := isElemAbelian2_inf_centSub hV hz hzc
  have hrel := relIndex_inf_centSub_le_two hV hV16 hX hzc hidx
  have hAle : X ⊓ centSub (fixV (Subgroup.zpowers z)) ≤ X := inf_le_left
  have hmul := Subgroup.relIndex_mul_card (X ⊓ centSub (fixV (Subgroup.zpowers z))) X
  rw [inf_eq_left.mpr hAle] at hmul
  have hA4 : 4 ≤ Nat.card ↥(X ⊓ centSub (fixV (Subgroup.zpowers z))) := by
    by_contra h
    have h1 : (X ⊓ centSub (fixV (Subgroup.zpowers z))).relIndex X *
        Nat.card ↥(X ⊓ centSub (fixV (Subgroup.zpowers z))) ≤ 2 * 3 :=
      Nat.mul_le_mul hrel (by omega)
    omega
  have hne : X ⊓ centSub (fixV (Subgroup.zpowers z)) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hA4
    omega
  have hAX : IsA2 X (X ⊓ centSub (fixV (Subgroup.zpowers z))) := ⟨hAle, hne, hA2⟩
  have hr := rAV_inf_centSub_le_one hidx hA2 hA4
  unfold qhatOf
  exact kq_le_iff.mpr ⟨X ⊓ centSub (fixV (Subgroup.zpowers z)), hAX,
    commSeries_inf_centSub_three hV hz hzc, hr⟩

end CFSG.Quasithin.E217Full.LemmaQ
