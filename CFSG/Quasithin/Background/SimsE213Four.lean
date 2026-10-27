module

public import CFSG.Quasithin.Background.SimsE213M
public import CFSG.Quasithin.Vol2.E2FourteenC

public section

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def DihFour : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H T M V : Subgroup Γ) (h : E2.Hyp28 H T M V), CharTwo H →
    ∀ (I : Subgroup Γ) (g : Γ), IsInIHTV H T M V I → g ∈ I → I = V ⊔ conjSubgroup V g →
      ∀ A : Subgroup Γ, A = conjSubgroup V g ⊓ pCoreOf 2 I →
        ∀ p a : ℕ, p.Prime → p ≠ 2 → 1 ≤ a →
          Nonempty (E2.StarQuot (M ⊓ I) I ≃* DihedralGroup (p ^ a)) →
          E2.dParamPrime (p ^ a) ≤ rk ↥(autI h.elem A)

namespace E213

section Pair

variable {G : Type} [Group G] [Finite G] {X T M V : Subgroup G} {g : G}

theorem exists_two_pow_le_sq (h : E2.Pair X T M V g) (hchar : CharTwo X) {c : G} (hcX : c ∈ X)
    {ℓ a : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hc : orderOf c = ℓ ^ (a + 1)) :
    ∃ m : ℕ, 0 < m ∧ ℓ ^ (a + 1) ∣ 2 ^ m - 1 ∧
      2 ^ m ≤ ((V ⊓ B6.conjSub g V).relIndex (kerIn M X ⊓ V)) ^ 2 := by
  obtain ⟨m, hm0, hdvd, hle⟩ := h.exists_two_pow_le_relIndex_P hchar hcX hℓ hℓ2 hc
  exact ⟨m, hm0, hdvd, hle.trans (Ch3E213M.relIndex_P_eq h).le⟩

theorem two_pow_le_sq_of_ppd (h : E2.Pair X T M V g) (hchar : CharTwo X) {r n : ℕ} (hn : 0 < n)
    (hr : CFSG.Timmesfeld.IsPrimitivePrimeDivisor r n) (hrX : r ∣ Nat.card X) :
    2 ^ n ≤ ((V ⊓ B6.conjSub g V).relIndex (kerIn M X ⊓ V)) ^ 2 := by
  have : Fact r.Prime := ⟨hr.prime⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' r hrX
  obtain ⟨m, hm0, hmdvd, hmP⟩ := exists_two_pow_le_sq h hchar c.2 (a := 0) hr.prime
    (hr.ne_two hn) (by rw [pow_one, Subgroup.orderOf_coe, hc])
  rw [zero_add, pow_one] at hmdvd
  exact (Nat.pow_le_pow_right two_pos
    (Nat.le_of_dvd hm0 ((hr.dvd_sub_one_iff hn m).1 hmdvd))).trans hmP

theorem two_pow_six_le_sq (h : E2.Pair X T M V g) (hchar : CharTwo X) {c : G} (hcX : c ∈ X)
    (hc : orderOf c = 9) : 2 ^ 6 ≤ ((V ⊓ B6.conjSub g V).relIndex (kerIn M X ⊓ V)) ^ 2 := by
  obtain ⟨m, hm0, hdvd, hmP⟩ := exists_two_pow_le_sq h hchar hcX (ℓ := 3) (a := 1)
    Nat.prime_three (by norm_num) (by rw [hc]; norm_num)
  have h6 : 6 ∣ m := Ch3E213M.six_dvd_of_nine_dvd_two_pow_sub_one (by simpa using hdvd)
  exact (Nat.pow_le_pow_right two_pos (Nat.le_of_dvd hm0 h6)).trans hmP

end Pair

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem card_autI_eq_relIndex {H T M V I : Subgroup Γ} {g : Γ} (h : E2.Hyp28 H T M V)
    (hp : E2.Pair I (T ⊓ I) (M ⊓ I) V g⁻¹) {A : Subgroup Γ}
    (hA : A = conjSubgroup V g ⊓ pCoreOf 2 I) (hAN : A ≤ Subgroup.normalizer (V : Set Γ))
    (hCA : A ⊓ Subgroup.centralizer (V : Set Γ) = V ⊓ conjSubgroup V g) :
    Nat.card ↥(autI h.elem A) = (V ⊓ B6.conjSub g⁻¹ V).relIndex (kerIn (M ⊓ I) I ⊓ V) := by
  rw [SimsE210.conjSubgroup_eq_conjSub] at hA hCA
  have hconjB : B6.conjSub g⁻¹ (kerIn (M ⊓ I) I ⊓ V) = A := by
    rw [hA, hp.conjSub_kerIn_inf_eq]
  have hconjZ : B6.conjSub g⁻¹ (V ⊓ B6.conjSub g⁻¹ V) = V ⊓ B6.conjSub g⁻¹ V :=
    hp.conjSub_inf_conj hp.mem
  rw [card_autI_eq h.elem hAN, hCA, ← hconjB]
  conv_lhs => rw [← hconjZ]
  show ((V ⊓ B6.conjSub g⁻¹ V).map (MulAut.conj g⁻¹).toMonoidHom).relIndex
      ((kerIn (M ⊓ I) I ⊓ V).map (MulAut.conj g⁻¹).toMonoidHom) = _
  exact Subgroup.relIndex_map_map_of_injective _ _ fun x y hxy => (MulAut.conj g⁻¹).injective hxy

end E213

open E213

theorem e213_four_nondih
    {Γ : Type} [Group Γ] [Finite Γ] (H T M V : Subgroup Γ) (h : E2.Hyp28 H T M V)
    (hc : CharTwo H) (I : Subgroup Γ) (g : Γ) (hI : IsInIHTV H T M V I) (hg : g ∈ I)
    (hIV : I = V ⊔ conjSubgroup V g) (A : Subgroup Γ) (hA : A = conjSubgroup V g ⊓ pCoreOf 2 I) :
    (∀ k : ℕ, 1 < k → IsPSL 2 2 k (E2.StarQuot (M ⊓ I) I) → k ≤ rk ↥(autI h.elem A)) ∧
      (∀ k : ℕ, IsSz k (E2.StarQuot (M ⊓ I) I) → 2 * k ≤ rk ↥(autI h.elem A)) ∧
      (∀ k : ℕ, 1 ≤ k → IsSp4Full k (E2.StarQuot (M ⊓ I) I) → 2 * k ≤ rk ↥(autI h.elem A)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgen : I = V ⊔ B6.conjSub g⁻¹ V := SimsE210.conjSubgroup_eq_conjSub V g ▸ hIV
  obtain ⟨hp, -⟩ := RonanE211.e2_11C_all E2.kgSz8CoverInvolutions_holds
    E2.kgI22One_holds h (E213M.noRoot_of_isInIHTV hI) (I.inv_mem hg) hgen
  have hcharI : CharTwo I := by
    have := E2.charTwo_of_charTwo h (hI.1 (I.inv_mem hg)) hc
    rwa [← hgen] at this
  obtain ⟨⟨hAeq, -, -, hCA, -⟩, -⟩ := e213_member H T M V h hc I g hI hg hIV A hA
  have hcard := card_autI_eq_relIndex h hp hA (hAeq ▸ inf_le_right) hCA
  obtain ⟨b, hb⟩ := E213M.exists_relIndex_eq_two_pow
    ((B6.isPGroup_of_isElemAbelian h.elem).to_le inf_le_right) (V ⊓ B6.conjSub g⁻¹ V)
  have hrk : rk ↥(autI h.elem A) = b := by
    unfold rk
    rw [hcard, hb, padicValNat.prime_pow]
  have key : ∀ n : ℕ, 2 ^ n ≤ ((V ⊓ B6.conjSub g⁻¹ V).relIndex (kerIn (M ⊓ I) I ⊓ V)) ^ 2 →
      n ≤ 2 * rk ↥(autI h.elem A) := by
    intro n hn
    rw [hb, ← pow_mul] at hn
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hn
    omega
  have hdvdI : ∀ r : ℕ, r ∣ Nat.card (E2.StarQuot (M ⊓ I) I) → r ∣ Nat.card I := fun r hr => by
    rw [← E2.relIndex_kerIn_eq_card] at hr
    exact hr.trans (Subgroup.relIndex_dvd_card _ _)
  refine ⟨fun k hk hP => ?_, fun k hSz => ?_, fun k hk hY => ?_⟩
  ·
    obtain ⟨K, _, _, hK, ⟨θ⟩⟩ := Ch3E213M.exists_equiv_projectiveSL_of_isPSL hP
    by_cases hk3 : k = 3
    · subst hk3
      obtain ⟨c, hc9⟩ := Ch3E213M.exists_orderOf_nine_projectiveSL hK
      obtain ⟨x, hxI, hx⟩ := E2.exists_orderOf_nine_of_star (c := θ.symm c)
        (by rw [MulEquiv.orderOf_eq, hc9])
      have := key 6 (two_pow_six_le_sq hp hcharI hxI hx)
      omega
    · have hcardI : Nat.card (E2.StarQuot (M ⊓ I) I) = 2 ^ k * ((2 ^ k) ^ 2 - 1) := by
        rw [Nat.card_congr θ.toEquiv, Ch3E213M.card_projectiveSL_two_pow hK]
      obtain ⟨r, hr⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 2 * k) (by omega)
        (by omega)
      have hq : (2 ^ k) ^ 2 = 2 ^ (2 * k) := by rw [← pow_mul, mul_comm]
      have hrI : r ∣ Nat.card I :=
        hdvdI r ((hq ▸ hr.2.1 : r ∣ (2 ^ k) ^ 2 - 1).trans (Dvd.intro_left _ hcardI.symm))
      have := key (2 * k) (two_pow_le_sq_of_ppd hp hcharI (by omega) hr hrI)
      omega
  ·
    obtain ⟨hk3, hcardI⟩ := E2.card_of_isSz hSz
    obtain ⟨r, hr⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 4 * k) (by omega)
      (by omega)
    have hrI : r ∣ Nat.card I := hdvdI r
      (((Ch3E213M.primitive_dvd_sq_add_one (by omega) hr).trans (Dvd.intro _ rfl)).trans
        (Dvd.intro_left _ hcardI.symm))
    have := key (4 * k) (two_pow_le_sq_of_ppd hp hcharI (by omega) hr hrI)
    omega
  ·
    obtain ⟨r, hr⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 4 * k) (by omega)
      (by omega)
    have hrI : r ∣ Nat.card I :=
      hdvdI r ((Ch3E213M.primitive_dvd_sq_add_one hk hr).trans (E213M.sq_add_one_dvd_card hY))
    have := key (4 * k) (two_pow_le_sq_of_ppd hp hcharI (by omega) hr hrI)
    omega

end CFSG.Quasithin.SimsE2
