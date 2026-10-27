module

public import CFSG.Quasithin.Vol2.Ch7Lem741Odd

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H

section L825K

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem isPGroup_intMod_82 {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (W : Subgroup (IntMod V hV)) : IsPGroup 2 ↥W := fun w =>
  ⟨1, Subtype.ext (by simpa using IntMod.sq_eq_one (w : IntMod V hV))⟩

theorem eq_of_le_of_rkIdx_le_82 {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {W₁ W₂ : Subgroup (IntMod V hV)} (hle : W₁ ≤ W₂) (h : rkIdx W₁ ≤ rkIdx W₂) : W₁ = W₂ := by
  have h1 := rk_add_rkIdx hV W₁
  have h2 := rk_add_rkIdx hV W₂
  have h3 : rk ↥W₂ ≤ rk ↥W₁ := by omega
  have hc1 := card_eq_two_pow_of_isPGroup (isPGroup_intMod_82 hV W₁)
  have hc2 := card_eq_two_pow_of_isPGroup (isPGroup_intMod_82 hV W₂)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hc1, hc2]
  exact Nat.pow_le_pow_right (by norm_num) h3

omit [Finite G] in
theorem le_fixV_convI_82 {V U : Subgroup G} (hV : IsElemAbelian 2 V) {y : G}
    (hyN : y ∈ Subgroup.normalizer (V : Set G)) (hyU : y ∈ Subgroup.centralizer (U : Set G)) :
    U.comap (E3.valHom hV) ≤ fixV (Subgroup.zpowers (convI hV ⟨y, hyN⟩)) := by
  refine A7.le_fixV_zpowers fun u hu => IntMod.val_injective ?_
  rw [convI_apply_val]
  have h := Subgroup.mem_centralizer_iff.1 hyU u.val hu
  change y * u.val * y⁻¹ = u.val
  rw [← h, mul_inv_cancel_right]

theorem lt_mQuot_of_odd_82 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h325 : Stmt3_2_5) (hin : Input8_1_2) (h755 : Input7_5_5)
    (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I)
    (hML : fsuM T L ≤ Subgroup.normalizer (L : Set G)) (hV : IsElemAbelian 2 (fsuV T I))
    (hTI : IsTISetUnder (fsuV T I) (fsuM T L)) {m : ℕ} (hm3 : 3 ≤ m)
    (hmV : m < rk ↥(fsuV T I)) (hα : (m : ℕ∞) < alphaE (autI hV ⊤))
    (hβ : ∀ y ∈ autI hV ⊤, y ≠ 1 → Odd (orderOf y) → rkIdx (fixV (Subgroup.zpowers y)) ≤ m →
      rkIdx (fixV (Subgroup.zpowers y)) = m ∧ orderOf y = 3 ∧
        autI hV ⊤ ⊓ centSub (fixV (Subgroup.zpowers y)) = Subgroup.zpowers y)
    {U : Subgroup G} (hUV : U ≤ fsuV T I)
    (hC : ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (fsuV T I : Set G)) :
    m < mQuot (fsuV T I) U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut (IntMod (fsuV T I) hV)) := MulEquiv.finite_left
  by_contra hle
  push Not at hle
  obtain ⟨-, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hU1 : U ≠ ⊥ := by
    rintro rfl
    have h1 : mQuot (fsuV T I) ⊥ = rk ↥(fsuV T I) := by
      unfold mQuot rk
      rw [Subgroup.relIndex_bot_left]
    omega
  have hαU : (mQuot (fsuV T I) U : ℕ∞) < alphaE (autI hV ⊤) :=
    lt_of_le_of_lt (Nat.cast_le.mpr hle) hα
  obtain ⟨y, ⟨hyN, hyU⟩, hyo, hy1⟩ :=
    exists_odd_741 h37 h38 h39 hmod h325 hin hyp h731 hML hV hUV hC hαU
  set y' := convI hV ⟨y, hyN⟩ with hy'
  have hy'A : y' ∈ autI hV ⊤ := convI_mem_autI hV (Subgroup.mem_top y) hyN
  have hy'1 : y' ≠ 1 := fun h => hy1 ((convI_eq_one_iff hV _).1 h)
  have hy'o : Odd (orderOf y') := by
    refine Odd.of_dvd_nat hyo ?_
    have h := orderOf_map_dvd (convI hV) ⟨y, hyN⟩
    rwa [Subgroup.orderOf_mk] at h
  have hUy := le_fixV_convI_82 hV hyN hyU
  have hrkU := mQuot_eq_rkIdx_comap hV hUV
  have hrky : rkIdx (fixV (Subgroup.zpowers y')) ≤ m :=
    (rkIdx_anti hUy).trans (hrkU ▸ hle)
  obtain ⟨hrkm, hyo3, hcent⟩ := hβ y' hy'A hy'1 hy'o hrky
  have hUeq : U.comap (E3.valHom hV) = fixV (Subgroup.zpowers y') :=
    eq_of_le_of_rkIdx_le_82 hV hUy (by rw [← hrkU, hrkm]; exact hle)
  have hcU : ∀ z ∈ autI hV ⊤, U.comap (E3.valHom hV) ≤ fixV (Subgroup.zpowers z) →
      z ∈ Subgroup.zpowers y' := by
    intro z hz hzU
    rw [← hcent]
    refine ⟨hz, fun u hu => ?_⟩
    rw [← hUeq] at hu
    exact hzU hu z (Subgroup.mem_zpowers z)
  have hinv : ∀ x ∈ autI hV ⊤, x * x = 1 →
      U.comap (E3.valHom hV) ≤ fixV (Subgroup.zpowers x) → x = 1 := by
    intro x hx hxx hxU
    have h1 := hcU x hx hxU
    have h2 : orderOf x ∣ 3 := hyo3 ▸ orderOf_dvd_of_mem_zpowers h1
    have h3 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hxx)
    have h4 : orderOf x ∣ Nat.gcd 3 2 := Nat.dvd_gcd h2 h3
    rw [show Nat.gcd 3 2 = 1 by norm_num, Nat.dvd_one] at h4
    exact orderOf_eq_one_iff.mp h4
  have hCM : ¬ Subgroup.centralizer (U : Set G) ≤ fsuM T L := fun h =>
    hC fun g hg => mem_normalizer_of_ti hTI hUV hU1 (h hg) hg
  obtain ⟨U₂, hUU₂, hU₂V, hCU₂, hmax⟩ := exists_maximal_centralizer hUV hCM
  have hU₂1 : U₂ ≠ ⊥ := fun h => hU1 (le_bot_iff.mp (h ▸ hUU₂))
  have hΓ := mem_gammaE64_of hTI hU₂V hU₂1 hCU₂ fun g hg hg2 =>
    mem_centralizer_of_twoElement hV hTI hUV hU1 hinv hg.1
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hUU₂) hg.2) hg2
  have hU₂le : mQuot (fsuV T I) U₂ ≤ m := (E3.mQuot_mono hUU₂).trans hle
  have hC₂ : ¬ Subgroup.centralizer (U₂ : Set G) ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    fun h => hCU₂ (h.trans hNM)
  obtain ⟨y₂, ⟨hy₂N, hy₂U⟩, hy₂o, hy₂1⟩ := exists_odd_741 h37 h38 h39 hmod h325 hin hyp h731 hML
    hV hU₂V hC₂ (lt_of_le_of_lt (Nat.cast_le.mpr hU₂le) hα)
  set y₂' := convI hV ⟨y₂, hy₂N⟩ with hy₂'
  have hy₂'1 : y₂' ≠ 1 := fun h => hy₂1 ((convI_eq_one_iff hV _).1 h)
  have hU₂y := le_fixV_convI_82 hV hy₂N hy₂U
  have hcomap : U.comap (E3.valHom hV) ≤ U₂.comap (E3.valHom hV) := Subgroup.comap_mono hUU₂
  have hy₂mem : y₂' ∈ Subgroup.zpowers y' :=
    hcU y₂' (convI_mem_autI hV (Subgroup.mem_top y₂) hy₂N) (hcomap.trans hU₂y)
  have hzp : Subgroup.zpowers y₂' = Subgroup.zpowers y' := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy₂mem) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hyo3]
    have h1 : orderOf y₂' ∣ 3 := hyo3 ▸ orderOf_dvd_of_mem_zpowers hy₂mem
    have h2 : orderOf y₂' ≠ 1 := fun h => hy₂'1 (orderOf_eq_one_iff.mp h)
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd h h2
    · rw [h]
  have hU₂U : U₂.comap (E3.valHom hV) ≤ U.comap (E3.valHom hV) := by
    rw [hUeq, ← hzp]
    exact hU₂y
  have hUU : U₂ = U := by
    refine le_antisymm (fun g hg => ?_) hUU₂
    have h1 : (IntMod.mk hV ⟨g, hU₂V hg⟩ : IntMod (fsuV T I) hV) ∈ U₂.comap (E3.valHom hV) := hg
    exact hU₂U h1
  have hmU : mQuot (fsuV T I) U = m := by rw [hrkU, hUeq, hrkm]
  obtain ⟨z, hz, hzo⟩ := h755 G T L I hyp hV U₂ hΓ hmax (by rw [hUU, hmU]; omega)
  rw [hUU, hmU] at hzo
  obtain ⟨g, hgMC, rfl⟩ := (mem_autI hV).mp hz
  have hzU : U.comap (E3.valHom hV) ≤ fixV (Subgroup.zpowers (convI hV g)) := by
    have h1 : convI hV g = convI hV ⟨(g : G), g.2⟩ := rfl
    rw [h1]
    exact le_fixV_convI_82 hV g.2 (hUU ▸ hgMC.2)
  have h1 := hcU _ (convI_mem_autI hV (Subgroup.mem_top _) g.2) hzU
  have h2 : orderOf (convI hV g) ∣ 3 := hyo3 ▸ orderOf_dvd_of_mem_zpowers h1
  rw [hzo] at h2
  have h3 : 2 ^ m - 1 ≤ 3 := Nat.le_of_dvd (by norm_num) h2
  have h4 : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
  omega

end L825K

end CFSG.Quasithin.H13
