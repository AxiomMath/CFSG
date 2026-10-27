module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G42Main
public import CFSG.LocalAnalysis.WeakClosure81.SixTwelveDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s16c1G43_card_V {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Case167_1 D ⊥ V hV L) : Nat.card V = 64 := by
  rw [card_Vtil_eq ⊥ V hV bot_le, Subgroup.card_bot, one_mul]
  exact s16c1_card_of_natOmegaMinus hc.2.1

theorem s16c1G43_conj_not_mem {D : Data G} (h22 : R1622 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) {x : G} (hxV : x ∈ V) (hx1 : x ≠ 1)
    (hCx : centralizer ({x} : Set G) ≤ D.M) {h : G} (hh : h ∉ D.M) : h * x * h⁻¹ ∉ V := by
  intro hxconj
  have hx2 : x ^ 2 = 1 := hV.2 x hxV
  let U : Subgroup G := Subgroup.zpowers x
  have hUV : U ≤ V := Subgroup.zpowers_le.mpr hxV
  have hU2 : ∀ y ∈ U, y = 1 ∨ y = x := by
    intro y hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have horder : orderOf x = 2 := orderOf_eq_prime hx2 hx1
    have hmod : x ^ (k % (2 : ℤ)) = x ^ k := by
      simpa [horder] using zpow_mod_orderOf x k
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [h0, zpow_zero] at hmod
      rw [← hk]
      exact hmod.symm
    · right
      rw [h1, zpow_one] at hmod
      rw [← hk]
      exact hmod.symm
  have hNU_le_cent : Subgroup.normalizer (U : Set G) ≤
      Subgroup.centralizer ({x} : Set G) := by
    intro n hn
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hmem : n * x * n⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.1 hn x).1 (Subgroup.mem_zpowers x)
    rcases hU2 (n * x * n⁻¹) hmem with h1 | h2
    · exfalso
      have : x = 1 := by
        have hc := congrArg (fun y => n⁻¹ * y * n) h1
        simpa [mul_assoc] using hc
      exact hx1 this
    · calc n * x = (n * x * n⁻¹) * n := by group
        _ = x * n := by rw [h2]
  have hΓ : rankThreeGamma 1 2 U ≤ D.M := by
    refine rankThreeGamma_le_of_normalizer_le (M := D.M) (V₀ := U) (Z := U) ?_ le_rfl
    intro X hXU hXne
    have hxX : x ∈ X := by
      by_contra hnot
      exact hXne (le_bot_iff.1 fun y hy => by
        rcases hU2 y (hXU hy) with h1 | h2
        · simpa [h1]
        · exact absurd (h2 ▸ hy) hnot)
    have hXUeq : X = U := le_antisymm hXU (Subgroup.zpowers_le.mpr hxX)
    rw [hXUeq]
    exact hNU_le_cent.trans hCx
  have hhinv : h⁻¹ ∉ D.M := fun h' => hh (by simpa using D.M.inv_mem h')
  have hbot : conjSubgroup U h⁻¹ ⊓ V = ⊥ :=
    h22 V₀ V hS.setting.hyp16 h⁻¹ hhinv U hUV hΓ
  have hmem : h * x * h⁻¹ ∈ conjSubgroup U h⁻¹ := by
    rw [mem_conjSubgroup_iff]
    have e : (h⁻¹) * (h * x * h⁻¹) * (h⁻¹)⁻¹ = x := by group
    rw [e]
    exact Subgroup.mem_zpowers x
  have hmem' : h * x * h⁻¹ ∈ conjSubgroup U h⁻¹ ⊓ V :=
    Subgroup.mem_inf.2 ⟨hmem, hxconj⟩
  rw [hbot, Subgroup.mem_bot] at hmem'
  exact hx1 (by
    have hc := congrArg (fun y => h⁻¹ * y * h) hmem'
    simpa [mul_assoc] using hc)

theorem s16c1G43_singular_of_mem_inf {D : Data G} (h22 : R1622 D) (h41 : R16_41 D)
    {V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D ⊥ V L hV)
    (hc : Case167_1 D ⊥ V hV L) {Q : Vtil ⊥ V hV → ZMod 2} (hQ : IsMinusQuadF2 Q)
    (hQi : QuadInvariant Q (lBar ⊥ V hV L)) {h : G} (hh : h ∉ D.M) {w : IntMod V hV}
    (hw : w.val ∈ conjSubgroup V h) : Q (mkTil ⊥ V hV w) = 0 := by
  by_contra hne
  have hw1 : w.val ≠ 1 := by
    intro h1
    apply hne
    have hone : w = 1 := by
      apply IntMod.val_injective
      change w.val = 1
      exact h1
    rw [hone, map_one]
    exact s16c1G_quad_one hQ.1.1
  have h41' := (h41 ⊥ V L hV hS hc).2 Q hQ hQi
  have hCw : Subgroup.centralizer ({w.val} : Set G) ≤ D.M := by
    have h := (h41'.2 (mkTil ⊥ V hV w) hne).2 w rfl
    change Subgroup.centralizer ({w.val} : Set G) ≤ D.M at h
    exact h
  exact (s16c1G43_conj_not_mem h22 hS w.val_mem hw1 hCw hh)
    (mem_conjSubgroup_iff.1 hw)

theorem s16c1G43_card_inf_le {D : Data G} (h22 : R1622 D) (h41 : R16_41 D)
    {V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D ⊥ V L hV)
    (hc : Case167_1 D ⊥ V hV L) {h : G} (hh : h ∉ D.M) :
    Nat.card ↥(V ⊓ conjSubgroup V h) ≤ 4 := by
  obtain ⟨Q, hQ, hQi⟩ := (h41 ⊥ V L hV hS hc).1
  let W : Subgroup G := V ⊓ conjSubgroup V h
  let Wt : Subgroup (Vtil ⊥ V hV) := imgTil ⊥ V hV W
  have hsq : ∀ x : Vtil ⊥ V hV, x ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  have hzero : ∀ q ∈ Wt, Q q = 0 := by
    intro q hq
    obtain ⟨x, hxW, rfl⟩ := (mem_imgTil ⊥ V hV W q).1 hq
    exact s16c1G43_singular_of_mem_inf h22 h41 hS hc hQ hQi hh (Subgroup.mem_inf.1 hxW).2
  have hrk : rk ↥Wt ≤ 2 :=
    s16c1G_rk_le_two (s16c1G_rk_top D hc) (fun x => by simpa [pow_two] using hsq x) hQ hzero
  have hcardWt : Nat.card Wt = 2 ^ rk Wt := card_eq_two_pow hsq Wt
  have hWt_le : Nat.card Wt ≤ 4 := by
    rw [hcardWt]
    calc 2 ^ rk Wt ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hrk
      _ = 4 := by norm_num
  have hcard_Wt : Nat.card Wt = Nat.card W := by
    have hmkTil_inj : Function.Injective (mkTil ⊥ V hV) := (TwelveShort.mkTilEquiv V hV).injective
    have h1 : Nat.card Wt = Nat.card (intSub V hV W) := by
      show Nat.card ((intSub V hV W).map (mkTil ⊥ V hV)) = Nat.card (intSub V hV W)
      exact Subgroup.card_map_of_injective hmkTil_inj
    rw [h1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : W ≤ V)).toEquiv
  change Nat.card ↥W ≤ 4
  rw [← hcard_Wt]
  exact hWt_le

theorem s16c1G43_lt_rStar {D : Data G} (h22 : R1622 D) (h41 : R16_41 D)
    {V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D ⊥ V L hV)
    (hc : Case167_1 D ⊥ V hV L) : (1 : ℕ∞) < rStarMV D.M V := by
  have hV64 : Nat.card V = 64 := s16c1G43_card_V hc
  have h2le : (2 : ℕ∞) ≤ rStarMV D.M V := by
    unfold rStarMV
    refine le_iInf₂ fun U hU => ?_
    obtain ⟨hUV, hN⟩ := hU
    obtain ⟨x, hxN, hxM⟩ := SetLike.not_le_iff_exists.1 hN
    have hUle : U ≤ V ⊓ conjSubgroup V x := by
      refine le_inf hUV ?_
      intro u hu
      rw [mem_conjSubgroup_iff]
      exact hUV ((Subgroup.mem_normalizer_iff.1 hxN u).1 hu)
    have hcardU : Nat.card ↥U ≤ 4 := by
      have h1 : Nat.card ↥U ≤ Nat.card ↥(V ⊓ conjSubgroup V x) :=
        Nat.card_le_card_of_injective (fun u : ↥U => ⟨u.val, hUle u.2⟩)
          (fun a b hab => by
            apply Subtype.ext
            exact congrArg (fun w : ↥(V ⊓ conjSubgroup V x) => (w : G)) hab)
      exact h1.trans (s16c1G43_card_inf_le h22 h41 hS hc hxM)
    have hcard := E3.card_eq_two_pow_mul hV.isPGroup hUV
    have h64 : 2 ^ E3.mQuot V U * Nat.card ↥U = 64 := by
      rw [← hcard]
      exact hV64
    have hq2 : 2 ≤ E3.mQuot V U := by
      have h16 : 16 ≤ 2 ^ E3.mQuot V U := by
        have h1 : 2 ^ E3.mQuot V U * Nat.card ↥U ≤ 2 ^ E3.mQuot V U * 4 :=
          Nat.mul_le_mul_left _ hcardU
        rw [h64] at h1
        omega
      have h16' : 2 ^ (4 : ℕ) ≤ 2 ^ E3.mQuot V U := by
        rw [show (2 : ℕ) ^ 4 = 16 by norm_num]
        exact h16
      have hq4 : 4 ≤ E3.mQuot V U :=
        (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h16'
      exact le_trans (by norm_num : (2 : ℕ) ≤ 4) hq4
    exact ENat.natCast_le_natCast.mpr hq2
  exact lt_of_lt_of_le (by norm_num : (1 : ℕ∞) < 2) h2le

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
