module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN2F4Module
public import CFSG.Quasithin.Background.E3Odd

public noncomputable section
public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open CFSG.QuasithinUnique

theorem fixedSubmodule_eq_of_finrank_eq_sub_one
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Y : Submodule K V} {g : V ≃ₗ[K] V}
    (hY : Y ≤ fixedSubmodule g.toLinearMap)
    (hfin : Module.finrank K Y + 1 = Module.finrank K V)
    (hg : g ≠ 1) :
    fixedSubmodule g.toLinearMap = Y := by
  set F := fixedSubmodule g.toLinearMap with hF
  have hYF : Module.finrank K Y ≤ Module.finrank K F := Submodule.finrank_mono hY
  have hFV : Module.finrank K F ≤ Module.finrank K V := Submodule.finrank_le F
  have hcases : Module.finrank K F = Module.finrank K Y ∨
      Module.finrank K F = Module.finrank K V := by omega
  rcases hcases with hcase | hcase
  · exact (Submodule.eq_of_le_of_finrank_eq hY hcase.symm).symm
  · exfalso
    have htop : F = ⊤ := Submodule.eq_top_of_finrank_eq hcase
    apply hg
    ext v
    have hv : v ∈ F := htop ▸ Submodule.mem_top
    rw [hF, mem_fixedSubmodule] at hv
    exact hv

theorem sixfourteen_n3_first_reduction {W : Type} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1)
    {G X D : Subgroup (MulAut W)} {s : MulAut W} {Y : Subgroup W} {n : ℕ}
    (hK : CFSG.Open.IsKGroup ↥G) (hpCore : pCoreOf 2 G = ⊥)
    (hirr : ∀ Z : Subgroup W, (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) → Z = ⊥ ∨ Z = ⊤)
    (ht2 : ∃ t ∈ G, orderOf t = 2 ∧ rkIdx (fixV (Subgroup.zpowers t)) ≤ 3)
    (hXG : X ≤ G) (hXnorm : ∀ g ∈ G, ∀ y ∈ X, g * y * g⁻¹ ∈ X)
    (hXcard : Nat.card X = 3)
    (hsG : s ∈ G) (hs_ord2 : orderOf s = 2)
    (hs_not_cent : s ∉ Subgroup.centralizer (X : Set (MulAut W)))
    (hYinv : ∀ a ∈ X, ∀ y ∈ Y, a y ∈ Y) (hYrk : rkIdx Y = 2)
    (hW : Nat.card W = 4 ^ n)
    (hD : D ≤ G) (hDCX : ∀ d ∈ D, ∀ x ∈ X, d * x = x * d)
    (hDs : ∀ d ∈ D, d * s = s * d)
    (hElem : CFSG.Quasithin.IsElemAbelian2 D) (hDcard : Nat.card D = 2 ^ (n - 1))
    (hYD : Y ≤ fixV D)
    (hn : 2 < n) :
    D ∈ CFSG.Quasithin.E3.aSet 2 G ∧
      D ≤ Subgroup.centralizer (CFSG.QuasithinUnique.oddCoreIn G : Set (MulAut W)) := by
  have hXne : X ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hXcard
    omega
  have hfixX : fixV X = ⊥ := fixV_eq_bot_of_irreducible hirr hXG hXnorm hXne
  have hXcard' : Nat.card ↥X = 3 := hXcard
  letI : Fintype ↥X := Fintype.ofFinite _
  have hXcardF : Fintype.card ↥X = 3 := by
    rw [← Nat.card_eq_fintype_card, hXcard']
  obtain ⟨xX, hxXne⟩ : ∃ xX : ↥X, xX ≠ 1 := by
    refine Fintype.exists_ne_of_one_lt_card ?_ (1 : ↥X)
    rw [hXcardF]
    norm_num
  let x : MulAut W := xX
  have hxX : x ∈ X := xX.2
  have hx_ne : x ≠ 1 := by
    intro h
    exact hxXne (Subtype.ext h)
  have hx_ord_dvd : orderOf x ∣ 3 := by
    have h : orderOf xX ∣ 3 := by
      have h2 := orderOf_dvd_natCard xX
      rwa [Nat.card_eq_fintype_card, hXcardF] at h2
    rwa [← Subgroup.orderOf_coe xX] at h
  have hx_ord3 : orderOf x = 3 := by
    rcases (by norm_num : Nat.Prime 3).eq_one_or_self_of_dvd (orderOf x) hx_ord_dvd with
      h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hx_ne
    · exact h3
  have hx3 : x ^ 3 = 1 := by
    rw [← hx_ord3]
    exact pow_orderOf_eq_one x
  have hxgen : X = Subgroup.zpowers x := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxX) ?_
    rw [Nat.card_zpowers, hx_ord3, hXcard]
  have hfix : fixV (Subgroup.zpowers x) = ⊥ := by
    rw [← hxgen]
    exact hfixX

  have hWpow : Nat.card W = 2 ^ (2 * n) := by
    rw [hW, show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]
  have hYidx_dvd : Y.index ∣ 2 ^ (2 * n) := by
    rw [← hWpow]
    exact ⟨Nat.card Y, by rw [mul_comm]; exact (Y.card_mul_index).symm⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hYidx_dvd
  have hk2 : k = 2 := by
    have h := hYrk
    change padicValNat 2 Y.index = 2 at h
    rw [hk, padicValNat.pow, padicValNat_self] at h
    norm_num at h
    exact h
  have hYidx : Y.index = 4 := by
    rw [hk, hk2]
    norm_num
  have hcardY : Nat.card Y = 4 ^ (n - 1) := by
    have hcard := Y.card_mul_index
    rw [hW, hYidx] at hcard
    have hpow : (4 : ℕ) ^ n = 4 ^ (n - 1) * 4 := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    rw [hpow] at hcard
    exact Nat.mul_right_cancel (by norm_num : 0 < 4) hcard

  have hDne : D ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hDcard
    have hgt : 1 < 2 ^ (n - 1) := Nat.one_lt_pow (by omega) (by norm_num : 1 < 2)
    omega
  have hDgt : 1 < Nat.card D := by
    rw [hDcard]
    exact Nat.one_lt_pow (by omega) (by norm_num : 1 < 2)
  letI : Fintype ↥D := Fintype.ofFinite _
  obtain ⟨dD, hdDne⟩ : ∃ dD : ↥D, dD ≠ 1 := by
    refine Fintype.exists_ne_of_one_lt_card ?_ (1 : ↥D)
    rw [← Nat.card_eq_fintype_card]
    exact hDgt
  let d : MulAut W := dD
  have hdD : d ∈ D := dD.2
  have hd_ne : d ≠ 1 := by
    intro h
    exact hdDne (Subtype.ext h)
  have hDpg : IsPGroup 2 D := E3.isPGroup_of_isElemAbelian2 hElem

  have hfix_of_mem : ∀ d : MulAut W, d ∈ D → d ≠ 1 → fixV (Subgroup.zpowers d) = Y := by
    intro d hdD hd_ne
    have hcomm : d * x = x * d := hDCX d hdD x hxX
    have hzp_le_D : Subgroup.zpowers d ≤ D := Subgroup.zpowers_le.mpr hdD
    have hYleZ : Y ≤ fixV (Subgroup.zpowers d) :=
      fun w hw y hy => hYD hw y (hzp_le_D hy)
    have hd_ord2 : orderOf d = 2 :=
      orderOf_eq_prime (by simpa [pow_two] using hElem.2 d hdD) hd_ne
    letI := galoisModule hw2 x hx3 hfix
    let Ys : Submodule (GaloisField 2 2) (Additive W) :=
      YSubmodule hw2 x hx3 hfix hxX hYinv
    have hKcard : Nat.card (GaloisField 2 2) = 4 := by
      rw [GaloisField.card 2 2 (by norm_num)]
      norm_num
    have hYcardYs : Nat.card Ys = 4 ^ (n - 1) := by
      calc Nat.card Ys = Nat.card Y :=
            (Nat.card_congr (YSubmoduleEquiv hw2 x hx3 hfix hxX hYinv)).symm
        _ = 4 ^ (n - 1) := hcardY
    have hVn : Module.finrank (GaloisField 2 2) (Additive W) = n := by
      have h := Module.natCard_eq_pow_finrank (K := GaloisField 2 2) (V := Additive W)
      change Nat.card W = Nat.card (GaloisField 2 2) ^
        Module.finrank (GaloisField 2 2) (Additive W) at h
      rw [hW, hKcard] at h
      exact (Nat.pow_right_injective (by norm_num : 2 ≤ 4) h).symm
    have hYn : Module.finrank (GaloisField 2 2) Ys = n - 1 := by
      have h := Module.natCard_eq_pow_finrank (K := GaloisField 2 2) (V := Ys)
      rw [hYcardYs, hKcard] at h
      exact (Nat.pow_right_injective (by norm_num : 2 ≤ 4) h).symm
    have hfin : Module.finrank (GaloisField 2 2) Ys + 1 =
        Module.finrank (GaloisField 2 2) (Additive W) := by omega
    have hYfix : Ys ≤ fixedSubmodule
        (hGaloisLinearEquiv hw2 x hx3 hfix d hcomm).toLinearMap :=
      YSubmodule_le_fixedSubmodule hw2 x hx3 hfix hxX hYinv hdD hYD hcomm
    have hg_ne : hGaloisLinearEquiv hw2 x hx3 hfix d hcomm ≠ 1 :=
      hGaloisLinearEquiv_ne_one hw2 x hx3 hfix hcomm hd_ne
    have hF_eq : fixedSubmodule
        (hGaloisLinearEquiv hw2 x hx3 hfix d hcomm).toLinearMap = Ys :=
      fixedSubmodule_eq_of_finrank_eq_sub_one hYfix hfin hg_ne
    have hgapp_of : ∀ w : W,
        (hGaloisLinearEquiv hw2 x hx3 hfix d hcomm) (Additive.ofMul w) =
          Additive.ofMul (d w) := by
      intro w
      calc
        (hGaloisLinearEquiv hw2 x hx3 hfix d hcomm) (Additive.ofMul w)
            = (autAddHom d) (Additive.ofMul w) :=
              hGaloisLinearEquiv_apply (hw2 := hw2) (x := x) (hx3 := hx3)
                (hfix := hfix) (h := d) hcomm (Additive.ofMul w)
        _ = Additive.ofMul (d w) := by
              rw [autAddHom_apply]
              simp
    have hcardF : Nat.card (fixedSubmodule
        (hGaloisLinearEquiv hw2 x hx3 hfix d hcomm).toLinearMap) = Nat.card Ys := by
      rw [hF_eq]
    have hcardYsY : Nat.card Ys = Nat.card Y := by
      rw [hYcardYs, hcardY]
    have hcardZ : Nat.card (fixV (Subgroup.zpowers d)) =
        Nat.card (fixedSubmodule
          (hGaloisLinearEquiv hw2 x hx3 hfix d hcomm).toLinearMap) := by
      refine Nat.card_congr ?_
      refine
        { toFun := fun z => ⟨Additive.ofMul z.1, ?_⟩
          invFun := fun v => ⟨Additive.toMul v.1, ?_⟩
          left_inv := fun z => by ext; simp
          right_inv := fun v => by ext; simp }
      · rw [mem_fixedSubmodule]
        have hdz : d z.1 = z.1 :=
          (mem_fixV.mp z.2) d (Subgroup.mem_zpowers d)
        exact (hgapp_of z.1).trans (by rw [hdz])
      · rw [mem_fixV]
        intro y hy
        have hdv : d (Additive.toMul v.1) = Additive.toMul v.1 := by
          have h := mem_fixedSubmodule.mp v.2
          have hgapp_v := hGaloisLinearEquiv_apply (hw2 := hw2) (x := x) (hx3 := hx3)
            (hfix := hfix) (h := d) hcomm v.1
          have h' : (autAddHom d) v.1 = v.1 := hgapp_v.symm.trans h
          have h'' := congrArg (fun a : Additive W => Additive.toMul a) h'
          simpa [autAddHom_apply] using h''
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        rw [← zpow_mod_orderOf d k, hd_ord2]
        norm_num
        rcases Int.emod_two_eq_zero_or_one k with hk | hk
        · rw [hk]
          simp
        · rw [hk]
          simpa using hdv
    apply (Subgroup.eq_of_le_of_card_ge hYleZ ?_).symm
    rw [hcardZ, hcardF, hcardYsY]

  have hfixD : fixV D = Y := by
    apply le_antisymm
    · intro w hw
      have hw' : w ∈ fixV (Subgroup.zpowers d) := by
        rw [mem_fixV]
        intro y hy
        exact hw y (Subgroup.zpowers_le.mpr hdD hy)
      rwa [hfix_of_mem d hdD hd_ne] at hw'
    · exact hYD

  have hDset : D ∈ E3.aSet 2 G := by
    refine ⟨hD, hDne, hElem, ?_⟩
    intro B hBD hm
    have hm01 : E3.mQuot D B = 0 ∨ E3.mQuot D B = 1 := by omega
    rcases hm01 with hm0 | hm1
    · have hBD_eq : B = D := (E3.mQuot_eq_zero_iff hDpg hBD).mp hm0
      rw [hBD_eq]
    · have hBcard : Nat.card B = 2 ^ (n - 2) := by
        have h := E3.card_eq_two_pow_mul hDpg hBD
        rw [hDcard, hm1, pow_one] at h
        have hpow : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
          rw [show n - 1 = (n - 2) + 1 by omega, pow_succ, mul_comm]
        omega
      have hBgt : 1 < Nat.card B := by
        rw [hBcard]
        exact Nat.one_lt_pow (by omega) (by norm_num : 1 < 2)
      letI : Fintype ↥B := Fintype.ofFinite _
      obtain ⟨bB, hbBne⟩ : ∃ bB : ↥B, bB ≠ 1 := by
        refine Fintype.exists_ne_of_one_lt_card ?_ (1 : ↥B)
        rw [← Nat.card_eq_fintype_card]
        exact hBgt
      let b : MulAut W := bB
      have hbB : b ∈ B := bB.2
      have hb_ne : b ≠ 1 := by
        intro h
        exact hbBne (Subtype.ext h)
      have hbD : b ∈ D := hBD hbB
      have hfixb : fixV (Subgroup.zpowers b) = Y := hfix_of_mem b hbD hb_ne
      have hYleB : Y ≤ fixV B :=
        fun w hw y hy => hYD hw y (hBD hy)
      have hBleY : fixV B ≤ Y := by
        have hle : fixV B ≤ fixV (Subgroup.zpowers b) :=
          fun w hw y hy => hw y (Subgroup.zpowers_le.mpr hbB hy)
        rwa [hfixb] at hle
      rw [hfixD]
      exact le_antisymm hBleY hYleB

  exact ⟨hDset, E3.e3_40 hw2 hDset⟩

end CFSG.LocalAnalysis.WeakClosure81

