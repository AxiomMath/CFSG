module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN2TransitiveFinal
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN2PairFinal

public noncomputable section
public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open

theorem concl139_two_of_hyp139_n2 {W : Type} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1)
    {G X D : Subgroup (MulAut W)} {s : MulAut W} {Y : Subgroup W}
    (hK : CFSG.Open.IsKGroup ↥G) (hpCore : pCoreOf 2 G = ⊥)
    (hirr : ∀ Z : Subgroup W, (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) → Z = ⊥ ∨ Z = ⊤)
    (ht2 : ∃ t ∈ G, orderOf t = 2 ∧ rkIdx (fixV (Subgroup.zpowers t)) ≤ 3)
    (hXG : X ≤ G) (hXnorm : ∀ g ∈ G, ∀ y ∈ X, g * y * g⁻¹ ∈ X)
    (hXcard : Nat.card X = 3)
    (hsG : s ∈ G) (hs_ord2 : orderOf s = 2)
    (hs_not_cent : s ∉ Subgroup.centralizer (X : Set (MulAut W)))
    (hYinv : ∀ a ∈ X, ∀ y ∈ Y, a y ∈ Y) (hYrk : rkIdx Y = 2)
    (hW : Nat.card W = 4 ^ 2)
    (hD : D ≤ G) (hDCX : ∀ d ∈ D, ∀ x ∈ X, d * x = x * d)
    (hDs : ∀ d ∈ D, d * s = s * d)
    (hElem : CFSG.Quasithin.IsElemAbelian2 D) (hDcard : Nat.card D = 2 ^ (2 - 1))
    (hYD : Y ≤ fixV D) :
    Concl139Printed W G X 2 := by
  have hW16 : Nat.card W = 16 := by
    rw [hW]
    norm_num
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
  let H : Subgroup (MulAut W) := G ⊓ Subgroup.centralizer (X : Set (MulAut W))
  have hH : H = G ⊓ Subgroup.centralizer (X : Set (MulAut W)) := rfl
  have hcommH : ∀ h ∈ H, h * x = x * h := by
    intro h hh
    have hcent : h ∈ Subgroup.centralizer (X : Set (MulAut W)) :=
      (Subgroup.mem_inf.mp (hH ▸ hh)).2
    exact ((Subgroup.mem_centralizer_iff.mp hcent) x hxX).symm
  have hDcard2 : Nat.card D = 2 := by
    simpa using hDcard
  letI : Fintype ↥D := Fintype.ofFinite _
  obtain ⟨dD, hdDne⟩ : ∃ dD : ↥D, dD ≠ 1 := by
    refine Fintype.exists_ne_of_one_lt_card ?_ (1 : ↥D)
    rw [← Nat.card_eq_fintype_card, hDcard2]
    norm_num
  let d : MulAut W := dD
  have hdD : d ∈ D := dD.2
  have hd_ne : d ≠ 1 := by
    intro h
    exact hdDne (Subtype.ext h)
  have hd_sq : d * d = 1 := by
    simpa [pow_two] using hElem.2 d hdD
  have hd_ord2 : orderOf d = 2 := orderOf_eq_prime (by rwa [pow_two]) hd_ne
  have hdH : d ∈ H := by
    rw [hH]
    refine Subgroup.mem_inf.mpr ⟨hD hdD, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hDCX d hdD y hy).symm
  have hYcard : Nat.card Y = 4 := card_of_rkIdx_two hYrk hW16
  letI := galoisModule hw2 x hx3 hfix
  have hdich := H_transitive_or_pair_Hyp139_n2 hw2 x hx3 hx_ord3 hfix hW16 hH hXG hXnorm
    hxgen hsG hs_ord2 hs_not_cent hirr hD hDCX hElem hDcard2 hYD hYinv hYcard hcommH
  rcases hdich with htrans | ⟨S, hS2, hSne, hSproper, hSinv⟩
  · exact concl139_two_of_transitive hw2 x hx3 hfix hW16 hH hxgen hXcard hXG hXnorm hsG
      hs_ord2 hs_not_cent hcommH htrans ⟨d, hdH, hd_ord2⟩
  · have hpair : ∃ S : Set (LineOf (K := GaloisField 2 2) (V := Additive W)),
        S.ncard = 2 ∧ S.Nonempty ∧ S ≠ Set.univ ∧
          (∀ h : ↥H,
            S.image (fun L => lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L) = S) :=
      ⟨S, hS2, hSne, hSproper, hSinv⟩
    have hT := sixfourteen_n2_isTensorS3L2 hw2 x hx3 hx_ord3 hfix hW16 hH hXG hXnorm hxgen
      hsG hs_ord2 hs_not_cent hirr hD hDCX hDs hElem hDcard2 hYD hYinv hYcard hcommH hpair
    exact Or.inr (Or.inl hT)

end CFSG.LocalAnalysis.WeakClosure81
