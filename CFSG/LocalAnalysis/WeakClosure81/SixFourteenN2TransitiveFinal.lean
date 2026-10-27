module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN2Transitive
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN2Thirty

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open

theorem isNatGL4_of_transitive {W : Type} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16)
    {G X H : Subgroup (MulAut W)} {s : MulAut W}
    (hH : H = G ⊓ Subgroup.centralizer (X : Set (MulAut W)))
    (hxgen : X = Subgroup.zpowers x)
    (hXcard : Nat.card X = 3) (hXG : X ≤ G)
    (hXnorm : ∀ g ∈ G, ∀ y ∈ X, g * y * g⁻¹ ∈ X)
    (hsG : s ∈ G) (hs_ord2 : orderOf s = 2)
    (hs_not_cent : s ∉ Subgroup.centralizer (X : Set (MulAut W)))
    (hcommH : ∀ h ∈ H, h * x = x * h)
    (htrans : letI := galoisModule hw2 x hx3 hfix;
      ∀ L M : LineOf (K := GaloisField 2 2) (V := Additive W),
        ∃ h : ↥H, lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L = M)
    (hd : ∃ d ∈ H, orderOf d = 2) :
    IsNatGL4 W H 2 := by
  rcases isNatGL4_or_card_thirty_of_transitive hw2 x hx3 hfix hW hH hxgen hXcard hXG
      hcommH htrans hd with hGL | hcard
  · exact hGL
  · exact (false_of_card_thirty_of_transitive hw2 x hx3 hfix hW hH hxgen hXcard hXG
      hXnorm hsG hs_ord2 hs_not_cent hcommH htrans hcard).elim

theorem concl139_two_of_transitive {W : Type} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16)
    {G X H : Subgroup (MulAut W)} {s : MulAut W}
    (hH : H = G ⊓ Subgroup.centralizer (X : Set (MulAut W)))
    (hxgen : X = Subgroup.zpowers x)
    (hXcard : Nat.card X = 3) (hXG : X ≤ G)
    (hXnorm : ∀ g ∈ G, ∀ y ∈ X, g * y * g⁻¹ ∈ X)
    (hsG : s ∈ G) (hs_ord2 : orderOf s = 2)
    (hs_not_cent : s ∉ Subgroup.centralizer (X : Set (MulAut W)))
    (hcommH : ∀ h ∈ H, h * x = x * h)
    (htrans : letI := galoisModule hw2 x hx3 hfix;
      ∀ L M : LineOf (K := GaloisField 2 2) (V := Additive W),
        ∃ h : ↥H, lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L = M)
    (hd : ∃ d ∈ H, orderOf d = 2) :
    Concl139Printed W G X 2 := by
  left
  exact hH ▸ isNatGL4_of_transitive hw2 x hx3 hfix hW hH hxgen hXcard hXG hXnorm hsG
    hs_ord2 hs_not_cent hcommH htrans hd

end CFSG.LocalAnalysis.WeakClosure81