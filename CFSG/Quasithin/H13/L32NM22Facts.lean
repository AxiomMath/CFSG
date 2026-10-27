module

public import CFSG.Quasithin.H13.L32NM22Quad
public import CFSG.Quasithin.H13.L32NM22Rank
public import CFSG.Quasithin.Background.HM22LinkComm

public section

namespace CFSG.Quasithin.H13.M22Facts

open CFSG.Quasithin.H.Mathieu L1442M Matrix

theorem m22_card_le
    {E : Subgroup (GL (Fin 12) (ZMod 2))} (hE : E ≤ m22)
    (hsq : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 2 ^ 5 :=
  M22Rank.m22_card_le_of M22Link.m22Zero_le_m22 M22Link.card_m22Zero M22Link.isHat_m22Zero hE hsq

theorem m22_quad_unique {Q' : (Fin 12 → ZMod 2) → ZMod 2}
    {B' : LinearMap.BilinForm (ZMod 2) (Fin 12 → ZMod 2)}
    (hQ' : ∀ x y, Q' (x + y) = Q' x + Q' y + B' x y) (hB' : B' ≠ 0)
    (hinv : ∀ γ ∈ m22, ∀ x, Q' ((γ : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ x) = Q' x) :
    ∀ x, Q' x = quadOf q12 x :=
  M22Quad.m22_quad_unique_of (fun _ ha hb => M22Link.commutant_m22 ha hb) M22Link.irreducible_m22
    hQ' hB' hinv

end CFSG.Quasithin.H13.M22Facts
