module

public import CFSG.Quasithin.Background.B5NonA
public import CFSG.Quasithin.EmptyFaithful.S153ZA
public import CFSG.Quasithin.EmptyFaithful.S153ZO

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise

namespace Z391

theorem v2g_ffBridge {W : Type} [CommGroup W] [Finite W] {M : Subgroup (MulAut W)}
    {L : Subgroup (MulAut W)} {Q : Type} [CommGroup Q] [MulDistribMulAction ↥M Q] (π : W →* Q)
    (hπM : ∀ (g : ↥M) (w : W), g • π w = π ((g : MulAut W) w)) (hker : π.ker = fixV L)
    (hexp : ∀ w : W, w ^ 2 = 1) [Finite Q]
    {VT : Subgroup W} {A : Subgroup (MulAut W)} (hAM : A ≤ M) (hAe : IsElemAbelian2 A)
    (hAne : A ≠ ⊥) (hAV : A ≤ stabSub VT) (hAC : A ≤ stabSub (VT ⊓ fixV L))
    (hf : A ⊓ centSec VT (VT ⊓ fixV L) = ⊥)
    (hnB : nB (A.subgroupOf M) (VT.map π) ≤ rk ↥A) :
    Nat.card (Sec VT (VT ⊓ fixV L)) ≤
      Nat.card ↥(autSec A VT (VT ⊓ fixV L)) * Nat.card ↥(fixV (autSec A VT (VT ⊓ fixV L))) := by
  have hA₀A : (A.subgroupOf M).map M.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAM
  have h1 := rkIdx_fixV_autSec_le_nB π hπM (A.subgroupOf M) VT
  rw [hA₀A, hker] at h1
  have hIsA2 : IsA2 A A := ⟨le_rfl, hAne, hAe⟩
  have hA2 := isA2_autSec hIsA2 hAV hAC hf
  have hrk : rk ↥(autSec A VT (VT ⊓ fixV L)) = rk ↥A := B5.rk_autSec_eq hAV hAC hf
  have hexpS : ∀ s : Sec VT (VT ⊓ fixV L), s ^ 2 = 1 :=
    CFSG.QuasithinUnique.Bridge.sec_sq_eq_one hexp _ _
  rw [← rAV_le_one_iff hexpS hA2]
  unfold rAV
  rw [hrk]
  have hpos : (0 : ℚ) < (rk ↥A : ℚ) := by exact_mod_cast hIsA2.rk_pos
  rw [div_le_one hpos]
  exact_mod_cast h1.trans hnB

end Z391

end CFSG.Quasithin
