module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallRows
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mPar
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mModule
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallU4Nat
import CFSG.Quasithin.Background.E3MParamAttained
import CFSG.Adapters.LieModelOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.Timmesfeld CFSG.Timmesfeld.Orders

theorem even_card_of_isOmega8m {G : Type} [Group G] [Finite G] {e : ℕ} (h : IsOmega8m G e) :
    Even (Nat.card G) := by
  have he : 1 ≤ e := h.admissible.2.1
  have hcard : Nat.card G = ordTwistedD 4 (2 ^ e) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h.card_eq_lieOrd (by norm_num)
  obtain ⟨r, hr, heq⟩ := (profile_ordTwistedD (n := 4) (by norm_num) he).two
  rw [hcard, heq]
  exact Even.mul_right (even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))) r

theorem k14_5SmallFor_o8m : K14_5SmallFor fun L _ e => IsOmega8m L e := by
  intro I _ _ hI X L P e n hLX hLn hq hirr hS hPL hpar hinf hN hn hm
  classical
  have : Finite (MulAut I) :=
    Finite.of_injective (fun f : MulAut I => (f : I → I)) DFunLike.coe_injective
  have : Fact (∀ x : I, x * x = 1) := ⟨fun x => by rw [← pow_two]; exact hI x⟩
  have hne := nParam_eq_of_isOmega8m_parabolic hS hPL hpar hinf hN hn
  have he : 2 ≤ e := by omega
  have hevL : Even (Nat.card ↥L) := even_card_of_isOmega8m hS
  have hevX : Even (Nat.card ↥X) :=
    even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hevL).trans (Subgroup.card_dvd_of_le hLX))
  obtain ⟨t, htX, ht2, htm⟩ := E3.exists_involution_rkIdx_fixV_eq_mParam X hevX
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hXN : X ≤ normalizer (L : Set (MulAut I)) :=
    (normal_subgroupOf_iff_le_normalizer hLX).mp hLn
  have hdt : CFSG.HardMathSupport.U4FF.disp t ≤ 2 * e + 1 := by
    rw [← rkIdx_fixV_zpowers_eq_disp, htm]
    omega
  have hnat : NatOmegaMinus L ⊤ ⊥ 8 e :=
    natOmegaMinus_eight_of_small_involution he hS hirr (hXN htX) htt ht1 hdt
  exact Or.inl ⟨e,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨hS, hnat⟩))))))))), hne⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
