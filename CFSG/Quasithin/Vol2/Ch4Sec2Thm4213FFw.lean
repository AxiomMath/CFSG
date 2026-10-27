module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213FFn
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213FFc
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Irr

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem two_eq_zero_of_card {F : Type} [Field F] [Fintype F] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n) : (2 : F) = 0 := by
  have h := FiniteField.cast_card_eq_zero F
  rw [hF, Nat.cast_pow, Nat.cast_ofNat] at h
  exact pow_eq_zero_iff'.mp h |>.1

namespace Conf4212

variable {T M L I H K : Subgroup G} (c : Conf4212 G T M L I H K)
include c

theorem isMulCommutative_V : IsMulCommutative ↥⁅reducedAggregate (L ⊔ T), L⁆ :=
  ⟨⟨fun a b => Subtype.ext (c.V_comm _ a.2 _ b.2)⟩⟩

theorem LHR_le : perfectCore (L ⊓ H) ⊔ pCoreOf 2 I ≤ L ⊔ T :=
  _root_.sup_le (((perfectCore_le _).trans inf_le_left).trans le_sup_left)
    (c.R_le.trans (pCoreOf_le 2 _))

theorem autOn_LHR_le :
    autOn (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) ⁅reducedAggregate (L ⊔ T), L⁆ ≤
      autOn (L ⊔ T) ⁅reducedAggregate (L ⊔ T), L⁆ :=
  T4213N.autOn_le_of_acts c.sup_le_normalizer_V fun a ha => ⟨a, c.LHR_le ha, fun _ _ => rfl⟩

open scoped IsMulCommutative in
theorem ff_of_autOn_LHR
    (h : ∀ _ : IsMulCommutative ↥⁅reducedAggregate (L ⊔ T), L⁆,
      IsFFModule (V := ↥⁅reducedAggregate (L ⊔ T), L⁆)
        (autOn (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) ⁅reducedAggregate (L ⊔ T), L⁆)) :
    ∃ _ : IsMulCommutative ↥⁅reducedAggregate (L ⊔ T), L⁆,
      IsFFModule (V := ↥⁅reducedAggregate (L ⊔ T), L⁆)
        (autOn (L ⊔ T) ⁅reducedAggregate (L ⊔ T), L⁆) := by
  have := c.isMulCommutative_V
  exact ⟨this, B1Red.isFFModule_mono c.autOn_LHR_le (h this)⟩

open scoped IsMulCommutative in
theorem ff_of_case1_natural
    (hCV : ⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    {F : Type} [Field F] [Fintype F] {n : ℕ} (hF : Fintype.card F = 2 ^ n)
    (hnat : IsNaturalSection (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) ⁅reducedAggregate (L ⊔ T), L⁆
      (⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer (perfectCore (L ⊓ H) : Set G))
      ((pCoreOf 2 I).subgroupOf (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I)) (StatedSL 2 F)) :
    ∃ _ : IsMulCommutative ↥⁅reducedAggregate (L ⊔ T), L⁆,
      IsFFModule (V := ↥⁅reducedAggregate (L ⊔ T), L⁆)
        (autOn (L ⊔ T) ⁅reducedAggregate (L ⊔ T), L⁆) := by
  rw [← c.inf_centralizer_eq, hCV] at hnat
  have hsum := (isNaturalSection_iff_isSumOfNaturalModules_one _ _ bot_le).mp hnat
  exact c.ff_of_autOn_LHR fun _ =>
    FFn.isFFModule_autOn_of_sum (n := 1) (two_eq_zero_of_card hF) le_rfl le_rfl hsum

open scoped IsMulCommutative in
theorem ff_of_case2_sum {m k : ℕ} (hm : m = 3 ∨ m = 4) (hk1 : 1 ≤ k) (hkm : k < m)
    (hsum : IsSumOfNaturalModules (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) ⁅reducedAggregate (L ⊔ T), L⁆
      ⊥ ((pCoreOf 2 I).subgroupOf (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I))
      (StatedSL m (ZMod 2)) false k) :
    ∃ _ : IsMulCommutative ↥⁅reducedAggregate (L ⊔ T), L⁆,
      IsFFModule (V := ↥⁅reducedAggregate (L ⊔ T), L⁆)
        (autOn (L ⊔ T) ⁅reducedAggregate (L ⊔ T), L⁆) := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  rcases hm with rfl | rfl
  · exact c.ff_of_autOn_LHR fun _ =>
      FFn.isFFModule_autOn_of_sum (n := 2) h2 hk1 (by omega) hsum
  · exact c.ff_of_autOn_LHR fun _ =>
      FFn.isFFModule_autOn_of_sum (n := 3) h2 hk1 (by omega) hsum

end Conf4212

end CFSG.Quasithin.H13.Ch4
