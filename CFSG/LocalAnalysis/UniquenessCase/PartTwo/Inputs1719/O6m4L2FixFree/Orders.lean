module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4L2FixFree.Defs

import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesOrders
import CFSG.Timmesfeld.Orders.Classical
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.OrderOfX
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rk
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4FF

open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem card_ker_mk'_comp_le_F02 {A B : Type} [Group A] [Group B] (N : Subgroup B)
    [N.Normal] [Finite ↥N] (g : A →* B) (hg : Function.Injective g) :
    Nat.card ↥((QuotientGroup.mk' N).comp g).ker ≤ Nat.card ↥N := by
  refine Nat.card_le_card_of_injective
    (fun x : ↥((QuotientGroup.mk' N).comp g).ker => (⟨g (x : A), ?_⟩ : ↥N)) ?_
  · have hx := x.2
    rw [MonoidHom.mem_ker] at hx
    exact (QuotientGroup.eq_one_iff _).mp hx
  · intro x y hxy
    exact Subtype.ext (hg (congrArg Subtype.val hxy))

private theorem card_le_four_of_isPGroup_two_dvd_sixty_F02 {H : Type} [Group H] [Finite H]
    {P : Subgroup H} (hP : IsPGroup 2 P) (h60 : Nat.card H = 60) : Nat.card ↥P ≤ 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hk_le : k ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ k := by omega
    have h8 : 2 ^ 3 ∣ 60 := dvd_trans (pow_dvd_pow 2 h3)
      (hk ▸ (by rw [← h60]; exact Subgroup.card_subgroup_dvd_card P))
    exact absurd h8 (by norm_num)
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk_le
    _ = 4 := by norm_num

private theorem le_card_ker_of_card_mul_le_F02 {A B : Type} [Group A] [Group B] (f : A →* B)
    (hf : Nat.card ↥f.ker * Nat.card ↥f.range = 2 ^ 12) (hr : Nat.card ↥f.range ≤ 4) :
    1024 ≤ Nat.card ↥f.ker := by
  have h : Nat.card ↥f.ker * Nat.card ↥f.range ≤ Nat.card ↥f.ker * 4 :=
    Nat.mul_le_mul_left _ hr
  rw [hf] at h
  have h' : 1024 * 4 ≤ Nat.card ↥f.ker * 4 := by
    calc 1024 * 4 = 4096 := by norm_num
      _ = 2 ^ 12 := by norm_num
      _ ≤ Nat.card ↥f.ker * 4 := h
  exact Nat.le_of_mul_le_mul_right h' (by norm_num)

theorem natCard_omega6_of_card_four {F : Type} [Field F] [Finite F] {b c : F}
    (hF : Nat.card F = 4) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Nat.card ↥(Omega6 F b c) = 2 ^ 12 * 248625 := by
  haveI : CharP F 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (K := F) (f := 2) (by rw [hF]; norm_num)
  rw [CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadMinus_three (K := F) hirr,
    CFSG.SeitzReduction.F4Pilot.ordSU_four, hF]
  norm_num

theorem card_eq_two_pow_twelve_of_isSylowIn {G : Type} [Group G] {S X : Subgroup G}
    (hS : IsSylowIn 2 S X) (hX : Nat.card ↥X = 2 ^ 12 * 248625) : Nat.card ↥S = 2 ^ 12 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXne : Nat.card ↥X ≠ 0 := by rw [hX]; norm_num
  haveI : Finite ↥X := Nat.finite_of_card_ne_zero hXne
  have h1 := Sylow.card_eq_multiplicity hS.toSylow
  rw [IsSylowIn.coe_toSylow] at h1
  have hfac : (2 ^ 12 * 248625).factorization 2 = 12 := by
    rw [Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (n := 248625) (p := 2) (by norm_num), add_zero]
  rw [hX, hfac] at h1
  rw [← h1]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.le).toEquiv).symm

theorem exists_sylow_of_isSylowIn {G G' : Type} [Group G] [Group G'] {S X : Subgroup G}
    (hS : IsSylowIn 2 S X) (e : ↥X ≃* G') :
    ∃ T : Sylow 2 G', (T : Subgroup G') = (S.subgroupOf X).map e.toMonoidHom := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P₀ : Subgroup ↥X := S.subgroupOf X
  have hP0 : IsPGroup 2 ↥P₀ :=
    hS.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hS.le).symm
  have hmap : IsPGroup 2 ↥(P₀.map e.toMonoidHom) := hP0.map e.toMonoidHom
  have hidx : (P₀.map e.toMonoidHom).index = P₀.index :=
    Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective P₀
  have hndvd : ¬ 2 ∣ (P₀.map e.toMonoidHom).index := by
    rw [hidx]
    exact hS.not_dvd_relIndex
  exact ⟨hmap.toSylow hndvd, rfl⟩

theorem lt_card_pCore {G : Type} [Group G] {J S : Subgroup G} [Finite ↥J] (hSJ : S ≤ J)
    (hS : IsPGroup 2 ↥S) (hSc : Nat.card ↥S = 2 ^ 12) (h60 : Nat.card (Bar2 J) = 60) :
    2 ^ 8 < Nat.card ↥(CFSG.pCore 2 ↥J) := by
  let N : Subgroup ↥J := CFSG.pCore 2 ↥J
  haveI : N.Normal := CFSG.pCore_normal
  let S₀ : Subgroup ↥J := S.subgroupOf J
  have hS0card : Nat.card ↥S₀ = 2 ^ 12 := by
    rw [← hSc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSJ).toEquiv
  have hS0p : IsPGroup 2 ↥S₀ := hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSJ).symm
  let f : ↥S₀ →* Bar2 J := (QuotientGroup.mk' N).comp S₀.subtype
  have hfker : Nat.card ↥f.ker * Nat.card ↥f.range = 2 ^ 12 := by
    rw [← hS0card]
    exact Subgroup.card_ker_mul_card_range f
  haveI : Finite (Bar2 J) :=
    Finite.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hrange_le : Nat.card ↥f.range ≤ 4 :=
    card_le_four_of_isPGroup_two_dvd_sixty_F02
      (hS0p.of_surjective f.rangeRestrict f.rangeRestrict_surjective) h60
  have hker_le : Nat.card ↥f.ker ≤ Nat.card ↥N :=
    card_ker_mk'_comp_le_F02 N S₀.subtype (fun _ _ h => Subtype.ext h)
  have hker_ge : 1024 ≤ Nat.card ↥f.ker := le_card_ker_of_card_mul_le_F02 f hfker hrange_le
  have hN : 2 ^ 8 < Nat.card ↥N := by
    have h1024 : 1024 ≤ Nat.card ↥N := le_trans hker_ge hker_le
    rw [show (2 : ℕ) ^ 8 = 256 by norm_num]
    omega
  exact hN

theorem card_bar2_of_isL2 {G : Type} [Group G] {J : Subgroup G} (h : IsL2 (Bar2 J) 2) :
    Nat.card (Bar2 J) = 60 := by
  obtain ⟨-, hcard⟩ := KOrdNat.isL2_two_le_and_card h
  rw [hcard]
  norm_num

theorem not_isSolvable_of_isL2 {G : Type} [Group G] {J : Subgroup G} (h : IsL2 (Bar2 J) 2) :
    ¬ Group.IsSolvable ↥J := by
  intro hsol
  have hsimple : IsSimpleGroup (Bar2 J) :=
    uc22p22r_lieModel_isSimple_classical (Or.inl rfl) h
  haveI : IsSimpleGroup (Bar2 J) := hsimple
  have hcomm : ∀ a b : Bar2 J, a * b = b * a :=
    IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance
  haveI : IsMulCommutative (Bar2 J) := IsMulCommutative.of_comm hcomm
  have hprime : Nat.Prime (Nat.card (Bar2 J)) :=
    Group.is_simple_iff_prime_card.mp hsimple
  rw [card_bar2_of_isL2 h] at hprime
  exact (by norm_num : ¬ Nat.Prime 60) hprime

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4FF
