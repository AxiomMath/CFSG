module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP
public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents
import all CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65Inversion
import CFSG.RankThree.Asc83Table.Ru
import CFSG.RankThree.Asc83Table.He
import CFSG.RankThree.Asc83Table.J4
import CFSG.RankThree.Asc83Table.M24
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item414Local
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65X0CardG2General
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ExtraspecialTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.KGroups.U33Inputs
public import CFSG.RankThree.Asc83Table.Reduction
public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
import CFSG.Quasithin.EmptyFaithful.S1422Basic
import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open scoped commutatorElement
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor)
open CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups (IsExtraspecialExpP)
open CFSG.RankThree.PartTwo.Sec4 (IsHeisThree)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2)

@[expose] def SylowIsExtraspecialOfTypes : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], (LieModel Y .PSL 3 3 1 ∨ LieModel Y .Tits 0 2 1) →
    ∀ S : Sylow 3 Y, IsExtraspecialExpP 3 1 ↥(S : Subgroup Y)

theorem isExtraspecialExpP_of_isHeisThree {P : Type} [Group P] (h : IsHeisThree P) :
    IsExtraspecialExpP 3 1 P := by
  obtain ⟨⟨-, hc, -, hz⟩, hcard, hexp⟩ := h
  unfold IsExtraspecialExpP
  exact ⟨by rw [hcard]; norm_num, hexp, hc, hz⟩

theorem isExtraspecialExpP_of_isSylowOf_bar {G : Type} [Group G] [Finite G] {L Q : Subgroup G}
    (hQ : IsSylowOf 3 Q L)
    (h : ∀ S : Sylow 3 (Bar2 L), IsExtraspecialExpP 3 1 ↥(S : Subgroup (Bar2 L))) :
    IsExtraspecialExpP 3 1 ↥Q := by
  classical
  have hQL : Q ≤ L := hQ.le
  have hQO2 : Q ⊓ CFSG.Open.pCoreOf 2 L = ⊥ :=
    (IsPGroup.disjoint_of_ne 3 2 (by norm_num) Q (CFSG.Open.pCoreOf 2 L) hQ.isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)).eq_bot
  obtain ⟨Pb, hPb⟩ := exists_sylow_map_subgroupOf_mk' hQ.exists_sylow_eq_subgroupOf
  have hf : Function.Injective ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp
      (Subgroup.inclusion hQL)) := injective_comp_subgroupOf_mk' hQL hQO2
  have hr := range_comp_subgroupOf_mk' hQL
  have e : ↥Q ≃* ↥(Pb : Subgroup (Bar2 L)) :=
    (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr (hr.trans hPb.symm))
  exact isExtraspecialExpP_of_mulEquiv e (h Pb)

private theorem exponent_eq_three {P : Type} [Group P] (hexp : ∀ g : P, g ^ 3 = 1)
    (hnt : Nat.card P ≠ 1) : Monoid.exponent P = 3 := by
  have hdvd : Monoid.exponent P ∣ 3 := Monoid.exponent_dvd_of_forall_pow_eq_one hexp
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
  · exfalso
    apply hnt
    have h1 : ∀ g : P, g = 1 := fun g => by
      have := Monoid.pow_exponent_eq_one g
      rwa [h, pow_one] at this
    have : Subsingleton P := ⟨fun a b => (h1 a).trans (h1 b).symm⟩
    exact Nat.card_of_subsingleton (1 : P)
  · exact h

private theorem isHeisThree_sylow_of_mulEquiv {X N : Type} [Group X] [Group N] [Finite X]
    [Finite N] (e : X ≃* N) (Q₀ : Sylow 3 N) (h : IsHeisThree ↥(Q₀ : Subgroup N))
    (Q : Sylow 3 X) : IsHeisThree ↥(Q : Subgroup X) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Q' : Sylow 3 N := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective Q
  have hQ' : (Q' : Subgroup N) = (Q : Subgroup X).map e.toMonoidHom := by simp [Q']
  have h1 : (Q : Subgroup X) ≃* (Q' : Subgroup N) := by
    rw [hQ']
    exact e.subgroupMap (Q : Subgroup X)
  have h2 : (Q' : Subgroup N) ≃* (Q₀ : Subgroup N) := Sylow.equiv Q' Q₀
  exact CFSG.RankThree.PartTwo.Sec13.isHeisThree_of_mulEquiv (h1.trans h2).symm h

private theorem isHeisThree_sylow_of_ex27 {N : Type} [Group N] [Finite N] {x y : N}
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (hz1 : ⁅x, y⁆ ≠ 1) (hN : (Nat.card N).factorization 3 = 3) {L : Type} [Group L] [Finite L]
    (e : L ≃* N) (P : Sylow 3 L) : IsHeisThree ↥(P : Subgroup L) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P₀ : Subgroup N := Subgroup.closure ({x, y} : Set N) with hP₀
  have hcard : Nat.card P₀ = 27 := CFSG.RankThree.Asc83Table.ex27_card hx hy hzx hzy hz1
  have hP₀p : IsPGroup 3 P₀ := IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num)
  have hexp : ∀ g : P₀, g ^ 3 = 1 := fun g =>
    Subtype.ext (CFSG.RankThree.Asc83Table.pow_three_eq_one_of_mem hx hzx hzy hy g.2)
  have hnc : ¬ IsMulCommutative P₀ := by
    intro hc
    apply hz1
    rw [commutatorElement_eq_one_iff_mul_comm]
    have := mul_comm' (⟨x, Subgroup.subset_closure (by simp)⟩ : P₀)
      ⟨y, Subgroup.subset_closure (by simp)⟩
    exact congrArg Subtype.val this
  have hext := CFSG.RankThree.PartTwo.isExtraspecialPGroup_of_card_eq_pow_three hP₀p hexp
    (by rw [hcard]; norm_num) hnc
  have hH : IsHeisThree ↥P₀ :=
    ⟨hext, hcard, exponent_eq_three hexp (by rw [hcard]; norm_num)⟩
  have hsyl : Nat.card P₀ = 3 ^ (Nat.card N).factorization 3 := by
    rw [hN, hcard]
    norm_num
  exact isHeisThree_sylow_of_mulEquiv e (Sylow.ofCard P₀ hsyl) hH P

private theorem isHeisThree_sylow_j2
    {Y : Type} [Group Y] [Finite Y] (hY : IsSpor Y .J2)
    (S : Sylow 3 Y) : IsHeisThree ↥(S : Subgroup Y) := by
  obtain ⟨e⟩ := hY
  exact (CFSG.RankThree.PartTwo.Sec4.Sporadic.rank3II_4_15 Y ⟨e⟩ S _ rfl _ rfl).1.1

theorem sylow_isExtraspecialExpP_of_j2
    {Y : Type} [Group Y] [Finite Y] (hY : IsSpor Y .J2)
    (S : Sylow 3 Y) : IsExtraspecialExpP 3 1 ↥(S : Subgroup Y) :=
  isExtraspecialExpP_of_isHeisThree (isHeisThree_sylow_j2 hY S)

private theorem isHeisThree_sylow_m12
    {Y : Type} [Group Y] [Finite Y] (hY : IsSpor Y .M12) (S : Sylow 3 Y) :
    IsHeisThree ↥(S : Subgroup Y) := by
  obtain ⟨e⟩ := hY
  exact (CFSG.RankThree.PartTwo.Sec4.Sporadic.rank3II_4_14_local Y ⟨e⟩ S).1

section Sporadic

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

private theorem isHeisThree_sylow_ru
    {Y : Type} [Group Y] [Finite Y] (hY : IsSpor Y .Ru) (S : Sylow 3 Y) :
    IsHeisThree ↥(S : Subgroup Y) := by
  obtain ⟨e⟩ := hY
  exact isHeisThree_sylow_of_ex27
    (CFSG.RankThree.Asc83Table.Ru.facts.x_cube (spec2fr 28)
      CFSG.RankThree.Asc83Table.Ru.ru_check)
    (CFSG.RankThree.Asc83Table.Ru.facts.y_cube (spec2fr 28)
      CFSG.RankThree.Asc83Table.Ru.ru_check)
    (CFSG.RankThree.Asc83Table.Ru.facts.z_x (spec2fr 28)
      CFSG.RankThree.Asc83Table.Ru.ru_check)
    (CFSG.RankThree.Asc83Table.Ru.facts.z_y (spec2fr 28)
      CFSG.RankThree.Asc83Table.Ru.ru_check)
    (CFSG.RankThree.Asc83Table.Ru.facts.z_ne (spec2fr 28)
      CFSG.RankThree.Asc83Table.Ru.ru_check)
    CFSG.RankThree.Asc83Table.Ru.factorization_card
    (e : Y ≃* CFSG.Blueprint.NativeSporadic.Ru) S

private theorem isHeisThree_sylow_he
    {Y : Type} [Group Y] [Finite Y] (hY : IsSpor Y .He) (S : Sylow 3 Y) :
    IsHeisThree ↥(S : Subgroup Y) := by
  obtain ⟨e⟩ := hY
  exact isHeisThree_sylow_of_ex27
    (CFSG.RankThree.Asc83Table.He.facts.x_cube (specP 7 50)
      CFSG.RankThree.Asc83Table.He.he_check)
    (CFSG.RankThree.Asc83Table.He.facts.y_cube (specP 7 50)
      CFSG.RankThree.Asc83Table.He.he_check)
    (CFSG.RankThree.Asc83Table.He.facts.z_x (specP 7 50)
      CFSG.RankThree.Asc83Table.He.he_check)
    (CFSG.RankThree.Asc83Table.He.facts.z_y (specP 7 50)
      CFSG.RankThree.Asc83Table.He.he_check)
    (CFSG.RankThree.Asc83Table.He.facts.z_ne (specP 7 50)
      CFSG.RankThree.Asc83Table.He.he_check)
    CFSG.RankThree.Asc83Table.He.factorization_card
    (e : Y ≃* CFSG.Blueprint.NativeSporadic.He) S

private theorem isHeisThree_sylow_j4
    {Y : Type} [Group Y] [Finite Y] (hY : IsSpor Y .J4) (S : Sylow 3 Y) :
    IsHeisThree ↥(S : Subgroup Y) := by
  obtain ⟨e⟩ := hY
  exact isHeisThree_sylow_of_ex27
    (CFSG.RankThree.Asc83Table.J4.facts.x_cube (spec2fr 112)
      CFSG.RankThree.Asc83Table.J4.j4_check)
    (CFSG.RankThree.Asc83Table.J4.facts.y_cube (spec2fr 112)
      CFSG.RankThree.Asc83Table.J4.j4_check)
    (CFSG.RankThree.Asc83Table.J4.facts.z_x (spec2fr 112)
      CFSG.RankThree.Asc83Table.J4.j4_check)
    (CFSG.RankThree.Asc83Table.J4.facts.z_y (spec2fr 112)
      CFSG.RankThree.Asc83Table.J4.j4_check)
    (CFSG.RankThree.Asc83Table.J4.facts.z_ne (spec2fr 112)
      CFSG.RankThree.Asc83Table.J4.j4_check)
    CFSG.RankThree.Asc83Table.J4.factorization_card
    (e : Y ≃* CFSG.Blueprint.NativeSporadic.J4) S

private theorem isHeisThree_sylow_m24
    {Y : Type} [Group Y] [Finite Y] (hY : IsSpor Y .M24) (S : Sylow 3 Y) :
    IsHeisThree ↥(S : Subgroup Y) := by
  obtain ⟨e⟩ := hY
  exact isHeisThree_sylow_of_ex27
    CFSG.RankThree.Asc83Table.M24.X_cube CFSG.RankThree.Asc83Table.M24.Y_cube
    CFSG.RankThree.Asc83Table.M24.Z_X CFSG.RankThree.Asc83Table.M24.Z_Y
    CFSG.RankThree.Asc83Table.M24.Z_ne CFSG.RankThree.Asc83Table.M24.factorization_card
    (e : Y ≃* CFSG.Blueprint.NativeSporadic.M24) S

end Sporadic

private theorem isHeisThree_sylow_u33
    {Y : Type} [Group Y] [Finite Y]
    (hY : LieModel Y .PSU 3 3 1) (S : Sylow 3 Y) : IsHeisThree ↥(S : Subgroup Y) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel hY
  let P : Subgroup (Equiv.Perm (Fin 28)) := CFSG.GH74.KGroups.U33.QP.originalSubgroup
  have hPcard : Nat.card P = 6048 := by
    rw [show P = CFSG.GH74.KGroups.U33.QP.originalSubgroup from rfl]
    rw [CFSG.GH74.KGroups.card_group CFSG.GH74.KGroups.U33.QP CFSG.GH74.KGroups.U33.QP_ok]
    exact (CFSG.GH74.KGroups.U33.QP_valid).2
  have hPsub_le : CFSG.SignalizerFunctorTheorem.NonLocalExc.Psub ≤ P := by
    intro g hg
    exact (CFSG.SignalizerFunctorTheorem.NonLocalExc.mem_Psub.mp hg).1
  have hPsubcard : Nat.card ↥CFSG.SignalizerFunctorTheorem.NonLocalExc.Psub = 27 :=
    CFSG.SignalizerFunctorTheorem.NonLocalExc.card_Psub
  have hPsubexp : ∀ g : ↥CFSG.SignalizerFunctorTheorem.NonLocalExc.Psub, g ^ 3 = 1 := fun g =>
    Subtype.ext ((CFSG.SignalizerFunctorTheorem.NonLocalExc.mem_Psub.mp g.2).2.2)
  have hPsubHeis : IsHeisThree ↥CFSG.SignalizerFunctorTheorem.NonLocalExc.Psub :=
    ⟨CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.U33Inversion.u33_isExtraspecial,
      hPsubcard, exponent_eq_three hPsubexp (by rw [hPsubcard]; norm_num)⟩
  let Qsub : Subgroup ↥P := CFSG.SignalizerFunctorTheorem.NonLocalExc.Psub.subgroupOf P
  have hQsub_card : Nat.card Qsub = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPsub_le).toEquiv]
    exact hPsubcard
  have hQsub_p : IsPGroup 3 Qsub := IsPGroup.of_card (n := 3) (by rw [hQsub_card]; norm_num)
  have : Finite ↥Qsub := Nat.finite_of_card_ne_zero (by rw [hQsub_card]; norm_num)
  have hQsub_index : ¬ 3 ∣ Qsub.index := by
    rw [Subgroup.index_eq_card_div, hQsub_card, hPcard]
    norm_num
  let Q0 : Sylow 3 ↥P := hQsub_p.toSylow hQsub_index
  have hQ0 : IsHeisThree ↥(Q0 : Subgroup ↥P) :=
    CFSG.RankThree.PartTwo.Sec13.isHeisThree_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hPsub_le).symm hPsubHeis
  exact isHeisThree_sylow_of_mulEquiv e Q0 hQ0 S

theorem sylow_isExtraspecialExpP_of_u33
    {Y : Type} [Group Y] [Finite Y]
    (hY : LieModel Y .PSU 3 3 1) (S : Sylow 3 Y) : IsExtraspecialExpP 3 1 ↥(S : Subgroup Y) :=
  isExtraspecialExpP_of_isHeisThree (isHeisThree_sylow_u33 hY S)

theorem sylow_isExtraspecialExpP_of_types
    (h : SylowIsExtraspecialOfTypes) {Y : Type} [Group Y] [Finite Y]
    (hY : LieModel Y .PSL 3 3 1 ∨ LieModel Y .PSU 3 3 1 ∨ LieModel Y .Tits 0 2 1 ∨
      IsSpor Y .J2 ∨ IsSpor Y .He ∨ IsSpor Y .Ru ∨ IsSpor Y .J4 ∨ IsSpor Y .M12 ∨
      IsSpor Y .M24)
    (S : Sylow 3 Y) : IsExtraspecialExpP 3 1 ↥(S : Subgroup Y) := by
  rcases hY with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact h Y (Or.inl h1) S
  · exact isExtraspecialExpP_of_isHeisThree (isHeisThree_sylow_u33 h2 S)
  · exact h Y (Or.inr h3) S
  · exact isExtraspecialExpP_of_isHeisThree (isHeisThree_sylow_j2 h4 S)
  · exact isExtraspecialExpP_of_isHeisThree (isHeisThree_sylow_he h5 S)
  · exact isExtraspecialExpP_of_isHeisThree (isHeisThree_sylow_ru h6 S)
  · exact isExtraspecialExpP_of_isHeisThree (isHeisThree_sylow_j4 h7 S)
  · exact isExtraspecialExpP_of_isHeisThree (isHeisThree_sylow_m12 h8 S)
  · exact isExtraspecialExpP_of_isHeisThree (isHeisThree_sylow_m24 h9 S)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
