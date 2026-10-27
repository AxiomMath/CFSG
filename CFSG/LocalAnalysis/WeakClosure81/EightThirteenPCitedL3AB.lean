module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCitedAut
import CFSG.RankThree.PartTwo.KFacts.L34Centralizers
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDescent
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.KFacts.L34Aut

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3)
open CFSG.RankThree.PartTwo.KFacts.L34
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel (autFixed mem_autFixed)
open CFSG.ComponentClassification.CatalogueBHigherLinearField

private theorem wccl_isPGroup_two_of_sq_eq_one {G : Type*} [Group G] {H : Subgroup G}
    (h : ∀ x : H, x * x = 1) : IsPGroup 2 H := by
  intro x
  exact ⟨1, by simpa [pow_two] using h x⟩

private theorem wccl_isPGroup_two_autFixed {G : Type*} [Group G] {β : MulAut G}
    (h : ∀ x : G, β x = x → x * x = 1) : IsPGroup 2 (autFixed β) := by
  apply wccl_isPGroup_two_of_sq_eq_one
  intro x
  exact Subtype.ext (h x (mem_autFixed.mp x.2))

private theorem wccl_false_of_isPGroup_two_of_three_dvd {G : Type*} [Group G] [Finite G]
    (hp : IsPGroup 2 G) (h3 : 3 ∣ Nat.card G) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hp
  rw [hn] at h3
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

private theorem wccl_simple_case {G : Type*} [Group G] [Finite G] {C F : Subgroup G}
    (hFC : F ≤ C) (hCn : C ≤ Subgroup.normalizer (F : Set G)) [IsSimpleGroup C]
    (hFp : IsPGroup 2 F) (h3 : 3 ∣ Nat.card C) : F = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFn : (F.subgroupOf C).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hCn
  rcases hFn.eq_bot_or_eq_top with h | h
  · rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxC : (⟨x, hFC hx⟩ : C) ∈ F.subgroupOf C := Subgroup.mem_subgroupOf.mpr hx
    rw [h] at hxC
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hxC)
  · exfalso
    have hCF : C ≤ F := Subgroup.subgroupOf_eq_top.mp h
    have hFC' : F = C := le_antisymm hFC hCF
    have hCp : IsPGroup 2 C := by rw [← hFC']; exact hFp
    exact wccl_false_of_isPGroup_two_of_three_dvd hCp h3

private theorem wccl_conj_setup {P : Type*} [Group P] {β τ c : MulAut P}
    (hβ : β = c * τ * c⁻¹) {E : Subgroup P} (hEC : E ≤ autFixed β)
    (hnorm : autFixed β ≤ Subgroup.normalizer (E : Set P)) :
    E.map c.symm.toMonoidHom ≤ autFixed τ ∧
      autFixed τ ≤ Subgroup.normalizer (E.map c.symm.toMonoidHom : Set P) ∧
      (E.map c.symm.toMonoidHom = ⊥ ↔ E = ⊥) := by
  have hcomp : ((c.symm).toMonoidHom.comp c.toMonoidHom) = MonoidHom.id P := by
    ext x
    simp
  have hCβ : autFixed β = (autFixed τ).map c.toMonoidHom := by
    rw [hβ, autFixed_conj]
  refine ⟨?_, ?_, ?_⟩
  · have h := Subgroup.map_mono (f := (c.symm).toMonoidHom) hEC
    rw [hCβ] at h
    rwa [Subgroup.map_map, hcomp, Subgroup.map_id] at h
  · have h := Subgroup.map_mono (f := (c.symm).toMonoidHom) hnorm
    rw [hCβ] at h
    rw [Subgroup.map_map, hcomp, Subgroup.map_id] at h
    rwa [Subgroup.map_equiv_normalizer_eq E c.symm] at h
  · exact Subgroup.map_eq_bot_iff_of_injective E
      (f := (c.symm).toMonoidHom) (c.symm).injective

private theorem wccl_notElem {k : Type} [Field k] (hk : Nat.card k = 4) :
    OuterFixedNotElem (projectiveSL 3 k) := by
  classical
  intro β hβ2 hout
  by_contra hcon
  haveI : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  haveI : CharP k 2 := LinearFieldFour.charP_two_of_card_eq_four hk
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (projectiveSL 3 k) :=
    Finite.of_surjective (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 k)
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective 3 k)
  have hall : ∀ x : projectiveSL 3 k, β x = x → x * x = 1 := by
    intro x hx
    by_contra hne
    exact hcon ⟨x, hx, hne⟩
  have hp : IsPGroup 2 (autFixed β) := wccl_isPGroup_two_autFixed hall
  have hσ : ∀ a : k, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  rcases involution_cases_card hk (σ := frobeniusEquiv k 2) hσ hβ2 with hinn | hcase
  · rcases hinn with ⟨g, hg⟩
    exact hout ⟨g, fun x => by rw [← hg]; rfl⟩
  · rcases hcase with ⟨⟨H, hH⟩, hcard⟩ | hcase
    · exact wccl_false_of_isPGroup_two_of_three_dvd hp (by rw [hcard]; norm_num)
    · rcases hcase with ⟨⟨H, hH⟩, hcard⟩ | ⟨⟨H, hH⟩, hcard⟩
      · exact wccl_false_of_isPGroup_two_of_three_dvd hp (by rw [hcard]; norm_num)
      · exact wccl_false_of_isPGroup_two_of_three_dvd hp (by rw [hcard]; norm_num)

private theorem wccl_isSimpleGroup_fieldAut {k : Type} [Field k] {σ : k ≃+* k}
    (hk : Nat.card k = 4) (hσ : ∀ a : k, σ a = a ^ 2) :
    IsSimpleGroup (autFixed (fieldAut 3 k σ)) := by
  haveI : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  haveI : IsSimpleGroup (projectiveSL 3 (fixedField k σ)) := by
    haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (fixedField k σ)) :=
      (CFSG.LinearGroups.linear_projective_simple (n := 3) (K := fixedField k σ)
        (by norm_num) (Or.inl (by norm_num))).2.1
    exact (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3
      (fixedField k σ)).symm.isSimpleGroup
  obtain ⟨e1⟩ := nonempty_autFixed_fieldAut_equiv hk hσ
  exact e1.isSimpleGroup

private theorem wccl_isSimpleGroup_dualAut {k : Type} [Field k] (hk : Nat.card k = 4) :
    IsSimpleGroup (autFixed (dualAut 3 k)) := by
  haveI : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  haveI : CharP k 2 := LinearFieldFour.charP_two_of_card_eq_four hk
  haveI : IsSimpleGroup (CFSG.Open.StatedSp 1 k) := by
    haveI : IsSimpleGroup (CFSG.Open.StatedProj (CFSG.Open.StatedSp 1 k)) :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp k 1 (by norm_num)
        (Or.inl (Or.inr (by omega)))
    have hZsp := CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot (n := 1) (K := k)
    have eSp : CFSG.Open.StatedProj (CFSG.Open.StatedSp 1 k) ≃* CFSG.Open.StatedSp 1 k :=
      (QuotientGroup.quotientMulEquivOfEq hZsp).trans QuotientGroup.quotientBot
    exact eSp.symm.isSimpleGroup
  obtain ⟨e2⟩ := nonempty_autFixed_dualAut_equiv hk
  exact e2.isSimpleGroup

private theorem wccl_noNormalTwo {k : Type} [Field k] (hk : Nat.card k = 4) :
    OuterFixedNoNormalTwo (projectiveSL 3 k) := by
  classical
  intro β hβ2 hout E hEp hfix hnorm
  haveI : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  haveI : CharP k 2 := LinearFieldFour.charP_two_of_card_eq_four hk
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (projectiveSL 3 k) :=
    Finite.of_surjective (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 k)
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective 3 k)
  have hσ : ∀ a : k, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  have hEC : E ≤ autFixed β := fun x hx => mem_autFixed.mpr (hfix x hx)
  have hnorm' : autFixed β ≤ Subgroup.normalizer (E : Set (projectiveSL 3 k)) :=
    Subgroup.le_normalizer_iff.mpr fun y hy x hx => hnorm y (mem_autFixed.mp hy) x hx
  rcases involution_cases_card hk (σ := frobeniusEquiv k 2) hσ hβ2 with hinn | hcase
  · rcases hinn with ⟨g, hg⟩
    exact absurd ⟨g, fun x => by rw [← hg]; rfl⟩ hout
  · rcases hcase with ⟨⟨H, hH⟩, _⟩ | hcase
    ·
      set τ : MulAut (projectiveSL 3 k) := fieldAut 3 k (frobeniusEquiv k 2) with hτ
      have hβ : β = conjAut 3 k H * τ * (conjAut 3 k H)⁻¹ := by rw [hτ]; exact hH
      obtain ⟨hFle, hnormF, hmapbot⟩ := wccl_conj_setup hβ hEC hnorm'
      haveI : IsSimpleGroup (autFixed τ) := by
        rw [hτ]; exact wccl_isSimpleGroup_fieldAut hk hσ
      have hFp : IsPGroup 2 (E.map (conjAut 3 k H).symm.toMonoidHom) :=
        hEp.of_equiv (Subgroup.equivMapOfInjective E
          (conjAut 3 k H).symm.toMonoidHom (conjAut 3 k H).symm.injective)
      have h3 : 3 ∣ Nat.card (autFixed τ) := by
        rw [hτ, card_autFixed_fieldAut hk hσ]
        norm_num
      have hFbot : E.map (conjAut 3 k H).symm.toMonoidHom = ⊥ :=
        wccl_simple_case hFle hnormF hFp h3
      exact hmapbot.mp hFbot
    · rcases hcase with ⟨⟨H, hH⟩, _⟩ | ⟨⟨H, hH⟩, _⟩
      ·
        set τ : MulAut (projectiveSL 3 k) := dualAut 3 k with hτ
        have hβ : β = conjAut 3 k H * τ * (conjAut 3 k H)⁻¹ := by rw [hτ]; exact hH
        obtain ⟨hFle, hnormF, hmapbot⟩ := wccl_conj_setup hβ hEC hnorm'
        haveI : IsSimpleGroup (autFixed τ) := by
          rw [hτ]; exact wccl_isSimpleGroup_dualAut hk
        have hFp : IsPGroup 2 (E.map (conjAut 3 k H).symm.toMonoidHom) :=
          hEp.of_equiv (Subgroup.equivMapOfInjective E
            (conjAut 3 k H).symm.toMonoidHom (conjAut 3 k H).symm.injective)
        have h3 : 3 ∣ Nat.card (autFixed τ) := by
          rw [hτ, card_autFixed_dualAut hk]
          norm_num
        have hFbot : E.map (conjAut 3 k H).symm.toMonoidHom = ⊥ :=
          wccl_simple_case hFle hnormF hFp h3
        exact hmapbot.mp hFbot
      ·
        set τ : MulAut (projectiveSL 3 k) := betaAut (frobeniusEquiv k 2) with hτ
        have hβ : β = conjAut 3 k H * τ * (conjAut 3 k H)⁻¹ := by rw [hτ]; exact hH
        obtain ⟨hFle, hnormF, hmapbot⟩ := wccl_conj_setup hβ hEC hnorm'
        have hFp : IsPGroup 2 (E.map (conjAut 3 k H).symm.toMonoidHom) :=
          hEp.of_equiv (Subgroup.equivMapOfInjective E
            (conjAut 3 k H).symm.toMonoidHom (conjAut 3 k H).symm.injective)
        have hτeq : autFixed τ =
            Subgroup.normalizer (eZero k : Set (projectiveSL 3 k)) := by
          rw [hτ]
          exact autFixed_betaAut hk hσ
        have hnormF' : Subgroup.normalizer (eZero k : Set (projectiveSL 3 k)) ≤
            Subgroup.normalizer (E.map (conjAut 3 k H).symm.toMonoidHom :
              Set (projectiveSL 3 k)) := by
          rw [← hτeq]
          exact hnormF
        have hE9le : eZero k ≤ Subgroup.normalizer
            (E.map (conjAut 3 k H).symm.toMonoidHom : Set (projectiveSL 3 k)) :=
          Subgroup.le_normalizer.trans hnormF'
        have hY : ¬ 3 ∣ Nat.card (E.map (conjAut 3 k H).symm.toMonoidHom) := by
          obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hFp
          rw [hn]
          intro h3
          exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
        have hFbot : E.map (conjAut 3 k H).symm.toMonoidHom = ⊥ :=
          eq_bot_of_le_normalizer hk (card_eZero hk) hY hE9le
        exact hmapbot.mp hFbot

theorem outerFixedNotElem_isL3 {M : Type} [Group M] [Finite M] (h : IsL3 M 2) :
    OuterFixedNotElem M := by
  obtain ⟨K, hK, hfin, hcard, ⟨e⟩⟩ :=
    LinearCover.exists_mulEquiv_projectiveSL_of_lieModel (n := 3) (p := 2) (f := 2) h
  letI : Field K := hK
  haveI : Finite K := hfin
  have hk : Nat.card K = 4 := by rw [hcard]; norm_num
  exact outerFixedNotElem_of_mulEquiv e.symm (wccl_notElem hk)

theorem outerFixedNoNormalTwo_isL3 {M : Type} [Group M] [Finite M] (h : IsL3 M 2) :
    OuterFixedNoNormalTwo M := by
  obtain ⟨K, hK, hfin, hcard, ⟨e⟩⟩ :=
    LinearCover.exists_mulEquiv_projectiveSL_of_lieModel (n := 3) (p := 2) (f := 2) h
  letI : Field K := hK
  haveI : Finite K := hfin
  have hk : Nat.card K = 4 := by rw [hcard]; norm_num
  exact outerFixedNoNormalTwo_of_mulEquiv e.symm (wccl_noNormalTwo hk)

end CFSG.LocalAnalysis.WeakClosure81

end
