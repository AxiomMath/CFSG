module

public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUComp
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUModel
import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSU
import CFSG.LocalAnalysis.StandardType.GGNbrBalanceBasic

public section

namespace CFSG.StandardType.SUTorus

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.SectionRank.OddCover

theorem exists_comp_conjSU_diag {K : Type} [Field K] {f n : ℕ} {G : Type*} [Group G]
    (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1) {ψ : ↥(unitarySU 2 f K n) →* G}
    (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n)) {E : Subgroup G}
    (hE : IsElemAbelian p E) (hbig : p ^ (n / p + 1) < Nat.card E)
    (hEB : ∀ e ∈ E, ∃ B ∈ primeFormUnitary h (idGram K n), (e, B) ∈ suPairs ψ)
    (hEC : E ⊓ Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    ∃ ψ' : ↥(unitarySU 2 f K n) →* G, ψ'.range = ψ.range ∧
      ψ'.ker ≤ Subgroup.center ↥(unitarySU 2 f K n) ∧
      ∀ e ∈ E, ∃ d : Fin n → Kˣ, (e, diagHom n d) ∈ suPairs ψ' := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  have hEA : ∀ e ∈ E, ∃ A, (e, A) ∈ suPairs ψ := fun e he => by
    obtain ⟨B, -, hB⟩ := hEB e he
    exact ⟨B, hB⟩
  have hT := isToral_inducedMatrices h hn hnq hp hp2 hpq hker hE hbig hEA hEC
  obtain ⟨Q, hQ, hQd⟩ := exists_unitary_frame h hp hp2 hpq
    (isProjElem_inducedMatrices h hn hnq hp hpq hker hE) hT
  refine ⟨ψ.comp (TableBUE.conjSU h Q hQ).symm.toMonoidHom, range_comp_conjSU_symm h ψ Q hQ,
    ker_comp_conjSU_symm_le h hker Q hQ, fun e he => ?_⟩
  obtain ⟨B, hBU, hB⟩ := hEB e he
  obtain ⟨d, hd⟩ := hQd B (mem_inducedMatrices.mpr ⟨e, he, hB⟩) hBU
  refine ⟨d, ?_⟩
  rw [← hd]
  exact mem_suPairs_frame h hQ hB

private lemma four_le_card_blockSU_of_isComponentOf_two {K : Type} [Field K] {m : ℕ} {G : Type}
    [Group G] [Finite G] (h : UnitaryFieldData 2 1 K)
    {ψ : ↥(unitarySU 2 1 K (m + 1)) →* G}
    {e : G} {J : Subgroup G}
    (hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer ({e} : Set G)))
    {I : Finset (Fin (m + 1))} {i : Fin (m + 1)} (hi : i ∈ I)
    (hJI : J ≤ (TableBUE.blockSU (K := K) (n := 1) I).map ψ) :
    4 ≤ I.card := by
  by_contra hlt
  have hk1 : 1 ≤ I.card := Finset.card_pos.mpr ⟨i, hi⟩
  have hk3 : I.card ≤ 3 := by omega
  haveI : Group.IsSolvable ↥(unitarySU 2 1 K I.card) :=
    WitSU.isSolvable_unitarySU_two_one h hk1 hk3
  let eI := TableBUE.blockSUEquiv (K := K) (n := 1) I h
  haveI : Group.IsSolvable ↥(TableBUE.blockSU (K := K) (n := 1) I) :=
    Group.isSolvable_of_isSolvable_injective (f := eI.symm.toMonoidHom)
      (fun x y hxy => eI.symm.injective hxy)
  have hsolv : Group.IsSolvable ↥((TableBUE.blockSU (K := K) (n := 1) I).map ψ) := by
    have hres := Group.isSolvable_of_surjective
      (f := (ψ.comp (TableBUE.blockSU (K := K) (n := 1) I).subtype).rangeRestrict)
      (MonoidHom.rangeRestrict_surjective _)
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at hres
  haveI := hsolv
  haveI hsolvJ : Group.IsSolvable ↥J := by
    let eJ := Subgroup.subgroupOfEquivOfLe hJI
    haveI : Group.IsSolvable ↥(J.subgroupOf
        ((TableBUE.blockSU (K := K) (n := 1) I).map ψ)) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (J.subgroupOf ((TableBUE.blockSU (K := K) (n := 1) I).map ψ)).subtype)
        (fun x y hxy => Subtype.ext hxy)
    exact Group.isSolvable_of_surjective (f := eJ.toMonoidHom) (fun z => ⟨eJ.symm z, by simp⟩)
  haveI : Group.IsPerfect ↥J := ⟨hJ.2.2.1⟩
  haveI : Nontrivial ↥J := CFSG.ComponentClassification.Quasisimple.nontrivial hJ.2.2
  exact Group.IsPerfect.not_isSolvable ↥J hsolvJ

theorem exists_blockSU_of_isComponentOf_two {K : Type} [Field K] {m : ℕ} {G : Type} [Group G]
    [Finite G] (h : UnitaryFieldData 2 1 K) {ψ : ↥(unitarySU 2 1 K (m + 1)) →* G}
    (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 1 K (m + 1))) {e : G}
    {δ : Fin (m + 1) → Kˣ} (he : (e, diagHom (m + 1) δ) ∈ suPairs ψ) {J : Subgroup G}
    (hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer ({e} : Set G))) :
    ∃ I : Finset (Fin (m + 1)), 4 ≤ I.card ∧ (∀ i ∈ I, ∀ j ∈ I, δ i = δ j) ∧
      J = (TableBUE.blockSU (K := K) (n := 1) I).map ψ := by
  classical
  set δ' : G → Fin (m + 1) → Kˣ := fun _ => δ with hδ'
  have hδ : ∀ e' ∈ ({e} : Set G), (e', diagHom (m + 1) (δ' e')) ∈ suPairs ψ := by
    intro e' he'
    rw [Set.mem_singleton_iff.mp he']
    exact he
  obtain ⟨i, hJI⟩ := exists_le_map_blockSU h Nat.prime_three (by norm_num) hker hδ hJ
  set I := LinTorus.diagClass ({e} : Set G) δ' i with hI
  have hconst : ∀ a ∈ I, ∀ b ∈ I, δ a = δ b := fun a ha b hb =>
    LinTorus.eq_of_mem_diagClass ha hb (Set.mem_singleton e)
  have hI4 : 4 ≤ I.card :=
    four_le_card_blockSU_of_isComponentOf_two h hJ
      (by rw [hI]; exact LinTorus.self_mem_diagClass _ δ' i) hJI
  have hnq : (I.card, 2 ^ 1) ≠ (3, 2) := fun hc => by
    have := congrArg Prod.fst hc
    simp only at this
    omega
  have hLq : CFSG.Assembly.IsQuasisimple ↥((TableBUE.blockSU (K := K) (n := 1) I).map ψ) :=
    isQuasisimple_map_blockSU h hker (by omega) hnq
  have hLs := isSubnormal_map_blockSU hker hδ i
  have hL : IsComponentOf ((TableBUE.blockSU (K := K) (n := 1) I).map ψ)
      (ψ.range ⊓ Subgroup.centralizer ({e} : Set G)) :=
    ⟨isSubnormal_le_of_assembly hLs, hLs, hLq⟩
  rcases isComponentOf_le_or_commutator_eq_bot hL hJ.2.1 with hLJ | hc
  · exact ⟨I, hI4, hconst, le_antisymm hJI hLJ⟩
  · exfalso
    apply commutator_ne_bot_of_isQuasisimple hJ.2.2
    exact le_bot_iff.1 ((Subgroup.commutator_mono hJI le_rfl).trans hc.le)

theorem exists_hom_of_eq_map_blockSU {K : Type} [Field K] {f n : ℕ} {G : Type} [Group G]
    (h : UnitaryFieldData 2 f K) {ψ : ↥(unitarySU 2 f K n) →* G}
    (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n)) {V : Finset (Fin n)} {J : Subgroup G}
    (hJ : J = (TableBUE.blockSU (K := K) (n := f) V).map ψ) :
    ∃ ρ : ↥(unitarySU 2 f K V.card) →* ↥J, Function.Surjective ρ ∧
      ρ.ker ≤ Subgroup.center ↥(unitarySU 2 f K V.card) := by
  subst hJ
  set U := TableBUE.blockSU (K := K) (n := f) V with hU
  set φ := ψ.comp U.subtype with hφ
  have hr : φ.range = U.map ψ := range_comp_subtype_blockSU ψ V
  let e := TableBUE.blockSUEquiv V h
  let ρ : ↥(unitarySU 2 f K V.card) →* ↥(U.map ψ) :=
    ((MulEquiv.subgroupCongr hr).toMonoidHom.comp φ.rangeRestrict).comp e.toMonoidHom
  refine ⟨ρ, ?_, ?_⟩
  · exact (MulEquiv.subgroupCongr hr).surjective.comp
      (φ.rangeRestrict_surjective.comp e.surjective)
  · intro u hu
    have h1 : φ.rangeRestrict (e u) = 1 :=
      (MulEquiv.subgroupCongr hr).injective (by
        rw [map_one]
        exact hu)
    have hu' : e u ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val h1
    have hz := ker_comp_subtype_blockSU_le hker V hu'
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    apply e.injective
    rw [map_mul, map_mul]
    exact hz (e g)

end CFSG.StandardType.SUTorus

end
