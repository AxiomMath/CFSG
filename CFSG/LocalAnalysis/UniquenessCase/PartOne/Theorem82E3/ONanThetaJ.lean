module

public import CFSG.RankThree.LocalRank.ThetaPlaneAlpha
public import CFSG.LocalAnalysis.SolvableSignalizer.CoprimeAction
public import CFSG.GroupTheory.PGroup.CardCoprime

public section

namespace CFSG.RankThree.LocalRank

open CFSG CFSG.SolvableSignalizer
open scoped Pointwise commutatorElement

private lemma isInvariant_conj_of_le_normalizer {G : Type} [Group G] {E Q : Subgroup G}
    (h : E ≤ Subgroup.normalizer (Q : Set G)) :
    SolvableSignalizer.IsInvariant ((MulAut.conj : G →* MulAut G).comp E.subtype) Q := by
  intro a
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (h a.2)

private lemma fixedSubgroup_conj_comp_eq_centralizer {G : Type} [Group G] (E : Subgroup G)
    (a : E) :
    fixedSubgroup ((MulAut.conj : G →* MulAut G).comp E.subtype) a =
      Subgroup.centralizer ({(a : G)} : Set G) := by
  ext x
  rw [mem_fixedSubgroup, Subgroup.mem_centralizer_singleton_iff]
  change (MulAut.conj (a : G)) x = x ↔ x * (a : G) = (a : G) * x
  rw [MulAut.conj_apply]
  constructor
  · intro h
    calc x * (a : G) = (a : G) * x * (a : G)⁻¹ * (a : G) := by rw [h]
      _ = (a : G) * x := by group
  · intro h
    calc (a : G) * x * (a : G)⁻¹ = x * (a : G) * (a : G)⁻¹ := by rw [h]
      _ = x := by group

private lemma map_fixedSubgroup_restrictAction_eq_inf_centralizer {G : Type} [Group G]
    (E Q : Subgroup G) (hQinv : SolvableSignalizer.IsInvariant ((MulAut.conj : G →* MulAut G).comp E.subtype) Q)
    (a : E) :
    (fixedSubgroup (restrictAction ((MulAut.conj : G →* MulAut G).comp E.subtype) Q hQinv)
        a).map Q.subtype =
      Q ⊓ Subgroup.centralizer ({(a : G)} : Set G) := by
  rw [fixedSubgroup_restrictAction_map_subtype, fixedIn,
    fixedSubgroup_conj_comp_eq_centralizer]

private lemma iSup_inf_centralizer_eq_self {G : Type} [Group G] [Finite G] {E Q : Subgroup G}
    [IsElementaryAbelian 3 E]
    (hQinv : SolvableSignalizer.IsInvariant ((MulAut.conj : G →* MulAut G).comp E.subtype) Q)
    (hcard3 : 3 ^ 2 ≤ Nat.card E) (hcop : ¬ 3 ∣ Nat.card ↥Q) :
    Q = ⨆ (a : E) (_ : a ≠ 1), Q ⊓ Subgroup.centralizer ({(a : G)} : Set G) := by
  letI : CommGroup E := IsMulCommutative.instCommGroup
  have hmain := iSup_fixedSubgroup_eq_top (A := E) (G := ↥Q) 3 Nat.prime_three
    (restrictAction ((MulAut.conj : G →* MulAut G).comp E.subtype) Q hQinv) hcard3 hcop
  have hmap := congrArg (Subgroup.map Q.subtype) hmain
  simp only [Subgroup.map_iSup,
    map_fixedSubgroup_restrictAction_eq_inf_centralizer E Q hQinv,
    Subgroup.map_top, Subgroup.range_subtype] at hmap
  exact hmap.symm

private lemma le_centralizer_of_thetaJ_eq_bot {G : Type} [Group G] {E : Subgroup G}
    (hJ : thetaJ 3 E = ⊥) :
    ∀ a : E, a ≠ 1 →
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({(a : G)} : Set G)) ≤
        Subgroup.centralizer (E : Set G) := by
  intro a ha
  have hle : ⁅inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({(a : G)} : Set G)), E⁆ ≤ thetaJ 3 E := by
    rw [thetaJ]
    exact le_iSup_of_le (a : G)
      (le_iSup_of_le a.2 (le_iSup_of_le (fun h => ha (Subtype.ext h)) le_rfl))
  have hbot : ⁅inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({(a : G)} : Set G)), E⁆ = ⊥ :=
    le_bot_iff.mp (by simpa [hJ] using hle)
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot

theorem thetaJ_ne_bot_of_le_theta {G : Type} [Group G] [Finite G] {E Q : Subgroup G}
    (hQ : IsPGroup 2 Q) (hEN : E ≤ Subgroup.normalizer (Q : Set G))
    [IsElementaryAbelian 3 E]
    (hcard : Nat.card E = 9)
    (hθ : ∀ f ∈ E, f ≠ 1 →
      Q ⊓ Subgroup.centralizer ({f} : Set G) ≤
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({f} : Set G)))
    (hnc : ¬ E ≤ Subgroup.centralizer (Q : Set G)) :
    thetaJ 3 E ≠ ⊥ := by
  intro hJ
  letI : CommGroup E := IsMulCommutative.instCommGroup
  let α : E →* MulAut G := (MulAut.conj : G →* MulAut G).comp E.subtype
  have hQinv : SolvableSignalizer.IsInvariant α Q := isInvariant_conj_of_le_normalizer hEN
  have hcard3 : 3 ^ 2 ≤ Nat.card E := by rw [hcard]; norm_num
  have hcop : ¬ 3 ∣ Nat.card ↥Q :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup hQ Nat.prime_three (by norm_num)
  have hgen : Q = ⨆ (a : E) (_ : a ≠ 1),
      Q ⊓ Subgroup.centralizer ({(a : G)} : Set G) :=
    iSup_inf_centralizer_eq_self hQinv hcard3 hcop
  have hcomm := le_centralizer_of_thetaJ_eq_bot (E := E) hJ
  have hQle : Q ≤ Subgroup.centralizer (E : Set G) := by
    rw [hgen]
    exact iSup_le fun a => iSup_le fun ha =>
      (hθ (a : G) a.2 (fun h => ha (Subtype.ext h))).trans (hcomm a ha)
  exact hnc (Subgroup.le_centralizer_iff.mp hQle)

end CFSG.RankThree.LocalRank

end
