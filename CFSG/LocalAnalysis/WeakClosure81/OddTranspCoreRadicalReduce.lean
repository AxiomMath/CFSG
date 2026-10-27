module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreRadicalDefs
public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreStar

import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreRadicalLift
import CFSG.Goldschmidt75.OddCore
import CFSG.OddTranspositions.SevenThreeQuotient
import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Hom
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Timmesfeld.Bridge.Asc72Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoreRadical

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.Timmesfeld.Bridge.Asc72 (IsOddTransp)

private theorem configB_of_hasCoreStar {G : Type} [Group G] [Finite G] {t : G}
    (ht : t * t = 1) (h : CFSG.LocalAnalysis.WeakClosure81.CoreStar.HasCoreStar G t) :
    ∃ Lh : Subgroup G, zpowers t ≤ Lh ∧ ¬ zpowers t ≤ pCoreOf 2 Lh ∧
      (⨆ (y : G) (_ : conjSubgroup (zpowers t) y ≤ Lh), conjSubgroup (zpowers t) y) = Lh ∧
      HasQuotShape Lh (pCoreOf 2 Lh : Set G) (fun Y _ => IsSymGp Y 3) ∧
      4 ≤ Set.ncard {W : Subgroup G | ∃ x ∈ pCoreOf 2 Lh, W = conjSubgroup (zpowers t) x} := by
  obtain ⟨e₁, e₂, e₃, k₁, k₂, k₃, o₁, o₂, o₃, c₁₂, c₁₃, c₂₃, n₁₂, n₁₃, n₂₃⟩ := h
  have hsq : ∀ x : G, IsConj t x → x * x = 1 := by
    intro x hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hx
    rw [show c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ by group, ht, mul_one,
      mul_inv_cancel]
  have hbr : ∀ x : G, IsConj t x → orderOf (t * x) = 3 → t * x * t = x * t * x := fun x hx h3 =>
    (CFSG.OddTranspositions.conj_eq_of_orderOf_mul_eq_three ht (hsq x hx) h3).symm
  have hne : t ≠ e₁ := by
    intro h'
    rw [← h', ht, orderOf_one] at o₁
    exact absurd o₁ (by decide)
  exact CFSG.LocalAnalysis.WeakClosure81.CoreStar.configB_of_star ht (hsq e₁ k₁) (hsq e₂ k₂)
    (hsq e₃ k₃) (hbr e₁ k₁ o₁) (hbr e₂ k₂ o₂) (hbr e₃ k₃ o₃) c₁₂ c₁₃ c₂₃ hne n₁₂ n₁₃ n₂₃
    k₁ k₂ k₃

private theorem isOddTransp_quotient_class {X : Type} [Group X] [Finite X] (N : Subgroup X)
    [N.Normal] {s : X} (hodd : IsOddTransp {x : X | IsConj s x}) (hs : s ∉ N) :
    IsOddTransp {y : X ⧸ N | IsConj (QuotientGroup.mk' N s) y} := by
  have hne : ∀ x ∈ {x : X | IsConj s x}, QuotientGroup.mk' N x ≠ 1 := by
    intro x hx hx1
    have hc : IsConj (QuotientGroup.mk' N s) (QuotientGroup.mk' N x) :=
      MonoidHom.map_isConj _ hx
    exact hs ((QuotientGroup.eq_one_iff s).mp (isConj_one_left.mp (hx1 ▸ hc)))
  have htransp := CFSG.OddTranspositions.image_isOddTransp_quotient N hodd hne
  obtain ⟨c, hc⟩ := CFSG.OddTranspositions.image_isClass_quotient
    (Θ := {x : X | IsConj s x}) (d₀ := s) rfl N
  have hmem : QuotientGroup.mk' N s ∈ QuotientGroup.mk' N '' {x : X | IsConj s x} :=
    ⟨s, IsConj.refl s, rfl⟩
  rw [hc] at hmem htransp
  have hcl : {g | IsConj c g} = {y : X ⧸ N | IsConj (QuotientGroup.mk' N s) y} := by
    ext y
    exact ⟨fun h => hmem.symm.trans h, fun h => hmem.trans h⟩
  rwa [hcl] at htransp

section Quot

variable {X : Type} [Group X] [Finite X] {s : X}

theorem solvableRadical_quot_le_center
    (hR : (CFSG.solvableRadical X).map (QuotientGroup.mk' (fusionOddCore X)) ≤
      Subgroup.center (X ⧸ fusionOddCore X)) :
    CFSG.solvableRadical (X ⧸ fusionOddCore X) ≤ Subgroup.center (X ⧸ fusionOddCore X) := by
  have hk : Group.IsSolvable (QuotientGroup.mk' (fusionOddCore X)).ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ CFSG.Goldschmidt75.odd_card_oddCore
  rw [← CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.map_solvableRadical
    (QuotientGroup.mk'_surjective _) hk]
  exact hR

theorem isOddTransp_quot (hord : orderOf s = 2) (hodd : IsOddTransp {x : X | IsConj s x}) :
    IsOddTransp
      {y : X ⧸ fusionOddCore X | IsConj (QuotientGroup.mk' (fusionOddCore X) s) y} := by
  refine isOddTransp_quotient_class _ hodd fun hmem => ?_
  have hs1 : s = 1 :=
    CFSG.Goldschmidt75.eq_one_of_mem_odd_of_two_power CFSG.Goldschmidt75.odd_card_oddCore hmem
      (k := 1) (by rw [pow_one, ← hord, pow_orderOf_eq_one])
  rw [hs1, orderOf_one] at hord
  exact absurd hord (by decide)

omit [Finite X] in
theorem not_threeTransp_quot
    (h3 : ¬ (∀ d e : X, IsConj s d → IsConj s e →
      orderOf (QuotientGroup.mk' (fusionOddCore X) d * QuotientGroup.mk' (fusionOddCore X) e) ∈
        ({1, 2, 3} : Set ℕ))) :
    ¬ (∀ d e : X ⧸ fusionOddCore X, IsConj (QuotientGroup.mk' (fusionOddCore X) s) d →
      IsConj (QuotientGroup.mk' (fusionOddCore X) s) e →
        orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) := by
  intro h
  apply h3
  intro d e hd he
  exact h _ _ (MonoidHom.map_isConj _ hd) (MonoidHom.map_isConj _ he)

end Quot

section Center

variable {Y : Type} [Group Y] [Finite Y] {t : Y}

theorem solvableRadical_quot_center_eq_bot
    (hR : CFSG.solvableRadical Y ≤ Subgroup.center Y) :
    CFSG.solvableRadical (Y ⧸ Subgroup.center Y) = ⊥ := by
  have hk : Group.IsSolvable (QuotientGroup.mk' (Subgroup.center Y)).ker := by
    rw [QuotientGroup.ker_mk']
    exact Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)
  rw [← CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.map_solvableRadical
    (QuotientGroup.mk'_surjective _) hk, eq_bot_iff]
  exact (Subgroup.map_mono hR).trans (QuotientGroup.map_mk'_self _).le

omit [Finite Y] in
private theorem not_mem_center_of_not_threeTransp (hodd : IsOddTransp {x : Y | IsConj t x})
    (h3 : ¬ (∀ d e : Y, IsConj t d → IsConj t e → orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))) :
    t ∉ Subgroup.center Y := by
  intro htZ
  have htt : t * t = 1 := by rw [← pow_two, ← hodd.1 t (IsConj.refl t), pow_orderOf_eq_one]
  apply h3
  intro d e hd he
  rw [← IsConj.eq_of_left_mem_center hd htZ, ← IsConj.eq_of_left_mem_center he htZ, htt,
    orderOf_one]
  norm_num

omit [Finite Y] in
theorem orderOf_mk_center (hodd : IsOddTransp {x : Y | IsConj t x})
    (h3 : ¬ (∀ d e : Y, IsConj t d → IsConj t e → orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))) :
    orderOf (QuotientGroup.mk t : Y ⧸ Subgroup.center Y) = 2 := by
  have htt : t * t = 1 := by rw [← pow_two, ← hodd.1 t (IsConj.refl t), pow_orderOf_eq_one]
  refine orderOf_eq_prime ?_ fun h =>
    not_mem_center_of_not_threeTransp hodd h3 ((QuotientGroup.eq_one_iff t).mp h)
  rw [← QuotientGroup.mk_pow, pow_two, htt, QuotientGroup.mk_one]

theorem isOddTransp_mk_center (hodd : IsOddTransp {x : Y | IsConj t x})
    (h3 : ¬ (∀ d e : Y, IsConj t d → IsConj t e → orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))) :
    IsOddTransp {x : Y ⧸ Subgroup.center Y | IsConj (QuotientGroup.mk t) x} :=
  isOddTransp_quotient_class _ hodd (not_mem_center_of_not_threeTransp hodd h3)

omit [Finite Y] in
theorem not_threeTransp_mk_center (hodd : IsOddTransp {x : Y | IsConj t x})
    (h3 : ¬ (∀ d e : Y, IsConj t d → IsConj t e → orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))) :
    ¬ (∀ d e : Y ⧸ Subgroup.center Y, IsConj (QuotientGroup.mk t) d →
      IsConj (QuotientGroup.mk t) e → orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) := by
  intro h
  apply h3
  intro d e hd he
  exact orderOf_mul_mem_of_mk_center hodd hd he
    (h (QuotientGroup.mk' (Subgroup.center Y) d) (QuotientGroup.mk' (Subgroup.center Y) e)
      (by simpa using MonoidHom.map_isConj (QuotientGroup.mk' (Subgroup.center Y)) hd)
      (by simpa using MonoidHom.map_isConj (QuotientGroup.mk' (Subgroup.center Y)) he))

end Center

variable {X : Type} [Group X] [Finite X] {s : X}

theorem configBC_of_radicalOutcome (hord : orderOf s = 2)
    (hodd : IsOddTransp {x : X | IsConj s x})
    (h : RadicalOutcome ((X ⧸ fusionOddCore X) ⧸ Subgroup.center (X ⧸ fusionOddCore X))
      (QuotientGroup.mk (QuotientGroup.mk' (fusionOddCore X) s))) :
    (∃ Lh : Subgroup (X ⧸ fusionOddCore X),
        Subgroup.zpowers (QuotientGroup.mk' (fusionOddCore X) s) ≤ Lh ∧
        ¬ Subgroup.zpowers (QuotientGroup.mk' (fusionOddCore X) s) ≤ pCoreOf 2 Lh ∧
        (⨆ (y : X ⧸ fusionOddCore X)
            (_ : conjSubgroup (Subgroup.zpowers (QuotientGroup.mk' (fusionOddCore X) s)) y ≤ Lh),
            conjSubgroup (Subgroup.zpowers (QuotientGroup.mk' (fusionOddCore X) s)) y) = Lh ∧
        HasQuotShape Lh (pCoreOf 2 Lh : Set (X ⧸ fusionOddCore X)) (fun Y _ => IsSymGp Y 3) ∧
        4 ≤ Set.ncard {W : Subgroup (X ⧸ fusionOddCore X) | ∃ x ∈ pCoreOf 2 Lh,
            W = conjSubgroup (Subgroup.zpowers (QuotientGroup.mk' (fusionOddCore X) s)) x}) ∨
      ∃ Lh : Subgroup (X ⧸ fusionOddCore X),
        ∃ hsLh : QuotientGroup.mk' (fusionOddCore X) s ∈ Lh,
        Subgroup.normalClosure ({⟨_, hsLh⟩} : Set ↥Lh) = ⊤ ∧
        ∃ n : ℕ, 1 < n ∧ IsL2OrSz (↥Lh ⧸ fusionZStar ↥Lh) n := by
  let π : X →* X ⧸ fusionOddCore X := QuotientGroup.mk' (fusionOddCore X)
  have hss : s * s = 1 := by rw [← pow_two, ← hord, pow_orderOf_eq_one]
  have htt : π s * π s = 1 := by rw [← map_mul, hss, map_one]
  have hO : fusionOddCore (X ⧸ fusionOddCore X) = ⊥ :=
    CFSG.Goldschmidt75.oddCore_quotient_eq_bot
  have hoddY : IsOddTransp {x : X ⧸ fusionOddCore X | IsConj (π s) x} :=
    isOddTransp_quot hord hodd
  rcases radicalOutcome_lift (Y := X ⧸ fusionOddCore X) (t := π s) hO hoddY h with hstar | hL
  · exact Or.inl (configB_of_hasCoreStar htt hstar)
  · exact Or.inr hL

end CFSG.LocalAnalysis.WeakClosure81.CoreRadical
