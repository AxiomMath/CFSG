module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Finite.Defs
public import Mathlib.GroupTheory.NoncommCoprod

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCorePInfPg
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.HhatConjugateTI
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FUFittingContainment
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma25
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 3: the Fitting subgroup `F(U)` is a TI-subgroup

In the cyclic first case, the paper's line L512 asserts `P ∩ P^g = 1` for
`g ∉ N_H(V₁)`, and line L513--L514 conclude that `P·P^g` is an abelian
direct product.  The stronger normalizer-control statement proved here is
the full `F(U) ∩ F(U)^g = 1` for every `g ∉ Ĥ`, obtained by the same
`lemma_2_5` pattern used in `OddQCoreCentralized.lean`: the intersection
`X = F(U) ∩ F(U)^g` is transported back by `g⁻¹` into `F(U)`, where the
conjugated first-case normalizer clause (2) controls its normalizer;
Lemma 2.5 then forces `g ∈ Ĥ`.

The direct-product corollaries are stated abstractly: for commuting
subgroups with trivial intersection their join is isomorphic to their
product, and if both factors are abelian the join is abelian.  In the
first-case application the commuting hypothesis is supplied by normality
in `C_U(t₁)`.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- The join of two commuting subgroups with trivial intersection is
isomorphic to their direct product. -/
public noncomputable def subgroup_sup_equiv_prod_of_commute_of_disjoint
    {G : Type u} [Group G]
    (H K : Subgroup G)
    (hdisj : H ⊓ K = ⊥)
    (hcomm : ∀ h k, h ∈ H → k ∈ K → Commute h k) :
    ↥(H ⊔ K) ≃* (↥H) × (↥K) := by
  classical
  let f : H →* G := H.subtype
  let k : K →* G := K.subtype
  let hcomm' : ∀ h : H, ∀ kh : K, Commute (f h) (k kh) :=
    fun h kh => hcomm h.1 kh.1 h.2 kh.2
  let φ : (↥H) × (↥K) →* G :=
    f.noncommCoprod k hcomm'
  have hφinj : Function.Injective φ := by
    dsimp [φ]
    rw [MonoidHom.noncommCoprod_injective f k hcomm']
    refine ⟨Subgroup.subtype_injective _, Subgroup.subtype_injective _, ?_⟩
    rw [disjoint_iff_inf_le]
    intro x hx
    have hxH : x ∈ H := by
      rcases (Subgroup.mem_inf.mp hx).1 with ⟨h, rfl⟩
      exact h.2
    have hxK : x ∈ K := by
      rcases (Subgroup.mem_inf.mp hx).2 with ⟨g, rfl⟩
      exact g.2
    have hbot : x ∈ (⊥ : Subgroup G) := by
      rw [← hdisj]
      exact Subgroup.mem_inf.mpr ⟨hxH, hxK⟩
    exact Subgroup.mem_bot.mp hbot
  let e : (↥H) × (↥K) ≃* φ.range := MonoidHom.ofInjective hφinj
  have hφrange : φ.range = H ⊔ K := by
    have h := MonoidHom.noncommCoprod_range f k
      (fun h kh => hcomm h.1 kh.1 h.2 kh.2)
    simpa [f, k, Subgroup.range_subtype] using h
  exact (e.trans (MulEquiv.subgroupCongr hφrange)).symm

/-- The join of two commuting abelian subgroups with trivial intersection is
abelian. -/
public theorem subgroup_sup_isMulCommutative_of_commute_of_disjoint
    {G : Type u} [Group G]
    (H K : Subgroup G)
    (hdisj : H ⊓ K = ⊥)
    (hcomm : ∀ h k, h ∈ H → k ∈ K → Commute h k)
    (hHabel : IsMulCommutative (↥H)) (hKabel : IsMulCommutative (↥K)) :
    IsMulCommutative (↥(H ⊔ K)) := by
  classical
  have : IsMulCommutative (↥H) := hHabel
  have : IsMulCommutative (↥K) := hKabel
  let e := subgroup_sup_equiv_prod_of_commute_of_disjoint H K hdisj hcomm
  rw [isMulCommutative_iff]
  intro a b
  exact e.injective (by
    have hprod : IsMulCommutative ((↥H) × (↥K)) := inferInstance
    calc
      e (a * b) = e a * e b := e.map_mul a b
      _ = e b * e a := (isMulCommutative_iff.mp hprod) (e a) (e b)
      _ = e (b * a) := (e.map_mul b a).symm)

/-- If two subgroups are normal in a common overgroup and have trivial
intersection, then their join is isomorphic to their direct product. -/
public noncomputable def subgroup_sup_equiv_prod_of_disjoint_of_normalIn
    {G : Type u} [Group G]
    (C H K : Subgroup G)
    (hHnorm : IsNormalIn H C) (hKnorm : IsNormalIn K C)
    (hdisj : H ⊓ K = ⊥) :
    ↥(H ⊔ K) ≃* (↥H) × (↥K) := by
  classical
  have hCnormH : C ≤ Subgroup.normalizer (H : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hHnorm.2 c hc x hx
    · intro hx
      have hc' : c⁻¹ ∈ C := C.inv_mem hc
      have hback := hHnorm.2 c⁻¹ hc' (c * x * c⁻¹) hx
      have hEq : c⁻¹ * (c * x * c⁻¹) * c = x := by group
      simpa [hEq] using hback
  have hCnormK : C ≤ Subgroup.normalizer (K : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hKnorm.2 c hc x hx
    · intro hx
      have hc' : c⁻¹ ∈ C := C.inv_mem hc
      have hback := hKnorm.2 c⁻¹ hc' (c * x * c⁻¹) hx
      have hEq : c⁻¹ * (c * x * c⁻¹) * c = x := by group
      simpa [hEq] using hback
  haveI hHc : (H.subgroupOf C).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := C) (N := H) hCnormH
  haveI hKc : (K.subgroupOf C).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := C) (N := K) hCnormK
  have hdisjC : H.subgroupOf C ⊓ K.subgroupOf C = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxG : (x : G) ∈ H ⊓ K :=
      Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hx).1,
          Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hx).2⟩
    have hbot : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [hdisj] at hxG
      exact hxG
    apply Subtype.ext
    exact Subgroup.mem_bot.mp hbot
  have hdisjC' : Disjoint (H.subgroupOf C) (K.subgroupOf C) :=
    disjoint_iff_inf_le.mpr (le_of_eq hdisjC)
  have hcomm : ∀ h k, h ∈ H → k ∈ K → Commute h k := by
    intro h k hh hk
    have hhC : h ∈ C := hHnorm.1 hh
    have hkC : k ∈ C := hKnorm.1 hk
    have hcommC := Subgroup.commute_of_normal_of_disjoint
      (H.subgroupOf C) (K.subgroupOf C) hHc hKc hdisjC'
      (⟨h, hhC⟩ : C) (⟨k, hkC⟩ : C)
      (by rw [Subgroup.mem_subgroupOf]; exact hh)
      (by rw [Subgroup.mem_subgroupOf]; exact hk)
    exact hcommC.map C.subtype
  exact subgroup_sup_equiv_prod_of_commute_of_disjoint H K hdisj hcomm

/-- If two abelian subgroups are normal in a common overgroup and have
trivial intersection, then their join is abelian. -/
public theorem subgroup_sup_isMulCommutative_of_disjoint_of_normalIn
    {G : Type u} [Group G]
    (C H K : Subgroup G)
    (hHnorm : IsNormalIn H C) (hKnorm : IsNormalIn K C)
    (hdisj : H ⊓ K = ⊥)
    (hHabel : IsMulCommutative (↥H)) (hKabel : IsMulCommutative (↥K)) :
    IsMulCommutative (↥(H ⊔ K)) := by
  classical
  have : IsMulCommutative (↥H) := hHabel
  have : IsMulCommutative (↥K) := hKabel
  let e := subgroup_sup_equiv_prod_of_disjoint_of_normalIn C H K
    hHnorm hKnorm hdisj
  rw [isMulCommutative_iff]
  intro a b
  exact e.injective (by
    have hprod : IsMulCommutative ((↥H) × (↥K)) := inferInstance
    calc
      e (a * b) = e a * e b := e.map_mul a b
      _ = e b * e a := (isMulCommutative_iff.mp hprod) (e a) (e b)
      _ = e (b * a) := (e.map_mul b a).symm)

/-- In the cyclic first case, `F(U)` has trivial intersection with every
conjugate by an element outside `Ĥ`. -/
public theorem firstCase_FU_inf_conj_eq_bot
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (g : G) (hg : g ∉ c.Hhat) :
    c.FU ⊓ conjugateSubgroup c.FU g = ⊥ := by
  classical
  let X : Subgroup G := c.FU ⊓ conjugateSubgroup c.FU g
  by_contra hXbot
  have hXne : X ≠ ⊥ := by simpa [X] using hXbot
  let Y : Subgroup G := conjugateSubgroup X g⁻¹
  have hYmap : conjugateSubgroup Y g = X := by
    simpa [Y] using conj_inv_then_conj_eq X g
  have hYleFU : Y ≤ c.FU := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
    have hxFU : x ∈ c.FU := (inf_le_left : X ≤ c.FU) hx
    have hxConj : x ∈ conjugateSubgroup c.FU g :=
      (inf_le_right : X ≤ conjugateSubgroup c.FU g) hx
    rcases Subgroup.mem_map.mp hxConj with ⟨f, hf, hxf⟩
    have hxf' : x = g * f * g⁻¹ := by
      simpa [conjugateSubgroup, MulAut.conj_apply] using hxf.symm
    have heq : (MulAut.conj g⁻¹).toMonoidHom x = f := by
      rw [hxf']
      simp
      group
    rw [heq]
    exact hf
  have hYne : Y ≠ ⊥ := by
    intro hYbot
    apply hXne
    rw [← hYmap]
    simp [conjugateSubgroup, hYbot]
  have hNY : Subgroup.normalizer (Y : Set G) ≤ c.Hhat :=
    hfirst.2 Y hYne hYleFU
  have hNX : Subgroup.normalizer (X : Set G) ≤
      conjugateSubgroup c.Hhat g := by
    have hmapN : conjugateSubgroup (Subgroup.normalizer (Y : Set G)) g =
        Subgroup.normalizer (X : Set G) := by
      have hYmap' : Y.map (MulAut.conj g).toMonoidHom = X := by
        simpa [conjugateSubgroup] using hYmap
      change (Subgroup.normalizer (Y : Set G)).map
          (MulAut.conj g).toMonoidHom = _
      rw [Subgroup.map_normalizer_eq_of_bijective Y (MulAut.conj g).bijective]
      rw [hYmap']
    rw [← hmapN]
    simpa [conjugateSubgroup] using
      (Subgroup.map_mono hNY (f := (MulAut.conj g).toMonoidHom))
  have hXfu : X ≤ c.FU := inf_le_left
  have hXfhat : X ≤ fittingSubgroupOf c.Hhat :=
    hXfu.trans (FU_le_fittingSubgroupOf_Hhat_of_centralizerStructure c
      (theorem_2_6 hmin c))
  exact hg (hhat_conjugate_TI_of_normalizer_control hmin c X hXne hXfhat g hNX)

/-- In the cyclic first case, every `P ≤ F(U)` has trivial intersection with
`P^g` for `g ∉ Ĥ`. -/
public theorem firstCase_P_inf_conj_eq_bot_of_not_mem_Hhat
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (P : Subgroup G) (hPfu : P ≤ c.FU)
    (g : G) (hg : g ∉ c.Hhat) :
    P ⊓ conjugateSubgroup P g = ⊥ := by
  classical
  apply le_bot_iff.mp
  intro x hx
  have hxFU : x ∈ c.FU := hPfu ((inf_le_left : P ⊓ conjugateSubgroup P g ≤ P) hx)
  have hxFUg : x ∈ conjugateSubgroup c.FU g := by
    exact (Subgroup.map_mono hPfu
      (f := (MulAut.conj g).toMonoidHom))
      ((inf_le_right : P ⊓ conjugateSubgroup P g ≤
        conjugateSubgroup P g) hx)
  have hx : x ∈ c.FU ⊓ conjugateSubgroup c.FU g :=
    Subgroup.mem_inf.mpr ⟨hxFU, hxFUg⟩
  have hbot := firstCase_FU_inf_conj_eq_bot hmin c hfirst g hg
  rw [hbot] at hx
  exact Subgroup.mem_bot.mp hx

/-- In the cyclic first case, `P ≤ F(U)` has `P·P^g ≃ P × P^g` whenever
the two factors commute. -/
public noncomputable def firstCase_join_conj_equiv_prod_of_abelian_of_commute
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (P : Subgroup G) (hPfu : P ≤ c.FU)
    (g : G) (hg : g ∉ c.Hhat)
    (hcomm : ∀ p q, p ∈ P → q ∈ conjugateSubgroup P g → Commute p q) :
    ↥(P ⊔ conjugateSubgroup P g) ≃*
      (↥P) × (↥(conjugateSubgroup P g)) := by
  exact subgroup_sup_equiv_prod_of_commute_of_disjoint P
    (conjugateSubgroup P g)
    (firstCase_P_inf_conj_eq_bot_of_not_mem_Hhat hmin c hfirst P hPfu g hg)
    hcomm

/-- In the cyclic first case, an abelian `P ≤ F(U)` has abelian
`P·P^g` whenever the two factors commute. -/
public theorem firstCase_join_conj_abelian_of_abelian_of_commute
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (P : Subgroup G) (hPfu : P ≤ c.FU)
    (g : G) (hg : g ∉ c.Hhat)
    (hPabel : IsMulCommutative (↥P))
    (hcomm : ∀ p q, p ∈ P → q ∈ conjugateSubgroup P g → Commute p q) :
    IsMulCommutative (↥(P ⊔ conjugateSubgroup P g)) := by
  have : IsMulCommutative (↥P) := hPabel
  have hPgabel : IsMulCommutative (↥(conjugateSubgroup P g)) := by
    change IsMulCommutative (↥(P.map (MulAut.conj g).toMonoidHom))
    infer_instance
  exact subgroup_sup_isMulCommutative_of_commute_of_disjoint P
    (conjugateSubgroup P g)
    (firstCase_P_inf_conj_eq_bot_of_not_mem_Hhat hmin c hfirst P hPfu g hg)
    hcomm hPabel hPgabel

/-- In the cyclic first case, `P ≤ F(U)` has `P·P^g ≃ P × P^g` when both
`P` and `P^g` are normal in a common overgroup `C` (the paper's
`C_U(t₁)`). -/
public noncomputable def firstCase_join_conj_equiv_prod_of_normalIn
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (P : Subgroup G) (hPfu : P ≤ c.FU)
    (g : G) (hg : g ∉ c.Hhat)
    (C : Subgroup G)
    (hPnorm : IsNormalIn P C)
    (hPgNorm : IsNormalIn (conjugateSubgroup P g) C) :
    ↥(P ⊔ conjugateSubgroup P g) ≃*
      (↥P) × (↥(conjugateSubgroup P g)) := by
  exact subgroup_sup_equiv_prod_of_disjoint_of_normalIn C P
    (conjugateSubgroup P g) hPnorm hPgNorm
    (firstCase_P_inf_conj_eq_bot_of_not_mem_Hhat hmin c hfirst P hPfu g hg)

/-- In the cyclic first case, an abelian `P ≤ F(U)` has abelian
`P·P^g` when both `P` and `P^g` are normal in a common overgroup
`C` (the paper's `C_U(t₁)`). -/
public theorem firstCase_join_conj_abelian_of_normalIn
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (P : Subgroup G) (hPfu : P ≤ c.FU)
    (g : G) (hg : g ∉ c.Hhat)
    (C : Subgroup G)
    (hPnorm : IsNormalIn P C)
    (hPgNorm : IsNormalIn (conjugateSubgroup P g) C)
    (hPabel : IsMulCommutative (↥P)) :
    IsMulCommutative (↥(P ⊔ conjugateSubgroup P g)) := by
  have : IsMulCommutative (↥P) := hPabel
  have hPgabel : IsMulCommutative (↥(conjugateSubgroup P g)) := by
    change IsMulCommutative (↥(P.map (MulAut.conj g).toMonoidHom))
    infer_instance
  exact subgroup_sup_isMulCommutative_of_disjoint_of_normalIn C P
    (conjugateSubgroup P g) hPnorm hPgNorm
    (firstCase_P_inf_conj_eq_bot_of_not_mem_Hhat hmin c hfirst P hPfu g hg)
    hPabel hPgabel

end CFSG.GorensteinWalter
