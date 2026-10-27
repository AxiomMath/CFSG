module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoP1Defs
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndSmall
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.SignalizerFunctorTheorem.McBride.Defs
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoVStar
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoPi
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma27Aux10
import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.KBasic
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoShapeB
import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Hom

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

theorem normal_on (N : Subgroup G) : ((t.On N).subgroupOf N).Normal := by
  classical
  let D : Subgroup G := t.Dn N
  have hDN : D ≤ N := t.Dn_le N
  let Dn : Subgroup ↥N := D.subgroupOf N
  have hDnNorm : Dn.Normal := t.normal_Dn N
  let On : Subgroup ↥N := (CFSG.pPrimeCore 3 ↥Dn).map Dn.subtype
  have hOnNormal : On.Normal := by
    haveI : Dn.Normal := hDnNorm
    have hc : (CFSG.pPrimeCore 3 ↥Dn).Characteristic := CFSG.pPrimeCore_characteristic
    haveI := hc
    exact ConjAct.normal_of_characteristic_of_normal (H := Dn)
  have hOnMap : On.map N.subtype = t.On N := by
    let e : ↥Dn ≃* ↥D := Subgroup.subgroupOfEquivOfLe hDN
    have hcomp : N.subtype.comp Dn.subtype = D.subtype.comp e.toMonoidHom := by
      ext y
      exact Subgroup.subgroupOfEquivOfLe_apply_coe hDN y
    show ((CFSG.pPrimeCore 3 ↥Dn).map Dn.subtype).map N.subtype = t.On N
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map,
      CFSG.pPrimeCore_map_iso (p := 3) (f := e)]
    rfl
  have hOnEq : On = (t.On N).subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [hOnMap, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr ((t.On_le_Dn N).trans hDN)]
  exact hOnEq ▸ hOnNormal

theorem le_normalizer_sol_on (N : Subgroup G) :
    N ≤ Subgroup.normalizer (sol (t.On N) : Set G) := by
  classical
  have hON : t.On N ≤ N := (t.On_le_Dn N).trans (t.Dn_le N)
  rw [Subgroup.le_normalizer_iff]
  intro n hn s hs
  have hnO : n ∈ Subgroup.normalizer (t.On N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hON).mp (t.normal_on N) hn
  have hs' : s ∈ (CFSG.solvableRadical ↥(t.On N)).map (t.On N).subtype := hs
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hs'
  let φ : MulAut ↥(t.On N) := Subgroup.normalizerMonoidHom (t.On N) ⟨n, hnO⟩
  have hφ : ∀ x : ↥(t.On N), ((φ x : ↥(t.On N)) : G) = n * (x : G) * n⁻¹ :=
    Subgroup.normalizerMonoidHom_apply_apply_coe (t.On N) ⟨n, hnO⟩
  have hmem : φ r ∈ CFSG.solvableRadical ↥(t.On N) := by
    have hchar : (CFSG.solvableRadical ↥(t.On N)).Characteristic := inferInstance
    have hmap := (Subgroup.characteristic_iff_map_eq.mp hchar) φ
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨r, hr, rfl⟩
  exact Subgroup.mem_map.mpr ⟨φ r, hmem, hφ r⟩

variable {N : Subgroup G} {O S : Subgroup G} {Γ : Type*} [Group Γ] [Finite Γ]
  {π : ↥N →* Γ} {Ō Ā : Subgroup Γ}

private lemma sol_quotient_eq_bot (hS : S = sol O) (hSO : S ≤ O) (hON : O ≤ N)
    (hŌ : Ō = (O.subgroupOf N).map π) (hker : π.ker = S.subgroupOf N) : sol Ō = ⊥ := by
  classical
  let fO : ↥O →* Γ := π.comp (Subgroup.inclusion hON)
  have hfO_range : fO.range = Ō := by
    rw [hŌ]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact Subgroup.mem_map.mpr ⟨⟨(x : G), hON x.2⟩, x.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩, rfl⟩
  let g : ↥O →* ↥Ō := fO.codRestrict Ō (fun x => hfO_range ▸ MonoidHom.mem_range.mpr ⟨x, rfl⟩)
  have hg_surj : Function.Surjective g := by
    rintro ⟨y, hy⟩
    rw [← hfO_range] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  have hgker : g.ker = S.subgroupOf O := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : fO x = 1 := congrArg Subtype.val hx
      have h1' : π (Subgroup.inclusion hON x) = 1 := h1
      have h2 : Subgroup.inclusion hON x ∈ S.subgroupOf N :=
        hker ▸ MonoidHom.mem_ker.mpr h1'
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp h2)
    · intro hx
      have hx' : ((Subgroup.inclusion hON x : ↥N) : G) ∈ S :=
        Subgroup.mem_subgroupOf.mp hx
      have h2 : Subgroup.inclusion hON x ∈ S.subgroupOf N :=
        Subgroup.mem_subgroupOf.mpr hx'
      have h2' : Subgroup.inclusion hON x ∈ π.ker := hker ▸ h2
      have h3 : fO x = 1 := MonoidHom.mem_ker.mp h2'
      exact Subtype.ext h3
  have hk : Group.IsSolvable ↥g.ker := by
    have h1 : Group.IsSolvable ↥S := hS ▸ isSolvable_sol O
    have h2 : Group.IsSolvable ↥(S.subgroupOf O) :=
      CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hSO).symm
    rwa [hgker]
  have hmap := CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.map_solvableRadical
    hg_surj hk
  rw [sol_eq_bot_iff, ← hmap, ← subgroupOf_sol O, ← hS, Subgroup.map_eq_bot_iff]
  exact le_of_eq hgker.symm

private lemma range_comp_inclusion {U : Subgroup G} {L : Subgroup Γ}
    (hUN : U ≤ N) (hπU : (U.subgroupOf N).map π = L) :
    (π.comp (Subgroup.inclusion hUN)).range = L := by
  have hincl : (⊤ : Subgroup ↥U).map (Subgroup.inclusion hUN) = U.subgroupOf N := by
    rw [Subgroup.map_top]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [MonoidHom.range_eq_map, ← Subgroup.map_map, hincl, hπU]

private lemma le_normalizer_image_of_invariant {U : Subgroup G} {X : Subgroup ↥U}
    (hĀ : Ā = (t.Ky.subgroupOf N).map π) (hUN : U ≤ N) (hKN : t.Ky ≤ N)
    (hUK : t.Ky ≤ Subgroup.normalizer (U : Set G))
    (hX : ∀ k (hk : k ∈ t.Ky) (x : ↥U), x ∈ X →
      (Subgroup.normalizerMonoidHom U ⟨k, hUK hk⟩) x ∈ X) :
    Ā ≤ Subgroup.normalizer
      ((X.map (π.comp (Subgroup.inclusion hUN)) : Subgroup Γ) : Set Γ) := by
  rw [hĀ] at *
  rw [Subgroup.le_normalizer_iff]
  rintro a ⟨k, hk, rfl⟩ y hy
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
  have hkK : (k : G) ∈ t.Ky := Subgroup.mem_subgroupOf.mp hk
  set φ := Subgroup.normalizerMonoidHom U ⟨(k : G), hUK hkK⟩ with hφ
  refine Subgroup.mem_map.mpr ⟨φ w, hX k hkK w hw, ?_⟩
  show π (Subgroup.inclusion hUN (φ w)) =
    π k * π (Subgroup.inclusion hUN w) * (π k)⁻¹
  have heq : Subgroup.inclusion hUN (φ w) =
      ⟨(k : G), hKN hkK⟩ * Subgroup.inclusion hUN w * ⟨(k : G), hKN hkK⟩⁻¹ := by
    apply Subtype.ext
    show ((φ w : ↥U) : G) = (k : G) * (w : G) * (k : G)⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  rw [heq, map_mul, map_mul, map_inv]

private lemma ky_le_normalizer_U {U : Subgroup G} {L : Subgroup Γ}
    (hĀ : Ā = (t.Ky.subgroupOf N).map π) (hUN : U ≤ N) (hKN : t.Ky ≤ N)
    (hAS : CFSG.SignalizerFunctorTheorem.Nonsolvable.IsASimple Ā L)
    (hUL : U.subgroupOf N = L.comap π) : t.Ky ≤ Subgroup.normalizer (U : Set G) := by
  rw [hĀ] at hAS
  rw [Subgroup.le_normalizer_iff]
  intro k hk x hx
  have hxN : (x : G) ∈ N := hUN hx
  have hkA : π ⟨k, hKN hk⟩ ∈ (t.Ky.subgroupOf N).map π :=
    Subgroup.mem_map.mpr ⟨⟨k, hKN hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  have hxL : π ⟨x, hxN⟩ ∈ L := by
    have h : (⟨x, hxN⟩ : ↥N) ∈ L.comap π := by
      rw [← hUL]
      exact Subgroup.mem_subgroupOf.mpr hx
    exact h
  have hconjL : π ⟨k, hKN hk⟩ * π ⟨x, hxN⟩ * (π ⟨k, hKN hk⟩)⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (hAS.1 hkA) (π ⟨x, hxN⟩)).mp hxL
  have hmem : (⟨k, hKN hk⟩ * ⟨x, hxN⟩ * (⟨k, hKN hk⟩ : ↥N)⁻¹) ∈ L.comap π := by
    rw [Subgroup.mem_comap]
    rw [show π (⟨k, hKN hk⟩ * ⟨x, hxN⟩ * (⟨k, hKN hk⟩ : ↥N)⁻¹) =
      π ⟨k, hKN hk⟩ * π ⟨x, hxN⟩ * (π ⟨k, hKN hk⟩)⁻¹ from by rw [map_mul, map_mul, map_inv]]
    exact hconjL
  rw [← hUL] at hmem
  have hxU : ((⟨k, hKN hk⟩ * ⟨x, hxN⟩ * (⟨k, hKN hk⟩ : ↥N)⁻¹ : ↥N) : G) ∈ U :=
    Subgroup.mem_subgroupOf.mp hmem
  simpa using hxU

private lemma S_maximal {U X : Subgroup G} {L : Subgroup Γ}
    (hĀ : Ā = (t.Ky.subgroupOf N).map π) (hUN : U ≤ N) (hKN : t.Ky ≤ N)
    (hUK : t.Ky ≤ Subgroup.normalizer (U : Set G))
    (hπU : (U.subgroupOf N).map π = L) (hker : π.ker = S.subgroupOf N)
    (hAS : CFSG.SignalizerFunctorTheorem.Nonsolvable.IsASimple Ā L)
    (hSX : S ≤ X) (hXU : X ≤ U) (hUX : U ≤ Subgroup.normalizer (X : Set G))
    (hKX : t.Ky ≤ Subgroup.normalizer (X : Set G)) (hXne : X ≠ U) : X = S := by
  classical
  let fU : ↥U →* Γ := π.comp (Subgroup.inclusion hUN)
  have hfU_range : fU.range = L := range_comp_inclusion hUN hπU
  let X₀ : Subgroup ↥U := X.subgroupOf U
  have hX₀normal : X₀.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXU).mpr hUX
  have hXbar_le : X₀.map fU ≤ L := hfU_range ▸ Subgroup.map_le_range fU X₀
  have hXbar_normal : ((X₀.map fU).subgroupOf L).Normal := by
    rw [← hfU_range]
    exact CFSG.Semidihedral.LocalPrincipalCompatibility.normal_image_in_range fU X₀
  have hXbar_inv : Ā ≤ Subgroup.normalizer ((X₀.map fU : Subgroup Γ) : Set Γ) := by
    refine t.le_normalizer_image_of_invariant hĀ hUN hKN hUK ?_
    intro k hk x hx
    have hconj : (Subgroup.normalizerMonoidHom U ⟨(k : G), hUK hk⟩) x =
        ⟨(k : G) * (x : G) * (k : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hUK hk) (x : G)).mp x.2⟩ := Subtype.ext rfl
    rw [hconj]
    exact Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp (hKX hk) (x : G)).mp
      (Subgroup.mem_subgroupOf.mp hx))
  rcases hAS.2.2 (X₀.map fU) hXbar_le hXbar_normal hXbar_inv with hbot | htop
  · refine le_antisymm ?_ hSX
    intro x hx
    have hxU : x ∈ U := hXU hx
    have hx₀ : (⟨x, hxU⟩ : ↥U) ∈ X₀ := Subgroup.mem_subgroupOf.mpr hx
    have h1 : fU ⟨x, hxU⟩ = 1 :=
      MonoidHom.mem_ker.mp ((Subgroup.map_eq_bot_iff X₀).mp hbot hx₀)
    have h1' : π (Subgroup.inclusion hUN ⟨x, hxU⟩) = 1 := h1
    exact Subgroup.mem_subgroupOf.mp (hker ▸ MonoidHom.mem_ker.mpr h1')
  · exfalso
    apply hXne
    refine le_antisymm hXU ?_
    intro u hu
    have huImg : fU ⟨u, hu⟩ ∈ X₀.map fU := by
      rw [htop, ← hfU_range]
      exact MonoidHom.mem_range.mpr ⟨⟨u, hu⟩, rfl⟩
    obtain ⟨w, hw, hweq⟩ := Subgroup.mem_map.mp huImg
    have hwX : (w : G) ∈ X := Subgroup.mem_subgroupOf.mp hw
    have hdiff : (w : ↥U)⁻¹ * ⟨u, hu⟩ ∈ S.subgroupOf U := by
      have h1 : fU ((w : ↥U)⁻¹ * ⟨u, hu⟩) = 1 := by
        rw [map_mul, map_inv, hweq]
        group
      have h1' : π (Subgroup.inclusion hUN ((w : ↥U)⁻¹ * ⟨u, hu⟩)) = 1 := h1
      have h2 : Subgroup.inclusion hUN ((w : ↥U)⁻¹ * ⟨u, hu⟩) ∈ S.subgroupOf N :=
        hker ▸ MonoidHom.mem_ker.mpr h1'
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp h2)
    have hdiffS : (w : G)⁻¹ * u ∈ S := Subgroup.mem_subgroupOf.mp hdiff
    have heq : u = (w : G) * ((w : G)⁻¹ * u) := by group
    rw [heq]
    exact X.mul_mem hwX (hSX hdiffS)

private lemma commutator_U_not_le {U : Subgroup G} {L : Subgroup Γ}
    (hUN : U ≤ N) (hπU : (U.subgroupOf N).map π = L) (hker : π.ker = S.subgroupOf N)
    (hAS : CFSG.SignalizerFunctorTheorem.Nonsolvable.IsASimple Ā L) : ¬ ⁅U, U⁆ ≤ S := by
  intro hc
  have hUU : ⁅U, U⁆ ≤ U := Subgroup.commutator_le.mpr fun x hx y hy =>
    U.mul_mem (U.mul_mem (U.mul_mem hx hy) (U.inv_mem hx)) (U.inv_mem hy)
  have hsub : ⁅U.subgroupOf N, U.subgroupOf N⁆ = (⁅U, U⁆).subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hUN,
      Subgroup.map_subgroupOf_eq_of_le (hUU.trans hUN)]
  have h2 : ⁅U.subgroupOf N, U.subgroupOf N⁆ ≤ S.subgroupOf N := by
    rw [hsub]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hc (Subgroup.mem_subgroupOf.mp hx))
  have h3 : ⁅(U.subgroupOf N).map π, (U.subgroupOf N).map π⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff]
    intro x hx
    exact MonoidHom.mem_ker.mp (hker ▸ h2 hx)
  have h4 : ⁅L, L⁆ = ⊥ := by rw [← hπU]; exact h3
  obtain ⟨x, hx, y, hy, hxy⟩ := hAS.2.1
  exact hxy ((Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h4 hx)) y hy).symm

private lemma U_facts {U : Subgroup G} {L : Subgroup Γ}
    (hĀ : Ā = (t.Ky.subgroupOf N).map π) (hUN : U ≤ N) (hKN : t.Ky ≤ N)
    (hUL : U.subgroupOf N = L.comap π) (hker : π.ker = S.subgroupOf N)
    (hSO : S ≤ O) (hON : O ≤ N) (hLR : L ≤ Ō) (hOŌ : Ō = (O.subgroupOf N).map π)
    (hAS : CFSG.SignalizerFunctorTheorem.Nonsolvable.IsASimple Ā L) :
    S ≤ U ∧ U ≤ O ∧ t.Ky ≤ Subgroup.normalizer (U : Set G) := by
  classical
  have hSN : S ≤ N := hSO.trans hON
  have hSNle : S.subgroupOf N ≤ O.subgroupOf N := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hSO (Subgroup.mem_subgroupOf.mp hx))
  have hU : U = (L.comap π).map N.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hUN, hUL]
  have hSU : S ≤ U := by
    rw [hU]
    intro s hs
    have hs' : (⟨s, hSN hs⟩ : ↥N) ∈ L.comap π := by
      rw [Subgroup.mem_comap]
      have h1 : π ⟨s, hSN hs⟩ = 1 := by
        rw [← MonoidHom.mem_ker, hker]
        exact Subgroup.mem_subgroupOf.mpr hs
      rw [h1]
      exact L.one_mem
    exact Subgroup.mem_map.mpr ⟨⟨s, hSN hs⟩, hs', rfl⟩
  have hUO : U ≤ O := by
    rw [hU]
    rintro x ⟨n, hn, rfl⟩
    have hπn : π n ∈ (O.subgroupOf N).map π := hOŌ ▸ hLR hn
    obtain ⟨o, ho, hoo⟩ := Subgroup.mem_map.mp hπn
    have hmem : n * o⁻¹ ∈ S.subgroupOf N := by
      rw [Subgroup.mem_subgroupOf]
      have h2 : π (n * o⁻¹) = 1 := by rw [map_mul, map_inv, hoo, mul_inv_cancel]
      exact Subgroup.mem_subgroupOf.mp (hker ▸ MonoidHom.mem_ker.mpr h2)
    have hno : ((n * o⁻¹) * o : ↥N) ∈ O.subgroupOf N :=
      (O.subgroupOf N).mul_mem (hSNle hmem) ho
    have hEq : ((n * o⁻¹) * o : ↥N) = n := by group
    rw [hEq] at hno
    exact Subgroup.mem_subgroupOf.mp hno
  exact ⟨hSU, hUO, t.ky_le_normalizer_U hĀ hUN hKN hAS hUL⟩

private lemma pCore_two_le {U : Subgroup G} {L J : Subgroup Γ}
    (hĀ : Ā = (t.Ky.subgroupOf N).map π) (hUN : U ≤ N) (hKN : t.Ky ≤ N)
    (hUK : t.Ky ≤ Subgroup.normalizer (U : Set G))
    (hπU : (U.subgroupOf N).map π = L) (hker : π.ker = S.subgroupOf N) (hSU : S ≤ U)
    (hAS : CFSG.SignalizerFunctorTheorem.Nonsolvable.IsASimple Ā L)
    (hJ : J ∈ lcal Ō) (hJleL : J ≤ L) : CFSG.Open.pCoreOf 2 U ≤ S := by
  classical
  let fU : ↥U →* Γ := π.comp (Subgroup.inclusion hUN)
  have hfU_range : fU.range = L := range_comp_inclusion hUN hπU
  let T : Subgroup ↥U := CFSG.pCore 2 ↥U
  have hTchar : T.Characteristic := inferInstance
  let Tbar : Subgroup Γ := T.map fU
  have hTbar_le : Tbar ≤ L := hfU_range ▸ Subgroup.map_le_range fU T
  have hTbar_normal : (Tbar.subgroupOf L).Normal := by
    rw [← hfU_range]
    exact CFSG.Semidihedral.LocalPrincipalCompatibility.normal_image_in_range fU T
  have hTbar_inv : Ā ≤ Subgroup.normalizer (Tbar : Set Γ) := by
    refine t.le_normalizer_image_of_invariant hĀ hUN hKN hUK ?_
    intro k hk x hx
    have hchar := Subgroup.characteristic_iff_map_eq.mp hTchar
      (Subgroup.normalizerMonoidHom U ⟨k, hUK hk⟩)
    rw [← hchar]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hT2 : IsPGroup 2 ↥Tbar := (CFSG.pCore_isPGroup (p := 2) (G := ↥U)).map fU
  obtain ⟨-, -, hJsimple, hJnc⟩ := mem_lcal_iff.mp hJ
  have hTbar_ne_top : Tbar ≠ L := by
    intro h
    rw [h] at hT2
    have hJ2 : IsPGroup 2 ↥J := hT2.to_le hJleL
    haveI : Group.IsNilpotent ↥J := IsPGroup.isNilpotent hJ2
    haveI : Group.IsSolvable ↥J := inferInstance
    haveI : IsSimpleGroup ↥J := hJsimple
    exact hJnc (isMulCommutative_iff.mpr
      (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance))
  have hTbar_bot : Tbar = ⊥ := by
    rcases hAS.2.2 Tbar hTbar_le hTbar_normal hTbar_inv with h | h
    · exact h
    · exact absurd h hTbar_ne_top
  have hTle : T ≤ S.subgroupOf U := by
    intro x hx
    have h1 : fU x = 1 := MonoidHom.mem_ker.mp ((Subgroup.map_eq_bot_iff T).mp hTbar_bot hx)
    have h1' : π (Subgroup.inclusion hUN x) = 1 := h1
    have h2 : Subgroup.inclusion hUN x ∈ S.subgroupOf N :=
      hker ▸ MonoidHom.mem_ker.mpr h1'
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp h2)
  rw [CFSG.openPCoreOf_eq_map_pCore]
  have h3 : (S.subgroupOf U).map U.subtype = S := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSU]
  rw [← h3]
  exact Subgroup.map_mono hTle

private lemma commutator_U_Ky_le {U : Subgroup G}
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hUM : U ≤ c.S.M) (hUK : t.Ky ≤ Subgroup.normalizer (U : Set G))
    (hU3 : ¬ 3 ∣ Nat.card U) (hO2 : CFSG.Open.pCoreOf 2 U ≤ S) : ⁅U, t.Ky⁆ ≤ S := by
  have h1 := t.commutator_Ky_le_inf_N hK32 hGA hSp hUM hUK hU3
  have hQle : U ⊓ (c.L ⊓ t.d.N) ≤ CFSG.Open.pCoreOf 2 U := by
    rw [CFSG.openPCoreOf_eq_map_pCore]
    have hnorm : ((U ⊓ (c.L ⊓ t.d.N)).subgroupOf U).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer
        (inf_le_left : U ⊓ (c.L ⊓ t.d.N) ≤ U)]
      exact fun u hu => Subgroup.inf_normalizer_le_normalizer_inf
        (Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer hu, t.le_normalizer_inf_N (hUM hu)⟩)
    have hp : IsPGroup 2 ↥((U ⊓ (c.L ⊓ t.d.N)).subgroupOf U) :=
      (t.d.N_isPGroup.to_le (inf_le_right.trans inf_le_right)).comap_subtype
    have h4 : (U ⊓ (c.L ⊓ t.d.N)).subgroupOf U ≤ CFSG.pCore 2 ↥U :=
      le_sSup ⟨hnorm, hp⟩
    have hmapinf : ((U ⊓ (c.L ⊓ t.d.N)).subgroupOf U).map U.subtype =
        U ⊓ (c.L ⊓ t.d.N) := by
      rw [Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.mpr inf_le_left
    calc U ⊓ (c.L ⊓ t.d.N) = ((U ⊓ (c.L ⊓ t.d.N)).subgroupOf U).map U.subtype :=
          hmapinf.symm
      _ ≤ _ := Subgroup.map_mono h4
  exact h1.trans (hQle.trans hO2)

private lemma commutator_L_A_eq_bot {U : Subgroup G} {L : Subgroup Γ}
    (hUN : U ≤ N) (hKN : t.Ky ≤ N) (hĀ : Ā = (t.Ky.subgroupOf N).map π)
    (hπU : (U.subgroupOf N).map π = L) (hker : π.ker = S.subgroupOf N)
    (hcommU : ⁅U, t.Ky⁆ ≤ S) : ⁅L, Ā⁆ = ⊥ := by
  have hUKyN : ⁅U, t.Ky⁆ ≤ N := Subgroup.commutator_le.mpr fun x hx y hy =>
    N.mul_mem (N.mul_mem (N.mul_mem (hUN hx) (hKN hy)) (N.inv_mem (hUN hx)))
      (N.inv_mem (hKN hy))
  have hsub : ⁅U.subgroupOf N, t.Ky.subgroupOf N⁆ = (⁅U, t.Ky⁆).subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hUN,
      Subgroup.map_subgroupOf_eq_of_le hKN, Subgroup.map_subgroupOf_eq_of_le hUKyN]
  rw [hĀ]
  calc ⁅L, (t.Ky.subgroupOf N).map π⁆ =
        ⁅(U.subgroupOf N).map π, (t.Ky.subgroupOf N).map π⁆ := by rw [hπU]
    _ = (⁅U.subgroupOf N, t.Ky.subgroupOf N⁆).map π := by rw [Subgroup.map_commutator]
    _ = ((⁅U, t.Ky⁆).subgroupOf N).map π := by rw [hsub]
    _ = ⊥ := by
        rw [Subgroup.map_eq_bot_iff]
        intro x hx
        exact MonoidHom.mem_ker.mp (hker ▸
          Subgroup.mem_subgroupOf.mpr (hcommU (Subgroup.mem_subgroupOf.mp hx)))

private lemma zbar_mem_centralizer_of_mem_lcal
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M)
    (hN : N ≠ ⊤) (hKN : t.Ky ≤ N) (hSM : S ≤ c.S.M) (hNS : N ≤ Subgroup.normalizer (S : Set G))
    (hSO : S ≤ O) (hON : O ≤ N) (h3O : ¬ 3 ∣ Nat.card O)
    (hOŌ : Ō = (O.subgroupOf N).map π) (hĀ : Ā = (t.Ky.subgroupOf N).map π)
    (hĀŌ : Ā ≤ Subgroup.normalizer (Ō : Set Γ)) (hker : π.ker = S.subgroupOf N)
    (hπ_range : π.range = ⊤) {zbar : Γ} (hzbar_mem : zbar ∈ Ā) {J : Subgroup Γ}
    (hJ : J ∈ lcal Ō) : zbar ∈ Subgroup.centralizer (J : Set Γ) := by
  classical
  obtain ⟨hJle, -, -, -⟩ := mem_lcal_iff.mp hJ
  let L : Subgroup Γ := orbitClosure J Ā
  let U : Subgroup G := (L.comap π).map N.subtype
  have hconj := Nonsolv.L514.conjOrbit_subset_lcal hĀŌ hJ
  have hLdir := Nonsolv.L514.isDirectProduct_conjOrbit hĀŌ hJ
  have hAS : CFSG.SignalizerFunctorTheorem.Nonsolvable.IsASimple Ā L :=
    Near.Lemma27.isASimple_of_isDirectProduct hLdir
      (fun D hD => Near.Lemma27.simple_of_mem_lcal (hconj hD))
      ⟨J, Nonsolv.L514.self_mem_conjOrbit Ā J⟩
      (fun x hx => Nonsolv.L514.mem_normalizer_orbitClosure hx)
      (fun D hD D' hD' => Nonsolv.L514.exists_conj_of_mem_conjOrbit hD hD')
  have hLU : L ≤ Ō := Near.Lemma27.orbitClosure_le_of_le_of_normalizes hJle hĀŌ
  have hJleL : J ≤ L := le_orbitClosure J Ā
  have hUN : U ≤ N := Subgroup.map_subtype_le _
  have hUL : U.subgroupOf N = L.comap π :=
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
  have hπU : (U.subgroupOf N).map π = L := by
    rw [hUL]
    exact Subgroup.map_comap_eq_self (by rw [hπ_range]; exact le_top)
  obtain ⟨hSU, hUO, hUK⟩ := t.U_facts hĀ hUN hKN hUL hker hSO hON hLU hOŌ hAS
  have hU3 : ¬ 3 ∣ Nat.card U := fun h => h3O (h.trans (Subgroup.card_dvd_of_le hUO))
  have hne : U ⊔ t.Ky ≠ ⊤ := fun h => hN (top_le_iff.mp (h ▸ sup_le hUN hKN))
  have hcomm : ¬ ⁅U, U⁆ ≤ S := commutator_U_not_le hUN hπU hker hAS
  have hUU : ⁅U, U⁆ ≤ U := Subgroup.commutator_le.mpr fun x hx y hy =>
    U.mul_mem (U.mul_mem (U.mul_mem hx hy) (U.inv_mem hx)) (U.inv_mem hy)
  have hSUne : S ≠ U := fun h => hcomm (h.symm ▸ hUU)
  have hSmax : ∀ X : Subgroup G, S ≤ X → X ≤ U → U ≤ Subgroup.normalizer (X : Set G) →
      t.Ky ≤ Subgroup.normalizer (X : Set G) → X ≠ U → X = S :=
    fun X hSX hXU hUX hKX hXne =>
      t.S_maximal hĀ hUN hKN hUK hπU hker hAS hSX hXU hUX hKX hXne
  have hUM : U ≤ c.S.M := by
    exact (t.le_inf_sup_of_commutator_not_le hK32 hGA hSp hSch hZ hU3 hne hUK hSU hSUne
      (hUN.trans hNS) (hKN.trans hNS) hSmax hcomm).trans (sup_le inf_le_right hSM)
  have hO2 : CFSG.Open.pCoreOf 2 U ≤ S :=
    t.pCore_two_le hĀ hUN hKN hUK hπU hker hSU hAS hJ hJleL
  have hcommU : ⁅U, t.Ky⁆ ≤ S := t.commutator_U_Ky_le hK32 hGA hSp hUM hUK hU3 hO2
  have hLcomm : ⁅L, Ā⁆ = ⊥ := t.commutator_L_A_eq_bot hUN hKN hĀ hπU hker hcommU
  have hLcent : L ≤ Subgroup.centralizer (Ā : Set Γ) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hLcomm
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  exact (Subgroup.mem_centralizer_iff.mp (hLcent (hJleL hj)) zbar hzbar_mem).symm

private lemma kOf_normal {X : Subgroup Γ} (hX : X.Normal) : (kOf X).Normal := by
  have h1 : (⊤ : Subgroup Γ) ≤ Subgroup.normalizer (X : Set Γ) :=
    (Subgroup.normalizer_eq_top X).ge
  have h2 : (⊤ : Subgroup Γ) ≤ Subgroup.normalizer (kOf X : Set Γ) :=
    Nonsolv.le_normalizer_kOf_of_le_normalizer h1
  exact ⟨fun x hx g => (Subgroup.mem_normalizer_iff.mp (h2 (Subgroup.mem_top g)) x).mp hx⟩

private lemma zbar_mem_centralizer_kOf {zbar : Γ}
    (hZbar : ∀ J ∈ lcal Ō, zbar ∈ Subgroup.centralizer (J : Set Γ)) (hsolŌ : sol Ō = ⊥) :
    zbar ∈ Subgroup.centralizer (kOf Ō : Set Γ) := by
  have hK := (isDirectProduct_lcal_kOf hsolŌ).sSup_eq
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 : kOf Ō ≤ Subgroup.centralizer ({zbar} : Set Γ) := by
    rw [← hK]
    refine sSup_le fun J hJ y hy => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (hZbar J hJ) y hy
  exact Subgroup.mem_centralizer_singleton_iff.mp (h1 hx)

private lemma Ō_eq_bot {O : Subgroup G} {zbar : Γ} (hŌNormal : Ō.Normal)
    (hZbar : ∀ J ∈ lcal Ō, zbar ∈ Subgroup.centralizer (J : Set Γ))
    (hsolŌ : sol Ō = ⊥) (hOŌ : Ō = (O.subgroupOf N).map π) (hOD : O ≤ t.Dn N)
    (hgen : (t.Z.subgroupOf N).map π = Subgroup.zpowers zbar)
    (hsurj : Function.Surjective π) : Ō = ⊥ := by
  classical
  have hkOf_cent : zbar ∈ Subgroup.centralizer (kOf Ō : Set Γ) :=
    zbar_mem_centralizer_kOf hZbar hsolŌ
  have hkOfNormal : (kOf Ō).Normal := kOf_normal hŌNormal
  have hCnormal : (Subgroup.centralizer (kOf Ō : Set Γ)).Normal := normal_centralizer
  have hDnormal : (t.Dn N).subgroupOf N =
      Subgroup.normalClosure (t.Z.subgroupOf N : Set ↥N) := by
    show ((Subgroup.normalClosure (t.Z.subgroupOf N : Set ↥N)).map N.subtype).comap N.subtype = _
    rw [Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
  have hDbar : ∀ x ∈ (Subgroup.normalClosure ((t.Z.subgroupOf N).map π : Set Γ)),
      x ∈ Subgroup.centralizer (kOf Ō : Set Γ) := by
    intro x hx
    rw [hgen] at hx
    haveI : (Subgroup.centralizer (kOf Ō : Set Γ)).Normal := hCnormal
    have hle : Subgroup.normalClosure ((Subgroup.zpowers zbar : Subgroup Γ) : Set Γ) ≤
        Subgroup.centralizer (kOf Ō : Set Γ) :=
      Subgroup.normalClosure_le_normal (by
        intro w hw
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        exact Subgroup.zpow_mem _ hkOf_cent n)
    exact hle hx
  have hŌle : Ō ≤ Subgroup.centralizer (kOf Ō : Set Γ) := by
    intro x hx
    have h1 : O.subgroupOf N ≤ (t.Dn N).subgroupOf N := fun y hy =>
      Subgroup.mem_subgroupOf.mpr (hOD (Subgroup.mem_subgroupOf.mp hy))
    have h2 : (O.subgroupOf N).map π ≤ ((t.Dn N).subgroupOf N).map π := Subgroup.map_mono h1
    have h3 : ((t.Dn N).subgroupOf N).map π =
        Subgroup.normalClosure ((t.Z.subgroupOf N).map π : Set Γ) := by
      rw [hDnormal, Subgroup.map_normalClosure _ _ hsurj]
      rfl
    have h4 : x ∈ ((t.Dn N).subgroupOf N).map π := h2 (hOŌ ▸ hx)
    rw [h3] at h4
    exact hDbar x h4
  have hdisj := centralizer_kOf_eq_bot hsolŌ
  rw [eq_bot_iff]
  intro x hx
  have hxi : x ∈ Ō ⊓ Subgroup.centralizer (kOf Ō : Set Γ) :=
    Subgroup.mem_inf.mpr ⟨hx, hŌle hx⟩
  rw [hdisj] at hxi
  exact hxi

private lemma map_Ky_le_normalizer_map_On (hON : O ≤ N) (hKN : t.Ky ≤ N)
    (hONormal : (O.subgroupOf N).Normal) :
    (t.Ky.subgroupOf N).map π ≤ Subgroup.normalizer ((O.subgroupOf N).map π : Set Γ) := by
  rw [Subgroup.le_normalizer_iff]
  rintro a ⟨k, hk, rfl⟩ y ⟨o, ho, rfl⟩
  have hkO : (k : G) ∈ Subgroup.normalizer (O : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hON).mp hONormal k.2
  have hmemO : k * o * k⁻¹ ∈ O.subgroupOf N := by
    rw [Subgroup.mem_subgroupOf]
    simpa using (Subgroup.mem_normalizer_iff.mp hkO (o : G)).mp
      (Subgroup.mem_subgroupOf.mp ho)
  refine Subgroup.mem_map.mpr ⟨k * o * k⁻¹, hmemO, ?_⟩
  show π (k * o * k⁻¹) = π k * π o * (π k)⁻¹
  rw [map_mul, map_mul, map_inv]

private lemma map_zpowers_subgroupOf {z : G} (hzn : z ∈ N) (hZgen : t.Z = Subgroup.zpowers z) :
    (t.Z.subgroupOf N).map π = Subgroup.zpowers (π ⟨z, hzn⟩) := by
  have hzp : (t.Z.subgroupOf N) = Subgroup.zpowers (⟨z, hzn⟩ : ↥N) := by
    rw [hZgen]
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, Subtype.ext hn⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, congrArg Subtype.val hn⟩
  rw [hzp, MonoidHom.map_zpowers]

private lemma le_of_map_eq_bot (hbot : (O.subgroupOf N).map π = ⊥)
    (hker : π.ker = S.subgroupOf N) (hON : O ≤ N) (hSN : S ≤ N) : O ≤ S := by
  have h1 : O.subgroupOf N ≤ S.subgroupOf N := by
    have h3 := (Subgroup.map_eq_bot_iff (O.subgroupOf N)).mp hbot
    rwa [hker] at h3
  have h2 : (O.subgroupOf N).map N.subtype ≤ (S.subgroupOf N).map N.subtype :=
    Subgroup.map_mono h1
  rwa [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hON, inf_eq_left.mpr hSN] at h2

theorem On_le_sol (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) {N : Subgroup G} (hN : N ≠ ⊤)
    (hKN : t.Ky ≤ N) (hS : CFSG.SignalizerFunctorTheorem.McBride.sol (t.On N) ≤ c.S.M) :
    t.On N ≤ CFSG.SignalizerFunctorTheorem.McBride.sol (t.On N) := by
  classical
  let O : Subgroup G := t.On N
  let S : Subgroup G := sol O
  have hSO : S ≤ O := sol_le O
  have hOD : O ≤ t.Dn N := t.On_le_Dn N
  have hON : O ≤ N := hOD.trans (t.Dn_le N)
  have hSN : S ≤ N := hSO.trans hON
  have hZK : t.Z ≤ t.Ky := t.Z_le_Ky
  have h3O : ¬ 3 ∣ Nat.card O := t.not_three_dvd_card_On N
  have hONormal : (O.subgroupOf N).Normal := t.normal_on N
  have hNS : N ≤ Subgroup.normalizer (S : Set G) := t.le_normalizer_sol_on N
  let SN : Subgroup ↥N := S.subgroupOf N
  have hSNNormal : SN.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSN).mpr hNS
  letI : SN.Normal := hSNNormal
  let Γ := ↥N ⧸ SN
  let π : ↥N →* Γ := QuotientGroup.mk' SN
  let Ō : Subgroup Γ := (O.subgroupOf N).map π
  let Ā : Subgroup Γ := (t.Ky.subgroupOf N).map π
  have hŌNormal : Ō.Normal := hONormal.map π (QuotientGroup.mk'_surjective SN)
  have hker : π.ker = S.subgroupOf N := QuotientGroup.ker_mk' SN
  have hπ_range : π.range = ⊤ := MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective SN)
  have hĀŌ : Ā ≤ Subgroup.normalizer (Ō : Set Γ) :=
    t.map_Ky_le_normalizer_map_On hON hKN hONormal
  have hsolŌ : sol Ō = ⊥ :=
    sol_quotient_eq_bot (O := O) (S := S) (π := π) (Ō := Ō) rfl hSO hON rfl hker
  have hzex : ∃ z ∈ t.Z, z ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : t.Z = ⊥ := (Subgroup.eq_bot_iff_forall t.Z).mpr h
    have hcard : Nat.card t.Z = 1 := by rw [hbot]; simp
    have h3 := t.card_Z
    omega
  obtain ⟨z, hzZ, hz1⟩ := hzex
  have hzK : z ∈ t.Ky := hZK hzZ
  have hZN : t.Z ≤ N := hZK.trans hKN
  let zbar : Γ := π ⟨z, hKN hzK⟩
  have hZgen : t.Z = Subgroup.zpowers z := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzZ) ?_).symm
    rw [Nat.card_zpowers, orderOf_eq_prime (t.d.isElemAbelian_AA.2 z (t.Z_le_AA hzZ)) hz1,
      t.card_Z]
  have hzbar_mem : zbar ∈ Ā :=
    Subgroup.mem_map.mpr ⟨⟨z, hKN hzK⟩, Subgroup.mem_subgroupOf.mpr hzK, rfl⟩
  have hzbar_cent : ∀ J ∈ lcal Ō, zbar ∈ Subgroup.centralizer (J : Set Γ) :=
    fun J hJ => t.zbar_mem_centralizer_of_mem_lcal hK32 hGA hSp hSch hZ hN hKN hS hNS hSO hON
      h3O rfl rfl hĀŌ hker hπ_range hzbar_mem hJ
  have hgen : (t.Z.subgroupOf N).map π = Subgroup.zpowers zbar :=
    t.map_zpowers_subgroupOf (hZN hzZ) hZgen
  have hŌbot : Ō = ⊥ :=
    t.Ō_eq_bot (O := O) (zbar := zbar) hŌNormal hzbar_cent hsolŌ rfl hOD hgen
      (QuotientGroup.mk'_surjective SN)
  exact le_of_map_eq_bot hŌbot hker hON hSN

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
