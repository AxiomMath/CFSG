module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2D4Out
import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddBClass
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2Minus
import CFSG.LocalAnalysis.UniquenessCase.UC22D4PrimeCentRank
import CFSG.GroupTheory.PRankMapOfKerPrimeNotDvd
import CFSG.Quasithin.Vol2.Ch10SecKRRb
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinThreeMain
import CFSG.RankThree.PartTwo.Sec13.K135D1cA
import CFSG.RankThree.PartTwo.Sec13.Item13Res5ProofTools
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open CFSG.GH74.GLS.Stage2.Bender.Thm1
open CFSG.ComponentClassification
open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Vol2Native.EvenWit
open CFSG.SectionRank.ClassicalEven
open scoped MatrixGroups

private def HasPPlane (p : ℕ) (X : Type) [Group X] : Prop :=
  ∃ E : Subgroup X, IsElemAbelian p E ∧ Nat.card E = p ^ 2

private theorem hasPPlane_isComponentProperty (p : ℕ) : IsComponentProperty (HasPPlane p) := by
  refine ⟨?_⟩
  intro X Y _ _ e h
  obtain ⟨E, hE, hcard⟩ := h
  refine ⟨E.map e.toMonoidHom, CFSG.SectionRank.isElemAbelian_map hE e.toMonoidHom, ?_⟩
  rw [Subgroup.card_map_of_injective e.injective, hcard]

private theorem hasPPlane_of_rank {p : ℕ} (hp : p.Prime) {X : Type} [Group X] [Finite X]
    (h : 2 ≤ Open.pRank p (⊤ : Subgroup X)) : HasPPlane p X := by
  obtain ⟨E, -, hE, hcard⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp h
  exact ⟨E, hE, hcard⟩

private theorem radicalFree_of_noAbelianNormal {X : Type} [Group X] [Finite X]
    (h : ∀ A : Subgroup X, A.Normal → (∀ a b : A, a * b = b * a) → A = ⊥) :
    SolvableRadical.Free X := by
  intro N hN hsol
  by_contra hne
  let : N.Normal := hN
  let : Group.IsSolvable N := hsol
  obtain ⟨A, hAN, hmin⟩ := MinimalNormal.exists_le N hne
  let : A.Normal := hmin.prop.1
  let : Group.IsSolvable A :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hAN)
  let : IsMulCommutative A := MinimalNormal.commutative_of_solvable A hmin
  exact hmin.prop.2 (h A inferInstance (fun a b => mul_comm' a b))

private theorem hasPPlane_central_sl3 {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = p)
    {Q : Type} [Group Q] [Finite Q] (ρ : SL(3, F) →* Q) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center SL(3, F)) : HasPPlane p Q := by
  have hcard : Nat.card ρ.ker ≤ 3 :=
    (Nat.card_le_card_of_injective (Subgroup.inclusion hker)
      (Subgroup.inclusion_injective hker)).trans
      (CFSG.AGLEmbedding.ToralCensus.card_center_sl_three_le F)
  have hpker : ¬ p ∣ Nat.card ρ.ker := by
    intro hdvd
    have hle := Nat.le_of_dvd (Nat.card_pos : 0 < Nat.card ρ.ker) hdvd
    omega
  have hrank : 2 ≤ Open.pRank p (⊤ : Subgroup SL(3, F)) := by
    have h := uc22d4_le_pRank_of_sl3 (G := SL(3, F)) (m := 1) hp
      (by simpa using hF) (L := ⊤) (H := ⊤) le_rfl Subgroup.topEquiv
    simpa using h
  have hmap := CFSG.pRank_map_eq_of_not_dvd_card_ker ρ hρ hp hpker ⊤
  rw [Subgroup.map_top_of_surjective _ hρ] at hmap
  exact hasPPlane_of_rank hp (hmap.symm ▸ hrank)

private theorem hasPPlane_central_su3 {p : ℕ} [hp : Fact p.Prime] (hp7 : 7 ≤ p)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ 2)
    {Q : Type} [Group Q] [Finite Q] (ρ : StatedSU 3 p F →* Q)
    (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ Subgroup.center (StatedSU 3 p F)) :
    HasPPlane p Q := by
  have hcenter := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (p := p) (f := 1) (n := 3) (by simpa using hF) le_rfl (by simp; omega)).2
  rw [pow_one] at hcenter
  have hpZ : ¬ p ∣ Nat.card (Subgroup.center (StatedSU 3 p F)) := by
    rw [hcenter]
    exact CFSG.Quasithin.Vol2.Ch10.SecB.KRR.not_dvd_card_scalars
      (fun g hg => CFSG.Quasithin.Vol2.Ch10.SecB.KRR.det_eq_one_of_mem_closure
        (fun a ha => ha.1) hg) (by omega)
  have hpker : ¬ p ∣ Nat.card ρ.ker :=
    fun h => hpZ (h.trans (Subgroup.card_dvd_of_le hker))
  have hrank : 2 ≤ Open.pRank p (⊤ : Subgroup (StatedSU 3 p F)) := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact CFSG.Quasithin.Vol2.Ch10.SecB.KRR.two_le_pRank_su3_odd (by omega) hF
  have hmap := CFSG.pRank_map_eq_of_not_dvd_card_ker ρ hρ hp.out hpker ⊤
  rw [Subgroup.map_top_of_surjective _ hρ] at hmap
  exact hasPPlane_of_rank hp.out (hmap.symm ▸ hrank)

section Certificates


private theorem hasPPlane_comps_G2 {p : ℕ} [hp : Fact p.Prime] (hp7 : 7 ≤ p)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = p) :
    CompsWith (HasPPlane p) (adjointGroup .G2 F) := by
  have : CharP F p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp.out
      (k := 1) le_rfl (by simpa using hF)
  have : Finite (ModGL .G2 F) := finite_modGL
  have hF3 : 3 ≤ Nat.card F := by omega
  have : IsSimpleGroup (adjointGroup .G2 F) :=
    CFSG.Quasithin.H13.isSimpleGroup_adjointGroup_G2 hF3
  have hq := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple
    (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card F hF3)
  have : Group.IsPerfect (adjointGroup .G2 F) := ⟨hq.1⟩
  have hnc : ∃ a b : adjointGroup .G2 F, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact Group.IsPerfect.not_isSolvable (adjointGroup .G2 F)
      (Group.isSolvable_of_comm h)
  have hrank : 2 ≤ Open.pRank p (⊤ : Subgroup (adjointGroup .G2 F)) := by
    have h := three_mul_le_pRank_G2 (p := p) (f := 1) (by simpa using hF)
    omega
  exact compsWith_of_simple (hasPPlane_isComponentProperty p) hnc
    (hasPPlane_of_rank hp.out hrank)

theorem triD4OuterThree_exists_component_plane {X : Type} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hX : LieModel X .trialityD4 0 p 1)
    (α : MulAut X) (hα : orderOf α = 3)
    (hout : α ∉ (MulAut.conj : X →* MulAut X).range) :
    ∃ (J : Subgroup (signalizerFixedSubgroup α)) (E : Subgroup X),
      IsComponentOf J ⊤ ∧ IsSimpleGroup J ∧ ¬ Group.IsSolvable J ∧
      E ≤ J.map (signalizerFixedSubgroup α).subtype ∧
      IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card
    .D4 hp (f := 1) le_rfl (CFSG.GH74.GLS.IVK.Proofs2.Ivk47.twisted_of_lieModel_D4 hX)
  let β := MulAut.congr e α
  have hβ : orderOf β = 3 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  have hβout : β ∉ (MulAut.conj : graphFixedRootGroup .D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup .D4 K σ.toRingHom)).range := by
    rintro ⟨y, hy⟩
    apply hout
    refine ⟨e.symm y, MulEquiv.ext fun x => ?_⟩
    have h := congrArg (fun φ : MulAut (graphFixedRootGroup .D4 K σ.toRingHom) =>
      e.symm (φ (e x))) hy
    change e.symm (y * e x * y⁻¹) = e.symm (e (α (e.symm (e x)))) at h
    simpa only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.symm_apply_apply] using h
  let C := signalizerFixedSubgroup α
  have hC : C.map e.toMonoidHom = fixSub β := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change e (α (e.symm (e x))) = e x
      simpa only [MulEquiv.symm_apply_apply] using congrArg e hx
    · intro hy
      change e (α (e.symm y)) = y at hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      change α (e.symm y) = e.symm y
      apply e.injective
      simpa only [MulEquiv.apply_symm_apply] using hy
  let eC : C ≃* fixSub β :=
    (C.equivMapOfInjective e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hC)
  have hno := (CFSG.LieType.SeitzGeneration.ExcWideThree.triOdd_d4OuterThree
    p 1 hp hp2 hp3 le_rfl K hK σ hσ β hβ hβout).1
  have hfreeModel := radicalFree_of_noAbelianNormal hno
  have hfree : SolvableRadical.Free C := by
    intro N hN hsol
    let : N.Normal := hN
    let : Group.IsSolvable N := hsol
    let N' := N.map eC.toMonoidHom
    have : N'.Normal := Subgroup.Normal.map hN eC.toMonoidHom eC.surjective
    let eN : N ≃* N' := N.equivMapOfInjective eC.toMonoidHom eC.injective
    have : Group.IsSolvable N' :=
      Group.isSolvable_of_surjective (f := eN.toMonoidHom) eN.surjective
    have hbot : N' = ⊥ := hfreeModel N' inferInstance inferInstance
    apply le_antisymm _ bot_le
    intro x hx
    have hm := Subgroup.mem_map_of_mem eC.toMonoidHom hx
    change eC x ∈ N' at hm
    rw [hbot, Subgroup.mem_bot] at hm
    exact Subgroup.mem_bot.mpr (eC.injective (hm.trans eC.map_one.symm))
  have hα3 : α ^ 3 = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
  have hthree : 3 ∣ Nat.card X := by
    rw [CFSG.GH74.card_of_lieModel_trialityD4 hp2 hX]
    exact CFSG.RankThree.PartTwo.Sec13.Res5Proof.three_dvd_ordTrialityD4 _
  obtain ⟨x, hxorder, hxfix⟩ :=
    CFSG.RankThree.PartTwo.Sec13.F135Last.exists_fixed_orderOf_eq_prime
      Nat.prime_three hthree α hα3
  have hx1 : x ≠ 1 := by
    intro hx
    rw [hx, orderOf_one] at hxorder
    omega
  have : Nontrivial C := ⟨⟨⟨x, hxfix⟩, 1, fun h => hx1 (congrArg Subtype.val h)⟩⟩
  obtain ⟨J, hJ⟩ := RadicalFreeLayer.exists_component hfree
  have hJs : IsSimpleGroup J := RadicalFreeLayer.component_simple hfree J hJ
  have : Group.IsPerfect J := ⟨hJ.2.2.1⟩
  have : Nontrivial J := Quasisimple.nontrivial hJ.2.2
  have hJns : ¬ Group.IsSolvable J := Group.IsPerfect.not_isSolvable J
  have hP := hasPPlane_isComponentProperty p
  have hplus : A2PlusCompsWith (HasPPlane p) p 1 := by
    apply TriA2.a2PlusCompsWith_holds hP
    intro F _ _ hF Q _ _ ρ hρ hker
    exact hasPPlane_central_sl3 hp hp7 (by simpa using hF) ρ hρ hker
  have hminus : A2MinusCompsWith (HasPPlane p) p 1 := by
    apply TriA2.a2MinusCompsWith_holds hP
    intro F _ _ hF Q _ _ ρ hρ hker
    have : Fact (p ^ 1).Prime := ⟨by simpa only [pow_one] using hp⟩
    simpa only [pow_one] using hasPPlane_central_su3 (p := p ^ 1)
      (by simpa only [pow_one] using hp7) hF ρ hρ hker
  have hG2 : ∀ {F : Type} [Field F] [Finite F], Nat.card F = p ^ 1 →
      CompsWith (HasPPlane p) (adjointGroup .G2 F) :=
    fun {_} _ _ hF => hasPPlane_comps_G2 hp7 (by simpa using hF)
  have hβ3 : β ^ 3 = 1 := by rw [← hβ]; exact pow_orderOf_eq_one β
  have hmodel : CompsWith (HasPPlane p)
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) := by
    have hmod : p % 3 ≠ 0 := by
      intro h
      have hdiv : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
      exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 hdiv).symm
    rcases (show p % 3 = 1 ∨ p % 3 = 2 from by omega) with hq | hq
    · exact compsWith_outer_three_odd_one hP hplus hG2 (by omega) le_rfl
        (by simpa using hq) hK σ hσ β hβ3 hβout
    · exact compsWith_outer_three_odd_two hP hminus hG2 (by omega) le_rfl
        (by simpa using hq) hK σ hσ β hβ3 hβout
  have hcomps : CompsWith (HasPPlane p) C := CompsWith.of_mulEquiv hP
    (eC.trans (MulEquiv.subgroupCongr
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual.fixSub_eq_fixSubgroup β)))
    hmodel
  obtain ⟨E₀, hE₀, hE₀card⟩ := hcomps J hJ
  let ι : J →* X := C.subtype.comp J.subtype
  have hι : Function.Injective ι := C.subtype_injective.comp J.subtype_injective
  refine ⟨J, E₀.map ι, hJ, hJs, hJns, ?_,
    CFSG.SectionRank.isElemAbelian_map hE₀ ι, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact Subgroup.mem_map.mpr ⟨(y : C), y.2, rfl⟩
  · rw [Subgroup.card_map_of_injective hι, hE₀card]

theorem triD4OuterThreeSection_holds : TriD4OuterThreeSection := by
  intro X _ _ p hp hp7 hX α hα hout
  obtain ⟨J, E, hJ, hJs, hJns, hEJ, -, hEcard⟩ :=
    triD4OuterThree_exists_component_plane hp hp7 hX α hα hout
  let C := signalizerFixedSubgroup α
  let Y := J.map C.subtype
  let eJ : J ≃* Y := J.equivMapOfInjective C.subtype C.subtype_injective
  refine ⟨Y, Subgroup.map_subtype_le J, J, inferInstance, hJs, hJns,
    eJ.symm.toMonoidHom, eJ.symm.surjective, ?_⟩
  have hpY : p ∣ Nat.card Y :=
    (show p ∣ Nat.card E from hEcard ▸ dvd_pow_self p (by norm_num)).trans
      (Subgroup.card_dvd_of_le hEJ)
  rwa [← Nat.card_congr eJ.toEquiv] at hpY

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.UC22
