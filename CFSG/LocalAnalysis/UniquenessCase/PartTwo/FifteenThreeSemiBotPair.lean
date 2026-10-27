module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeSemiBotFit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeSemiBotLayer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

section Abstract

variable {A : Type*} [Group A]

private theorem s15_semiBot_conj_comp (g h : A) :
    (MulAut.conj g).toMonoidHom.comp (MulAut.conj h).toMonoidHom =
      (MulAut.conj (g * h)).toMonoidHom := by
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

private theorem s15_semiBot_conj_one :
    (MulAut.conj (1 : A)).toMonoidHom = MonoidHom.id A := by
  ext x
  simp

private theorem s15_semiBot_isComponentOf_map_conj_of_mem_normalizer {X : Type*} [Group X]
    {J K : Subgroup X} (hJ : IsComponentOf J K) {g : X}
    (hg : g ∈ normalizer (K : Set X)) :
    IsComponentOf (J.map (MulAut.conj g).toMonoidHom) K := by
  have hK : K.map (MulAut.conj g).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 hg
  refine ⟨?_, ?_, ?_⟩
  · rw [← hK]
    exact Subgroup.map_mono hJ.1
  · have h := CFSG.ComponentClassification.Components.chain_map
      (MulAut.conj g).toMonoidHom hJ.2.1
    rwa [hK] at h
  · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (J.equivMapOfInjective _ (MulAut.conj g).injective).symm hJ.2.2

private theorem s15_semiBot_isComponentOf_subgroupOf_top {X : Type*} [Group X]
    {J K : Subgroup X} (hJ : IsComponentOf J K) :
    IsComponentOf (J.subgroupOf K) ⊤ :=
  ⟨le_top, CFSG.Open.IsSubnormal.top_iff.mpr
      ((CFSG.Open.IsSubnormal.iff_subgroupOf hJ.1).mp hJ.2.1),
    CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (Subgroup.subgroupOfEquivOfLe hJ.1) hJ.2.2⟩

private theorem s15_semiBot_commute_of_isComponentOf_ne {X : Type*} [Group X] [Finite X]
    {A B K : Subgroup X} (hA : IsComponentOf A K) (hB : IsComponentOf B K) (hne : A ≠ B) :
    ⁅A, B⁆ = ⊥ := by
  have hA' : IsComponentOf (A.subgroupOf K) ⊤ := s15_semiBot_isComponentOf_subgroupOf_top hA
  have hB' : IsComponentOf (B.subgroupOf K) ⊤ := s15_semiBot_isComponentOf_subgroupOf_top hB
  have hne' : A.subgroupOf K ≠ B.subgroupOf K := by
    intro h
    exact hne (by
      have := Subgroup.subgroupOf_inj.mp h
      rwa [inf_eq_left.mpr hA.1, inf_eq_left.mpr hB.1] at this)
  have h := CFSG.ComponentClassification.LocalComponents.commute_of_ne
    (A.subgroupOf K) (B.subgroupOf K) hA' hB' hne'
  have hmap := congrArg (Subgroup.map K.subtype) h
  rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA.1,
    Subgroup.map_subgroupOf_eq_of_le hB.1, Subgroup.map_bot] at hmap

private theorem s15_semiBot_map_conj_ne {K₁ K₂ N : Subgroup A} (hne : K₂ ∉ conjSet K₁ N)
    {n n' : A} (hn : n ∈ N) (hn' : n' ∈ N) :
    K₁.map (MulAut.conj n).toMonoidHom ≠ K₂.map (MulAut.conj n').toMonoidHom := by
  intro heq
  apply hne
  refine ⟨n'⁻¹ * n, N.mul_mem (N.inv_mem hn') hn, ?_⟩
  have h := congrArg (fun Z : Subgroup A => Z.map (MulAut.conj n'⁻¹).toMonoidHom) heq
  rw [Subgroup.map_map, Subgroup.map_map] at h
  rw [s15_semiBot_conj_comp, s15_semiBot_conj_comp, inv_mul_cancel,
    s15_semiBot_conj_one, Subgroup.map_id] at h
  exact h.symm

private theorem s15_semiBot_component_commutator_fittingOf {V : Type*} [CommGroup V] [Finite V]
    {H C : Subgroup (MulAut V)} (hC : IsComponentOf C H) :
    ⁅fittingOf H, C⁆ = ⊥ := by
  haveI : Nontrivial ↥C := by
    haveI : Nontrivial (↥C ⧸ Subgroup.center ↥C) := hC.2.2.2.toNontrivial
    obtain ⟨a, b, hab⟩ := exists_pair_ne (↥C ⧸ Subgroup.center ↥C)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a, b, fun h => hab (by rw [h])⟩
  have hCgw : CFSG.GorensteinWalter.IsComponentOf C H :=
    ⟨hC.1, (CFSG.Open.IsSubnormal.iff_subgroupOf hC.1).1 hC.2.1,
      ⟨inferInstance, hC.2.2.1, hC.2.2.2⟩⟩
  have h : ⁅C, CFSG.fittingSubgroupOf H⁆ = ⊥ :=
    CFSG.GorensteinWalter.component_centralizes_fittingSubgroupOf hCgw
  rw [Subgroup.commutator_comm]
  simpa only [fittingOf, CFSG.fittingSubgroupOf] using h

theorem s15_semiBot_iSup_conj_le {H K N : Subgroup A} (hKH : K ≤ H)
    (hN : N ≤ normalizer (H : Set A)) :
    (⨆ n ∈ N, K.map (MulAut.conj n).toMonoidHom) ≤ H := by
  refine iSup₂_le fun n hn => ?_
  rw [Subgroup.map_le_iff_le_comap]
  intro x hx
  rw [Subgroup.mem_comap]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact (Subgroup.mem_normalizer_iff.1 (hN hn) x).mp (hKH hx)

theorem s15_semiBot_commutator_iSup_conj_self {K N : Subgroup A} (hK : ⁅K, K⁆ = K) :
    ⁅⨆ n ∈ N, K.map (MulAut.conj n).toMonoidHom, ⨆ n ∈ N, K.map (MulAut.conj n).toMonoidHom⁆ =
      ⨆ n ∈ N, K.map (MulAut.conj n).toMonoidHom := by
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  refine iSup₂_le fun n hn => ?_
  calc K.map (MulAut.conj n).toMonoidHom
      = (⁅K, K⁆).map (MulAut.conj n).toMonoidHom := by rw [hK]
    _ = ⁅K.map (MulAut.conj n).toMonoidHom, K.map (MulAut.conj n).toMonoidHom⁆ := by
        rw [Subgroup.map_commutator]
    _ ≤ ⁅⨆ n ∈ N, K.map (MulAut.conj n).toMonoidHom,
          ⨆ n ∈ N, K.map (MulAut.conj n).toMonoidHom⁆ :=
        Subgroup.commutator_mono
          (le_iSup₂ (f := fun n (_ : n ∈ N) => K.map (MulAut.conj n).toMonoidHom) n hn)
          (le_iSup₂ (f := fun n (_ : n ∈ N) => K.map (MulAut.conj n).toMonoidHom) n hn)

private theorem s15_semiBot_map_conj_iSup_conj_le {K N : Subgroup A} {m : A} (hm : m ∈ N) :
    (⨆ n ∈ N, K.map (MulAut.conj n).toMonoidHom).map (MulAut.conj m).toMonoidHom ≤
      ⨆ n ∈ N, K.map (MulAut.conj n).toMonoidHom := by
  rw [Subgroup.map_iSup (MulAut.conj m).toMonoidHom
    (fun n : A => ⨆ (_ : n ∈ N), K.map (MulAut.conj n).toMonoidHom)]
  refine iSup_le fun n => ?_
  rw [Subgroup.map_iSup (MulAut.conj m).toMonoidHom
    (fun _ : n ∈ N => K.map (MulAut.conj n).toMonoidHom)]
  refine iSup_le fun hn => ?_
  rw [Subgroup.map_map, s15_semiBot_conj_comp]
  exact le_iSup₂ (f := fun n (_ : n ∈ N) => K.map (MulAut.conj n).toMonoidHom)
    (m * n) (N.mul_mem hm hn)

theorem s15_semiBot_conj_mem_iSup_conj {K N : Subgroup A} {m x : A} (hm : m ∈ N)
    (hx : x ∈ ⨆ n ∈ N, K.map (MulAut.conj n).toMonoidHom) :
    m * x * m⁻¹ ∈ ⨆ n ∈ N, K.map (MulAut.conj n).toMonoidHom := by
  have hmem : (MulAut.conj m).toMonoidHom x ∈
      (⨆ n ∈ N, K.map (MulAut.conj n).toMonoidHom).map (MulAut.conj m).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hx
  have h := s15_semiBot_map_conj_iSup_conj_le (K := K) (N := N) hm hmem
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h

theorem s15_semiBot_commutator_iSup_conj_eq_bot [Finite A] {H N K₁ K₂ : Subgroup A}
    (hN : N ≤ normalizer (H : Set A)) (h₁ : IsComponentOf K₁ H) (h₂ : IsComponentOf K₂ H)
    (hne : K₂ ∉ conjSet K₁ N) :
    ⁅⨆ n ∈ N, K₁.map (MulAut.conj n).toMonoidHom,
      ⨆ n ∈ N, K₂.map (MulAut.conj n).toMonoidHom⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine iSup₂_le fun n hn => ?_
  rw [Subgroup.le_centralizer_iff]
  refine iSup₂_le fun n' hn' => ?_
  rw [Subgroup.le_centralizer_iff]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (s15_semiBot_commute_of_isComponentOf_ne
      (s15_semiBot_isComponentOf_map_conj_of_mem_normalizer h₁ (hN hn))
      (s15_semiBot_isComponentOf_map_conj_of_mem_normalizer h₂ (hN hn'))
      (s15_semiBot_map_conj_ne hne hn hn'))

theorem s15_semiBot_commutator_fittingOf_iSup_conj {V : Type*} [CommGroup V] [Finite V]
    {H K N : Subgroup (MulAut V)} (hN : N ≤ normalizer (H : Set (MulAut V)))
    (hK : IsComponentOf K H) :
    ⁅fittingOf H, ⨆ n ∈ N, K.map (MulAut.conj n).toMonoidHom⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
  refine iSup₂_le fun n hn => ?_
  rw [Subgroup.le_centralizer_iff]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (s15_semiBot_component_commutator_fittingOf
      (s15_semiBot_isComponentOf_map_conj_of_mem_normalizer hK (hN hn)))

end Abstract

section Concrete

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}

theorem s15_semiBot_exists_pair_of_multi (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hmulti : ∃ K₁ K₂, IsComponentOf K₁ (barSub V₀ V h.isElemAbelian L) ∧
      IsComponentOf K₂ (barSub V₀ V h.isElemAbelian L) ∧
      K₂ ∉ conjSet K₁ (Mbar D.M V₀ V h.isElemAbelian ⊓
        normalizer ((barSub V₀ V h.isElemAbelian L : Subgroup _) : Set _))) :
    ∃ P Q : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian)),
      P ≤ barSub V₀ V h.isElemAbelian L ∧ Q ≤ barSub V₀ V h.isElemAbelian L ∧
      ⁅P, Q⁆ = ⊥ ∧ ⁅Q, Q⁆ = Q ∧
      commSub (wTil V₀ V h.isElemAbelian L) P = wTil V₀ V h.isElemAbelian L ∧
      commSub (wTil V₀ V h.isElemAbelian L) Q = wTil V₀ V h.isElemAbelian L ∧
      ∀ n ∈ Mbar D.M V₀ V h.isElemAbelian ⊓
          normalizer ((barSub V₀ V h.isElemAbelian L : Subgroup _) : Set _),
        ∀ p ∈ P, n * p * n⁻¹ ∈ P := by
  obtain ⟨K₁, K₂, hK₁, hK₂, hne⟩ := hmulti
  set N : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian)) :=
    Mbar D.M V₀ V h.isElemAbelian ⊓
      normalizer ((barSub V₀ V h.isElemAbelian L : Subgroup _) : Set _) with hNdef
  have hNn : N ≤ normalizer ((barSub V₀ V h.isElemAbelian L : Subgroup _) : Set _) := inf_le_right
  have hperf : ⁅K₂, K₂⁆ = K₂ :=
    Subgroup.isPerfect_iff.1 (Group.IsPerfect.mk hK₂.2.2.1)
  refine ⟨⨆ n ∈ N, K₁.map (MulAut.conj n).toMonoidHom,
    ⨆ n ∈ N, K₂.map (MulAut.conj n).toMonoidHom,
    s15_semiBot_iSup_conj_le hK₁.1 hNn, s15_semiBot_iSup_conj_le hK₂.1 hNn,
    s15_semiBot_commutator_iSup_conj_eq_bot hNn hK₁ hK₂ hne,
    s15_semiBot_commutator_iSup_conj_self hperf,
    s15_semiBot_commSub_wTil_classSum h1217 h hK₁,
    s15_semiBot_commSub_wTil_classSum h1217 h hK₂, ?_⟩
  intro n hn p hp
  exact s15_semiBot_conj_mem_iSup_conj hn hp

theorem s15_semiBot_exists_pair_of_mixed (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hfit : fittingOf (barSub V₀ V h.isElemAbelian L) ≠ ⊥)
    (hcomp : ∃ K, IsComponentOf K (barSub V₀ V h.isElemAbelian L)) :
    ∃ P Q : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian)),
      P ≤ barSub V₀ V h.isElemAbelian L ∧ Q ≤ barSub V₀ V h.isElemAbelian L ∧
      ⁅P, Q⁆ = ⊥ ∧ ⁅Q, Q⁆ = Q ∧
      commSub (wTil V₀ V h.isElemAbelian L) P = wTil V₀ V h.isElemAbelian L ∧
      commSub (wTil V₀ V h.isElemAbelian L) Q = wTil V₀ V h.isElemAbelian L ∧
      ∀ n ∈ Mbar D.M V₀ V h.isElemAbelian ⊓
          normalizer ((barSub V₀ V h.isElemAbelian L : Subgroup _) : Set _),
        ∀ p ∈ P, n * p * n⁻¹ ∈ P := by
  obtain ⟨K, hK⟩ := hcomp
  set N : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian)) :=
    Mbar D.M V₀ V h.isElemAbelian ⊓
      normalizer ((barSub V₀ V h.isElemAbelian L : Subgroup _) : Set _) with hNdef
  have hNn : N ≤ normalizer ((barSub V₀ V h.isElemAbelian L : Subgroup _) : Set _) := inf_le_right
  have hperf : ⁅K, K⁆ = K :=
    Subgroup.isPerfect_iff.1 (Group.IsPerfect.mk hK.2.2.1)
  refine ⟨fittingOf (barSub V₀ V h.isElemAbelian L),
    ⨆ n ∈ N, K.map (MulAut.conj n).toMonoidHom,
    fittingOf_le _, s15_semiBot_iSup_conj_le hK.1 hNn,
    s15_semiBot_commutator_fittingOf_iSup_conj hNn hK,
    s15_semiBot_commutator_iSup_conj_self hperf,
    s15_semiBot_commSub_wTil_fitting h1217 h hfit,
    s15_semiBot_commSub_wTil_classSum h1217 h hK, ?_⟩
  intro n hn p hp
  have hnL := hNn hn
  have hmap : (barSub V₀ V h.isElemAbelian L).map (MulAut.conj n).toMonoidHom =
      barSub V₀ V h.isElemAbelian L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 hnL
  have hF := s15_semiBot_fittingOf_map_conj (barSub V₀ V h.isElemAbelian L) n
  rw [hmap] at hF
  rw [hF]
  exact ⟨p, hp, by simp [MulAut.conj_apply]⟩

end Concrete

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
