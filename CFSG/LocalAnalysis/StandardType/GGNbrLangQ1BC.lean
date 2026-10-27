module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1RLevel
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagModel
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.S2MathAs51642Interfaces

theorem ggAutFixedSubgroup_inner_actor_spProj {K : Type} [Field K] [Finite K] [CharP K 2]
    {m : ℕ} [NeZero m] {A : Subgroup (MulAut (LargeEvenProj (LargeEvenSpGroup K m)))}
    (hA : (A : Set (MulAut (LargeEvenProj (LargeEvenSpGroup K m)))) ⊆
      LargeEvenInnSet (LargeEvenProj (LargeEvenSpGroup K m)))
    {u : MulAut (LargeEvenProj (LargeEvenSpGroup K m))} (hu : u ∈ A) (huodd : Odd (orderOf u))
    (hcomm : ∀ a ∈ A, Commute a u) {C : Subgroup (LargeEvenProj (LargeEvenSpGroup K m))}
    (hC : IsComponentOf C (ggAutFixedSubgroup u)) :
    (∀ a ∈ A, ∀ c ∈ C, a c ∈ C) ∧
      CFSG.StandardType.LargeEvenMarking ↥C (fun _ _ _ I _ θ => GGAutsInduceOn A C θ I) := by
  classical
  obtain ⟨s, hs⟩ := hA hu
  have hconj : Function.Injective
      (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K m) →* MulAut _) :=
    mulAut_conj_injective (TableBSymp.center_spProj_eq_bot (K := K) (m := m))
  have hord : orderOf u = orderOf s := by
    rw [← hs]
    exact orderOf_injective _ hconj s
  have hodd : Odd (orderOf s) := hord ▸ huodd
  let e := TableBSymp.spProjEquivSp (K := K) (m := m)
  have hodd' : Odd (orderOf (e s)) := by
    rw [MulEquiv.orderOf_eq]
    exact hodd
  have hmap : (Subgroup.centralizer ({s} : Set (LargeEvenProj (LargeEvenSpGroup K m)))).map
        e.toMonoidHom = Subgroup.centralizer ({e s} : Set ↥(LargeEvenSpGroup K m)) := by
    have h := CFSG.ABGDGroups.map_inf_centralizer_of_injective e.toMonoidHom e.injective ⊤ s
    rwa [top_inf_eq, Subgroup.map_top_of_surjective _ e.surjective, top_inf_eq] at h
  let eC : ↥(Subgroup.centralizer ({s} : Set (LargeEvenProj (LargeEvenSpGroup K m)))) ≃*
      ↥(Subgroup.centralizer ({e s} : Set ↥(LargeEvenSpGroup K m))) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)
  refine ggAutFixedSubgroup_inner_actor hconj hA hs hcomm ?_ hC
  intro C' hC'
  have hC'' : IsComponentOf C'
      (Subgroup.centralizer ({s} : Set (LargeEvenProj (LargeEvenSpGroup K m)))) := by
    have h := hC'
    rw [← hs, ggAutFixedSubgroup_mulAut_conj] at h
    exact h
  have hmark : LargeEvenMarking ↥C' (fun _ _ _ _ _ _ => True) :=
    largeEvenMarking_of_isComponentOf_mulEquiv eC
      (fun D hD => largeEvenMarking_of_isComponentOf_centralizer_statedSp (e s) hodd' D hD)
      hC''
  have hE : GGE0Concl
      (Subgroup.centralizer ({s} : Set (LargeEvenProj (LargeEvenSpGroup K m)))) C' :=
    ggE0Concl_centralizer_of_mulEquiv e s
      (fun D hD => ggE0Concl_centralizer_statedSp (e s) hodd' D hD) C' hC''
  exact ⟨hE.1, largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.2) (hE.2 hmark)⟩

theorem q1RToralTransfer_bc :
    Q1RToralTransfer (fun _ _ _ => True) (fun _ lab => lab.tag = .B ∨ lab.tag = .C)
      (fun _ _ _ => True) := by
  intro p hp hp2 lab hlab htag
  obtain ⟨t, l, n⟩ := lab
  intro Q hQ
  rcases htag with h | h <;> dsimp only at h <;> subst h
  all_goals
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeSymplectic] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    have hchar : CharP K 2 := charP_two_of_card hK
    have hl2 : 2 ≤ l := hlab.2.1
    have hne : NeZero l := ⟨by omega⟩
    refine ⟨K, i1, i2, hK, hq, ?_⟩
    intro A hA hAI _ u hu huord J hJ
    have hAinn : (A : Set (MulAut (LargeEvenProj (if false = true then
        ⁅LargeEvenSpGroup K l, LargeEvenSpGroup K l⁆ else LargeEvenSpGroup K l)))) ⊆
        LargeEvenInnSet (LargeEvenProj (if false = true then
          ⁅LargeEvenSpGroup K l, LargeEvenSpGroup K l⁆ else LargeEvenSpGroup K l)) :=
      fun a ha => TableBSymp.sp_I_subset_inn (K := K) (m := l) (hAI a ha)
    have hodd : Odd (orderOf u) := by
      rw [huord]
      exact hp.odd_of_ne_two hp2
    have hcomm : ∀ a ∈ A, Commute a u := fun a ha =>
      congrArg Subtype.val (hA.1.is_comm.comm (⟨a, ha⟩ : ↥A) (⟨u, hu⟩ : ↥A))
    obtain ⟨hnorm, hmark⟩ := ggAutFixedSubgroup_inner_actor_spProj (K := K) (m := l)
      hAinn hu hodd hcomm (isComponentOf_iff_open.mpr hJ)
    exact largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨trivial, hnorm, h⟩) hmark

theorem q1On_bc : GGBstarInnerDiagJInputOn (fun _ lab => lab.tag = .B ∨ lab.tag = .C) := by
  refine q1On_of_selectedTransfer (Rel := fun _ _ _ => True) ?_
  refine q1SelectedTransfer_of_toral (Toral := fun _ _ _ => True)
    (q1ToralActionTransfer_of_rToral q1RToralTransfer_bc) ?_
  intro G _ _ p B Bs x L D J hcfg P hP
  exact largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h, fun _ _ _ => trivial⟩) hP

theorem q1On_of_not_bc {S : ℕ → LargeEvenLabel → Prop}
    (h : GGBstarInnerDiagJInputOn fun p lab => S p lab ∧ ¬ (lab.tag = .B ∨ lab.tag = .C)) :
    GGBstarInnerDiagJInputOn S := by
  intro G _ _ p B Bs x L D J hcfg hmark
  refine q1On_or q1On_bc h G p B Bs x L D J hcfg
    (largeEvenMarking_mono (fun lab _ _ _ _ _ hh => ⟨?_, hh.2⟩) hmark)
  exact (Classical.em (lab.tag = .B ∨ lab.tag = .C)).imp_right fun hbc => ⟨hh.1, hbc⟩

end CFSG.StandardType
