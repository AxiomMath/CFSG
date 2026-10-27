module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413SpEndLift
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413SpEndB
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413SpEndY
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413SpFix
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6Props

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSmallReeTorus

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch1413

open CFSG.Quasithin CFSG.Open CFSG.ComponentClassification.CatFactsSp4 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial SymplecticHigher SymplecticFlag Subgroup

theorem sp4_four_group_in_psl {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p) {A : Subgroup (StatedProj (StatedSp 2 K))}
    (hA : Nat.card A = 4) (hAe : IsElemAbelian 2 A) (hAX : A ≤ X0 K) (hu : u1 K ∉ A) :
    ∃ Y : Subgroup (StatedProj (StatedSp 2 K)), A ≤ Y ∧ F6.IsL2 p 2 ↥Y := by
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact hp.odd_of_ne_two hp2
  obtain ⟨g₁, g₂, h₁, h₂, hg1, hg2, hh1, hh2, hgh1, hgh2, hAeq⟩ :=
    sp4_four_group_lifts hodd hA hAe hAX hu
  obtain ⟨B, d, hd0, hdsq, hBB, hμ, hBg, hBh⟩ :=
    sp4_commutant_B hodd hg1 hg2 hh1 hh2 hgh1 hgh2
  refine ⟨(fixOf (conjSp 2 K B)).map (proj 2 K), ?_,
    sp4_Y_of_B hp hp2 hK B hd0 hdsq hBB hμ⟩
  rw [hAeq, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact Subgroup.mem_map_of_mem (proj 2 K) (mem_fixOf.mpr hBg)
  · exact Subgroup.mem_map_of_mem (proj 2 K) (mem_fixOf.mpr hBh)

theorem asch1413_sp4_end (h64o : Asch6_4Odd) {Q : Type} [Group Q] [Finite Q] {V : Type}
    [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {ρ : Q →* MulAut V}
    (hρ : Function.Injective ρ) {L A : Subgroup Q} {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 < p) (hK : Nat.card K = p)
    (e : ↥L ≃* StatedProj (StatedSp 2 K)) (hA : Nat.card A = 4) (hAe : IsElemAbelian 2 A)
    (hq : IsQuadraticOn ρ A)
    (hAX : A ≤ (X0 K).map (spIota e)) (hzA : spIota e (u1 K) ∉ A) : False := by
  let ι : StatedProj (StatedSp 2 K) →* Q := spIota e
  have hιinj : Function.Injective ι := by
    intro x y hxy
    exact e.symm.injective (Subtype.coe_injective hxy)
  have hp2 : p ≠ 2 := by omega
  have hp9 : 9 < p ^ 2 := by nlinarith
  let A_P : Subgroup (StatedProj (StatedSp 2 K)) := A.comap ι
  have hA_P_le_range : A ≤ ι.range :=
    hAX.trans (Subgroup.map_le_range (f := ι) (X0 K))
  have hmap : A_P.map ι = A := Subgroup.map_comap_eq_self hA_P_le_range
  have hcardAP : Nat.card A_P = 4 := by
    have h := Subgroup.card_map_of_injective (K := A_P) (f := ι) hιinj
    rw [hmap] at h
    omega
  have hAeAP : IsElemAbelian 2 A_P := IsElemAbelian.comap hAe hιinj
  have hAXAP : A_P ≤ X0 K := by
    intro x hx
    have hxA : ι x ∈ A := (Subgroup.mem_comap).mp hx
    rcases (Subgroup.mem_map.mp (hAX hxA)) with ⟨y, hy, hyx⟩
    exact hιinj hyx ▸ hy
  have huAP : u1 K ∉ A_P := by
    intro hu
    apply hzA
    have : ι (u1 K) ∈ A_P.map ι := Subgroup.mem_map_of_mem ι hu
    rwa [hmap] at this
  obtain ⟨Y, hA_PY, hL2Y⟩ :=
    sp4_four_group_in_psl hp hp2 hK hcardAP hAeAP hAXAP huAP
  let YQ : Subgroup Q := Y.map ι
  have hAYQ : A ≤ YQ := by
    rw [← hmap]
    exact Subgroup.map_mono hA_PY
  let eY : ↥Y ≃* ↥YQ := Subgroup.equivMapOfInjective Y ι hιinj
  have hsimpleY : IsSimpleGroup ↥Y := by
    obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ := hL2Y
    have h4 : 4 ≤ Nat.card F := by rw [hF]; nlinarith
    haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
    exact (eF.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj
      2 F).symm).isSimpleGroup
  have hnabY : ∃ a b : ↥Y, a * b ≠ b * a := by
    obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ := hL2Y
    have hFne2 : Nat.card F ≠ 2 := by rw [hF]; omega
    have hFne3 : Nat.card F ≠ 3 := by rw [hF]; omega
    obtain ⟨x, y, hxy⟩ :=
      CFSG.ComponentClassification.CatalogueBSmallRee.projectiveSpecialLinear_two_nonabelian
        F hFne2 hFne3
    let e' := eF.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
    exact ⟨e'.symm x, e'.symm y, fun hc => hxy (by simpa using congrArg e' hc)⟩
  haveI : IsSimpleGroup ↥Y := hsimpleY
  haveI : Group.IsPerfect ↥Y :=
    ⟨CFSG.ComponentClassification.Helpers.commutator_eq_top ↥Y hnabY⟩
  have hquasiY := CFSG.ComponentClassification.Quasisimple.simple_of_perfect ↥Y
  have hcenterY : Subgroup.center ↥Y = ⊥ :=
    CFSG.ComponentClassification.Helpers.center_eq_bot ↥Y hnabY
  let Q' := ↥YQ
  have hquasiQ' := CFSG.ComponentClassification.Components.quasisimple_of_equiv
    ((Subgroup.topEquiv (G := Q')).trans eY.symm) hquasiY
  have hcenterQ' : Subgroup.center Q' = ⊥ := by
    have h := Subgroup.map_center_eq (eY : ↥Y ≃* Q')
    rw [hcenterY, Subgroup.map_bot] at h
    exact h.symm
  have hL2Q' : F6.IsL2 p 2 ↥(⊤ : Subgroup Q') :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv
      (Subgroup.topEquiv (G := Q')).symm
      (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eY hL2Y)
  let A' : Subgroup Q' := A.subgroupOf YQ
  have hcardA' : Nat.card A' = 4 := by
    have h := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAYQ).toEquiv
    simpa using h.trans hA
  have hAe' : IsElemAbelian 2 A' := hAe.subgroupOf YQ
  have hq' : IsQuadraticOn (ρ.comp YQ.subtype) A' := by
    intro a ha b hb v
    have haA : (a : Q) ∈ A := (Subgroup.mem_subgroupOf).mp ha
    have hbA : (b : Q) ∈ A := (Subgroup.mem_subgroupOf).mp hb
    simpa [MonoidHom.comp_apply, Subgroup.coe_subtype] using hq (a : Q) haA (b : Q) hbA v
  have hAC' : A' ⊓ Subgroup.centralizer (↑(⊤ : Subgroup Q') : Set Q') = ⊥ := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ, hcenterQ']
    exact inf_bot_eq _
  have hAnorm' : A' ≤ Subgroup.normalizer (↑(⊤ : Subgroup Q') : Set Q') := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  exact h64o Q' V hV (ρ.comp YQ.subtype) (hρ.comp YQ.subtype_injective) ⊤ A'
    ⟨le_top, IsSubnormal.refl ⊤, hquasiQ'⟩ hAnorm' hcardA' hAe' hq' hAC' p 2 hp hp2 hp9 hL2Q'

end CFSG.LocalAnalysis.WeakClosure81.Asch1413

end
