module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDatumOfTor

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace E6D4Loc

private lemma coxeter_reindex_refl {ι : Type} (M : CoxeterMatrix ι) :
    M = M.reindex (Equiv.refl ι) := by
  apply CoxeterMatrix.ext
  ext i j
  rw [CoxeterMatrix.reindex_apply]
  simp

theorem ggResXDatumE6x_of_wit_of_mem {G : Type} [Group G] [Finite G] {p m : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hm : Odd m) (hpm : p ∣ m) {Bs X : Subgroup G}
    (hM : GGIsWeylMatrix CoxeterMatrix.E₆) (hMC : GGIntCartan CoxeterMatrix.E₆ CartanMatrix.E₆)
    (hBs : IsElemAbelian p Bs)
    (hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (w : GGTorusTorWit m 6 ↥X (ggGamma X hN).range)
    (hw : w.Holds CartanMatrix.E₆ CoxeterMatrix.E₆) (z : G)
    (hInd : z ∈ X → ∀ c : Fin 6 → ZMod p,
      (List.ofFn fun k => w.cor k (ggZetaP p m ^ (c k).val)).prod = 1 → c = 0) :
    GGResXDatumE6x p Bs X z := by
  by_cases hz : z ∈ X
  · exact ggResXDatumE6x_of_wit hp2 hm hpm hM hMC hBs hS hN w hw (hInd hz) z
  obtain ⟨V, hVadd, hVmod, hι⟩ := exists_ggLinData (p := p) (G := G) (Bs := Bs) hBs
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod p) V := hVmod
  obtain ⟨ι⟩ := hι
  obtain ⟨hnk, hbk, α, hlin, hpair, -, -⟩ := ggTD_linearData hm hpm hBs hS hN w hw V ι
  obtain ⟨e, he⟩ := ggTD_weyl hN hw hp2 hBs hnk
  have hcl := ggTD_closure hN hw hp2 hBs hnk
  have hfx : ∀ i, α i (ι (Additive.ofMul (⟨_, hbk i⟩ : ↥Bs))) = 2 := by
    intro i
    rw [hpair i i, hMC.1 i]
    norm_num
  refine ⟨Fin 6, inferInstance, inferInstance, CoxeterMatrix.E₆, CartanMatrix.E₆, V, hVadd,
    hVmod, ι, (fun k => ggTDρB X Bs (ggTDnH w hnk k)),
    (fun k => ι (Additive.ofMul (⟨_, hbk k⟩ : ↥Bs))), α, Equiv.refl _,
    coxeter_reindex_refl _, hM, hMC, hlin, ?_, hpair, ⟨e, he⟩, hcl, fun h => absurd h hz⟩
  intro i
  exact ggIsReflection_of_eq_reflection hp2 ι (hfx i) (ggLin_eq_reflection ι (hfx i) (hlin i))

theorem ggResXDatumE6x_split (hRig : GGLabelRigidInput) (hE6 : GGTBTorE6)
    (hLift : GGTBTorLiftRows) {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp 3 B Bs x L D J y K)
    {X : Subgroup G} {z : G} (hXz : (X = L ∧ z = x) ∨ (X = K ∧ z = y))
    {labX : LargeEvenLabel} (hXΛ : LargeEvenInLambda2 labX)
    (hXl : GGHasLabel labX (↥X ⧸ Subgroup.center ↥X)) (htag : labX.tag = .E6)
    (hM : 3 ∣ ggTorM labX) : GGResXDatumE6x 3 Bs X z := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hBs : IsElemAbelian 3 Bs := hH.1.tableB_facts.2.1
  have hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hH.1.2.1.2.2.2
  have hdata : z ∈ Subgroup.centralizer (X : Set G) ∧ z ≠ 1 ∧ z ^ 3 = 1 ∧
      GGInnerDiagOn Bs X ∧ GGTorusTBAt 3 Bs X := by
    rcases hXz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨hc, h1, hpz, hperf⟩ := GGConfig.data_L hH.1
      exact ⟨hc, h1, hpz, hH.2.2.1.1, ggTorusTBAt_L hH.1 hperf⟩
    · obtain ⟨hc, h1, hpz, hperf⟩ := hH.data_K
      exact ⟨hc, h1, hpz, hH.2.2.1.2 _ _ hH.2.2.2.2.1,
        ggTorusTBAt_nbr hH.1 hH.2.2.2.2.1 hperf⟩
  obtain ⟨hzc, hz1, hzp, hInn, hTB⟩ := hdata
  have hrow := GGTBTorRowAt.e6Three (p := 3) htag rfl hM
  obtain ⟨hodd, hpm, hMw, hMC⟩ := l05nPlP1_row_facts hp hp2 hXΛ hrow
  obtain ⟨hN, hTor⟩ := ggTorData_of_hasLabel hRig hInn hTB hXΛ hXl (hE6 labX hXΛ htag hM)
    (hLift 3 labX _ _ _ _ _ hp hp2 hXΛ hrow)
  obtain ⟨w, hw⟩ := hTor
  refine ggResXDatumE6x_of_wit_of_mem hp2 hodd hpm hMw hMC hBs hS hN w hw z fun hzX => ?_
  have hzcen : (⟨z, hzX⟩ : ↥X) ∈ Subgroup.center ↥X := by
    refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
    simpa using Subgroup.mem_centralizer_iff.mp hzc g g.2
  have hzo : orderOf (⟨z, hzX⟩ : ↥X) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by simpa using hzp)
    · exact fun h => hz1 (congrArg Subtype.val h)
  have hxs := ggTor_central_mem_closure_E6 hodd hpm w hw hw.2.2.2.2.2.1 _ hzcen hzo
  exact w.coroot_indep_of_center hp hodd hpm hw ggCartanE₆_ker_le_one _ hzcen hzo hxs

end E6D4Loc

end CFSG.StandardType

end
