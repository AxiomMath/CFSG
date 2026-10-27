module

public import CFSG.LocalAnalysis.StandardType.GGTwA5ThreeIndep
public import CFSG.LocalAnalysis.StandardType.GGResXDatumAHL
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResXDatumAx_of_torData_twA5 {G : Type} [Group G] [Finite G] {m : ℕ}
    (hm : Odd m) (h3m : 3 ∣ m) {Bs X : Subgroup G} {z : G}
    (hBs : IsElemAbelian 3 Bs)
    (hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hzc : z ∈ Subgroup.centralizer (X : Set G)) (hzo : orderOf z = 3)
    (hTor : GGTorusTorData m 5 (CartanMatrix.A 5) (CoxeterMatrix.A 5) ↥X
      (ggGamma X hN).range) :
    GGResXDatumAx 3 Bs X z 5 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨w, hw⟩ := hTor
  obtain ⟨V, hVadd, hVmod, hι⟩ := exists_ggLinData (p := 3) (G := G) (Bs := Bs) hBs
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod 3) V := hVmod
  obtain ⟨ι⟩ := hι
  obtain ⟨hnk, hbk, α, hlin, hpair, -⟩ :=
    ggHLT_lin hm h3m hBs hS hN w hw V ι (x := 1) (Subgroup.one_mem Bs)
      (Subgroup.one_mem (Subgroup.centralizer (X : Set G)))
  obtain ⟨e, he⟩ := ggTD_weyl hN hw (by norm_num : (3 : ℕ) ≠ 2) hBs hnk
  have hcl := ggTD_closure hN hw (by norm_num : (3 : ℕ) ≠ 2) hBs hnk
  have hMC : GGIntCartan (CoxeterMatrix.A 5) (CartanMatrix.A 5) := ggIntCartan_A 5
  have hrefl : CoxeterMatrix.A 5 = (CoxeterMatrix.A 5).reindex (Equiv.refl (Fin 5)) := by
    apply CoxeterMatrix.ext
    ext i j
    rw [CoxeterMatrix.reindex_apply]
    simp
  have hM : GGIsWeylMatrix (CoxeterMatrix.A 5) :=
    Or.inl ⟨5, Equiv.refl _, by norm_num, Or.inl hrefl⟩
  have hfx : ∀ i, α i (ι (Additive.ofMul (⟨_, hbk i⟩ : ↥Bs))) = 2 := by
    intro i
    rw [hpair i i, hMC.1 i]
    norm_num
  refine ⟨Fin 5, inferInstance, inferInstance, CoxeterMatrix.A 5, CartanMatrix.A 5, V, hVadd,
    hVmod, ι, (fun k => ggTDρB X Bs (ggTDnH w hnk k)),
    (fun k => ι (Additive.ofMul (⟨_, hbk k⟩ : ↥Bs))), α, Equiv.refl _, hrefl, hM, hMC, hlin,
    ?_, hpair, ⟨e, he⟩, hcl, ?_⟩
  · intro i
    exact ggIsReflection_of_eq_reflection (by norm_num : (3 : ℕ) ≠ 2) ι (hfx i)
      (ggLin_eq_reflection ι (hfx i) (hlin i))
  · intro hzX
    have hzc' : (⟨z, hzX⟩ : ↥X) ∈ Subgroup.center ↥X := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzc (g : G) g.2)
    have hzo' : orderOf (⟨z, hzX⟩ : ↥X) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact hzo
    have hInd := ggTorusTorWit_coroot_indep_twA5 hm h3m w hw hzc' hzo'
    obtain ⟨_hnk', _hbk', _α', -, -, -, -, hind⟩ := ggTD_lin hm h3m hBs hS hN w hw hInd V ι
    exact hind

end CFSG.StandardType

end
