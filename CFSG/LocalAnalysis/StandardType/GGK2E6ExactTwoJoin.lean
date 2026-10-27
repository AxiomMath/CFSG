module

public import CFSG.LocalAnalysis.StandardType.GGK2E6KOnlyE6DependentLConsumer
public import CFSG.LocalAnalysis.StandardType.GGK2E6B5ActualJoin
public import CFSG.LocalAnalysis.StandardType.GGK2E6D5E6ActualDataConsumer
public import CFSG.LocalAnalysis.StandardType.GGK2E6D5PlaneModel
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeA5Consumer
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeA5DepConsumer
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeE6ConsumerK
public import CFSG.LocalAnalysis.StandardType.GGReflExtA5
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeA5DepFinal
public import CFSG.LocalAnalysis.StandardType.GGReflExtE6
public import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbrHolds

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem KOnlyE6_dependent_L_A5_join_or_B5D5_of_moving_K
    (hAll : LR6A5All) (hA5Dep : LR6A5DepAll) (hOrb : GGResCentBoundInput)
    (hFix : GGTBFixInput)
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hmoveK : ∃ t ∈ ggAutomizer K Bs, GGIsReflection 3 t ∧
      t ⟨x, hH.1.tableB_facts.2.2.1⟩ ≠ ⟨x, hH.1.tableB_facts.2.2.1⟩)
    (hD : GGResLeviDatumExact2 3 Bs K J L ggSelDep ggTypLE6)
    (hno : ¬ (GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypAny)) :
    GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ∨
      ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (S : Finset Λ)
        (Λa : Type) (_ : Fintype Λa) (_ : DecidableEq Λa)
        (ML : CoxeterMatrix Λ) (CL : Matrix Λ Λ ℤ)
        (MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa))
        (CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ)
        (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V)
        (ι : Additive ↥Bs ≃+ V) (φ : Λ ⊕ Λa → MulAut ↥Bs)
        (h : Λ ⊕ Λa → V) (α : Λ ⊕ Λa → Module.Dual (ZMod 3) V)
        (e : Fin 6 ≃ Λ),
        S.card = 2 ∧ 1 ≤ Nat.card Λa ∧ Nat.card Λa = 1 ∧ Nat.card Λa ≤ 3 ∧
        GGIsWeylMatrix ML ∧ GGIntCartan ML CL ∧ GGIsWeylMatrix MK ∧ GGIntCartan MK CK ∧
        GGIsTypeE6 ML ∧
        (∀ o w, ggLin (p := 3) ι (φ o) w = w - α o w • h o) ∧
        (∀ o, GGIsReflection 3 (φ o)) ∧
        (∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod 3)) ∧
        (∀ o o' : {i : Λ // i ∉ S} ⊕ Λa,
          α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod 3)) ∧
        (¬ LinearIndependent (ZMod 3) (fun i : Λ => h (Sum.inl i))) ∧
        (∃ fL : ML.Group ≃* ↥(ggAutomizer K Bs),
          ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ (Sum.inl i)) ∧
        (∃ fK : MK.Group ≃* ↥(ggAutomizer L Bs),
          ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id)) ∧
        ggAutomizer K Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)) ∧
        ggAutomizer L Bs = Subgroup.closure
          (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
            Set.range fun a : Λa => φ (Sum.inr a)) ∧
        GGDeletedConnectedS ML S ∧
        ggAutomizer J Bs = Subgroup.closure
          (Set.range fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∧
        ML = (CoxeterMatrix.E₆).reindex e ∧
        Fintype.card ({i : Λ // i ∉ S} ⊕ Λa) = 5 ∧
        ((∃ e5 : Fin 5 ≃ ({i : Λ // i ∉ S} ⊕ Λa),
            MK = (CoxeterMatrix.B 5).reindex e5) ∨
          (∃ e5 : Fin 5 ≃ ({i : Λ // i ∉ S} ⊕ Λa),
            MK = (ggCoxeterMatrixD 5).reindex e5)) := by
  classical
  have hDany := ggResLeviDatumExact2_any_of_dep hD
  have hcardBs := hH.card_Bs_six_of_K_only_E6 hFix hDany hno
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α, e,
    hS, hA1, hA3, hMLW, hCLL, hMKW, hCKW, htyp, hlin, hrefl, hpair, hpairK, hsel,
    ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ, heML, hcardL, hType, hD5rel⟩ :=
    KOnlyE6_dependent_L_full hH hFix hD hno
  letI := i1; letI := i2; letI := i3; letI := i4; letI := i5; letI := i6
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hcardΛ : Fintype.card Λ = 6 := by
    have hc : Fintype.card (Fin 6) = Fintype.card Λ := Fintype.card_congr e
    simpa using hc.symm
  have hrange : Set.range (fun o : {i : Λ // i ∉ S} ⊕ Λa => φ (o.map Subtype.val id)) =
      Set.range (fun j : {i : Λ // i ∉ S} => φ (Sum.inl (j : Λ))) ∪
        Set.range (fun a : Λa => φ (Sum.inr a)) := by
    rw [Sum.range_eq]
    rfl
  have hclosL' : ggAutomizer L Bs = Subgroup.closure
      (Set.range fun o : {i : Λ // i ∉ S} ⊕ Λa => φ (o.map Subtype.val id)) := by
    rw [hclosK, hrange]
  rcases hType with hA5eq | hB5eq | hD5eq
  ·
    obtain ⟨e5, he5⟩ := hA5eq
    by_cases hind : LinearIndependent (ZMod 3)
      (fun o : {i : Λ // i ∉ S} ⊕ Λa => h (o.map Subtype.val id))
    · exact Or.inl (ggTwoNodeIndepAtL_a5_of_moving_K hAll hOrb hFix rfl hH hx hmoveK e5 he5 hCKW
        (fun o w => hlin (o.map Subtype.val id) w)
        (fun o => hrefl (o.map Subtype.val id))
        (fun o o' => hpairK o o') hclosL' hind)
    · have hNontriv : 1 < Fintype.card Λ := by omega
      exact Or.inl (ggTwoNodeA5DepL_of_moving_K hA5Dep hOrb hFix rfl hH hx hcardBs hmoveK
        e5 he5 hCKW (fun o w => hlin (o.map Subtype.val id) w)
        (fun o => hrefl (o.map Subtype.val id)) (fun o o' => hpairK o o')
        fK hfK hclosL' hind hMLW (fun i => hrefl (Sum.inl i)) fL hfL hclosL hNontriv)
  · exact Or.inr ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α, e,
      hS, hA1, hA3, (by omega : Nat.card Λa ≤ 3), hMLW, hCLL, hMKW, hCKW, htyp, hlin, hrefl,
      hpair, hpairK, hsel,
      ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ, heML, hcardL, Or.inl hB5eq⟩
  · exact Or.inr ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α, e,
      hS, hA1, hA3, (by omega : Nat.card Λa ≤ 3), hMLW, hCLL, hMKW, hCKW, htyp, hlin, hrefl,
      hpair, hpairK, hsel,
      ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ, heML, hcardL, Or.inr hD5eq⟩

end CFSG.StandardType

end

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem KOnlyE6_dependent_L_A5_B5_join_or_D5_of_moving_K
    (hAll : LR6A5All) (hA5Dep : LR6A5DepAll) (hOrb : GGResCentBoundInput)
    (hFix : GGTBFixInput)
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hmoveK : ∃ t ∈ ggAutomizer K Bs, GGIsReflection 3 t ∧
      t ⟨x, hH.1.tableB_facts.2.2.1⟩ ≠ ⟨x, hH.1.tableB_facts.2.2.1⟩)
    (hD : GGResLeviDatumExact2 3 Bs K J L ggSelDep ggTypLE6)
    (hno : ¬ (GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypAny)) :
    GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ∨
      ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (S : Finset Λ)
        (Λa : Type) (_ : Fintype Λa) (_ : DecidableEq Λa)
        (ML : CoxeterMatrix Λ) (CL : Matrix Λ Λ ℤ)
        (MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa))
        (CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ)
        (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V)
        (ι : Additive ↥Bs ≃+ V) (φ : Λ ⊕ Λa → MulAut ↥Bs)
        (h : Λ ⊕ Λa → V) (α : Λ ⊕ Λa → Module.Dual (ZMod 3) V)
        (e : Fin 6 ≃ Λ),
        S.card = 2 ∧ 1 ≤ Nat.card Λa ∧ Nat.card Λa = 1 ∧ Nat.card Λa ≤ 3 ∧
        GGIsWeylMatrix ML ∧ GGIntCartan ML CL ∧ GGIsWeylMatrix MK ∧ GGIntCartan MK CK ∧
        GGIsTypeE6 ML ∧
        (∀ o w, ggLin (p := 3) ι (φ o) w = w - α o w • h o) ∧
        (∀ o, GGIsReflection 3 (φ o)) ∧
        (∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod 3)) ∧
        (∀ o o' : {i : Λ // i ∉ S} ⊕ Λa,
          α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod 3)) ∧
        (¬ LinearIndependent (ZMod 3) (fun i : Λ => h (Sum.inl i))) ∧
        (∃ fL : ML.Group ≃* ↥(ggAutomizer K Bs),
          ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ (Sum.inl i)) ∧
        (∃ fK : MK.Group ≃* ↥(ggAutomizer L Bs),
          ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id)) ∧
        ggAutomizer K Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)) ∧
        ggAutomizer L Bs = Subgroup.closure
          (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
            Set.range fun a : Λa => φ (Sum.inr a)) ∧
        GGDeletedConnectedS ML S ∧
        ggAutomizer J Bs = Subgroup.closure
          (Set.range fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∧
        ML = (CoxeterMatrix.E₆).reindex e ∧
        Fintype.card ({i : Λ // i ∉ S} ⊕ Λa) = 5 ∧
        (∃ e5 : Fin 5 ≃ ({i : Λ // i ∉ S} ⊕ Λa),
          MK = (ggCoxeterMatrixD 5).reindex e5) := by
  classical
  have hDany := ggResLeviDatumExact2_any_of_dep hD
  have hcardBs := hH.card_Bs_six_of_K_only_E6 hFix hDany hno
  rcases KOnlyE6_dependent_L_A5_join_or_B5D5_of_moving_K hAll hA5Dep hOrb hFix hH hmoveK hD hno with
    hW | hRest
  · exact Or.inl hW
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α, e,
    hS, hA1, hAeq, hA3, hMLW, hCLL, hMKW, hCKW, htyp, hlin, hrefl, hpair, hpairK, hsel,
    ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ, heML, hcardL, hType⟩ := hRest
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  letI := i5
  letI := i6
  have hD2 : GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypAny :=
    ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
      hS, hA1, hA3, hMLW, hCLL, hMKW, hCKW, trivial, hlin, hrefl, hpair, hpairK,
      trivial, ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ⟩
  rcases hType with ⟨e5, he5⟩ | hD5
  · have hrange : Set.range (fun o : {i : Λ // i ∉ S} ⊕ Λa => φ (o.map Subtype.val id)) =
        Set.range (fun j : {i : Λ // i ∉ S} => φ (Sum.inl (j : Λ))) ∪
          Set.range (fun a : Λa => φ (Sum.inr a)) := by
      rw [Sum.range_eq]
      rfl
    have hclosL' : ggAutomizer L Bs = Subgroup.closure
        (Set.range fun o : {i : Λ // i ∉ S} ⊕ Λa => φ (o.map Subtype.val id)) := by
      rw [hclosK, hrange]
    exact Or.inl (K_only_E6_dependent_L_B5_join_raw hH e5 he5 hCKW hpairK
      (fun o w => hlin (o.map Subtype.val id) w) fK hclosL' hcardBs hD2)
  · exact Or.inr ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α, e,
      hS, hA1, hAeq, hA3, hMLW, hCLL, hMKW, hCKW, htyp, hlin, hrefl, hpair, hpairK, hsel,
      ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ, heML, hcardL, hD5⟩

end CFSG.StandardType

end

public section

namespace CFSG.StandardType

open CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace GGResHyp

theorem K_only_E6_dependent_join_of_moving_K
    (hAll : LR6A5All) (hA5Dep : LR6A5DepAll) (hOrb : GGResCentBoundInput)
    (hFix : GGTBFixInput)
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hmoveK : ∃ t ∈ ggAutomizer K Bs, GGIsReflection 3 t ∧
      t ⟨x, hH.1.tableB_facts.2.2.1⟩ ≠ ⟨x, hH.1.tableB_facts.2.2.1⟩)
    (hD : GGResLeviDatumExact2 3 Bs K J L ggSelDep ggTypLE6)
    (hno : ¬ (GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypAny)) :
    GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  rcases KOnlyE6_dependent_L_A5_B5_join_or_D5_of_moving_K hAll hA5Dep hOrb hFix hH hmoveK hD hno with
    hjoin | hD5
  · exact hjoin
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α, e,
    hS, hA1, hA3, hA3', hMLW, hCLL, hMKW, hCKW, htyp, hlin, hrefl, hpair, hpairK, hsel,
    ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ, heML, hcardL, hType⟩ := hD5
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  letI := i5
  letI := i6
  obtain ⟨e5, he5⟩ := hType
  subst MK
  have hcardBs : Nat.card Bs = 3 ^ 6 :=
    hH.card_Bs_six_of_K_only_E6 hFix (ggResLeviDatumExact2_any_of_dep hD) hno
  have hCKmodel : ∀ i j : Fin 5, CK (e5 i) (e5 j) = CartanMatrix.D 5 i j :=
    d5_actual_CK_model e5 rfl hCKW
  let φL : Fin 5 → MulAut ↥Bs := fun i => φ ((e5 i).map Subtype.val id)
  let hL : Fin 5 → V := fun i => h ((e5 i).map Subtype.val id)
  let αL : Fin 5 → Module.Dual (ZMod 3) V := fun i => α ((e5 i).map Subtype.val id)
  have hpairL : ∀ i j, αL i (hL j) = (CartanMatrix.D 5 i j : ZMod 3) := by
    intro i j
    dsimp [φL, hL, αL]
    rw [hpairK (e5 i) (e5 j), hCKmodel i j]
  have hlinL : ∀ i w, ggLin (p := 3) ι (φL i) w = w - αL i w • hL i := by
    intro i w
    exact hlin ((e5 i).map Subtype.val id) w
  have hreflL : ∀ i, GGIsReflection 3 (φL i) := by
    intro i
    exact hrefl ((e5 i).map Subtype.val id)
  have hrangeL : Set.range φL =
      Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl (j : Λ))) ∪
        Set.range (fun a : Λa => φ (Sum.inr a)) := by
    have hcomp : φL = (fun o : {i : Λ // i ∉ S} ⊕ Λa =>
        φ (o.map Subtype.val id)) ∘ e5 := rfl
    rw [hcomp, Set.range_comp, Equiv.range_eq_univ, Set.image_univ, Sum.range_eq]
    rfl
  have hgenL : ggAutomizer L Bs = Subgroup.closure (Set.range φL) := by
    rw [hclosK, hrangeL]
  let fLD5 : (ggCoxeterMatrixD 5).Group ≃* ↥(ggAutomizer L Bs) :=
    ((ggCoxeterMatrixD 5).reindexGroupEquiv e5).symm.trans fK
  have hfLD5 : ∀ i : Fin 5,
      (fLD5 ((ggCoxeterMatrixD 5).simple i) : MulAut ↥Bs) = φL i := by
    intro i
    dsimp [fLD5, φL]
    rw [CoxeterMatrix.reindexGroupEquiv_symm_apply_simple]
    exact hfK (e5 i)
  have hCLnorm : ∀ i j : Fin 6, CL (e i) (e j) = CartanMatrix.E 6 i j :=
    e6Cartan_reindex e hCLL heML
  let φK : Fin 6 → MulAut ↥Bs := fun i => φ (Sum.inl (e i))
  let hK : Fin 6 → V := fun i => h (Sum.inl (e i))
  let αK : Fin 6 → Module.Dual (ZMod 3) V := fun i => α (Sum.inl (e i))
  have hpairK6 : ∀ i j, αK i (hK j) = (CartanMatrix.E 6 i j : ZMod 3) := by
    intro i j
    dsimp [φK, hK, αK]
    rw [hpair (e i) (e j), hCLnorm i j]
  have hlinK : ∀ i w, ggLin (p := 3) ι (φK i) w = w - αK i w • hK i := by
    intro i w
    exact hlin (Sum.inl (e i)) w
  have hgenK : ggAutomizer K Bs = Subgroup.closure (Set.range φK) := by
    have hrangeK : Set.range φK = Set.range (fun i : Λ => φ (Sum.inl i)) := by
      have hcomp : φK = (fun i : Λ => φ (Sum.inl i)) ∘ e := rfl
      rw [hcomp, Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
    rw [hclosL, hrangeK]
  have hdepK : ¬ LinearIndependent (ZMod 3) hK := by
    intro hli
    change LinearIndependent (ZMod 3) ((fun i : Λ => h (Sum.inl i)) ∘ e) at hli
    exact hsel ((linearIndependent_equiv (e := e)).mp hli)
  subst ML
  let fLE6 : (CoxeterMatrix.E₆).Group ≃* ↥(ggAutomizer K Bs) :=
    (CoxeterMatrix.E₆.reindexGroupEquiv e).symm.trans fL
  have hfLE6 : ∀ i : Fin 6,
      (fLE6 ((CoxeterMatrix.E₆).simple i) : MulAut ↥Bs) = φK i := by
    intro i
    dsimp [fLE6, φK]
    rw [CoxeterMatrix.reindexGroupEquiv_symm_apply_simple]
    exact hfL (e i)
  exact (hH.false_of_D5_E6_original_data ι φL hL αL hpairL hlinL fLD5 hfLD5 hgenL hreflL
    φK hK αK hpairK6 hlinK hgenK fLE6 hdepK hcardBs).elim

end GGResHyp

end CFSG.StandardType

end

public section
namespace CFSG.StandardType

private theorem ggK2E6_other_reflGenerated
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs L J K : Subgroup G}
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypLE6) :
    GGReflGenerated p (ggAutomizer L Bs) := by
  classical
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, ha1, ha3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpairL, hpairK,
    hsel, hfL, hfK, hclosL, hclosK, hdel, hclosJ⟩ := hD
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  letI := i5
  letI := i6
  let φL : ({i : Λ // i ∉ S} ⊕ Λa) → MulAut ↥Bs :=
    fun o => φ (o.map Subtype.val id)
  have hrange : Set.range φL =
      Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
        Set.range (fun a : Λa => φ (Sum.inr a)) := by
    ext z
    constructor
    · rintro ⟨o, rfl⟩
      cases o with
      | inl j => exact Or.inl ⟨j, rfl⟩
      | inr a => exact Or.inr ⟨a, rfl⟩
    · rintro (⟨j, rfl⟩ | ⟨a, rfl⟩)
      · exact ⟨Sum.inl j, rfl⟩
      · exact ⟨Sum.inr a, rfl⟩
  exact ggIndep_reflGenerated_of_closure (fun o : {i : Λ // i ∉ S} ⊕ Λa => hrefl (o.map Subtype.val id))
    (by rw [hclosK, hrange])

theorem ggResK_typed_E6_card_six_weyl_join
{G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
{B Bs L D J K : Subgroup G} {x y : G}
(hH : GGResHyp p B Bs x L D J y K)
(hp : p = 3)
(hcard : Nat.card Bs = 3 ^ 6)
(hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypLE6)
(hno2L : ¬ GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny)
(hno3L : ¬ GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) :
GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  subst hp
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hNbr : GGNbr 3 B x D J y K := hH.2.2.2.2.1
  have hyB : y ∈ B := hNbr.1.2.1
  have hy1 : y ≠ 1 := hNbr.1.2.2.1
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hNbr.1.2.2.2.1
  have hy : y ∈ Bs := hH.1.2.1.1 hyB
  have hyfix : ∀ ψ ∈ ggAutomizer K Bs, ψ (⟨y, hy⟩ : ↥Bs) = ⟨y, hy⟩ :=
    ggResI_automizer_fix hy hKy
  have hKFix : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) →
      (b : G) ∈ Subgroup.zpowers y :=
    ggResK_fixedLine_of_twE6_card_six hH rfl hcard hD
  have hDkeep : GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypLE6 := hD
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, ha1, ha3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpairL, hpairK,
    hsel, hfL, hfK, hclosL, hclosK, hdel, hclosJ⟩ := hD
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  letI := i5
  letI := i6
  obtain ⟨fL, hfL⟩ := hfL
  obtain ⟨fK, hfK⟩ := hfK
  obtain ⟨e, he⟩ := htyp
  have hLrefl : GGReflGenerated 3 (ggAutomizer L Bs) :=
    ggK2E6_other_reflGenerated hDkeep
  have hmoveK := ggIndep_moving_K_of_fixedLine hH hx hKFix
  have hBs7 : Nat.card ↥Bs ≤ 3 ^ 7 := by
    rw [hcard]
    norm_num
  have hAKcard : Nat.card ↥(ggAutomizer K Bs) = 51840 :=
    ggE6K_card_AK e he fL
  have hOrbK : GGResCentBoundNbrInput := ggResCentBoundNbrInput_holds
  have hbound : Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) ≤
      3 ^ 7 * (6 * (3 - 1) * 51840) :=
    ggE6K_card_join_le hOrbK rfl hH hy hBs7 hAKcard
  by_cases hind : LinearIndependent (ZMod 3) (fun i : Λ => h (Sum.inl i))
  · exact ggTwoNodeIndepAtK_e6_of_moving_K
      (x := x) (y := y) (φ := fun i : Λ => φ (Sum.inl i))
      (h := fun i : Λ => h (Sum.inl i)) (α := fun i : Λ => α (Sum.inl i))
      (ι := ι) lr6E6All_of_certificate ggTBFixInput_holds
      rfl hH hmoveK hBs7 hLrefl hbound e he hCL
      (fun i w => hlin (Sum.inl i) w) hpairL hclosL hind
  · have hDdep : GGResLeviDatumExact2 3 Bs K J L ggSelDep ggTypLE6 :=
      ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
        hS, ha1, ha3, hML, hCL, hMK, hCK, ⟨e, he⟩, hlin, hrefl, hpairL, hpairK,
        hind, ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hdel, hclosJ⟩
    exact hH.K_only_E6_dependent_join_of_moving_K lr6A5All_of_certificate
      lr6A5DepAll_of_certificate ggResCentBoundInput_holds ggTBFixInput_holds hmoveK hDdep
      (fun hn => hn.elim hno2L hno3L)

theorem GGResHyp.K_only_E6_exact2_weyl_join
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypLE6)
    (hno : ¬ (GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypAny)) :
    GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  have hcard := hH.card_Bs_six_of_K_only_E6 ggTBFixInput_holds hD hno
  exact ggResK_typed_E6_card_six_weyl_join hH rfl hcard hD
    (fun h => hno (Or.inl h)) (fun h => hno (Or.inr h))

end CFSG.StandardType
end
