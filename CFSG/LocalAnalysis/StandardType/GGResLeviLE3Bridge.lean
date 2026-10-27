module

public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Defs
public import CFSG.LocalAnalysis.StandardType.GGResSideDatumDefs
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3BridgeB2
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepChain
public import CFSG.LocalAnalysis.StandardType.GGResJLineA3
public import CFSG.LocalAnalysis.StandardType.GGPZWeylType
public import CFSG.Monster.B.Geometry.InitialIsometryParabolic
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classification
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.DynkinType

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResLeviDatumLE3_of_sides_conj {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {Bs L J K : Subgroup G} (hL : GGResLeviSideDatumLE3 p Bs L J)
    (hK : GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J) :
    GGResLeviDatumLE3 p Bs L J K ggSelAny ggTypAny := by
  rcases hK with hK | hK
  ·
    obtain ⟨D⟩ := l05nBL_align ggWeylSimpleSystemsConjInput_holds hp2 hL (l05nBL_sum_of_one hK)
    exact l05nBL_DatumK.toDatum (l05nBL_datum D) (le_refl 1) (by norm_num)
  ·
    obtain ⟨k, hk1, hk3, hSS⟩ := l05nBL_sum_of_levi hK
    obtain ⟨D⟩ := l05nBL_align ggWeylSimpleSystemsConjInput_holds hp2 hL hSS
    exact l05nBL_DatumK.toDatum (l05nBL_datum D) (by omega) hk3

theorem l05nBL_order_eq_of_simple_map_eq {Λ Λ' : Type} {M : CoxeterMatrix Λ}
    {M' : CoxeterMatrix Λ'} {H : Type} [Group H] (f : M.Group →* H) (f' : M'.Group →* H)
    (hf : Function.Injective f) (hf' : Function.Injective f') (i j : Λ) (i' j' : Λ')
    (hi : f (M.simple i) = f' (M'.simple i')) (hj : f (M.simple j) = f' (M'.simple j')) :
    M.M i j = M'.M i' j' := by
  have h1 : orderOf (f (M.simple i) * f (M.simple j)) = M.M i j := by
    rw [← map_mul]
    exact (orderOf_injective f hf (M.simple i * M.simple j)).trans (by
      simpa only [CoxeterMatrix.toCoxeterSystem_simple] using
        CoxeterSystem.orderOf_simple_mul_simple M.toCoxeterSystem i j)
  have h3 : orderOf (f' (M'.simple i') * f' (M'.simple j')) = M'.M i' j' := by
    rw [← map_mul]
    exact (orderOf_injective f' hf' (M'.simple i' * M'.simple j')).trans (by
      simpa only [CoxeterMatrix.toCoxeterSystem_simple] using
        CoxeterSystem.orderOf_simple_mul_simple M'.toCoxeterSystem i' j')
  rw [← h1, ← h3, hi, hj]

theorem ggResLeviDatumCard_reverse_of_witness {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs L J K : Subgroup G}
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Λ ⊕ Λa → MulAut ↥Bs} {h : Λ ⊕ Λa → V} {α : Λ ⊕ Λa → Module.Dual (ZMod p) V}
    (hS1 : 1 ≤ S.card) (hS3 : S.card ≤ 3)
    (hWML : GGIsWeylMatrix ML) (hCLL : GGIntCartan ML CL)
    (hWMK : GGIsWeylMatrix MK) (hCKK : GGIntCartan MK CK)
    (hlin : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hrefl : ∀ o, GGIsReflection p (φ o))
    (hpairL : ∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod p))
    (hpairK : ∀ o o' : {i : Λ // i ∉ S} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p))
    (hfLx : ∃ fL : ML.Group ≃* ↥(ggAutomizer L Bs),
      ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ (Sum.inl i))
    (hfKx : ∃ fK : MK.Group ≃* ↥(ggAutomizer K Bs),
      ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id))
    (hclosL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (hclosK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
        Set.range fun a : Λa => φ (Sum.inr a)))
    (hdel : GGDeletedConnectedS ML S)
    (hclosJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ∉ S} => φ (Sum.inl j))) :
    GGResLeviDatumCard (Nat.card Λa) p Bs K J L ggSelAny ggTypAny := by
  obtain ⟨fL, hfL⟩ := hfLx
  obtain ⟨fK, hfK⟩ := hfKx
  have hMKML : ∀ i j : {i : Λ // i ∉ S},
      MK.M (Sum.inl i) (Sum.inl j) = ML.M i.1 j.1 := by
    intro i j
    let fK' : MK.Group →* MulAut ↥Bs :=
      (Subgroup.subtype (ggAutomizer K Bs)).comp (fK : MK.Group →* ↥(ggAutomizer K Bs))
    let fL' : ML.Group →* MulAut ↥Bs :=
      (Subgroup.subtype (ggAutomizer L Bs)).comp (fL : ML.Group →* ↥(ggAutomizer L Bs))
    have hfK' : Function.Injective fK' := by
      intro x y hxy
      exact fK.injective (Subtype.ext hxy)
    have hfL' : Function.Injective fL' := by
      intro x y hxy
      exact fL.injective (Subtype.ext hxy)
    refine l05nBL_order_eq_of_simple_map_eq fK' fL' hfK' hfL'
      (Sum.inl i) (Sum.inl j) i.1 j.1 ?_ ?_
    · change (fK (MK.simple (Sum.inl i)) : MulAut ↥Bs) =
        (fL (ML.simple i.1) : MulAut ↥Bs)
      exact (hfK (Sum.inl i)).trans (hfL i.1).symm
    · change (fK (MK.simple (Sum.inl j)) : MulAut ↥Bs) =
        (fL (ML.simple j.1) : MulAut ↥Bs)
      exact (hfK (Sum.inl j)).trans (hfL j.1).symm
  let S' : Finset ({i : Λ // i ∉ S} ⊕ Λa) :=
    Finset.univ.image (Sum.inr : Λa → ({i : Λ // i ∉ S} ⊕ Λa))
  let C' : Type := {x : ({i : Λ // i ∉ S} ⊕ Λa) // x ∉ S'}
  let A' : Type := {i : Λ // i ∈ S}
  have hS'card : S'.card = Nat.card Λa := by
    change (Finset.univ.image (Sum.inr : Λa → ({i : Λ // i ∉ S} ⊕ Λa))).card =
      Nat.card Λa
    rw [Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ,
      Nat.card_eq_fintype_card]
  have hA'card : Nat.card A' = S.card := by
    change Nat.card {i : Λ // i ∈ S} = S.card
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp
  let eC : C' ≃ {i : Λ // i ∉ S} :=
    { toFun := fun x =>
        match hx : x.1 with
        | Sum.inl c => c
        | Sum.inr a => False.elim (x.2 (by
            rw [hx]
            exact Finset.mem_image_of_mem _ (Finset.mem_univ a)))
      invFun := fun c => ⟨Sum.inl c, by simp [S']⟩
      left_inv := by
        intro x
        rcases x with ⟨o, ho⟩
        cases o with
        | inl c => apply Subtype.ext; rfl
        | inr a => exact False.elim (ho (by simp [S']))
      right_inv := by
        intro c
        rfl }
  let e2 : C' ⊕ A' ≃ Λ :=
    { toFun := fun o =>
        match o with
        | Sum.inl x => (eC x).1
        | Sum.inr s => s.1
      invFun := fun i =>
        if hi : i ∈ S then Sum.inr ⟨i, hi⟩
        else Sum.inl (eC.symm ⟨i, hi⟩)
      left_inv := by
        intro o
        cases o with
        | inl x =>
            have hx : (eC x).1 ∉ S := (eC x).2
            dsimp only
            rw [dif_neg hx]
            apply congrArg Sum.inl
            have hsub : (⟨(eC x).1, hx⟩ : {i : Λ // i ∉ S}) = eC x := Subtype.ext rfl
            rw [hsub, Equiv.symm_apply_apply]
        | inr s =>
            simp only [dif_pos s.2]
            apply congrArg Sum.inr
            apply Subtype.ext
            rfl
      right_inv := by
        intro i
        by_cases hi : i ∈ S
        · simp only [dif_pos hi]
        · simp only [dif_neg hi]
          rw [Equiv.apply_symm_apply] }
  let eT : ({i : Λ // i ∉ S} ⊕ Λa) ⊕ A' → Λ ⊕ Λa :=
    fun o =>
      match o with
      | Sum.inl (Sum.inl c) => Sum.inl c.1
      | Sum.inl (Sum.inr a) => Sum.inr a
      | Sum.inr s => Sum.inl s.1
  have eT_inl : ∀ i : {i : Λ // i ∉ S} ⊕ Λa,
      eT (Sum.inl i) = i.map Subtype.val id := by
    intro i
    cases i <;> rfl
  have eT_inl_C' : ∀ x : C', eT (Sum.inl x.1) = Sum.inl (eC x).1 := by
    intro x
    rcases x with ⟨o, ho⟩
    cases o with
    | inl c => rfl
    | inr a => exact False.elim (ho (by simp [S']))
  have eT_inr_A' : ∀ s : A', eT (Sum.inr s) = Sum.inl s.1 := fun s => rfl
  have hmap_e2 : ∀ o : C' ⊕ A', eT (o.map Subtype.val id) = Sum.inl (e2 o) := by
    intro o
    cases o with
    | inl x =>
        show eT (Sum.inl x.1) = Sum.inl (e2 (Sum.inl x))
        rw [eT_inl_C']
        rfl
    | inr s =>
        show eT (Sum.inr s) = Sum.inl (e2 (Sum.inr s))
        rw [eT_inr_A']
        rfl
  let CK' : Matrix (C' ⊕ A') (C' ⊕ A') ℤ := fun o o' => CL (e2 o) (e2 o')
  have hWMK' : GGIsWeylMatrix (ML.reindex e2.symm) :=
    l05nBL_weyl_reindex hWML e2.symm
  have hCKK' : GGIntCartan (ML.reindex e2.symm) CK' :=
    l05nBL_intCartan_reindex hCLL e2
  have hlin' : ∀ o w, ggLin (p := p) ι ((fun o => φ (eT o)) o) w =
      w - ((fun o => α (eT o)) o) w • ((fun o => h (eT o)) o) := by
    intro o w
    exact hlin (eT o) w
  have hrefl' : ∀ o, GGIsReflection p ((fun o => φ (eT o)) o) := by
    intro o
    exact hrefl (eT o)
  have hpairLL' : ∀ i j : {i : Λ // i ∉ S} ⊕ Λa,
      (fun o => α (eT o)) (Sum.inl i) ((fun o => h (eT o)) (Sum.inl j)) =
        (CK i j : ZMod p) := by
    intro i j
    simpa only [eT_inl] using hpairK i j
  have hpairCK' : ∀ o o' : C' ⊕ A',
      (fun o => α (eT o)) (o.map Subtype.val id)
        ((fun o => h (eT o)) (o'.map Subtype.val id)) = (CK' o o' : ZMod p) := by
    intro o o'
    change α (eT (o.map Subtype.val id)) (h (eT (o'.map Subtype.val id))) =
      (CK' o o' : ZMod p)
    rw [hmap_e2 o, hmap_e2 o']
    cases o with
    | inl x =>
        cases o' with
        | inl y =>
            show α (Sum.inl (e2 (Sum.inl x))) (h (Sum.inl (e2 (Sum.inl y)))) =
              (CK' (Sum.inl x) (Sum.inl y) : ZMod p)
            rw [show e2 (Sum.inl x) = (eC x).1 from rfl,
              show e2 (Sum.inl y) = (eC y).1 from rfl]
            exact hpairL (eC x).1 (eC y).1
        | inr s =>
            show α (Sum.inl (e2 (Sum.inl x))) (h (Sum.inl (e2 (Sum.inr s)))) =
              (CK' (Sum.inl x) (Sum.inr s) : ZMod p)
            rw [show e2 (Sum.inl x) = (eC x).1 from rfl,
              show e2 (Sum.inr s) = s.1 from rfl]
            exact hpairL (eC x).1 s.1
    | inr s =>
        cases o' with
        | inl y =>
            show α (Sum.inl (e2 (Sum.inr s))) (h (Sum.inl (e2 (Sum.inl y)))) =
              (CK' (Sum.inr s) (Sum.inl y) : ZMod p)
            rw [show e2 (Sum.inr s) = s.1 from rfl,
              show e2 (Sum.inl y) = (eC y).1 from rfl]
            exact hpairL s.1 (eC y).1
        | inr t =>
            show α (Sum.inl (e2 (Sum.inr s))) (h (Sum.inl (e2 (Sum.inr t)))) =
              (CK' (Sum.inr s) (Sum.inr t) : ZMod p)
            rw [show e2 (Sum.inr s) = s.1 from rfl,
              show e2 (Sum.inr t) = t.1 from rfl]
            exact hpairL s.1 t.1
  have hclosK' : ggAutomizer K Bs = Subgroup.closure
      (Set.range fun i : {i : Λ // i ∉ S} ⊕ Λa => (fun o => φ (eT o)) (Sum.inl i)) := by
    rw [hclosK]
    congr 1
    ext γ
    constructor
    · rintro (h | h)
      · rcases h with ⟨c, rfl⟩
        exact ⟨Sum.inl c, rfl⟩
      · rcases h with ⟨a, rfl⟩
        exact ⟨Sum.inr a, rfl⟩
    · rintro ⟨i, rfl⟩
      cases i with
      | inl c => exact Or.inl ⟨c, rfl⟩
      | inr a => exact Or.inr ⟨a, rfl⟩
  have hclosJ' : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : C' => (fun o => φ (eT o)) (Sum.inl j)) := by
    rw [hclosJ]
    congr 1
    ext γ
    constructor
    · rintro ⟨c, rfl⟩
      refine ⟨eC.symm c, ?_⟩
      show φ (eT (Sum.inl (eC.symm c))) = φ (Sum.inl c)
      rw [eT_inl_C' (eC.symm c), Equiv.apply_symm_apply]
    · rintro ⟨j, rfl⟩
      refine ⟨eC j, ?_⟩
      simp only [eT_inl_C' j]
  have hclosL' : ggAutomizer L Bs = Subgroup.closure
      (Set.range (fun j : C' => (fun o => φ (eT o)) (Sum.inl j)) ∪
        Set.range fun a : A' => (fun o => φ (eT o)) (Sum.inr a)) := by
    rw [hclosL]
    congr 1
    have hsum : Set.range (fun o : C' ⊕ A' => (fun o => φ (eT o)) (o.map Subtype.val id)) =
        Set.range (fun j : C' => (fun o => φ (eT o)) (Sum.inl j)) ∪
          Set.range fun a : A' => (fun o => φ (eT o)) (Sum.inr a) := by
      ext γ
      constructor
      · rintro ⟨o, rfl⟩
        cases o with
        | inl j => exact Or.inl ⟨j, rfl⟩
        | inr a => exact Or.inr ⟨a, rfl⟩
      · rintro (h | h)
        · rcases h with ⟨j, rfl⟩
          exact ⟨Sum.inl j, rfl⟩
        · rcases h with ⟨a, rfl⟩
          exact ⟨Sum.inr a, rfl⟩
    have hrange : Set.range (fun o : C' ⊕ A' => (fun o => φ (eT o)) (o.map Subtype.val id)) =
        Set.range (fun i : Λ => φ (Sum.inl i)) := by
      ext γ
      constructor
      · rintro ⟨o, rfl⟩
        refine ⟨e2 o, ?_⟩
        change φ (Sum.inl (e2 o)) = φ (eT (o.map Subtype.val id))
        rw [hmap_e2 o]
      · rintro ⟨i, rfl⟩
        refine ⟨e2.symm i, ?_⟩
        change φ (eT ((e2.symm i).map Subtype.val id)) = φ (Sum.inl i)
        rw [hmap_e2 (e2.symm i), Equiv.apply_symm_apply]
    rw [← hrange, hsum]
  have hdel' : GGDeletedConnectedS MK S' := by
    intro x y
    have h := l05nBL_rtg_map
      (r := fun u v : {i : Λ // i ∉ S} => u ≠ v ∧ ML.M u.1 v.1 ≠ 2)
      (p := fun u v : C' => u ≠ v ∧ MK.M u v ≠ 2)
      (f := fun c : {i : Λ // i ∉ S} => eC.symm c)
      (fun u v huv => by
        refine ⟨?_, ?_⟩
        · intro hh; exact huv.1 (eC.symm.injective hh)
        · rw [show MK.M (eC.symm u) (eC.symm v) = ML.M u.1 v.1 from hMKML u v]
          simpa using huv.2)
      (hdel (eC x) (eC y))
    simpa using h
  refine ⟨{i : Λ // i ∉ S} ⊕ Λa, inferInstance, inferInstance, S', A', inferInstance,
    inferInstance, MK, CK, ML.reindex e2.symm, CK', V, inferInstance, inferInstance, ι,
    (fun o => φ (eT o)), (fun o => h (eT o)), (fun o => α (eT o)),
    hS'card, ?_, ?_, hWMK, hCKK, hWMK', hCKK', trivial, hlin', hrefl', hpairLL',
    hpairCK', trivial, ?_, ?_, hclosK', hclosL', hdel', hclosJ'⟩
  · omega
  · omega
  · refine ⟨fK, fun o => ?_⟩
    change (fK (MK.simple o) : MulAut ↥Bs) = φ (eT (Sum.inl o))
    rw [eT_inl]
    exact hfK o
  ·
    refine ⟨(ML.reindexGroupEquiv e2.symm).trans fL, ?_⟩
    intro o
    have h := hfL (e2 o)
    change fL ((ML.reindexGroupEquiv e2.symm) ((ML.reindex e2.symm).simple o)) =
      φ (eT (o.map Subtype.val id))
    rw [CoxeterMatrix.reindexGroupEquiv_apply_simple]
    rw [show (e2.symm).symm = e2 from rfl]
    rw [h, hmap_e2 o]

theorem ggResTwoNodeDatum_of_exact2_not_exact3_reverse {G : Type} [Group G]
    {p : ℕ} [Fact p.Prime] {Bs L J K : Subgroup G}
    (h2 : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny)
    (h3 : ¬ GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) :
    GGResTwoNodeDatum p Bs L J K ggSelAny ggTypAny := by
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS2, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    hfLx, hfKx, hclosL, hclosK, hdel, hclosJ⟩ := h2
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  have hrev : GGResLeviDatumCard (Nat.card Λa) p Bs K J L ggSelAny ggTypAny :=
    ggResLeviDatumCard_reverse_of_witness (S := S) (by omega) (by omega)
      hWML hCLL hWMK hCKK hlin hrefl hpairL hpairK hfLx hfKx hclosL hclosK hdel hclosJ
  obtain ⟨fL, hfL⟩ := hfLx
  obtain ⟨fK, hfK⟩ := hfKx
  have hAle2 : Nat.card Λa ≤ 2 := by
    by_contra hle
    have hAeq3 : Nat.card Λa = 3 := by omega
    have hrev3 : GGResLeviDatumCard 3 p Bs K J L ggSelAny ggTypAny := by
      rw [← hAeq3]
      exact hrev
    exact h3 (by simpa [GGResLeviDatumExact3] using hrev3)
  obtain ⟨b₁, b₂, hbne, hS⟩ := Finset.card_eq_two.mp hS2
  let C2 : Type := {i : Λ // i ≠ b₁ ∧ i ≠ b₂}
  let eC2 : {i : Λ // i ∉ S} ≃ C2 :=
    { toFun := fun x => ⟨x.1, by
        have hx : x.1 ∉ ({b₁, b₂} : Finset Λ) := by simpa [hS] using x.2
        simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hx⟩
      invFun := fun x => ⟨x.1, by
        have hx : x.1 ∉ ({b₁, b₂} : Finset Λ) := by
          simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using x.2
        simpa [hS] using hx⟩
      left_inv := fun x => by apply Subtype.ext; rfl
      right_inv := fun x => by apply Subtype.ext; rfl }
  let e2C : ({i : Λ // i ∉ S} ⊕ Λa) ≃ (C2 ⊕ Λa) :=
    eC2.sumCongr (Equiv.refl Λa)
  let CK2 : Matrix (C2 ⊕ Λa) (C2 ⊕ Λa) ℤ := fun o o' => CK (e2C.symm o) (e2C.symm o')
  have hWMK2 : GGIsWeylMatrix (MK.reindex e2C) := l05nBL_weyl_reindex hWMK e2C
  have hCKK2 : GGIntCartan (MK.reindex e2C) CK2 := l05nBL_intCartan_reindex hCKK e2C.symm
  have hpairK2 : ∀ o o' : C2 ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK2 o o' : ZMod p) := by
    intro o o'
    have hmap : o.map Subtype.val id = (e2C.symm o).map Subtype.val id := by
      cases o with
      | inl x => rfl
      | inr a => rfl
    have hmap' : o'.map Subtype.val id = (e2C.symm o').map Subtype.val id := by
      cases o' with
      | inl x => rfl
      | inr a => rfl
    rw [hmap, hmap']
    exact hpairK (e2C.symm o) (e2C.symm o')
  have hdel2 : GGDeletedConnected2 ML b₁ b₂ := by
    intro i j
    have h := l05nBL_rtg_map
      (r := fun u v : {i : Λ // i ∉ S} => u ≠ v ∧ ML.M u v ≠ 2)
      (p := fun u v : C2 => u ≠ v ∧ ML.M u.1 v.1 ≠ 2)
      (f := fun c : {i : Λ // i ∉ S} => eC2 c)
      (fun u v huv => by
        refine ⟨?_, ?_⟩
        · intro hh; exact huv.1 (eC2.injective hh)
        · have hu : (eC2 u).1 = u.1 := rfl
          have hv : (eC2 v).1 = v.1 := rfl
          simpa only [hu, hv] using huv.2)
      (hdel (eC2.symm i) (eC2.symm j))
    simpa using h
  have hclosK2 : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : C2 => φ (Sum.inl j)) ∪ Set.range fun a : Λa => φ (Sum.inr a)) := by
    rw [hclosK]
    congr 1
    ext γ
    constructor
    · rintro (⟨j, rfl⟩ | ⟨a, rfl⟩)
      · exact Or.inl ⟨eC2 j, rfl⟩
      · exact Or.inr ⟨a, rfl⟩
    · rintro (⟨j, rfl⟩ | ⟨a, rfl⟩)
      · exact Or.inl ⟨eC2.symm j, rfl⟩
      · exact Or.inr ⟨a, rfl⟩
  have hclosJ2 : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : C2 => φ (Sum.inl j)) := by
    rw [hclosJ]
    congr 1
    ext γ
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨eC2 j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨eC2.symm j, rfl⟩
  refine ⟨Λ, i1, i2, b₁, b₂, Λa, i3, i4, ML, CL, MK.reindex e2C, CK2,
    V, i5, i6, ι, φ, h, α, hbne, hA1, hAle2, hWML, hCLL, hWMK2, hCKK2, trivial,
    hlin, hrefl, hpairL, hpairK2, trivial, ⟨fL, hfL⟩, ?_, hclosL, hclosK2, hdel2, hclosJ2⟩
  · refine ⟨(MK.reindexGroupEquiv e2C).trans fK, ?_⟩
    intro o
    change fK ((MK.reindexGroupEquiv e2C) ((MK.reindex e2C).simple o)) =
      φ (o.map Subtype.val id)
    rw [CoxeterMatrix.reindexGroupEquiv_apply_simple]
    rw [show (o.map Subtype.val id) = (e2C.symm o).map Subtype.val id from by
      cases o with
      | inl x => rfl
      | inr a => rfl]
    exact hfK (e2C.symm o)


theorem ggResLeviDatumCard_reverse {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs L J K : Subgroup G} {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3)
    (hD : GGResLeviDatumCard k p Bs L J K ggSelAny ggTypAny) :
    ∃ j, 1 ≤ j ∧ j ≤ 3 ∧ GGResLeviDatumCard j p Bs K J L ggSelAny ggTypAny := by
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hcard, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    hfLx, hfKx, hclosL, hclosK, hdel, hclosJ⟩ := hD
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  refine ⟨Nat.card Λa, hA1, hA3, ?_⟩
  exact ggResLeviDatumCard_reverse_of_witness (S := S) (by omega) (by omega)
    hWML hCLL hWMK hCKK hlin hrefl hpairL hpairK hfLx hfKx hclosL hclosK hdel hclosJ

theorem ggResLeviDatumExact2_reverse_card_one_two_three {G : Type} [Group G]
    {p : ℕ} [Fact p.Prime] {Bs L J K : Subgroup G}
    (h2 : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) :
    GGResLeviDatumCard 1 p Bs K J L ggSelAny ggTypAny ∨
      GGResLeviDatumCard 2 p Bs K J L ggSelAny ggTypAny ∨
      GGResLeviDatumCard 3 p Bs K J L ggSelAny ggTypAny := by
  obtain ⟨j, hj1, hj3, hcard⟩ :=
    ggResLeviDatumCard_reverse (k := 2) (by norm_num) (by norm_num) h2
  rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl
  · exact Or.inl hcard
  · exact Or.inr (Or.inl hcard)
  · exact Or.inr (Or.inr hcard)

theorem ggResLeviDatumExact2_reverse_card_one_two_of_not_exact3 {G : Type} [Group G]
    {p : ℕ} [Fact p.Prime] {Bs L J K : Subgroup G}
    (h2 : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny)
    (h3 : ¬ GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) :
    GGResLeviDatumCard 1 p Bs K J L ggSelAny ggTypAny ∨
      GGResLeviDatumCard 2 p Bs K J L ggSelAny ggTypAny := by
  obtain ⟨j, hj1, hj3, hcard⟩ :=
    ggResLeviDatumCard_reverse (k := 2) (by norm_num) (by norm_num) h2
  have hjne : j ≠ 3 := by
    rintro rfl
    exact h3 (by simpa [GGResLeviDatumExact3] using hcard)
  rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl
  · exact Or.inl hcard
  · exact Or.inr hcard



open CFSG.Monster.B.Geometry

theorem l05nBL_ggIsWeylMatrix_dynkinType_reindex {t : TauCeti.DynkinType} (ht : t.Valid) {ι : Type}
    (e : Fin t.rank ≃ ι) : GGIsWeylMatrix (t.coxeterMatrix.reindex e) := by
  cases t with
  | A n =>
      have hn : 1 ≤ n := by simpa [TauCeti.DynkinType.valid_A] using ht
      rw [TauCeti.DynkinType.coxeterMatrix_A]
      exact l05nBL_weyl_reindex (Or.inl ⟨n, Equiv.refl (Fin n), hn, Or.inl rfl⟩) e
  | B n =>
      have hn : 2 ≤ n := by simpa [TauCeti.DynkinType.valid_B] using ht
      rw [TauCeti.DynkinType.coxeterMatrix_B]
      exact l05nBL_weyl_reindex (Or.inl ⟨n, Equiv.refl (Fin n), by omega, Or.inr (Or.inl ⟨hn, rfl⟩)⟩) e
  | C n =>
      have hn : 3 ≤ n := by simpa [TauCeti.DynkinType.valid_C] using ht
      rw [TauCeti.DynkinType.coxeterMatrix_C]
      exact l05nBL_weyl_reindex (Or.inl ⟨n, Equiv.refl (Fin n), by omega, Or.inr (Or.inl ⟨by omega, rfl⟩)⟩) e
  | D n =>
      have hn : 4 ≤ n := by simpa [TauCeti.DynkinType.valid_D] using ht
      have hD : (TauCeti.DynkinType.D n).coxeterMatrix =
          ggCoxeterMatrixD (TauCeti.DynkinType.D n).rank := by
        ext i j
        by_cases hij : i = j
        · subst hij
          rw [ggCoxeterMatrixD_apply (TauCeti.DynkinType.D n).rank i i]
          rw [if_pos rfl]
          exact CoxeterMatrix.diagonal (TauCeti.DynkinType.D n).coxeterMatrix i
        · rw [TauCeti.DynkinType.coxeterMatrix_D_apply n hij]
          rw [ggCoxeterMatrixD_apply (TauCeti.DynkinType.D n).rank i j]
          rw [if_neg hij]
          rfl
      have hnr : 4 ≤ (TauCeti.DynkinType.D n).rank := by simpa using hn
      rw [hD]
      exact l05nBL_weyl_reindex
        (Or.inl ⟨(TauCeti.DynkinType.D n).rank, Equiv.refl _, by omega,
          Or.inr (Or.inr ⟨hnr, rfl⟩)⟩) e
  | E6 =>
      rw [TauCeti.DynkinType.coxeterMatrix_E6]
      exact l05nBL_weyl_reindex (Or.inr (Or.inl ⟨Equiv.refl (Fin 6), rfl⟩)) e
  | E7 =>
      rw [TauCeti.DynkinType.coxeterMatrix_E7]
      exact l05nBL_weyl_reindex (Or.inr (Or.inr (Or.inl ⟨Equiv.refl (Fin 7), rfl⟩))) e
  | E8 =>
      rw [TauCeti.DynkinType.coxeterMatrix_E8]
      exact l05nBL_weyl_reindex (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl (Fin 8), rfl⟩)))) e
  | F4 =>
      rw [TauCeti.DynkinType.coxeterMatrix_F4]
      exact l05nBL_weyl_reindex (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl (Fin 4), rfl⟩))))) e
  | G2 =>
      rw [TauCeti.DynkinType.coxeterMatrix_G2]
      exact l05nBL_weyl_reindex (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Equiv.refl (Fin 2), rfl⟩))))) e

noncomputable def l05nBL_parEquiv {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W]
    (cs : CoxeterSystem M W) (J : Set ι) :
    (parMatrix M J).Group ≃* cs.parabolic J :=
{ toFun := parToPar cs J
  invFun := parOfGroup cs J
  left_inv := parOfGroup_parToPar cs J
  right_inv := fun w => Subtype.ext (parToGroup_parOfGroup cs J w)
  map_mul' := map_mul (parToPar cs J) }

theorem l05nBL_ggIsWeylMatrix_parMatrix_of_deletedConnected {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (S : Finset Λ) (ML : CoxeterMatrix Λ) (CL : Matrix Λ Λ ℤ)
    (hW : GGIsWeylMatrix ML) (hC : GGIntCartan ML CL)
    (hdel : GGDeletedConnectedS ML S)
    (hne : Nonempty {i : Λ // i ∉ S}) :
    GGIsWeylMatrix (parMatrix ML {i | i ∉ S}) := by
  classical
  let T : Set Λ := {i | i ∉ S}
  let eT : T → Λ := Subtype.val
  have hFT : TauCeti.IsFiniteType CL := isFiniteType_of_ggIsWeylMatrixFixed hW hC
  have hFTT : TauCeti.IsFiniteType (CL.submatrix eT eT) := hFT.submatrix Subtype.val_injective
  have hCTT : GGIntCartan (parMatrix ML T) (CL.submatrix eT eT) := by
    constructor
    · intro i
      exact hC.1 i.1
    · intro i j hij
      have hij' : (i : Λ) ≠ j := fun h => hij (Subtype.ext h)
      have h := hC.2 i.1 j.1 hij'
      simpa [parMatrix, Matrix.submatrix_apply] using h
  have hMeq : CFSG.LieType.RootSystem.coxeterMatrix hFTT = parMatrix ML T :=
    coxeterMatrix_eq_of_ggIntCartan hFTT hCTT
  have hconn : (TauCeti.diagramGraph (CL.submatrix eT eT)).Connected := by
    have hpre : (TauCeti.diagramGraph (CL.submatrix eT eT)).Preconnected := by
      intro i j
      have h := l05nBL_rtg_map (p := (TauCeti.diagramGraph (CL.submatrix eT eT)).Adj) id
        (fun u v huv => by
          rw [TauCeti.IsFiniteType.diagramGraph_adj_iff hFTT]
          exact ⟨huv.1, by
            rw [Matrix.submatrix_apply]
            have huv' : (u : Λ) ≠ v := fun h => huv.1 (Subtype.ext h)
            exact fun h0 => huv.2 ((l05nBL_cartan_eq_zero_iff hC huv').mp h0)⟩) (hdel i j)
      simpa [SimpleGraph.reachable_iff_reflTransGen] using h
    exact (SimpleGraph.connected_iff _).2 ⟨hpre, hne⟩
  obtain ⟨t, ⟨ht, e, hA⟩, -⟩ := hFTT.existsUnique_dynkinType hconn
  have hcox : CFSG.LieType.RootSystem.coxeterMatrix hFTT = t.coxeterMatrix.reindex e.symm := by
    ext i j
    rw [show (CFSG.LieType.RootSystem.coxeterMatrix hFTT).M i j =
        TauCeti.coxeterOrder ((CL.submatrix eT eT) i j * (CL.submatrix eT eT) j i) by
      simp only [CFSG.LieType.RootSystem.coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply]]
    rw [CoxeterMatrix.reindex_apply, TauCeti.DynkinType.coxeterMatrix_apply]
    rw [hA i j, hA j i]
    simp only [Equiv.symm_symm]
  have hmat : parMatrix ML T = t.coxeterMatrix.reindex e.symm := by
    rw [← hMeq, hcox]
  rw [hmat]
  exact l05nBL_ggIsWeylMatrix_dynkinType_reindex ht e.symm

noncomputable def ggParabolic_equiv_of_generator_equiv
    {Λ H : Type*} [Group H] (M : CoxeterMatrix Λ) {X J : Subgroup H}
    (T : Set Λ) (φ : Λ → H) (f : M.Group ≃* ↥X)
    (hf : ∀ i, (f (M.simple i) : H) = φ i)
    (hJ : J = Subgroup.closure (Set.range fun i : T => φ i)) :
    (parMatrix M T).Group ≃* ↥J := by
  let cs := M.toCoxeterSystem
  have hmem : ∀ w : cs.parabolic T, (f (w : M.Group) : H) ∈ J := by
    have hle : cs.parabolic T ≤ Subgroup.comap (X.subtype.comp f.toMonoidHom) J := by
      rw [cs.parabolic_le_iff]
      intro i hi
      change (f (M.simple i) : H) ∈ J
      rw [hf i, hJ]
      exact Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩
    intro w
    exact hle w.2
  let g : cs.parabolic T →* ↥J :=
    { toFun := fun w => ⟨(f (w : M.Group) : H), hmem w⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp [map_mul] }
  have hginj : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    apply f.injective
    apply Subtype.ext
    exact congrArg (fun j : ↥J => (j : H)) hab
  have hgsurj : Function.Surjective g := by
    intro a
    have hclosure : Subgroup.closure (Set.range fun i : T => φ i) ≤
        Subgroup.map (J.subtype.comp g) ⊤ := by
      refine (Subgroup.closure_le _).2 ?_
      rintro b ⟨i, rfl⟩
      refine ⟨⟨cs.simple i, cs.simple_mem_parabolic i.2⟩, Subgroup.mem_top _, ?_⟩
      change (f (M.simple i) : H) = φ i
      exact hf i
    obtain ⟨w, -, hw⟩ := hJ.le.trans hclosure a.2
    exact ⟨w, Subtype.ext hw⟩
  exact (l05nBL_parEquiv cs T).trans (MulEquiv.ofBijective g ⟨hginj, hgsurj⟩)

theorem ggResLeviDatumCard_weylTypeData
    {G : Type} [Group G] [Finite G]
    {p k : ℕ} [Fact p.Prime] {Bs X J Y : Subgroup G}
    (hD : GGResLeviDatumCard k p Bs X J Y ggSelAny ggTypAny)
    (hJ : ggAutomizer J Bs ≠ ⊥) :
    ∃ r : ℕ,
      GGWeylTypeData (r + k) (Nat.card ↥(ggAutomizer X Bs))
        (Nat.card ↥(Subgroup.center ↥(ggAutomizer X Bs))) ∧
      GGWeylTypeData r (Nat.card ↥(ggAutomizer J Bs))
        (Nat.card ↥(Subgroup.center ↥(ggAutomizer J Bs))) := by
  classical
  rcases hD with ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, -, -, hML, hCL, -, -, -, -, -, -, -, -, ⟨fL, hfL⟩, -, -, -, hconn, hclosJ⟩
  let := i1
  let := i2
  let T : Set Λ := {i | i ∉ S}
  have hT : Nonempty T := by
    by_contra he
    have hrange : Set.range (fun j : T => φ (Sum.inl j)) = ∅ := by
      rw [Set.range_eq_empty_iff]
      exact not_nonempty_iff.mp he
    apply hJ
    rw [hclosJ]
    change Subgroup.closure (Set.range fun j : T => φ (Sum.inl j)) = ⊥
    rw [hrange, Subgroup.closure_empty]
  let eJ : (parMatrix ML T).Group ≃* ↥(ggAutomizer J Bs) :=
    ggParabolic_equiv_of_generator_equiv ML T (fun i => φ (Sum.inl i)) fL hfL hclosJ
  have hMJ : GGIsWeylMatrix (parMatrix ML T) :=
    l05nBL_ggIsWeylMatrix_parMatrix_of_deletedConnected S ML CL hML hCL hconn hT
  have hfull := ggWeylTypeData_of_isWeylMatrix hML
  have hsurv := ggWeylTypeData_of_isWeylMatrix hMJ
  have hcard : Fintype.card T + k = Fintype.card Λ := by
    have hle := S.card_le_univ
    have hsub : Fintype.card {i : Λ // i ∈ S} = S.card := by
      rw [Fintype.card_subtype]
      simp
    have hcomp : Fintype.card T = Fintype.card Λ - S.card := by
      change Fintype.card {i : Λ // i ∉ S} = Fintype.card Λ - S.card
      rw [Fintype.card_subtype_compl (fun i : Λ => i ∈ S), hsub]
    omega
  refine ⟨Fintype.card T, ?_, ?_⟩
  · rw [hcard, ← Nat.card_congr fL.toEquiv,
      ← Nat.card_congr (Subgroup.centerCongr fL).toEquiv]
    exact hfull
  · rw [← Nat.card_congr eJ.toEquiv,
      ← Nat.card_congr (Subgroup.centerCongr eJ).toEquiv]
    exact hsurv

theorem ggResLeviDatumCard_rank_eq_of_weylTypeData
    {G : Type} [Group G] [Finite G]
    {p k n c : ℕ} [Fact p.Prime] {Bs X J Y : Subgroup G}
    (hD : GGResLeviDatumCard k p Bs X J Y ggSelAny ggTypAny)
    (hJ : ggAutomizer J Bs ≠ ⊥)
    (hX : GGWeylTypeData n (Nat.card ↥(ggAutomizer X Bs)) c) :
    ∃ r : ℕ, r + k = n ∧
      GGWeylTypeData r (Nat.card ↥(ggAutomizer J Bs))
        (Nat.card ↥(Subgroup.center ↥(ggAutomizer J Bs))) := by
  obtain ⟨r, hfull, hsurv⟩ := ggResLeviDatumCard_weylTypeData hD hJ
  exact ⟨r, ggWeylTypeData_rank_eq hfull hX, hsurv⟩

theorem ggResLeviDatumCard_card_eq_of_same_base
    {G : Type} [Group G] [Finite G]
    {p k k' : ℕ} [Fact p.Prime] {Bs X J Y Y' : Subgroup G}
    (hD : GGResLeviDatumCard k p Bs X J Y ggSelAny ggTypAny)
    (hD' : GGResLeviDatumCard k' p Bs X J Y' ggSelAny ggTypAny)
    (hJ : ggAutomizer J Bs ≠ ⊥) : k = k' := by
  obtain ⟨r, hfull, hsurv⟩ := ggResLeviDatumCard_weylTypeData hD hJ
  obtain ⟨r', hfull', hsurv'⟩ := ggResLeviDatumCard_weylTypeData hD' hJ
  have hfullEq := ggWeylTypeData_rank_eq hfull hfull'
  have hsurvEq := ggWeylTypeData_rank_eq hsurv hsurv'
  omega

theorem ggRes_typeA_deletedS_card_automizer
    {G : Type} [Group G] {Bs X J : Subgroup G} {Λ : Type}
    [Fintype Λ] [DecidableEq Λ] {r k : ℕ} (hr : k < r) (e : Fin r ≃ Λ) (S : Finset Λ)
    (hS : S.card = k) (hconn : GGDeletedConnectedS ((CoxeterMatrix.A r).reindex e) S)
    (φ : Λ → MulAut Bs)
    (f : ((CoxeterMatrix.A r).reindex e).Group ≃* ggAutomizer X Bs)
    (hf : ∀ i, (f (((CoxeterMatrix.A r).reindex e).simple i) : MulAut Bs) = φ i)
    (hclosJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun i : {i : Λ // i ∉ S} => φ i.val)) :
    Nat.card (ggAutomizer J Bs) = (r - k + 1).factorial := by
  classical
  let M : CoxeterMatrix Λ := (CoxeterMatrix.A r).reindex e
  let Tset : Set Λ := {i | i ∉ S}
  let eSurv : (parMatrix M Tset).Group ≃* ggAutomizer J Bs :=
    ggParabolic_equiv_of_generator_equiv M Tset φ f hf hclosJ
  obtain ⟨eS, heS⟩ := ggChainA_deletedS_coxeter (n := r) (k := k) hr e S hS hconn
  have hmat : parMatrix M Tset = (CoxeterMatrix.A (r - k)).reindex eS.symm := by
    ext i j
    rw [CoxeterMatrix.reindex_apply, parMatrix_apply, heS i j]
    simp
  calc Nat.card (ggAutomizer J Bs)
      = Nat.card (parMatrix M Tset).Group := (Nat.card_congr eSurv.toEquiv).symm
    _ = Nat.card ((CoxeterMatrix.A (r - k)).reindex eS.symm).Group := by rw [hmat]
    _ = Nat.card (CoxeterMatrix.A (r - k)).Group :=
        Nat.card_congr
          (CoxeterMatrix.reindexGroupEquiv (CoxeterMatrix.A (r - k)) eS.symm).toEquiv
    _ = (r - k + 1).factorial := l05nK3a_card_coxeterA (r - k)

theorem not_ggResSideDatum_of_ggResLeviDatumCard_of_two_le
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X J Y : Subgroup G}
    (hSide : GGResSideDatum p Bs X J)
    {k : ℕ} (hk : 2 ≤ k)
    (h2 : GGResLeviDatumCard k p Bs X J Y ggSelAny ggTypAny) : False := by
  classical
  unfold GGResSideDatum at hSide
  unfold GGResLeviDatumCard at h2
  rcases hSide with ⟨Λs, hΛs, hΛsd, bs, Ms, Cs, MJs, Vs, hVs, hVsd, ιs, φs, hs, αs,
    hWMs, hCMs, hWMJs, hMJsub, hlinS, hreflS, hpairS, hfS, hclosS, hfJS, hclosJS, hconjS⟩
  rcases h2 with ⟨Λe, hΛe, hΛed, Se, Λa, hΛa, hΛad, MLe, CLe, MKe, CKe, Ve, hVe, hVed,
    ιe, φe, he, αe, hSe, hΛa1, hΛa3, hWMLe, hCMLe, hWMKe, hCMKe, htyp, hlinE, hreflE,
    hpairLE, hpairKE, hselE, hfLe, hfKe, hclosLe, hclosKe, hdelE, hclosJe⟩
  let := hΛs
  let := hΛsd
  let := hΛe
  let := hΛed
  obtain ⟨fS, hfS_simple⟩ := hfS
  obtain ⟨fJS, hfJS_simple⟩ := hfJS
  obtain ⟨fLe, hfLe_simple⟩ := hfLe
  let Tset : Set Λe := {i | i ∉ Se}
  let AJ : Subgroup (MulAut ↥Bs) := ggAutomizer J Bs
  have hclosJe'' : AJ = Subgroup.closure
      (Set.range fun j : Tset => φe (Sum.inl j)) := hclosJe
  let eSurv : (parMatrix MLe Tset).Group ≃* ↥AJ :=
    ggParabolic_equiv_of_generator_equiv MLe Tset (fun j => φe (Sum.inl j))
      fLe hfLe_simple hclosJe''
  let eJ : MJs.Group ≃* (parMatrix MLe Tset).Group := fJS.trans eSurv.symm
  by_cases hT : Nonempty Tset
  · have hWS : GGIsWeylMatrix (parMatrix MLe Tset) :=
      l05nBL_ggIsWeylMatrix_parMatrix_of_deletedConnected Se MLe CLe hWMLe hCMLe hdelE hT
    have hrankFull : Fintype.card Λs = Fintype.card Λe :=
      ggWeylTypeData_rank_eq_of_mulEquiv hWMs hWMLe (fS.trans fLe.symm)
    have hrankJ : Fintype.card {j : Λs // j ≠ bs} = Fintype.card Tset :=
      ggWeylTypeData_rank_eq_of_mulEquiv hWMJs hWS eJ
    have hcardSide : Fintype.card {j : Λs // j ≠ bs} = Fintype.card Λs - 1 := by
      rw [Fintype.card_subtype_compl (fun j : Λs => j = bs), Fintype.card_subtype_eq bs]
    have hcardExact : Fintype.card Tset = Fintype.card Λe - k := by
      change Fintype.card {i : Λe // i ∉ Se} = Fintype.card Λe - k
      rw [Fintype.card_subtype_compl (fun i : Λe => i ∈ Se)]
      have hsub : Fintype.card {i : Λe // i ∈ Se} = Se.card := by
        rw [Fintype.card_subtype]
        simp
      rw [hsub, hSe]
    have hΛsPos : 1 ≤ Fintype.card Λs := Fintype.card_pos_iff.mpr ⟨bs⟩
    have hΛeTwo : 2 ≤ Fintype.card Λe := by
      have := Finset.card_le_univ Se
      omega
    omega
  · exfalso
    have hrange : Set.range (fun j : Tset => φe (Sum.inl j)) = ∅ := by
      rw [Set.range_eq_empty_iff]
      exact not_nonempty_iff.mp hT
    have hAJbot : AJ = ⊥ := by
      rw [hclosJe'', hrange]
      exact Subgroup.closure_empty
    obtain ⟨j⟩ := l05nBL_nonempty hWMJs
    have hsimple_ne : MJs.simple j ≠ 1 := by
      intro h
      have h2 : orderOf (MJs.simple j) = 2 := by
        simpa using CoxeterSystem.orderOf_simple MJs.toCoxeterSystem j
      rw [h, orderOf_one] at h2
      omega
    have hAJ_ne_bot : AJ ≠ ⊥ := by
      intro hbot
      have hmem : ((fJS (MJs.simple j) : ↥AJ) : MulAut ↥Bs) ∈
          (⊥ : Subgroup (MulAut ↥Bs)) := by
        rw [← hbot]
        exact (fJS (MJs.simple j)).2
      have h1 : fJS (MJs.simple j) = 1 := by
        apply Subtype.ext
        simpa using hmem
      exact hsimple_ne (fJS.injective (by simpa using h1))
    exact hAJ_ne_bot hAJbot

theorem not_ggResSideDatum_of_ggResLeviDatumExact2
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X J Y : Subgroup G}
    (hSide : GGResSideDatum p Bs X J)
    (h2 : GGResLeviDatumExact2 p Bs X J Y ggSelAny ggTypAny) : False := by
  exact not_ggResSideDatum_of_ggResLeviDatumCard_of_two_le hSide (by omega : 2 ≤ 2) h2

namespace HdRo7C

theorem ggResXDatum_left_of_leviLE3
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs L J K : Subgroup G}
    (hD : GGResLeviDatumLE3 p Bs L J K ggSelAny ggTypAny) :
    GGResXDatum p Bs L := by
  classical
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS2, hS3, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    hfLx, hfKx, hclosL, hclosK, hdel, hclosJ⟩ := hD
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  obtain ⟨fL, hfL⟩ := hfLx
  exact ⟨Λ, i1, i2, ML, CL, V, i5, i6, ι, (fun i => φ (Sum.inl i)),
    (fun i => h (Sum.inl i)), (fun i => α (Sum.inl i)), hWML, hCLL,
    (fun i w => hlin (Sum.inl i) w), (fun i => hrefl (Sum.inl i)),
    (fun i j => hpairL i j), ⟨fL, hfL⟩, hclosL⟩

theorem ggResXDatum_right_of_leviLE3
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs L J K : Subgroup G}
    (hD : GGResLeviDatumLE3 p Bs L J K ggSelAny ggTypAny) :
    GGResXDatum p Bs K := by
  classical
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS2, hS3, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    hfLx, hfKx, hclosL, hclosK, hdel, hclosJ⟩ := hD
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  obtain ⟨fK, hfK⟩ := hfKx
  have hgenK' : ggAutomizer K Bs =
      Subgroup.closure (Set.range fun o : {i : Λ // i ∉ S} ⊕ Λa =>
        φ (o.map Subtype.val id)) := by
    rw [hclosK, Sum.range_eq]
    rfl
  exact ⟨{i : Λ // i ∉ S} ⊕ Λa, inferInstance, inferInstance, MK, CK, V, i5, i6, ι,
    (fun o => φ (o.map Subtype.val id)), (fun o => h (o.map Subtype.val id)),
    (fun o => α (o.map Subtype.val id)), hWMK, hCKK,
    (fun o w => hlin (o.map Subtype.val id) w),
    (fun o => hrefl (o.map Subtype.val id)), (fun o o' => hpairK o o'),
    ⟨fK, hfK⟩, hgenK'⟩

theorem ggResXDatum_left_of_exact2
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs L J K : Subgroup G}
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) :
    GGResXDatum p Bs L :=
  ggResXDatum_left_of_leviLE3
    ((ggResLeviDatumLE3_iff_exact2_or_exact3 p Bs L J K ggSelAny ggTypAny).mpr (Or.inl hD))

theorem ggResXDatum_right_of_exact2
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs L J K : Subgroup G}
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) :
    GGResXDatum p Bs K :=
  ggResXDatum_right_of_leviLE3
    ((ggResLeviDatumLE3_iff_exact2_or_exact3 p Bs L J K ggSelAny ggTypAny).mpr (Or.inl hD))

end HdRo7C

private theorem e6Deletion_path_label_eq {α : Type} {r : α → α → Prop} {q : α → Bool}
    (h : ∀ a b, r a b → q a = q b) {a b : α} (hp : Relation.ReflTransGen r a b) :
    q a = q b := by
  induction hp with
  | refl => rfl
  | @tail b c _ hbc ih => exact ih.trans (h b c hbc)

private theorem e6Deletion_separated_false (a b i j : Fin 6) (q : Fin 6 → Bool)
    (hi : i ∉ ({a,b} : Finset (Fin 6))) (hj : j ∉ ({a,b} : Finset (Fin 6)))
    (hij : q i ≠ q j)
    (he : ∀ u v : {k : Fin 6 // k ∉ ({a,b} : Finset (Fin 6))},
      u ≠ v ∧ CoxeterMatrix.E₆.M u v ≠ 2 → q u = q v)
    (hc : GGDeletedConnectedS CoxeterMatrix.E₆ {a,b}) : False := by
  exact hij (e6Deletion_path_label_eq he (hc ⟨i,hi⟩ ⟨j,hj⟩))

private theorem e6Deletion_sorted_deletions (a b : Fin 6) (horder : a < b)
    (hc : GGDeletedConnectedS CoxeterMatrix.E₆ {a,b}) :
    ({a,b} : Finset (Fin 6)) = {0,1} ∨ ({a,b} : Finset (Fin 6)) = {0,2} ∨
      ({a,b} : Finset (Fin 6)) = {0,5} ∨ ({a,b} : Finset (Fin 6)) = {1,5} ∨
      ({a,b} : Finset (Fin 6)) = {4,5} := by
  fin_cases a <;> fin_cases b <;> simp_all
  · exact False.elim (e6Deletion_separated_false 0 3 1 2 (![false, true, false, false, false, false])
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hc)
  · exact False.elim (e6Deletion_separated_false 0 4 1 5 (![false, true, true, true, false, false])
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hc)
  · exact False.elim (e6Deletion_separated_false 1 2 0 3 (![true, false, false, false, false, false])
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hc)
  · exact False.elim (e6Deletion_separated_false 1 3 0 4 (![true, false, true, false, false, false])
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hc)
  · exact False.elim (e6Deletion_separated_false 1 4 0 5 (![true, false, true, true, false, false])
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hc)
  · exact False.elim (e6Deletion_separated_false 2 3 0 1 (![true, false, false, false, false, false])
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hc)
  · exact False.elim (e6Deletion_separated_false 2 4 0 1 (![true, false, false, false, false, false])
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hc)
  · exact False.elim (e6Deletion_separated_false 2 5 0 1 (![true, false, false, false, false, false])
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hc)
  · exact False.elim (e6Deletion_separated_false 3 4 0 1 (![true, false, true, false, false, false])
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hc)
  · exact False.elim (e6Deletion_separated_false 3 5 0 1 (![true, false, true, false, false, false])
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hc)

theorem ggDeletedConnectedS_E6_exact_two {S : Finset (Fin 6)} (hS : S.card = 2)
    (hc : GGDeletedConnectedS CoxeterMatrix.E₆ S) :
    S = {0,1} ∨ S = {0,2} ∨ S = {0,5} ∨ S = {1,5} ∨ S = {4,5} := by
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hS
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · exact e6Deletion_sorted_deletions a b hlt hc
  · have he : ({a,b} : Finset (Fin 6)) = {b,a} := Finset.pair_comm a b
    rw [he] at hc ⊢
    exact e6Deletion_sorted_deletions b a hlt hc

private def e6Deletion_e01 : Fin 4 ≃ {i : Fin 6 // i ∉ ({0,1} : Finset (Fin 6))} where
  toFun k := ⟨(![2, 3, 4, 5] : Fin 4 → Fin 6) k, by fin_cases k <;> decide +kernel⟩
  invFun i := (![0, 0, 0, 1, 2, 3] : Fin 6 → Fin 4) i.val
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem e6Deletion_matrix01 : parMatrix CoxeterMatrix.E₆ {i | i ∉ ({0,1} : Finset (Fin 6))} =
    (CoxeterMatrix.A 4).reindex e6Deletion_e01 := by
  apply CoxeterMatrix.ext
  decide +kernel

private def e6Deletion_e02 : Fin 4 ≃ {i : Fin 6 // i ∉ ({0,2} : Finset (Fin 6))} where
  toFun k := ⟨(![1, 3, 4, 5] : Fin 4 → Fin 6) k, by fin_cases k <;> decide +kernel⟩
  invFun i := (![0, 0, 0, 1, 2, 3] : Fin 6 → Fin 4) i.val
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem e6Deletion_matrix02 : parMatrix CoxeterMatrix.E₆ {i | i ∉ ({0,2} : Finset (Fin 6))} =
    (CoxeterMatrix.A 4).reindex e6Deletion_e02 := by
  apply CoxeterMatrix.ext
  decide +kernel

private def e6Deletion_e05 : Fin 4 ≃ {i : Fin 6 // i ∉ ({0,5} : Finset (Fin 6))} where
  toFun k := ⟨(![1, 3, 2, 4] : Fin 4 → Fin 6) k, by fin_cases k <;> decide +kernel⟩
  invFun i := (![0, 0, 2, 1, 3, 0] : Fin 6 → Fin 4) i.val
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem e6Deletion_matrix05 : parMatrix CoxeterMatrix.E₆ {i | i ∉ ({0,5} : Finset (Fin 6))} =
    (ggCoxeterMatrixD 4).reindex e6Deletion_e05 := by
  apply CoxeterMatrix.ext
  decide +kernel

private def e6Deletion_e15 : Fin 4 ≃ {i : Fin 6 // i ∉ ({1,5} : Finset (Fin 6))} where
  toFun k := ⟨(![0, 2, 3, 4] : Fin 4 → Fin 6) k, by fin_cases k <;> decide +kernel⟩
  invFun i := (![0, 0, 1, 2, 3, 0] : Fin 6 → Fin 4) i.val
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem e6Deletion_matrix15 : parMatrix CoxeterMatrix.E₆ {i | i ∉ ({1,5} : Finset (Fin 6))} =
    (CoxeterMatrix.A 4).reindex e6Deletion_e15 := by
  apply CoxeterMatrix.ext
  decide +kernel

private def e6Deletion_e45 : Fin 4 ≃ {i : Fin 6 // i ∉ ({4,5} : Finset (Fin 6))} where
  toFun k := ⟨(![0, 2, 3, 1] : Fin 4 → Fin 6) k, by fin_cases k <;> decide +kernel⟩
  invFun i := (![0, 3, 1, 2, 0, 0] : Fin 6 → Fin 4) i.val
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem e6Deletion_matrix45 : parMatrix CoxeterMatrix.E₆ {i | i ∉ ({4,5} : Finset (Fin 6))} =
    (CoxeterMatrix.A 4).reindex e6Deletion_e45 := by
  apply CoxeterMatrix.ext
  decide +kernel

theorem ggDeletedConnectedS_E6_parMatrix {S : Finset (Fin 6)} (hS : S.card = 2)
    (hc : GGDeletedConnectedS CoxeterMatrix.E₆ S) :
    (∃ e : Fin 4 ≃ {i : Fin 6 // i ∉ S},
      parMatrix CoxeterMatrix.E₆ {i | i ∉ S} = (CoxeterMatrix.A 4).reindex e) ∨
    (∃ e : Fin 4 ≃ {i : Fin 6 // i ∉ S},
      parMatrix CoxeterMatrix.E₆ {i | i ∉ S} = (ggCoxeterMatrixD 4).reindex e) := by
  rcases ggDeletedConnectedS_E6_exact_two hS hc with h | h | h | h | h
  · subst S; exact Or.inl ⟨e6Deletion_e01, e6Deletion_matrix01⟩
  · subst S; exact Or.inl ⟨e6Deletion_e02, e6Deletion_matrix02⟩
  · subst S; exact Or.inr ⟨e6Deletion_e05, e6Deletion_matrix05⟩
  · subst S; exact Or.inl ⟨e6Deletion_e15, e6Deletion_matrix15⟩
  · subst S; exact Or.inl ⟨e6Deletion_e45, e6Deletion_matrix45⟩

theorem GGDeletedConnectedS.of_reindex
    {Λ Λ' : Type} (e : Λ ≃ Λ') {M : CoxeterMatrix Λ} {S : Finset Λ'}
    (hc : GGDeletedConnectedS (M.reindex e) S) :
    GGDeletedConnectedS M (S.map e.symm.toEmbedding) := by
  classical
  let T := S.map e.symm.toEmbedding
  let eT : {i : Λ // i ∉ T} ≃ {i : Λ' // i ∉ S} :=
    { toFun := fun i => ⟨e i, by simpa [T] using i.2⟩
      invFun := fun i => ⟨e.symm i, by simpa [T] using i.2⟩
      left_inv := fun i => by ext; simp
      right_inv := fun i => by ext; simp }
  intro i j
  have hp := l05nBL_rtg_map
    (r := fun u v : {i : Λ' // i ∉ S} =>
      u ≠ v ∧ (M.reindex e).M u v ≠ 2)
    (p := fun u v : {i : Λ // i ∉ T} => u ≠ v ∧ M.M u v ≠ 2)
    eT.symm (fun u v huv => by
      refine ⟨fun h => huv.1 (eT.symm.injective h), ?_⟩
      simpa [CoxeterMatrix.reindex_apply, eT] using huv.2)
    (hc (eT i) (eT j))
  simpa using hp

theorem ggDeletedConnectedS_E6_deletion_image
    {Λ : Type} (e : Fin 6 ≃ Λ) {M : CoxeterMatrix Λ}
    (hM : M = CoxeterMatrix.E₆.reindex e) {S : Finset Λ}
    (hS : S.card = 2) (hc : GGDeletedConnectedS M S) :
    S.image e.symm = {0, 1} ∨ S.image e.symm = {0, 2} ∨
      S.image e.symm = {0, 5} ∨ S.image e.symm = {1, 5} ∨
      S.image e.symm = {4, 5} := by
  classical
  have hc' : GGDeletedConnectedS (CoxeterMatrix.E₆.reindex e) S := hM ▸ hc
  have hcard : (S.map e.symm.toEmbedding).card = 2 := by simpa using hS
  have hcases := ggDeletedConnectedS_E6_exact_two hcard
    (GGDeletedConnectedS.of_reindex e hc')
  simpa only [Finset.map_eq_image, Equiv.coe_toEmbedding] using hcases


theorem ggDeletedConnectedS_E6_parMatrix_reindex {Λ : Type} [DecidableEq Λ]
    {M : CoxeterMatrix Λ} (e : Fin 6 ≃ Λ) (hM : M = CoxeterMatrix.E₆.reindex e)
    {S : Finset Λ} (hS : S.card = 2) (hc : GGDeletedConnectedS M S) :
    (∃ f : Fin 4 ≃ {i : Λ // i ∉ S},
      parMatrix M {i | i ∉ S} = (CoxeterMatrix.A 4).reindex f) ∨
    (∃ f : Fin 4 ≃ {i : Λ // i ∉ S},
      parMatrix M {i | i ∉ S} = (ggCoxeterMatrixD 4).reindex f) := by
  classical
  let S0 := S.map e.symm.toEmbedding
  have hS0 : S0.card = 2 := by simpa [S0] using hS
  let eT : {i : Fin 6 // i ∉ S0} ≃ {i : Λ // i ∉ S} :=
    { toFun := fun i => ⟨e i, by simpa [S0] using i.2⟩
      invFun := fun i => ⟨e.symm i, by simpa [S0] using i.2⟩
      left_inv := fun i => by ext; simp
      right_inv := fun i => by ext; simp }
  have hc0 : GGDeletedConnectedS CoxeterMatrix.E₆ S0 :=
    GGDeletedConnectedS.of_reindex e (hM ▸ hc)
  have hpar : parMatrix M {i | i ∉ S} =
      (parMatrix CoxeterMatrix.E₆ {i | i ∉ S0}).reindex eT := by
    ext i j
    simp [parMatrix, hM, CoxeterMatrix.reindex_apply, eT]
  rcases ggDeletedConnectedS_E6_parMatrix hS0 hc0 with ⟨f,hf⟩ | ⟨f,hf⟩
  · left
    refine ⟨f.trans eT, ?_⟩
    rw [hpar, hf]
    ext i j
    simp [CoxeterMatrix.reindex_apply]
  · right
    refine ⟨f.trans eT, ?_⟩
    rw [hpar, hf]
    ext i j
    simp [CoxeterMatrix.reindex_apply]

theorem ggParabolic_equiv_of_generator_equiv_simple
    {Λ H : Type*} [Group H] (M : CoxeterMatrix Λ) {X J : Subgroup H}
    (f : M.Group ≃* ↥X) (φ : Λ → H)
    (hf : ∀ i, (f (M.simple i) : H) = φ i) (T : Set Λ)
    (hJ : J = Subgroup.closure (Set.range fun i : T => φ i)) (i : T) :
    (ggParabolic_equiv_of_generator_equiv M T φ f hf hJ
      ((parMatrix M T).simple i) : H) = φ i := by
  change (f (parToGroup M.toCoxeterSystem T ((parMatrix M T).simple i)) : H) = φ i
  rw [parToGroup_simple]
  exact hf i

theorem ggParabolic_E6_exact_two_actual
    {Λ H : Type} [DecidableEq Λ] [Group H] {M : CoxeterMatrix Λ}
    (e : Fin 6 ≃ Λ) (hM : M = CoxeterMatrix.E₆.reindex e)
    {S : Finset Λ} (hS : S.card = 2) (hc : GGDeletedConnectedS M S)
    {X J : Subgroup H} (f : M.Group ≃* ↥X) (φ : Λ → H)
    (hf : ∀ i, (f (M.simple i) : H) = φ i)
    (hJ : J = Subgroup.closure (Set.range fun i : {i : Λ // i ∉ S} => φ i)) :
    (∃ (a : Fin 4 ≃ {i : Λ // i ∉ S}) (g : (CoxeterMatrix.A 4).Group ≃* ↥J),
      ∀ i, (g ((CoxeterMatrix.A 4).simple i) : H) = φ (a i)) ∨
    (∃ (a : Fin 4 ≃ {i : Λ // i ∉ S}) (g : (ggCoxeterMatrixD 4).Group ≃* ↥J),
      ∀ i, (g ((ggCoxeterMatrixD 4).simple i) : H) = φ (a i)) := by
  classical
  let T : Set Λ := {i | i ∉ S}
  let jEquiv := ggParabolic_equiv_of_generator_equiv M T φ f hf hJ
  have hjEquiv (i : T) : (jEquiv ((parMatrix M T).simple i) : H) = φ i :=
    ggParabolic_equiv_of_generator_equiv_simple M f φ hf T hJ i
  have key (M0 : CoxeterMatrix (Fin 4)) (a : Fin 4 ≃ T)
      (ha : parMatrix M T = M0.reindex a) :
      ∃ g : M0.Group ≃* ↥J, ∀ i, (g (M0.simple i) : H) = φ (a i) := by
    have hx : ∃ g : (parMatrix M T).Group ≃* ↥J,
        ∀ i : T, (g ((parMatrix M T).simple i) : H) = φ i := ⟨jEquiv, hjEquiv⟩
    rw [ha] at hx
    obtain ⟨g,hg⟩ := hx
    refine ⟨(M0.reindexGroupEquiv a).symm.trans g, ?_⟩
    intro i
    have heq : (M0.reindexGroupEquiv a).symm (M0.simple i) =
        (M0.reindex a).simple (a i) := by
      apply (M0.reindexGroupEquiv a).injective
      simp [CoxeterMatrix.reindexGroupEquiv_apply_simple]
    simpa only [MulEquiv.trans_apply, heq] using hg (a i)
  rcases ggDeletedConnectedS_E6_parMatrix_reindex e hM hS hc with ⟨a,ha⟩ | ⟨a,ha⟩
  · obtain ⟨g,hg⟩ := key (CoxeterMatrix.A 4) a ha
    exact Or.inl ⟨a,g,hg⟩
  · obtain ⟨g,hg⟩ := key (ggCoxeterMatrixD 4) a ha
    exact Or.inr ⟨a,g,hg⟩

theorem ggIntCartan_coxeter_eq {Λ : Type} {M N : CoxeterMatrix Λ}
    {C : Matrix Λ Λ ℤ} (hM : GGIntCartan M C) (hN : GGIntCartan N C) : M = N := by
  ext i j
  by_cases hij : i = j
  · subst j
    rw [M.diagonal, N.diagonal]
  · rcases hM.2 i j hij with ⟨hm,a,b⟩ | ⟨hm,a,b⟩ | ⟨hm,a,-,-⟩ | ⟨hm,a,-,-⟩ <;>
      rcases hN.2 i j hij with ⟨hn,c,d⟩ | ⟨hn,c,d⟩ | ⟨hn,c,-,-⟩ | ⟨hn,c,-,-⟩ <;>
      first | exact hm.trans hn.symm | exfalso; nlinarith

theorem ggIntCartan_E6_coxeter_reindex {Λ : Type} {M : CoxeterMatrix Λ}
    {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C) (e : Fin 6 ≃ Λ)
    (he : ∀ i j, C (e i) (e j) = CartanMatrix.E 6 i j) :
    M = CoxeterMatrix.E₆.reindex e := by
  have heq : C = fun i j => CartanMatrix.E 6 (e.symm i) (e.symm j) := by
    ext i j
    simpa using he (e.symm i) (e.symm j)
  apply ggIntCartan_coxeter_eq hC
  rw [heq]
  exact l05nBL_intCartan_reindex ggIntCartan_E₆ e.symm

theorem ggParabolic_E6_exact_two_actual_card
    {Λ H : Type} [DecidableEq Λ] [Group H] {M : CoxeterMatrix Λ}
    (e : Fin 6 ≃ Λ) (hM : M = CoxeterMatrix.E₆.reindex e)
    {S : Finset Λ} (hS : S.card = 2) (hc : GGDeletedConnectedS M S)
    {X J : Subgroup H} (f : M.Group ≃* ↥X) (φ : Λ → H)
    (hf : ∀ i, (f (M.simple i) : H) = φ i)
    (hJ : J = Subgroup.closure (Set.range fun i : {i : Λ // i ∉ S} => φ i)) :
    Nat.card ↥J = 120 ∨ Nat.card ↥J = 192 := by
  rcases ggParabolic_E6_exact_two_actual e hM hS hc f φ hf hJ with
    ⟨a,g,hg⟩ | ⟨a,g,hg⟩
  · left
    rw [← Nat.card_congr g.toEquiv, l05nK3a_card_coxeterA]
    norm_num
  · right
    rw [← Nat.card_congr g.toEquiv, OrthF3.card_coxeterD_eq 4 (by omega)]
    norm_num

theorem ggResLeviDatumExact2_E6_automizerJ_card
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs X J Y : Subgroup G}
    (hD : GGResLeviDatumExact2 p Bs X J Y ggSelAny ggTypLE6) :
    Nat.card ↥(ggAutomizer J Bs) = 120 ∨ Nat.card ↥(ggAutomizer J Bs) = 192 := by
  classical
  rcases hD with ⟨Λ,i1,i2,S,Λa,i3,i4,ML,CL,MK,CK,V,i5,i6,ι,φ,h,α,
    hS,-,-,-,-,-,-,htyp,-,-,-,-,-,⟨f,hf⟩,-,-,-,hconn,hclosJ⟩
  let := i1
  let := i2
  obtain ⟨e,he⟩ := htyp
  exact ggParabolic_E6_exact_two_actual_card e he hS hconn f
    (fun i => φ (Sum.inl i)) hf hclosJ

section E6ExactThreeSurvivor

open CFSG.Monster.B.Geometry

private def GGNoMultipleEdge {Γ : Type} (M : CoxeterMatrix Γ) : Prop :=
  ∀ i j, i ≠ j → M i j ≤ 3

private theorem ggNoMultipleEdge_E6 : GGNoMultipleEdge CoxeterMatrix.E₆ := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem GGNoMultipleEdge.reindex {Γ Γ' : Type} {M : CoxeterMatrix Γ}
    (h : GGNoMultipleEdge M) (e : Γ ≃ Γ') : GGNoMultipleEdge (M.reindex e) := by
  intro i j hij
  simpa [CoxeterMatrix.reindex_apply] using
    h (e.symm i) (e.symm j) (fun hh => hij (e.symm.injective hh))

private theorem GGNoMultipleEdge.parMatrix {Γ : Type} {M : CoxeterMatrix Γ}
    (h : GGNoMultipleEdge M) (T : Set Γ) : GGNoMultipleEdge (parMatrix M T) := by
  intro i j hij
  simpa [parMatrix_apply] using h i j (fun hh => hij (Subtype.ext hh))

theorem exists_A3_reindex_of_e6_three_survivor
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hML : GGIsWeylMatrix ML) (hCL : GGIntCartan ML CL) (hE6 : GGIsTypeE6 ML)
    {S : Finset Λ} (hS : S.card = 3) (hconn : GGDeletedConnectedS ML S) :
    ∃ e : Fin 3 ≃ {i : Λ // i ∉ S},
      parMatrix ML {i | i ∉ S} = (CoxeterMatrix.A 3).reindex e := by
  classical
  obtain ⟨e6, he6⟩ := hE6
  have hcardΛ : Fintype.card Λ = 6 := by
    simpa using (Fintype.card_congr e6).symm
  have hcardT : Fintype.card {i : Λ // i ∉ S} = 3 := by
    have hsub : Fintype.card {i : Λ // i ∈ S} = S.card := by
      rw [Fintype.card_subtype]
      simp
    have hcomp : Fintype.card {i : Λ // i ∉ S} = Fintype.card Λ - S.card := by
      rw [Fintype.card_subtype_compl (fun i : Λ => i ∈ S), hsub]
    omega
  have hTne : Nonempty {i : Λ // i ∉ S} := Fintype.card_pos_iff.mp (by omega)
  have hMJ : GGIsWeylMatrix (parMatrix ML {i | i ∉ S}) :=
    l05nBL_ggIsWeylMatrix_parMatrix_of_deletedConnected S ML CL hML hCL hconn hTne
  have hNoML : GGNoMultipleEdge ML := by
    rw [he6]
    exact ggNoMultipleEdge_E6.reindex e6
  have hNoPar : GGNoMultipleEdge (parMatrix ML {i | i ∉ S}) := hNoML.parMatrix {i | i ∉ S}
  rcases hMJ with ⟨n, e, hn, hABC⟩ |
    ⟨e6', hE6'⟩ | ⟨e7', hE7'⟩ | ⟨e8', hE8'⟩ | ⟨e4', hF4'⟩ | ⟨e2', hG2'⟩
  · have hn3 : n = 3 := by
      exact (Fintype.card_fin n).symm.trans ((Fintype.card_congr e).trans hcardT)
    rcases hABC with hA | ⟨hn2, hB⟩ | ⟨hn4, hD⟩
    · subst n
      exact ⟨e, hA⟩
    · exfalso
      subst n
      have hBno : GGNoMultipleEdge ((CoxeterMatrix.B 3).reindex e) := by
        simpa [hB] using hNoPar
      have hBno' : GGNoMultipleEdge (CoxeterMatrix.B 3) := by
        intro i j hij
        have := hBno (e i) (e j) (fun hh => hij (e.injective hh))
        simpa [CoxeterMatrix.reindex_apply] using this
      have hB12 : 4 ≤ (CoxeterMatrix.B 3).M 1 2 := by decide +kernel
      exact absurd (hBno' 1 2 (by decide +kernel)) (by omega)
    · omega
  · exfalso
    have h6 : (6 : ℕ) = 3 := by
      exact (Fintype.card_fin 6).symm.trans ((Fintype.card_congr e6').trans hcardT)
    omega
  · exfalso
    have h7 : (7 : ℕ) = 3 := by
      exact (Fintype.card_fin 7).symm.trans ((Fintype.card_congr e7').trans hcardT)
    omega
  · exfalso
    have h8 : (8 : ℕ) = 3 := by
      exact (Fintype.card_fin 8).symm.trans ((Fintype.card_congr e8').trans hcardT)
    omega
  · exfalso
    have h4 : (4 : ℕ) = 3 := by
      exact (Fintype.card_fin 4).symm.trans ((Fintype.card_congr e4').trans hcardT)
    omega
  · exfalso
    have h2 : (2 : ℕ) = 3 := by
      exact (Fintype.card_fin 2).symm.trans ((Fintype.card_congr e2').trans hcardT)
    omega

theorem e6_exact_three_survivor_equiv
    {Λ H : Type} [Fintype Λ] [DecidableEq Λ] [Group H]
    {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C) (hE6 : GGIsTypeE6 M)
    {S : Finset Λ} (hS : S.card = 3) (hconn : GGDeletedConnectedS M S)
    {X J : Subgroup H} (f : M.Group ≃* ↥X) (φ : Λ → H)
    (hf : ∀ i, (f (M.simple i) : H) = φ i)
    (hJ : J = Subgroup.closure (Set.range fun i : {i : Λ // i ∉ S} => φ i)) :
    ∃ (e : Fin 3 ≃ {i : Λ // i ∉ S}) (g : (CoxeterMatrix.A 3).Group ≃* ↥J),
      ∀ i, (g ((CoxeterMatrix.A 3).simple i) : H) = φ (e i) := by
  classical
  let T : Set Λ := {i | i ∉ S}
  have hJ' : J = Subgroup.closure (Set.range fun i : T => φ i) := by
    exact hJ
  obtain ⟨a, ha⟩ := exists_A3_reindex_of_e6_three_survivor hM hC hE6 hS hconn
  have haT : parMatrix M T = (CoxeterMatrix.A 3).reindex a := by
    simpa [T] using ha
  let jEquiv : (parMatrix M T).Group ≃* ↥J :=
    ggParabolic_equiv_of_generator_equiv M T φ f hf hJ'
  have hjEquiv (i : T) : (jEquiv ((parMatrix M T).simple i) : H) = φ i :=
    ggParabolic_equiv_of_generator_equiv_simple M f φ hf T hJ' i
  have hx : ∃ g : (parMatrix M T).Group ≃* ↥J,
      ∀ i : T, (g ((parMatrix M T).simple i) : H) = φ i := ⟨jEquiv, hjEquiv⟩
  rw [haT] at hx
  obtain ⟨g, hg⟩ := hx
  refine ⟨a, (CoxeterMatrix.reindexGroupEquiv (CoxeterMatrix.A 3) a).symm.trans g, ?_⟩
  intro i
  have heq : (CoxeterMatrix.reindexGroupEquiv (CoxeterMatrix.A 3) a).symm
      ((CoxeterMatrix.A 3).simple i) =
      ((CoxeterMatrix.A 3).reindex a).simple (a i) := by
    apply (CoxeterMatrix.reindexGroupEquiv (CoxeterMatrix.A 3) a).injective
    simp [CoxeterMatrix.reindexGroupEquiv_apply_simple]
  simpa only [MulEquiv.trans_apply, heq] using hg (a i)

theorem e6_exact_three_survivor_card
    {Λ H : Type} [Fintype Λ] [DecidableEq Λ] [Group H]
    {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C) (hE6 : GGIsTypeE6 M)
    {S : Finset Λ} (hS : S.card = 3) (hconn : GGDeletedConnectedS M S)
    {X J : Subgroup H} (f : M.Group ≃* ↥X) (φ : Λ → H)
    (hf : ∀ i, (f (M.simple i) : H) = φ i)
    (hJ : J = Subgroup.closure (Set.range fun i : {i : Λ // i ∉ S} => φ i)) :
    Nat.card ↥J = 24 := by
  obtain ⟨a, g, hg⟩ := e6_exact_three_survivor_equiv hM hC hE6 hS hconn f φ hf hJ
  rw [← Nat.card_congr g.toEquiv, l05nK3a_card_coxeterA 3]
  norm_num

theorem ggResLeviDatumExact3_E6_automizerJ_card
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs X J Y : Subgroup G}
    (hD : GGResLeviDatumExact3 p Bs X J Y ggSelAny ggTypLE6) :
    Nat.card ↥(ggAutomizer J Bs) = 24 := by
  classical
  rcases hD with ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, -, -, hML, hCL, -, -, htyp, -, -, -, -, -, ⟨f, hf⟩, -, -, -, hconn, hclosJ⟩
  let := i1
  let := i2
  have hE6 : GGIsTypeE6 ML := htyp
  exact e6_exact_three_survivor_card hML hCL hE6 hS hconn f
    (fun i => φ (Sum.inl i)) hf hclosJ

end E6ExactThreeSurvivor


theorem GGResXDatumA_of_exactThree_E6
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X J Y : Subgroup G}
    (hD : GGResLeviDatumExact3 p Bs X J Y ggSelAny ggTypLE6) :
    GGResXDatumA p Bs J 3 := by
  classical
  rcases hD with ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, -, -, hML, hCL, -, -, htyp, hlin, hrefl, hpair, -, -, ⟨f, hf⟩, -, -, -, hconn, hclosJ⟩
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  let Tset : Set Λ := {i | i ∉ S}
  let T : Type := ↥Tset
  have hclosJT : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun i : T => φ (Sum.inl i.1)) := by
    exact hclosJ
  have hE6 : GGIsTypeE6 ML := htyp
  obtain ⟨e, he⟩ := exists_A3_reindex_of_e6_three_survivor hML hCL hE6 hS hconn
  let eT : Fin 3 ≃ T := e
  have heT : parMatrix ML Tset = (CoxeterMatrix.A 3).reindex eT := by
    change parMatrix ML {i | i ∉ S} = (CoxeterMatrix.A 3).reindex e
    exact he
  have hTne : Nonempty T := ⟨eT 0⟩
  have hMJ : GGIsWeylMatrix (parMatrix ML Tset) := by
    simpa [Tset] using
      l05nBL_ggIsWeylMatrix_parMatrix_of_deletedConnected S ML CL hML hCL hconn hTne
  have hCJ : GGIntCartan (parMatrix ML Tset)
      (CL.submatrix (Subtype.val : T → Λ) (Subtype.val : T → Λ)) := by
    constructor
    · intro i
      simpa [Matrix.submatrix_apply] using hCL.1 i.1
    · intro i j hij
      have hij' : (i : Λ) ≠ j := fun hh => hij (Subtype.ext hh)
      have hh := hCL.2 i.1 j.1 hij'
      simpa [parMatrix_apply, Matrix.submatrix_apply] using hh
  refine ⟨T, inferInstance, inferInstance, parMatrix ML Tset,
    CL.submatrix (Subtype.val : T → Λ) (Subtype.val : T → Λ),
    V, i5, i6, ι, (fun i : T => φ (Sum.inl i.1)), (fun i : T => h (Sum.inl i.1)),
    (fun i : T => α (Sum.inl i.1)), eT, heT, hMJ, hCJ,
    (fun i w => hlin (Sum.inl i.1) w),
    (fun i => hrefl (Sum.inl i.1)),
    (fun i j => by simpa [Matrix.submatrix_apply] using hpair i.1 j.1),
    ⟨ggParabolic_equiv_of_generator_equiv ML Tset (fun i => φ (Sum.inl i)) f hf
        hclosJT,
      fun i => ggParabolic_equiv_of_generator_equiv_simple ML f
        (fun i => φ (Sum.inl i)) hf Tset hclosJT i⟩,
    hclosJT⟩


theorem GGResLineJDatum_A3_of_GGResXDatumA
    {G : Type} [Group G] [Finite G] {Bs J : Subgroup G} [Fact (Nat.Prime 3)]
    (hXD : GGResXDatumA 3 Bs J 3) :
    GGResLineJDatum 3 Bs J .A3 := by
  classical
  rcases hXD with ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, e,
    hM, -, hC, hform, hrefl, hpair, -, hclos⟩
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  let r : Fin 3 → MulAut ↥Bs := fun i => φ (e i)
  let h' : Fin 3 → V := fun i => h (e i)
  let α' : Fin 3 → Module.Dual (ZMod 3) V := fun i => α (e i)
  have hsymm : ∀ a b : Fin 3, CartanMatrix.A 3 a b = CartanMatrix.A 3 b a := by
    intro a b
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  have hC' : GGIntCartan ((CoxeterMatrix.A 3).reindex e) C := by
    simpa [hM] using hC
  have hCeq : C = Matrix.reindex e e (CartanMatrix.A 3) ∨
      C = (Matrix.reindex e e (CartanMatrix.A 3)).transpose :=
    GGIntCartan.eq_or_eq_transpose
      (M := (CoxeterMatrix.A 3).reindex e) hC'
      ((ggIntCartan_A 3).reindex e)
      ((ggAtMostOneMultipleEdge_A 3).reindex e)
  have hCast : ∀ i j : Fin 3, ((C (e i) (e j) : ℤ) : ZMod 3) =
      ((CartanMatrix.A 3 i j : ℤ) : ZMod 3) := by
    intro i j
    rcases hCeq with hEq | hEq
    · rw [hEq, Matrix.reindex_apply, Matrix.submatrix_apply]
      simp only [Equiv.symm_apply_apply]
    · rw [hEq, Matrix.transpose_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
      simp only [Equiv.symm_apply_apply]
      exact (congrArg (fun z : ℤ => (z : ZMod 3)) (hsymm i j)).symm
  have hpair' : ∀ i j : Fin 3, α' i (h' j) = (CartanMatrix.A 3 i j : ZMod 3) := by
    intro i j
    rw [hpair (e i) (e j)]
    exact hCast i j
  have hLI : LinearIndependent (ZMod 3) h' := by
    refine linearIndependent_of_det_ne_zero h' α' ?_
    have hmat : (Matrix.of fun i j => α' i (h' j)) =
        (CartanMatrix.A 3).map (Int.castRingHom (ZMod 3)) := by
      ext i j
      exact hpair' i j
    rw [hmat]
    have hdet : ((CartanMatrix.A 3).map (Int.castRingHom (ZMod 3))).det ≠ 0 := by
      have hmap : ((CartanMatrix.A 3).map (Int.castRingHom (ZMod 3))).det =
          ((CartanMatrix.A 3).det : ZMod 3) := by
        simpa [RingHom.mapMatrix_apply] using
          (RingHom.map_det (Int.castRingHom (ZMod 3)) (CartanMatrix.A 3)).symm
      rw [hmap, CartanMatrix.A_det]
      rw [Int.cast_add, Int.cast_natCast, ZMod.natCast_self, zero_add, Int.cast_one]
      exact one_ne_zero
    exact hdet
  refine ⟨V, i3, i4, ι, r, h', α', ?_, ?_, ?_, hLI, ?_⟩
  · intro i w
    exact hform (e i) w
  · intro i
    exact hrefl (e i)
  · intro i j
    exact hpair' i j
  · change ggAutomizer J Bs = Subgroup.closure (Set.range r)
    have hrange : Set.range r = Set.range φ := by
      ext a
      simp only [Set.mem_range]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨e i, rfl⟩
      · rintro ⟨l, rfl⟩
        exact ⟨e.symm l, by
          change φ (e (e.symm l)) = φ l
          rw [e.apply_symm_apply]⟩
    rw [hrange]
    exact hclos

theorem e6_exactThree_GGResLineJDatum_A3
    {G : Type} [Group G] [Finite G] {Bs X J Y : Subgroup G} [Fact (Nat.Prime 3)]
    (hD : GGResLeviDatumExact3 3 Bs X J Y ggSelAny ggTypLE6) :
    GGResLineJDatum 3 Bs J .A3 :=
  GGResLineJDatum_A3_of_GGResXDatumA (GGResXDatumA_of_exactThree_E6 hD)

theorem ggResExactThree_E6_exists_coroot_subgroup
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} [Fact (Nat.Prime 3)]
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypLE6 ∨
      GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypLE6) :
    ∃ E : Subgroup G, E ≤ Bs ⊓ J ∧ IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
      E ⊓ Subgroup.centralizer (J : Set G) = ⊥ := by
  have hLine : GGResLineJDatum 3 Bs J .A3 := by
    rcases hD with hD | hD
    · exact e6_exactThree_GGResLineJDatum_A3 hD
    · exact e6_exactThree_GGResLineJDatum_A3 hD
  exact hH.exists_coroot_subgroup_of_A3 hLine

theorem ggResExactThree_E6_cube_le_card_gamma_J
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} [Fact (Nat.Prime 3)]
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypLE6 ∨
      GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypLE6) :
    3 ^ 3 ≤ Nat.card (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range := by
  have hLine : GGResLineJDatum 3 Bs J .A3 := by
    rcases hD with hD | hD
    · exact e6_exactThree_GGResLineJDatum_A3 hD
    · exact e6_exactThree_GGResLineJDatum_A3 hD
  exact hH.cube_le_card_gamma_of_A3 hLine


theorem ggResLevi_dvd_card_J_of_reflection
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs J : Subgroup G}
    (hBsJ : Bs ≤ Subgroup.normalizer (J : Set G))
    (hp : p.Prime) (hp2 : p ≠ 2) (hexp : ∀ b ∈ Bs, b ^ p = 1)
    {r : MulAut ↥Bs} (hr : r ∈ ggAutomizer J Bs) (hrefl : GGIsReflection p r) :
    p ∣ Nat.card J ∧ ∃ e ∈ J ⊓ Bs, ∃ j ∈ J, j * e * j⁻¹ ≠ e := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hgJ, -, hrg⟩ := mem_ggAutomizer_iff.mp hr
  obtain ⟨hr2, hcard⟩ := hrefl
  have hrr : ∀ b : ↥Bs, r (r b) = b := fun b => by
    rw [← MulAut.mul_apply, ← pow_two, hr2, MulAut.one_apply]
  obtain ⟨b, hb⟩ : ∃ b : ↥Bs, r b ≠ b := by
    by_contra! h
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv h)] at hcard
    exact hp.one_lt.ne' (Nat.eq_of_mul_eq_mul_left Nat.card_pos
      (hcard.trans (mul_one _).symm))
  set e : ↥Bs := r b * b⁻¹ with he_def
  have heJ : (e : G) ∈ J := by
    have e1 : (e : G) = g * ((b : G) * g⁻¹ * (b : G)⁻¹) := by
      rw [he_def, Subgroup.coe_mul, Subgroup.coe_inv, hrg b]
      group
    rw [e1]
    exact J.mul_mem hgJ ((Subgroup.mem_normalizer_iff.mp (hBsJ b.2) _).mp (J.inv_mem hgJ))
  have hre : r e = e⁻¹ := by
    rw [he_def, map_mul, map_inv, hrr]
    group
  have hconj : g * (e : G) * g⁻¹ = (e : G)⁻¹ := by
    rw [← hrg e, hre]
    rfl
  have he1 : (e : G) ≠ 1 := fun h => hb (mul_inv_eq_one.mp (Subtype.ext h))
  have hep : (e : G) ^ p = 1 := hexp _ e.2
  refine ⟨?_, (e : G), Subgroup.mem_inf.mpr ⟨heJ, e.2⟩, g, hgJ, fun h => he1 ?_⟩
  · have hdvd := orderOf_dvd_natCard (⟨(e : G), heJ⟩ : ↥J)
    rwa [Subgroup.orderOf_mk, orderOf_eq_prime hep he1] at hdvd
  · have h2 : (e : G) ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [← hconj.symm.trans h]
      exact inv_mul_cancel _
    have hg := pow_gcd_eq_one.mpr ⟨h2, hep⟩
    rwa [((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)).gcd_eq_one, pow_one] at hg

theorem ggResLeviDatumCard_survivor_dvd_and_ne
    {G : Type} [Group G] [Finite G]
    {p k n : ℕ} [Fact p.Prime] {Bs X J Y : Subgroup G}
    (hD : GGResLeviDatumCard k p Bs X J Y ggSelAny ggTypAny)
    (hX : ∃ c, GGWeylTypeData n (Nat.card ↥(ggAutomizer X Bs)) c)
    (hnk : k < n) (hBsJ : Bs ≤ Subgroup.normalizer (J : Set G))
    (hp2 : p ≠ 2) (hexp : ∀ b ∈ Bs, b ^ p = 1) :
    p ∣ Nat.card J ∧ ggAutomizer J Bs ≠ ⊥ := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨Λ, hΛF, hΛD, S, Λa, hΛaF, hΛaD, ML, CL, MK, CK, V, hV, hVp, ι, φ, h, α,
    hS, hΛa1, hΛa3, hWM, hCL, hWMK, hCK, htyp, hlin, hrefl, hCLmat, hCKmat, hsel, hfL,
    hfK, hgenL, hgenK, hdel, hgenJ⟩ := hD
  obtain ⟨fL, hfL⟩ := hfL
  let := hΛF
  let := hΛD
  have hWML : GGWeylTypeData (Fintype.card Λ) (Nat.card ↥(ggAutomizer X Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer X Bs))) := by
    rw [← Nat.card_congr fL.toEquiv,
      ← Nat.card_congr (Subgroup.centerCongr fL).toEquiv]
    exact ggWeylTypeData_of_isWeylMatrix hWM
  obtain ⟨c, hXc⟩ := hX
  have hcardΛ : Fintype.card Λ = n := ggWeylTypeData_rank_eq hWML hXc
  have hsub : Fintype.card {i : Λ // i ∈ S} = S.card := by
    rw [Fintype.card_subtype]
    simp
  have hTcard : Fintype.card {i : Λ // i ∉ S} = n - k := by
    rw [Fintype.card_subtype_compl (fun i : Λ => i ∈ S), hsub, hS, hcardΛ]
  have hTpos : 0 < Fintype.card {i : Λ // i ∉ S} := by
    rw [hTcard]
    omega
  obtain ⟨j⟩ := Fintype.card_pos_iff.mp hTpos
  have hr : φ (Sum.inl j.1) ∈ ggAutomizer J Bs := by
    rw [hgenJ]
    exact Subgroup.subset_closure ⟨j, rfl⟩
  obtain ⟨hpJ, -⟩ := ggResLevi_dvd_card_J_of_reflection hBsJ hp hp2 hexp hr
    (hrefl (Sum.inl j.1))
  have hrne : φ (Sum.inl j.1) ≠ 1 := by
    intro h1
    have hfix : Nat.card {b : ↥Bs // φ (Sum.inl j.1) b = b} = Nat.card ↥Bs := by
      apply Nat.card_congr
      exact Equiv.subtypeUnivEquiv (fun b => by rw [h1]; rfl)
    have hcardr := (hrefl (Sum.inl j.1)).2
    rw [hfix] at hcardr
    have hpos : 0 < Nat.card ↥Bs :=
      Nat.card_pos_iff.mpr ⟨⟨1, Bs.one_mem⟩, inferInstance⟩
    have hp1 : p = 1 := by
      apply Nat.eq_of_mul_eq_mul_left hpos
      simpa using hcardr
    exact hp.one_lt.ne' hp1
  refine ⟨hpJ, ?_⟩
  intro hbot
  have hmem : φ (Sum.inl j.1) ∈ (⊥ : Subgroup (MulAut ↥Bs)) := by
    rw [← hbot]
    exact hr
  exact hrne (by simpa using hmem)


theorem ggResLeviDatumExact2_reverse_card_one_of_not_exact2_or_exact3
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs X J Y : Subgroup G}
    (h2 : GGResLeviDatumExact2 p Bs X J Y ggSelAny ggTypAny)
    (hno : ¬ (GGResLeviDatumExact2 p Bs Y J X ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 p Bs Y J X ggSelAny ggTypAny)) :
    GGResLeviDatumCard 1 p Bs Y J X ggSelAny ggTypAny := by
  rcases ggResLeviDatumExact2_reverse_card_one_two_three h2 with h1 | h2' | h3'
  · exact h1
  · exact (hno (Or.inl h2')).elim
  · exact (hno (Or.inr h3')).elim

theorem ggResLeviDatumExact2_rank_gap_of_only_orientation
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X J Y : Subgroup G}
    (h2 : GGResLeviDatumExact2 p Bs X J Y ggSelAny ggTypAny)
    (hno : ¬ (GGResLeviDatumExact2 p Bs Y J X ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 p Bs Y J X ggSelAny ggTypAny))
    (hJ : ggAutomizer J Bs ≠ ⊥) :
    ∃ r, GGWeylTypeData (r + 2) (Nat.card ↥(ggAutomizer X Bs))
        (Nat.card ↥(Subgroup.center ↥(ggAutomizer X Bs))) ∧
      GGWeylTypeData (r + 1) (Nat.card ↥(ggAutomizer Y Bs))
        (Nat.card ↥(Subgroup.center ↥(ggAutomizer Y Bs))) ∧
      GGWeylTypeData r (Nat.card ↥(ggAutomizer J Bs))
        (Nat.card ↥(Subgroup.center ↥(ggAutomizer J Bs))) := by
  have h1 := ggResLeviDatumExact2_reverse_card_one_of_not_exact2_or_exact3 h2 hno
  obtain ⟨r, hX, hJr⟩ := ggResLeviDatumCard_weylTypeData h2 hJ
  obtain ⟨r', hY, hJr'⟩ := ggResLeviDatumCard_weylTypeData h1 hJ
  have hr : r = r' := ggWeylTypeData_rank_eq hJr hJr'
  subst r'
  exact ⟨r, hX, hY, hJr⟩

end CFSG.StandardType
