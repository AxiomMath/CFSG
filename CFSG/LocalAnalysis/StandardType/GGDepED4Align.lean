module

public import CFSG.LocalAnalysis.StandardType.GGDepED4False
public import CFSG.LocalAnalysis.StandardType.GGDepED4Pat1
public import CFSG.LocalAnalysis.StandardType.GGDepED4Pat2
public import CFSG.LocalAnalysis.StandardType.GGDepEFrame
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepAssembly
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGDepED4PackDefs
public import CFSG.LocalAnalysis.StandardType.GGDepED4Pos
public import CFSG.LocalAnalysis.StandardType.GGResConjWire
public import CFSG.LocalAnalysis.StandardType.GGReflClosedFaith
public import CFSG.LocalAnalysis.StandardType.GGFixedRealizedConfig
public import CFSG.Monster.B.Geometry.InitialIsometryParabolic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem l05nEA_typeE6_of_datum {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Bs L : Subgroup G} {Λ₁ : Type} [Fintype Λ₁] [DecidableEq Λ₁] {M₁ : CoxeterMatrix Λ₁}
    (e₁ : Fin 6 ≃ Λ₁) (hM₁ : M₁ = CoxeterMatrix.E₆.reindex e₁) (hWM₁ : GGIsWeylMatrix M₁)
    {Λ₂ : Type} [Fintype Λ₂] [DecidableEq Λ₂] {M₂ : CoxeterMatrix Λ₂} (hWM₂ : GGIsWeylMatrix M₂)
    (f₁ : M₁.Group ≃* ↥(ggAutomizer L Bs)) (f₂ : M₂.Group ≃* ↥(ggAutomizer L Bs))
    (hconj : ∀ k : Λ₂, ∃ (w : ↥(ggAutomizer L Bs)) (i : Λ₁),
      f₂ (M₂.simple k) = w * f₁ (M₁.simple i) * w⁻¹) :
    ∃ e₂ : Fin 6 ≃ Λ₂, M₂ = CoxeterMatrix.E₆.reindex e₂ := by
  classical
  obtain ⟨σ, w, hw⟩ :=
    ggWeylSimpleSystemsConjInput_holds Λ₁ Λ₂ M₁ M₂ hWM₁ hWM₂ ↥(ggAutomizer L Bs) f₁ f₂ hconj
  have hM₂eq : M₂ = M₁.reindex σ := by
    refine CoxeterMatrix.ext (funext fun i => funext fun j => ?_)
    rw [CoxeterMatrix.reindex_apply]
    set i' : Λ₁ := σ.symm i
    set j' : Λ₁ := σ.symm j
    have hi : σ i' = i := σ.apply_symm_apply i
    have hj : σ j' = j := σ.apply_symm_apply j
    have hwi := hw i'
    have hwj := hw j'
    rw [hi] at hwi
    rw [hj] at hwj
    have hord₂ : orderOf (M₂.simple i * M₂.simple j) = M₂.M i j := by
      rw [← CoxeterMatrix.toCoxeterSystem_simple]
      exact CoxeterSystem.orderOf_simple_mul_simple M₂.toCoxeterSystem i j
    have hord₁ : orderOf (M₁.simple i' * M₁.simple j') = M₁.M i' j' := by
      rw [← CoxeterMatrix.toCoxeterSystem_simple]
      exact CoxeterSystem.orderOf_simple_mul_simple M₁.toCoxeterSystem i' j'
    have hmap : f₂ (M₂.simple i * M₂.simple j) =
        w * f₁ (M₁.simple i' * M₁.simple j') * w⁻¹ := by
      rw [map_mul, map_mul, hwi, hwj]
      group
    have hord_eq : orderOf (M₂.simple i * M₂.simple j) =
        orderOf (M₁.simple i' * M₁.simple j') := by
      calc orderOf (M₂.simple i * M₂.simple j)
          = orderOf (f₂ (M₂.simple i * M₂.simple j)) := (MulEquiv.orderOf_eq f₂ _).symm
        _ = orderOf (w * f₁ (M₁.simple i' * M₁.simple j') * w⁻¹) := by rw [hmap]
        _ = orderOf (f₁ (M₁.simple i' * M₁.simple j')) := by
              rw [← MulAut.conj_apply]
              exact orderOf_injective (MulAut.conj w).toMonoidHom (MulAut.conj w).injective _
        _ = orderOf (M₁.simple i' * M₁.simple j') := MulEquiv.orderOf_eq f₁ _
    rw [← hord₂, hord_eq, hord₁]
  refine ⟨e₁.trans σ, ?_⟩
  rw [hM₂eq, hM₁]
  exact l05nBL_reindex_trans (CoxeterMatrix.E₆) e₁ σ

theorem l05nEA_card_MJ {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {Bs L J : Subgroup G} {Λ : Type} [Fintype Λ] [DecidableEq Λ] (b₁ b₂ : Λ) (ML : CoxeterMatrix Λ)
    (hWM : GGIsWeylMatrix ML) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan ML C)
    (fL : ML.Group ≃* ↥(ggAutomizer L Bs)) (φ : Λ → MulAut ↥Bs)
    (hfL : ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ i)
    (hclosJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ j.1))
    (hJ : Nat.card ↥(ggAutomizer J Bs) = 192) :
    ∃ MJ : CoxeterMatrix {j : Λ // j ≠ b₁ ∧ j ≠ b₂},
      (∀ j j', MJ.M j j' = ML.M j.1 j'.1) ∧ 192 ≤ Nat.card MJ.Group := by
  classical
  have hFT : TauCeti.IsFiniteType C :=
    isFiniteType_of_ggIsWeylMatrixFixed (hWM : GGIsWeylMatrixFixed ML) hC
  haveI : Finite ML.Group := by
    have h : Finite (CFSG.LieType.RootSystem.coxeterMatrix hFT).Group :=
      CFSG.LieType.RootSystem.finite_group hFT
    rwa [coxeterMatrix_eq_of_ggIntCartan hFT hC] at h
  let Js : Set Λ := {j | j ≠ b₁ ∧ j ≠ b₂}
  let MJ : CoxeterMatrix {j : Λ // j ≠ b₁ ∧ j ≠ b₂} := CFSG.Monster.B.Geometry.parMatrix ML Js
  have hJM : ∀ j j', MJ.M j j' = ML.M j.1 j'.1 := fun _ _ => rfl
  haveI : Finite MJ.Group :=
    Finite.of_injective (CFSG.Monster.B.Geometry.parToGroup ML.toCoxeterSystem Js)
      (CFSG.Monster.B.Geometry.parToGroup_injective ML.toCoxeterSystem Js)
  let hMJ : MJ.Group →* MulAut ↥Bs :=
    (Subgroup.subtype (ggAutomizer L Bs)).comp
      (fL.toMonoidHom.comp (CFSG.Monster.B.Geometry.parToGroup ML.toCoxeterSystem Js))
  have hsimple : ∀ j, hMJ (MJ.simple j) = φ j.1 := by
    intro j
    change (fL ((CFSG.Monster.B.Geometry.parToGroup ML.toCoxeterSystem Js) (MJ.simple j)) :
      MulAut ↥Bs) = φ j.1
    rw [show MJ.simple j = (CFSG.Monster.B.Geometry.parMatrix ML Js).simple j from rfl,
      CFSG.Monster.B.Geometry.parToGroup_simple, CoxeterMatrix.toCoxeterSystem_simple, hfL]
  have hset : hMJ '' Set.range MJ.toCoxeterSystem.simple =
      Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ j.1) := by
    ext x; constructor
    · rintro ⟨a, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, by rw [CoxeterMatrix.toCoxeterSystem_simple, hsimple]⟩
    · rintro ⟨j, rfl⟩
      exact ⟨MJ.toCoxeterSystem.simple j, ⟨j, rfl⟩,
        by rw [CoxeterMatrix.toCoxeterSystem_simple, hsimple]⟩
  have hrange : hMJ.range = ggAutomizer J Bs := by
    rw [MonoidHom.range_eq_map, ← MJ.toCoxeterSystem.subgroup_closure_range_simple,
      MonoidHom.map_closure, hset, ← hclosJ]
  have hcard_eq : Nat.card ↥(hMJ.range) = Nat.card ↥(ggAutomizer J Bs) :=
    Nat.card_congr (MulEquiv.subgroupCongr hrange).toEquiv
  have hle0 : Nat.card ↥(hMJ.range) ≤ Nat.card MJ.Group :=
    Nat.card_le_card_of_surjective hMJ.rangeRestrict hMJ.rangeRestrict_surjective
  refine ⟨MJ, hJM, ?_⟩
  rw [← hJ, ← hcard_eq]
  exact hle0

theorem l05nEA_reflClosed_of_datum {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {G : Type}
    [Group G] [Finite G] {Bs L : Subgroup G} {Λ₁ : Type} [Fintype Λ₁] [DecidableEq Λ₁]
    {M₁ : CoxeterMatrix Λ₁} (e₁ : Fin 6 ≃ Λ₁) (hM₁ : M₁ = CoxeterMatrix.E₆.reindex e₁)
    (hWM₁ : GGIsWeylMatrix M₁) {C₁ : Matrix Λ₁ Λ₁ ℤ} (hC₁ : GGIntCartan M₁ C₁)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V] (ι : Additive ↥Bs ≃+ V)
    (φ₁ : Λ₁ → MulAut ↥Bs) (h₁ : Λ₁ → V) (α₁ : Λ₁ → Module.Dual (ZMod p) V)
    (hlin₁ : ∀ i w, ggLin (p := p) ι (φ₁ i) w = w - α₁ i w • h₁ i)
    (hpair₁ : ∀ i j, α₁ i (h₁ j) = (C₁ i j : ZMod p))
    (hclos₁ : ggAutomizer L Bs = Subgroup.closure (Set.range φ₁))
    (f₁ : M₁.Group ≃* ↥(ggAutomizer L Bs))
    (hf₁ : ∀ i, (f₁ (M₁.simple i) : MulAut ↥Bs) = φ₁ i) :
    GGReflClosed (fun i => ggLin (p := p) ι (φ₁ i)) := by
  classical
  have hFT : TauCeti.IsFiniteType C₁ :=
    isFiniteType_of_ggIsWeylMatrixFixed (Or.inr (Or.inl ⟨e₁, hM₁⟩)) hC₁
  let s₁ : Λ₁ → V ≃ₗ[ZMod p] V := fun i => ggLin (p := p) ι (φ₁ i)
  have hs₁ : ∀ i v, s₁ i v = v - α₁ i v • h₁ i := hlin₁
  let W₁ := Subgroup.closure (Set.range s₁)
  have hmap : Subgroup.map (ggLin (p := p) ι) (ggAutomizer L Bs) = W₁ := by
    rw [hclos₁, MonoidHom.map_closure]
    congr 1
    rw [← Set.range_comp]; rfl
  let f₁' : M₁.Group ≃* ↥W₁ :=
    f₁.trans ((Subgroup.equivMapOfInjective (ggAutomizer L Bs) (ggLin (p := p) ι)
      (ggLin_injective ι)).trans (MulEquiv.subgroupCongr hmap))
  have hf₁' : ∀ i, (f₁' (M₁.simple i) : V ≃ₗ[ZMod p] V) = s₁ i := by
    intro i
    simp only [f₁', MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
      Subgroup.coe_equivMapOfInjective_apply, hf₁ i, s₁]
  exact ggReflClosed_of_faithful hp2 hFT hC₁ h₁ α₁ hpair₁ s₁ hs₁ f₁' hf₁'

theorem l05nEA_conj_of_reflClosed {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {Bs L : Subgroup G} {Λ₁ : Type} [Fintype Λ₁] [DecidableEq Λ₁] {M₁ : CoxeterMatrix Λ₁}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V] (ι : Additive ↥Bs ≃+ V)
    (φ₁ : Λ₁ → MulAut ↥Bs)
    (hclos₁ : ggAutomizer L Bs = Subgroup.closure (Set.range φ₁))
    (hRC₁ : GGReflClosed (fun i => ggLin (p := p) ι (φ₁ i)))
    (f₁ : M₁.Group ≃* ↥(ggAutomizer L Bs))
    (hf₁ : ∀ i, (f₁ (M₁.simple i) : MulAut ↥Bs) = φ₁ i)
    {Λ₂ : Type} [Fintype Λ₂] [DecidableEq Λ₂] {M₂ : CoxeterMatrix Λ₂}
    (f₂ : M₂.Group ≃* ↥(ggAutomizer L Bs)) (φ₂ : Λ₂ → MulAut ↥Bs)
    (hf₂ : ∀ i, (f₂ (M₂.simple i) : MulAut ↥Bs) = φ₂ i)
    (hrefl₂ : ∀ i, GGIsReflection p (φ₂ i)) :
    ∀ k : Λ₂, ∃ (w : ↥(ggAutomizer L Bs)) (i : Λ₁),
      f₂ (M₂.simple k) = w * f₁ (M₁.simple i) * w⁻¹ := by
  classical
  intro k
  have hmemclos : φ₂ k ∈ Subgroup.closure (Set.range φ₁) := by
    rw [← hclos₁]
    rw [← hf₂ k]
    exact (f₂ (M₂.simple k)).2
  have h2range : Set.range (fun i => ggLin (p := p) ι (φ₁ i)) =
      (ggLin (p := p) ι) '' Set.range φ₁ := by
    rw [← Set.range_comp]; rfl
  have hmemV : ggLin (p := p) ι (φ₂ k) ∈
      Subgroup.closure (Set.range fun i => ggLin (p := p) ι (φ₁ i)) := by
    have h1 := Subgroup.mem_map_of_mem (f := ggLin (p := p) ι) hmemclos
    rw [MonoidHom.map_closure] at h1
    rwa [h2range]
  have h2 : (ggLin (p := p) ι (φ₂ k)) ^ 2 = 1 := by
    rw [← map_pow, (hrefl₂ k).1, map_one]
  have hne : ggLin (p := p) ι (φ₂ k) ≠ 1 := by
    intro h
    exact GGIsReflection.ne_one (Fact.out : p.Prime) (hrefl₂ k)
      (ggLin_injective ι (by rw [h, map_one]))
  have hform : ∃ (v : V) (f : Module.Dual (ZMod p) V),
      ∀ w, ggLin (p := p) ι (φ₂ k) w = w - f w • v := by
    obtain ⟨x, f, -, hf⟩ := exists_of_ggIsReflection (p := p) ι (hrefl₂ k)
    exact ⟨x, f, hf⟩
  obtain ⟨u, huW, i, heq⟩ := hRC₁ _ hmemV h2 hne hform
  have hu' : u ∈ Subgroup.map (ggLin (p := p) ι) (Subgroup.closure (Set.range φ₁)) := by
    simpa only [MonoidHom.map_closure, ← h2range] using huW
  obtain ⟨w, hwmem, hwu⟩ := Subgroup.mem_map.mp hu'
  refine ⟨⟨w, by rw [hclos₁]; exact hwmem⟩, i, ?_⟩
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hf₂ k, hf₁ i]
  have : ggLin (p := p) ι (φ₂ k) = ggLin (p := p) ι (w * φ₁ i * w⁻¹) := by
    rw [map_mul, map_mul, map_inv]
    rw [← hwu] at heq
    exact heq
  exact ggLin_injective ι this

@[expose] def GGResXDatumE6Core {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (Bs X : Subgroup G) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V) (e : Fin 6 ≃ Λ),
    M = CoxeterMatrix.E₆.reindex e ∧ GGIsWeylMatrix M ∧ GGIntCartan M C ∧
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧ (∀ i, GGIsReflection p (φ i)) ∧
      (∀ i j, α i (h j) = (C i j : ZMod p)) ∧
      (∃ f : M.Group ≃* ↥(ggAutomizer X Bs), ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i) ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range φ)

theorem GGResXDatumE6x.core {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} {x : G} (h : GGResXDatumE6x p Bs X x) : GGResXDatumE6Core p Bs X := by
  obtain ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h', α, e, hM, hW, hC, hlin, hrefl, hpair, hf, hcl, -⟩ := h
  exact ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h', α, e, hM, hW, hC, hlin, hrefl, hpair, hf, hcl⟩

theorem ggDepED4_align_one {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Bs L J K : Subgroup G} {x : G} (hXL : GGResXDatumE6x p Bs L x)
    (hLd : GGResTwoNodeSideDatum p Bs L J) (hK : GGResSideDatum p Bs K J)
    (hJ : Nat.card ↥(ggAutomizer J Bs) = 192) : GGDepED4Aligned p 1 Bs L J K := by
  obtain ⟨Λ, i1, i2, b₁, b₂, Λa, i1a, i2a, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α,
    hb, hcard, hWML, hCL, hWMK, hCK, hlin, hrefl, hpairL, hpairK, fLex, fKex,
    hclosL, hclosK, hconn, hclosJ⟩ :=
    ggResTwoNodeDatum_of_sides_card_one ggWeylSimpleSystemsConjInput_holds hp2 hLd hK
  obtain ⟨Λ₁, iΛ₁f, iΛ₁d, M₁, C₁, V₁, iV₁add, iV₁mod, ι₁, φ₁, h₁, α₁, e₁,
    hM₁, hWM₁, hC₁, hlin₁, hrefl₁, hpair₁, f₁ex, hclos₁, -⟩ := hXL
  obtain ⟨f₁, hf₁⟩ := f₁ex
  obtain ⟨fL, hfL⟩ := fLex
  letI := i1; letI := i2; letI := i1a; letI := i2a; letI := i3; letI := i4
  letI := iΛ₁f; letI := iΛ₁d; letI := iV₁add; letI := iV₁mod
  haveI : Finite V₁ := Finite.of_injective ι₁.toEquiv.symm ι₁.toEquiv.symm.injective
  have hRC₁ : GGReflClosed (fun i => ggLin (p := p) ι₁ (φ₁ i)) :=
    l05nEA_reflClosed_of_datum hp2 e₁ hM₁ hWM₁ hC₁ (ι := ι₁) φ₁ h₁ α₁ hlin₁ hpair₁ hclos₁ f₁ hf₁
  have hconj : ∀ k : Λ, ∃ (w : ↥(ggAutomizer L Bs)) (i : Λ₁),
      fL (ML.simple k) = w * f₁ (M₁.simple i) * w⁻¹ :=
    l05nEA_conj_of_reflClosed (p := p) ι₁ φ₁ hclos₁ hRC₁ f₁ hf₁ fL
      (fun i => φ (Sum.inl i)) hfL (fun i => hrefl (Sum.inl i))
  obtain ⟨e₂, hML₂⟩ := l05nEA_typeE6_of_datum (p := p) e₁ hM₁ hWM₁ hWML f₁ fL hconj
  obtain ⟨MJ, hJM, hcardMJ⟩ :=
    l05nEA_card_MJ (p := p) b₁ b₂ ML hWML hCL fL (fun i => φ (Sum.inl i)) hfL hclosJ hJ
  obtain ⟨e', hML', hb1, hb2⟩ := ggDepED4_positions hb e₂ hML₂ hconn MJ hJM hcardMJ
  exact ⟨Λ, i1, i2, b₁, b₂, Λa, i1a, i2a, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α, e',
    hb1, hb2, hcard, hML', hWML, hCL, hWMK, hCK, (fun h12 => absurd h12 (by norm_num)),
    hlin, hrefl, hpairL, hpairK, hclosL, hclosK, hclosJ⟩

theorem ggDepED4_align_two_core {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {Bs L J K : Subgroup G} (hXL : GGResXDatumE6Core p Bs L)
    (hXK : GGResXDatumE6Core p Bs K) (hLd : GGResTwoNodeSideDatum p Bs L J)
    (hKd : GGResTwoNodeSideDatum p Bs K J) (hJ : Nat.card ↥(ggAutomizer J Bs) = 192) :
    GGDepED4Aligned p 2 Bs L J K := by
  obtain ⟨Λ, i1, i2, b₁, b₂, Λa, i1a, i2a, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α,
    hb, hcard, hWML, hCL, hWMK, hCK, hlin, hrefl, hpairL, hpairK, fLex, fKex,
    hclosL, hclosK, hconn, hclosJ⟩ :=
    ggResTwoNodeDatum_of_sides_card_two ggWeylSimpleSystemsConjInput_holds hp2 hLd hKd
  obtain ⟨Λ₁, iΛ₁f, iΛ₁d, M₁, C₁, V₁, iV₁add, iV₁mod, ι₁, φ₁, h₁, α₁, e₁,
    hM₁, hWM₁, hC₁, hlin₁, hrefl₁, hpair₁, f₁ex, hclos₁⟩ := hXL
  obtain ⟨f₁, hf₁⟩ := f₁ex
  obtain ⟨fL, hfL⟩ := fLex
  obtain ⟨ΛK, iΛKf, iΛKd, MK0, CK0, VK, iVKadd, iVKmod, ιK, φK0, hK0, αK0, eK0,
    hMK0, hWMK0, hCK0, hlinK0, hreflK0, hpairK0, fK0ex, hclosK0⟩ := hXK
  obtain ⟨fK0, hfK0⟩ := fK0ex
  obtain ⟨fK, hfK⟩ := fKex
  letI := i1; letI := i2; letI := i1a; letI := i2a; letI := i3; letI := i4
  letI := iΛ₁f; letI := iΛ₁d; letI := iV₁add; letI := iV₁mod
  letI := iΛKf; letI := iΛKd; letI := iVKadd; letI := iVKmod
  haveI : Finite V₁ := Finite.of_injective ι₁.toEquiv.symm ι₁.toEquiv.symm.injective
  haveI : Finite VK := Finite.of_injective ιK.toEquiv.symm ιK.toEquiv.symm.injective
  have hRC₁ : GGReflClosed (fun i => ggLin (p := p) ι₁ (φ₁ i)) :=
    l05nEA_reflClosed_of_datum hp2 e₁ hM₁ hWM₁ hC₁ (ι := ι₁) φ₁ h₁ α₁ hlin₁ hpair₁ hclos₁ f₁ hf₁
  have hconj : ∀ k : Λ, ∃ (w : ↥(ggAutomizer L Bs)) (i : Λ₁),
      fL (ML.simple k) = w * f₁ (M₁.simple i) * w⁻¹ :=
    l05nEA_conj_of_reflClosed (p := p) ι₁ φ₁ hclos₁ hRC₁ f₁ hf₁ fL
      (fun i => φ (Sum.inl i)) hfL (fun i => hrefl (Sum.inl i))
  obtain ⟨e₂, hML₂⟩ := l05nEA_typeE6_of_datum (p := p) e₁ hM₁ hWM₁ hWML f₁ fL hconj
  have hRCK : GGReflClosed (fun i => ggLin (p := p) ιK (φK0 i)) :=
    l05nEA_reflClosed_of_datum hp2 eK0 hMK0 hWMK0 hCK0 (ι := ιK) φK0 hK0 αK0 hlinK0 hpairK0
      hclosK0 fK0 hfK0
  have hconjK : ∀ k : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} ⊕ Λa,
      ∃ (w : ↥(ggAutomizer K Bs)) (i : ΛK),
        fK (MK.simple k) = w * fK0 (MK0.simple i) * w⁻¹ :=
    l05nEA_conj_of_reflClosed (p := p) ιK φK0 hclosK0 hRCK fK0 hfK0 fK
      (fun o => φ (o.map Subtype.val id)) hfK (fun o => hrefl (o.map Subtype.val id))
  obtain ⟨eK, hMKeq⟩ := l05nEA_typeE6_of_datum (p := p) eK0 hMK0 hWMK0 hWMK fK0 fK hconjK
  obtain ⟨MJ, hJM, hcardMJ⟩ :=
    l05nEA_card_MJ (p := p) b₁ b₂ ML hWML hCL fL (fun i => φ (Sum.inl i)) hfL hclosJ hJ
  obtain ⟨e', hML', hb1, hb2⟩ := ggDepED4_positions hb e₂ hML₂ hconn MJ hJM hcardMJ
  exact ⟨Λ, i1, i2, b₁, b₂, Λa, i1a, i2a, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α, e',
    hb1, hb2, hcard, hML', hWML, hCL, hWMK, hCK, (fun _ => ⟨eK, hMKeq⟩),
    hlin, hrefl, hpairL, hpairK, hclosL, hclosK, hclosJ⟩

theorem ggDepED4_align_two {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Bs L J K : Subgroup G} {x y : G} (hXL : GGResXDatumE6x p Bs L x)
    (hXK : GGResXDatumE6x p Bs K y) (hLd : GGResTwoNodeSideDatum p Bs L J)
    (hKd : GGResTwoNodeSideDatum p Bs K J) (hJ : Nat.card ↥(ggAutomizer J Bs) = 192) :
    GGDepED4Aligned p 2 Bs L J K :=
  ggDepED4_align_two_core hp2 hXL.core hXK.core hLd hKd hJ

end CFSG.StandardType

end
