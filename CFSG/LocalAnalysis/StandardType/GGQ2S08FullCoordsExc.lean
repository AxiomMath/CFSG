module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08FullCoords

public section

namespace CFSG.StandardType

@[expose] def e7β : Fin 7 → TestLin.Vn 8 :=
  ![![1, 2, 2, 2, 1, 1, 1, 2], ![2, 1, 1, 2, 2, 1, 1, 2], ![2, 1, 1, 2, 1, 2, 2, 1],
    ![1, 2, 2, 1, 2, 1, 2, 1], ![2, 1, 2, 1, 1, 2, 1, 2], ![1, 2, 1, 2, 2, 2, 1, 1],
    ![2, 2, 1, 1, 1, 1, 2, 2]]

@[expose] def e7Inv : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  !![2, 2, 0, 1, 0, 2, 1;
     2, 2, 1, 0, 0, 0, 0;
     0, 1, 0, 2, 0, 1, 2;
     1, 0, 2, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 2, 1;
     2, 0, 1, 0, 2, 1, 2;
     1, 0, 2, 0, 1, 2, 0]

@[expose] def e7RootQ : TestLin.Vn 8 →ₗ[ZMod 3] (Option (Fin 7) → ZMod 3) :=
  LinearMap.pi fun o => match o with
    | none => (2 : ZMod 3) • ∑ i : Fin 8, coord i
    | some j => ∑ k : Fin 8, e7β j k • coord k

@[expose] def e7Rec : (Option (Fin 7) → ZMod 3) →ₗ[ZMod 3] TestLin.Vn 8 :=
  LinearMap.pi fun k : Fin 8 =>
    coord (ι := Option (Fin 7)) none +
      ∑ i : Fin 7, (∑ j : Fin 7, e7Inv j i * e7β j k) • coord (ι := Option (Fin 7)) (some i)

@[expose] def e7FullX : TestLin.Vn 8 := fun _ => 1

@[expose] def e7FullS (k : Fin 7) : TestLin.Vn 8 ≃ₗ[ZMod 3] TestLin.Vn 8 :=
  TestLin.refl (e7β k) (e7β k) (by fin_cases k <;> decide +kernel)

theorem ggQ2_fullCoords_E7 {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hx : M.xV ∉ M.coSpan) (e : Fin 7 ≃ M.Λ)
    (hC : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.E₇ i j) :
    ∃ κ : M.V ≃ₗ[ZMod 3] TestLin.Vn 8, κ M.xV = e7FullX ∧
      ∀ k v, κ (ggLin (p := 3) M.model (M.simple (e k)) (κ.symm v)) = e7FullS k v := by
  have hρ : Function.Surjective M.rootMap := by
    refine ggQ2LDatum_rootMap_surjective M
      (isUnit_cartan_det_of_reindex M e CartanMatrix.E₇ hC ?_)
    rw [show CartanMatrix.E₇.map (Int.castRingHom (ZMod 3)) =
        (Int.castRingHom (ZMod 3)).mapMatrix CartanMatrix.E₇ from rfl]
    rw [← RingHom.map_det (Int.castRingHom (ZMod 3)) CartanMatrix.E₇,
      CartanMatrix.E_det (by norm_num : 3 ≤ 7)]
    exact isUnit_iff_ne_zero.mpr (by decide)
  have hQP : ∀ y : Option (Fin 7) → ZMod 3, e7RootQ (e7Rec y) = y := by
    apply leftInverse_of_basis
    intro o
    cases o with
    | none => decide +kernel
    | some j => fin_cases j <;> decide +kernel
  have hPQ : ∀ v : TestLin.Vn 8, e7Rec (e7RootQ v) = v := by
    apply rightInverse_of_basis
    intro a
    fin_cases a <;> decide +kernel
  have hQx : e7RootQ e7FullX = Pi.single none 1 := by decide +kernel
  have hQS : ∀ k : Fin 7, e7RootQ.comp (e7FullS k).toLinearMap =
      (rootCoordReflLin CartanMatrix.E₇ k).comp e7RootQ := by
    intro k
    apply linearMap_eq_of_basis
    intro a
    fin_cases k <;> fin_cases a <;> decide +kernel
  obtain ⟨P, hPx, hPS⟩ :=
    coordsData e7RootQ e7Rec e7FullX e7FullS CartanMatrix.E₇ hQP hPQ hQx hQS
  exact ggQ2LDatum_coords_of_root M hρ hx e CartanMatrix.E₇ hC P e7FullX e7FullS hPx hPS

@[expose] def e8β : Fin 8 → TestLin.Vn 8 :=
  ![![2, 1, 1, 1, 1, 1, 1, 2], ![1, 1, 0, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0, 0, 0],
    ![0, 2, 1, 0, 0, 0, 0, 0], ![0, 0, 2, 1, 0, 0, 0, 0], ![0, 0, 0, 2, 1, 0, 0, 0],
    ![0, 0, 0, 0, 2, 1, 0, 0], ![0, 0, 0, 0, 0, 2, 1, 0]]

@[expose] def e8β9 (j : Fin 8) : TestLin.Vn 9 :=
  fun i => if h : i.val < 8 then e8β j ⟨i.val, h⟩ else 0

@[expose] def e8Inv : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  !![1, 2, 1, 1, 2, 0, 1, 2;
     2, 2, 1, 0, 0, 0, 0, 0;
     1, 1, 2, 2, 1, 0, 2, 1;
     1, 0, 2, 0, 0, 0, 0, 0;
     2, 0, 1, 0, 2, 0, 1, 2;
     0, 0, 0, 0, 0, 0, 2, 1;
     1, 0, 2, 0, 1, 2, 0, 0;
     2, 0, 1, 0, 2, 1, 0, 2]

@[expose] def e8RootQ : TestLin.Vn 9 →ₗ[ZMod 3] (Option (Fin 8) → ZMod 3) :=
  LinearMap.pi fun o => match o with
    | none => coord (Fin.last 8)
    | some j => ∑ k : Fin 8, e8β j k • coord (Fin.castSucc k)

@[expose] def e8Rec : (Option (Fin 8) → ZMod 3) →ₗ[ZMod 3] TestLin.Vn 9 :=
  LinearMap.pi fun k : Fin 9 =>
    if h : k.val < 8 then
      ∑ i : Fin 8, (∑ j : Fin 8, e8Inv j i * e8β j ⟨k.val, h⟩) •
        coord (ι := Option (Fin 8)) (some i)
    else coord (ι := Option (Fin 8)) none

@[expose] def e8FullX : TestLin.Vn 9 := Pi.single (Fin.last 8) 1

@[expose] def e8FullS (k : Fin 8) : TestLin.Vn 9 ≃ₗ[ZMod 3] TestLin.Vn 9 :=
  TestLin.refl (e8β9 k) (e8β9 k) (by fin_cases k <;> decide +kernel)

theorem ggQ2_fullCoords_E8 {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hx : M.xV ∉ M.coSpan) (e : Fin 8 ≃ M.Λ)
    (hC : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.E₈ i j) :
    ∃ κ : M.V ≃ₗ[ZMod 3] TestLin.Vn 9, κ M.xV = e8FullX ∧
      ∀ k v, κ (ggLin (p := 3) M.model (M.simple (e k)) (κ.symm v)) = e8FullS k v := by
  have hρ : Function.Surjective M.rootMap := by
    refine ggQ2LDatum_rootMap_surjective M
      (isUnit_cartan_det_of_reindex M e CartanMatrix.E₈ hC ?_)
    rw [show CartanMatrix.E₈.map (Int.castRingHom (ZMod 3)) =
        (Int.castRingHom (ZMod 3)).mapMatrix CartanMatrix.E₈ from rfl]
    rw [← RingHom.map_det (Int.castRingHom (ZMod 3)) CartanMatrix.E₈,
      CartanMatrix.E_det (by norm_num : 3 ≤ 8)]
    exact isUnit_iff_ne_zero.mpr (by decide)
  have hQP : ∀ y : Option (Fin 8) → ZMod 3, e8RootQ (e8Rec y) = y := by
    apply leftInverse_of_basis
    intro o
    cases o with
    | none => decide +kernel
    | some j => fin_cases j <;> decide +kernel
  have hPQ : ∀ v : TestLin.Vn 9, e8Rec (e8RootQ v) = v := by
    apply rightInverse_of_basis
    intro a
    fin_cases a <;> decide +kernel
  have hQx : e8RootQ e8FullX = Pi.single none 1 := by decide +kernel
  have hQS : ∀ k : Fin 8, e8RootQ.comp (e8FullS k).toLinearMap =
      (rootCoordReflLin CartanMatrix.E₈ k).comp e8RootQ := by
    intro k
    apply linearMap_eq_of_basis
    intro a
    fin_cases k <;> fin_cases a <;> decide +kernel
  obtain ⟨P, hPx, hPS⟩ :=
    coordsData e8RootQ e8Rec e8FullX e8FullS CartanMatrix.E₈ hQP hPQ hQx hQS
  exact ggQ2LDatum_coords_of_root M hρ hx e CartanMatrix.E₈ hC P e8FullX e8FullS hPx hPS

@[expose] def f4α : Fin 4 → TestLin.Vn 4 :=
  ![![0, 1, 2, 0], ![0, 0, 1, 2], ![0, 0, 0, 1], ![2, 1, 1, 1]]

@[expose] def f4h : Fin 4 → TestLin.Vn 4 :=
  ![![0, 1, 2, 0], ![0, 0, 1, 2], ![0, 0, 0, 2], ![1, 2, 2, 2]]

@[expose] def f4α5 (j : Fin 4) : TestLin.Vn 5 :=
  fun i => if h : i.val < 4 then f4α j ⟨i.val, h⟩ else 0

@[expose] def f4h5 (j : Fin 4) : TestLin.Vn 5 :=
  fun i => if h : i.val < 4 then f4h j ⟨i.val, h⟩ else 0

@[expose] def f4Ginv : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  !![2, 0, 1, 2;
     0, 0, 2, 1;
     1, 2, 0, 0;
     2, 1, 0, 1]

@[expose] def f4Hinv : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  !![2, 0, 2, 1;
     0, 0, 1, 2;
     2, 1, 0, 0;
     1, 2, 0, 1]

@[expose] def f4RootQ : TestLin.Vn 5 →ₗ[ZMod 3] (Option (Fin 4) → ZMod 3) :=
  LinearMap.pi fun o => match o with
    | none => coord (Fin.last 4)
    | some j => ∑ k : Fin 4, f4α j k • coord (Fin.castSucc k)

@[expose] def f4Rec : (Option (Fin 4) → ZMod 3) →ₗ[ZMod 3] TestLin.Vn 5 :=
  LinearMap.pi fun k : Fin 5 =>
    if h : k.val < 4 then
      ∑ i : Fin 4, (∑ j : Fin 4, f4Ginv j i * f4α j ⟨k.val, h⟩) •
        coord (ι := Option (Fin 4)) (some i)
    else coord (ι := Option (Fin 4)) none

@[expose] def f4FullX : TestLin.Vn 5 := Pi.single (Fin.last 4) 1

@[expose] def f4FullS (k : Fin 4) : TestLin.Vn 5 ≃ₗ[ZMod 3] TestLin.Vn 5 :=
  TestLin.refl (f4h5 k) (f4α5 k) (by fin_cases k <;> decide +kernel)

theorem ggQ2_fullCoords_F4 {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hx : M.xV ∉ M.coSpan) (e : Fin 4 ≃ M.Λ)
    (hC : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.F₄ i j) :
    ∃ κ : M.V ≃ₗ[ZMod 3] TestLin.Vn 5, κ M.xV = f4FullX ∧
      ∀ k v, κ (ggLin (p := 3) M.model (M.simple (e k)) (κ.symm v)) = f4FullS k v := by
  have hρ : Function.Surjective M.rootMap := by
    refine ggQ2LDatum_rootMap_surjective M
      (isUnit_cartan_det_of_reindex M e CartanMatrix.F₄ hC ?_)
    rw [show CartanMatrix.F₄.map (Int.castRingHom (ZMod 3)) =
        (Int.castRingHom (ZMod 3)).mapMatrix CartanMatrix.F₄ from rfl]
    rw [← RingHom.map_det (Int.castRingHom (ZMod 3)) CartanMatrix.F₄, CartanMatrix.F₄_det]
    exact isUnit_iff_ne_zero.mpr (by decide)
  have hQP : ∀ y : Option (Fin 4) → ZMod 3, f4RootQ (f4Rec y) = y := by
    apply leftInverse_of_basis
    intro o
    cases o with
    | none => decide +kernel
    | some j => fin_cases j <;> decide +kernel
  have hPQ : ∀ v : TestLin.Vn 5, f4Rec (f4RootQ v) = v := by
    apply rightInverse_of_basis
    intro a
    fin_cases a <;> decide +kernel
  have hQx : f4RootQ f4FullX = Pi.single none 1 := by decide +kernel
  have hQS : ∀ k : Fin 4, f4RootQ.comp (f4FullS k).toLinearMap =
      (rootCoordReflLin CartanMatrix.F₄ k).comp f4RootQ := by
    intro k
    apply linearMap_eq_of_basis
    intro a
    fin_cases k <;> fin_cases a <;> decide +kernel
  obtain ⟨P, hPx, hPS⟩ :=
    coordsData f4RootQ f4Rec f4FullX f4FullS CartanMatrix.F₄ hQP hPQ hQx hQS
  exact ggQ2LDatum_coords_of_root M hρ hx e CartanMatrix.F₄ hC P f4FullX f4FullS hPx hPS

@[expose] def f4tRootQ : TestLin.Vn 5 →ₗ[ZMod 3] (Option (Fin 4) → ZMod 3) :=
  LinearMap.pi fun o => match o with
    | none => coord (Fin.last 4)
    | some j => ∑ k : Fin 4, f4h j k • coord (Fin.castSucc k)

@[expose] def f4tRec : (Option (Fin 4) → ZMod 3) →ₗ[ZMod 3] TestLin.Vn 5 :=
  LinearMap.pi fun k : Fin 5 =>
    if h : k.val < 4 then
      ∑ i : Fin 4, (∑ j : Fin 4, f4Hinv j i * f4h j ⟨k.val, h⟩) •
        coord (ι := Option (Fin 4)) (some i)
    else coord (ι := Option (Fin 4)) none

theorem ggQ2_fullCoords_F4t {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hx : M.xV ∉ M.coSpan) (e : Fin 4 ≃ M.Λ)
    (hC : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.F₄.transpose i j) :
    ∃ κ : M.V ≃ₗ[ZMod 3] TestLin.Vn 5, κ M.xV = f4FullX ∧
      ∀ k v, κ (ggLin (p := 3) M.model (M.simple (e k)) (κ.symm v)) = f4FullS k v := by
  have hρ : Function.Surjective M.rootMap := by
    refine ggQ2LDatum_rootMap_surjective M
      (isUnit_cartan_det_of_reindex M e CartanMatrix.F₄.transpose hC ?_)
    rw [show (CartanMatrix.F₄.transpose).map (Int.castRingHom (ZMod 3)) =
        (Int.castRingHom (ZMod 3)).mapMatrix (CartanMatrix.F₄.transpose) from rfl]
    rw [← RingHom.map_det (Int.castRingHom (ZMod 3)) (CartanMatrix.F₄.transpose),
      Matrix.det_transpose, CartanMatrix.F₄_det]
    exact isUnit_iff_ne_zero.mpr (by decide)
  have hQP : ∀ y : Option (Fin 4) → ZMod 3, f4tRootQ (f4tRec y) = y := by
    apply leftInverse_of_basis
    intro o
    cases o with
    | none => decide +kernel
    | some j => fin_cases j <;> decide +kernel
  have hPQ : ∀ v : TestLin.Vn 5, f4tRec (f4tRootQ v) = v := by
    apply rightInverse_of_basis
    intro a
    fin_cases a <;> decide +kernel
  have hQx : f4tRootQ f4FullX = Pi.single none 1 := by decide +kernel
  have hQS : ∀ k : Fin 4, f4tRootQ.comp (f4FullS k).toLinearMap =
      (rootCoordReflLin CartanMatrix.F₄.transpose k).comp f4tRootQ := by
    intro k
    apply linearMap_eq_of_basis
    intro a
    fin_cases k <;> fin_cases a <;> decide +kernel
  obtain ⟨P, hPx, hPS⟩ :=
    coordsData f4tRootQ f4tRec f4FullX f4FullS CartanMatrix.F₄.transpose hQP hPQ hQx hQS
  exact ggQ2LDatum_coords_of_root M hρ hx e CartanMatrix.F₄.transpose hC P f4FullX f4FullS
    hPx hPS

end CFSG.StandardType

end
