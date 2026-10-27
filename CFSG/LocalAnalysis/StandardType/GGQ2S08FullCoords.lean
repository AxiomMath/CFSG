module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08SplitCoords
public import CFSG.LocalAnalysis.StandardType.GGQ2S08Cartan
public import CFSG.LocalAnalysis.StandardType.GGQ2S08TestLin
import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2LDatum_coords_of_root {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hρ : Function.Surjective M.rootMap) (hx : M.xV ∉ M.coSpan)
    {ℓ n : ℕ} (e : Fin ℓ ≃ M.Λ) (C₀ : Matrix (Fin ℓ) (Fin ℓ) ℤ)
    (hC : ∀ i j, M.cartan (e i) (e j) = C₀ i j)
    (P : (Option (Fin ℓ) → ZMod 3) ≃ₗ[ZMod 3] TestLin.Vn n) (x₀ : TestLin.Vn n)
    (S : Fin ℓ → (TestLin.Vn n ≃ₗ[ZMod 3] TestLin.Vn n))
    (hPx : P (Pi.single none 1) = x₀)
    (hPS : ∀ i v, P (ggQ2RootCoordRefl C₀ i (P.symm v)) = S i v) :
    ∃ κ : M.V ≃ₗ[ZMod 3] TestLin.Vn n, κ M.xV = x₀ ∧
      ∀ i v, κ (ggLin (p := 3) M.model (M.simple (e i)) (κ.symm v)) = S i v := by
  obtain ⟨κ, hκx, -, hκact⟩ := ggQ2LDatum_rootCoords M hρ hx
  let R : (Option M.Λ → ZMod 3) ≃ₗ[ZMod 3] (Option (Fin ℓ) → ZMod 3) :=
    LinearEquiv.funCongrLeft (ZMod 3) (ZMod 3) (Equiv.optionCongr e)
  let κ₁ : M.V ≃ₗ[ZMod 3] (Option (Fin ℓ) → ZMod 3) := κ.trans R
  let κ₂ : M.V ≃ₗ[ZMod 3] TestLin.Vn n := κ₁.trans P
  have hR_one : R (Pi.single none (1 : ZMod 3)) = Pi.single none 1 := by
    funext o
    cases o with
    | none => rfl
    | some i => rfl
  have hR_refl : ∀ (i : Fin ℓ) (w : Option M.Λ → ZMod 3),
      R (ggQ2RootCoordRefl M.cartan (e i) w) = ggQ2RootCoordRefl C₀ i (R w) := by
    intro i w
    funext o
    cases o with
    | none => rfl
    | some a =>
        show w (some (e a)) - w (some (e i)) * (M.cartan (e a) (e i) : ZMod 3) =
          (R w) (some a) - (R w) (some i) * (C₀ a i : ZMod 3)
        rw [show (R w) (some a) = w (some (e a)) from rfl,
          show (R w) (some i) = w (some (e i)) from rfl, hC a i]
  refine ⟨κ₂, ?_, ?_⟩
  · calc κ₂ M.xV = P (R (κ M.xV)) := rfl
      _ = P (R (Pi.single none 1)) := by rw [hκx]
      _ = P (Pi.single none 1) := by rw [hR_one]
      _ = x₀ := hPx
  · intro i v
    have hRw : R (κ (κ₂.symm v)) = P.symm v := by
      have h1 : κ₂ (κ₂.symm v) = v := LinearEquiv.apply_symm_apply κ₂ v
      have h2 : P (R (κ (κ₂.symm v))) = v := by
        simpa only [κ₂, κ₁, LinearEquiv.trans_apply] using h1
      simpa using congrArg P.symm h2
    have hstep : κ (ggLin (p := 3) M.model (M.simple (e i)) (κ₂.symm v)) =
        ggQ2RootCoordRefl M.cartan (e i) (κ (κ₂.symm v)) := by
      have := hκact (e i) (κ (κ₂.symm v))
      simpa using this
    calc κ₂ (ggLin (p := 3) M.model (M.simple (e i)) (κ₂.symm v))
        = P (R (κ (ggLin (p := 3) M.model (M.simple (e i)) (κ₂.symm v)))) := rfl
      _ = P (R (ggQ2RootCoordRefl M.cartan (e i) (κ (κ₂.symm v)))) := by rw [hstep]
      _ = P (ggQ2RootCoordRefl C₀ i (R (κ (κ₂.symm v)))) := by rw [hR_refl]
      _ = P (ggQ2RootCoordRefl C₀ i (P.symm v)) := by rw [hRw]
      _ = S i v := hPS i v

theorem ggQ2LDatum_rootMap_surjective {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hdet : IsUnit (M.cartan.map (Int.castRingHom (ZMod 3))).det) :
    Function.Surjective M.rootMap := by
  classical
  let Cm : Matrix M.Λ M.Λ (ZMod 3) := M.cartan.map (Int.castRingHom (ZMod 3))
  have hunit : IsUnit Cm := (Matrix.isUnit_iff_isUnit_det Cm).mpr hdet
  have hinj_fun : Function.Injective Cm.mulVec :=
    (Matrix.mulVec_injective_iff_isUnit).mpr hunit
  obtain ⟨u, hu⟩ := hunit
  intro w
  let c : M.Λ → ZMod 3 := (↑(u⁻¹) : Matrix M.Λ M.Λ (ZMod 3)).mulVec w
  have hc : Cm.mulVec c = w := by
    have h1 : Cm.mulVec c = (u : Matrix M.Λ M.Λ (ZMod 3)).mulVec
        ((↑(u⁻¹) : Matrix M.Λ M.Λ (ZMod 3)).mulVec w) := by
      rw [← hu]
    rw [h1, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  refine ⟨∑ j, c j • M.coroot j, ?_⟩
  funext i
  rw [show M.rootMap (∑ j, c j • M.coroot j) i =
      M.root i (∑ j, c j • M.coroot j) from rfl]
  rw [map_sum]
  simp only [map_smul, M.pairing, smul_eq_mul]
  rw [← hc]
  simp only [Cm, Matrix.mulVec, dotProduct, Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro j _
  change c j * (M.cartan i j : ZMod 3) = (M.cartan i j : ZMod 3) * c j
  ring

@[expose] def coord {ι : Type} [DecidableEq ι] (i : ι) : (ι → ZMod 3) →ₗ[ZMod 3] ZMod 3 where
  toFun v := v i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coord_apply {ι : Type} [DecidableEq ι] (i : ι) (v : ι → ZMod 3) :
    coord i v = v i := rfl

@[expose] def aIdx (N : ℕ) (j : Fin (N - 1)) : Fin N :=
  ⟨j.val, by have := j.isLt; omega⟩

@[expose] def aIdxSucc (N : ℕ) (j : Fin (N - 1)) : Fin N :=
  ⟨j.val + 1, by have := j.isLt; omega⟩

@[expose] def fIdx (r : ℕ) (j : Fin r) : Fin (r + 1) :=
  ⟨j.val, by have := j.isLt; omega⟩

@[expose] def fIdxSucc (r : ℕ) (j : Fin r) : Fin (r + 1) :=
  ⟨j.val + 1, by have := j.isLt; omega⟩

@[expose] def fPred (r : ℕ) (j : Fin r) : Fin (r + 1) :=
  ⟨j.val - 1, by have := j.isLt; omega⟩

@[expose] def aRootQ (N : ℕ) : TestLin.Vn N →ₗ[ZMod 3] (Option (Fin (N - 1)) → ZMod 3) :=
  LinearMap.pi fun o => match o with
    | none => (N : ZMod 3)⁻¹ • ∑ i : Fin N, coord i
    | some j => coord (ι := Fin N) (aIdx N j) + (-1 : ZMod 3) • coord (ι := Fin N) (aIdxSucc N j)

@[expose] def bRootQ (r : ℕ) : TestLin.Vn (r + 1) →ₗ[ZMod 3] (Option (Fin r) → ZMod 3) :=
  LinearMap.pi fun o => match o with
    | none => coord (Fin.last r)
    | some j =>
        if j.val + 1 < r then coord (ι := Fin (r + 1)) (fIdx r j) +
          (-1 : ZMod 3) • coord (ι := Fin (r + 1)) (fIdxSucc r j)
        else coord (ι := Fin (r + 1)) (fIdx r j)

@[expose] def cRootQ (r : ℕ) : TestLin.Vn (r + 1) →ₗ[ZMod 3] (Option (Fin r) → ZMod 3) :=
  LinearMap.pi fun o => match o with
    | none => coord (Fin.last r)
    | some j =>
        if j.val + 1 < r then coord (ι := Fin (r + 1)) (fIdx r j) +
          (-1 : ZMod 3) • coord (ι := Fin (r + 1)) (fIdxSucc r j)
        else (2 : ZMod 3) • coord (ι := Fin (r + 1)) (fIdx r j)

@[expose] def dRootQ (r : ℕ) : TestLin.Vn (r + 1) →ₗ[ZMod 3] (Option (Fin r) → ZMod 3) :=
  LinearMap.pi fun o => match o with
    | none => coord (Fin.last r)
    | some j =>
        if j.val + 1 < r then coord (ι := Fin (r + 1)) (fIdx r j) +
          (-1 : ZMod 3) • coord (ι := Fin (r + 1)) (fIdxSucc r j)
        else coord (ι := Fin (r + 1)) (fPred r j) + coord (ι := Fin (r + 1)) (fIdx r j)

@[expose] def aRec (N : ℕ) : (Option (Fin (N - 1)) → ZMod 3) →ₗ[ZMod 3] TestLin.Vn N :=
  LinearMap.pi fun k : Fin N =>
    coord (ι := Option (Fin (N - 1))) none +
      ∑ j : Fin (N - 1),
        ((N : ZMod 3)⁻¹ * ((N - 1 - j.val : ℕ) : ZMod 3) -
          (if j.val < k.val then 1 else 0)) • coord (ι := Option (Fin (N - 1))) (some j)

@[expose] def bRec (r : ℕ) : (Option (Fin r) → ZMod 3) →ₗ[ZMod 3] TestLin.Vn (r + 1) :=
  LinearMap.pi fun k : Fin (r + 1) =>
    if k = Fin.last r then coord (ι := Option (Fin r)) none
    else ∑ j : Fin r, (if k.val ≤ j.val then coord (ι := Option (Fin r)) (some j) else 0)

@[expose] def cRec (r : ℕ) : (Option (Fin r) → ZMod 3) →ₗ[ZMod 3] TestLin.Vn (r + 1) :=
  LinearMap.pi fun k : Fin (r + 1) =>
    if k = Fin.last r then coord (ι := Option (Fin r)) none
    else ∑ j : Fin r,
      (if k.val ≤ j.val then
        (if j.val = r - 1 then (2 : ZMod 3)⁻¹ else 1) • coord (ι := Option (Fin r)) (some j)
      else 0)

@[expose] def dRec (r : ℕ) (hr : 2 ≤ r) :
    (Option (Fin r) → ZMod 3) →ₗ[ZMod 3] TestLin.Vn (r + 1) :=
  LinearMap.pi fun k : Fin (r + 1) =>
    if k = Fin.last r then coord (ι := Option (Fin r)) none
    else if k.val + 2 ≤ r then
      (∑ j : Fin r,
        (if k.val ≤ j.val ∧ j.val ≤ r - 3 then coord (ι := Option (Fin r)) (some j) else 0)) +
        (2 : ZMod 3)⁻¹ • (coord (ι := Option (Fin r)) (some ⟨r - 2, by omega⟩) +
          coord (ι := Option (Fin r)) (some ⟨r - 1, by omega⟩))
    else
      (2 : ZMod 3)⁻¹ • (coord (ι := Option (Fin r)) (some ⟨r - 1, by omega⟩) +
        (-1 : ZMod 3) • coord (ι := Option (Fin r)) (some ⟨r - 2, by omega⟩))

@[expose] def aFullS (N : ℕ) (k : Fin (N - 1)) : TestLin.Vn N ≃ₗ[ZMod 3] TestLin.Vn N :=
  LinearEquiv.funCongrLeft (ZMod 3) (ZMod 3) (Equiv.swap (aIdx N k) (aIdxSucc N k))

@[expose] def negCoord {n : ℕ} (i : Fin n) : TestLin.Vn n ≃ₗ[ZMod 3] TestLin.Vn n :=
  TestLin.refl (Pi.single i 1) (2 • Pi.single i 1) (by
    rw [dotProduct, Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hi
      exact absurd (Finset.mem_univ i) hi)

@[expose] def bcFullS (r : ℕ) (k : Fin r) : TestLin.Vn (r + 1) ≃ₗ[ZMod 3] TestLin.Vn (r + 1) :=
  if k.val + 1 < r then
    LinearEquiv.funCongrLeft (ZMod 3) (ZMod 3) (Equiv.swap (fIdx r k) (fIdxSucc r k))
  else negCoord (fIdx r k)

@[expose] def dFullS (r : ℕ) (k : Fin r) : TestLin.Vn (r + 1) ≃ₗ[ZMod 3] TestLin.Vn (r + 1) :=
  if k.val + 1 < r then
    LinearEquiv.funCongrLeft (ZMod 3) (ZMod 3) (Equiv.swap (fIdx r k) (fIdxSucc r k))
  else
    negCoord (fPred r k) * negCoord (fIdx r k) *
      LinearEquiv.funCongrLeft (ZMod 3) (ZMod 3) (Equiv.swap (fPred r k) (fIdx r k))

@[expose] def aFullX (N : ℕ) : TestLin.Vn N := fun _ => 1

@[expose] def frameFullX (r : ℕ) : TestLin.Vn (r + 1) := Pi.single (Fin.last r) 1

@[expose] def coordSubMul {ι : Type} [DecidableEq ι] (i k : ι) (a : ZMod 3) :
    (ι → ZMod 3) →ₗ[ZMod 3] ZMod 3 where
  toFun v := v i - v k * a
  map_add' v w := by
    simp only [Pi.add_apply]
    ring
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[expose] def rootCoordReflLin {ι : Type} [DecidableEq ι] (C : Matrix ι ι ℤ) (k : ι) :
    (Option ι → ZMod 3) →ₗ[ZMod 3] (Option ι → ZMod 3) :=
  LinearMap.pi fun o => match o with
    | none => coord (ι := Option ι) none
    | some j => coordSubMul (some j) (some k) (C j k : ZMod 3)

private lemma rootCoordReflLin_apply {ι : Type} [DecidableEq ι] (C : Matrix ι ι ℤ) (k : ι)
    (v : Option ι → ZMod 3) :
    rootCoordReflLin C k v = ggQ2RootCoordRefl C k v := by
  funext o
  cases o with
  | none => rfl
  | some j => rfl

lemma linearMap_eq_of_basis {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {f g : (ι → ZMod 3) →ₗ[ZMod 3] (κ → ZMod 3)}
    (h : ∀ i, f (Pi.single i 1) = g (Pi.single i 1)) : f = g :=
  (Pi.basisFun (ZMod 3) ι).ext (fun i => by simpa only [Pi.basisFun_apply] using h i)

lemma leftInverse_of_basis {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    {Q : TestLin.Vn n →ₗ[ZMod 3] (Option ι → ZMod 3)}
    {P : (Option ι → ZMod 3) →ₗ[ZMod 3] TestLin.Vn n}
    (h : ∀ o : Option ι, Q (P (Pi.single o 1)) = Pi.single o 1) :
    ∀ y, Q (P y) = y := by
  have hcomp : Q.comp P = 1 := (Pi.basisFun (ZMod 3) (Option ι)).ext (fun o => by
    simpa using h o)
  intro y
  have := congrArg (fun f : (Option ι → ZMod 3) →ₗ[ZMod 3] (Option ι → ZMod 3) => f y) hcomp
  simpa [LinearMap.comp_apply] using this

lemma rightInverse_of_basis {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    {Q : TestLin.Vn n →ₗ[ZMod 3] (Option ι → ZMod 3)}
    {P : (Option ι → ZMod 3) →ₗ[ZMod 3] TestLin.Vn n}
    (h : ∀ a : Fin n, P (Q (Pi.single a 1)) = Pi.single a 1) :
    ∀ v, P (Q v) = v := by
  have hcomp : P.comp Q = 1 := (Pi.basisFun (ZMod 3) (Fin n)).ext (fun a => by
    simpa using h a)
  intro v
  have := congrArg (fun f : TestLin.Vn n →ₗ[ZMod 3] TestLin.Vn n => f v) hcomp
  simpa [LinearMap.comp_apply] using this

lemma coordsData {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (Q : TestLin.Vn n →ₗ[ZMod 3] (Option ι → ZMod 3))
    (Plin : (Option ι → ZMod 3) →ₗ[ZMod 3] TestLin.Vn n)
    (x0 : TestLin.Vn n) (S : ι → TestLin.Vn n ≃ₗ[ZMod 3] TestLin.Vn n)
    (C : Matrix ι ι ℤ)
    (hQP : ∀ y, Q (Plin y) = y)
    (hPQ : ∀ v, Plin (Q v) = v)
    (hQx : Q x0 = Pi.single none 1)
    (hQS : ∀ k, Q.comp (S k).toLinearMap = (rootCoordReflLin C k).comp Q) :
    ∃ P : (Option ι → ZMod 3) ≃ₗ[ZMod 3] TestLin.Vn n,
      P (Pi.single none 1) = x0 ∧
      ∀ k v, P (ggQ2RootCoordRefl C k (P.symm v)) = S k v := by
  have hsurj : Function.Surjective Q := fun y => ⟨Plin y, hQP y⟩
  have hinj : Function.Injective Q := by
    intro u v huv
    calc u = Plin (Q u) := (hPQ u).symm
      _ = Plin (Q v) := by rw [huv]
      _ = v := hPQ v
  let QEquiv : TestLin.Vn n ≃ₗ[ZMod 3] (Option ι → ZMod 3) :=
    LinearEquiv.ofBijective Q ⟨hinj, hsurj⟩
  let P : (Option ι → ZMod 3) ≃ₗ[ZMod 3] TestLin.Vn n := QEquiv.symm
  have hQ_apply : ∀ v, QEquiv v = Q v := fun v => LinearEquiv.ofBijective_apply ..
  refine ⟨P, ?_, ?_⟩
  · have h1 : QEquiv (P (Pi.single none 1)) = Pi.single none 1 :=
      LinearEquiv.apply_symm_apply QEquiv (Pi.single none 1)
    have h2 : QEquiv x0 = Pi.single none 1 := by rw [hQ_apply]; exact hQx
    exact QEquiv.injective (h1.trans h2.symm)
  · intro k v
    have hQSv : Q (S k v) = rootCoordReflLin C k (Q v) := by
      have := congrArg (fun f : TestLin.Vn n →ₗ[ZMod 3] (Option ι → ZMod 3) => f v) (hQS k)
      simpa [LinearMap.comp_apply] using this
    calc P (ggQ2RootCoordRefl C k (P.symm v))
        = P (ggQ2RootCoordRefl C k (Q v)) := by
            rw [show P.symm = QEquiv from rfl, hQ_apply]
      _ = P (rootCoordReflLin C k (Q v)) := by rw [← rootCoordReflLin_apply]
      _ = P (Q (S k v)) := by rw [← hQSv]
      _ = S k v := by
            rw [show Q (S k v) = QEquiv (S k v) from (hQ_apply (S k v)).symm]
            change QEquiv.symm (QEquiv (S k v)) = S k v
            rw [LinearEquiv.symm_apply_apply]

lemma isUnit_cartan_det_of_reindex {ℓ : ℕ} {G : Type} [Group G] {Bs L : Subgroup G}
    {x : G} (M : GGQ2LDatum 3 Bs L x) (e : Fin ℓ ≃ M.Λ) (C₀ : Matrix (Fin ℓ) (Fin ℓ) ℤ)
    (hC : ∀ i j, M.cartan (e i) (e j) = C₀ i j)
    (hunit : IsUnit (C₀.map (Int.castRingHom (ZMod 3))).det) :
    IsUnit (M.cartan.map (Int.castRingHom (ZMod 3))).det := by
  have hcart : M.cartan = Matrix.reindex e e C₀ := by
    ext i j
    have := hC (e.symm i) (e.symm j)
    simpa [Matrix.reindex, Matrix.submatrix_apply] using this
  have hdet_eq : (M.cartan.map (Int.castRingHom (ZMod 3))).det =
      (C₀.map (Int.castRingHom (ZMod 3))).det := by
    rw [hcart]
    rw [show (Matrix.reindex e e C₀).map (Int.castRingHom (ZMod 3)) =
        Matrix.reindex e e (C₀.map (Int.castRingHom (ZMod 3))) from rfl]
    change ((C₀.map (Int.castRingHom (ZMod 3))).submatrix e.symm e.symm).det =
      (C₀.map (Int.castRingHom (ZMod 3))).det
    rw [Matrix.det_submatrix_equiv_self e.symm (C₀.map (Int.castRingHom (ZMod 3)))]
  rwa [hdet_eq]

theorem ggQ2_fullCoords_A5 {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hx : M.xV ∉ M.coSpan) (e : Fin 4 ≃ M.Λ)
    (hC : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.A 4 i j) :
    ∃ κ : M.V ≃ₗ[ZMod 3] TestLin.Vn 5, κ M.xV = aFullX 5 ∧
      ∀ k v, κ (ggLin (p := 3) M.model (M.simple (e k)) (κ.symm v)) = aFullS 5 k v := by
  have hρ : Function.Surjective M.rootMap := by
    refine ggQ2LDatum_rootMap_surjective M
      (isUnit_cartan_det_of_reindex M e (CartanMatrix.A 4) hC ?_)
    rw [show (CartanMatrix.A 4).map (Int.castRingHom (ZMod 3)) =
        (Int.castRingHom (ZMod 3)).mapMatrix (CartanMatrix.A 4) from rfl]
    rw [← RingHom.map_det (Int.castRingHom (ZMod 3)) (CartanMatrix.A 4), CartanMatrix.A_det]
    exact isUnit_iff_ne_zero.mpr (by decide)
  have hQP : ∀ y : Option (Fin 4) → ZMod 3, aRootQ 5 (aRec 5 y) = y := by
    apply leftInverse_of_basis
    intro o
    cases o with
    | none => decide +kernel
    | some j => fin_cases j <;> decide +kernel
  have hPQ : ∀ v : TestLin.Vn 5, aRec 5 (aRootQ 5 v) = v := by
    apply rightInverse_of_basis
    intro a
    fin_cases a <;> decide +kernel
  have hQx : aRootQ 5 (aFullX 5) = Pi.single none 1 := by decide +kernel
  have hQS : ∀ k : Fin 4, (aRootQ 5).comp (aFullS 5 k).toLinearMap =
      (rootCoordReflLin (CartanMatrix.A 4) k).comp (aRootQ 5) := by
    intro k
    apply linearMap_eq_of_basis
    intro a
    fin_cases k <;> fin_cases a <;> decide +kernel
  obtain ⟨P, hPx, hPS⟩ := coordsData (aRootQ 5) (aRec 5) (aFullX 5) (aFullS 5)
    (CartanMatrix.A 4) hQP hPQ hQx hQS
  exact ggQ2LDatum_coords_of_root M hρ hx e (CartanMatrix.A 4) hC P (aFullX 5) (aFullS 5)
    hPx hPS

theorem ggQ2_fullCoords_A7 {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hx : M.xV ∉ M.coSpan) (e : Fin 6 ≃ M.Λ)
    (hC : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.A 6 i j) :
    ∃ κ : M.V ≃ₗ[ZMod 3] TestLin.Vn 7, κ M.xV = aFullX 7 ∧
      ∀ k v, κ (ggLin (p := 3) M.model (M.simple (e k)) (κ.symm v)) = aFullS 7 k v := by
  have hρ : Function.Surjective M.rootMap := by
    refine ggQ2LDatum_rootMap_surjective M
      (isUnit_cartan_det_of_reindex M e (CartanMatrix.A 6) hC ?_)
    rw [show (CartanMatrix.A 6).map (Int.castRingHom (ZMod 3)) =
        (Int.castRingHom (ZMod 3)).mapMatrix (CartanMatrix.A 6) from rfl]
    rw [← RingHom.map_det (Int.castRingHom (ZMod 3)) (CartanMatrix.A 6), CartanMatrix.A_det]
    exact isUnit_iff_ne_zero.mpr (by decide)
  have hQP : ∀ y : Option (Fin 6) → ZMod 3, aRootQ 7 (aRec 7 y) = y := by
    apply leftInverse_of_basis
    intro o
    cases o with
    | none => decide +kernel
    | some j => fin_cases j <;> decide +kernel
  have hPQ : ∀ v : TestLin.Vn 7, aRec 7 (aRootQ 7 v) = v := by
    apply rightInverse_of_basis
    intro a
    fin_cases a <;> decide +kernel
  have hQx : aRootQ 7 (aFullX 7) = Pi.single none 1 := by decide +kernel
  have hQS : ∀ k : Fin 6, (aRootQ 7).comp (aFullS 7 k).toLinearMap =
      (rootCoordReflLin (CartanMatrix.A 6) k).comp (aRootQ 7) := by
    intro k
    apply linearMap_eq_of_basis
    intro a
    fin_cases k <;> fin_cases a <;> decide +kernel
  obtain ⟨P, hPx, hPS⟩ := coordsData (aRootQ 7) (aRec 7) (aFullX 7) (aFullS 7)
    (CartanMatrix.A 6) hQP hPQ hQx hQS
  exact ggQ2LDatum_coords_of_root M hρ hx e (CartanMatrix.A 6) hC P (aFullX 7) (aFullS 7)
    hPx hPS

theorem ggQ2_fullCoords_A8 {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hx : M.xV ∉ M.coSpan) (e : Fin 7 ≃ M.Λ)
    (hC : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.A 7 i j) :
    ∃ κ : M.V ≃ₗ[ZMod 3] TestLin.Vn 8, κ M.xV = aFullX 8 ∧
      ∀ k v, κ (ggLin (p := 3) M.model (M.simple (e k)) (κ.symm v)) = aFullS 8 k v := by
  have hρ : Function.Surjective M.rootMap := by
    refine ggQ2LDatum_rootMap_surjective M
      (isUnit_cartan_det_of_reindex M e (CartanMatrix.A 7) hC ?_)
    rw [show (CartanMatrix.A 7).map (Int.castRingHom (ZMod 3)) =
        (Int.castRingHom (ZMod 3)).mapMatrix (CartanMatrix.A 7) from rfl]
    rw [← RingHom.map_det (Int.castRingHom (ZMod 3)) (CartanMatrix.A 7), CartanMatrix.A_det]
    exact isUnit_iff_ne_zero.mpr (by decide)
  have hQP : ∀ y : Option (Fin 7) → ZMod 3, aRootQ 8 (aRec 8 y) = y := by
    apply leftInverse_of_basis
    intro o
    cases o with
    | none => decide +kernel
    | some j => fin_cases j <;> decide +kernel
  have hPQ : ∀ v : TestLin.Vn 8, aRec 8 (aRootQ 8 v) = v := by
    apply rightInverse_of_basis
    intro a
    fin_cases a <;> decide +kernel
  have hQx : aRootQ 8 (aFullX 8) = Pi.single none 1 := by decide +kernel
  have hQS : ∀ k : Fin 7, (aRootQ 8).comp (aFullS 8 k).toLinearMap =
      (rootCoordReflLin (CartanMatrix.A 7) k).comp (aRootQ 8) := by
    intro k
    apply linearMap_eq_of_basis
    intro a
    fin_cases k <;> fin_cases a <;> decide +kernel
  obtain ⟨P, hPx, hPS⟩ := coordsData (aRootQ 8) (aRec 8) (aFullX 8) (aFullS 8)
    (CartanMatrix.A 7) hQP hPQ hQx hQS
  exact ggQ2LDatum_coords_of_root M hρ hx e (CartanMatrix.A 7) hC P (aFullX 8) (aFullS 8)
    hPx hPS

private lemma dDet_unit (r : ℕ) (hr4 : 4 ≤ r) (hr8 : r ≤ 8) :
    IsUnit ((CartanMatrix.D r).map (Int.castRingHom (ZMod 3))).det := by
  interval_cases r
  · exact Matrix.isUnit_det_of_right_inverse
      (A := (CartanMatrix.D 4).map (Int.castRingHom (ZMod 3)))
      (by decide +kernel :
        (CartanMatrix.D 4).map (Int.castRingHom (ZMod 3)) *
          !![1, 1, 2, 2;
             1, 2, 1, 1;
             2, 1, 1, 2;
             2, 1, 2, 1] = 1)
  · exact Matrix.isUnit_det_of_right_inverse
      (A := (CartanMatrix.D 5).map (Int.castRingHom (ZMod 3)))
      (by decide +kernel :
        (CartanMatrix.D 5).map (Int.castRingHom (ZMod 3)) *
          !![1, 1, 1, 2, 2;
             1, 2, 2, 1, 1;
             1, 2, 0, 0, 0;
             2, 1, 0, 2, 0;
             2, 1, 0, 0, 2] = 1)
  · exact Matrix.isUnit_det_of_right_inverse
      (A := (CartanMatrix.D 6).map (Int.castRingHom (ZMod 3)))
      (by decide +kernel :
        (CartanMatrix.D 6).map (Int.castRingHom (ZMod 3)) *
          !![1, 1, 1, 1, 2, 2;
             1, 2, 2, 2, 1, 1;
             1, 2, 0, 0, 0, 0;
             1, 2, 0, 1, 2, 2;
             2, 1, 0, 2, 0, 1;
             2, 1, 0, 2, 1, 0] = 1)
  · exact Matrix.isUnit_det_of_right_inverse
      (A := (CartanMatrix.D 7).map (Int.castRingHom (ZMod 3)))
      (by decide +kernel :
        (CartanMatrix.D 7).map (Int.castRingHom (ZMod 3)) *
          !![1, 1, 1, 1, 1, 2, 2;
             1, 2, 2, 2, 2, 1, 1;
             1, 2, 0, 0, 0, 0, 0;
             1, 2, 0, 1, 1, 2, 2;
             1, 2, 0, 1, 2, 1, 1;
             2, 1, 0, 2, 1, 1, 2;
             2, 1, 0, 2, 1, 2, 1] = 1)
  · exact Matrix.isUnit_det_of_right_inverse
      (A := (CartanMatrix.D 8).map (Int.castRingHom (ZMod 3)))
      (by decide +kernel :
        (CartanMatrix.D 8).map (Int.castRingHom (ZMod 3)) *
          !![1, 1, 1, 1, 1, 1, 2, 2;
             1, 2, 2, 2, 2, 2, 1, 1;
             1, 2, 0, 0, 0, 0, 0, 0;
             1, 2, 0, 1, 1, 1, 2, 2;
             1, 2, 0, 1, 2, 2, 1, 1;
             1, 2, 0, 1, 2, 0, 0, 0;
             2, 1, 0, 2, 1, 0, 2, 0;
             2, 1, 0, 2, 1, 0, 0, 2] = 1)

theorem ggQ2_fullCoords_B (r : ℕ) (hr4 : 4 ≤ r) (hr8 : r ≤ 8) {G : Type} [Group G]
    {Bs L : Subgroup G} {x : G} (M : GGQ2LDatum 3 Bs L x) (hx : M.xV ∉ M.coSpan)
    (e : Fin r ≃ M.Λ) (hC : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.B r i j) :
    ∃ κ : M.V ≃ₗ[ZMod 3] TestLin.Vn (r + 1), κ M.xV = frameFullX r ∧
      ∀ k v, κ (ggLin (p := 3) M.model (M.simple (e k)) (κ.symm v)) = bcFullS r k v := by
  have hρ : Function.Surjective M.rootMap := by
    refine ggQ2LDatum_rootMap_surjective M
      (isUnit_cartan_det_of_reindex M e (CartanMatrix.B r) hC ?_)
    rw [show (CartanMatrix.B r).map (Int.castRingHom (ZMod 3)) =
        (Int.castRingHom (ZMod 3)).mapMatrix (CartanMatrix.B r) from rfl]
    rw [← RingHom.map_det (Int.castRingHom (ZMod 3)) (CartanMatrix.B r),
      CartanMatrix.B_det (by omega)]
    exact isUnit_iff_ne_zero.mpr (by decide)
  interval_cases r
  ·
    have hQP : ∀ y : Option (Fin 4) → ZMod 3, bRootQ 4 (bRec 4 y) = y := by
      apply leftInverse_of_basis
      intro o
      cases o with
      | none => decide +kernel
      | some j => fin_cases j <;> decide +kernel
    have hPQ : ∀ v : TestLin.Vn 5, bRec 4 (bRootQ 4 v) = v := by
      apply rightInverse_of_basis
      intro a
      fin_cases a <;> decide +kernel
    have hQx : bRootQ 4 (frameFullX 4) = Pi.single none 1 := by decide +kernel
    have hQS : ∀ k : Fin 4, (bRootQ 4).comp (bcFullS 4 k).toLinearMap =
        (rootCoordReflLin (CartanMatrix.B 4) k).comp (bRootQ 4) := by
      intro k
      apply linearMap_eq_of_basis
      intro a
      fin_cases k <;> fin_cases a <;> decide +kernel
    obtain ⟨P, hPx, hPS⟩ := coordsData (bRootQ 4) (bRec 4) (frameFullX 4)
      (bcFullS 4) (CartanMatrix.B 4) hQP hPQ hQx hQS
    exact ggQ2LDatum_coords_of_root M hρ hx e (CartanMatrix.B 4) hC P (frameFullX 4)
      (bcFullS 4) hPx hPS
  ·
    have hQP : ∀ y : Option (Fin 5) → ZMod 3, bRootQ 5 (bRec 5 y) = y := by
      apply leftInverse_of_basis
      intro o
      cases o with
      | none => decide +kernel
      | some j => fin_cases j <;> decide +kernel
    have hPQ : ∀ v : TestLin.Vn 6, bRec 5 (bRootQ 5 v) = v := by
      apply rightInverse_of_basis
      intro a
      fin_cases a <;> decide +kernel
    have hQx : bRootQ 5 (frameFullX 5) = Pi.single none 1 := by decide +kernel
    have hQS : ∀ k : Fin 5, (bRootQ 5).comp (bcFullS 5 k).toLinearMap =
        (rootCoordReflLin (CartanMatrix.B 5) k).comp (bRootQ 5) := by
      intro k
      apply linearMap_eq_of_basis
      intro a
      fin_cases k <;> fin_cases a <;> decide +kernel
    obtain ⟨P, hPx, hPS⟩ := coordsData (bRootQ 5) (bRec 5) (frameFullX 5)
      (bcFullS 5) (CartanMatrix.B 5) hQP hPQ hQx hQS
    exact ggQ2LDatum_coords_of_root M hρ hx e (CartanMatrix.B 5) hC P (frameFullX 5)
      (bcFullS 5) hPx hPS
  ·
    have hQP : ∀ y : Option (Fin 6) → ZMod 3, bRootQ 6 (bRec 6 y) = y := by
      apply leftInverse_of_basis
      intro o
      cases o with
      | none => decide +kernel
      | some j => fin_cases j <;> decide +kernel
    have hPQ : ∀ v : TestLin.Vn 7, bRec 6 (bRootQ 6 v) = v := by
      apply rightInverse_of_basis
      intro a
      fin_cases a <;> decide +kernel
    have hQx : bRootQ 6 (frameFullX 6) = Pi.single none 1 := by decide +kernel
    have hQS : ∀ k : Fin 6, (bRootQ 6).comp (bcFullS 6 k).toLinearMap =
        (rootCoordReflLin (CartanMatrix.B 6) k).comp (bRootQ 6) := by
      intro k
      apply linearMap_eq_of_basis
      intro a
      fin_cases k <;> fin_cases a <;> decide +kernel
    obtain ⟨P, hPx, hPS⟩ := coordsData (bRootQ 6) (bRec 6) (frameFullX 6)
      (bcFullS 6) (CartanMatrix.B 6) hQP hPQ hQx hQS
    exact ggQ2LDatum_coords_of_root M hρ hx e (CartanMatrix.B 6) hC P (frameFullX 6)
      (bcFullS 6) hPx hPS
  ·
    have hQP : ∀ y : Option (Fin 7) → ZMod 3, bRootQ 7 (bRec 7 y) = y := by
      apply leftInverse_of_basis
      intro o
      cases o with
      | none => decide +kernel
      | some j => fin_cases j <;> decide +kernel
    have hPQ : ∀ v : TestLin.Vn 8, bRec 7 (bRootQ 7 v) = v := by
      apply rightInverse_of_basis
      intro a
      fin_cases a <;> decide +kernel
    have hQx : bRootQ 7 (frameFullX 7) = Pi.single none 1 := by decide +kernel
    have hQS : ∀ k : Fin 7, (bRootQ 7).comp (bcFullS 7 k).toLinearMap =
        (rootCoordReflLin (CartanMatrix.B 7) k).comp (bRootQ 7) := by
      intro k
      apply linearMap_eq_of_basis
      intro a
      fin_cases k <;> fin_cases a <;> decide +kernel
    obtain ⟨P, hPx, hPS⟩ := coordsData (bRootQ 7) (bRec 7) (frameFullX 7)
      (bcFullS 7) (CartanMatrix.B 7) hQP hPQ hQx hQS
    exact ggQ2LDatum_coords_of_root M hρ hx e (CartanMatrix.B 7) hC P (frameFullX 7)
      (bcFullS 7) hPx hPS
  ·
    have hQP : ∀ y : Option (Fin 8) → ZMod 3, bRootQ 8 (bRec 8 y) = y := by
      apply leftInverse_of_basis
      intro o
      cases o with
      | none => decide +kernel
      | some j => fin_cases j <;> decide +kernel
    have hPQ : ∀ v : TestLin.Vn 9, bRec 8 (bRootQ 8 v) = v := by
      apply rightInverse_of_basis
      intro a
      fin_cases a <;> decide +kernel
    have hQx : bRootQ 8 (frameFullX 8) = Pi.single none 1 := by decide +kernel
    have hQS : ∀ k : Fin 8, (bRootQ 8).comp (bcFullS 8 k).toLinearMap =
        (rootCoordReflLin (CartanMatrix.B 8) k).comp (bRootQ 8) := by
      intro k
      apply linearMap_eq_of_basis
      intro a
      fin_cases k <;> fin_cases a <;> decide +kernel
    obtain ⟨P, hPx, hPS⟩ := coordsData (bRootQ 8) (bRec 8) (frameFullX 8)
      (bcFullS 8) (CartanMatrix.B 8) hQP hPQ hQx hQS
    exact ggQ2LDatum_coords_of_root M hρ hx e (CartanMatrix.B 8) hC P (frameFullX 8)
      (bcFullS 8) hPx hPS

theorem ggQ2_fullCoords_C (r : ℕ) (hr4 : 4 ≤ r) (hr8 : r ≤ 8) {G : Type} [Group G]
    {Bs L : Subgroup G} {x : G} (M : GGQ2LDatum 3 Bs L x) (hx : M.xV ∉ M.coSpan)
    (e : Fin r ≃ M.Λ) (hC : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.C r i j) :
    ∃ κ : M.V ≃ₗ[ZMod 3] TestLin.Vn (r + 1), κ M.xV = frameFullX r ∧
      ∀ k v, κ (ggLin (p := 3) M.model (M.simple (e k)) (κ.symm v)) = bcFullS r k v := by
  have hρ : Function.Surjective M.rootMap := by
    refine ggQ2LDatum_rootMap_surjective M
      (isUnit_cartan_det_of_reindex M e (CartanMatrix.C r) hC ?_)
    rw [show (CartanMatrix.C r).map (Int.castRingHom (ZMod 3)) =
        (Int.castRingHom (ZMod 3)).mapMatrix (CartanMatrix.C r) from rfl]
    rw [← RingHom.map_det (Int.castRingHom (ZMod 3)) (CartanMatrix.C r),
      CartanMatrix.C_det (by omega)]
    exact isUnit_iff_ne_zero.mpr (by decide)
  interval_cases r
  ·
    have hQP : ∀ y : Option (Fin 4) → ZMod 3, cRootQ 4 (cRec 4 y) = y := by
      apply leftInverse_of_basis
      intro o
      cases o with
      | none => decide +kernel
      | some j => fin_cases j <;> decide +kernel
    have hPQ : ∀ v : TestLin.Vn 5, cRec 4 (cRootQ 4 v) = v := by
      apply rightInverse_of_basis
      intro a
      fin_cases a <;> decide +kernel
    have hQx : cRootQ 4 (frameFullX 4) = Pi.single none 1 := by decide +kernel
    have hQS : ∀ k : Fin 4, (cRootQ 4).comp (bcFullS 4 k).toLinearMap =
        (rootCoordReflLin (CartanMatrix.C 4) k).comp (cRootQ 4) := by
      intro k
      apply linearMap_eq_of_basis
      intro a
      fin_cases k <;> fin_cases a <;> decide +kernel
    obtain ⟨P, hPx, hPS⟩ := coordsData (cRootQ 4) (cRec 4) (frameFullX 4)
      (bcFullS 4) (CartanMatrix.C 4) hQP hPQ hQx hQS
    exact ggQ2LDatum_coords_of_root M hρ hx e (CartanMatrix.C 4) hC P (frameFullX 4)
      (bcFullS 4) hPx hPS
  ·
    have hQP : ∀ y : Option (Fin 5) → ZMod 3, cRootQ 5 (cRec 5 y) = y := by
      apply leftInverse_of_basis
      intro o
      cases o with
      | none => decide +kernel
      | some j => fin_cases j <;> decide +kernel
    have hPQ : ∀ v : TestLin.Vn 6, cRec 5 (cRootQ 5 v) = v := by
      apply rightInverse_of_basis
      intro a
      fin_cases a <;> decide +kernel
    have hQx : cRootQ 5 (frameFullX 5) = Pi.single none 1 := by decide +kernel
    have hQS : ∀ k : Fin 5, (cRootQ 5).comp (bcFullS 5 k).toLinearMap =
        (rootCoordReflLin (CartanMatrix.C 5) k).comp (cRootQ 5) := by
      intro k
      apply linearMap_eq_of_basis
      intro a
      fin_cases k <;> fin_cases a <;> decide +kernel
    obtain ⟨P, hPx, hPS⟩ := coordsData (cRootQ 5) (cRec 5) (frameFullX 5)
      (bcFullS 5) (CartanMatrix.C 5) hQP hPQ hQx hQS
    exact ggQ2LDatum_coords_of_root M hρ hx e (CartanMatrix.C 5) hC P (frameFullX 5)
      (bcFullS 5) hPx hPS
  ·
    have hQP : ∀ y : Option (Fin 6) → ZMod 3, cRootQ 6 (cRec 6 y) = y := by
      apply leftInverse_of_basis
      intro o
      cases o with
      | none => decide +kernel
      | some j => fin_cases j <;> decide +kernel
    have hPQ : ∀ v : TestLin.Vn 7, cRec 6 (cRootQ 6 v) = v := by
      apply rightInverse_of_basis
      intro a
      fin_cases a <;> decide +kernel
    have hQx : cRootQ 6 (frameFullX 6) = Pi.single none 1 := by decide +kernel
    have hQS : ∀ k : Fin 6, (cRootQ 6).comp (bcFullS 6 k).toLinearMap =
        (rootCoordReflLin (CartanMatrix.C 6) k).comp (cRootQ 6) := by
      intro k
      apply linearMap_eq_of_basis
      intro a
      fin_cases k <;> fin_cases a <;> decide +kernel
    obtain ⟨P, hPx, hPS⟩ := coordsData (cRootQ 6) (cRec 6) (frameFullX 6)
      (bcFullS 6) (CartanMatrix.C 6) hQP hPQ hQx hQS
    exact ggQ2LDatum_coords_of_root M hρ hx e (CartanMatrix.C 6) hC P (frameFullX 6)
      (bcFullS 6) hPx hPS
  ·
    have hQP : ∀ y : Option (Fin 7) → ZMod 3, cRootQ 7 (cRec 7 y) = y := by
      apply leftInverse_of_basis
      intro o
      cases o with
      | none => decide +kernel
      | some j => fin_cases j <;> decide +kernel
    have hPQ : ∀ v : TestLin.Vn 8, cRec 7 (cRootQ 7 v) = v := by
      apply rightInverse_of_basis
      intro a
      fin_cases a <;> decide +kernel
    have hQx : cRootQ 7 (frameFullX 7) = Pi.single none 1 := by decide +kernel
    have hQS : ∀ k : Fin 7, (cRootQ 7).comp (bcFullS 7 k).toLinearMap =
        (rootCoordReflLin (CartanMatrix.C 7) k).comp (cRootQ 7) := by
      intro k
      apply linearMap_eq_of_basis
      intro a
      fin_cases k <;> fin_cases a <;> decide +kernel
    obtain ⟨P, hPx, hPS⟩ := coordsData (cRootQ 7) (cRec 7) (frameFullX 7)
      (bcFullS 7) (CartanMatrix.C 7) hQP hPQ hQx hQS
    exact ggQ2LDatum_coords_of_root M hρ hx e (CartanMatrix.C 7) hC P (frameFullX 7)
      (bcFullS 7) hPx hPS
  ·
    have hQP : ∀ y : Option (Fin 8) → ZMod 3, cRootQ 8 (cRec 8 y) = y := by
      apply leftInverse_of_basis
      intro o
      cases o with
      | none => decide +kernel
      | some j => fin_cases j <;> decide +kernel
    have hPQ : ∀ v : TestLin.Vn 9, cRec 8 (cRootQ 8 v) = v := by
      apply rightInverse_of_basis
      intro a
      fin_cases a <;> decide +kernel
    have hQx : cRootQ 8 (frameFullX 8) = Pi.single none 1 := by decide +kernel
    have hQS : ∀ k : Fin 8, (cRootQ 8).comp (bcFullS 8 k).toLinearMap =
        (rootCoordReflLin (CartanMatrix.C 8) k).comp (cRootQ 8) := by
      intro k
      apply linearMap_eq_of_basis
      intro a
      fin_cases k <;> fin_cases a <;> decide +kernel
    obtain ⟨P, hPx, hPS⟩ := coordsData (cRootQ 8) (cRec 8) (frameFullX 8)
      (bcFullS 8) (CartanMatrix.C 8) hQP hPQ hQx hQS
    exact ggQ2LDatum_coords_of_root M hρ hx e (CartanMatrix.C 8) hC P (frameFullX 8)
      (bcFullS 8) hPx hPS

theorem ggQ2_fullCoords_D (r : ℕ) (hr4 : 4 ≤ r) (hr8 : r ≤ 8) {G : Type} [Group G]
    {Bs L : Subgroup G} {x : G} (M : GGQ2LDatum 3 Bs L x) (hx : M.xV ∉ M.coSpan)
    (e : Fin r ≃ M.Λ) (hC : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.D r i j) :
    ∃ κ : M.V ≃ₗ[ZMod 3] TestLin.Vn (r + 1), κ M.xV = frameFullX r ∧
      ∀ k v, κ (ggLin (p := 3) M.model (M.simple (e k)) (κ.symm v)) = dFullS r k v := by
  have hρ : Function.Surjective M.rootMap :=
    ggQ2LDatum_rootMap_surjective M
      (isUnit_cartan_det_of_reindex M e (CartanMatrix.D r) hC (dDet_unit r hr4 hr8))
  interval_cases r
  ·
    have hQP : ∀ y : Option (Fin 4) → ZMod 3, dRootQ 4 (dRec 4 (by omega) y) = y := by
      apply leftInverse_of_basis
      intro o
      cases o with
      | none => decide +kernel
      | some j => fin_cases j <;> decide +kernel
    have hPQ : ∀ v : TestLin.Vn 5, dRec 4 (by omega) (dRootQ 4 v) = v := by
      apply rightInverse_of_basis
      intro a
      fin_cases a <;> decide +kernel
    have hQx : dRootQ 4 (frameFullX 4) = Pi.single none 1 := by decide +kernel
    have hQS : ∀ k : Fin 4, (dRootQ 4).comp (dFullS 4 k).toLinearMap =
        (rootCoordReflLin (CartanMatrix.D 4) k).comp (dRootQ 4) := by
      intro k
      apply linearMap_eq_of_basis
      intro a
      fin_cases k <;> fin_cases a <;> decide +kernel
    obtain ⟨P, hPx, hPS⟩ := coordsData (dRootQ 4) (dRec 4 (by omega)) (frameFullX 4)
      (dFullS 4) (CartanMatrix.D 4) hQP hPQ hQx hQS
    exact ggQ2LDatum_coords_of_root M hρ hx e (CartanMatrix.D 4) hC P (frameFullX 4)
      (dFullS 4) hPx hPS
  ·
    have hQP : ∀ y : Option (Fin 5) → ZMod 3, dRootQ 5 (dRec 5 (by omega) y) = y := by
      apply leftInverse_of_basis
      intro o
      cases o with
      | none => decide +kernel
      | some j => fin_cases j <;> decide +kernel
    have hPQ : ∀ v : TestLin.Vn 6, dRec 5 (by omega) (dRootQ 5 v) = v := by
      apply rightInverse_of_basis
      intro a
      fin_cases a <;> decide +kernel
    have hQx : dRootQ 5 (frameFullX 5) = Pi.single none 1 := by decide +kernel
    have hQS : ∀ k : Fin 5, (dRootQ 5).comp (dFullS 5 k).toLinearMap =
        (rootCoordReflLin (CartanMatrix.D 5) k).comp (dRootQ 5) := by
      intro k
      apply linearMap_eq_of_basis
      intro a
      fin_cases k <;> fin_cases a <;> decide +kernel
    obtain ⟨P, hPx, hPS⟩ := coordsData (dRootQ 5) (dRec 5 (by omega)) (frameFullX 5)
      (dFullS 5) (CartanMatrix.D 5) hQP hPQ hQx hQS
    exact ggQ2LDatum_coords_of_root M hρ hx e (CartanMatrix.D 5) hC P (frameFullX 5)
      (dFullS 5) hPx hPS
  ·
    have hQP : ∀ y : Option (Fin 6) → ZMod 3, dRootQ 6 (dRec 6 (by omega) y) = y := by
      apply leftInverse_of_basis
      intro o
      cases o with
      | none => decide +kernel
      | some j => fin_cases j <;> decide +kernel
    have hPQ : ∀ v : TestLin.Vn 7, dRec 6 (by omega) (dRootQ 6 v) = v := by
      apply rightInverse_of_basis
      intro a
      fin_cases a <;> decide +kernel
    have hQx : dRootQ 6 (frameFullX 6) = Pi.single none 1 := by decide +kernel
    have hQS : ∀ k : Fin 6, (dRootQ 6).comp (dFullS 6 k).toLinearMap =
        (rootCoordReflLin (CartanMatrix.D 6) k).comp (dRootQ 6) := by
      intro k
      apply linearMap_eq_of_basis
      intro a
      fin_cases k <;> fin_cases a <;> decide +kernel
    obtain ⟨P, hPx, hPS⟩ := coordsData (dRootQ 6) (dRec 6 (by omega)) (frameFullX 6)
      (dFullS 6) (CartanMatrix.D 6) hQP hPQ hQx hQS
    exact ggQ2LDatum_coords_of_root M hρ hx e (CartanMatrix.D 6) hC P (frameFullX 6)
      (dFullS 6) hPx hPS
  ·
    have hQP : ∀ y : Option (Fin 7) → ZMod 3, dRootQ 7 (dRec 7 (by omega) y) = y := by
      apply leftInverse_of_basis
      intro o
      cases o with
      | none => decide +kernel
      | some j => fin_cases j <;> decide +kernel
    have hPQ : ∀ v : TestLin.Vn 8, dRec 7 (by omega) (dRootQ 7 v) = v := by
      apply rightInverse_of_basis
      intro a
      fin_cases a <;> decide +kernel
    have hQx : dRootQ 7 (frameFullX 7) = Pi.single none 1 := by decide +kernel
    have hQS : ∀ k : Fin 7, (dRootQ 7).comp (dFullS 7 k).toLinearMap =
        (rootCoordReflLin (CartanMatrix.D 7) k).comp (dRootQ 7) := by
      intro k
      apply linearMap_eq_of_basis
      intro a
      fin_cases k <;> fin_cases a <;> decide +kernel
    obtain ⟨P, hPx, hPS⟩ := coordsData (dRootQ 7) (dRec 7 (by omega)) (frameFullX 7)
      (dFullS 7) (CartanMatrix.D 7) hQP hPQ hQx hQS
    exact ggQ2LDatum_coords_of_root M hρ hx e (CartanMatrix.D 7) hC P (frameFullX 7)
      (dFullS 7) hPx hPS
  ·
    have hQP : ∀ y : Option (Fin 8) → ZMod 3, dRootQ 8 (dRec 8 (by omega) y) = y := by
      apply leftInverse_of_basis
      intro o
      cases o with
      | none => decide +kernel
      | some j => fin_cases j <;> decide +kernel
    have hPQ : ∀ v : TestLin.Vn 9, dRec 8 (by omega) (dRootQ 8 v) = v := by
      apply rightInverse_of_basis
      intro a
      fin_cases a <;> decide +kernel
    have hQx : dRootQ 8 (frameFullX 8) = Pi.single none 1 := by decide +kernel
    have hQS : ∀ k : Fin 8, (dRootQ 8).comp (dFullS 8 k).toLinearMap =
        (rootCoordReflLin (CartanMatrix.D 8) k).comp (dRootQ 8) := by
      intro k
      apply linearMap_eq_of_basis
      intro a
      fin_cases k <;> fin_cases a <;> decide +kernel
    obtain ⟨P, hPx, hPS⟩ := coordsData (dRootQ 8) (dRec 8 (by omega)) (frameFullX 8)
      (dFullS 8) (CartanMatrix.D 8) hQP hPQ hQx hQS
    exact ggQ2LDatum_coords_of_root M hρ hx e (CartanMatrix.D 8) hC P (frameFullX 8)
      (dFullS 8) hPx hPS

end CFSG.StandardType

end
