module

public import CFSG.RankThree.PartOne.CTP.SeitzDiag
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Diagonal.Diagonalization
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix TauCeti TauCeti.GLSymplecticFin

section PiGL

variable {m : ℕ} {F : Type*} [Field F] {ι : Type*}

@[expose] noncomputable def piGL (g : ι → GL (Fin (m + m)) F) : GL (Fin (m + m)) (ι → F) where
  val := Matrix.of fun a b i =>
    ((g i : GL (Fin (m + m)) F) : Matrix (Fin (m + m)) (Fin (m + m)) F) a b
  inv := Matrix.of fun a b i =>
    (((g i)⁻¹ : GL (Fin (m + m)) F) : Matrix (Fin (m + m)) (Fin (m + m)) F) a b
  val_inv := by
    ext a b i
    have h := congrArg (fun M : Matrix (Fin (m + m)) (Fin (m + m)) F => M a b)
      (Units.mul_inv (g i))
    simp only [Matrix.mul_apply, Matrix.one_apply] at h
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply,
      Matrix.one_apply]
    split_ifs at h ⊢ <;> simpa using h
  inv_val := by
    ext a b i
    have h := congrArg (fun M : Matrix (Fin (m + m)) (Fin (m + m)) F => M a b)
      (Units.inv_mul (g i))
    simp only [Matrix.mul_apply, Matrix.one_apply] at h
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply,
      Matrix.one_apply]
    split_ifs at h ⊢ <;> simpa using h

theorem piGL_apply (g : ι → GL (Fin (m + m)) F) (a b : Fin (m + m)) (i : ι) :
    ((piGL g : GL (Fin (m + m)) (ι → F)) : Matrix (Fin (m + m)) (Fin (m + m)) (ι → F)) a b i =
      ((g i : GL (Fin (m + m)) F) : Matrix (Fin (m + m)) (Fin (m + m)) F) a b := rfl

theorem map_eval_piGL (g : ι → GL (Fin (m + m)) F) (i : ι) :
    Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : ι => F) i) (piGL g) = g i := by
  apply Matrix.GeneralLinearGroup.ext
  intro a b
  rfl

theorem piGL_mem {g : ι → GL (Fin (m + m)) F} (hg : ∀ i, g i ∈ GLSymplecticFin m F) :
    piGL g ∈ GLSymplecticFin m (ι → F) := by
  rw [GLSymplecticFin.mem_iff']
  ext a b i
  have h := GLSymplecticFin.mem_iff'.1 (hg i)
  have h1 := congrArg (fun M : Matrix (Fin (m + m)) (Fin (m + m)) F => M a b) h
  have hmap : ((piGL g : GL (Fin (m + m)) (ι → F)) :
      Matrix (Fin (m + m)) (Fin (m + m)) (ι → F)).map (Pi.evalRingHom (fun _ : ι => F) i) =
      ((g i : GL (Fin (m + m)) F) : Matrix (Fin (m + m)) (Fin (m + m)) F) := by
    ext x y
    rfl
  have hJ := JFin_map (m := m) (Pi.evalRingHom (fun _ : ι => F) i)
  have hJ' : JFin m (ι → F) a b i = JFin m F a b := by
    simpa using congrArg (fun M : Matrix (Fin (m + m)) (Fin (m + m)) F => M a b) hJ
  have h2 : ((((piGL g : GL (Fin (m + m)) (ι → F)) :
      Matrix (Fin (m + m)) (Fin (m + m)) (ι → F))ᵀ * JFin m (ι → F) *
      ((piGL g : GL (Fin (m + m)) (ι → F)) : Matrix (Fin (m + m)) (Fin (m + m)) (ι → F))).map
      (Pi.evalRingHom (fun _ : ι => F) i)) a b = (JFin m F) a b := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hmap, hJ]
    exact h1
  exact h2.trans hJ'.symm

end PiGL

section Diagonalize

variable {m : ℕ} {F : Type*} [Field F] {ι : Type*}

@[expose] noncomputable def piSp (x : ι → GLSymplecticFin m F) : GLSymplecticFin m (ι → F) :=
  ⟨piGL (fun i => ((x i : GLSymplecticFin m F) : GL (Fin (m + m)) F)), piGL_mem (fun i => (x i).2)⟩

theorem map_eval_piSp (x : ι → GLSymplecticFin m F) (i : ι) :
    GLSymplecticFin.map m (ι → F) (Pi.evalRingHom (fun _ : ι => F) i) (piSp x) = x i := by
  apply Subtype.ext
  rw [GLSymplecticFin.coe_map]
  exact map_eval_piGL (fun i => ((x i : GLSymplecticFin m F) : GL (Fin (m + m)) F)) i

theorem map_eval_map_const (P : GLSymplecticFin m F) (i : ι) :
    GLSymplecticFin.map m (ι → F) (Pi.evalRingHom (fun _ : ι => F) i)
      (GLSymplecticFin.map m F (algebraMap F (ι → F)) P) = P := by
  apply Subtype.ext
  rw [GLSymplecticFin.coe_map, GLSymplecticFin.coe_map]
  apply Matrix.GeneralLinearGroup.ext
  intro a b
  rfl

theorem piGL_intertwine [Finite ι] (g : GL (Fin (m + m)) F) (x : ι → GL (Fin (m + m)) F)
    (T : ι → Fin (m + m) → Fˣ) (hrel : ∀ i, x i * g = g * diagGL (T i)) :
    piGL x * Matrix.GeneralLinearGroup.map (algebraMap F (ι → F)) g =
      Matrix.GeneralLinearGroup.map (algebraMap F (ι → F)) g *
        diagGL (fun j => MulEquiv.piUnits.symm (fun i => T i j)) := by
  classical
  apply Units.ext
  ext a b y
  have hy := congrArg (fun A : GL (Fin (m + m)) F => (A : Matrix (Fin (m + m)) (Fin (m + m)) F) a b)
    (hrel y)
  simp only [Units.val_mul, Matrix.mul_apply, diagGL_apply] at hy ⊢
  simp only [Finset.sum_apply, Pi.mul_apply, apply_ite (fun f : ι → F => f y)]
  simpa [piGL_apply, Matrix.GeneralLinearGroup.map_apply] using hy

theorem exists_symplectic_conj_diagonal [Finite F] {p : ℕ} [Fact p.Prime]
    (hζ : ∃ ζ : F, IsPrimitiveRoot ζ p) (E : Subgroup (GLSymplecticFin m F))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1) :
    ∃ P : GLSymplecticFin m F, ∀ x ∈ E, ∃ u : Fin m → Fˣ, x * P = P * diagonal u := by
  classical
  have : Finite (GL (Fin (m + m)) F) := inferInstance
  let Eg : Subgroup (GL (Fin (m + m)) F) := E.map (GLSymplecticFin m F).subtype
  have hEgcomm : ∀ x ∈ Eg, ∀ y ∈ Eg, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hcomm a ha b hb)
  have hEgexp : ∀ x ∈ Eg, x ^ p = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    exact congrArg Subtype.val (hexp a ha)
  obtain ⟨g, hg⟩ := exists_conj_diagonal_of_exponent_prime hζ Eg hEgcomm hEgexp
  have hdiag : ∀ x : E, ∃ t : Fin (m + m) → Fˣ,
      ((x : GLSymplecticFin m F) : GL (Fin (m + m)) F) * g⁻¹ = g⁻¹ * diagGL t := by
    intro x
    have hd : ((g * ((x : GLSymplecticFin m F) : GL (Fin (m + m)) F) * g⁻¹ :
        GL (Fin (m + m)) F) : Matrix (Fin (m + m)) (Fin (m + m)) F).IsDiag := fun i j hij =>
      hg _ ⟨x.1, x.2, rfl⟩ i j hij
    obtain ⟨t, ht⟩ := TauCeti.mem_diagonalTorus_iff_exists_diagGL.mp
      (TauCeti.mem_diagonalTorus_iff.mpr hd)
    exact ⟨t, by rw [ht]; group⟩
  choose T hT using hdiag
  obtain ⟨P, u, hPu⟩ := GLSymplecticFin.exists_mul_map_eq_map_mul_diagonal
    (piSp (fun x : E => (x : GLSymplecticFin m F)))
    (piGL_intertwine g⁻¹ (fun x : E => ((x : GLSymplecticFin m F) : GL (Fin (m + m)) F)) T hT)
  refine ⟨P, fun x hx => ⟨fun i => Units.map (Pi.evalRingHom (fun _ : E => F) ⟨x, hx⟩ :
    (E → F) →* F) (u i), ?_⟩⟩
  have h2 := congrArg (GLSymplecticFin.map m (E → F)
    (Pi.evalRingHom (fun _ : E => F) ⟨x, hx⟩)) hPu
  rw [map_mul, map_mul, map_eval_piSp, map_eval_map_const, GLSymplecticFin.map_diagonal] at h2
  exact h2

end Diagonalize

end CFSG.RankThree.PartOne.CTP
