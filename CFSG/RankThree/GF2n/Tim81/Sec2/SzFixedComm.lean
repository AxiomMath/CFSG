module

public import CFSG.Quasithin.Background.SmithB42Sp4Desc
public import CFSG.Quasithin.Background.SmithB45SzRep

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open scoped Matrix

open CFSG.Blueprint CFSG.LieType.Ree CFSG.Quasithin CFSG.Quasithin.B45Sz
  CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.X7b

section Commutator

variable {k : Type} [Field k] {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module k V]

@[expose] def commSubK (ρ : Representation k G V) (A : Subgroup G) : Submodule k V :=
  ⨆ a ∈ A, LinearMap.range (ρ a - 1)

theorem range_le_commSubK {ρ : Representation k G V} {A : Subgroup G} {a : G} (ha : a ∈ A) :
    LinearMap.range (ρ a - 1) ≤ commSubK ρ A :=
  le_iSup₂ (f := fun a (_ : a ∈ A) => LinearMap.range (ρ a - 1)) a ha

end Commutator

section DotProduct

variable {k : Type} [Field k] {κ : Type} [Fintype κ] [DecidableEq κ]
variable {G : Type} [Group G]

@[expose] def dotBilin : LinearMap.BilinForm k (κ → k) := dotProductBilin k k

theorem dotBilin_apply (x y : κ → k) : dotBilin x y = x ⬝ᵥ y := rfl

theorem dotBilin_nondegenerate : dotBilin (k := k) (κ := κ).Nondegenerate := by
  have key : ∀ x : κ → k, (∀ y, x ⬝ᵥ y = 0) → x = 0 := by
    intro x hx
    funext i
    have h := hx (Pi.single i 1)
    simpa using h
  refine ⟨fun x hx => key x hx, fun y hy => key y fun x => ?_⟩
  rw [dotProduct_comm]
  exact hy x

theorem dotBilin_transpose (M : Matrix κ κ k) (y x : κ → k) :
    dotBilin (M.mulVec y) x = dotBilin y (M.transpose.mulVec x) := by
  calc dotBilin (M.mulVec y) x = (M.mulVec y) ⬝ᵥ x := dotBilin_apply _ _
    _ = x ⬝ᵥ (M.mulVec y) := dotProduct_comm _ _
    _ = y ⬝ᵥ (M.transpose.mulVec x) := (Matrix.dotProduct_transpose_mulVec M y x).symm
    _ = dotBilin y (M.transpose.mulVec x) := (dotBilin_apply _ _).symm

theorem matRep_sub_one_apply (R : G →* Matrix κ κ k) (a : G) (y : κ → k) :
    ((matRep R a : Module.End k (κ → k)) - 1) y = (R a - 1).mulVec y := by
  rw [LinearMap.sub_apply, Module.End.one_apply, matRep_apply, Matrix.sub_mulVec,
    Matrix.one_mulVec]

theorem dotBilin_sub_one (M : Matrix κ κ k) (y x : κ → k) :
    dotBilin ((M - 1).mulVec y) x = dotBilin y (M.transpose.mulVec x - x) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [show dotBilin (M.mulVec y - y) x = dotBilin (M.mulVec y) x - dotBilin y x by
      simp only [map_sub, LinearMap.sub_apply],
    show dotBilin y (M.transpose.mulVec x - x) = dotBilin y (M.transpose.mulVec x) - dotBilin y x by
      simp only [map_sub],
    dotBilin_transpose]

theorem dotBilin_orthogonal_commSubK (R : G →* Matrix κ κ k) (A : Subgroup G) :
    dotBilin.orthogonal (commSubK (matRep R) A) = fixedSub (matRep (dualMat R)) A := by
  classical
  ext x
  rw [LinearMap.BilinForm.mem_orthogonal_iff, mem_fixedSub]
  constructor
  · intro hx a ha
    have h1 : ∀ y, dotBilin y ((R a⁻¹).transpose.mulVec x - x) = 0 := by
      intro y
      have h2 := hx (((matRep R (a⁻¹) : Module.End k (κ → k)) - 1) y)
        (range_le_commSubK (A.inv_mem ha) ⟨y, rfl⟩)
      rwa [matRep_sub_one_apply, dotBilin_sub_one] at h2
    have h4 := dotBilin_nondegenerate.2 _ h1
    rw [matRep_apply, dualMat_apply]
    exact sub_eq_zero.mp h4
  · intro hx n hn
    have hle : commSubK (matRep R) A ≤ LinearMap.ker (dotBilin x) := by
      refine iSup₂_le fun a ha => ?_
      rintro _ ⟨y, rfl⟩
      rw [LinearMap.mem_ker]
      have hxa : ((R a).transpose).mulVec x = x := by
        have h := mem_fixedSub.mp hx a⁻¹ (A.inv_mem ha)
        rw [matRep_apply, dualMat_apply, inv_inv] at h
        exact h
      have hkey : x ⬝ᵥ ((R a).mulVec y) = y ⬝ᵥ x := by
        rw [← Matrix.dotProduct_transpose_mulVec (A := R a) (x := y) (y := x), hxa]
      rw [matRep_sub_one_apply, Matrix.sub_mulVec, Matrix.one_mulVec, map_sub, dotBilin_apply,
        dotBilin_apply, hkey, dotProduct_comm x y, sub_self]
    have h2 := LinearMap.mem_ker.mp (hle hn)
    rwa [dotBilin_apply, dotProduct_comm] at h2

theorem finrank_commSubK_add_finrank_fixedSub_dualMat (R : G →* Matrix κ κ k) (A : Subgroup G) :
    Module.finrank k (commSubK (matRep R) A) +
      Module.finrank k (fixedSub (matRep (dualMat R)) A) = Fintype.card κ := by
  rw [← dotBilin_orthogonal_commSubK R A]
  have h := LinearMap.BilinForm.finrank_orthogonal (B := dotBilin (k := k) (κ := κ))
    dotBilin_nondegenerate (commSubK (matRep R) A)
  have hle : Module.finrank k (commSubK (matRep R) A) ≤ Fintype.card κ := by
    rw [← Module.finrank_fintype_fun_eq_card k]
    exact Submodule.finrank_le (commSubK (matRep R) A)
  rw [Module.finrank_fintype_fun_eq_card k] at h
  omega

end DotProduct

section SelfDual

variable {k : Type} [Field k] {κ : Type} [Fintype κ] [DecidableEq κ]
variable {G : Type} [Group G]

theorem fixedSub_dualMat_eq_map (R : G →* Matrix κ κ k) (A : Subgroup G) (J : Matrix κ κ k)
    (hJ : J * J = 1) (hdual : ∀ g, (R g⁻¹)ᵀ = J * R g * J) :
    fixedSub (matRep (dualMat R)) A = (fixedSub (matRep R) A).map (Matrix.mulVecLin J) := by
  classical
  have hD : ∀ g, dualMat R g = J * R g * J := fun g => by rw [dualMat_apply, hdual g]
  have hR : ∀ g, R g = J * dualMat R g * J := by
    intro g
    have h1 : J * dualMat R g * J = R g := by
      rw [hD g]
      calc J * (J * R g * J) * J = (J * J) * R g * (J * J) := by noncomm_ring
        _ = R g := by rw [hJ, Matrix.one_mul, Matrix.mul_one]
    rw [h1]
  have hJJ : ∀ x : κ → k, J.mulVec (J.mulVec x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, hJ, Matrix.one_mulVec]
  ext x
  constructor
  · intro hx
    rw [Submodule.mem_map]
    refine ⟨J.mulVec x, ?_, hJJ x⟩
    rw [mem_fixedSub]
    intro a ha
    have hxa : (dualMat R a).mulVec x = x := mem_fixedSub.mp hx a ha
    calc (R a).mulVec (J.mulVec x)
        = (J * dualMat R a * J).mulVec (J.mulVec x) := by rw [hR a]
      _ = J.mulVec ((dualMat R a).mulVec (J.mulVec (J.mulVec x))) := by
            rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      _ = J.mulVec x := by rw [hJJ x, hxa]
  · rintro ⟨y, hy, rfl⟩
    rw [mem_fixedSub]
    intro a ha
    have hya : (R a).mulVec y = y := mem_fixedSub.mp hy a ha
    calc (dualMat R a).mulVec (J.mulVec y)
        = (J * R a * J).mulVec (J.mulVec y) := by rw [hD a]
      _ = J.mulVec ((R a).mulVec (J.mulVec (J.mulVec y))) := by
            rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      _ = J.mulVec y := by rw [hJJ y, hya]

private theorem finrank_map_eq_of_injective {M : Type*} [AddCommGroup M] [Module k M]
    (f : M →ₗ[k] M) (g : M →ₗ[k] M) (hgf : ∀ x, g (f x) = x) (p : Submodule k M) :
    Module.finrank k ↥(p.map f) = Module.finrank k ↥p := by
  have hinj : Function.Injective f := fun a b hab => by
    rw [← hgf a, ← hgf b, hab]
  exact (Submodule.equivMapOfInjective f hinj p).finrank_eq.symm

theorem finrank_fixedSub_dualMat_eq (R : G →* Matrix κ κ k) (A : Subgroup G) (J : Matrix κ κ k)
    (hJ : J * J = 1) (hdual : ∀ g, (R g⁻¹)ᵀ = J * R g * J) :
    Module.finrank k (fixedSub (matRep (dualMat R)) A) =
      Module.finrank k (fixedSub (matRep R) A) := by
  rw [fixedSub_dualMat_eq_map R A J hJ hdual]
  have hcomp : (Matrix.mulVecLin J) ∘ₗ (Matrix.mulVecLin J) = LinearMap.id := by
    rw [← Matrix.mulVecLin_mul, hJ, Matrix.mulVecLin_one]
  have hJJ : ∀ x : κ → k, (Matrix.mulVecLin J) ((Matrix.mulVecLin J) x) = x := by
    intro x
    rw [← LinearMap.comp_apply, hcomp]
    rfl
  exact finrank_map_eq_of_injective (Matrix.mulVecLin J) (Matrix.mulVecLin J) hJJ _

end SelfDual

end CFSG.RankThree.GF2n.Tim81.Sec2
