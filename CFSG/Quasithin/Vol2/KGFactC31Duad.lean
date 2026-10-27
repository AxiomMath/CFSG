module

public import CFSG.Quasithin.Vol2.KGFactC31EBasis
public import CFSG.GH74.KGroups.FieldGF
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.KGC31.Duad

open Matrix CFSG.Assembly.LowTwoRank

abbrev F4 : Type := CFSG.GH74.KGroups.GF4

@[expose] def om : F4 := ⟨2⟩

@[expose] def emb (a : ZMod 2) : F4 := if a = 0 then 0 else 1

@[expose] def toF4 (c : Fin 4 → ZMod 2) : Fin 2 → F4 :=
  ![emb (c 0) + emb (c 1) * om, emb (c 2) + emb (c 3) * om]

@[expose] def Om : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1]

theorem toF4_add : ∀ c d : Fin 4 → ZMod 2, toF4 (c + d) = toF4 c + toF4 d := by decide

theorem toF4_zero : toF4 0 = 0 := by decide

theorem toF4_Om : ∀ c : Fin 4 → ZMod 2, toF4 (Om *ᵥ c) = om • toF4 c := by decide

theorem toF4_smul : ∀ (a : ZMod 2) (c : Fin 4 → ZMod 2), toF4 (a • c) = emb a • toF4 c := by
  decide

theorem toF4_injective : Function.Injective toF4 := by
  intro c d h
  revert c d
  decide

theorem toF4_surjective : Function.Surjective toF4 := by
  intro y
  revert y
  decide

theorem toF4_bijective : Function.Bijective toF4 := ⟨toF4_injective, toF4_surjective⟩

@[expose] def toF4Hom : (Fin 4 → ZMod 2) →+ (Fin 2 → F4) where
  toFun := toF4
  map_zero' := toF4_zero
  map_add' := toF4_add

@[expose] def bvec (j : Fin 2) : Fin 4 → ZMod 2 := if j = 0 then Pi.single 0 1 else Pi.single 2 1

theorem decomp : ∀ c : Fin 4 → ZMod 2,
    c = c 0 • bvec 0 + c 1 • (Om *ᵥ bvec 0) + c 2 • bvec 1 + c 3 • (Om *ᵥ bvec 1) := by decide

@[expose] def f4Mat (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Matrix (Fin 2) (Fin 2) F4 :=
  Matrix.of fun r j => toF4 (A *ᵥ bvec j) r

theorem toF4_mulVec {A : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hA : A * Om = Om * A)
    (c : Fin 4 → ZMod 2) : toF4 (A *ᵥ c) = f4Mat A *ᵥ toF4 c := by
  have hAc : A *ᵥ c = c 0 • (A *ᵥ bvec 0) + c 1 • (Om *ᵥ (A *ᵥ bvec 0)) +
      c 2 • (A *ᵥ bvec 1) + c 3 • (Om *ᵥ (A *ᵥ bvec 1)) := by
    conv_lhs => rw [decomp c]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hA]
  rw [hAc]
  simp only [toF4_add, toF4_smul, toF4_Om]
  funext r
  have h0 : toF4 c 0 = emb (c 0) + emb (c 1) * om := rfl
  have h1 : toF4 c 1 = emb (c 2) + emb (c 3) * om := rfl
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, f4Mat, Matrix.of_apply, h0, h1,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem matrix_ext_mulVec₂ {M N : Matrix (Fin 2) (Fin 2) F4} (hMN : ∀ y, M *ᵥ y = N *ᵥ y) :
    M = N :=
  Matrix.toLin'.injective (LinearMap.ext fun c => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hMN])

theorem f4Mat_mul {A B : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hA : A * Om = Om * A)
    (hB : B * Om = Om * B) : f4Mat (A * B) = f4Mat A * f4Mat B := by
  have hAB : A * B * Om = Om * (A * B) := by
    rw [mul_assoc, hB, ← mul_assoc, hA, mul_assoc]
  apply matrix_ext_mulVec₂
  intro y
  obtain ⟨c, rfl⟩ := toF4_surjective y
  rw [← toF4_mulVec hAB, ← Matrix.mulVec_mulVec, toF4_mulVec hA, toF4_mulVec hB,
    Matrix.mulVec_mulVec]

theorem f4Mat_one : f4Mat 1 = 1 := by decide

theorem eq_one_of_f4Mat {A : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hA : A * Om = Om * A)
    (h : f4Mat A = 1) : A = 1 :=
  matrix_ext_mulVec fun c => by
    rw [Matrix.one_mulVec]
    apply toF4_injective
    rw [toF4_mulVec hA, h, Matrix.one_mulVec]

theorem eq_one_of_sq : ∀ r : F4, r ^ 2 = 1 → r = 1 := by decide

theorem center_sl2 : Subgroup.center (SpecialLinearGroup (Fin 2) F4) = ⊥ := by
  refine eq_bot_iff.mpr fun A hA => ?_
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  rw [eq_one_of_sq r hr] at hrA
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA]
  simp

@[expose] noncomputable def slEquivPSL :
    SpecialLinearGroup (Fin 2) F4 ≃* ProjectiveSpecialLinearGroup (Fin 2) F4 :=
  ((QuotientGroup.quotientMulEquivOfEq center_sl2).trans QuotientGroup.quotientBot).symm

theorem isSimpleGroup_statedSL : IsSimpleGroup ↥(StatedSL 2 F4) := by
  obtain ⟨-, hs, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := F4) (n := 2) le_rfl
    (Or.inr ⟨Finset.univ, by decide⟩)
  have := hs
  exact ((specialLinearGroupEquivStatedSL 2 F4).symm.trans slEquivPSL).isSimpleGroup

theorem card_statedSL : Nat.card ↥(StatedSL 2 F4) = 60 := by
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 2 F4).toEquiv, Matrix.card_SL_field]
  decide

@[expose] noncomputable def statedSLEquivProj : ↥(StatedSL 2 F4) ≃* StatedProj (StatedSL 2 F4) :=
  ((specialLinearGroupEquivStatedSL 2 F4).symm.trans slEquivPSL).trans
    (projectiveSpecialLinearGroupEquivStatedProj 2 F4)

theorem isPSL_of_equiv {X : Type} [Group X] (e : X ≃* ↥(StatedSL 2 F4)) :
    CFSG.Quasithin.IsPSL 2 2 2 X :=
  ⟨⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩, F4, inferInstance, inferInstance,
    by rw [Nat.card_eq_fintype_card]; rfl, ⟨e.trans statedSLEquivProj⟩⟩

variable {Γ : Type*} [Group Γ] {v : Fin 4 → Γ} (hv : EBasis v)

theorem comm_inv {g : ↥(eNorm hv)} (h : eMat hv g * Om = Om * eMat hv g) :
    eMat hv g⁻¹ * Om = Om * eMat hv g⁻¹ := by
  have h1 : eMat hv g⁻¹ * eMat hv g = 1 := by rw [← eMat_mul, inv_mul_cancel, eMat_one]
  have h2 : eMat hv g * eMat hv g⁻¹ = 1 := by rw [← eMat_mul, mul_inv_cancel, eMat_one]
  calc eMat hv g⁻¹ * Om = eMat hv g⁻¹ * Om * (eMat hv g * eMat hv g⁻¹) := by rw [h2, mul_one]
    _ = eMat hv g⁻¹ * (Om * eMat hv g) * eMat hv g⁻¹ := by simp only [mul_assoc]
    _ = eMat hv g⁻¹ * (eMat hv g * Om) * eMat hv g⁻¹ := by rw [h]
    _ = Om * eMat hv g⁻¹ := by rw [← mul_assoc, h1, one_mul]

@[expose] def f4Stab : Subgroup Γ where
  carrier := {g | ∃ hg : g ∈ eNorm hv, eMat hv ⟨g, hg⟩ * Om = Om * eMat hv ⟨g, hg⟩}
  mul_mem' := by
    rintro a b ⟨ha, hA⟩ ⟨hb, hB⟩
    refine ⟨(eNorm hv).mul_mem ha hb, ?_⟩
    have : (⟨a * b, (eNorm hv).mul_mem ha hb⟩ : ↥(eNorm hv)) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [this, eMat_mul, mul_assoc, hB, ← mul_assoc, hA, mul_assoc]
  one_mem' := ⟨(eNorm hv).one_mem, by
    have : (⟨1, (eNorm hv).one_mem⟩ : ↥(eNorm hv)) = 1 := rfl
    rw [this, eMat_one, one_mul, mul_one]⟩
  inv_mem' := by
    rintro a ⟨ha, hA⟩
    exact ⟨(eNorm hv).inv_mem ha, comm_inv hv (g := ⟨a, ha⟩) hA⟩

@[expose] noncomputable def f4M (g : ↥(f4Stab hv)) : Matrix (Fin 2) (Fin 2) F4 :=
  f4Mat (eMat hv ⟨g, g.2.1⟩)

theorem f4M_mul (g k : ↥(f4Stab hv)) : f4M hv (g * k) = f4M hv g * f4M hv k := by
  unfold f4M
  have : (⟨((g * k : ↥(f4Stab hv)) : Γ), (g * k).2.1⟩ : ↥(eNorm hv)) =
      ⟨g, g.2.1⟩ * ⟨k, k.2.1⟩ := rfl
  rw [this, eMat_mul, f4Mat_mul g.2.2 k.2.2]

theorem f4M_one : f4M hv 1 = 1 := by
  unfold f4M
  have : (⟨((1 : ↥(f4Stab hv)) : Γ), (1 : ↥(f4Stab hv)).2.1⟩ : ↥(eNorm hv)) = 1 := rfl
  rw [this, eMat_one, f4Mat_one]

@[expose] noncomputable def f4Rep : ↥(f4Stab hv) →* GL (Fin 2) F4 where
  toFun g := ⟨f4M hv g, f4M hv g⁻¹, by rw [← f4M_mul, mul_inv_cancel, f4M_one],
    by rw [← f4M_mul, inv_mul_cancel, f4M_one]⟩
  map_one' := Units.ext (f4M_one hv)
  map_mul' g k := Units.ext (f4M_mul hv g k)

theorem f4Rep_coe (g : ↥(f4Stab hv)) :
    ((f4Rep hv g : GL (Fin 2) F4) : Matrix (Fin 2) (Fin 2) F4) = f4Mat (eMat hv ⟨g, g.2.1⟩) :=
  rfl

theorem f4Rep_eq_one_iff (g : ↥(f4Stab hv)) :
    f4Rep hv g = 1 ↔ (g : Γ) ∈ Subgroup.centralizer (eSub hv : Set Γ) := by
  rw [← eMat_eq_one_iff hv ⟨g, g.2.1⟩]
  constructor
  · intro h
    have h1 := congrArg (fun x : GL (Fin 2) F4 => (x : Matrix (Fin 2) (Fin 2) F4)) h
    simp only [f4Rep_coe, Units.val_one] at h1
    exact eq_one_of_f4Mat g.2.2 h1
  · intro h
    apply Units.ext
    rw [f4Rep_coe, h, f4Mat_one, Units.val_one]

theorem toF4_conj (g : ↥(f4Stab hv)) (c : Fin 4 → ZMod 2) :
    toF4 (eMat hv ⟨g, g.2.1⟩ *ᵥ c) =
      ((f4Rep hv g : GL (Fin 2) F4) : Matrix (Fin 2) (Fin 2) F4) *ᵥ toF4 c := by
  rw [f4Rep_coe]
  exact toF4_mulVec g.2.2 c

@[expose] noncomputable def f4Hom {X : Subgroup Γ} (hX : X ≤ f4Stab hv)
    (hdet : ∀ x : ↥X, (f4Mat (eMat hv ⟨x, (hX x.2).1⟩)).det = 1) : ↥X →* ↥(StatedSL 2 F4) :=
  ((f4Rep hv).comp (Subgroup.inclusion hX)).codRestrict _ fun x =>
    Subgroup.subset_closure (hdet x)

theorem f4Hom_coe {X : Subgroup Γ} (hX : X ≤ f4Stab hv)
    (hdet : ∀ x : ↥X, (f4Mat (eMat hv ⟨x, (hX x.2).1⟩)).det = 1) (x : ↥X) :
    (((f4Hom hv hX hdet x : ↥(StatedSL 2 F4)) : GL (Fin 2) F4) : Matrix (Fin 2) (Fin 2) F4) =
      f4Mat (eMat hv ⟨x, (hX x.2).1⟩) := rfl

end CFSG.Quasithin.KGC31.Duad

end
