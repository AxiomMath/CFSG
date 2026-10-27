module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem12StD
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem12StB
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitL52Rep

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis
open scoped IsMulCommutative Matrix

namespace Lem12St

section Alt

@[expose] def altMat {R : Type*} [CommRing R] (w : Fin 10 → R) : Matrix (Fin 5) (Fin 5) R :=
  !![0, w 0, w 1, w 2, w 3;
    -w 0, 0, w 4, w 5, w 6;
    -w 1, -w 4, 0, w 7, w 8;
    -w 2, -w 5, -w 7, 0, w 9;
    -w 3, -w 6, -w 8, -w 9, 0]

theorem altMat_transpose {R : Type*} [CommRing R] (w : Fin 10 → R) :
    (altMat w)ᵀ = -altMat w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [altMat]

theorem altMat_pr5 {R : Type*} [CommRing R] (w : Fin 10 → R) (k : Fin 10) :
    altMat w (pr5 k).1 (pr5 k).2 = w k := by
  fin_cases k <;> simp [altMat, pr5]

theorem altMat_injective {R : Type*} [CommRing R] : Function.Injective (altMat (R := R)) := by
  intro w w' h
  funext k
  rw [← altMat_pr5 w k, ← altMat_pr5 w' k, h]

theorem det_altMat_X :
    (altMat (fun k => (MvPolynomial.X k : MvPolynomial (Fin 10) ℤ))).det = 0 := by
  set A := altMat (fun k => (MvPolynomial.X k : MvPolynomial (Fin 10) ℤ))
  have h : A.det = -A.det := by
    calc A.det = Aᵀ.det := (Matrix.det_transpose A).symm
      _ = (-A).det := by rw [altMat_transpose]
      _ = -A.det := by rw [Matrix.det_neg]; norm_num
  have h2 : (2 : MvPolynomial (Fin 10) ℤ) * A.det = 0 := by
    rw [two_mul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 two_ne_zero
  · exact h3

theorem altMat_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (w : Fin 10 → R) :
    (altMat w).map f = altMat (fun k => f (w k)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [altMat]

theorem det_altMat {R : Type*} [CommRing R] (w : Fin 10 → R) : (altMat w).det = 0 := by
  set φ : MvPolynomial (Fin 10) ℤ →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) w
  have h1 : altMat w =
      (altMat (fun k => (MvPolynomial.X k : MvPolynomial (Fin 10) ℤ))).map φ := by
    rw [altMat_map]
    congr 1
    funext k
    simp [φ]
  rw [h1, ← RingHom.mapMatrix_apply, ← RingHom.map_det, det_altMat_X, map_zero]

theorem altMat_wedgeMat_row0 {R : Type*} [Field R] (g : Matrix (Fin 5) (Fin 5) R)
    (w : Fin 10 → R) (j : Fin 5) :
    altMat (wedgeMat g *ᵥ w) 0 j = (g * altMat w * gᵀ) 0 j := by
  fin_cases j <;>
    simp [altMat, wedgeMat, pr5, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring

theorem altMat_wedgeMat_row1 {R : Type*} [Field R] (g : Matrix (Fin 5) (Fin 5) R)
    (w : Fin 10 → R) (j : Fin 5) :
    altMat (wedgeMat g *ᵥ w) 1 j = (g * altMat w * gᵀ) 1 j := by
  fin_cases j <;>
    simp [altMat, wedgeMat, pr5, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring

theorem altMat_wedgeMat_row2 {R : Type*} [Field R] (g : Matrix (Fin 5) (Fin 5) R)
    (w : Fin 10 → R) (j : Fin 5) :
    altMat (wedgeMat g *ᵥ w) 2 j = (g * altMat w * gᵀ) 2 j := by
  fin_cases j <;>
    simp [altMat, wedgeMat, pr5, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring

theorem altMat_wedgeMat_row3 {R : Type*} [Field R] (g : Matrix (Fin 5) (Fin 5) R)
    (w : Fin 10 → R) (j : Fin 5) :
    altMat (wedgeMat g *ᵥ w) 3 j = (g * altMat w * gᵀ) 3 j := by
  fin_cases j <;>
    simp [altMat, wedgeMat, pr5, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring

theorem altMat_wedgeMat_row4 {R : Type*} [Field R] (g : Matrix (Fin 5) (Fin 5) R)
    (w : Fin 10 → R) (j : Fin 5) :
    altMat (wedgeMat g *ᵥ w) 4 j = (g * altMat w * gᵀ) 4 j := by
  fin_cases j <;>
    simp [altMat, wedgeMat, pr5, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring

theorem altMat_wedgeMat {R : Type*} [Field R] (g : Matrix (Fin 5) (Fin 5) R)
    (w : Fin 10 → R) : altMat (wedgeMat g *ᵥ w) = g * altMat w * gᵀ := by
  ext i j
  fin_cases i
  · exact altMat_wedgeMat_row0 g w j
  · exact altMat_wedgeMat_row1 g w j
  · exact altMat_wedgeMat_row2 g w j
  · exact altMat_wedgeMat_row3 g w j
  · exact altMat_wedgeMat_row4 g w j

end Alt

section Wedge

@[expose] def suppW (w : Fin 10 → ZMod 2) : Submodule (ZMod 2) (Fin 5 → ZMod 2) :=
  LinearMap.range (altMat w).mulVecLin

variable {w : Fin 10 → ZMod 2}

theorem mulVec_mem_suppW (x : Fin 5 → ZMod 2) : altMat w *ᵥ x ∈ suppW w :=
  ⟨x, rfl⟩

theorem altMat_eq_of_fix {g : G5} (hg : wedgeRep g w = w) :
    (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) * altMat w * (g : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ =
      altMat w := by
  rw [← altMat_wedgeMat, ← wedgeRep_apply', hg]

theorem mem_suppW_of_fix {g : G5} (hg : wedgeRep g w = w) {u : Fin 5 → ZMod 2}
    (hu : u ∈ suppW w) : (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ u ∈ suppW w := by
  obtain ⟨x, rfl⟩ := hu
  have hA := altMat_eq_of_fix hg
  have h1 : altMat w * ((g⁻¹ : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ =
      (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) * altMat w := by
    conv_lhs => rw [← hA]
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one, Matrix.mul_one]
  refine ⟨((g⁻¹ : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ x, ?_⟩
  change altMat w *ᵥ (((g⁻¹ : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ x) =
    (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ (altMat w *ᵥ x)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1]

theorem wedgeRep_inv_of_fix {g : G5} (hg : wedgeRep g w = w) : wedgeRep g⁻¹ w = w := by
  conv_lhs => rw [← hg]
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem wedgeRep_eq_of_isRadU {g : G5}
    (hg : IsRadU (suppW w) (g : Matrix (Fin 5) (Fin 5) (ZMod 2))) : wedgeRep g w = w := by
  apply altMat_injective
  rw [wedgeRep_apply', altMat_wedgeMat]
  have h1 : (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) * altMat w = altMat w := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    rw [← Matrix.mulVec_mulVec]
    exact hg.2 _ (mulVec_mem_suppW _)
  have h2 : altMat w * (g : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ = altMat w := by
    have h3 := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, altMat_transpose, Matrix.neg_mul] at h3
    exact neg_inj.mp h3
  rw [h1, h2]

theorem exists_mem_suppW_ne_zero (hw : w ≠ 0) : ∃ u ∈ suppW w, u ≠ 0 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hw
  refine ⟨altMat w *ᵥ Pi.single (pr5 k).2 1, mulVec_mem_suppW _, fun h => hk ?_⟩
  have h1 := congrFun h (pr5 k).1
  rw [Matrix.mulVec_single_one, Matrix.col_apply, altMat_pr5] at h1
  exact h1

theorem exists_not_mem_suppW : ∃ y : Fin 5 → ZMod 2, y ∉ suppW w := by
  by_contra hcon
  push Not at hcon
  have hs : Function.Surjective (altMat w).mulVec := fun y => hcon y
  have h1 := (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_surjective_iff_isUnit.mp hs)
  rw [det_altMat] at h1
  exact not_isUnit_zero h1

end Wedge

section L52

variable {G : Type} [Group G] [Finite G] {L V : Subgroup G} [IsMulCommutative ↥V]

theorem false_of_wedge
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hV2 : ∀ x ∈ V, x ^ 2 = 1) (hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G))
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)))
    (hcard : Nat.card V = 2 ^ 10) (hirr : IsIrreducibleUnder L V) {v : G} (hv : v ∈ V)
    (hv1 : v ≠ 1)
    (hK2 : pCoreOf 2 (autOn (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))) V) = ⊥)
    (hVL : V = ⁅V, oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))⁆) : False := by
  classical
  have hsq : ∀ x : ↥V, x ^ 2 = 1 := fun x => Subtype.ext (by simpa using hV2 x x.2)
  have : IsSimpleGroup G5 := CFSG.Quasithin.Vol2.Ch11.SecA.isSimpleGroup_SL_zmod_two (by norm_num)
  obtain ⟨e5⟩ := he
  obtain ⟨ψ⟩ := nonempty_autOn_mulEquiv_of_simple hLV hO2 (not_le_centralizer hLV hv hv1 hVL) e5
  have hirr' : ∀ W : Subgroup ↥V, (∀ a ∈ autOn L V, ∀ x ∈ W, (a : MulAut ↥V) x ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
    intro W hW
    have hconj : ∀ l ∈ L, ∀ x ∈ W.map V.subtype, l * x * l⁻¹ ∈ W.map V.subtype := by
      intro l hl x hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨A4.actionOn V L hLV ⟨l, hl⟩ y, hW _ ((A4.mem_autOn_iff hLV).mpr ⟨_, rfl⟩) y hy,
        A4.actionOn_apply_coe hLV ⟨l, hl⟩ y⟩
    have hnorm : L ≤ Subgroup.normalizer ((W.map V.subtype : Subgroup G) : Set G) := by
      intro l hl
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨hconj l hl x, fun hx => ?_⟩
      have h1 := hconj l⁻¹ (L.inv_mem hl) _ hx
      simpa [mul_assoc] using h1
    rcases hirr.2 (W.map V.subtype) (Subgroup.map_subtype_le W) hnorm with h | h
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective _ V.subtype_injective).1 h
    · right
      rw [eq_top_iff]
      intro x _
      have hx : (x : G) ∈ W.map V.subtype := by
        rw [h]
        exact x.2
      obtain ⟨x', hx', hxx'⟩ := hx
      rw [show x = x' from Subtype.ext hxx'.symm]
      exact hx'
  obtain ⟨e, γ, he1, hwe⟩ := Orbit.exists_wedge_coords hsq hcard ψ hirr'
  set w := e ⟨v, hv⟩ with hw
  have hw0 : w ≠ 0 := by
    intro h
    apply hv1
    have h1 : e ⟨v, hv⟩ = e 1 := by rw [← hw, h, he1]
    exact congrArg Subtype.val (e.injective h1)
  set C := autOn L V ⊓ MulAction.stabilizer (MulAut ↥V) (⟨v, hv⟩ : ↥V) with hC
  let ι : G5 →* MulAut ↥V := (autOn L V).subtype.comp γ.symm.toMonoidHom
  have hιi : Function.Injective ι := Subtype.val_injective.comp γ.symm.injective
  let mat : G5 →* Matrix (Fin 5) (Fin 5) (ZMod 2) :=
    (Units.coeHom (Matrix (Fin 5) (Fin 5) (ZMod 2))).comp Matrix.SpecialLinearGroup.toGL
  have hmat : Function.Injective mat := fun x y h => Subtype.ext h
  have hCι : C ≤ ι.range := by
    rintro c ⟨hc, -⟩
    exact ⟨γ ⟨c, hc⟩, by simp [ι]⟩
  have hCe : ∀ y, ι y ∈ C ↔ wedgeRep y w = w := by
    intro y
    have hfix : ι y ∈ MulAction.stabilizer (MulAut ↥V) (⟨v, hv⟩ : ↥V) ↔
        ((γ.symm y : ↥(autOn L V)) : MulAut ↥V) ⟨v, hv⟩ = ⟨v, hv⟩ :=
      MulAction.mem_stabilizer_iff
    have hey : e (((γ.symm y : ↥(autOn L V)) : MulAut ↥V) ⟨v, hv⟩) = wedgeRep y w := by
      rw [hwe, MulEquiv.apply_symm_apply]
    constructor
    · rintro ⟨-, hy⟩
      rw [← hey, hfix.mp hy]
    · intro hy
      refine ⟨(γ.symm y).2, hfix.mpr (e.injective ?_)⟩
      rw [hey, hy]
  set U := suppW w with hU
  obtain ⟨u₀, hu₀, hu₀1⟩ := exists_mem_suppW_ne_zero hw0
  obtain ⟨y₀, hy₀⟩ := exists_not_mem_suppW (w := w)
  have htr : ∀ u ∈ U, ∀ φ : Fin 5 → ZMod 2, (∀ u' ∈ U, φ ⬝ᵥ u' = 0) →
      ∃ t : G5, mat t = 1 + Matrix.vecMulVec u φ :=
    fun u hu φ hφ => ⟨⟨1 + Matrix.vecMulVec u φ, det_transv (hφ u hu)⟩, rfl⟩
  refine autOn_ne_bot (((oTwoUpper_le _).trans inf_le_left).trans hLV) hVL hv hv1
    (eq_bot_of_radical_model ι hιi hCι (radSub mat U) (autOn_le_stab hLV hv)
      (stab_le_normalizer hLV hv) (fun r hr => (hCe r).mpr (wedgeRep_eq_of_isRadU hr)) ?_
      (fun r hr => sq_eq_one_of_mem_radSub (by decide) hmat hr) ?_ hK2)
  · intro y hy r hr
    have hy' := (hCe y).mp hy
    exact conj_mem_radSub (fun u hu => mem_suppW_of_fix hy' hu)
      (fun u hu => mem_suppW_of_fix (wedgeRep_inv_of_fix hy') hu) hr
  · intro y _ hy
    exact mem_radSub_of_commute (by decide) hu₀ hu₀1 hy₀ htr hy

end L52

end Lem12St

end CFSG.Quasithin.H13
