module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.Basic

import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.claim_H3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.claim_2
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.claim_9
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.proposition
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section3.claim_1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section3.claim_2
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section3.claim_3_b
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.Reconstruction
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.lemma_1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.lemma_2
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_12
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_13

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section3

open PFchapter1section1 PFAppendixIII PFchapter1section3
open PFchapter3section1 PFchapter3section3 MatrixGroups
open scoped LinearAlgebra.Projectivization

universe u v w

private theorem exists_standardHermitianForm
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (F : Subfield E) (sigma : E ≃+* E)
    (hfinrank : Module.finrank F E = 2)
    (hsigmaF : ∀ a : F, sigma (a : E) = (a : E))
    (hsigmaPow : ∀ x : E, sigma x = x ^ Nat.card F)
    (hfixed_mem : ∀ y : E, sigma y = y → y ∈ F) :
    ∃ J : HermitianForm 3 E,
      J.conj = sigma ∧
      J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
      Nat.card E = Nat.card F ^ 2 ∧
      Nat.card {x : E // J.conj x = x} = Nat.card F := by
  have hEcard : Nat.card E = Nat.card F ^ 2 := by
    have hcard := Module.natCard_eq_pow_finrank (K := F) (V := E)
    rw [hfinrank] at hcard
    exact hcard
  have hsigma_involutive : Function.Involutive sigma := by
    intro x
    letI : Fintype E := Fintype.ofFinite E
    calc
      sigma (sigma x) = (sigma x) ^ Nat.card F := hsigmaPow (sigma x)
      _ = (x ^ Nat.card F) ^ Nat.card F := by rw [hsigmaPow]
      _ = x ^ (Nat.card F ^ 2) := by rw [pow_two, pow_mul]
      _ = x ^ Nat.card E := by rw [hEcard]
      _ = x := by
        simpa [Nat.card_eq_fintype_card] using FiniteField.pow_card x
  let J : HermitianForm 3 E :=
    { conj := sigma
      conj_involutive := hsigma_involutive
      form := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
      form_hermitian := by
        intro i j
        fin_cases i <;> fin_cases j <;> simp
      form_nondegenerate := by
        simp [Matrix.det_fin_three] }
  let fixedEquiv : {x : E // J.conj x = x} ≃ F :=
    Equiv.ofBijective
      (fun x => (⟨x, hfixed_mem x (by simpa [J] using x.property)⟩ : F))
      ⟨by
        intro x y hxy
        apply Subtype.ext
        exact congrArg (fun z : F => (z : E)) hxy,
       by
        intro a
        refine ⟨⟨(a : E), by simpa [J] using hsigmaF a⟩, ?_⟩
        rfl⟩
  exact ⟨J, rfl, rfl, hEcard, Nat.card_congr fixedEquiv⟩

private theorem exists_unitaryCoordinateMulEquiv
    {E S : Type*} [Field E] [CharP E 2] [Group S]
    (F : Subfield E) (theta : F ≃+* F) (sigma : E ≃+* E)
    (phi : E → E → E)
    (coord : S ≃
      {p : E × E //
        (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
          (theta ≠ 1 ∧ p.2 ∈ F)})
    (hcoordMul : ∀ x y : S,
      ((coord (x * y) :
          {p : E × E //
            (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
              (theta ≠ 1 ∧ p.2 ∈ F)}) : E × E) =
        ((coord x).1.1 + (coord y).1.1,
          (coord x).1.2 + (coord y).1.2 +
            phi (coord x).1.1 (coord y).1.1))
    (htheta : theta = 1)
    (hphi : ∀ x y : E, phi x y = x * sigma y)
    (J : HermitianForm 3 E) (hJconj : J.conj = sigma) :
    ∃ e : S ≃* External.hermitianUnipotentCoord J, ∀ x : S,
      (((e x : External.hermitianUnipotentCoord J) : E × E)) =
        ((coord x :
          {p : E × E //
            (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
              (theta ≠ 1 ∧ p.2 ∈ F)}) : E × E) := by
  let Carrier :=
    {p : E × E //
      (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
        (theta ≠ 1 ∧ p.2 ∈ F)}
  let coordToRoot : Carrier ≃ External.hermitianUnipotentCoord J :=
    { toFun := fun p => ⟨p, by
        rw [hJconj]
        have hp := p.property.resolve_right (fun hp => hp.1 htheta)
        rw [hp.2, CharTwo.add_self_eq_zero]⟩
      invFun := fun z => ⟨z, Or.inl ⟨htheta, by
        rw [← hJconj]
        exact CharTwo.add_eq_zero.mp z.property⟩⟩
      left_inv := by intro p; rfl
      right_inv := by intro z; rfl }
  let e : S ≃ External.hermitianUnipotentCoord J :=
    coord.trans coordToRoot
  let eMul : S ≃* External.hermitianUnipotentCoord J :=
    { toEquiv := e
      map_mul' := by
        intro x y
        apply Subtype.ext
        change
          ((coord (x * y) : Carrier) : E × E) =
            ((coord x).1.1 + (coord y).1.1,
              (coord x).1.2 + (coord y).1.2 -
                (coord x).1.1 * J.conj (coord y).1.1)
        rw [hcoordMul, hphi, hJconj, CharTwo.sub_eq_add] }
  exact ⟨eMul, fun _ => rfl⟩

set_option maxHeartbeats 1000000 in
private theorem unitaryModelEquiv_of_rankOneCoordinates
    {L Xs E : Type*}
    [Group L] [Finite L] [MulAction L Xs] [Finite Xs] [FaithfulSMul L Xs]
    [Field E] [Finite E] [CharP E 2]
    (M Q D : Subgroup L) (t : L) (f g h : L → L) (a : Xs)
    (htwoSource : MulAction.IsMultiplyPretransitive L Xs 2)
    (hM : M = MulAction.stabilizer L a)
    (htSource : IsInvolution t) (htNotM : t ∉ M)
    (hD : D = M ⊓ rightConjugate M t)
    (hQnormal : (Q.subgroupOf M).Normal)
    (hQdisjoint : Disjoint Q D) (hQsup : Q ⊔ D = M)
    (hfmem : ∀ x : L, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hgmem : ∀ x : L, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hhmem : ∀ x : L, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical : ∀ x : L, x ∈ Q → x ≠ 1 →
      t * x * t = g x * h x * t * f x)
    (J : HermitianForm 3 E) (q : ℕ) (hq : 2 < q)
    (hEcard : Nat.card E = q ^ 2)
    (hfixedCard : Nat.card {x : E // J.conj x = x} = q)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (qCoord : Q ≃* External.hermitianUnipotentCoord J)
    (hfCoord : ∀ (x : Q) (hx : x ≠ 1),
      (((qCoord ⟨f x, (hfmem x x.property (by simpa using hx)).1⟩ :
          External.hermitianUnipotentCoord J) : E × E)) =
        ((qCoord x).1.1 / (qCoord x).1.2, (qCoord x).1.2⁻¹))
    (hQsylow : ∃ P : Sylow 2 L, Q = (P : Subgroup L)) :
    Nonempty (twoPrimeResidual L ≃*
      ProjectiveSpecialUnitaryMatrixGroup J) := by
  classical
  let P := ℙ E (Fin 3 → E)
  let A : Set P :=
    {x | ∃ (v : Fin 3 → E) (hv : v ≠ 0),
      x = Projectivization.mk E v hv ∧
        dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
  let X := {x : P // x ∈ A}
  rcases External.huppert_II_10_12 J q hEcard hfixedCard hJstandard with
    ⟨_hXcard, rho, pinf, hrho, hnatural, _hUcard, hroot,
      htwo, _hGcard, _hthree⟩
  letI : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective rho hrho
  letI : MulAction (ProjectiveSpecialUnitaryMatrixGroup J) X :=
    MulAction.compHom X rho
  letI : FaithfulSMul (ProjectiveSpecialUnitaryMatrixGroup J) X :=
    faithfulSMul_iff.mpr (by
      intro g hg
      apply hrho
      apply Equiv.ext
      intro x
      have hx := hg x
      change rho g • x = x at hx
      rw [Equiv.Perm.smul_def] at hx
      calc
        rho g x = x := hx
        _ = rho 1 x := by rw [map_one]; rfl)
  have htwo' : MulAction.IsMultiplyPretransitive
      (ProjectiveSpecialUnitaryMatrixGroup J) X 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    exact htwo a b c d hab hcd
  rcases hroot with
    ⟨R, H, hRle, hHle, hnormalizer, _hRinfH, hRsupH,
      _hHcyclic, hRcard, _hRcomm, _hRcommCard, _hHcard,
      hRregular, hcoords, hHcoords, _hHcoordsSurj⟩
  letI : Group R := Subgroup.toGroup R
  letI : DivisionMonoid R := Group.toDivisionMonoid
  rcases hcoords with ⟨coordR, hcoordRMatrix⟩
  let rootPSU := External.hermitianUnipotentPSU J hJstandard
  have hcoordR_eq_root (z : External.hermitianUnipotentCoord J) :
      ((coordR z : R) : ProjectiveSpecialUnitaryMatrixGroup J) =
        rootPSU z := by
    rcases hcoordRMatrix z with ⟨M, hM, hMproj⟩
    have hMroot : M = External.hermitianUnipotentGL J z := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      change (M : Matrix (Fin 3) (Fin 3) E) i j =
        (External.hermitianUnipotentGL J z :
          Matrix (Fin 3) (Fin 3) E) i j
      rw [hM, External.hermitianUnipotentGL_val,
        External.hermitianUnipotentMatrix_eq]
    apply Subtype.ext
    calc
      (((coordR z : R) : ProjectiveSpecialUnitaryMatrixGroup J) :
          Matrix.ProjGenLinGroup (Fin 3) E) =
          Matrix.ProjGenLinGroup.mk M := hMproj
      _ = Matrix.ProjGenLinGroup.mk
          (External.hermitianUnipotentGL J z) := by rw [hMroot]
      _ = (rootPSU z : Matrix.ProjGenLinGroup (Fin 3) E) := by
        rw [External.hermitianUnipotentPSU_val]
  let coordRMul : External.hermitianUnipotentCoord J ≃* R :=
    { coordR with
      map_mul' := by
        intro z w
        apply Subtype.ext
        calc
          ((coordR (z * w) : R) : ProjectiveSpecialUnitaryMatrixGroup J) =
              rootPSU (z * w) := hcoordR_eq_root (z * w)
          _ = rootPSU z * rootPSU w := map_mul rootPSU z w
          _ = ((coordR z : R) : ProjectiveSpecialUnitaryMatrixGroup J) *
              ((coordR w : R) : ProjectiveSpecialUnitaryMatrixGroup J) := by
                rw [hcoordR_eq_root, hcoordR_eq_root] }
  let pinf0 : X :=
    ⟨Projectivization.mk E ![1, 0, 0] (by simp), by
      refine ⟨![1, 0, 0], by simp, rfl, ?_⟩
      rw [hJstandard]
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]⟩
  let pzero : X :=
    ⟨Projectivization.mk E ![0, 0, 1] (by simp), by
      refine ⟨![0, 0, 1], by simp, rfl, ?_⟩
      rw [hJstandard]
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]⟩
  have hunipotentSU_coe (z : External.hermitianUnipotentCoord J) :
      ((External.hermitianUnipotentSU J hJstandard z : J.specialSubgroup) :
        GL (Fin 3) E) = External.hermitianUnipotentGL J z := rfl
  have hweylSU_coe :
      ((External.hermitianWeylSU J hJstandard : J.specialSubgroup) :
        GL (Fin 3) E) = External.hermitianWeylGL := rfl
  have htorusSU_coe (k : Eˣ) :
      ((External.hermitianTorusSU J hJstandard k : J.specialSubgroup) :
        GL (Fin 3) E) = External.hermitianTorusGL J k := rfl
  have hpinf_ne_zero : pinf0 ≠ pzero := by
    intro heq
    have hval := congrArg Subtype.val heq
    dsimp [pinf0, pzero] at hval
    rw [Projectivization.mk_eq_mk_iff] at hval
    rcases hval with ⟨c, hc⟩
    have hc0 := congrFun hc (0 : Fin 3)
    simp at hc0
  have hroot_fix_inf (z : External.hermitianUnipotentCoord J) :
      rho (rootPSU z) pinf0 = pinf0 := by
    apply Subtype.ext
    rw [hnatural (rootPSU z) pinf0
      (External.hermitianUnipotentSU J hJstandard z) (by rfl)]
    dsimp only [pinf0]
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
    refine ⟨1, ?_⟩
    funext i
    fin_cases i <;>
      simp [hunipotentSU_coe, External.hermitianUnipotentGL,
        External.hermitianUnipotentMatrix, Matrix.mulVec]
  have hR_fix_inf (r : R) :
      rho (r : ProjectiveSpecialUnitaryMatrixGroup J) pinf0 = pinf0 := by
    obtain ⟨z, rfl⟩ := coordR.surjective r
    rw [hcoordR_eq_root]
    exact hroot_fix_inf z
  have hpinf_eq : pinf = pinf0 := by
    by_contra hne
    have hne' : pinf0 ≠ pinf := Ne.symm hne
    have hR_ne_bot : R ≠ ⊥ := by
      rw [← Subgroup.one_lt_card_iff_ne_bot, hRcard]
      exact one_lt_pow₀ (by omega : 1 < q) (by decide : (3 : ℕ) ≠ 0)
    obtain ⟨r, hr⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR_ne_bot
    rcases hRregular pinf0 pinf0 hne' hne' with ⟨r0, hr0, huniq⟩
    have hr_eq : r = r0 := huniq r (hR_fix_inf r)
    have h1_eq : (1 : R) = r0 := huniq 1 (by
      change rho (1 : ProjectiveSpecialUnitaryMatrixGroup J) pinf0 = pinf0
      rw [map_one]
      rfl)
    exact hr (hr_eq.trans h1_eq.symm)
  subst pinf
  let T : ProjectiveSpecialUnitaryMatrixGroup J :=
    External.hermitianWeylPSU J hJstandard
  have hTGL_sq :
      External.hermitianWeylGL (K := E) *
          External.hermitianWeylGL = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [External.hermitianWeylGL, External.hermitianWeylMatrix,
        Matrix.mul_apply, Fin.sum_univ_three]
  have hT_sq : T * T = 1 := by
    apply Subtype.ext
    change Matrix.ProjGenLinGroup.mk
          (External.hermitianWeylGL (K := E)) *
        Matrix.ProjGenLinGroup.mk External.hermitianWeylGL = 1
    rw [← map_mul, hTGL_sq, map_one]
  have hT_inf : rho T pinf0 = pzero := by
    apply Subtype.ext
    rw [hnatural T pinf0 (External.hermitianWeylSU J hJstandard) (by rfl)]
    dsimp only [T, pinf0, pzero]
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
    refine ⟨1, ?_⟩
    funext i
    fin_cases i <;>
      simp [hweylSU_coe, External.hermitianWeylGL,
        External.hermitianWeylMatrix, Matrix.mulVec]
  have hT_involution : IsInvolution T := by
    constructor
    · intro hTone
      apply hpinf_ne_zero
      calc
        pinf0 = rho T pinf0 := by rw [hTone, map_one]; rfl
        _ = pzero := hT_inf
    · simpa [pow_two] using hT_sq
  have hH_fix_zero : ∀ h : H,
      rho (h : ProjectiveSpecialUnitaryMatrixGroup J) pzero = pzero := by
    intro h
    rcases hHcoords h with ⟨k, M, hM, hproj⟩
    have hMtorus : M = External.hermitianTorusGL J k := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      change (M : Matrix (Fin 3) (Fin 3) E) i j =
        (External.hermitianTorusGL J k : Matrix (Fin 3) (Fin 3) E) i j
      rw [hM, External.hermitianTorusGL_val]
      rfl
    have hh : (h : ProjectiveSpecialUnitaryMatrixGroup J) =
        External.hermitianTorusPSU J hJstandard k := by
      apply Subtype.ext
      exact hproj.trans (by
        rw [hMtorus, External.hermitianTorusPSU_val])
    rw [hh]
    apply Subtype.ext
    rw [hnatural (External.hermitianTorusPSU J hJstandard k) pzero
      (External.hermitianTorusSU J hJstandard k) (by rfl)]
    dsimp only [pzero]
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
    refine ⟨(k : E), ?_⟩
    funext i
    fin_cases i <;>
      simp [htorusSU_coe, External.hermitianTorusGL,
        External.hermitianTorusMatrix, Matrix.mulVec]
  let U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) pinf0
  have hRleU : R ≤ U := hRle
  have hHleU : H ≤ U := hHle
  have hnormalizerU : U ≤ Subgroup.normalizer R := hnormalizer
  have hRsupHU : R ⊔ H = U := hRsupH
  have hT_not_U : T ∉ U := by
    change rho T pinf0 ≠ pinf0
    intro hfix
    exact hpinf_ne_zero (hfix.symm.trans hT_inf)
  let Dt : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    U ⊓ rightConjugate U T
  have hright : rightConjugate U T =
      MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) pzero := by
    calc
      rightConjugate U T =
          MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J)
            (T⁻¹ • pinf0) := by
              exact rightConjugate_stabilizer pinf0 T
      _ = MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J)
          pzero := by
            rw [hT_involution.inv_eq_self]
            change MulAction.stabilizer _ (rho T pinf0) = _
            rw [hT_inf]
  have hHleDt : H ≤ Dt := by
    intro h hh
    refine ⟨hHleU hh, ?_⟩
    rw [hright]
    change rho h pzero = pzero
    exact hH_fix_zero ⟨h, hh⟩
  have hRdisjointDt : Disjoint R Dt := by
    rw [Subgroup.disjoint_def]
    intro x hxR hxDt
    let xr : R := ⟨x, hxR⟩
    have hxfix : rho (xr : ProjectiveSpecialUnitaryMatrixGroup J) pzero =
        pzero := by
      have hxright : x ∈ rightConjugate U T := hxDt.2
      rw [hright] at hxright
      change rho x pzero = pzero at hxright
      exact hxright
    have h1fix : rho ((1 : R) : ProjectiveSpecialUnitaryMatrixGroup J)
        pzero = pzero := by
      change rho (1 : ProjectiveSpecialUnitaryMatrixGroup J) pzero = pzero
      rw [map_one]
      rfl
    rcases hRregular pzero pzero hpinf_ne_zero.symm hpinf_ne_zero.symm with
      ⟨r0, _hr0, huniq⟩
    have hxr : xr = r0 := huniq xr hxfix
    have h1r : (1 : R) = r0 := huniq 1 h1fix
    exact congrArg Subtype.val (hxr.trans h1r.symm)
  have hRsupDt : R ⊔ Dt = U := by
    apply le_antisymm
    · exact sup_le hRleU (fun _ hx => hx.1)
    · rw [← hRsupHU]
      exact sup_le le_sup_left
        (fun _ hh => Subgroup.mem_sup_right (hHleDt hh))
  letI : (R.subgroupOf U).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hnormalizerU
  obtain ⟨cTarget, hcTarget_apply⟩ :=
    PFchapter4section1.exists_rankOneCoordinateEquiv U R Dt T pinf0 htwo' rfl
      hT_involution hT_not_U rfl
      (inferInstance : (R.subgroupOf U).Normal) hRdisjointDt hRsupDt
  have hcTarget_some (z : External.hermitianUnipotentCoord J) :
      ((cTarget (some (coordRMul z)) : X) : P) =
        Projectivization.mk E ![J.conj z.1.2, J.conj z.1.1, 1]
          (by simp) := by
    have hr :
        (((coordRMul z : R) : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹) =
          rootPSU z⁻¹ := by
      rw [show ((coordRMul z : R) :
          ProjectiveSpecialUnitaryMatrixGroup J) = rootPSU z by
            exact hcoordR_eq_root z]
      exact (map_inv rootPSU z).symm
    rw [hcTarget_apply, PFchapter4section1.rankOneCoordinate_some]
    change ((rho
      (((coordRMul z : R) : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹)
        (rho T pinf0) : X) : P) = _
    rw [hT_inf, hr]
    rw [hnatural (rootPSU z⁻¹) pzero
      (External.hermitianUnipotentSU J hJstandard z⁻¹) (by rfl)]
    rw [hunipotentSU_coe]
    dsimp only [pzero]
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
    refine ⟨1, ?_⟩
    have hzinv : (((z⁻¹ : External.hermitianUnipotentCoord J) : E × E)) =
        (-z.1.1, J.conj z.1.2) := rfl
    funext i
    fin_cases i <;>
      simp [hzinv,
        External.hermitianUnipotentGL, External.hermitianUnipotentMatrix,
        Matrix.mulVec, CharTwo.neg_eq]
  have hT_coord (z : External.hermitianUnipotentCoord J)
      (hz : z ≠ 1) :
      let z' : External.hermitianUnipotentCoord J :=
        ⟨(z.1.1 / z.1.2, z.1.2⁻¹), by
          have hy : z.1.2 ≠ 0 := by
            intro hy
            have hxprod : z.1.1 * J.conj z.1.1 = 0 := by
              simpa [hy] using z.property.symm
            have hx : z.1.1 = 0 := by
              rcases mul_eq_zero.mp hxprod with hx | hx
              · exact hx
              · apply J.conj.injective
                simpa using hx
            apply hz
            apply Subtype.ext
            apply Prod.ext
            · change z.1.1 = 0
              exact hx
            · change z.1.2 = 0
              exact hy
          have hconjy : J.conj z.1.2 ≠ 0 := (map_ne_zero J.conj).2 hy
          change z.1.2⁻¹ + J.conj z.1.2⁻¹ +
              (z.1.1 / z.1.2) * J.conj (z.1.1 / z.1.2) = 0
          rw [map_inv₀, map_div₀]
          field_simp [hy, hconjy]
          linear_combination z.property⟩
      rho T (cTarget (some (coordRMul z))) =
        cTarget (some (coordRMul z')) := by
    dsimp only
    have hy : z.1.2 ≠ 0 := by
      intro hy
      have hxprod : z.1.1 * J.conj z.1.1 = 0 := by
        simpa [hy] using z.property.symm
      have hx : z.1.1 = 0 := by
        rcases mul_eq_zero.mp hxprod with hx | hx
        · exact hx
        · apply J.conj.injective
          simpa using hx
      apply hz
      apply Subtype.ext
      apply Prod.ext
      · change z.1.1 = 0
        exact hx
      · change z.1.2 = 0
        exact hy
    have hconjy : J.conj z.1.2 ≠ 0 := (map_ne_zero J.conj).2 hy
    apply Subtype.ext
    rw [hnatural T (cTarget (some (coordRMul z)))
      (External.hermitianWeylSU J hJstandard) (by rfl)]
    rw [hcTarget_some z, Projectivization.smul_mk]
    rw [hcTarget_some]
    rw [Projectivization.mk_eq_mk_iff']
    refine ⟨J.conj z.1.2, ?_⟩
    funext i
    fin_cases i <;>
      simp [hweylSU_coe, External.hermitianWeylGL,
        External.hermitianWeylMatrix, Matrix.mulVec, map_inv₀,
        map_div₀, hconjy, CharTwo.neg_eq]
    · field_simp [hconjy]
  have hnormalClosure_le :
      Subgroup.normalClosure (R : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤
        Subgroup.closure
          ((R : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ∪ ({T} : Set _)) := by
    rw [← PFchapter4section1.iSup_rightConjugate_eq_normalClosure]
    exact PFchapter4section1.rankOneNormalClosure_le_generated
      U R Dt T pinf0 htwo' rfl hT_involution hT_not_U rfl
      (inferInstance : (R.subgroupOf U).Normal) hRdisjointDt hRsupDt
  letI : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    External.huppert_II_10_13 J q hq hEcard hfixedCard
  have hR_ne_bot : R ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, hRcard]
    exact one_lt_pow₀ (by omega : 1 < q) (by decide : (3 : ℕ) ≠ 0)
  have hnormalClosure_top :
      Subgroup.normalClosure
          (R : Set (ProjectiveSpecialUnitaryMatrixGroup J)) = ⊤ := by
    rcases (Subgroup.normalClosure_normal :
        (Subgroup.normalClosure
          (R : Set (ProjectiveSpecialUnitaryMatrixGroup J))).Normal).eq_bot_or_eq_top with
      hbot | htop
    · exfalso
      apply hR_ne_bot
      apply le_antisymm
      · intro r hr
        have hr' := Subgroup.le_normalClosure hr
        rw [hbot] at hr'
        simpa using hr'
      · exact bot_le
    · exact htop
  have hgenerated_top :
      Subgroup.closure
          ((R : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ∪ ({T} : Set _)) =
        ⊤ := by
    apply top_unique
    rw [← hnormalClosure_top]
    exact hnormalClosure_le
  let qIso : Q ≃* R := qCoord.trans coordRMul
  obtain ⟨cSource, hcSource_apply⟩ :=
    PFchapter4section1.exists_rankOneCoordinateEquiv M Q D t a htwoSource hM
      htSource htNotM hD hQnormal hQdisjoint hQsup
  let ePoint : Xs ≃ X :=
    PFchapter4section1.rankOnePointEquiv cSource cTarget qIso
  have hQtransport : ∀ q0 : Q,
      PFchapter4section1.IsActionTransport ePoint (q0 : L)
        ((qIso q0 : R) : ProjectiveSpecialUnitaryMatrixGroup J) := by
    intro q0 x
    obtain ⟨z, rfl⟩ := cSource.surjective x
    cases z with
    | none =>
        calc
          ePoint ((q0 : L) • cSource none) = ePoint (cSource none) := by
            rw [show (q0 : L) • cSource none = cSource none by
              simpa only [hcSource_apply] using
                PFchapter4section1.rankOneCoordinate_smul_Q_none
                  M Q t a hM
                    (PFchapter4section1.rankOneSplit_Q_le_M hQsup) q0]
          _ = cTarget none :=
            PFchapter4section1.rankOnePointEquiv_apply_none
              cSource cTarget qIso
          _ = ((qIso q0 : R) : ProjectiveSpecialUnitaryMatrixGroup J) •
              cTarget none := by
            symm
            simpa only [hcTarget_apply] using
              PFchapter4section1.rankOneCoordinate_smul_Q_none
                U R T pinf0 rfl hRleU (qIso q0)
          _ = ((qIso q0 : R) : ProjectiveSpecialUnitaryMatrixGroup J) •
              ePoint (cSource none) := by
            rw [PFchapter4section1.rankOnePointEquiv_apply_none
              cSource cTarget qIso]
    | some x =>
        calc
          ePoint ((q0 : L) • cSource (some x)) =
              ePoint (cSource (some (x * q0⁻¹))) := by
            rw [show (q0 : L) • cSource (some x) =
                cSource (some (x * q0⁻¹)) by
              simpa only [hcSource_apply] using
                PFchapter4section1.rankOneCoordinate_smul_Q
                  M Q t a hM
                    (PFchapter4section1.rankOneSplit_Q_le_M hQsup) q0 x]
          _ = cTarget (some (qIso (x * q0⁻¹))) :=
            PFchapter4section1.rankOnePointEquiv_apply_some
              cSource cTarget qIso (x * q0⁻¹)
          _ = cTarget (some (qIso x * (qIso q0)⁻¹)) := by
            rw [map_mul, map_inv]
          _ = ((qIso q0 : R) : ProjectiveSpecialUnitaryMatrixGroup J) •
              cTarget (some (qIso x)) := by
            symm
            simpa only [hcTarget_apply] using
              PFchapter4section1.rankOneCoordinate_smul_Q
                U R T pinf0 rfl hRleU (qIso q0) (qIso x)
          _ = ((qIso q0 : R) : ProjectiveSpecialUnitaryMatrixGroup J) •
              ePoint (cSource (some x)) := by
            rw [PFchapter4section1.rankOnePointEquiv_apply_some
              cSource cTarget qIso x]
  have htTransport : PFchapter4section1.IsActionTransport ePoint t T := by
    intro x
    obtain ⟨z, rfl⟩ := cSource.surjective x
    cases z with
    | none =>
        calc
          ePoint (t • cSource none) = ePoint (cSource (some 1)) := by
            rw [show t • cSource none = cSource (some 1) by
              simpa only [hcSource_apply] using
                PFchapter4section1.rankOneCoordinate_smul_t_none Q t a]
          _ = cTarget (some (qIso 1)) :=
            PFchapter4section1.rankOnePointEquiv_apply_some
              cSource cTarget qIso 1
          _ = cTarget (some 1) := by simp
          _ = T • cTarget none := by
            symm
            simpa only [hcTarget_apply] using
              PFchapter4section1.rankOneCoordinate_smul_t_none R T pinf0
          _ = T • ePoint (cSource none) := by
            rw [PFchapter4section1.rankOnePointEquiv_apply_none
              cSource cTarget qIso]
    | some x =>
        by_cases hx : x = 1
        · subst x
          calc
            ePoint (t • cSource (some 1)) = ePoint (cSource none) := by
              rw [show t • cSource (some 1) = cSource none by
                simpa only [hcSource_apply] using
                  PFchapter4section1.rankOneCoordinate_smul_t_one
                    Q t a htSource]
            _ = cTarget none :=
              PFchapter4section1.rankOnePointEquiv_apply_none
                cSource cTarget qIso
            _ = T • cTarget (some 1) := by
              symm
              simpa only [hcTarget_apply] using
                PFchapter4section1.rankOneCoordinate_smul_t_one
                  R T pinf0 hT_involution
            _ = T • ePoint (cSource (some 1)) := by
              rw [PFchapter4section1.rankOnePointEquiv_apply_some
                cSource cTarget qIso 1]
              simp
        · have hxL : (x : L) ≠ 1 := by simpa using hx
          let fx : Q := ⟨f x, (hfmem x x.property hxL).1⟩
          have hqcoord_ne : qCoord x ≠ 1 :=
            (map_ne_one_iff qCoord qCoord.injective).2 hx
          let z' : External.hermitianUnipotentCoord J :=
            ⟨((qCoord x).1.1 / (qCoord x).1.2,
                (qCoord x).1.2⁻¹), by
              have hy : (qCoord x).1.2 ≠ 0 := by
                intro hy
                have hxprod : (qCoord x).1.1 * J.conj (qCoord x).1.1 = 0 := by
                  simpa [hy] using (qCoord x).property.symm
                have hfirst : (qCoord x).1.1 = 0 := by
                  rcases mul_eq_zero.mp hxprod with hfirst | hfirst
                  · exact hfirst
                  · apply J.conj.injective
                    simpa using hfirst
                apply hqcoord_ne
                apply Subtype.ext
                apply Prod.ext
                · change (qCoord x).1.1 = 0
                  exact hfirst
                · change (qCoord x).1.2 = 0
                  exact hy
              have hconjy : J.conj (qCoord x).1.2 ≠ 0 :=
                (map_ne_zero J.conj).2 hy
              change (qCoord x).1.2⁻¹ + J.conj (qCoord x).1.2⁻¹ +
                  ((qCoord x).1.1 / (qCoord x).1.2) *
                    J.conj ((qCoord x).1.1 / (qCoord x).1.2) = 0
              rw [map_inv₀, map_div₀]
              field_simp [hy, hconjy]
              linear_combination (qCoord x).property⟩
          have hqIso_fx : qIso fx = coordRMul z' := by
            have hqcoord_fx : qCoord fx = z' := by
              apply Subtype.ext
              exact hfCoord x hx
            change coordRMul (qCoord fx) = coordRMul z'
            rw [hqcoord_fx]
          calc
            ePoint (t • cSource (some x)) = ePoint (cSource (some fx)) := by
              rw [show t • cSource (some x) = cSource (some fx) by
                simpa only [hcSource_apply] using
                  PFchapter4section1.rankOneCoordinate_smul_t
                    M Q D t f g h a htwoSource hM htSource htNotM hD
                    hQnormal hQdisjoint hQsup hfmem hgmem hhmem hcanonical x hx]
            _ = cTarget (some (qIso fx)) :=
              PFchapter4section1.rankOnePointEquiv_apply_some
                cSource cTarget qIso fx
            _ = cTarget (some (coordRMul z')) := by rw [hqIso_fx]
            _ = T • cTarget (some (coordRMul (qCoord x))) := by
              exact (hT_coord (qCoord x) hqcoord_ne).symm
            _ = T • cTarget (some (qIso x)) := rfl
            _ = T • ePoint (cSource (some x)) := by
              rw [PFchapter4section1.rankOnePointEquiv_apply_some
                cSource cTarget qIso x]
  obtain ⟨egen, _hgenQ, _hgenT⟩ :=
    PFchapter4section1.rankOneGeneratedSubgroup_equiv
      Q t R T qIso ePoint hQtransport htTransport
  let As : Subgroup L :=
    Subgroup.closure ((Q : Set L) ∪ ({t} : Set L))
  let At : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Subgroup.closure
      ((R : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ∪ ({T} : Set _))
  have hnormalSource : Subgroup.normalClosure (Q : Set L) ≤ As := by
    rw [← PFchapter4section1.iSup_rightConjugate_eq_normalClosure]
    exact PFchapter4section1.rankOneNormalClosure_le_generated
      M Q D t a htwoSource hM htSource htNotM hD hQnormal
      hQdisjoint hQsup
  rcases hQsylow with ⟨P0, hQP0⟩
  have hQ_le_residual : Q ≤ twoPrimeResidual L := by
    rw [hQP0, twoPrimeResidual]
    exact le_iSup (fun P : Sylow 2 L => (P : Subgroup L)) P0
  have ht_residual : t ∈ twoPrimeResidual L := by
    have htp : IsPGroup 2 (Subgroup.zpowers t) := by
      refine IsPGroup.of_card (p := 2) (G := Subgroup.zpowers t) (n := 1) ?_
      rw [Nat.card_zpowers,
        orderOf_eq_prime htSource.sq_eq_one htSource.ne_one, pow_one]
    obtain ⟨Pt, htle⟩ := htp.exists_le_sylow
    rw [twoPrimeResidual]
    exact (le_iSup (fun P : Sylow 2 L => (P : Subgroup L)) Pt)
      (htle (Subgroup.mem_zpowers t))
  have hAs_le_residual : As ≤ twoPrimeResidual L := by
    change Subgroup.closure ((Q : Set L) ∪ ({t} : Set L)) ≤
      twoPrimeResidual L
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · exact hQ_le_residual hx
    · simpa only [Set.mem_singleton_iff] using hx ▸ ht_residual
  have hresidual_le_As : twoPrimeResidual L ≤ As := by
    rw [twoPrimeResidual]
    refine iSup_le ?_
    intro P1
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq L P0 P1
    intro x hxP1
    have hxsmul : x ∈ ((c • P0 : Sylow 2 L) : Subgroup L) := by
      simpa [hc] using hxP1
    rw [Sylow.coe_subgroup_smul] at hxsmul
    have hyP0 : (MulAut.conj c)⁻¹ x ∈ (P0 : Subgroup L) :=
      (Subgroup.mem_pointwise_smul_iff_inv_smul_mem
        (a := MulAut.conj c) (S := (P0 : Subgroup L)) (x := x)).mp hxsmul
    let y : L := (MulAut.conj c)⁻¹ x
    have hyQ : y ∈ Q := by
      change (MulAut.conj c)⁻¹ x ∈ Q
      rw [hQP0]
      exact hyP0
    have hynormal : y ∈ Subgroup.normalClosure (Q : Set L) :=
      Subgroup.le_normalClosure hyQ
    have hconj := (Subgroup.normalClosure_normal :
      (Subgroup.normalClosure (Q : Set L)).Normal).conj_mem'
        y hynormal c⁻¹
    apply hnormalSource
    simpa [y, MulAut.conj_apply, mul_assoc] using hconj
  have hAs : As = twoPrimeResidual L :=
    le_antisymm hAs_le_residual hresidual_le_As
  have hAt : At = ⊤ := hgenerated_top
  exact ⟨
    (MulEquiv.subgroupCongr hAs).symm |>.trans egen |>.trans
      (MulEquiv.subgroupCongr hAt) |>.trans
        (Subgroup.topEquiv :
          (⊤ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ≃*
            ProjectiveSpecialUnitaryMatrixGroup J)⟩


set_option maxHeartbeats 1000000 in
private theorem corollary_1_core
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [Finite Omega]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G) (f g h : G → G)
    (hsection3 : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA
      G Omega H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧
      _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔
                x = 1 ∨ (x ∈ H ∧
                  _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q,
                      S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ a : G, a ∈ S → ∀ b : G, b ∈ Q1 →
                            a * b = b * a) ∧
                            S ⊔ Q1 = Q) ∧
      s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
        ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hC1 : HypothesisC1 G V) (hC2 : HypothesisC2 G S W t s)
    (hC3 : TypeBChapter3Data G K Q0 S W s)
    (hQ_two : IsPGroup 2 Q)
    (hf_mem : ∀ x : G, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : G, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : G, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : G, x ∈ Q → x ≠ 1 →
      t * x * t = g x * h x * t * f x)
    (hroute :
      (V = W ∨
        (∀ d : G, d ∈ D → d ≠ 1 →
          ∀ x : G, x ∈ Q → x ∉ Q0 →
            rightConjugateElem x d * x⁻¹ ∉ Q0)) ∨
        ∃ omega zeta : G,
          omega ∈ Q ∧ omega ∉ Q0 ∧ zeta ∈ W ∧ zeta ≠ 1 ∧
            f omega = rightConjugateElem omega⁻¹ zeta ∧ h omega ∈ W) :
    unitaryConclusion.{u, v} G Omega := by
  classical
  have hA1 := hsection3.section2.hA.A1
  obtain ⟨P, hS_eq⟩ := hsection3.section2.S_sylow_in_Q
  have hP_top : (P : Subgroup Q) = ⊤ :=
    (P.is_maximal' (hQ_two.to_subgroup ⊤) le_top).symm
  have hSQ : S = Q := by
    rw [hS_eq, hP_top]
    ext q
    constructor
    · rintro ⟨q, _hq, rfl⟩
      exact q.property
    · intro hq
      exact ⟨⟨q, hq⟩, trivial, rfl⟩
  have hC3Section2 := hC3
  rcases hC3 with
    ⟨E, hEField, hEFinite, hEChar, F, theta, sigma, phi, K1, W1,
      S1, hS1Group, coord, rho, rho1, sIso, kwIso, modelIso,
      hfinrank, hcardF, hthetaOdd, hsigmaF, hsigmaFrob, hK1, hW1ne,
      hW1norm, hW1inv, hphiThetaOne, hphiThetaNe, hcoordMul, hrho,
      hrho1, hmodelS, hmodelKW, hmapK, hmapW, hs⟩
  letI : Field E := hEField
  letI : Finite E := hEFinite
  letI : CharP E 2 := hEChar
  letI : Group S1 := hS1Group
  have hphi_zero_left : ∀ x : E, phi 0 x = 0 := by
    intro x
    by_cases htheta : theta = 1
    · rw [hphiThetaOne htheta]
      simp
    · have hzero := (hphiThetaNe htheta).2.1 0 0 x
      simpa using hzero
  have hphi_zero_right : ∀ x : E, phi x 0 = 0 := by
    intro x
    by_cases htheta : theta = 1
    · rw [hphiThetaOne htheta]
      simp
    · have hzero := (hphiThetaNe htheta).2.2.1 x 0 0
      simpa using hzero
  have hcoord_one :
      ((coord (1 : S1) :
          {p : E × E //
            (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
              (theta ≠ 1 ∧ p.2 ∈ F)}) : E × E) = (0, 0) := by
    let p : E × E :=
      ((coord (1 : S1) :
          {p : E × E //
            (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
              (theta ≠ 1 ∧ p.2 ∈ F)}) : E × E)
    have hp := hcoordMul (1 : S1) 1
    have hp_eq : p =
        (p.1 + p.1, p.2 + p.2 + phi p.1 p.1) := by
      simpa [p] using hp
    have hp_one : p.1 = 0 := by
      have hfirst := congrArg Prod.fst hp_eq
      simpa using hfirst
    have hp_two : p.2 = 0 := by
      have hsecond := congrArg Prod.snd hp_eq
      rw [hp_one, hphi_zero_left] at hsecond
      simpa using hsecond
    exact Prod.ext hp_one hp_two
  have hsIso_rho : ∀ (a : (K ⊔ W : Subgroup G)) (x : S),
      sIso (rho a x) = rho1 (kwIso a) (sIso x) := by
    intro a x
    apply (SemidirectProduct.inl_injective (φ := rho1))
    calc
      SemidirectProduct.inl (sIso (rho a x)) =
          modelIso (SemidirectProduct.inl (rho a x)) :=
        (hmodelS (rho a x)).symm
      _ = modelIso
          (SemidirectProduct.inr a * SemidirectProduct.inl x *
            SemidirectProduct.inr a⁻¹) := by
        rw [← SemidirectProduct.inl_aut]
      _ = modelIso (SemidirectProduct.inr a) *
          modelIso (SemidirectProduct.inl x) *
            modelIso (SemidirectProduct.inr a⁻¹) := by
        rw [map_mul, map_mul]
      _ = SemidirectProduct.inr (kwIso a) *
          SemidirectProduct.inl (sIso x) *
            SemidirectProduct.inr (kwIso a)⁻¹ := by
        rw [hmodelKW a, hmodelS x, hmodelKW a⁻¹, map_inv]
      _ = SemidirectProduct.inl (rho1 (kwIso a) (sIso x)) :=
        (SemidirectProduct.inl_aut (kwIso a) (sIso x)).symm
  let centerCoord (u : F) :
      {p : E × E //
        (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
          (theta ≠ 1 ∧ p.2 ∈ F)} :=
    ⟨(0, (u : E)), by
      by_cases htheta : theta = 1
      · left
        refine ⟨htheta, ?_⟩
        rw [hsigmaF]
        rw [htheta]
        simpa using CharTwo.add_self_eq_zero (u : E)
      · exact Or.inr ⟨htheta, u.property⟩⟩
  let centerS (u : F) : S := sIso.symm (coord.symm (centerCoord u))
  let center (u : F) : G := (centerS u : G)
  have hcenter_coord : ∀ u : F,
      ((coord (sIso (centerS u)) :
          {p : E × E //
            (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
              (theta ≠ 1 ∧ p.2 ∈ F)}) : E × E) = (0, (u : E)) := by
    intro u
    simp [centerS, centerCoord]
  have hcenterS_zero : centerS 0 = 1 := by
    apply sIso.injective
    apply coord.injective
    apply Subtype.ext
    simpa [centerS, centerCoord] using hcoord_one.symm
  have hcenter_zero : center 0 = 1 :=
    congrArg Subtype.val hcenterS_zero
  have hcenterS_add : ∀ u v : F, centerS (u + v) = centerS u * centerS v := by
    intro u v
    apply sIso.injective
    rw [map_mul]
    apply coord.injective
    apply Subtype.ext
    rw [hcoordMul]
    simp [hcenter_coord, hphi_zero_left]
  have hcenter_add : ∀ u v : F, center (u + v) = center u * center v := by
    intro u v
    exact congrArg Subtype.val (hcenterS_add u v)
  have hcenter_sq : ∀ u : F, center u ^ 2 = 1 := by
    intro u
    rw [pow_two, ← hcenter_add, CharTwo.add_self_eq_zero, hcenter_zero]
  have hcenter_mem_Q0 : ∀ u : F, center u ∈ Q0 := by
    intro u
    by_cases hcenter_one : center u = 1
    · simp [hcenter_one]
    · apply (hsection3.section2.Q0_def (center u)).2
      refine Or.inr ⟨?_, hcenter_one, hcenter_sq u⟩
      apply hA1.Q_le_H
      simpa [hSQ, center] using (centerS u).property
  have hcenter_injective : Function.Injective center := by
    intro u v huv
    apply Subtype.ext
    have huvS : centerS u = centerS v := Subtype.ext huv
    have hcoords := congrArg
      (fun x : S =>
        ((coord (sIso x) :
          {p : E × E //
            (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
              (theta ≠ 1 ∧ p.2 ∈ F)}) : E × E)) huvS
    have hsecond := congrArg Prod.snd hcoords
    simpa [hcenter_coord] using hsecond
  let centerToQ0 : F → Q0 := fun u => ⟨center u, hcenter_mem_Q0 u⟩
  have hcenterToQ0_injective : Function.Injective centerToQ0 := by
    intro u v huv
    apply hcenter_injective
    exact congrArg (fun q : Q0 => (q : G)) huv
  have hcenterToQ0_bijective : Function.Bijective centerToQ0 :=
    hcenterToQ0_injective.bijective_of_nat_card_le (by rw [hcardF])
  have hcenter_surjective : ∀ y : G, y ∈ Q0 → ∃ u : F, center u = y := by
    intro y hy
    obtain ⟨u, hu⟩ := hcenterToQ0_bijective.2 ⟨y, hy⟩
    exact ⟨u, congrArg Subtype.val hu⟩
  let coordPair (x : S) : E × E :=
    ((coord (sIso x) :
      {p : E × E //
        (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
          (theta ≠ 1 ∧ p.2 ∈ F)}) : E × E)
  have hcenter_coordPair (u : F) :
      coordPair (centerS u) = (0, (u : E)) := by
    simpa [coordPair] using hcenter_coord u
  have hcoordPair_mul (x y : S) :
      coordPair (x * y) =
        ((coordPair x).1 + (coordPair y).1,
          (coordPair x).2 + (coordPair y).2 +
            phi (coordPair x).1 (coordPair y).1) := by
    simpa [coordPair] using hcoordMul (sIso x) (sIso y)
  have hcoordPair_one : coordPair 1 = (0, 0) := by
    simpa [coordPair] using hcoord_one
  have hcoordPair_zero_of_mem_Q0 (x : S) (hxQ0 : (x : G) ∈ Q0) :
      (coordPair x).1 = 0 := by
    obtain ⟨u, hu⟩ := hcenter_surjective (x : G) hxQ0
    have hx : x = centerS u := Subtype.ext hu.symm
    rw [hx]
    exact congrArg Prod.fst (hcenter_coord u)
  have hmem_Q0_of_coordPair_zero (x : S) (hxzero : (coordPair x).1 = 0) :
      (x : G) ∈ Q0 := by
    have hx_sq : x * x = 1 := by
      apply sIso.injective
      apply coord.injective
      apply Subtype.ext
      change coordPair (x * x) = coordPair 1
      rw [hcoordPair_mul, hxzero, hphi_zero_left]
      simp [hcoordPair_one, CharTwo.add_self_eq_zero]
    by_cases hxone : (x : G) = 1
    · simp [hxone]
    · exact (hsection3.section2.Q0_def _).2 <|
        Or.inr ⟨hA1.Q_le_H (by simpa [hSQ] using x.property),
          hxone, by simpa [pow_two] using congrArg Subtype.val hx_sq⟩
  let conjS (x : S) (a : (K ⊔ W : Subgroup G)) : S := rho a⁻¹ x
  have hconjS_coe : ∀ (x : S) (a : (K ⊔ W : Subgroup G)),
      ((conjS x a : S) : G) = rightConjugateElem (x : G) (a : G) := by
    intro x a
    simpa [conjS, rightConjugateElem] using hrho a⁻¹ x
  have hconjS_coord : ∀ (x : S) (a : (K ⊔ W : Subgroup G)),
      coordPair (conjS x a) =
          ((((kwIso a : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) *
            (coordPair x).1,
          (((kwIso a : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) *
            sigma (((kwIso a : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) *
              (coordPair x).2) := by
    intro x a
    change
      ((coord (sIso (rho a⁻¹ x)) :
        {p : E × E //
          (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
            (theta ≠ 1 ∧ p.2 ∈ F)}) : E × E) = _
    rw [hsIso_rho]
    simpa [map_inv, coordPair] using hrho1 (kwIso a) (sIso x)
  have hconjS_first : ∀ (x : S) (a : (K ⊔ W : Subgroup G)),
      (coordPair (conjS x a)).1 =
        (((kwIso a : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) *
          (coordPair x).1 := by
    intro x a
    exact congrArg Prod.fst (hconjS_coord x a)
  have hkwIso_mem_K1 : ∀ (a : G), ∀ ha : a ∈ K,
      (((kwIso (⟨a, Subgroup.mem_sup_left ha⟩ : (K ⊔ W : Subgroup G)) :
          (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) ∈ K1) := by
    intro a ha
    let aKW : (K ⊔ W : Subgroup G) := ⟨a, Subgroup.mem_sup_left ha⟩
    have ha_sub : aKW ∈ K.subgroupOf (K ⊔ W) := ha
    have ha_map : kwIso aKW ∈
        Subgroup.map kwIso.toMonoidHom (K.subgroupOf (K ⊔ W)) :=
      ⟨aKW, ha_sub, rfl⟩
    rw [hmapK] at ha_map
    exact ha_map
  have hkwIso_mem_W1 : ∀ (a : G), ∀ ha : a ∈ W,
      (((kwIso (⟨a, Subgroup.mem_sup_right ha⟩ : (K ⊔ W : Subgroup G)) :
          (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) ∈ W1) := by
    intro a ha
    let aKW : (K ⊔ W : Subgroup G) := ⟨a, Subgroup.mem_sup_right ha⟩
    have ha_sub : aKW ∈ W.subgroupOf (K ⊔ W) := ha
    have ha_map : kwIso aKW ∈
        Subgroup.map kwIso.toMonoidHom (W.subgroupOf (K ⊔ W)) :=
      ⟨aKW, ha_sub, rfl⟩
    rw [hmapW] at ha_map
    exact ha_map
  have hK_of_scalar : ∀ b : Fˣ,
      ∃ a : G, ∃ ha : a ∈ K,
        (((kwIso (⟨a, Subgroup.mem_sup_left ha⟩ : (K ⊔ W : Subgroup G)) :
            (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) = ((b : F) : E) := by
    intro b
    let bE : Eˣ := Units.map F.subtype.toMonoidHom b
    have hbE_K1 : bE ∈ K1 := by
      apply (hK1 bE).2
      exact ⟨b, by simp [bE]⟩
    let bKW : (K1 ⊔ W1 : Subgroup Eˣ) :=
      ⟨bE, Subgroup.mem_sup_left hbE_K1⟩
    have hb_sub : bKW ∈ K1.subgroupOf (K1 ⊔ W1) := hbE_K1
    rw [← hmapK] at hb_sub
    obtain ⟨aKW, haK, ha_image⟩ := hb_sub
    refine ⟨(aKW : G), haK, ?_⟩
    have haKW_eq :
        (⟨(aKW : G), Subgroup.mem_sup_left haK⟩ :
            (K ⊔ W : Subgroup G)) = aKW := Subtype.ext rfl
    rw [haKW_eq]
    have himage := congrArg
      (fun z : (K1 ⊔ W1 : Subgroup Eˣ) => (((z : Eˣ) : E))) ha_image
    simpa [bKW, bE] using himage
  let kOf (b : Fˣ) : G := Classical.choose (hK_of_scalar b)
  have hkOf_mem : ∀ b : Fˣ, kOf b ∈ K := by
    intro b
    exact Classical.choose (Classical.choose_spec (hK_of_scalar b))
  have hkOf_coord : ∀ b : Fˣ,
      (((kwIso (⟨kOf b, Subgroup.mem_sup_left (hkOf_mem b)⟩ :
          (K ⊔ W : Subgroup G)) : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) =
        ((b : F) : E) := by
    intro b
    exact Classical.choose_spec (Classical.choose_spec (hK_of_scalar b))
  have hcenter_conj_K_exact : ∀ (a : G), ∀ ha : a ∈ K, ∀ (b : Fˣ),
      (((kwIso (⟨a, Subgroup.mem_sup_left ha⟩ : (K ⊔ W : Subgroup G)) :
          (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) = ((b : F) : E) →
      ∀ u : F, rightConjugateElem (center u) a =
        center ((b : F) * theta (b : F) * u) := by
    intro a ha b hb u
    let aKW : (K ⊔ W : Subgroup G) := ⟨a, Subgroup.mem_sup_left ha⟩
    have hsub : conjS (centerS u) aKW =
        centerS ((b : F) * theta (b : F) * u) := by
      apply sIso.injective
      apply coord.injective
      apply Subtype.ext
      change coordPair (conjS (centerS u) aKW) =
        coordPair (centerS ((b : F) * theta (b : F) * u))
      rw [hconjS_coord, hcenter_coordPair, hcenter_coordPair]
      change
        (((((kwIso aKW : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E)) * 0,
          ((((kwIso aKW : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E)) *
            sigma ((((kwIso aKW : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E)) *
              (u : E)) =
          (0, (((b : F) * theta (b : F) * u : F) : E))
      rw [hb, hsigmaF]
      simp
    calc
      rightConjugateElem (center u) a =
          ((conjS (centerS u) aKW : S) : G) := by rw [hconjS_coe]
      _ = center ((b : F) * theta (b : F) * u) :=
        congrArg Subtype.val hsub
  have hcenter_conj_W : ∀ (a : G), a ∈ W → ∀ u : F,
      rightConjugateElem (center u) a = center u := by
    intro a ha u
    let aKW : (K ⊔ W : Subgroup G) := ⟨a, Subgroup.mem_sup_right ha⟩
    let aUnit : Eˣ :=
      ((kwIso aKW : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ)
    have haUnit_W1 : aUnit ∈ W1 := hkwIso_mem_W1 a ha
    have ha_sigma : sigma (aUnit : E) = (aUnit : E)⁻¹ :=
      hW1inv aUnit haUnit_W1
    have hsub : conjS (centerS u) aKW = centerS u := by
      apply sIso.injective
      apply coord.injective
      apply Subtype.ext
      change coordPair (conjS (centerS u) aKW) = coordPair (centerS u)
      rw [hconjS_coord, hcenter_coordPair]
      change ((aUnit : E) * 0,
          (aUnit : E) * sigma (aUnit : E) * (u : E)) = (0, (u : E))
      rw [ha_sigma]
      simp
    calc
      rightConjugateElem (center u) a =
          ((conjS (centerS u) aKW : S) : G) := by rw [hconjS_coe]
      _ = center u := congrArg Subtype.val hsub
  have hKW_commute : ∀ (a b : G), a ∈ K ⊔ W → b ∈ K ⊔ W → Commute a b := by
    intro a b ha hb
    let aKW : (K ⊔ W : Subgroup G) := ⟨a, ha⟩
    let bKW : (K ⊔ W : Subgroup G) := ⟨b, hb⟩
    have hsub : Commute aKW bKW := by
      rw [Commute]
      apply kwIso.injective
      simpa only [map_mul] using mul_comm (kwIso aKW) (kwIso bKW)
    exact congrArg Subtype.val hsub.eq
  obtain ⟨hsS, hs_coord⟩ := hs
  have hs_centerS : (⟨s, hsS⟩ : S) = centerS 1 := by
    apply sIso.injective
    apply coord.injective
    apply Subtype.ext
    rw [hs_coord, hcenter_coord]
    simp
  have hs_center : s = center 1 := congrArg Subtype.val hs_centerS
  have hKW_fixed_point_free : ∀ d : G, d ∈ K ⊔ W → d ≠ 1 →
      ∀ x : G, x ∈ Q → x ∉ Q0 →
        rightConjugateElem x d * x⁻¹ ∉ Q0 := by
    intro d hdKW hdne x hxQ hxQ0 hfixed
    let dKW : (K ⊔ W : Subgroup G) := ⟨d, hdKW⟩
    let xS : S := ⟨x, by simpa [hSQ] using hxQ⟩
    let yS : S := conjS xS dKW
    have hy_coe : (yS : G) = rightConjugateElem x d := by
      exact hconjS_coe xS dKW
    let zS : S := yS * xS⁻¹
    have hzQ0 : (zS : G) ∈ Q0 := by
      simpa [zS, hy_coe, xS] using hfixed
    have hzfirst : (coordPair zS).1 = 0 :=
      hcoordPair_zero_of_mem_Q0 zS hzQ0
    have hxinvfirst : (coordPair xS⁻¹).1 = (coordPair xS).1 := by
      have hone := congrArg Prod.fst (hcoordPair_mul xS⁻¹ xS)
      rw [show xS⁻¹ * xS = 1 by simp, hcoordPair_one] at hone
      change 0 = (coordPair xS⁻¹).1 + (coordPair xS).1 at hone
      exact (CharTwo.add_eq_zero.mp hone.symm)
    have hyfirst : (coordPair yS).1 = (coordPair xS).1 := by
      rw [hcoordPair_mul, hxinvfirst] at hzfirst
      exact CharTwo.add_eq_zero.mp hzfirst
    have hxfirst_ne : (coordPair xS).1 ≠ 0 := by
      intro hxzero
      exact hxQ0 (by
        simpa [xS] using hmem_Q0_of_coordPair_zero xS hxzero)
    have hscalar :
        (((kwIso dKW : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) = 1 := by
      have hscale := hconjS_first xS dKW
      rw [hyfirst] at hscale
      exact mul_right_cancel₀ hxfirst_ne (by simpa using hscale.symm)
    have hkw_one : kwIso dKW = 1 := by
      apply Subtype.ext
      apply Units.ext
      exact hscalar
    have hdKW_one : dKW = 1 := kwIso.injective (by simpa using hkw_one)
    apply hdne
    exact congrArg Subtype.val hdKW_one
  have hW_fixed_point_free : ∀ d : G, d ∈ W → d ≠ 1 →
      ∀ x : G, x ∈ Q → x ∉ Q0 →
        rightConjugateElem x d * x⁻¹ ∉ Q0 := by
    intro d hdW hdne x hxQ hxQ0
    exact hKW_fixed_point_free d (Subgroup.mem_sup_right hdW) hdne x hxQ hxQ0
  have hV_le_D : V ≤ D := by
    rw [hsection3.section2.V_eq]
    exact inf_le_left
  have hW_le_D : W ≤ D := hsection3.section2.W_le_V.trans hV_le_D
  have hKW_le_D : K ⊔ W ≤ D :=
    sup_le hsection3.section2.K_le_D hW_le_D
  have hQ0_commutes_Q : ∀ x : G, x ∈ Q0 → ∀ q : G, q ∈ Q → x * q = q * x :=
    PFchapter4section2.Q0_commutes_Q
      H D Q K V W Q0 S Q1 t s hsection3 hC2
  have hQ0_stable_D : ∀ d : D, ∀ q : Q0,
      rightConjugateElem (q : G) (d : G)⁻¹ ∈ Q0 := by
    intro d q
    rcases (hsection3.section2.Q0_def (q : G)).1 q.property with
      hq_one | ⟨hqH, hqI⟩
    · rw [hq_one]
      simp [rightConjugateElem]
    · apply (hsection3.section2.Q0_def _).2
      refine Or.inr ⟨?_, isInvolution_rightConjugateElem hqI⟩
      have hdH : (d : G) ∈ H := hA1.D_le_H d.property
      exact H.mul_mem
        (H.mul_mem (H.inv_mem (H.inv_mem hdH)) hqH) (H.inv_mem hdH)
  let Q0Q : Subgroup Q := Q0.subgroupOf Q
  have hQ0Q_normal : Q0Q.Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer
      hsection3.section2.Q0_le_Q).2
    intro q hqQ
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hyQ0
      have hcomm := hQ0_commutes_Q y hyQ0 q hqQ
      have hconj : q * y * q⁻¹ = y := by
        rw [← hcomm]
        simp
      simpa [hconj] using hyQ0
    · intro hyQ0
      have hcomm := hQ0_commutes_Q (q * y * q⁻¹) hyQ0 q hqQ
      have hy_eq : y = q * y * q⁻¹ := by
        calc
          y = q⁻¹ * (q * y * q⁻¹) * q := by group
          _ = q⁻¹ * ((q * y * q⁻¹) * q) := by rw [mul_assoc]
          _ = q⁻¹ * (q * (q * y * q⁻¹)) := by rw [hcomm]
          _ = q * y * q⁻¹ := by group
      rwa [hy_eq]
  letI : Q0Q.Normal := hQ0Q_normal
  have hKW_normalizes_Q : K ⊔ W ≤ Subgroup.normalizer Q :=
    hKW_le_D.trans hA1.D_le_H |>.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hA1.Q_le_H).1
        hA1.Q_normal_in_H)
  letI : MulDistribMulAction (K ⊔ W : Subgroup G) Q :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer
      (G := G) (K ⊔ W) Q hKW_normalizes_Q
  have hKW_smul_coe : ∀ (d : (K ⊔ W : Subgroup G)) (q : Q),
      ((d • q : Q) : G) = (d : G) * (q : G) * (d : G)⁻¹ := by
    intro d q
    exact Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit
      (K ⊔ W) Q hKW_normalizes_Q d q
  have hQ0Q_invariant : IsInvariant (K ⊔ W : Subgroup G) Q Q0Q := by
    refine ⟨?_⟩
    have hforward : ∀ (d : (K ⊔ W : Subgroup G)) (q : Q),
        q ∈ Q0Q → d • q ∈ Q0Q := by
      intro d q hq
      let dD : D := ⟨d, hKW_le_D d.property⟩
      have hstable := hQ0_stable_D dD ⟨q, hq⟩
      change (d : G) * (q : G) * (d : G)⁻¹ ∈ Q0
      simpa [dD, rightConjugateElem, mul_assoc] using hstable
    intro d q
    constructor
    · exact hforward d q
    · intro hdq
      have hinv : d⁻¹ • (d • q) ∈ Q0Q := hforward d⁻¹ (d • q) hdq
      simpa using hinv
  letI : MulAction.QuotientAction (K ⊔ W : Subgroup G) Q0Q :=
    quotientAction_of_isInvariant (A := (K ⊔ W : Subgroup G))
      (G := Q) Q0Q hQ0Q_invariant
  letI : MulDistribMulAction (K ⊔ W : Subgroup G) (Q ⧸ Q0Q) :=
    quotientMulDistribMulAction (A := (K ⊔ W : Subgroup G))
      (G := Q) Q0Q hQ0Q_invariant
  have hquotient_card : Nat.card (Q ⧸ Q0Q) = Nat.card Q0 ^ 2 := by
    have hcardQ :=
      PFchapter4section2.natCard_eq_cube_of_isSuzukiTwoTypeB H Q Q0 S
        hC2.S_type_B hsection3.section2.S_le_Q hA1.Q_le_H
        hsection3.section2.Q0_le_Q hsection3.section2.Q0_def hSQ
    have hcardQ0Q : Nat.card Q0Q = Nat.card Q0 :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (H := Q0) (K := Q) hsection3.section2.Q0_le_Q).toEquiv
    have hprod : Nat.card (Q ⧸ Q0Q) * Nat.card Q0 =
        Nat.card Q0 ^ 2 * Nat.card Q0 := by
      calc
        Nat.card (Q ⧸ Q0Q) * Nat.card Q0 =
            Nat.card (Q ⧸ Q0Q) * Nat.card Q0Q := by rw [hcardQ0Q]
        _ = Nat.card Q :=
          (Subgroup.card_eq_card_quotient_mul_card_subgroup Q0Q).symm
        _ = Nat.card Q0 ^ 3 := hcardQ
        _ = Nat.card Q0 ^ 2 * Nat.card Q0 := by ring
    apply Nat.mul_right_cancel (Nat.card_pos (α := Q0))
    exact hprod
  have hquotient_fixed : ∀ d : (K ⊔ W : Subgroup G), d ≠ 1 →
      ∀ qbar : Q ⧸ Q0Q,
      d • qbar = qbar → qbar = 1 := by
    intro d hd qbar hfix
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective Q0Q qbar
    change (q : Q ⧸ Q0Q) = 1
    rw [QuotientGroup.eq_one_iff]
    by_contra hqQ0
    apply hKW_fixed_point_free (d : G)⁻¹ ((K ⊔ W).inv_mem d.property)
    · intro hdG
      apply hd
      apply Subtype.ext
      simpa using congrArg Inv.inv hdG
    · exact q.property
    · exact hqQ0
    · have hquot :
          QuotientGroup.mk' Q0Q (d • q) = QuotientGroup.mk' Q0Q q := by
        simpa using hfix
      have hdiv : (d • q) / q ∈ Q0Q :=
        (QuotientGroup.eq_iff_div_mem).1 hquot
      have hdivG : (((d • q) / q : Q) : G) ∈ Q0 := hdiv
      have hsmul : ((d • q : Q) : G) =
          (d : G) * (q : G) * (d : G)⁻¹ := hKW_smul_coe d q
      simpa only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv,
        hsmul, div_eq_mul_inv, rightConjugateElem, inv_inv, mul_assoc] using hdivG
  let QuotientNontrivial := {qbar : Q ⧸ Q0Q // qbar ≠ 1}
  letI : MulAction (K ⊔ W : Subgroup G) QuotientNontrivial :=
    { smul := fun d qbar => ⟨d • (qbar : Q ⧸ Q0Q), by
        intro hone
        apply qbar.property
        have hback := congrArg (fun x : Q ⧸ Q0Q => d⁻¹ • x) hone
        simpa using hback⟩
      one_smul := by
        intro qbar
        apply Subtype.ext
        exact one_smul (K ⊔ W : Subgroup G) (qbar : Q ⧸ Q0Q)
      mul_smul := by
        intro a b qbar
        apply Subtype.ext
        exact mul_smul a b (qbar : Q ⧸ Q0Q) }
  have hstab : ∀ qbar : QuotientNontrivial,
      MulAction.stabilizer (K ⊔ W : Subgroup G) qbar = ⊥ := by
    intro qbar
    rw [eq_bot_iff]
    intro d hd
    have hfix : d • qbar = qbar := by
      simpa [MulAction.mem_stabilizer_iff] using hd
    by_contra hd_ne
    exact qbar.property
      (hquotient_fixed d hd_ne (qbar : Q ⧸ Q0Q)
        (congrArg Subtype.val hfix))
  let eKSub : K.subgroupOf (K ⊔ W) ≃*
      K1.subgroupOf (K1 ⊔ W1) :=
    (kwIso.subgroupMap (K.subgroupOf (K ⊔ W))).trans
      (MulEquiv.subgroupCongr hmapK)
  let eK : K ≃* K1 :=
    (Subgroup.subgroupOfEquivOfLe (H := K) (K := K ⊔ W) le_sup_left).symm |>.trans
      (eKSub.trans
        (Subgroup.subgroupOfEquivOfLe
          (H := K1) (K := K1 ⊔ W1) le_sup_left))
  let eWSub : W.subgroupOf (K ⊔ W) ≃*
      W1.subgroupOf (K1 ⊔ W1) :=
    (kwIso.subgroupMap (W.subgroupOf (K ⊔ W))).trans
      (MulEquiv.subgroupCongr hmapW)
  let eW : W ≃* W1 :=
    (Subgroup.subgroupOfEquivOfLe (H := W) (K := K ⊔ W) le_sup_right).symm |>.trans
      (eWSub.trans
        (Subgroup.subgroupOfEquivOfLe
          (H := W1) (K := K1 ⊔ W1) le_sup_right))
  have hW1_cyclic : IsCyclic W1 :=
    isCyclic_of_injective W1.subtype W1.subtype_injective
  have hW_cyclic : IsCyclic W := eW.isCyclic.mpr hW1_cyclic
  let liftK1 : Fˣ → K1 := fun b =>
    ⟨Units.map F.subtype b, (hK1 _).2 ⟨b, rfl⟩⟩
  have hliftK1_bijective : Function.Bijective liftK1 := by
    constructor
    · intro b c hbc
      apply Units.ext
      apply F.subtype.injective
      have hval := congrArg (fun a : K1 => (((a : Eˣ) : E))) hbc
      simpa [liftK1] using hval
    · intro a
      obtain ⟨b, hb⟩ := (hK1 (a : Eˣ)).1 a.property
      refine ⟨b, ?_⟩
      apply Subtype.ext
      apply Units.ext
      simpa [liftK1] using hb.symm
  let eFK1 : Fˣ ≃ K1 := Equiv.ofBijective liftK1 hliftK1_bijective
  have hcardK : Nat.card K = Nat.card Q0 - 1 := by
    calc
      Nat.card K = Nat.card K1 := Nat.card_congr eK.toEquiv
      _ = Nat.card Fˣ := (Nat.card_congr eFK1).symm
      _ = Nat.card F - 1 := Nat.card_units F
      _ = Nat.card Q0 - 1 := by rw [hcardF]
  have hK_inter_W : ∀ x : G, x ∈ K → x ∈ W → x = 1 := by
    intro x hxK hxW
    have hxV : x ∈ V := hsection3.section2.W_le_V hxW
    rw [hsection3.section2.V_eq] at hxV
    have hxt : t * x = x * t :=
      (Subgroup.mem_centralizer_iff.mp hxV.2) t (by simp)
    have hfix : rightConjugateElem x t = x := by
      calc
        rightConjugateElem x t = t⁻¹ * x * t := rfl
        _ = t⁻¹ * (x * t) := by rw [mul_assoc]
        _ = t⁻¹ * (t * x) := by rw [hxt]
        _ = x := by simp
    have hinv : rightConjugateElem x t = x⁻¹ :=
      (hsection3.section2.K_def x).1 hxK |>.2
    have hxinverse : x = x⁻¹ := hfix.symm.trans hinv
    have hx_sq : x ^ 2 = 1 := by
      rw [pow_two]
      nth_rw 1 [hxinverse]
      simp
    let xD : D := ⟨x, hsection3.section2.K_le_D hxK⟩
    have hxD_sq : xD ^ 2 = 1 := by
      apply Subtype.ext
      simpa [xD] using hx_sq
    have horder_two : orderOf xD ∣ 2 := orderOf_dvd_of_pow_eq_one hxD_sq
    have horder_card : orderOf xD ∣ Nat.card D := orderOf_dvd_natCard xD
    have horder_one : orderOf xD = 1 :=
      Nat.eq_one_of_dvd_coprimes hA1.D_odd.coprime_two_right
        horder_card horder_two
    have hxD_one : xD = 1 := orderOf_eq_one_iff.mp horder_one
    exact congrArg Subtype.val hxD_one
  have hW_centralizes_K : W ≤ Subgroup.centralizer (K : Set G) := by
    intro w hw
    rw [hsection3.section2.W_eq] at hw
    exact hw.2
  have hW_normalizes_K : W ≤ Subgroup.normalizer (K : Set G) :=
    hW_centralizes_K.trans (centralizer_le_normalizer K)
  let mulD : K × W → (K ⊔ W : Subgroup G) := fun p =>
    ⟨(p.1 : G) * (p.2 : G),
      (K ⊔ W).mul_mem
        (Subgroup.mem_sup_left p.1.property)
        (Subgroup.mem_sup_right p.2.property)⟩
  have hmulD_bijective : Function.Bijective mulD := by
    constructor
    · rintro ⟨k₁, w₁⟩ ⟨k₂, w₂⟩ hp
      have hval : (k₁ : G) * (w₁ : G) = (k₂ : G) * (w₂ : G) :=
        congrArg (fun d : (K ⊔ W : Subgroup G) => (d : G)) hp
      have hcross : (k₂ : G)⁻¹ * (k₁ : G) =
          (w₂ : G) * (w₁ : G)⁻¹ := by
        calc
          (k₂ : G)⁻¹ * (k₁ : G) =
              (k₂ : G)⁻¹ * ((k₁ : G) * (w₁ : G)) * (w₁ : G)⁻¹ := by
                simp [mul_assoc]
          _ = (k₂ : G)⁻¹ * ((k₂ : G) * (w₂ : G)) * (w₁ : G)⁻¹ := by
            rw [hval]
          _ = (w₂ : G) * (w₁ : G)⁻¹ := by simp
      have hcrossK : (k₂ : G)⁻¹ * (k₁ : G) ∈ K :=
        K.mul_mem (K.inv_mem k₂.property) k₁.property
      have hcrossW : (k₂ : G)⁻¹ * (k₁ : G) ∈ W := by
        rw [hcross]
        exact W.mul_mem w₂.property (W.inv_mem w₁.property)
      have hcross_one := hK_inter_W _ hcrossK hcrossW
      have hk : (k₁ : G) = (k₂ : G) := by
        calc
          (k₁ : G) = (k₂ : G) * ((k₂ : G)⁻¹ * (k₁ : G)) := by group
          _ = (k₂ : G) * 1 := by rw [hcross_one]
          _ = (k₂ : G) := by simp
      have hw : (w₁ : G) = (w₂ : G) := by
        rw [hk] at hval
        exact mul_left_cancel hval
      exact Prod.ext (Subtype.ext hk) (Subtype.ext hw)
    · intro d
      have hdSup : (d : G) ∈ K ⊔ W := d.property
      change (d : G) ∈ ((K ⊔ W : Subgroup G) : Set G) at hdSup
      rw [Subgroup.coe_mul_of_right_le_normalizer_left
        K W hW_normalizes_K] at hdSup
      rcases Set.mem_mul.mp hdSup with ⟨k, hk, w, hw, hkw⟩
      exact ⟨(⟨k, hk⟩, ⟨w, hw⟩), Subtype.ext hkw⟩
  let dEquiv : K × W ≃ (K ⊔ W : Subgroup G) :=
    Equiv.ofBijective mulD hmulD_bijective
  have hcardD : Nat.card (K ⊔ W : Subgroup G) =
      (Nat.card Q0 - 1) * Nat.card W := by
    calc
      Nat.card (K ⊔ W : Subgroup G) = Nat.card (K × W) :=
        (Nat.card_congr dEquiv).symm
      _ = Nat.card K * Nat.card W := Nat.card_prod K W
      _ = (Nat.card Q0 - 1) * Nat.card W := by rw [hcardK]
  let OrbitIndex := Quotient
    (MulAction.orbitRel (K ⊔ W : Subgroup G) QuotientNontrivial)
  let n := Nat.card OrbitIndex
  let orbitDecomp : QuotientNontrivial ≃
      OrbitIndex × (K ⊔ W : Subgroup G) :=
    MulAction.selfEquivOrbitsQuotientProd hstab
  have hcardQuotientNontrivial :
      Nat.card QuotientNontrivial = Nat.card (Q ⧸ Q0Q) - 1 := by
    letI : Fintype (Q ⧸ Q0Q) := Fintype.ofFinite (Q ⧸ Q0Q)
    letI : Fintype QuotientNontrivial := Fintype.ofFinite QuotientNontrivial
    simp [QuotientNontrivial, Nat.card_eq_fintype_card]
  have horbit_card :
      n * ((Nat.card Q0 - 1) * Nat.card W) = Nat.card Q0 ^ 2 - 1 := by
    calc
      n * ((Nat.card Q0 - 1) * Nat.card W) =
          n * Nat.card (K ⊔ W : Subgroup G) := by
        rw [hcardD]
      _ = Nat.card (OrbitIndex × (K ⊔ W : Subgroup G)) := by
        rw [Nat.card_prod]
      _ = Nat.card QuotientNontrivial :=
        (Nat.card_congr orbitDecomp).symm
      _ = Nat.card (Q ⧸ Q0Q) - 1 := hcardQuotientNontrivial
      _ = Nat.card Q0 ^ 2 - 1 := by rw [hquotient_card]
  have hsQ0 : s ∈ Q0 :=
    (hsection3.section2.Q0_def s).2
      (Or.inr ⟨hsection3.2.1, hsection3.2.2.1⟩)
  have hcardQ0_two : 2 ≤ Nat.card Q0 := by
    let embed : Bool → Q0 := fun b => if b then ⟨s, hsQ0⟩ else 1
    have hembed : Function.Injective embed := by
      intro a b hab
      cases a <;> cases b
      · rfl
      · exfalso
        have hsone : s = 1 := by
          simpa [embed] using congrArg (fun q : Q0 => (q : G)) hab.symm
        exact hsection3.2.2.1.ne_one hsone
      · exfalso
        have hsone : s = 1 := by
          simpa [embed] using congrArg (fun q : Q0 => (q : G)) hab
        exact hsection3.2.2.1.ne_one hsone
      · rfl
    simpa using Nat.card_le_card_of_injective embed hembed
  have hn : n * Nat.card W = Nat.card Q0 + 1 := by
    have hfactor : Nat.card Q0 ^ 2 - 1 =
        (Nat.card Q0 + 1) * (Nat.card Q0 - 1) := by
      let q := Nat.card Q0 - 1
      have hq : q + 1 = Nat.card Q0 := Nat.sub_add_cancel (by omega)
      calc
        Nat.card Q0 ^ 2 - 1 = (q + 1) ^ 2 - 1 := by rw [hq]
        _ = q ^ 2 + 2 * q := by ring_nf; omega
        _ = (q + 2) * q := by ring
        _ = (Nat.card Q0 + 1) * (Nat.card Q0 - 1) := by
          rw [← hq]
          simp
    have hcancel : (n * Nat.card W) * (Nat.card Q0 - 1) =
        (Nat.card Q0 + 1) * (Nat.card Q0 - 1) := by
      calc
        (n * Nat.card W) * (Nat.card Q0 - 1) =
            n * ((Nat.card Q0 - 1) * Nat.card W) := by ring
        _ = Nat.card Q0 ^ 2 - 1 := horbit_card
        _ = (Nat.card Q0 + 1) * (Nat.card Q0 - 1) := hfactor
    apply Nat.mul_right_cancel (by omega : 0 < Nat.card Q0 - 1)
    exact hcancel
  letI : IsCyclic W := hW_cyclic
  obtain ⟨zeta0, hzeta0_zpowers⟩ :=
    (W.isCyclic_iff_exists_zpowers_eq_top).mp (inferInstance : IsCyclic W)
  have hzeta0 : zeta0 ∈ W := by
    rw [← hzeta0_zpowers]
    exact Subgroup.mem_zpowers zeta0
  have hzeta0_ne : zeta0 ≠ 1 := by
    intro hzeta0_one
    apply hC2.W_ne_bot
    rw [← hzeta0_zpowers, hzeta0_one]
    simp
  have hzeta0_gen : Subgroup.closure ({zeta0} : Set G) = W := by
    rw [← Subgroup.zpowers_eq_closure]
    exact hzeta0_zpowers
  letI : Fintype OrbitIndex := Fintype.ofFinite OrbitIndex
  let orbitFin : OrbitIndex ≃ Fin n := by
    simpa [n, Nat.card_eq_fintype_card] using Fintype.equivFin OrbitIndex
  let repSharp (i : Fin n) : QuotientNontrivial :=
    Quotient.out (orbitFin.symm i)
  have hrepSharp_orbit (i : Fin n) :
      (Quotient.mk'' (repSharp i) : OrbitIndex) = orbitFin.symm i := by
    exact Quotient.out_eq' (orbitFin.symm i)
  let repQ (i : Fin n) : Q :=
    Classical.choose
      (QuotientGroup.mk'_surjective Q0Q (repSharp i : Q ⧸ Q0Q))
  have hrepQ_bar (i : Fin n) :
      QuotientGroup.mk' Q0Q (repQ i) = (repSharp i : Q ⧸ Q0Q) :=
    Classical.choose_spec
      (QuotientGroup.mk'_surjective Q0Q (repSharp i : Q ⧸ Q0Q))
  let omega0 (j : ℕ) : G :=
    if hj : 1 ≤ j ∧ j ≤ n then
      (repQ ⟨j - 1, by omega⟩ : G)
    else 1
  have homega0_valid : ∀ j : ℕ, 1 ≤ j → j ≤ n →
      omega0 j ∈ Q ∧ omega0 j ∉ Q0 := by
    intro j hj_one hj_n
    let i : Fin n := ⟨j - 1, by omega⟩
    have homega : omega0 j = (repQ i : G) := by
      simp [omega0, i, hj_one, hj_n]
    rw [homega]
    refine ⟨(repQ i).property, ?_⟩
    intro hQ0
    apply (repSharp i).property
    rw [← hrepQ_bar i]
    exact (QuotientGroup.eq_one_iff (repQ i)).2 hQ0
  have horbit_complete : ∀ x : G, x ∈ Q → x ∉ Q0 →
      ∃ j : ℕ, 1 ≤ j ∧ j ≤ n ∧
        ∃ d q0 : G, d ∈ K ⊔ W ∧ q0 ∈ Q0 ∧
          x = rightConjugateElem (omega0 j) d * q0 := by
    intro x hxQ hxQ0
    let xQ : Q := ⟨x, hxQ⟩
    let xbar : QuotientNontrivial :=
      ⟨QuotientGroup.mk' Q0Q xQ, by
        intro hone
        exact hxQ0 ((QuotientGroup.eq_one_iff xQ).1 hone)⟩
    let i : Fin n := orbitFin (Quotient.mk'' xbar)
    let j : ℕ := (i : ℕ) + 1
    have hj_one : 1 ≤ j := by omega
    have hj_n : j ≤ n := by
      change (i : ℕ) + 1 ≤ n
      omega
    have horbit_eq :
        (Quotient.mk'' (repSharp i) : OrbitIndex) = Quotient.mk'' xbar := by
      calc
        (Quotient.mk'' (repSharp i) : OrbitIndex) = orbitFin.symm i :=
          hrepSharp_orbit i
        _ = Quotient.mk'' xbar := by simp [i]
    have hrel : repSharp i ∈
        MulAction.orbit (K ⊔ W : Subgroup G) xbar :=
      MulAction.orbitRel_apply.mp (Quotient.eq''.mp horbit_eq)
    rcases hrel with ⟨d, hd⟩
    have hd' : d • xbar = repSharp i := hd
    have hxbar : xbar = d⁻¹ • repSharp i := by
      calc
        xbar = d⁻¹ • (d • xbar) := by simp
        _ = d⁻¹ • repSharp i := by rw [hd']
    let conjugateQ : Q := d⁻¹ • repQ i
    have hquot : QuotientGroup.mk' Q0Q xQ =
        QuotientGroup.mk' Q0Q conjugateQ := by
      have hxbar_val := congrArg Subtype.val hxbar
      calc
        QuotientGroup.mk' Q0Q xQ =
            d⁻¹ • (repSharp i : Q ⧸ Q0Q) := hxbar_val
        _ = d⁻¹ • QuotientGroup.mk' Q0Q (repQ i) := by
          rw [hrepQ_bar i]
        _ = QuotientGroup.mk' Q0Q (d⁻¹ • repQ i) := rfl
    have hdiv : xQ / conjugateQ ∈ Q0Q :=
      (QuotientGroup.eq_iff_div_mem).1 hquot
    let q0 : G := ((xQ / conjugateQ : Q) : G)
    have hq0 : q0 ∈ Q0 := hdiv
    have hcomm : q0 * (conjugateQ : G) = (conjugateQ : G) * q0 :=
      hQ0_commutes_Q q0 hq0 (conjugateQ : G) conjugateQ.property
    have hconjugate : (conjugateQ : G) =
        rightConjugateElem (omega0 j) (d : G) := by
      rw [show (conjugateQ : G) =
          (d⁻¹ : (K ⊔ W : Subgroup G)) * (repQ i : Q) *
              (d⁻¹ : (K ⊔ W : Subgroup G))⁻¹ from
        hKW_smul_coe d⁻¹ (repQ i)]
      have homega : omega0 j = (repQ i : G) := by
        simp [omega0, j, i, hj_one, hj_n]
      rw [homega]
      simp [rightConjugateElem, mul_assoc]
    refine ⟨j, hj_one, hj_n, (d : G), q0, ?_, hq0, ?_⟩
    · exact d.property
    · calc
        x = (xQ : G) := rfl
        _ = (conjugateQ : G) * q0 := by
          symm
          calc
            (conjugateQ : G) * q0 = q0 * (conjugateQ : G) := hcomm.symm
            _ = (xQ : G) := by simp [q0, div_eq_mul_inv, mul_assoc]
        _ = rightConjugateElem (omega0 j) (d : G) * q0 := by
          rw [hconjugate]
  have horbit_distinct : ∀ j k : ℕ,
      1 ≤ j → j ≤ n → 1 ≤ k → k ≤ n →
      (∃ d q0 : G, d ∈ K ⊔ W ∧ q0 ∈ Q0 ∧
        omega0 j = rightConjugateElem (omega0 k) d * q0) → j = k := by
    intro j k hj_one hj_n hk_one hk_n horbit
    rcases horbit with ⟨d, q0, hdKW, hq0, homega⟩
    let ij : Fin n := ⟨j - 1, by omega⟩
    let ik : Fin n := ⟨k - 1, by omega⟩
    let dKW : (K ⊔ W : Subgroup G) := ⟨d, hdKW⟩
    let q0Q : Q := ⟨q0, hsection3.section2.Q0_le_Q hq0⟩
    let conjugateQ : Q := dKW⁻¹ • repQ ik
    have homega_j : omega0 j = (repQ ij : G) := by
      simp [omega0, ij, hj_one, hj_n]
    have homega_k : omega0 k = (repQ ik : G) := by
      simp [omega0, ik, hk_one, hk_n]
    have hconjugate : (conjugateQ : G) =
        rightConjugateElem (omega0 k) d := by
      rw [show (conjugateQ : G) =
          (dKW⁻¹ : (K ⊔ W : Subgroup G)) * (repQ ik : Q) *
              (dKW⁻¹ : (K ⊔ W : Subgroup G))⁻¹ from
        hKW_smul_coe dKW⁻¹ (repQ ik), homega_k]
      simp [dKW, rightConjugateElem, mul_assoc]
    have hrep_eq : (repQ ij : G) = (conjugateQ : G) * q0 := by
      simpa [homega_j, hconjugate] using homega
    have hcomm : q0 * (conjugateQ : G) = (conjugateQ : G) * q0 :=
      hQ0_commutes_Q q0 hq0 (conjugateQ : G) conjugateQ.property
    have hdiv : repQ ij / conjugateQ ∈ Q0Q := by
      change ((repQ ij / conjugateQ : Q) : G) ∈ Q0
      rw [Subgroup.coe_div, hrep_eq, ← hcomm]
      simpa [div_eq_mul_inv, mul_assoc] using hq0
    have hbar : QuotientGroup.mk' Q0Q (repQ ij) =
        QuotientGroup.mk' Q0Q conjugateQ :=
      (QuotientGroup.eq_iff_div_mem).2 hdiv
    have hbar' : (repSharp ij : Q ⧸ Q0Q) =
        dKW⁻¹ • (repSharp ik : Q ⧸ Q0Q) := by
      calc
        _ = QuotientGroup.mk' Q0Q (repQ ij) := (hrepQ_bar ij).symm
        _ = QuotientGroup.mk' Q0Q conjugateQ := hbar
        _ = QuotientGroup.mk' Q0Q (dKW⁻¹ • repQ ik) := rfl
        _ = dKW⁻¹ • QuotientGroup.mk' Q0Q (repQ ik) := rfl
        _ = dKW⁻¹ • (repSharp ik : Q ⧸ Q0Q) := by
          rw [hrepQ_bar ik]
    have horbit_indices : (Quotient.mk'' (repSharp ij) : OrbitIndex) =
        Quotient.mk'' (repSharp ik) := by
      apply Quotient.sound
      apply MulAction.orbitRel_apply.mpr
      exact ⟨dKW⁻¹, Subtype.ext hbar'.symm⟩
    have hij : ij = ik := by
      apply orbitFin.symm.injective
      calc
        orbitFin.symm ij = Quotient.mk'' (repSharp ij) :=
          (hrepSharp_orbit ij).symm
        _ = Quotient.mk'' (repSharp ik) := horbit_indices
        _ = orbitFin.symm ik := hrepSharp_orbit ik
    have hsub : j - 1 = k - 1 := congrArg Fin.val hij
    omega
  have horbit_representatives0 :
      (∀ j : ℕ, 1 ≤ j → j ≤ n → omega0 j ∈ Q ∧ omega0 j ∉ Q0) ∧
      (∀ x : G, x ∈ Q → x ∉ Q0 →
        ∃ j : ℕ, 1 ≤ j ∧ j ≤ n ∧
          ∃ d q0 : G, d ∈ K ⊔ W ∧ q0 ∈ Q0 ∧
            x = rightConjugateElem (omega0 j) d * q0) ∧
      (∀ j k : ℕ, 1 ≤ j → j ≤ n → 1 ≤ k → k ≤ n →
        (∃ d q0 : G, d ∈ K ⊔ W ∧ q0 ∈ Q0 ∧
          omega0 j = rightConjugateElem (omega0 k) d * q0) → j = k) :=
    ⟨homega0_valid, horbit_complete, horbit_distinct⟩
  have hclaim9 :=
    PFchapter4section2.claim_9 H D Q K V W Q0 S Q1 (K ⊔ W)
      t s zeta0 f g h omega0 (Nat.card W) n hsection3 hC1 hC2
      hA1.two_transitive hA1.point_stabilizer hA1.involution_t
      hA1.t_not_mem_H hA1.D_eq hA1.Q_normal_in_H hA1.Q_disjoint_D
      hA1.Q_sup_D hf_mem hg_mem hh_mem hcanonical_eq rfl hzeta0 hzeta0_ne
      hzeta0_gen rfl hn horbit_representatives0
  let ValidIndex := {i : ℕ // 1 ≤ i ∧ i ≤ n}
  have hclaim9_valid (i : ValidIndex) :=
    hclaim9 (i : ℕ) i.property.1 i.property.2
  let normalizedOmega (i : ValidIndex) : G :=
    Classical.choose (hclaim9_valid i)
  let normalizedY (i : ValidIndex) : G :=
    Classical.choose (Classical.choose_spec (hclaim9_valid i))
  have hnormalized_spec (i : ValidIndex) :
      normalizedOmega i ∈ Q ∧ normalizedOmega i ∉ Q0 ∧
        normalizedY i ∈ Q0 ∧ normalizedY i ≠ 1 ∧
          (∃ d q0 : G, d ∈ K ⊔ W ∧ q0 ∈ Q0 ∧
            normalizedOmega i =
              rightConjugateElem (omega0 (i : ℕ)) d * q0) ∧
            f (normalizedOmega i) =
              rightConjugateElem (normalizedOmega i * normalizedY i) zeta0 := by
    exact Classical.choose_spec (Classical.choose_spec (hclaim9_valid i))
  let omega (j : ℕ) : G :=
    if hj : 1 ≤ j ∧ j ≤ n then normalizedOmega ⟨j, hj⟩ else 1
  have homega_eq (i : ValidIndex) :
      omega (i : ℕ) = normalizedOmega i := by
    simp [omega, i.property]
  have hQ0_conj_D : ∀ q a : G, q ∈ Q0 → a ∈ D →
      rightConjugateElem q a ∈ Q0 := by
    intro q a hq ha
    let d : D := ⟨a⁻¹, D.inv_mem ha⟩
    have hstable := hQ0_stable_D d ⟨q, hq⟩
    simpa [d] using hstable
  let SameOrbit (x y : G) : Prop :=
    ∃ d q0 : G, d ∈ K ⊔ W ∧ q0 ∈ Q0 ∧
      x = rightConjugateElem y d * q0
  have hsame_refl (x : G) : SameOrbit x x := by
    refine ⟨1, 1, (K ⊔ W).one_mem, Q0.one_mem, ?_⟩
    simp [rightConjugateElem]
  have hsame_symm : ∀ x y : G, SameOrbit x y → SameOrbit y x := by
    intro x y hxy
    rcases hxy with ⟨d, q0, hd, hq0, rfl⟩
    have hdD : d ∈ D := by
      exact hKW_le_D hd
    refine ⟨d⁻¹, (rightConjugateElem q0 d⁻¹)⁻¹,
      (K ⊔ W).inv_mem hd, Q0.inv_mem (hQ0_conj_D q0 d⁻¹ hq0 (D.inv_mem hdD)), ?_⟩
    simp [rightConjugateElem, mul_assoc]
  have hsame_trans : ∀ x y z : G,
      SameOrbit x y → SameOrbit y z → SameOrbit x z := by
    intro x y z hxy hyz
    rcases hxy with ⟨d, q0, hd, hq0, rfl⟩
    rcases hyz with ⟨e, r0, he, hr0, rfl⟩
    have hdD : d ∈ D := by
      exact hKW_le_D hd
    refine ⟨e * d, rightConjugateElem r0 d * q0,
      (K ⊔ W).mul_mem he hd,
      Q0.mul_mem (hQ0_conj_D r0 d hr0 hdD) hq0, ?_⟩
    simp [rightConjugateElem, mul_assoc]
  have hnormalized_orbit (i : ValidIndex) :
      SameOrbit (normalizedOmega i) (omega0 (i : ℕ)) := by
    rcases hnormalized_spec i with ⟨_, _, _, _, horbit, _⟩
    exact horbit
  have homega_valid : ∀ j : ℕ, 1 ≤ j → j ≤ n →
      omega j ∈ Q ∧ omega j ∉ Q0 := by
    intro j hj_one hj_n
    let i : ValidIndex := ⟨j, hj_one, hj_n⟩
    rw [show omega j = normalizedOmega i by simp [omega, i, hj_one, hj_n]]
    exact ⟨(hnormalized_spec i).1, (hnormalized_spec i).2.1⟩
  have homega_complete : ∀ x : G, x ∈ Q → x ∉ Q0 →
      ∃ j : ℕ, 1 ≤ j ∧ j ≤ n ∧
        ∃ d q0 : G, d ∈ K ⊔ W ∧ q0 ∈ Q0 ∧
          x = rightConjugateElem (omega j) d * q0 := by
    intro x hxQ hxQ0
    rcases horbit_complete x hxQ hxQ0 with
      ⟨j, hj_one, hj_n, d, q0, hd, hq0, hx⟩
    let i : ValidIndex := ⟨j, hj_one, hj_n⟩
    have hx_old : SameOrbit x (omega0 j) := ⟨d, q0, hd, hq0, hx⟩
    have hold_new : SameOrbit (omega0 j) (omega j) := by
      rw [show omega j = normalizedOmega i by simp [omega, i, hj_one, hj_n]]
      exact hsame_symm _ _ (hnormalized_orbit i)
    rcases hsame_trans x (omega0 j) (omega j) hx_old hold_new with
      ⟨e, r0, he, hr0, hfinal⟩
    exact ⟨j, hj_one, hj_n, e, r0, he, hr0, hfinal⟩
  have homega_distinct : ∀ j k : ℕ,
      1 ≤ j → j ≤ n → 1 ≤ k → k ≤ n →
      (∃ d q0 : G, d ∈ K ⊔ W ∧ q0 ∈ Q0 ∧
        omega j = rightConjugateElem (omega k) d * q0) → j = k := by
    intro j k hj_one hj_n hk_one hk_n hjk
    let ij : ValidIndex := ⟨j, hj_one, hj_n⟩
    let ik : ValidIndex := ⟨k, hk_one, hk_n⟩
    have holdj_newj : SameOrbit (omega0 j) (omega j) := by
      rw [show omega j = normalizedOmega ij by
        simp [omega, ij, hj_one, hj_n]]
      exact hsame_symm _ _ (hnormalized_orbit ij)
    have hnewj_newk : SameOrbit (omega j) (omega k) := hjk
    have hnewk_oldk : SameOrbit (omega k) (omega0 k) := by
      rw [show omega k = normalizedOmega ik by
        simp [omega, ik, hk_one, hk_n]]
      exact hnormalized_orbit ik
    have holdj_oldk : SameOrbit (omega0 j) (omega0 k) :=
      hsame_trans _ _ _ (hsame_trans _ _ _ holdj_newj hnewj_newk) hnewk_oldk
    exact horbit_distinct j k hj_one hj_n hk_one hk_n holdj_oldk
  have horbit_representatives :
      (∀ j : ℕ, 1 ≤ j → j ≤ n → omega j ∈ Q ∧ omega j ∉ Q0) ∧
      (∀ x : G, x ∈ Q → x ∉ Q0 →
        ∃ j : ℕ, 1 ≤ j ∧ j ≤ n ∧
          ∃ d q0 : G, d ∈ K ⊔ W ∧ q0 ∈ Q0 ∧
            x = rightConjugateElem (omega j) d * q0) ∧
      (∀ j k : ℕ, 1 ≤ j → j ≤ n → 1 ≤ k → k ≤ n →
        (∃ d q0 : G, d ∈ K ⊔ W ∧ q0 ∈ Q0 ∧
          omega j = rightConjugateElem (omega k) d * q0) → j = k) :=
    ⟨homega_valid, homega_complete, homega_distinct⟩
  have hnormalized : ∀ i : ℕ, 1 ≤ i → i ≤ n →
      ∃ y : G, y ∈ Q0 ∧ y ≠ 1 ∧
        f (omega i) = rightConjugateElem (omega i * y) zeta0 := by
    intro i hi_one hi_n
    let ii : ValidIndex := ⟨i, hi_one, hi_n⟩
    refine ⟨normalizedY ii, (hnormalized_spec ii).2.2.1,
      (hnormalized_spec ii).2.2.2.1, ?_⟩
    rw [homega_eq ii]
    exact (hnormalized_spec ii).2.2.2.2.2
  obtain ⟨omegaChosen, zeta, i, hi_one, hi_n,
      homegaChosenQ, homegaChosenQ0, hzeta, hzeta_ne,
      hfomega, hhomega, homegaChosen_orbit⟩ :
      ∃ omegaChosen zeta : G, ∃ i : ℕ,
        1 ≤ i ∧ i ≤ n ∧ omegaChosen ∈ Q ∧ omegaChosen ∉ Q0 ∧
          zeta ∈ W ∧ zeta ≠ 1 ∧
            f omegaChosen = rightConjugateElem omegaChosen⁻¹ zeta ∧
              h omegaChosen ∈ W ∧ SameOrbit omegaChosen (omega i) := by
    rcases hroute with hfixed | hseed
    · have hD_fixed_point_free : ∀ d : G, d ∈ D → d ≠ 1 →
          ∀ x : G, x ∈ Q → x ∉ Q0 →
            rightConjugateElem x d * x⁻¹ ∉ Q0 := by
        rcases hfixed with hVW | hD_fixed_point_free
        · have hD_le_KW : D ≤ K ⊔ W := by
            intro d hdD
            obtain ⟨v, k, hvV, hkK, rfl⟩ :=
              PFchapter1section3.lemma_2_D_mem_decompose_VK
                H D Q K V W Q0 S Q1 t s d hsection3 hdD
            exact (K ⊔ W).mul_mem
              (Subgroup.mem_sup_right (by simpa [hVW] using hvV))
              (Subgroup.mem_sup_left hkK)
          intro d hdD hdne x hxQ hxQ0
          exact hKW_fixed_point_free d (hD_le_KW hdD) hdne x hxQ hxQ0
        · exact hD_fixed_point_free
      obtain ⟨i, hi_one, hi_n, hfomega, hhomega⟩ :=
        PFchapter4section2.proposition H D Q K V W Q0 S Q1 (K ⊔ W)
          t s zeta0 f g h omega n hsection3 hC1 hC2 hC3Section2 hQ_two
          hA1.two_transitive hA1.point_stabilizer hA1.involution_t
          hA1.t_not_mem_H hA1.D_eq hA1.Q_normal_in_H hA1.Q_disjoint_D
          hA1.Q_sup_D hf_mem hg_mem hh_mem hcanonical_eq rfl hzeta0 hzeta0_ne
          hzeta0_gen horbit_representatives hnormalized hD_fixed_point_free
      exact ⟨omega i, zeta0, i, hi_one, hi_n,
        (homega_valid i hi_one hi_n).1,
        (homega_valid i hi_one hi_n).2, hzeta0, hzeta0_ne,
        hfomega, hhomega, hsame_refl (omega i)⟩
    · rcases hseed with
        ⟨omegaChosen, zeta, homegaQ, homegaQ0, hzeta, hzeta_ne,
          hfomega, hhomega⟩
      obtain ⟨i, hi_one, hi_n, d, q0, hd, hq0, horbit⟩ :=
        homega_complete omegaChosen homegaQ homegaQ0
      exact ⟨omegaChosen, zeta, i, hi_one, hi_n, homegaQ, homegaQ0,
        hzeta, hzeta_ne, hfomega, hhomega, ⟨d, q0, hd, hq0, horbit⟩⟩
  have homegaChosen : omegaChosen ∈ Q ∧ omegaChosen ∉ Q0 :=
    ⟨homegaChosenQ, homegaChosenQ0⟩
  let omegaSeed (j : ℕ) : G := if j = i then omegaChosen else omega j
  have homegaSeed_i : omegaSeed i = omegaChosen := by
    simp [omegaSeed]
  have homegaSeed_valid : ∀ j : ℕ, 1 ≤ j → j ≤ n →
      omegaSeed j ∈ Q ∧ omegaSeed j ∉ Q0 := by
    intro j hj_one hj_n
    by_cases hji : j = i
    · subst j
      simpa [homegaSeed_i] using homegaChosen
    · simpa [omegaSeed, hji] using homega_valid j hj_one hj_n
  have hold_to_seed : ∀ j : ℕ, 1 ≤ j → j ≤ n →
      SameOrbit (omega j) (omegaSeed j) := by
    intro j hj_one hj_n
    by_cases hji : j = i
    · subst j
      rw [homegaSeed_i]
      exact hsame_symm _ _ homegaChosen_orbit
    · simpa [omegaSeed, hji] using hsame_refl (omega j)
  have hseed_to_old : ∀ j : ℕ, 1 ≤ j → j ≤ n →
      SameOrbit (omegaSeed j) (omega j) := by
    intro j hj_one hj_n
    exact hsame_symm _ _ (hold_to_seed j hj_one hj_n)
  have homegaSeed_complete : ∀ x : G, x ∈ Q → x ∉ Q0 →
      ∃ j : ℕ, 1 ≤ j ∧ j ≤ n ∧
        ∃ d q0 : G, d ∈ K ⊔ W ∧ q0 ∈ Q0 ∧
          x = rightConjugateElem (omegaSeed j) d * q0 := by
    intro x hxQ hxQ0
    obtain ⟨j, hj_one, hj_n, d, q0, hd, hq0, hx⟩ :=
      homega_complete x hxQ hxQ0
    have hxold : SameOrbit x (omega j) := ⟨d, q0, hd, hq0, hx⟩
    rcases hsame_trans x (omega j) (omegaSeed j) hxold
        (hold_to_seed j hj_one hj_n) with
      ⟨e, r0, he, hr0, hfinal⟩
    exact ⟨j, hj_one, hj_n, e, r0, he, hr0, hfinal⟩
  have homegaSeed_distinct : ∀ j k : ℕ,
      1 ≤ j → j ≤ n → 1 ≤ k → k ≤ n →
      (∃ d q0 : G, d ∈ K ⊔ W ∧ q0 ∈ Q0 ∧
        omegaSeed j = rightConjugateElem (omegaSeed k) d * q0) → j = k := by
    intro j k hj_one hj_n hk_one hk_n hjk
    have hseed : SameOrbit (omegaSeed j) (omegaSeed k) := hjk
    have hold : SameOrbit (omega j) (omega k) :=
      hsame_trans (omega j) (omegaSeed j) (omega k)
        (hold_to_seed j hj_one hj_n)
        (hsame_trans (omegaSeed j) (omegaSeed k) (omega k) hseed
          (hseed_to_old k hk_one hk_n))
    exact homega_distinct j k hj_one hj_n hk_one hk_n hold
  have horbit_representativesSeed :
      (∀ j : ℕ, 1 ≤ j → j ≤ n →
        omegaSeed j ∈ Q ∧ omegaSeed j ∉ Q0) ∧
      (∀ x : G, x ∈ Q → x ∉ Q0 →
        ∃ j : ℕ, 1 ≤ j ∧ j ≤ n ∧
          ∃ d q0 : G, d ∈ K ⊔ W ∧ q0 ∈ Q0 ∧
            x = rightConjugateElem (omegaSeed j) d * q0) ∧
      (∀ j k : ℕ, 1 ≤ j → j ≤ n → 1 ≤ k → k ≤ n →
        (∃ d q0 : G, d ∈ K ⊔ W ∧ q0 ∈ Q0 ∧
          omegaSeed j = rightConjugateElem (omegaSeed k) d * q0) → j = k) :=
    ⟨homegaSeed_valid, homegaSeed_complete, homegaSeed_distinct⟩
  have hmem_F_of_frobenius_fixed (y : E)
      (hy : y ^ Nat.card F = y) : y ∈ F := by
    letI : Fintype F := Fintype.ofFinite F
    let fr : E ≃ₐ[F] E := FiniteField.frobeniusAlgEquivOfAlgebraic F E
    have hyfr : fr y = y := by
      simpa [fr, Nat.card_eq_fintype_card] using hy
    have hall_fixed : ∀ tau : E ≃ₐ[F] E, tau y = y := by
      intro tau
      obtain ⟨j, hj⟩ :=
        (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F E).2 tau
      have hjlt : (j : ℕ) < 2 := by
        have hjlt' : (j : ℕ) < Module.finrank F E := j.isLt
        omega
      have hjcases : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by omega
      rcases hjcases with hjzero | hjone
      · rw [← hj]
        change (FiniteField.frobeniusAlgEquivOfAlgebraic F E ^ (j : ℕ)) y = y
        rw [hjzero]
        simp
      · rw [← hj]
        change (FiniteField.frobeniusAlgEquivOfAlgebraic F E ^ (j : ℕ)) y = y
        rw [hjone, pow_one]
        exact hyfr
    have hyrange : y ∈ Set.range (algebraMap F E) :=
      (IsGalois.mem_range_algebraMap_iff_fixed y).2 hall_fixed
    rcases hyrange with ⟨a, ha⟩
    rw [← ha]
    exact a.property
  have htrace_zero_mem_F (htheta : theta = 1) (y : E)
      (hy : y + sigma y = 0) : y ∈ F := by
    have hyadd : y + y = 0 := by
      exact CharTwo.add_self_eq_zero y
    have hsigmay : sigma y = y := by
      calc
        sigma y = -y := eq_neg_of_add_eq_zero_right hy
        _ = y := (eq_neg_of_add_eq_zero_left hyadd).symm
    letI : Fintype F := Fintype.ofFinite F
    let fr : E ≃ₐ[F] E := FiniteField.frobeniusAlgEquivOfAlgebraic F E
    have hfrfixed : fr y = y := by
      calc
        fr y = y ^ Nat.card F := by
          simp [fr, Nat.card_eq_fintype_card]
        _ = sigma y := (hsigmaFrob htheta y).symm
        _ = y := hsigmay
    have hall_fixed : ∀ tau : E ≃ₐ[F] E, tau y = y := by
      intro tau
      obtain ⟨j, hj⟩ :=
        (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F E).2 tau
      have hjlt : (j : ℕ) < 2 := by
        have hjlt' : (j : ℕ) < Module.finrank F E := j.isLt
        omega
      have hjcases : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by omega
      rcases hjcases with hjzero | hjone
      · rw [← hj]
        change (FiniteField.frobeniusAlgEquivOfAlgebraic F E ^ (j : ℕ)) y = y
        rw [hjzero]
        simp
      · rw [← hj]
        change (FiniteField.frobeniusAlgEquivOfAlgebraic F E ^ (j : ℕ)) y = y
        rw [hjone, pow_one]
        exact hfrfixed
    have hyrange : y ∈ Set.range (algebraMap F E) :=
      (IsGalois.mem_range_algebraMap_iff_fixed y).2 hall_fixed
    rcases hyrange with ⟨a, ha⟩
    rw [← ha]
    exact a.property
  let ValidPair (x y : E) : Prop :=
    (theta = 1 ∧ y + sigma y = x * sigma x) ∨
      (theta ≠ 1 ∧ y ∈ F)
  let mkS (x y : E) (hxy : ValidPair x y) : S :=
    sIso.symm (coord.symm ⟨(x, y), hxy⟩)
  have hmkS_coord (x y : E) (hxy : ValidPair x y) :
      coordPair (mkS x y hxy) = (x, y) := by
    simp [coordPair, mkS]
  have ht_not_mem_Q : t ∉ Q := fun htQ =>
    hA1.t_not_mem_H (hA1.Q_le_H htQ)
  let mk (x y : E) : G :=
    if hxy : ValidPair x y then (mkS x y hxy : G) else t
  have hmk_of_valid (x y : E) (hxy : ValidPair x y) :
      mk x y = (mkS x y hxy : G) := by
    simp [mk, hxy]
  have hmk_mem_Q : ∀ x y : E, ValidPair x y → mk x y ∈ Q := by
    intro x y hxy
    rw [hmk_of_valid x y hxy, ← hSQ]
    exact (mkS x y hxy).property
  have hmk_injective : ∀ x y : E, ValidPair x y →
      ∀ x' y' : E, ValidPair x' y' →
        mk x y = mk x' y' → x = x' ∧ y = y' := by
    intro x y hxy x' y' hxy' heq
    have heq' : (mkS x y hxy : G) = (mkS x' y' hxy' : G) := by
      calc
        (mkS x y hxy : G) = mk x y := (hmk_of_valid x y hxy).symm
        _ = mk x' y' := heq
        _ = (mkS x' y' hxy' : G) := hmk_of_valid x' y' hxy'
    have hmkS : mkS x y hxy = mkS x' y' hxy' := Subtype.ext heq'
    have hcoord :
        (⟨(x, y), hxy⟩ : {p : E × E // ValidPair p.1 p.2}) =
          ⟨(x', y'), hxy'⟩ := by
      apply coord.symm.injective
      apply sIso.symm.injective
      exact hmkS
    have hpair : (x, y) = (x', y') := congrArg Subtype.val hcoord
    exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
  have hrho_coordinates : ∀ rho : G, rho ∈ Q →
      ∃ x y : E, ValidPair x y ∧ rho = mk x y := by
    intro rho hrhoQ
    let rhoS : S := ⟨rho, by rwa [hSQ]⟩
    let p := coord (sIso rhoS)
    refine ⟨(p : E × E).1, (p : E × E).2, p.property, ?_⟩
    rw [hmk_of_valid _ _ p.property]
    change (rhoS : G) = (mkS (p : E × E).1 (p : E × E).2 p.property : G)
    apply congrArg Subtype.val
    simp [mkS, p]
  let bar : G → E := fun x =>
    if hx : x ∈ Q then
      (coordPair (⟨x, by simpa [hSQ] using hx⟩ : S)).1
    else 0
  let kcoord : G → E := fun a =>
    if ha : a ∈ K ⊔ W then
      (((kwIso (⟨a, ha⟩ : (K ⊔ W : Subgroup G)) :
          (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E)
    else 0
  have hbar_of_mem_Q (x : G) (hx : x ∈ Q) :
      bar x = (coordPair (⟨x, by simpa [hSQ] using hx⟩ : S)).1 := by
    simp [bar, hx]
  have hkcoord_of_mem_KW (a : G) (ha : a ∈ K ⊔ W) :
      kcoord a =
        (((kwIso (⟨a, ha⟩ : (K ⊔ W : Subgroup G)) :
            (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) := by
    simp [kcoord, ha]
  have hbar_mul : ∀ x : G, x ∈ Q → ∀ y : G, y ∈ Q →
      bar (x * y) = bar x + bar y := by
    intro x hx y hy
    let xS : S := ⟨x, by simpa [hSQ] using hx⟩
    let yS : S := ⟨y, by simpa [hSQ] using hy⟩
    have hfirst := congrArg Prod.fst (hcoordPair_mul xS yS)
    simpa [bar, hx, hy, Q.mul_mem hx hy, xS, yS] using hfirst
  have hbar_Q0 : ∀ x : G, x ∈ Q → (bar x = 0 ↔ x ∈ Q0) := by
    intro x hx
    let xS : S := ⟨x, by simpa [hSQ] using hx⟩
    rw [hbar_of_mem_Q x hx]
    constructor
    · intro hzero
      simpa [xS] using hmem_Q0_of_coordPair_zero xS hzero
    · intro hxQ0
      exact hcoordPair_zero_of_mem_Q0 xS hxQ0
  have hQ_conj_KW : ∀ x : G, x ∈ Q → ∀ d : G, d ∈ K ⊔ W →
      rightConjugateElem x d ∈ Q := by
    intro x hx d hd
    exact PFchapter4section1.h6_rightConjugateElem_mem_Q_of_mem_M
      (PFchapter4section1.rankOneSplit_Q_le_M hA1.Q_sup_D)
      hA1.Q_normal_in_H hx (hA1.D_le_H (hKW_le_D hd))
  have hbar_conj : ∀ x : G, x ∈ Q → ∀ d : G, d ∈ K ⊔ W →
      bar (rightConjugateElem x d) = kcoord d * bar x := by
    intro x hx d hd
    let xS : S := ⟨x, by simpa [hSQ] using hx⟩
    let dKW : (K ⊔ W : Subgroup G) := ⟨d, hd⟩
    let rS : S :=
      ⟨rightConjugateElem x d,
        by simpa [hSQ] using hQ_conj_KW x hx d hd⟩
    have hrS : rS = conjS xS dKW := by
      apply Subtype.ext
      exact (hconjS_coe xS dKW).symm
    have hscale := hconjS_first xS dKW
    rw [hbar_of_mem_Q _ (hQ_conj_KW x hx d hd), hbar_of_mem_Q x hx,
      hkcoord_of_mem_KW d hd]
    change (coordPair rS).1 =
      (((kwIso dKW : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) *
        (coordPair xS).1
    rw [hrS]
    exact hscale
  have hkcoord_mul : ∀ x : G, x ∈ K ⊔ W → ∀ y : G, y ∈ K ⊔ W →
      kcoord (x * y) = kcoord x * kcoord y := by
    intro x hx y hy
    let xKW : (K ⊔ W : Subgroup G) := ⟨x, hx⟩
    let yKW : (K ⊔ W : Subgroup G) := ⟨y, hy⟩
    have hmap := congrArg
      (fun a : (K1 ⊔ W1 : Subgroup Eˣ) => (((a : Eˣ) : E)))
      (kwIso.map_mul xKW yKW)
    simpa [kcoord, hx, hy, (K ⊔ W).mul_mem hx hy, xKW, yKW] using hmap
  have hkcoord_inv : ∀ x : G, x ∈ K ⊔ W →
      kcoord x⁻¹ = (kcoord x)⁻¹ := by
    intro x hx
    let xKW : (K ⊔ W : Subgroup G) := ⟨x, hx⟩
    rw [hkcoord_of_mem_KW x⁻¹ ((K ⊔ W).inv_mem hx),
      hkcoord_of_mem_KW x hx]
    have hxinv :
        (⟨x⁻¹, (K ⊔ W).inv_mem hx⟩ : (K ⊔ W : Subgroup G)) = xKW⁻¹ := by
      rfl
    rw [hxinv, map_inv]
    simp [xKW]
  have hkcoord_pow : ∀ x : G, x ∈ K ⊔ W → ∀ m : ℕ,
      kcoord (x ^ m) = kcoord x ^ m := by
    intro x hx m
    let xKW : (K ⊔ W : Subgroup G) := ⟨x, hx⟩
    rw [hkcoord_of_mem_KW (x ^ m) ((K ⊔ W).pow_mem hx m),
      hkcoord_of_mem_KW x hx]
    have hxpow :
        (⟨x ^ m, (K ⊔ W).pow_mem hx m⟩ : (K ⊔ W : Subgroup G)) =
          xKW ^ m := by
      rfl
    rw [hxpow, map_pow]
    rfl
  have hkcoord_ne_zero : ∀ x : G, x ∈ K ⊔ W → kcoord x ≠ 0 := by
    intro x hx
    simp [kcoord, hx]
  have hQ0_coordinates : ∀ y : E, mk 0 y ∈ Q0 ↔ y ∈ F := by
    intro y
    constructor
    · intro hmkQ0
      by_cases hvalid : ValidPair 0 y
      · rcases hvalid with hunitary | htwisted
        · exact htrace_zero_mem_F hunitary.1 y (by simpa using hunitary.2)
        · exact htwisted.2
      · have htQ0 : t ∈ Q0 := by
          simpa [mk, hvalid] using hmkQ0
        exact False.elim (ht_not_mem_Q (hsection3.section2.Q0_le_Q htQ0))
    · intro hyF
      have hvalid : ValidPair 0 y := by
        by_cases htheta : theta = 1
        · left
          refine ⟨htheta, ?_⟩
          have hsigmay : sigma y = y := by
            simpa [htheta] using hsigmaF ⟨y, hyF⟩
          rw [hsigmay]
          simp [CharTwo.add_self_eq_zero]
        · exact Or.inr ⟨htheta, hyF⟩
      rw [hmk_of_valid 0 y hvalid]
      apply hmem_Q0_of_coordPair_zero (mkS 0 y hvalid)
      rw [hmkS_coord]
  have hbar_mk (x y : E) (hxy : ValidPair x y) : bar (mk x y) = x := by
    rw [hbar_of_mem_Q _ (hmk_mem_Q x y hxy)]
    simpa [hmk_of_valid x y hxy] using
      congrArg Prod.fst (hmkS_coord x y hxy)
  have hkcoord_kOf (a : Fˣ) : kcoord (kOf a) = ((a : F) : E) := by
    rw [hkcoord_of_mem_KW (kOf a) (Subgroup.mem_sup_left (hkOf_mem a))]
    exact hkOf_coord a
  have hclaim2_bar : ∀ a : G, a ∈ K →
      bar (f (omegaChosen * rightConjugateElem s a)) =
        bar omegaChosen / (kcoord a ^ 2 + (kcoord zeta)⁻¹) :=
    PFchapter4section3.claim_2 H D Q K V W Q0 S Q1 t s omegaChosen zeta
      bar kcoord f g h hsection3 hC1 hC2 hA1.two_transitive
      hA1.point_stabilizer hA1.involution_t hA1.t_not_mem_H hA1.D_eq
      hA1.Q_normal_in_H hA1.Q_disjoint_D hA1.Q_sup_D hf_mem hg_mem
      hh_mem hcanonical_eq homegaChosen.1 homegaChosen.2 hzeta hzeta_ne
      hfomega hhomega hW_fixed_point_free hbar_mul hbar_Q0 hbar_conj
      hkcoord_mul hkcoord_inv hkcoord_pow hkcoord_ne_zero
  let omegaS : S :=
    ⟨omegaChosen, by simpa [hSQ] using homegaChosen.1⟩
  have homega_sq_first : (coordPair (omegaS ^ 2)).1 = 0 := by
    rw [pow_two, hcoordPair_mul]
    exact CharTwo.add_self_eq_zero (coordPair omegaS).1
  have homega_sq_mem_Q0 : omegaChosen ^ 2 ∈ Q0 := by
    have hsquare := hmem_Q0_of_coordPair_zero (omegaS ^ 2) homega_sq_first
    simpa [omegaS] using hsquare
  obtain ⟨alpha, halpha_center⟩ :=
    hcenter_surjective (omegaChosen ^ 2) homega_sq_mem_Q0
  have homega_inv_shape : omegaChosen⁻¹ = omegaChosen * center alpha := by
    apply inv_eq_of_mul_eq_one_right
    calc
      omegaChosen * (omegaChosen * center alpha) =
          omegaChosen ^ 2 * center alpha := by rw [pow_two, mul_assoc]
      _ = center alpha * center alpha := by rw [← halpha_center]
      _ = 1 := by simpa [pow_two] using hcenter_sq alpha
  have homega_bar_ne_zero : bar omegaChosen ≠ 0 := by
    intro hzero
    exact homegaChosen.2 ((hbar_Q0 omegaChosen homegaChosen.1).1 hzero)
  let zetaKW : (K ⊔ W : Subgroup G) :=
    ⟨zeta, Subgroup.mem_sup_right hzeta⟩
  let zetaUnit : Eˣ :=
    ((kwIso zetaKW : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ)
  have hzetaUnit_W1 : zetaUnit ∈ W1 := by
    simpa [zetaUnit, zetaKW] using hkwIso_mem_W1 zeta hzeta
  have hzeta_coord : kcoord zeta = (zetaUnit : E) := by
    simpa [zetaUnit, zetaKW] using
      hkcoord_of_mem_KW zeta (Subgroup.mem_sup_right hzeta)
  have hzeta_coord_sigma : sigma (kcoord zeta) = (kcoord zeta)⁻¹ := by
    rw [hzeta_coord]
    exact hW1inv zetaUnit hzetaUnit_W1
  have hzeta_coord_norm :
      kcoord zeta ^ (Nat.card F + 1) = 1 := by
    rw [hzeta_coord]
    exact hW1norm zetaUnit hzetaUnit_W1
  have hzeta_coord_frobenius :
      kcoord zeta ^ Nat.card F = (kcoord zeta)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa [pow_succ] using hzeta_coord_norm
  letI : Fintype F := Fintype.ofFinite F
  let fr : E ≃ₐ[F] E := FiniteField.frobeniusAlgEquivOfAlgebraic F E
  have hfr_zeta : fr (kcoord zeta) = (kcoord zeta)⁻¹ := by
    calc
      fr (kcoord zeta) = kcoord zeta ^ Nat.card F := by
        simp [fr, Nat.card_eq_fintype_card]
      _ = (kcoord zeta)⁻¹ := hzeta_coord_frobenius
  have hbeta_pow :
      (kcoord zeta + (kcoord zeta)⁻¹) ^ Nat.card F =
        kcoord zeta + (kcoord zeta)⁻¹ := by
    calc
      (kcoord zeta + (kcoord zeta)⁻¹) ^ Nat.card F =
          fr (kcoord zeta + (kcoord zeta)⁻¹) := by
        simp [fr, Nat.card_eq_fintype_card]
      _ = fr (kcoord zeta) + fr ((kcoord zeta)⁻¹) := map_add _ _ _
      _ = (kcoord zeta)⁻¹ + ((kcoord zeta)⁻¹)⁻¹ := by
        rw [map_inv₀]
        exact congrArg (fun x : E => x + x⁻¹) hfr_zeta
      _ = kcoord zeta + (kcoord zeta)⁻¹ := by
        rw [inv_inv, add_comm]
  have hbeta_mem_F : kcoord zeta + (kcoord zeta)⁻¹ ∈ F :=
    hmem_F_of_frobenius_fixed _ hbeta_pow
  let beta : F := ⟨kcoord zeta + (kcoord zeta)⁻¹, hbeta_mem_F⟩
  have htheta_beta : theta beta = beta := by
    apply Subtype.ext
    calc
      ((theta beta : F) : E) = sigma (beta : E) := (hsigmaF beta).symm
      _ = sigma (kcoord zeta + (kcoord zeta)⁻¹) := rfl
      _ = sigma (kcoord zeta) + sigma ((kcoord zeta)⁻¹) := map_add _ _ _
      _ = (kcoord zeta)⁻¹ + ((kcoord zeta)⁻¹)⁻¹ := by
        rw [map_inv₀]
        exact congrArg (fun x : E => x + x⁻¹) hzeta_coord_sigma
      _ = kcoord zeta + (kcoord zeta)⁻¹ := by
        rw [inv_inv, add_comm]
      _ = (beta : E) := rfl
  have hzeta_coord_ne_one : kcoord zeta ≠ 1 := by
    intro hzeta_one
    apply hzeta_ne
    have himage : kwIso zetaKW = 1 := by
      apply Subtype.ext
      apply Units.ext
      exact hzeta_coord.symm.trans hzeta_one
    have hpreimage : zetaKW = 1 := by
      apply kwIso.injective
      simpa using himage
    exact congrArg Subtype.val hpreimage
  have hbeta_ne_zero : beta ≠ 0 := by
    intro hbeta
    have hsum : kcoord zeta + (kcoord zeta)⁻¹ = 0 := by
      exact congrArg Subtype.val hbeta
    have heq_inv : kcoord zeta = (kcoord zeta)⁻¹ :=
      CharTwo.add_eq_zero.mp hsum
    have hsq : kcoord zeta ^ 2 = 1 := by
      calc
        kcoord zeta ^ 2 = kcoord zeta * kcoord zeta := pow_two _
        _ = (kcoord zeta)⁻¹ * kcoord zeta :=
          congrArg (fun x : E => x * kcoord zeta) heq_inv
        _ = 1 :=
          inv_mul_cancel₀ (hkcoord_ne_zero zeta (Subgroup.mem_sup_right hzeta))
    have hadd_sq : (kcoord zeta + 1) ^ 2 = 0 := by
      rw [CharTwo.add_sq, hsq, one_pow, CharTwo.add_self_eq_zero]
    apply hzeta_coord_ne_one
    exact CharTwo.add_eq_zero.mp (eq_zero_of_pow_eq_zero hadd_sq)
  let normEquiv : F ≃ F :=
    Equiv.ofBijective (fun x : F => x * theta x)
      (PFchapter4section2.norm_bijective_of_odd_order theta hthetaOdd)
  let tau : F → F := normEquiv.symm
  have hnorm_tau : ∀ x : F, tau x * theta (tau x) = x := by
    intro x
    exact normEquiv.apply_symm_apply x
  have htau_ne_zero : ∀ x : F, x ≠ 0 → tau x ≠ 0 := by
    intro x hx htau
    apply hx
    rw [← hnorm_tau x, htau]
    simp
  have hs_conj_kOf (a : Fˣ) :
      rightConjugateElem s (kOf a) =
        center ((a : F) * theta (a : F)) := by
    rw [hs_center]
    simpa using
      hcenter_conj_K_exact (kOf a) (hkOf_mem a) a (hkOf_coord a) 1
  have hs_conj_kOf_inv (a : Fˣ) :
      rightConjugateElem s (kOf a)⁻¹ =
        center ((a : F)⁻¹ * theta ((a : F)⁻¹)) := by
    have ha_inv_mem : (kOf a)⁻¹ ∈ K := K.inv_mem (hkOf_mem a)
    have ha_inv_coord :
        (((kwIso
          (⟨(kOf a)⁻¹, Subgroup.mem_sup_left ha_inv_mem⟩ :
            (K ⊔ W : Subgroup G)) : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) =
          (((a⁻¹ : Fˣ) : F) : E) := by
      calc
        (((kwIso
          (⟨(kOf a)⁻¹, Subgroup.mem_sup_left ha_inv_mem⟩ :
            (K ⊔ W : Subgroup G)) : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) =
            kcoord (kOf a)⁻¹ :=
          (hkcoord_of_mem_KW (kOf a)⁻¹
            (Subgroup.mem_sup_left ha_inv_mem)).symm
        _ = (kcoord (kOf a))⁻¹ :=
          hkcoord_inv (kOf a) (Subgroup.mem_sup_left (hkOf_mem a))
        _ = ((((a : F) : E))⁻¹) := by rw [hkcoord_kOf]
        _ = (((a⁻¹ : Fˣ) : F) : E) := by simp
    rw [hs_center]
    simpa using
      hcenter_conj_K_exact (kOf a)⁻¹ ha_inv_mem a⁻¹ ha_inv_coord 1
  have hs_conj_kOf_mem_Q0 (a : Fˣ) :
      rightConjugateElem s (kOf a) ∈ Q0 := by
    rw [hs_conj_kOf]
    exact hcenter_mem_Q0 _
  have hs_conj_kOf_inv_mem_Q0 (a : Fˣ) :
      rightConjugateElem s (kOf a)⁻¹ ∈ Q0 := by
    rw [hs_conj_kOf_inv]
    exact hcenter_mem_Q0 _
  have homega_mul_s_mem_Q (a : Fˣ) :
      omegaChosen * rightConjugateElem s (kOf a) ∈ Q :=
    Q.mul_mem homegaChosen.1
      (hsection3.section2.Q0_le_Q (hs_conj_kOf_mem_Q0 a))
  have homega_mul_s_ne_one (a : Fˣ) :
      omegaChosen * rightConjugateElem s (kOf a) ≠ 1 := by
    intro hprod
    apply homegaChosen.2
    have homega_eq :
        omegaChosen = (rightConjugateElem s (kOf a))⁻¹ :=
      eq_inv_of_mul_eq_one_left hprod
    rw [homega_eq]
    exact Q0.inv_mem (hs_conj_kOf_mem_Q0 a)
  have hzeta_mem_peterfalviV : zeta ∈ peterfalviV D t := by
    rw [← hsection3.section2.V_eq]
    exact hsection3.section2.W_le_V hzeta
  have hzeta_fixed_t : rightConjugateElem zeta t = zeta := by
    have hcomm : Commute zeta t :=
      Subgroup.mem_centralizer_singleton_iff.mp hzeta_mem_peterfalviV.2
    simp [rightConjugateElem, hcomm.eq, mul_assoc]
  have hinner_identity (a b : Fˣ)
      (hnorm :
        (b : F) * theta (b : F) =
          alpha + (a : F)⁻¹ * theta ((a : F)⁻¹)) :
      f omegaChosen * rightConjugateElem s (kOf a)⁻¹ =
        rightConjugateElem
          (omegaChosen * rightConjugateElem s (kOf b)) zeta := by
    have homega_center_conj :
        rightConjugateElem (omegaChosen * center alpha) zeta =
          rightConjugateElem omegaChosen zeta * center alpha := by
      calc
        rightConjugateElem (omegaChosen * center alpha) zeta =
            rightConjugateElem omegaChosen zeta *
              rightConjugateElem (center alpha) zeta := by
          simp [rightConjugateElem, mul_assoc]
        _ = rightConjugateElem omegaChosen zeta * center alpha := by
          rw [hcenter_conj_W zeta hzeta alpha]
    have hprod_conj :
        rightConjugateElem
            (omegaChosen * rightConjugateElem s (kOf b)) zeta =
          rightConjugateElem omegaChosen zeta *
            rightConjugateElem s (kOf b) := by
      calc
        rightConjugateElem
            (omegaChosen * rightConjugateElem s (kOf b)) zeta =
          rightConjugateElem omegaChosen zeta *
              rightConjugateElem (rightConjugateElem s (kOf b)) zeta := by
            simp [rightConjugateElem, mul_assoc]
        _ = rightConjugateElem omegaChosen zeta *
            rightConjugateElem s (kOf b) := by
          rw [hs_conj_kOf b, hcenter_conj_W zeta hzeta]
    calc
      f omegaChosen * rightConjugateElem s (kOf a)⁻¹ =
          rightConjugateElem omegaChosen⁻¹ zeta *
            rightConjugateElem s (kOf a)⁻¹ := by rw [hfomega]
      _ = rightConjugateElem (omegaChosen * center alpha) zeta *
            rightConjugateElem s (kOf a)⁻¹ := by rw [homega_inv_shape]
      _ = (rightConjugateElem omegaChosen zeta * center alpha) *
            center ((a : F)⁻¹ * theta ((a : F)⁻¹)) := by
        rw [homega_center_conj, hs_conj_kOf_inv]
      _ = rightConjugateElem omegaChosen zeta *
            center (alpha + (a : F)⁻¹ * theta ((a : F)⁻¹)) := by
        rw [mul_assoc, ← hcenter_add]
      _ = rightConjugateElem omegaChosen zeta *
            center ((b : F) * theta (b : F)) := by rw [← hnorm]
      _ = rightConjugateElem omegaChosen zeta *
            rightConjugateElem s (kOf b) := by rw [hs_conj_kOf]
      _ = rightConjugateElem
          (omegaChosen * rightConjugateElem s (kOf b)) zeta := hprod_conj.symm
  have hf_conj_zeta (b : Fˣ) :
      f (rightConjugateElem
          (omegaChosen * rightConjugateElem s (kOf b)) zeta) =
        rightConjugateElem
          (f (omegaChosen * rightConjugateElem s (kOf b))) zeta := by
    have htransport := PFchapter4section1.claim_H3 H Q D t f g h
      hA1.two_transitive hA1.point_stabilizer hA1.involution_t
      hA1.t_not_mem_H hA1.D_eq hA1.Q_normal_in_H hA1.Q_disjoint_D
      hA1.Q_sup_D hf_mem hg_mem hh_mem hcanonical_eq
      (omegaChosen * rightConjugateElem s (kOf b)) zeta
      (homega_mul_s_mem_Q b) (homega_mul_s_ne_one b) (hW_le_D hzeta)
    simpa [hzeta_fixed_t] using htransport
  have hdenom_ne (a : Fˣ) :
      (((a : F) : E) ^ 2 + (kcoord zeta)⁻¹) ≠ 0 := by
    intro hdenom
    have hcoord_eq :
        ((a : F) : E) ^ 2 = (kcoord zeta)⁻¹ :=
      CharTwo.add_eq_zero.mp hdenom
    have ha_sq_mem : (kOf a) ^ 2 ∈ K := K.pow_mem (hkOf_mem a) 2
    have ha_sq_KW : (kOf a) ^ 2 ∈ K ⊔ W :=
      Subgroup.mem_sup_left ha_sq_mem
    have hzeta_inv_KW : zeta⁻¹ ∈ K ⊔ W :=
      (K ⊔ W).inv_mem (Subgroup.mem_sup_right hzeta)
    let aKW : (K ⊔ W : Subgroup G) := ⟨(kOf a) ^ 2, ha_sq_KW⟩
    let zetaInvKW : (K ⊔ W : Subgroup G) := ⟨zeta⁻¹, hzeta_inv_KW⟩
    have himage : kwIso aKW = kwIso zetaInvKW := by
      apply Subtype.ext
      apply Units.ext
      calc
        (((kwIso aKW : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) =
            kcoord ((kOf a) ^ 2) :=
          (hkcoord_of_mem_KW ((kOf a) ^ 2) ha_sq_KW).symm
        _ = kcoord (kOf a) ^ 2 :=
          hkcoord_pow (kOf a) (Subgroup.mem_sup_left (hkOf_mem a)) 2
        _ = ((a : F) : E) ^ 2 := by rw [hkcoord_kOf]
        _ = (kcoord zeta)⁻¹ := hcoord_eq
        _ = kcoord zeta⁻¹ :=
          (hkcoord_inv zeta (Subgroup.mem_sup_right hzeta)).symm
        _ = (((kwIso zetaInvKW : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) :=
          hkcoord_of_mem_KW zeta⁻¹ hzeta_inv_KW
    have hgroup_eq : (kOf a) ^ 2 = zeta⁻¹ :=
      congrArg Subtype.val (kwIso.injective himage)
    have hzeta_mem_K : zeta ∈ K := by
      have hzeta_inv_mem_K : zeta⁻¹ ∈ K := by
        rw [← hgroup_eq]
        exact ha_sq_mem
      simpa using K.inv_mem hzeta_inv_mem_K
    exact hzeta_ne (hK_inter_W zeta hzeta_mem_K hzeta)
  have hstar_units : ∀ a : Fˣ,
      alpha + (a : F)⁻¹ * theta ((a : F)⁻¹) ≠ 0 →
        alpha ^ 2 + beta ^ 2 +
          beta * ((a : F)⁻¹ ^ 2 + theta ((a : F)⁻¹ ^ 2)) = 0 := by
    intro a htarget
    let target : F := alpha + (a : F)⁻¹ * theta ((a : F)⁻¹)
    have htarget_ne : target ≠ 0 := by simpa [target] using htarget
    let b0 : F := tau target
    have hb0_ne : b0 ≠ 0 := htau_ne_zero target htarget_ne
    let b : Fˣ := Units.mk0 b0 hb0_ne
    have hnorm :
        (b : F) * theta (b : F) =
          alpha + (a : F)⁻¹ * theta ((a : F)⁻¹) := by
      change tau target * theta (tau target) = target
      exact hnorm_tau target
    have hsection2_eq := PFchapter4section2.claim_2
      H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
      hA1.two_transitive hA1.point_stabilizer hA1.involution_t
      hA1.t_not_mem_H hA1.D_eq hA1.Q_normal_in_H hA1.Q_disjoint_D
      hA1.Q_sup_D hf_mem hg_mem hh_mem hcanonical_eq omegaChosen (kOf a)
      homegaChosen.1 homegaChosen.2 (hkOf_mem a)
    rw [hinner_identity a b hnorm, hf_conj_zeta b] at hsection2_eq
    have hfprod_b_mem_Q :
        f (omegaChosen * rightConjugateElem s (kOf b)) ∈ Q :=
      (hf_mem _ (homega_mul_s_mem_Q b) (homega_mul_s_ne_one b)).1
    have hzeta_KW : zeta ∈ K ⊔ W := Subgroup.mem_sup_right hzeta
    have hconj_zeta_mem_Q :
        rightConjugateElem
            (f (omegaChosen * rightConjugateElem s (kOf b))) zeta ∈ Q :=
      hQ_conj_KW _ hfprod_b_mem_Q zeta hzeta_KW
    have ha_inv_KW : (kOf a)⁻¹ ∈ K ⊔ W :=
      (K ⊔ W).inv_mem (Subgroup.mem_sup_left (hkOf_mem a))
    have ha_inv_sq_KW : (kOf a)⁻¹ ^ 2 ∈ K ⊔ W :=
      (K ⊔ W).pow_mem ha_inv_KW 2
    have houter_mem_Q :
        rightConjugateElem
            (rightConjugateElem
              (f (omegaChosen * rightConjugateElem s (kOf b))) zeta)
            ((kOf a)⁻¹ ^ 2) ∈ Q :=
      hQ_conj_KW _ hconj_zeta_mem_Q _ ha_inv_sq_KW
    have hsa_inv_mem_Q0 : rightConjugateElem s (kOf a)⁻¹ ∈ Q0 :=
      hs_conj_kOf_inv_mem_Q0 a
    have hsa_inv_mem_Q : rightConjugateElem s (kOf a)⁻¹ ∈ Q :=
      hsection3.section2.Q0_le_Q hsa_inv_mem_Q0
    have hbar_relation :
        bar (f (omegaChosen * rightConjugateElem s (kOf a))) =
          (((a : F) : E)⁻¹) ^ 2 *
            (kcoord zeta *
              bar (f (omegaChosen * rightConjugateElem s (kOf b)))) := by
      calc
        bar (f (omegaChosen * rightConjugateElem s (kOf a))) =
            bar (rightConjugateElem
                (rightConjugateElem
                  (f (omegaChosen * rightConjugateElem s (kOf b))) zeta)
                ((kOf a)⁻¹ ^ 2) *
              rightConjugateElem s (kOf a)⁻¹) :=
          congrArg bar hsection2_eq
        _ = bar (rightConjugateElem
                (rightConjugateElem
                  (f (omegaChosen * rightConjugateElem s (kOf b))) zeta)
                ((kOf a)⁻¹ ^ 2)) +
              bar (rightConjugateElem s (kOf a)⁻¹) :=
          hbar_mul _ houter_mem_Q _ hsa_inv_mem_Q
        _ = kcoord ((kOf a)⁻¹ ^ 2) *
              bar (rightConjugateElem
                (f (omegaChosen * rightConjugateElem s (kOf b))) zeta) + 0 := by
          rw [hbar_conj _ hconj_zeta_mem_Q _ ha_inv_sq_KW,
            (hbar_Q0 _ hsa_inv_mem_Q).2 hsa_inv_mem_Q0]
        _ = kcoord ((kOf a)⁻¹ ^ 2) *
            (kcoord zeta *
              bar (f (omegaChosen * rightConjugateElem s (kOf b)))) := by
          rw [hbar_conj _ hfprod_b_mem_Q zeta hzeta_KW, add_zero]
        _ = (((a : F) : E)⁻¹) ^ 2 *
            (kcoord zeta *
              bar (f (omegaChosen * rightConjugateElem s (kOf b)))) := by
          rw [hkcoord_pow (kOf a)⁻¹ ha_inv_KW 2,
            hkcoord_inv (kOf a) (Subgroup.mem_sup_left (hkOf_mem a)),
            hkcoord_kOf]
    have hbar_relation' :
        bar omegaChosen /
            (((a : F) : E) ^ 2 + (kcoord zeta)⁻¹) =
          (((a : F) : E)⁻¹) ^ 2 *
            (kcoord zeta *
              (bar omegaChosen /
                (((b : F) : E) ^ 2 + (kcoord zeta)⁻¹))) := by
      simpa only [hclaim2_bar (kOf a) (hkOf_mem a),
        hclaim2_bar (kOf b) (hkOf_mem b), hkcoord_kOf] using hbar_relation
    have hratio :
        1 / (((a : F) : E) ^ 2 + (kcoord zeta)⁻¹) =
          kcoord zeta * (((a : F) : E)⁻¹) ^ 2 /
            (((b : F) : E) ^ 2 + (kcoord zeta)⁻¹) := by
      apply mul_right_cancel₀ homega_bar_ne_zero
      calc
        (1 / (((a : F) : E) ^ 2 + (kcoord zeta)⁻¹)) *
            bar omegaChosen =
          bar omegaChosen /
            (((a : F) : E) ^ 2 + (kcoord zeta)⁻¹) := by ring
        _ = (((a : F) : E)⁻¹) ^ 2 *
            (kcoord zeta *
              (bar omegaChosen /
                (((b : F) : E) ^ 2 + (kcoord zeta)⁻¹))) := hbar_relation'
        _ = (kcoord zeta * (((a : F) : E)⁻¹) ^ 2 /
            (((b : F) : E) ^ 2 + (kcoord zeta)⁻¹)) *
              bar omegaChosen := by ring
    have hb_sq_E :
        ((b : F) : E) ^ 2 =
          kcoord zeta + (kcoord zeta)⁻¹ + (((a : F) : E)⁻¹) ^ 2 :=
      claim_3_rational_step ((a : F) : E) ((b : F) : E) (kcoord zeta)
        (by simp) (hkcoord_ne_zero zeta hzeta_KW) (hdenom_ne a)
        (hdenom_ne b) hratio
    have hb_sq_F : (b : F) ^ 2 = beta + (a : F)⁻¹ ^ 2 := by
      apply F.subtype.injective
      simpa [beta] using hb_sq_E
    exact claim_3_norm_step theta alpha beta (a : F) (b : F)
      hnorm hb_sq_F htheta_beta
  have hsquare_surjective : Function.Surjective (fun x : F => x ^ 2) :=
    Finite.injective_iff_surjective.mp CharTwo.sq_injective
  let exceptional : F := (tau alpha) ^ 2
  have hstar : ∀ X : F, X ≠ 0 → X ≠ exceptional →
      alpha ^ 2 + beta ^ 2 + beta * (X + theta X) = 0 := by
    intro X hXzero hXexceptional
    obtain ⟨y, hy⟩ := hsquare_surjective X
    have hy_ne : y ≠ 0 := by
      intro hy_zero
      apply hXzero
      calc
        X = y ^ 2 := hy.symm
        _ = 0 := by simp [hy_zero]
    let a : Fˣ := Units.mk0 y⁻¹ (inv_ne_zero hy_ne)
    have ha_inv : (a : F)⁻¹ = y := by simp [a]
    have htarget :
        alpha + (a : F)⁻¹ * theta ((a : F)⁻¹) ≠ 0 := by
      intro hzero
      apply hXexceptional
      have hnorm_eq :
          (a : F)⁻¹ * theta ((a : F)⁻¹) = alpha :=
        (CharTwo.add_eq_zero.mp hzero).symm
      have ha_inv_tau : (a : F)⁻¹ = tau alpha := by
        apply (PFchapter4section2.norm_bijective_of_odd_order
          theta hthetaOdd).1
        calc
          (a : F)⁻¹ * theta ((a : F)⁻¹) = alpha := hnorm_eq
          _ = tau alpha * theta (tau alpha) := (hnorm_tau alpha).symm
      calc
        X = y ^ 2 := hy.symm
        _ = (a : F)⁻¹ ^ 2 := by rw [ha_inv]
        _ = (tau alpha) ^ 2 := by rw [ha_inv_tau]
        _ = exceptional := rfl
    simpa [ha_inv, hy] using hstar_units a htarget
  let c : F := (alpha ^ 2 + beta ^ 2) / beta
  have hconstant : ∀ X : F, X ≠ 0 → X ≠ exceptional →
      X + theta X = c := by
    intro X hXzero hXexceptional
    apply (eq_div_iff hbeta_ne_zero).2
    have hzero := CharTwo.add_eq_zero.mp (hstar X hXzero hXexceptional)
    simpa [c, mul_comm] using hzero.symm
  have htheta_claim3 : theta = 1 :=
    claim_3_a theta hthetaOdd exceptional c hconstant
  have hexceptional_eq_alpha : exceptional = alpha := by
    have hnorm := hnorm_tau alpha
    rw [htheta_claim3] at hnorm
    simpa [exceptional, pow_two] using hnorm
  have halpha_beta : alpha = beta := by
    by_cases hadmissible : ∃ X : F, X ≠ 0 ∧ X ≠ exceptional
    · obtain ⟨X, hXzero, hXexceptional⟩ := hadmissible
      exact claim_3_b theta alpha beta X htheta_claim3
        (hstar X hXzero hXexceptional)
    · have hbeta_exceptional : beta = exceptional := by
        by_contra hbeta_exceptional
        exact hadmissible ⟨beta, hbeta_ne_zero, hbeta_exceptional⟩
      exact (hbeta_exceptional.trans hexceptional_eq_alpha).symm
  have htheta : theta = 1 := htheta_claim3
  let omegaBar : E := (coordPair omegaS).1
  let omegaY : E := (coordPair omegaS).2
  have homega_bar_eq : bar omegaChosen = omegaBar := by
    rw [hbar_of_mem_Q omegaChosen homegaChosen.1]
  have homega_sq_center : omegaS ^ 2 = centerS alpha := by
    apply Subtype.ext
    change omegaChosen ^ 2 = center alpha
    exact halpha_center.symm
  have homega_norm : omegaBar * sigma omegaBar = (alpha : E) := by
    have hsecond := congrArg Prod.snd (hcoordPair_mul omegaS omegaS)
    rw [show omegaS * omegaS = omegaS ^ 2 by rw [pow_two],
      homega_sq_center, hcenter_coordPair] at hsecond
    change (alpha : E) = omegaY + omegaY + phi omegaBar omegaBar at hsecond
    rw [CharTwo.add_self_eq_zero, zero_add, hphiThetaOne htheta] at hsecond
    exact hsecond.symm
  have homega_norm_beta :
      omegaBar * sigma omegaBar = kcoord zeta + (kcoord zeta)⁻¹ := by
    calc
      omegaBar * sigma omegaBar = (alpha : E) := homega_norm
      _ = (beta : E) := congrArg Subtype.val halpha_beta
      _ = kcoord zeta + (kcoord zeta)⁻¹ := rfl
  have homega_unitary :
      omegaY + sigma omegaY = omegaBar * sigma omegaBar := by
    have hvalid := (coord (sIso omegaS)).property
    change
      (theta = 1 ∧ omegaY + sigma omegaY = omegaBar * sigma omegaBar) ∨
        (theta ≠ 1 ∧ omegaY ∈ F) at hvalid
    rcases hvalid with hunitary | htwisted
    · exact hunitary.2
    · exact False.elim (htwisted.1 htheta)
  have hconjS_coord_kcoord (x : S) (d : G) (hd : d ∈ K ⊔ W) :
      coordPair (conjS x ⟨d, hd⟩) =
        (kcoord d * (coordPair x).1,
          kcoord d * sigma (kcoord d) * (coordPair x).2) := by
    rw [hkcoord_of_mem_KW d hd]
    exact hconjS_coord x ⟨d, hd⟩
  have hsigma_kOf_coord (a : Fˣ) :
      sigma ((a : F) : E) = ((a : F) : E) := by
    simpa [htheta] using hsigmaF (a : F)
  have hs_conj_kOf_sq (a : Fˣ) :
      rightConjugateElem s (kOf a) = center ((a : F) ^ 2) := by
    rw [hs_conj_kOf, htheta]
    simp [pow_two]
  let sS : S := ⟨s, hsS⟩
  have hsS_coordPair : coordPair sS = (0, (1 : E)) := by
    rw [show sS = centerS 1 by simpa [sS] using hs_centerS,
      hcenter_coordPair]
    rfl
  let seedS (a : Fˣ) : S :=
    ⟨omegaChosen * rightConjugateElem s (kOf a),
      by simpa [hSQ] using homega_mul_s_mem_Q a⟩
  have hseedS_coord (a : Fˣ) :
      coordPair (seedS a) =
        (omegaBar, omegaY + (((a : F) : E) ^ 2)) := by
    have hseed_eq : seedS a = omegaS * centerS ((a : F) ^ 2) := by
      apply Subtype.ext
      change omegaChosen * rightConjugateElem s (kOf a) =
        omegaChosen * center ((a : F) ^ 2)
      rw [hs_conj_kOf_sq]
    rw [hseed_eq, hcoordPair_mul, hcenter_coordPair]
    simp [omegaBar, omegaY, hphi_zero_right]
  let fSeedS (a : Fˣ) : S :=
    ⟨f (omegaChosen * rightConjugateElem s (kOf a)), by
      simpa [hSQ] using
        (hf_mem _ (homega_mul_s_mem_Q a) (homega_mul_s_ne_one a)).1⟩
  let gamma (a : Fˣ) : E := (coordPair (fSeedS a)).2
  have hfSeedS_first (a : Fˣ) :
      (coordPair (fSeedS a)).1 =
        omegaBar / (((a : F) : E) ^ 2 + (kcoord zeta)⁻¹) := by
    calc
      (coordPair (fSeedS a)).1 =
          bar (f (omegaChosen * rightConjugateElem s (kOf a))) := by
        symm
        exact hbar_of_mem_Q _
          (hf_mem _ (homega_mul_s_mem_Q a) (homega_mul_s_ne_one a)).1
      _ = bar omegaChosen /
          (kcoord (kOf a) ^ 2 + (kcoord zeta)⁻¹) :=
        hclaim2_bar (kOf a) (hkOf_mem a)
      _ = omegaBar / (((a : F) : E) ^ 2 + (kcoord zeta)⁻¹) := by
        rw [homega_bar_eq, hkcoord_kOf]
  have hfSeedS_coord (a : Fˣ) :
      coordPair (fSeedS a) =
        (omegaBar / (((a : F) : E) ^ 2 + (kcoord zeta)⁻¹), gamma a) :=
    Prod.ext (hfSeedS_first a) rfl
  have hclaim1_seed (a : Fˣ) :=
    PFchapter4section3.claim_1 H D Q K V W Q0 S Q1 t s omegaChosen zeta
      f g h (kOf a) hsection3 hC1 hC2 hA1.two_transitive
      hA1.point_stabilizer hA1.involution_t hA1.t_not_mem_H hA1.D_eq
      hA1.Q_normal_in_H hA1.Q_disjoint_D hA1.Q_sup_D hf_mem hg_mem
      hh_mem hcanonical_eq homegaChosen.1 homegaChosen.2 hzeta hzeta_ne
      hfomega hhomega (hkOf_mem a) hW_fixed_point_free
  have hclaim4_scalar (a : Fˣ) :
      ((((a : F) : E) ^ 4) + 1) * gamma a =
        omegaY + (((a : F) : E) ^ 2) +
          (kcoord zeta)⁻¹ * (omegaBar * sigma omegaBar) /
            (((a : F) : E) ^ 2 + (kcoord zeta)⁻¹) := by
    have hzeta_KW : zeta ∈ K ⊔ W := Subgroup.mem_sup_right hzeta
    have hzeta_inv_KW : zeta⁻¹ ∈ K ⊔ W := (K ⊔ W).inv_mem hzeta_KW
    have hkOf_KW : kOf a ∈ K ⊔ W := Subgroup.mem_sup_left (hkOf_mem a)
    have hkOf_sq_KW : (kOf a) ^ 2 ∈ K ⊔ W := (K ⊔ W).pow_mem hkOf_KW 2
    have hdLeft_mem : zeta⁻¹ * (kOf a) ^ 2 ∈ K ⊔ W :=
      (K ⊔ W).mul_mem hzeta_inv_KW hkOf_sq_KW
    have hdRight_mem : zeta⁻¹ ^ 2 ∈ K ⊔ W :=
      (K ⊔ W).pow_mem hzeta_inv_KW 2
    let dLeft : (K ⊔ W : Subgroup G) :=
      ⟨zeta⁻¹ * (kOf a) ^ 2, hdLeft_mem⟩
    let dRight : (K ⊔ W : Subgroup G) := ⟨zeta⁻¹ ^ 2, hdRight_mem⟩
    let dOmega : (K ⊔ W : Subgroup G) := ⟨zeta⁻¹, hzeta_inv_KW⟩
    have hgroup :
        conjS (fSeedS a) dLeft * centerS ((a : F) ^ 2) =
          conjS (fSeedS a) dRight * conjS omegaS dOmega := by
      apply Subtype.ext
      have hclaim := hclaim1_seed a
      have hclaim' :
          rightConjugateElem
                (f (omegaChosen * rightConjugateElem s (kOf a)))
                (zeta⁻¹ * (kOf a) ^ 2) * center ((a : F) ^ 2) =
            rightConjugateElem
                (f (omegaChosen * rightConjugateElem s (kOf a)))
                (zeta⁻¹ ^ 2) * rightConjugateElem omegaChosen zeta⁻¹ := by
        calc
          _ = rightConjugateElem
                (f (omegaChosen * rightConjugateElem s (kOf a)))
                (zeta⁻¹ * (kOf a) ^ 2) *
              rightConjugateElem s (kOf a) := by rw [hs_conj_kOf_sq]
          _ = _ := hclaim
      simpa [dLeft, dRight, dOmega, fSeedS, omegaS, center,
        hconjS_coe] using hclaim'
    have hdLeft_coord :
        kcoord (dLeft : G) =
          (kcoord zeta)⁻¹ * (((a : F) : E) ^ 2) := by
      dsimp [dLeft]
      rw [hkcoord_mul zeta⁻¹ hzeta_inv_KW ((kOf a) ^ 2) hkOf_sq_KW,
        hkcoord_inv zeta hzeta_KW,
        hkcoord_pow (kOf a) hkOf_KW 2, hkcoord_kOf]
    have hdRight_coord :
        kcoord (dRight : G) = (kcoord zeta)⁻¹ ^ 2 := by
      dsimp [dRight]
      rw [hkcoord_pow zeta⁻¹ hzeta_inv_KW 2,
        hkcoord_inv zeta hzeta_KW]
    have hdOmega_coord : kcoord (dOmega : G) = (kcoord zeta)⁻¹ := by
      dsimp [dOmega]
      exact hkcoord_inv zeta hzeta_KW
    have hdLeft_sigma :
        sigma (kcoord (dLeft : G)) =
          kcoord zeta * (((a : F) : E) ^ 2) := by
      rw [hdLeft_coord, map_mul, map_inv₀, hzeta_coord_sigma, inv_inv,
        map_pow, hsigma_kOf_coord]
    have hdRight_sigma :
        sigma (kcoord (dRight : G)) = kcoord zeta ^ 2 := by
      rw [hdRight_coord, map_pow, map_inv₀, hzeta_coord_sigma, inv_inv]
    have hdOmega_sigma :
        sigma (kcoord (dOmega : G)) = kcoord zeta := by
      rw [hdOmega_coord, map_inv₀, hzeta_coord_sigma, inv_inv]
    have hzeta_coord_ne : kcoord zeta ≠ 0 :=
      hkcoord_ne_zero zeta hzeta_KW
    have hdLeft_norm :
        kcoord (dLeft : G) * sigma (kcoord (dLeft : G)) =
          (((a : F) : E) ^ 4) := by
      rw [hdLeft_sigma, hdLeft_coord]
      field_simp [hzeta_coord_ne]
    have hdRight_norm :
        kcoord (dRight : G) * sigma (kcoord (dRight : G)) = 1 := by
      rw [hdRight_sigma, hdRight_coord]
      field_simp [hzeta_coord_ne]
    have hdOmega_norm :
        kcoord (dOmega : G) * sigma (kcoord (dOmega : G)) = 1 := by
      rw [hdOmega_sigma, hdOmega_coord]
      exact inv_mul_cancel₀ hzeta_coord_ne
    have hleft_coord :=
      hconjS_coord_kcoord (fSeedS a) (dLeft : G) dLeft.property
    have hright_coord :=
      hconjS_coord_kcoord (fSeedS a) (dRight : G) dRight.property
    have homega_conj_coord :=
      hconjS_coord_kcoord omegaS (dOmega : G) dOmega.property
    have hleft_second :
        (coordPair (conjS (fSeedS a) dLeft)).2 =
          (((a : F) : E) ^ 4) * gamma a := by
      have hsecond := congrArg Prod.snd hleft_coord
      change
        (coordPair (conjS (fSeedS a) dLeft)).2 =
          kcoord (dLeft : G) * sigma (kcoord (dLeft : G)) * gamma a at hsecond
      simpa [hdLeft_norm] using hsecond
    have hright_first :
        (coordPair (conjS (fSeedS a) dRight)).1 =
          (kcoord zeta)⁻¹ ^ 2 *
            (omegaBar / (((a : F) : E) ^ 2 + (kcoord zeta)⁻¹)) := by
      have hfirst := congrArg Prod.fst hright_coord
      rw [hdRight_coord, hfSeedS_first] at hfirst
      exact hfirst
    have hright_second :
        (coordPair (conjS (fSeedS a) dRight)).2 = gamma a := by
      have hsecond := congrArg Prod.snd hright_coord
      change
        (coordPair (conjS (fSeedS a) dRight)).2 =
          kcoord (dRight : G) * sigma (kcoord (dRight : G)) * gamma a at hsecond
      simpa [hdRight_norm] using hsecond
    have homega_conj_first :
        (coordPair (conjS omegaS dOmega)).1 =
          (kcoord zeta)⁻¹ * omegaBar := by
      have hfirst := congrArg Prod.fst homega_conj_coord
      simpa [hdOmega_coord, omegaBar] using hfirst
    have homega_conj_second :
        (coordPair (conjS omegaS dOmega)).2 = omegaY := by
      have hsecond := congrArg Prod.snd homega_conj_coord
      change
        (coordPair (conjS omegaS dOmega)).2 =
          kcoord (dOmega : G) * sigma (kcoord (dOmega : G)) * omegaY at hsecond
      simpa [hdOmega_norm] using hsecond
    have hphi_term :
        phi (coordPair (conjS (fSeedS a) dRight)).1
            (coordPair (conjS omegaS dOmega)).1 =
          (kcoord zeta)⁻¹ * (omegaBar * sigma omegaBar) /
            (((a : F) : E) ^ 2 + (kcoord zeta)⁻¹) := by
      rw [hphiThetaOne htheta, hright_first, homega_conj_first,
        map_mul, map_inv₀, hzeta_coord_sigma, inv_inv]
      field_simp [hzeta_coord_ne, hdenom_ne a]
    have hseconds := congrArg Prod.snd (congrArg coordPair hgroup)
    rw [hcoordPair_mul, hcoordPair_mul, hleft_second, hcenter_coordPair,
      hright_second, homega_conj_second, hphi_zero_right, hphi_term] at hseconds
    have ha_sq_coe :
        (((((a : F) ^ 2) : F) : E)) = (((a : F) : E) ^ 2) :=
      map_pow F.subtype (a : F) 2
    rw [ha_sq_coe] at hseconds
    have htwo : (2 : E) = 0 := CharTwo.two_eq_zero
    linear_combination hseconds - ((((a : F) : E) ^ 2) - gamma a) * htwo
  have homegaY_eq : omegaY = (kcoord zeta)⁻¹ := by
    have hscalar :
        (((1 : E) ^ 4) + 1) * gamma (1 : Fˣ) =
          omegaY + ((1 : E) ^ 2) +
            (kcoord zeta)⁻¹ *
                (kcoord zeta + (kcoord zeta)⁻¹) /
              ((1 : E) ^ 2 + (kcoord zeta)⁻¹) := by
      simpa [homega_norm_beta] using hclaim4_scalar (1 : Fˣ)
    have hzeta_coord_ne : kcoord zeta ≠ 0 :=
      hkcoord_ne_zero zeta (Subgroup.mem_sup_right hzeta)
    have hzeta_add_one_ne : kcoord zeta + 1 ≠ 0 := by
      intro hzero
      exact hzeta_coord_ne_one (CharTwo.add_eq_zero.mp hzero)
    field_simp [hzeta_coord_ne, hzeta_add_one_ne] at hscalar
    have htwo : (2 : E) = 0 := CharTwo.two_eq_zero
    have hfactor :
        (kcoord zeta + 1) * (omegaY * kcoord zeta + 1) = 0 := by
      linear_combination hscalar +
        (1 + kcoord zeta + kcoord zeta * omegaY + kcoord zeta ^ 2 +
          kcoord zeta ^ 2 * omegaY - kcoord zeta * gamma (1 : Fˣ) -
          kcoord zeta ^ 2 * gamma (1 : Fˣ)) * htwo
    have hinner : omegaY * kcoord zeta + 1 = 0 :=
      (mul_eq_zero.mp hfactor).resolve_left hzeta_add_one_ne
    field_simp [hzeta_coord_ne]
    linear_combination hinner - htwo
  have hgamma_formula (a : Fˣ) (ha_ne_one : (a : F) ≠ 1) :
      gamma a = 1 / (((a : F) : E) ^ 2 + (kcoord zeta)⁻¹) := by
    have hscalar := hclaim4_scalar a
    rw [homegaY_eq, homega_norm_beta] at hscalar
    have hzeta_coord_ne : kcoord zeta ≠ 0 :=
      hkcoord_ne_zero zeta (Subgroup.mem_sup_right hzeta)
    have hden := hdenom_ne a
    have hrhs :
        (kcoord zeta)⁻¹ + (((a : F) : E) ^ 2) +
            (kcoord zeta)⁻¹ *
                (kcoord zeta + (kcoord zeta)⁻¹) /
              (((a : F) : E) ^ 2 + (kcoord zeta)⁻¹) =
          ((((a : F) : E) ^ 4) + 1) /
            (((a : F) : E) ^ 2 + (kcoord zeta)⁻¹) := by
      apply (eq_div_iff hden).2
      rw [add_mul, div_mul_cancel₀ _ hden]
      field_simp [hzeta_coord_ne]
      ring_nf
      simp [CharTwo.two_eq_zero]
    rw [hrhs] at hscalar
    have haE_ne_one : ((a : F) : E) ≠ 1 := by
      intro haE
      apply ha_ne_one
      apply F.subtype.injective
      simpa using haE
    have hfactor : ((((a : F) : E) ^ 4) + 1) ≠ 0 := by
      intro hzero
      have hpow : (((a : F) : E) ^ 4) = 1 :=
        CharTwo.add_eq_zero.mp hzero
      have hsq2 : ((((a : F) : E) ^ 2) ^ 2) = (1 : E) ^ 2 := by
        calc
          (((a : F) : E) ^ 2) ^ 2 = ((a : F) : E) ^ 4 := by ring
          _ = 1 := hpow
          _ = (1 : E) ^ 2 := by simp
      have hsq : (((a : F) : E) ^ 2) = 1 := CharTwo.sq_injective hsq2
      exact haE_ne_one
        (CharTwo.sq_injective (by simpa only [one_pow] using hsq))
    apply mul_left_cancel₀ hfactor
    simpa [div_eq_mul_inv, mul_assoc] using hscalar
  have hvalid_of_coord (x : S) (u v : E)
      (hx : coordPair x = (u, v)) : ValidPair u v := by
    have hvalid := (coord (sIso x)).property
    change ValidPair (coordPair x).1 (coordPair x).2 at hvalid
    simpa [hx] using hvalid
  have hS_coe_eq_mk (x : S) (u v : E) (huv : ValidPair u v)
      (hx : coordPair x = (u, v)) : (x : G) = mk u v := by
    rw [hmk_of_valid u v huv]
    apply congrArg Subtype.val
    apply sIso.injective
    apply coord.injective
    apply Subtype.ext
    change coordPair x = coordPair (mkS u v huv)
    rw [hx, hmkS_coord]
  have hseed_formula (a : Fˣ) (ha_ne_one : (a : F) ≠ 1) :
      f (mk omegaBar (omegaY + (((a : F) : E) ^ 2))) =
        mk
          (omegaBar / (omegaY + (((a : F) : E) ^ 2)))
          (omegaY + (((a : F) : E) ^ 2))⁻¹ := by
    have hseed_valid :
        ValidPair omegaBar (omegaY + (((a : F) : E) ^ 2)) :=
      hvalid_of_coord (seedS a) _ _ (hseedS_coord a)
    have hseed_mk :
        ((seedS a : S) : G) =
          mk omegaBar (omegaY + (((a : F) : E) ^ 2)) :=
      hS_coe_eq_mk (seedS a) _ _ hseed_valid (hseedS_coord a)
    have hfseed_coord :
        coordPair (fSeedS a) =
          (omegaBar / (omegaY + (((a : F) : E) ^ 2)),
            (omegaY + (((a : F) : E) ^ 2))⁻¹) := by
      rw [hfSeedS_coord, hgamma_formula a ha_ne_one, homegaY_eq]
      simp only [add_comm, one_div]
    have hfseed_valid :
        ValidPair
          (omegaBar / (omegaY + (((a : F) : E) ^ 2)))
          (omegaY + (((a : F) : E) ^ 2))⁻¹ :=
      hvalid_of_coord (fSeedS a) _ _ hfseed_coord
    have hfseed_mk :
        ((fSeedS a : S) : G) =
          mk
            (omegaBar / (omegaY + (((a : F) : E) ^ 2)))
            (omegaY + (((a : F) : E) ^ 2))⁻¹ :=
      hS_coe_eq_mk (fSeedS a) _ _ hfseed_valid hfseed_coord
    calc
      f (mk omegaBar (omegaY + (((a : F) : E) ^ 2))) =
          f ((seedS a : S) : G) := by rw [hseed_mk]
      _ = ((fSeedS a : S) : G) := rfl
      _ = _ := hfseed_mk
  have hclaim4_nonexceptional :
      ∀ y : E,
        y + sigma y = omegaBar * sigma omegaBar →
        y + omegaY ≠ 0 → y + omegaY ≠ 1 →
          f (mk omegaBar y) = mk (omegaBar / y) y⁻¹ := by
    intro y hy hdelta_ne_zero hdelta_ne_one
    have htrace :
        (y + omegaY) + sigma (y + omegaY) = 0 := by
      rw [map_add]
      calc
        y + omegaY + (sigma y + sigma omegaY) =
            (y + sigma y) + (omegaY + sigma omegaY) := by ring
        _ = (omegaBar * sigma omegaBar) +
            (omegaBar * sigma omegaBar) := by rw [hy, homega_unitary]
        _ = 0 := CharTwo.add_self_eq_zero _
    have hdelta_mem : y + omegaY ∈ F :=
      htrace_zero_mem_F htheta (y + omegaY) htrace
    let delta : F := ⟨y + omegaY, hdelta_mem⟩
    obtain ⟨r, hr⟩ := hsquare_surjective delta
    have hrE : ((r : F) : E) ^ 2 = y + omegaY := by
      calc
        ((r : F) : E) ^ 2 = ((r ^ 2 : F) : E) :=
          (map_pow F.subtype r 2).symm
        _ = (delta : E) := congrArg Subtype.val hr
        _ = y + omegaY := rfl
    have hr_ne_zero : r ≠ 0 := by
      intro hrzero
      apply hdelta_ne_zero
      rw [← hrE, hrzero]
      simp
    let a : Fˣ := Units.mk0 r hr_ne_zero
    have ha_sq : (((a : F) : E) ^ 2) = y + omegaY := by
      simpa [a] using hrE
    have ha_ne_one : (a : F) ≠ 1 := by
      intro haone
      apply hdelta_ne_one
      rw [← ha_sq, haone]
      simp
    have hy_eq : y = omegaY + (((a : F) : E) ^ 2) := by
      calc
        y = (y + omegaY) + omegaY := by
          rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
        _ = (((a : F) : E) ^ 2) + omegaY := by rw [ha_sq]
        _ = omegaY + (((a : F) : E) ^ 2) := add_comm _ _
    simpa [hy_eq] using hseed_formula a ha_ne_one
  have hclaim4_at_omega :
      f (mk omegaBar omegaY) = mk (omegaBar / omegaY) omegaY⁻¹ := by
    have homega_valid_pair : ValidPair omegaBar omegaY :=
      Or.inl ⟨htheta, homega_unitary⟩
    have homega_mk : (omegaS : G) = mk omegaBar omegaY :=
      hS_coe_eq_mk omegaS _ _ homega_valid_pair rfl
    have homega_ne_one : omegaChosen ≠ 1 := by
      intro homega_one
      exact homegaChosen.2 (homega_one ▸ Q0.one_mem)
    let fOmegaS : S :=
      ⟨f omegaChosen, by
        simpa [hSQ] using (hf_mem omegaChosen homegaChosen.1 homega_ne_one).1⟩
    have homegaS_inv_shape : omegaS⁻¹ = omegaS * centerS alpha := by
      apply Subtype.ext
      simpa [omegaS, center] using homega_inv_shape
    have homega_inv_coord :
        coordPair omegaS⁻¹ = (omegaBar, kcoord zeta) := by
      rw [homegaS_inv_shape, hcoordPair_mul, hcenter_coordPair]
      apply Prod.ext
      · simp [omegaBar]
      · simp only [hphi_zero_right, add_zero]
        change omegaY + (alpha : E) = kcoord zeta
        rw [homegaY_eq, congrArg Subtype.val halpha_beta]
        change
          (kcoord zeta)⁻¹ +
              (kcoord zeta + (kcoord zeta)⁻¹) = kcoord zeta
        rw [← add_assoc, add_right_comm, CharTwo.add_self_eq_zero, zero_add]
    have hfOmegaS_eq : fOmegaS = conjS omegaS⁻¹ zetaKW := by
      apply Subtype.ext
      simpa [fOmegaS, zetaKW, hconjS_coe] using hfomega
    have hfOmega_coord :
        coordPair fOmegaS =
          (kcoord zeta * omegaBar, kcoord zeta) := by
      rw [hfOmegaS_eq]
      have hcoord :=
        hconjS_coord_kcoord omegaS⁻¹ zeta
          (Subgroup.mem_sup_right hzeta)
      rw [homega_inv_coord, hzeta_coord_sigma] at hcoord
      have hzeta_coord_ne : kcoord zeta ≠ 0 :=
        hkcoord_ne_zero zeta (Subgroup.mem_sup_right hzeta)
      simpa [inv_mul_cancel₀ hzeta_coord_ne] using hcoord
    have htarget_coord :
        coordPair fOmegaS = (omegaBar / omegaY, omegaY⁻¹) := by
      rw [hfOmega_coord, homegaY_eq]
      have hzeta_coord_ne : kcoord zeta ≠ 0 :=
        hkcoord_ne_zero zeta (Subgroup.mem_sup_right hzeta)
      apply Prod.ext
      · field_simp [hzeta_coord_ne]
      · simp
    have htarget_valid : ValidPair (omegaBar / omegaY) omegaY⁻¹ :=
      hvalid_of_coord fOmegaS _ _ htarget_coord
    have hfOmega_mk :
        (fOmegaS : G) = mk (omegaBar / omegaY) omegaY⁻¹ :=
      hS_coe_eq_mk fOmegaS _ _ htarget_valid htarget_coord
    calc
      f (mk omegaBar omegaY) = f (omegaS : G) := by rw [homega_mk]
      _ = (fOmegaS : G) := rfl
      _ = _ := hfOmega_mk
  have hclaim4_second_exception :
      f (mk omegaBar (omegaY + 1)) =
        mk (omegaBar / (omegaY + 1)) (omegaY + 1)⁻¹ := by
    have homega_ne_one : omegaChosen ≠ 1 := by
      intro homega_one
      exact homegaChosen.2 (homega_one ▸ Q0.one_mem)
    let fOmegaS : S :=
      ⟨f omegaChosen, by
        simpa [hSQ] using (hf_mem omegaChosen homegaChosen.1 homega_ne_one).1⟩
    let pS : S := omegaS * sS
    let qS : S := fOmegaS * sS
    let zetaInvKW : (K ⊔ W : Subgroup G) :=
      ⟨zeta⁻¹, (K ⊔ W).inv_mem (Subgroup.mem_sup_right hzeta)⟩
    let qPrimeS : S := conjS qS zetaInvKW
    have hfOmega_conj_back :
        rightConjugateElem (f omegaChosen) zeta⁻¹ = omegaChosen⁻¹ := by
      have hfomega' :
          f omegaChosen = rightConjugateElem omegaChosen⁻¹ zeta := by
        exact hfomega
      rw [hfomega']
      simp [rightConjugateElem, mul_assoc]
    have hs_conj_zeta_inv : rightConjugateElem s zeta⁻¹ = s := by
      rw [hs_center]
      exact hcenter_conj_W zeta⁻¹ (W.inv_mem hzeta) 1
    have hqPrime_coe :
        (qPrimeS : G) = omegaChosen⁻¹ * s := by
      calc
        (qPrimeS : G) = rightConjugateElem (qS : G) zeta⁻¹ := by
          simpa [qPrimeS, zetaInvKW] using hconjS_coe qS zetaInvKW
        _ = rightConjugateElem (f omegaChosen * s) zeta⁻¹ := by
          rfl
        _ = rightConjugateElem (f omegaChosen) zeta⁻¹ *
            rightConjugateElem s zeta⁻¹ := by
          simp [rightConjugateElem, mul_assoc]
        _ = omegaChosen⁻¹ * s := by
          rw [hfOmega_conj_back, hs_conj_zeta_inv]
    have hqPrime_shape :
        qPrimeS = omegaS * centerS (alpha + 1) := by
      apply Subtype.ext
      calc
        (qPrimeS : G) = omegaChosen⁻¹ * s := hqPrime_coe
        _ = (omegaChosen * center alpha) * center 1 := by
          rw [homega_inv_shape, hs_center]
        _ = omegaChosen * center (alpha + 1) := by
          rw [mul_assoc, ← hcenter_add]
        _ = ((omegaS * centerS (alpha + 1) : S) : G) := rfl
    have hqPrime_coord :
        coordPair qPrimeS = (omegaBar, kcoord zeta + 1) := by
      rw [hqPrime_shape, hcoordPair_mul, hcenter_coordPair]
      apply Prod.ext
      · simp [omegaBar]
      · simp only [hphi_zero_right, add_zero]
        change omegaY + ((alpha + 1 : F) : E) = kcoord zeta + 1
        rw [show ((alpha + 1 : F) : E) = (alpha : E) + 1 by
          exact map_add F.subtype alpha 1,
          homegaY_eq, congrArg Subtype.val halpha_beta]
        rw [show (beta : E) =
          kcoord zeta + (kcoord zeta)⁻¹ by rfl]
        ring_nf
        simp [CharTwo.two_eq_zero]
    have hqPrime_valid : ValidPair omegaBar (kcoord zeta + 1) :=
      hvalid_of_coord qPrimeS _ _ hqPrime_coord
    have hyPrime_unitary :
        (kcoord zeta + 1) + sigma (kcoord zeta + 1) =
          omegaBar * sigma omegaBar := by
      rcases hqPrime_valid with hunitary | htwisted
      · exact hunitary.2
      · exact False.elim (htwisted.1 htheta)
    have hqPrime_mk :
        (qPrimeS : G) = mk omegaBar (kcoord zeta + 1) :=
      hS_coe_eq_mk qPrimeS _ _ hqPrime_valid hqPrime_coord
    have hdelta_prime :
        (kcoord zeta + 1) + omegaY = (beta : E) + 1 := by
      rw [homegaY_eq]
      change
        kcoord zeta + 1 + (kcoord zeta)⁻¹ =
          (kcoord zeta + (kcoord zeta)⁻¹) + 1
      ring
    have hqPrime_formula :
        f (mk omegaBar (kcoord zeta + 1)) =
          mk (omegaBar / (kcoord zeta + 1)) (kcoord zeta + 1)⁻¹ := by
      by_cases hbeta_one : beta = 1
      · have hbeta_one_E :
            kcoord zeta + (kcoord zeta)⁻¹ = 1 :=
          congrArg Subtype.val hbeta_one
        have hy_eq : kcoord zeta + 1 = omegaY := by
          calc
            kcoord zeta + 1 =
                kcoord zeta +
                  (kcoord zeta + (kcoord zeta)⁻¹) := by
              rw [hbeta_one_E]
            _ = (kcoord zeta)⁻¹ := by
              rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
            _ = omegaY := homegaY_eq.symm
        simpa [hy_eq] using hclaim4_at_omega
      · have hdelta_ne_zero :
            (kcoord zeta + 1) + omegaY ≠ 0 := by
          intro hzero
          rw [hdelta_prime] at hzero
          apply hbeta_one
          apply Subtype.ext
          exact CharTwo.add_eq_zero.mp hzero
        have hdelta_ne_one :
            (kcoord zeta + 1) + omegaY ≠ 1 := by
          intro hone
          rw [hdelta_prime] at hone
          apply hbeta_ne_zero
          apply Subtype.ext
          have hzero : (beta : E) + 1 = 0 + 1 := by simpa using hone
          exact add_right_cancel hzero
        exact hclaim4_nonexceptional (kcoord zeta + 1)
          hyPrime_unitary hdelta_ne_zero hdelta_ne_one
    have hqPrime_ne_one : qPrimeS ≠ 1 := by
      intro hqPrime_one
      have hcoords := congrArg coordPair hqPrime_one
      rw [hqPrime_coord, hcoordPair_one] at hcoords
      apply homega_bar_ne_zero
      rw [homega_bar_eq]
      exact congrArg Prod.fst hcoords
    have hqS_ne_one : (qS : G) ≠ 1 := by
      intro hq_one
      apply hqPrime_ne_one
      have hq_one_sub : qS = 1 := Subtype.ext hq_one
      simp [qPrimeS, hq_one_sub, conjS]
    have hqS_mem_Q : (qS : G) ∈ Q := by
      simpa [hSQ] using qS.property
    have hzeta_inv_fixed_t : rightConjugateElem zeta⁻¹ t = zeta⁻¹ := by
      calc
        rightConjugateElem zeta⁻¹ t =
            (rightConjugateElem zeta t)⁻¹ := by
          simp [rightConjugateElem, mul_assoc]
        _ = zeta⁻¹ := by rw [hzeta_fixed_t]
    have hf_qPrime :
        f (qPrimeS : G) =
          rightConjugateElem (f (qS : G)) zeta⁻¹ := by
      have htransport := PFchapter4section1.claim_H3 H Q D t f g h
        hA1.two_transitive hA1.point_stabilizer hA1.involution_t
        hA1.t_not_mem_H hA1.D_eq hA1.Q_normal_in_H hA1.Q_disjoint_D
        hA1.Q_sup_D hf_mem hg_mem hh_mem hcanonical_eq (qS : G) zeta⁻¹
        hqS_mem_Q hqS_ne_one (D.inv_mem (hW_le_D hzeta))
      calc
        f (qPrimeS : G) =
            f (rightConjugateElem (qS : G) zeta⁻¹) := by
          rw [← hconjS_coe qS zetaInvKW]
        _ = rightConjugateElem (f (qS : G))
            (rightConjugateElem zeta⁻¹ t) := htransport
        _ = rightConjugateElem (f (qS : G)) zeta⁻¹ := by
          rw [hzeta_inv_fixed_t]
    have hf_q :
        f (qS : G) = rightConjugateElem (f (qPrimeS : G)) zeta := by
      have hback := congrArg
        (fun x : G => rightConjugateElem x zeta) hf_qPrime
      symm
      simpa [rightConjugateElem, mul_assoc] using hback
    have hp_coord :
        coordPair pS = (omegaBar, omegaY + 1) := by
      simp [pS, hcoordPair_mul, hsS_coordPair, omegaBar, omegaY,
        hphi_zero_right]
    have hp_ne_one : (pS : G) ≠ 1 := by
      intro hp_one
      have hp_one_sub : pS = 1 := Subtype.ext hp_one
      have hcoords := congrArg coordPair hp_one_sub
      rw [hp_coord, hcoordPair_one] at hcoords
      apply homega_bar_ne_zero
      rw [homega_bar_eq]
      exact congrArg Prod.fst hcoords
    have hp_mem_Q : (pS : G) ∈ Q := by
      simpa [hSQ] using pS.property
    have hsection2_one :=
      PFchapter4section2.claim_2 H D Q K V W Q0 S Q1 t s f g h
        hsection3 hC1 hC2 hA1.two_transitive hA1.point_stabilizer
        hA1.involution_t hA1.t_not_mem_H hA1.D_eq hA1.Q_normal_in_H
        hA1.Q_disjoint_D hA1.Q_sup_D hf_mem hg_mem hh_mem hcanonical_eq
        omegaChosen 1 homegaChosen.1 homegaChosen.2 K.one_mem
    have hf_p : f (pS : G) = f (qS : G) * s := by
      simpa [pS, qS, fOmegaS, sS, rightConjugateElem] using hsection2_one
    let fqPrimeS : S :=
      ⟨f (qPrimeS : G), by
        simpa [hSQ] using
          (hf_mem (qPrimeS : G) (by simpa [hSQ] using qPrimeS.property)
            (fun hq => hqPrime_ne_one (Subtype.ext hq))).1⟩
    have hfqPrime_group :
        (fqPrimeS : G) =
          mk (omegaBar / (kcoord zeta + 1)) (kcoord zeta + 1)⁻¹ := by
      simpa [fqPrimeS, hqPrime_mk] using hqPrime_formula
    have hfqPrime_target_valid :
        ValidPair (omegaBar / (kcoord zeta + 1)) (kcoord zeta + 1)⁻¹ := by
      by_contra hvalid
      have hmkQ :
          mk (omegaBar / (kcoord zeta + 1)) (kcoord zeta + 1)⁻¹ ∈ Q := by
        rw [← hfqPrime_group]
        simpa [hSQ] using fqPrimeS.property
      have htQ : t ∈ Q := by
        simpa [mk, hvalid] using hmkQ
      exact ht_not_mem_Q htQ
    have hfqPrime_coord :
        coordPair fqPrimeS =
          (omegaBar / (kcoord zeta + 1), (kcoord zeta + 1)⁻¹) := by
      have hfqPrimeS_eq :
          fqPrimeS = mkS (omegaBar / (kcoord zeta + 1))
            (kcoord zeta + 1)⁻¹ hfqPrime_target_valid := by
        apply Subtype.ext
        simpa [hmk_of_valid _ _ hfqPrime_target_valid] using hfqPrime_group
      rw [hfqPrimeS_eq, hmkS_coord]
    let fqS : S :=
      ⟨f (qS : G), by
        simpa [hSQ] using (hf_mem (qS : G) hqS_mem_Q hqS_ne_one).1⟩
    have hfqS_eq : fqS = conjS fqPrimeS zetaKW := by
      apply Subtype.ext
      simpa [fqS, fqPrimeS, zetaKW, hconjS_coe] using hf_q
    have hfq_coord :
        coordPair fqS =
          (kcoord zeta * (omegaBar / (kcoord zeta + 1)),
            (kcoord zeta + 1)⁻¹) := by
      rw [hfqS_eq]
      have hcoord := hconjS_coord_kcoord fqPrimeS zeta
        (Subgroup.mem_sup_right hzeta)
      rw [hfqPrime_coord, hzeta_coord_sigma] at hcoord
      have hzeta_coord_ne : kcoord zeta ≠ 0 :=
        hkcoord_ne_zero zeta (Subgroup.mem_sup_right hzeta)
      simpa [zetaKW, mul_inv_cancel₀ hzeta_coord_ne] using hcoord
    let fpS : S :=
      ⟨f (pS : G), by
        simpa [hSQ] using (hf_mem (pS : G) hp_mem_Q hp_ne_one).1⟩
    have hfpS_eq : fpS = fqS * sS := by
      apply Subtype.ext
      simpa [fpS, fqS, sS] using hf_p
    have hfp_coord :
        coordPair fpS =
          (omegaBar / (omegaY + 1), (omegaY + 1)⁻¹) := by
      rw [hfpS_eq, hcoordPair_mul, hfq_coord, hsS_coordPair,
        hphi_zero_right, add_zero, homegaY_eq]
      simp only [add_zero]
      have hzeta_coord_ne : kcoord zeta ≠ 0 :=
        hkcoord_ne_zero zeta (Subgroup.mem_sup_right hzeta)
      have hzeta_add_one_ne : kcoord zeta + 1 ≠ 0 := by
        intro hzero
        exact hzeta_coord_ne_one (CharTwo.add_eq_zero.mp hzero)
      have hzeta_inv_add_one_ne : (kcoord zeta)⁻¹ + 1 ≠ 0 := by
        intro hzero
        have hzinv : (kcoord zeta)⁻¹ = 1 :=
          CharTwo.add_eq_zero.mp hzero
        exact hzeta_coord_ne_one (by
          apply inv_injective
          simpa using hzinv)
      apply Prod.ext
      · field_simp [hzeta_coord_ne, hzeta_add_one_ne,
          hzeta_inv_add_one_ne]
        rw [add_comm 1 (kcoord zeta)]
        simp [hzeta_add_one_ne]
      · field_simp [hzeta_coord_ne, hzeta_add_one_ne,
          hzeta_inv_add_one_ne]
        rw [add_comm 1 (kcoord zeta)]
        field_simp [hzeta_add_one_ne]
        rw [← add_assoc, add_right_comm, CharTwo.add_self_eq_zero, zero_add]
    have hfp_valid :
        ValidPair (omegaBar / (omegaY + 1)) (omegaY + 1)⁻¹ :=
      hvalid_of_coord fpS _ _ hfp_coord
    have hfp_mk :
        (fpS : G) = mk (omegaBar / (omegaY + 1)) (omegaY + 1)⁻¹ :=
      hS_coe_eq_mk fpS _ _ hfp_valid hfp_coord
    have hp_valid : ValidPair omegaBar (omegaY + 1) :=
      hvalid_of_coord pS _ _ hp_coord
    have hp_mk : (pS : G) = mk omegaBar (omegaY + 1) :=
      hS_coe_eq_mk pS _ _ hp_valid hp_coord
    calc
      f (mk omegaBar (omegaY + 1)) = f (pS : G) := by rw [hp_mk]
      _ = (fpS : G) := rfl
      _ = _ := hfp_mk
  have hclaim4 :
      ∀ y : E, y ≠ 0 →
        y + sigma y = omegaBar * sigma omegaBar →
          f (mk omegaBar y) = mk (omegaBar / y) y⁻¹ := by
    intro y _hy hy_unitary
    by_cases hbase : y + omegaY = 0
    · have hy_eq : y = omegaY := CharTwo.add_eq_zero.mp hbase
      simpa [hy_eq] using hclaim4_at_omega
    by_cases hshift : y + omegaY = 1
    · have hy_eq : y = omegaY + 1 := by
        calc
          y = (y + omegaY) + omegaY := by
            rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
          _ = 1 + omegaY := by rw [hshift]
          _ = omegaY + 1 := add_comm _ _
      simpa [hy_eq] using hclaim4_second_exception
    exact hclaim4_nonexceptional y hy_unitary hbase hshift
  have hsigma_kcoord_K (a : G) (ha : a ∈ K) :
      sigma (kcoord a) = kcoord a := by
    have haKW : a ∈ K ⊔ W := Subgroup.mem_sup_left ha
    let aKW : (K ⊔ W : Subgroup G) := ⟨a, haKW⟩
    have haK1 :
        (((kwIso aKW : (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ)) ∈ K1 := by
      simpa [aKW] using hkwIso_mem_K1 a ha
    obtain ⟨b, hb⟩ := (hK1 _).1 haK1
    rw [hkcoord_of_mem_KW a haKW]
    calc
      sigma
          (((kwIso (⟨a, haKW⟩ : (K ⊔ W : Subgroup G)) :
              (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) =
          sigma ((b : F) : E) := by simpa [aKW] using congrArg sigma hb
      _ = ((theta b : F) : E) := hsigmaF b
      _ = ((b : F) : E) := by rw [htheta]; rfl
      _ =
          (((kwIso (⟨a, haKW⟩ : (K ⊔ W : Subgroup G)) :
              (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) := by
            simpa [aKW] using hb.symm
  have hsigma_kcoord_W (a : G) (ha : a ∈ W) :
      sigma (kcoord a) = (kcoord a)⁻¹ := by
    have haKW : a ∈ K ⊔ W := Subgroup.mem_sup_right ha
    rw [hkcoord_of_mem_KW a haKW]
    exact hW1inv _ (hkwIso_mem_W1 a ha)
  have hKW_t_coordinate : ∀ d : G, d ∈ K ⊔ W →
      rightConjugateElem d t ∈ K ⊔ W ∧
        kcoord (rightConjugateElem d t) = (sigma (kcoord d))⁻¹ := by
    intro d hd
    have hd' : d ∈ ((K ⊔ W : Subgroup G) : Set G) := hd
    rw [Subgroup.coe_mul_of_right_le_normalizer_left
      K W hW_normalizes_K] at hd'
    rcases Set.mem_mul.mp hd' with ⟨k, hkK, v, hvW, hkv⟩
    have hd_eq : d = k * v := hkv.symm
    have hvKW : v ∈ K ⊔ W := Subgroup.mem_sup_right hvW
    have hkKW : k ∈ K ⊔ W := Subgroup.mem_sup_left hkK
    have hkt : rightConjugateElem k t = k⁻¹ :=
      (hsection3.section2.K_def k).mp hkK |>.2
    have htC : t ∈ Subgroup.centralizer (W : Set G) :=
      PFchapter1section1.t_mem_centralizer_of_le_peterfalviV
        D V W t hsection3.section2.W_le_V hsection3.section2.V_eq
    have hvt : rightConjugateElem v t = v := by
      have hcomm : Commute v t :=
        Subgroup.mem_centralizer_iff.mp htC v hvW
      simp [rightConjugateElem, hcomm.eq, mul_assoc]
    have hconj_mul : ∀ x y z : G,
        rightConjugateElem (x * y) z =
          rightConjugateElem x z * rightConjugateElem y z := by
      intro x y z
      simp [rightConjugateElem, mul_assoc]
    have hdt_eq : rightConjugateElem d t = k⁻¹ * v := by
      rw [hd_eq, hconj_mul, hvt, hkt]
    have hdtKW : rightConjugateElem d t ∈ K ⊔ W := by
      rw [hdt_eq]
      exact (K ⊔ W).mul_mem ((K ⊔ W).inv_mem hkKW) hvKW
    refine ⟨hdtKW, ?_⟩
    rw [hdt_eq, hd_eq,
      hkcoord_mul k⁻¹ ((K ⊔ W).inv_mem hkKW) v hvKW,
      hkcoord_inv k hkKW, hkcoord_mul k hkKW v hvKW,
      map_mul, hsigma_kcoord_K k hkK, hsigma_kcoord_W v hvW]
    simp [mul_comm]
  have hmk_conj_KW (x y : E) (hxy : ValidPair x y)
      (d : G) (hd : d ∈ K ⊔ W) :
      rightConjugateElem (mk x y) d =
        mk (kcoord d * x)
          (kcoord d * sigma (kcoord d) * y) := by
    let xS : S := mkS x y hxy
    have hxS_coord : coordPair xS = (x, y) := hmkS_coord x y hxy
    have hout_coord := hconjS_coord_kcoord xS d hd
    rw [hxS_coord] at hout_coord
    have hout_valid :
        ValidPair (kcoord d * x)
          (kcoord d * sigma (kcoord d) * y) :=
      hvalid_of_coord (conjS xS ⟨d, hd⟩) _ _ hout_coord
    calc
      rightConjugateElem (mk x y) d =
          rightConjugateElem (xS : G) d := by rw [hmk_of_valid]
      _ = (conjS xS ⟨d, hd⟩ : S) :=
        (hconjS_coe xS ⟨d, hd⟩).symm
      _ = mk (kcoord d * x)
          (kcoord d * sigma (kcoord d) * y) :=
        hS_coe_eq_mk (conjS xS ⟨d, hd⟩) _ _ hout_valid hout_coord
  have hformula_conj_KW : ∀ x y : E,
      ValidPair x y → x ≠ 0 → y ≠ 0 →
      f (mk x y) = mk (x / y) y⁻¹ →
      ∀ d : G, d ∈ K ⊔ W →
        f (mk (kcoord d * x)
            (kcoord d * sigma (kcoord d) * y)) =
          mk ((kcoord d * x) /
              (kcoord d * sigma (kcoord d) * y))
            (kcoord d * sigma (kcoord d) * y)⁻¹ := by
    intro x y hxy hx hy hformula d hd
    have hbar_one : bar (1 : G) = 0 := by
      rw [hbar_of_mem_Q 1 Q.one_mem]
      have honeS :
          (⟨(1 : G), by simp [hSQ]⟩ : S) = 1 :=
        Subtype.ext rfl
      rw [honeS]
      exact congrArg Prod.fst hcoordPair_one
    have hxy_ne_one : mk x y ≠ 1 := by
      intro hone
      have hxcoord := hbar_mk x y hxy
      rw [hone, hbar_one] at hxcoord
      exact hx hxcoord.symm
    have hxyQ : mk x y ∈ Q := hmk_mem_Q x y hxy
    have hfxyQ : f (mk x y) ∈ Q :=
      (hf_mem (mk x y) hxyQ hxy_ne_one).1
    have htarget_valid : ValidPair (x / y) y⁻¹ := by
      by_contra hnotvalid
      rw [hformula] at hfxyQ
      have htQ : t ∈ Q := by
        simpa [mk, hnotvalid] using hfxyQ
      exact ht_not_mem_Q htQ
    let dt := rightConjugateElem d t
    obtain ⟨hdtKW, hdtcoord⟩ := hKW_t_coordinate d hd
    obtain ⟨_hbackKW, hbackcoord⟩ := hKW_t_coordinate dt hdtKW
    have ht_sq : t * t = 1 := by
      simpa [pow_two] using hA1.involution_t.sq_eq_one
    have hback : rightConjugateElem dt t = d := by
      simp only [dt, rightConjugateElem, hA1.involution_t.inv_eq_self]
      calc
        t * (t * d * t) * t = (t * t) * d * (t * t) := by group
        _ = d := by rw [ht_sq]; simp
    rw [hback] at hbackcoord
    have hsigma_dtcoord : sigma (kcoord dt) = (kcoord d)⁻¹ := by
      simpa using (congrArg Inv.inv hbackcoord).symm
    have hsigma_sigma_dcoord : sigma (sigma (kcoord d)) = kcoord d := by
      apply inv_injective
      rw [← hsigma_dtcoord, hdtcoord, map_inv₀]
    have htransport := PFchapter4section1.claim_H3 H Q D t f g h
      hA1.two_transitive hA1.point_stabilizer hA1.involution_t
      hA1.t_not_mem_H hA1.D_eq hA1.Q_normal_in_H hA1.Q_disjoint_D
      hA1.Q_sup_D hf_mem hg_mem hh_mem hcanonical_eq
      (mk x y) d hxyQ hxy_ne_one (hKW_le_D hd)
    have hdcoord_ne : kcoord d ≠ 0 := hkcoord_ne_zero d hd
    have hsigma_dcoord_ne : sigma (kcoord d) ≠ 0 :=
      (map_ne_zero sigma).2 hdcoord_ne
    calc
      f (mk (kcoord d * x)
          (kcoord d * sigma (kcoord d) * y)) =
          f (rightConjugateElem (mk x y) d) := by
            rw [hmk_conj_KW x y hxy d hd]
      _ = rightConjugateElem (f (mk x y)) dt := htransport
      _ = rightConjugateElem (mk (x / y) y⁻¹) dt := by rw [hformula]
      _ = mk (kcoord dt * (x / y))
          (kcoord dt * sigma (kcoord dt) * y⁻¹) :=
        hmk_conj_KW (x / y) y⁻¹ htarget_valid dt hdtKW
      _ = mk ((kcoord d * x) /
              (kcoord d * sigma (kcoord d) * y))
            (kcoord d * sigma (kcoord d) * y)⁻¹ := by
        rw [hdtcoord, map_inv₀, hsigma_sigma_dcoord]
        congr 1 <;> field_simp [hdcoord_ne, hsigma_dcoord_ne, hy]
  have hformula_image : ∀ x y : E,
      ValidPair x y → x ≠ 0 → y ≠ 0 →
      f (mk x y) = mk (x / y) y⁻¹ →
        f (mk (x / y) y⁻¹) =
          mk ((x / y) / y⁻¹) (y⁻¹)⁻¹ := by
    intro x y hxy hx hy hformula
    have hbar_one : bar (1 : G) = 0 := by
      rw [hbar_of_mem_Q 1 Q.one_mem]
      have honeS :
          (⟨(1 : G), by simp [hSQ]⟩ : S) = 1 :=
        Subtype.ext rfl
      rw [honeS]
      exact congrArg Prod.fst hcoordPair_one
    have hxy_ne_one : mk x y ≠ 1 := by
      intro hone
      have hxcoord := hbar_mk x y hxy
      rw [hone, hbar_one] at hxcoord
      exact hx hxcoord.symm
    have hdouble := PFchapter4section1.claim_H2 H Q D t f g h
      hA1.two_transitive hA1.point_stabilizer hA1.involution_t
      hA1.t_not_mem_H hA1.D_eq hA1.Q_normal_in_H hA1.Q_disjoint_D
      hA1.Q_sup_D hf_mem hg_mem hh_mem hcanonical_eq
      (mk x y) (hmk_mem_Q x y hxy) hxy_ne_one
    calc
      f (mk (x / y) y⁻¹) = f (f (mk x y)) := by rw [hformula]
      _ = mk x y := hdouble
      _ = mk ((x / y) / y⁻¹) (y⁻¹)⁻¹ := by
        congr 1 <;> field_simp [hy]
  have hclaim5_shift_field (x y u : E) (hy : y ≠ 0) (hu : u ≠ 0)
      (hyu : y + u ≠ 0) :
      (u⁻¹ * ((x / y) / (y⁻¹ + u⁻¹)),
          u⁻¹ ^ 2 * (y⁻¹ + u⁻¹)⁻¹ + u⁻¹) =
        (x / (y + u), (y + u)⁻¹) := by
    have hinner : y⁻¹ + u⁻¹ ≠ 0 := by
      intro hzero
      have hinv : y⁻¹ = u⁻¹ := CharTwo.add_eq_zero.mp hzero
      have hy_eq : y = u := inv_injective hinv
      exact hyu (by rw [hy_eq, CharTwo.add_self_eq_zero])
    apply Prod.ext
    · field_simp [hy, hu, hyu, hinner]
      rw [add_comm u y]
      field_simp [hyu]
    · field_simp [hy, hu, hyu, hinner]
      rw [add_comm u y]
      field_simp [hyu]
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hs_conj_kOf_inv_sq (a : Fˣ) :
      rightConjugateElem s (kOf a)⁻¹ = center (((a : F) ^ 2)⁻¹) := by
    have haKW : kOf a ∈ K ⊔ W := Subgroup.mem_sup_left (hkOf_mem a)
    have hainvK : (kOf a)⁻¹ ∈ K := K.inv_mem (hkOf_mem a)
    have hcoord :
        (((kwIso
            (⟨(kOf a)⁻¹, Subgroup.mem_sup_left hainvK⟩ :
              (K ⊔ W : Subgroup G)) :
                (K1 ⊔ W1 : Subgroup Eˣ)) : Eˣ) : E) =
          (((a⁻¹ : Fˣ) : F) : E) := by
      rw [← hkcoord_of_mem_KW (kOf a)⁻¹ (Subgroup.mem_sup_left hainvK),
        hkcoord_inv (kOf a) haKW, hkcoord_kOf]
      simp
    have haction := hcenter_conj_K_exact (kOf a)⁻¹ hainvK a⁻¹ hcoord 1
    rw [← hs_center, htheta] at haction
    simpa [pow_two] using haction
  let FormulaAt (q : S) : Prop :=
    f (q : G) =
      mk ((coordPair q).1 / (coordPair q).2) (coordPair q).2⁻¹
  have hcoord_first_ne (q : S) (hq0 : (q : G) ∉ Q0) :
      (coordPair q).1 ≠ 0 := by
    intro hzero
    exact hq0 (hmem_Q0_of_coordPair_zero q hzero)
  have hcoord_unitary (q : S) :
      (coordPair q).2 + sigma (coordPair q).2 =
        (coordPair q).1 * sigma (coordPair q).1 := by
    have hvalid := hvalid_of_coord q (coordPair q).1 (coordPair q).2 rfl
    rcases hvalid with hunitary | htwisted
    · exact hunitary.2
    · exact False.elim (htwisted.1 htheta)
  have hcoord_second_ne (q : S) (hq0 : (q : G) ∉ Q0) :
      (coordPair q).2 ≠ 0 := by
    intro hzero
    have hnorm := hcoord_unitary q
    rw [hzero, map_zero, add_zero] at hnorm
    have hxzero : (coordPair q).1 = 0 := by
      rcases mul_eq_zero.mp hnorm.symm with hx | hsx
      · exact hx
      · apply sigma.injective
        simpa using hsx
    exact hcoord_first_ne q hq0 hxzero
  have hformulaAt_conj (q : S) (hq0 : (q : G) ∉ Q0)
      (d : G) (hd : d ∈ K ⊔ W) (hqformula : FormulaAt q) :
      FormulaAt (conjS q ⟨d, hd⟩) := by
    let x := (coordPair q).1
    let y := (coordPair q).2
    have hxy : ValidPair x y := hvalid_of_coord q x y rfl
    have hx : x ≠ 0 := hcoord_first_ne q hq0
    have hy : y ≠ 0 := hcoord_second_ne q hq0
    have hq_mk : (q : G) = mk x y := hS_coe_eq_mk q x y hxy rfl
    have hformula_mk : f (mk x y) = mk (x / y) y⁻¹ := by
      simpa [FormulaAt, x, y, hq_mk] using hqformula
    have htransport :=
      hformula_conj_KW x y hxy hx hy hformula_mk d hd
    have hout_coord := hconjS_coord_kcoord q d hd
    have hout_valid :
        ValidPair (kcoord d * x)
          (kcoord d * sigma (kcoord d) * y) := by
      apply hvalid_of_coord (conjS q ⟨d, hd⟩) _ _
      simpa [x, y] using hout_coord
    have hout_mk : (conjS q ⟨d, hd⟩ : S) =
        mk (kcoord d * x)
          (kcoord d * sigma (kcoord d) * y) := by
      apply hS_coe_eq_mk (conjS q ⟨d, hd⟩) _ _ hout_valid
      simpa [x, y] using hout_coord
    unfold FormulaAt
    rw [hout_coord]
    simpa [x, y, hout_mk] using htransport
  have hformulaAt_image (q : S) (hq0 : (q : G) ∉ Q0)
      (hqformula : FormulaAt q) :
      ∃ fq : S,
        (fq : G) = f (q : G) ∧
          coordPair fq =
            ((coordPair q).1 / (coordPair q).2, (coordPair q).2⁻¹) ∧
          FormulaAt fq := by
    let x := (coordPair q).1
    let y := (coordPair q).2
    have hxy : ValidPair x y := hvalid_of_coord q x y rfl
    have hx : x ≠ 0 := hcoord_first_ne q hq0
    have hy : y ≠ 0 := hcoord_second_ne q hq0
    have hq_mk : (q : G) = mk x y := hS_coe_eq_mk q x y hxy rfl
    have hq_ne_one : (q : G) ≠ 1 := by
      intro hone
      exact hq0 (hone ▸ Q0.one_mem)
    have hfqQ : f (q : G) ∈ Q :=
      (hf_mem (q : G) (by simpa [hSQ] using q.property) hq_ne_one).1
    have htarget_valid : ValidPair (x / y) y⁻¹ := by
      by_contra hnotvalid
      have htQ : t ∈ Q := by
        have hqformula' : f (q : G) = mk (x / y) y⁻¹ := by
          simpa [FormulaAt, x, y] using hqformula
        rw [hqformula'] at hfqQ
        simpa [mk, hnotvalid] using hfqQ
      exact ht_not_mem_Q htQ
    let fq : S := ⟨f (q : G), by simpa [hSQ] using hfqQ⟩
    have hfq_mk : (fq : G) = mk (x / y) y⁻¹ := by
      simpa [fq, FormulaAt, x, y] using hqformula
    have hfq_coord : coordPair fq = (x / y, y⁻¹) := by
      have hsub : fq = mkS (x / y) y⁻¹ htarget_valid := by
        apply Subtype.ext
        rw [hfq_mk, hmk_of_valid]
      rw [hsub, hmkS_coord]
    have hfq_formula : FormulaAt fq := by
      have himage := hformula_image x y hxy hx hy (by
        simpa [hq_mk, FormulaAt, x, y] using hqformula)
      unfold FormulaAt
      rw [hfq_coord]
      simpa [hfq_mk] using himage
    exact ⟨fq, rfl, by simpa [x, y] using hfq_coord, hfq_formula⟩
  have hformulaAt_of_sameOrbit (r : S) (hr0 : (r : G) ∉ Q0)
      (hrformula : ∀ u : F, FormulaAt (r * centerS u)) :
      ∀ q : S, SameOrbit (q : G) (r : G) → FormulaAt q := by
    intro q hsame
    rcases hsame with ⟨d, q0, hd, hq0, hqeq⟩
    have hdD : d ∈ D := hKW_le_D hd
    let q0pre : G := rightConjugateElem q0 d⁻¹
    have hq0pre : q0pre ∈ Q0 :=
      hQ0_conj_D q0 d⁻¹ hq0 (D.inv_mem hdD)
    obtain ⟨u, hu⟩ := hcenter_surjective q0pre hq0pre
    have hq0_back : rightConjugateElem (center u) d = q0 := by
      rw [hu]
      simp [q0pre, rightConjugateElem, mul_assoc]
    have hbase0 : ((r * centerS u : S) : G) ∉ Q0 := by
      intro hbase
      apply hr0
      have hr_eq : (r : G) = ((r * centerS u : S) : G) * (center u)⁻¹ := by
        simp [center]
      rw [hr_eq]
      exact Q0.mul_mem hbase (Q0.inv_mem (hcenter_mem_Q0 u))
    have hq_sub : q = conjS (r * centerS u) ⟨d, hd⟩ := by
      apply Subtype.ext
      calc
        (q : G) = rightConjugateElem (r : G) d * q0 := hqeq
        _ = rightConjugateElem (r : G) d *
            rightConjugateElem (center u) d := by rw [hq0_back]
        _ = rightConjugateElem ((r : G) * center u) d := by
          simp [rightConjugateElem, mul_assoc]
        _ = rightConjugateElem ((r * centerS u : S) : G) d := by
          simp [center]
        _ = (conjS (r * centerS u) ⟨d, hd⟩ : S) :=
          (hconjS_coe (r * centerS u) ⟨d, hd⟩).symm
    rw [hq_sub]
    exact hformulaAt_conj (r * centerS u) hbase0 d hd (hrformula u)
  have hsameOrbit_noncentral (q r : S) (hr0 : (r : G) ∉ Q0)
      (hsame : SameOrbit (q : G) (r : G)) : (q : G) ∉ Q0 := by
    rcases hsame with ⟨d, q0, hd, hq0, hqeq⟩
    intro hqQ0
    have hrconjQ0 : rightConjugateElem (r : G) d ∈ Q0 := by
      have heq : rightConjugateElem (r : G) d = (q : G) * q0⁻¹ := by
        rw [hqeq]
        simp [mul_assoc]
      rw [heq]
      exact Q0.mul_mem hqQ0 (Q0.inv_mem hq0)
    have hbackQ0 := hQ0_conj_D (rightConjugateElem (r : G) d) d⁻¹
      hrconjQ0 (D.inv_mem (hKW_le_D hd))
    apply hr0
    simpa [rightConjugateElem, mul_assoc] using hbackQ0
  have homegaS_center_formula : ∀ u : F,
      FormulaAt (omegaS * centerS u) := by
    intro u
    let q : S := omegaS * centerS u
    have hq_coord : coordPair q = (omegaBar, omegaY + (u : E)) := by
      simp [q, hcoordPair_mul, hcenter_coordPair, omegaBar, omegaY,
        hphi_zero_right]
    have hq0 : (q : G) ∉ Q0 := by
      intro hqQ0
      apply homegaChosen.2
      have homega_eq : omegaChosen = (q : G) * (center u)⁻¹ := by
        simp [q, omegaS, center, mul_assoc]
      rw [homega_eq]
      exact Q0.mul_mem hqQ0 (Q0.inv_mem (hcenter_mem_Q0 u))
    have hy : omegaY + (u : E) ≠ 0 := by
      simpa [hq_coord] using hcoord_second_ne q hq0
    have hunitary :
        (omegaY + (u : E)) + sigma (omegaY + (u : E)) =
          omegaBar * sigma omegaBar := by
      simpa [hq_coord] using hcoord_unitary q
    have hvalid : ValidPair omegaBar (omegaY + (u : E)) :=
      hvalid_of_coord q _ _ hq_coord
    have hq_mk : (q : G) = mk omegaBar (omegaY + (u : E)) :=
      hS_coe_eq_mk q _ _ hvalid hq_coord
    have hformula := hclaim4 (omegaY + (u : E)) hy hunitary
    unfold FormulaAt
    rw [hq_coord]
    calc
      f (q : G) = f (mk omegaBar (omegaY + (u : E))) :=
        congrArg f hq_mk
      _ = mk (omegaBar / (omegaY + (u : E)))
          (omegaY + (u : E))⁻¹ := hformula
  have homega_orbit_formula : ∀ q : S,
      SameOrbit (q : G) omegaChosen → FormulaAt q := by
    intro q hsame
    exact hformulaAt_of_sameOrbit omegaS homegaChosen.2
      homegaS_center_formula q (by simpa [omegaS] using hsame)
  have hcrossing_representative : ∀ j : ℕ,
      1 ≤ j → j ≤ n → j ≠ i →
        ∃ rho : S,
          (rho : G) ∉ Q0 ∧
            SameOrbit (rho : G) (omegaSeed j) ∧
              SameOrbit (f (rho : G)) omegaChosen := by
    intro j hj_one hj_n hji
    obtain ⟨x0, y0, k, hx0, hy0, hk, hcross⟩ :=
      PFchapter4section2.claim_8_exists_crossing_in_K
        H D Q K V W Q0 S Q1 (K ⊔ W) t s omegaChosen f g h
        (Nat.card W) n i j omegaSeed hsection3 hC1 hC2
        hA1.two_transitive hA1.point_stabilizer hA1.involution_t
        hA1.t_not_mem_H hA1.D_eq hA1.Q_normal_in_H hA1.Q_disjoint_D
        hA1.Q_sup_D hf_mem hg_mem hh_mem hcanonical_eq rfl rfl hn
        ⟨hi_one, hi_n⟩ ⟨hj_one, hj_n⟩ hji
        horbit_representativesSeed homegaSeed_i.symm
    let xS : S :=
      ⟨x0, by simpa [hSQ] using hsection3.section2.Q0_le_Q hx0⟩
    let yS : S :=
      ⟨y0, by simpa [hSQ] using hsection3.section2.Q0_le_Q hy0⟩
    let omegaJS : S :=
      ⟨omegaSeed j, by
        simpa [hSQ] using (homegaSeed_valid j hj_one hj_n).1⟩
    let kKW : (K ⊔ W : Subgroup G) := ⟨k, Subgroup.mem_sup_left hk⟩
    let aS : S := omegaS * xS
    let bS : S := omegaJS * yS
    let rho : S := conjS bS kKW
    have ha0 : (aS : G) ∉ Q0 := by
      intro haQ0
      apply homegaChosen.2
      have homega_eq : omegaChosen = (aS : G) * x0⁻¹ := by
        simp [aS, omegaS, xS, mul_assoc]
      rw [homega_eq]
      exact Q0.mul_mem haQ0 (Q0.inv_mem hx0)
    have hb0 : (bS : G) ∉ Q0 := by
      intro hbQ0
      exact (homegaSeed_valid j hj_one hj_n).2 (by
        have homegaj_eq : omegaSeed j = (bS : G) * y0⁻¹ := by
          simp [bS, omegaJS, yS, mul_assoc]
        rw [homegaj_eq]
        exact Q0.mul_mem hbQ0 (Q0.inv_mem hy0))
    have hrho0 : (rho : G) ∉ Q0 := by
      have hbfirst := hcoord_first_ne bS hb0
      have hrcoord := hconjS_coord_kcoord bS k
        (Subgroup.mem_sup_left hk)
      intro hrQ0
      have hrzero := hcoordPair_zero_of_mem_Q0 rho hrQ0
      rw [hrcoord] at hrzero
      exact hbfirst (by
        exact (mul_eq_zero.mp hrzero).resolve_left
          (hkcoord_ne_zero k (Subgroup.mem_sup_left hk)))
    have hcross' : f (aS : G) = (rho : G) := by
      calc
        f (aS : G) = rightConjugateElem (bS : G) k := by
          simpa [aS, bS, omegaS, omegaJS, xS, yS] using hcross
        _ = (rho : G) := (hconjS_coe bS kKW).symm
    have ha_ne_one : (aS : G) ≠ 1 := by
      intro hone
      exact ha0 (hone ▸ Q0.one_mem)
    have hdouble_a := PFchapter4section1.claim_H2 H Q D t f g h
      hA1.two_transitive hA1.point_stabilizer hA1.involution_t
      hA1.t_not_mem_H hA1.D_eq hA1.Q_normal_in_H hA1.Q_disjoint_D
      hA1.Q_sup_D hf_mem hg_mem hh_mem hcanonical_eq (aS : G)
      (by simpa [hSQ] using aS.property) ha_ne_one
    have hfrho : f (rho : G) = (aS : G) := by
      rw [← hcross']
      exact hdouble_a
    have hrho_orbit : SameOrbit (rho : G) (omegaSeed j) := by
      let y0k := rightConjugateElem y0 k
      have hy0k : y0k ∈ Q0 :=
        hQ0_conj_D y0 k hy0 (hsection3.section2.K_le_D hk)
      refine ⟨k, y0k, Subgroup.mem_sup_left hk, hy0k, ?_⟩
      calc
        (rho : G) = rightConjugateElem (bS : G) k :=
          hconjS_coe bS kKW
        _ = rightConjugateElem (omegaSeed j * y0) k := by
          simp [bS, omegaJS, yS]
        _ = rightConjugateElem (omegaSeed j) k * y0k := by
          simp [y0k, rightConjugateElem, mul_assoc]
    have hfrho_orbit : SameOrbit (f (rho : G)) omegaChosen := by
      refine ⟨1, x0, (K ⊔ W).one_mem, hx0, ?_⟩
      rw [hfrho]
      simp [aS, omegaS, xS, rightConjugateElem]
    exact ⟨rho, hrho0, hrho_orbit, hfrho_orbit⟩
  have hformulaAt_of_image_selected (rho : S) (hrho0 : (rho : G) ∉ Q0)
      (himage : SameOrbit (f (rho : G)) omegaChosen) : FormulaAt rho := by
    have hrho_ne_one : (rho : G) ≠ 1 := by
      intro hone
      exact hrho0 (hone ▸ Q0.one_mem)
    have hfrho_mem := hf_mem (rho : G)
      (by simpa [hSQ] using rho.property) hrho_ne_one
    let frho : S := ⟨f (rho : G), by simpa [hSQ] using hfrho_mem.1⟩
    have hfrho_orbit : SameOrbit (frho : G) omegaChosen := by
      simpa [frho] using himage
    have hfrho0 : (frho : G) ∉ Q0 :=
      hsameOrbit_noncentral frho omegaS homegaChosen.2 (by
        simpa [omegaS] using hfrho_orbit)
    have hfrho_formula : FormulaAt frho :=
      homega_orbit_formula frho hfrho_orbit
    obtain ⟨ffrho, hffrho_coe, _hffrho_coord, hffrho_formula⟩ :=
      hformulaAt_image frho hfrho0 hfrho_formula
    have hdouble := PFchapter4section1.claim_H2 H Q D t f g h
      hA1.two_transitive hA1.point_stabilizer hA1.involution_t
      hA1.t_not_mem_H hA1.D_eq hA1.Q_normal_in_H hA1.Q_disjoint_D
      hA1.Q_sup_D hf_mem hg_mem hh_mem hcanonical_eq (rho : G)
      (by simpa [hSQ] using rho.property) hrho_ne_one
    have hffrho_eq : ffrho = rho := by
      apply Subtype.ext
      calc
        (ffrho : G) = f (frho : G) := hffrho_coe
        _ = f (f (rho : G)) := by rfl
        _ = (rho : G) := hdouble
    rw [hffrho_eq] at hffrho_formula
    exact hffrho_formula
  have hcenter_formula_of_image_selected (rho : S)
      (hrho0 : (rho : G) ∉ Q0)
      (himage : SameOrbit (f (rho : G)) omegaChosen) :
      ∀ u : F, FormulaAt (rho * centerS u) := by
    have hrho_formula : FormulaAt rho :=
      hformulaAt_of_image_selected rho hrho0 himage
    have hrho_ne_one : (rho : G) ≠ 1 := by
      intro hone
      exact hrho0 (hone ▸ Q0.one_mem)
    have hfrho_mem := hf_mem (rho : G)
      (by simpa [hSQ] using rho.property) hrho_ne_one
    let frho : S := ⟨f (rho : G), by simpa [hSQ] using hfrho_mem.1⟩
    have hfrho_orbit : SameOrbit (frho : G) omegaChosen := by
      simpa [frho] using himage
    have hfrho0 : (frho : G) ∉ Q0 :=
      hsameOrbit_noncentral frho omegaS homegaChosen.2 (by
        simpa [omegaS] using hfrho_orbit)
    let x := (coordPair rho).1
    let y := (coordPair rho).2
    have hy : y ≠ 0 := hcoord_second_ne rho hrho0
    obtain ⟨frho', hfrho'_coe, hfrho'_coord, _hfrho'_formula⟩ :=
      hformulaAt_image rho hrho0 hrho_formula
    have hfrho'_eq : frho' = frho := by
      apply Subtype.ext
      simpa [frho] using hfrho'_coe
    have hfrho_coord : coordPair frho = (x / y, y⁻¹) := by
      rw [← hfrho'_eq]
      simpa [x, y] using hfrho'_coord
    intro u
    by_cases hu : u = 0
    · subst u
      simpa [hcenterS_zero] using hrho_formula
    have huE : (u : E) ≠ 0 := by
      intro hzero
      apply hu
      apply Subtype.ext
      simpa using hzero
    let rhoU : S := rho * centerS u
    have hrhoU_coord : coordPair rhoU = (x, y + (u : E)) := by
      simp [rhoU, hcoordPair_mul, hcenter_coordPair, x, y,
        hphi_zero_right]
    have hrhoU0 : (rhoU : G) ∉ Q0 := by
      intro hshift0
      apply hrho0
      have hrho_eq : (rho : G) = (rhoU : G) * (center u)⁻¹ := by
        simp [rhoU, center, mul_assoc]
      rw [hrho_eq]
      exact Q0.mul_mem hshift0 (Q0.inv_mem (hcenter_mem_Q0 u))
    have hyu : y + (u : E) ≠ 0 := by
      simpa [hrhoU_coord] using hcoord_second_ne rhoU hrhoU0
    obtain ⟨b, hb⟩ := hsquare_surjective u
    have hbne : b ≠ 0 := by
      intro hzero
      apply hu
      rw [← hb, hzero]
      simp
    let bUnit : Fˣ := Units.mk0 b hbne
    let a : G := kOf bUnit
    have haK : a ∈ K := hkOf_mem bUnit
    have haKW : a ∈ K ⊔ W := Subgroup.mem_sup_left haK
    have hcenter_a : rightConjugateElem s a = center u := by
      have haction := hs_conj_kOf_sq bUnit
      simpa [a, bUnit, hb] using haction
    have hcenter_ainv : rightConjugateElem s a⁻¹ = center u⁻¹ := by
      have haction := hs_conj_kOf_inv_sq bUnit
      simpa [a, bUnit, hb] using haction
    let inner : S := frho * centerS u⁻¹
    have hinner_frho : SameOrbit (inner : G) (frho : G) := by
      refine ⟨1, center u⁻¹, (K ⊔ W).one_mem,
        hcenter_mem_Q0 u⁻¹, ?_⟩
      simp [inner, center, rightConjugateElem]
    have hinner_orbit : SameOrbit (inner : G) omegaChosen :=
      hsame_trans _ _ _ hinner_frho hfrho_orbit
    have hinner0 : (inner : G) ∉ Q0 :=
      hsameOrbit_noncentral inner omegaS homegaChosen.2 (by
        simpa [omegaS] using hinner_orbit)
    have hinner_formula : FormulaAt inner :=
      homega_orbit_formula inner hinner_orbit
    have hinner_coord :
        coordPair inner = (x / y, y⁻¹ + (u : E)⁻¹) := by
      rw [show inner = frho * centerS u⁻¹ by rfl,
        hcoordPair_mul, hfrho_coord, hcenter_coordPair, hphi_zero_right]
      simp
    obtain ⟨finner, hfinner_coe, hfinner_coord0, _hfinner_formula⟩ :=
      hformulaAt_image inner hinner0 hinner_formula
    have hfinner_coord : coordPair finner =
        ((x / y) / (y⁻¹ + (u : E)⁻¹),
          (y⁻¹ + (u : E)⁻¹)⁻¹) := by
      simpa [hinner_coord] using hfinner_coord0
    let d : G := a⁻¹ ^ 2
    have hdK : d ∈ K := K.pow_mem (K.inv_mem haK) 2
    have hdKW : d ∈ K ⊔ W := Subgroup.mem_sup_left hdK
    have hbE : ((b : E) ^ 2) = (u : E) := by
      exact congrArg (fun z : F => (z : E)) hb
    have hdcoord : kcoord d = (u : E)⁻¹ := by
      rw [show d = a⁻¹ ^ 2 by rfl,
        hkcoord_pow a⁻¹ ((K ⊔ W).inv_mem haKW) 2,
        hkcoord_inv a haKW]
      change (kcoord (kOf bUnit))⁻¹ ^ 2 = (u : E)⁻¹
      rw [hkcoord_kOf]
      change ((b : E)⁻¹) ^ 2 = (u : E)⁻¹
      rw [inv_pow, hbE]
    have hsigmadcoord : sigma (kcoord d) = (u : E)⁻¹ := by
      rw [hdcoord, map_inv₀]
      simpa [htheta] using congrArg Inv.inv (hsigmaF u)
    let acted : S := conjS finner ⟨d, hdKW⟩
    have hacted_coord : coordPair acted =
        ((u : E)⁻¹ * ((x / y) / (y⁻¹ + (u : E)⁻¹)),
          (u : E)⁻¹ ^ 2 * (y⁻¹ + (u : E)⁻¹)⁻¹) := by
      have hcoord := hconjS_coord_kcoord finner d hdKW
      rw [hfinner_coord, hsigmadcoord, hdcoord] at hcoord
      simpa [acted, pow_two, mul_assoc] using hcoord
    let rhs : S := acted * centerS u⁻¹
    have hrhs_coord : coordPair rhs =
        (x / (y + (u : E)), (y + (u : E))⁻¹) := by
      calc
        coordPair rhs =
            ((u : E)⁻¹ * ((x / y) / (y⁻¹ + (u : E)⁻¹)),
              (u : E)⁻¹ ^ 2 * (y⁻¹ + (u : E)⁻¹)⁻¹ + (u : E)⁻¹) := by
          rw [show rhs = acted * centerS u⁻¹ by rfl,
            hcoordPair_mul, hacted_coord, hcenter_coordPair,
            hphi_zero_right]
          simp
        _ = (x / (y + (u : E)), (y + (u : E))⁻¹) :=
          hclaim5_shift_field x y (u : E) hy huE hyu
    have hclaim2 := PFchapter4section2.claim_2
      H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
      hA1.two_transitive hA1.point_stabilizer hA1.involution_t
      hA1.t_not_mem_H hA1.D_eq hA1.Q_normal_in_H hA1.Q_disjoint_D
      hA1.Q_sup_D hf_mem hg_mem hh_mem hcanonical_eq
      (rho : G) a (by simpa [hSQ] using rho.property) hrho0 haK
    have hf_rhoU : f (rhoU : G) = (rhs : G) := by
      calc
        f (rhoU : G) =
            f ((rho : G) * rightConjugateElem s a) := by
          rw [hcenter_a]
          rfl
        _ = rightConjugateElem
              (f (f (rho : G) * rightConjugateElem s a⁻¹)) d *
                rightConjugateElem s a⁻¹ := hclaim2
        _ = rightConjugateElem (f (inner : G)) d * center u⁻¹ := by
          rw [hcenter_ainv]
          rfl
        _ = rightConjugateElem (finner : G) d * center u⁻¹ := by
          rw [hfinner_coe]
        _ = (acted : G) * center u⁻¹ := by
          rw [hconjS_coe finner ⟨d, hdKW⟩]
        _ = (rhs : G) := by rfl
    have hrhs_valid : ValidPair (x / (y + (u : E)))
        (y + (u : E))⁻¹ :=
      hvalid_of_coord rhs _ _ hrhs_coord
    have hrhs_mk : (rhs : G) =
        mk (x / (y + (u : E))) (y + (u : E))⁻¹ :=
      hS_coe_eq_mk rhs _ _ hrhs_valid hrhs_coord
    unfold FormulaAt
    rw [hrhoU_coord]
    exact hf_rhoU.trans hrhs_mk
  have hformulaAt_all (q : S) (hq0 : (q : G) ∉ Q0) : FormulaAt q := by
    rcases homegaSeed_complete (q : G) (by simpa [hSQ] using q.property) hq0 with
      ⟨j, hj_one, hj_n, d, q0, hd, hq0_mem, hqeq⟩
    have hq_orbit : SameOrbit (q : G) (omegaSeed j) :=
      ⟨d, q0, hd, hq0_mem, hqeq⟩
    by_cases hji : j = i
    · subst j
      exact homega_orbit_formula q (by
        simpa [homegaSeed_i] using hq_orbit)
    · obtain ⟨rho, hrho0, hrho_orbit, hfrho_orbit⟩ :=
        hcrossing_representative j hj_one hj_n hji
      have hrho_center : ∀ u : F, FormulaAt (rho * centerS u) :=
        hcenter_formula_of_image_selected rho hrho0 hfrho_orbit
      apply hformulaAt_of_sameOrbit rho hrho0 hrho_center q
      exact hsame_trans (q : G) (omegaSeed j) (rho : G) hq_orbit
        (hsame_symm (rho : G) (omegaSeed j) hrho_orbit)
  have hclaim5 : ∀ x y : E, ValidPair x y → mk x y ∉ Q0 →
      f (mk x y) = mk (x / y) y⁻¹ := by
    intro x y hxy hxy0
    let q : S := mkS x y hxy
    have hq_coord : coordPair q = (x, y) := hmkS_coord x y hxy
    have hq_mk : (q : G) = mk x y := (hmk_of_valid x y hxy).symm
    have hq0 : (q : G) ∉ Q0 := by simpa [hq_mk] using hxy0
    have hqformula := hformulaAt_all q hq0
    unfold FormulaAt at hqformula
    rw [hq_coord] at hqformula
    simpa [hq_mk] using hqformula
  have hformula' :
      ∀ x y : E, y ≠ 0 → mk x y ∈ Q → mk x y ∉ Q0 →
        f (mk x y) = mk (x / y) y⁻¹ := by
    intro x y _hy hmkQ hmkQ0
    by_cases hvalid : ValidPair x y
    · exact hclaim5 x y hvalid hmkQ0
    · have htQ : t ∈ Q := by
        simpa [mk, hvalid] using hmkQ
      exact False.elim (ht_not_mem_Q htQ)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Pambient, hPambient_le_Q⟩ :=
    PFchapter1section1.proposition_1_c H D Q t hA1
  have hQ_eq_Pambient : Q = (Pambient : Subgroup G) :=
    Pambient.is_maximal' hQ_two hPambient_le_Q
  obtain ⟨E4, hE4card, hE4sq⟩ :=
    TwoRankAtLeastTwo.exists_subgroup hsection3.section2.hA.A3
  have hE4_two : IsPGroup 2 E4 := by
    apply IsPGroup.of_card (n := 2)
    rw [hE4card]
    norm_num
  obtain ⟨PE4, hE4_le_PE4⟩ := hE4_two.exists_le_sylow
  obtain ⟨cE4, hcE4⟩ := MulAction.exists_smul_eq G PE4 Pambient
  let E4' : Subgroup G := E4.map (MulAut.conj cE4).toMonoidHom
  have hE4'_le_Q : E4' ≤ Q := by
    rw [hQ_eq_Pambient, ← hcE4, Sylow.coe_subgroup_smul]
    exact Subgroup.map_mono hE4_le_PE4
  have hE4'_le_Q0 : E4' ≤ Q0 := by
    intro x hxE4'
    rw [Subgroup.mem_map] at hxE4'
    rcases hxE4' with ⟨y, hyE4, rfl⟩
    have hy_sq : y ^ 2 = 1 := by
      simpa using congrArg Subtype.val (hE4sq ⟨y, hyE4⟩)
    have hconj_sq : (MulAut.conj cE4 y) ^ 2 = 1 := by
      rw [← map_pow, hy_sq, map_one]
    by_cases hconj_one : MulAut.conj cE4 y = 1
    · simp [hconj_one]
    · apply (hsection3.section2.Q0_def _).2
      exact Or.inr
        ⟨hA1.Q_le_H (hE4'_le_Q (Subgroup.mem_map_of_mem _ hyE4)),
          hconj_one, hconj_sq⟩
  have hE4'card : Nat.card E4' = 4 := by
    calc
      Nat.card E4' = Nat.card E4 :=
        (Nat.card_congr
          ((MulAut.conj cE4).subgroupMap E4).toEquiv).symm
      _ = 4 := hE4card
  let E4toQ0 : E4' → Q0 := fun x => ⟨x, hE4'_le_Q0 x.property⟩
  have hE4toQ0_injective : Function.Injective E4toQ0 := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : Q0 => (z : G)) hxy
  have hQ0card_ge_four : 4 ≤ Nat.card Q0 := by
    rw [← hE4'card]
    exact Nat.card_le_card_of_injective E4toQ0 hE4toQ0_injective
  have hFcard_gt : 2 < Nat.card F := by
    rw [hcardF]
    omega
  have hfixed_mem (y : E) (hy : sigma y = y) : y ∈ F := by
    apply hmem_F_of_frobenius_fixed y
    exact (hsigmaFrob htheta y).symm.trans hy
  obtain ⟨J, hJconj, hJstandard, hEcard, hfixedCard⟩ :=
    exists_standardHermitianForm F sigma hfinrank
      (fun a => by simpa [htheta] using hsigmaF a)
      (hsigmaFrob htheta) hfixed_mem
  obtain ⟨s1Coord, hs1Coord⟩ :=
    exists_unitaryCoordinateMulEquiv F theta sigma phi coord hcoordMul
      htheta (hphiThetaOne htheta) J hJconj
  let qToS : Q ≃* S := MulEquiv.subgroupCongr hSQ.symm
  let qCoord : Q ≃* External.hermitianUnipotentCoord J :=
    qToS.trans (sIso.trans s1Coord)
  have hqCoord_apply (x : Q) :
      (((qCoord x : External.hermitianUnipotentCoord J) : E × E)) =
        coordPair (qToS x) := by
    change
      (((s1Coord (sIso (qToS x)) :
          External.hermitianUnipotentCoord J) : E × E)) =
        ((coord (sIso (qToS x)) :
          {p : E × E //
            (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
              (theta ≠ 1 ∧ p.2 ∈ F)}) : E × E)
    exact hs1Coord (sIso (qToS x))
  have hfCoord : ∀ (x : Q) (hx : x ≠ 1),
      (((qCoord ⟨f x, (hf_mem x x.property (by simpa using hx)).1⟩ :
          External.hermitianUnipotentCoord J) : E × E)) =
        ((qCoord x).1.1 / (qCoord x).1.2, (qCoord x).1.2⁻¹) := by
    intro x hx
    have hxG : (x : G) ≠ 1 := by simpa using hx
    let xS : S := qToS x
    let fxQ : Q := ⟨f x, (hf_mem x x.property hxG).1⟩
    change
      (((qCoord fxQ : External.hermitianUnipotentCoord J) : E × E)) =
        ((qCoord x).1.1 / (qCoord x).1.2, (qCoord x).1.2⁻¹)
    by_cases hxQ0 : (x : G) ∈ Q0
    · obtain ⟨u, hu⟩ := hcenter_surjective (x : G) hxQ0
      have hu0 : u ≠ 0 := by
        intro hu_zero
        apply hxG
        rw [← hu, hu_zero, hcenter_zero]
      obtain ⟨b, hb⟩ := hsquare_surjective u
      have hb0 : b ≠ 0 := by
        intro hb_zero
        apply hu0
        rw [← hb, hb_zero]
        simp
      let bUnit : Fˣ := Units.mk0 b hb0
      have hbUnit_sq : (bUnit : F) ^ 2 = u := by
        simpa [bUnit] using hb
      have hx_conj : rightConjugateElem s (kOf bUnit) = center u := by
        rw [hs_conj_kOf, htheta]
        simpa [pow_two] using congrArg center hbUnit_sq
      have hclaim1 :=
        PFchapter4section2.claim_1_a H D Q K V W Q0 S Q1 t s f g h
          hsection3 hC1 hC2 hA1.two_transitive hA1.point_stabilizer
          hA1.involution_t hA1.t_not_mem_H hA1.D_eq
          hA1.Q_normal_in_H hA1.Q_disjoint_D hA1.Q_sup_D
          hf_mem hg_mem hh_mem hcanonical_eq (kOf bUnit) (hkOf_mem bUnit)
      have hfx : f (x : G) = center u⁻¹ := by
        calc
          f (x : G) = f (center u) := congrArg f hu.symm
          _ = f (rightConjugateElem s (kOf bUnit)) := by rw [hx_conj]
          _ = rightConjugateElem s (kOf bUnit)⁻¹ := hclaim1.1
          _ = center (((bUnit : F) ^ 2)⁻¹) :=
            hs_conj_kOf_inv_sq bUnit
          _ = center u⁻¹ := by rw [hbUnit_sq]
      have hxS : qToS x = centerS u := by
        apply Subtype.ext
        change (x : G) = center u
        exact hu.symm
      have hfxS : qToS fxQ = centerS u⁻¹ := by
        apply Subtype.ext
        change f (x : G) = center u⁻¹
        exact hfx
      calc
        (((qCoord fxQ : External.hermitianUnipotentCoord J) : E × E)) =
            coordPair (qToS fxQ) := hqCoord_apply fxQ
        _ = coordPair (centerS u⁻¹) := by rw [hfxS]
        _ = ((0 : E) / (u : E), (u : E)⁻¹) := by
          simpa [hu0] using hcenter_coordPair u⁻¹
        _ = ((qCoord x).1.1 / (qCoord x).1.2,
            (qCoord x).1.2⁻¹) := by
          rw [hqCoord_apply, hxS, hcenter_coordPair]
    · have hxS0 : (xS : G) ∉ Q0 := by
        simpa [xS, qToS] using hxQ0
      have hxFormula := hformulaAt_all xS hxS0
      obtain ⟨fq, hfq, hfqCoord, _hfqFormula⟩ :=
        hformulaAt_image xS hxS0 hxFormula
      have hfxS : qToS fxQ = fq := by
        apply Subtype.ext
        change f (x : G) = (fq : G)
        simpa [xS, qToS] using hfq.symm
      calc
        (((qCoord fxQ : External.hermitianUnipotentCoord J) : E × E)) =
            coordPair (qToS fxQ) := hqCoord_apply fxQ
        _ = coordPair fq := by rw [hfxS]
        _ = ((coordPair xS).1 / (coordPair xS).2,
            (coordPair xS).2⁻¹) := hfqCoord
        _ = ((qCoord x).1.1 / (qCoord x).1.2,
            (qCoord x).1.2⁻¹) := by
          rw [hqCoord_apply]
  obtain ⟨rankOneBase, hHrankOneBase⟩ := hA1.point_stabilizer
  letI : FaithfulSMul G Omega := hsection3.section2.hA.A2
  have hresidualIso :
      Nonempty (twoPrimeResidual G ≃*
        ProjectiveSpecialUnitaryMatrixGroup J) :=
    unitaryModelEquiv_of_rankOneCoordinates H Q D t f g h rankOneBase
      hA1.two_transitive hHrankOneBase hA1.involution_t hA1.t_not_mem_H
      hA1.D_eq hA1.Q_normal_in_H hA1.Q_disjoint_D hA1.Q_sup_D
      hf_mem hg_mem hh_mem hcanonical_eq J (Nat.card F) hFcard_gt
      hEcard hfixedCard hJstandard qCoord hfCoord
      ⟨Pambient, hQ_eq_Pambient⟩
  have hcorollary :
      ∃ (q : ℕ) (E0 : Type) (_ : Field E0) (_ : Finite E0)
          (J : HermitianForm 3 E0),
        J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
        Nat.card E0 = q ^ 2 ∧
        Nat.card {x : E0 // J.conj x = x} = q ∧
        q = Nat.card Q0 ∧
        Nonempty (twoPrimeResidual G ≃* ProjectiveSpecialUnitaryMatrixGroup J) := by
    exact ⟨Nat.card F, E, inferInstance, inferInstance, J, hJstandard,
      hEcard, hfixedCard, hcardF, hresidualIso⟩
  obtain ⟨q, E0, hE0Field, hE0Finite, J, hJstandard, hE0card,
      hfixedCard, hqQ0, hresidualIso⟩ := hcorollary
  have hFcard_data :
      ∃ n : ℕ+, Nat.Prime 2 ∧ Nat.card F = 2 ^ (n : ℕ) := by
    letI : Fintype F := Fintype.ofFinite F
    obtain ⟨nF, hprime_two, hFcard_pow⟩ := FiniteField.card F 2
    exact ⟨nF, hprime_two, by
      simpa [Nat.card_eq_fintype_card] using hFcard_pow⟩
  obtain ⟨nF, _hprime_two, hFcard_pow⟩ := hFcard_data
  have hq_pow : ∃ n : ℕ, q = 2 ^ n := by
    refine ⟨nF, ?_⟩
    calc
      q = Nat.card Q0 := hqQ0
      _ = Nat.card F := hcardF.symm
      _ = 2 ^ (nF : ℕ) := hFcard_pow
  have hq_gt : 2 < q := by
    rw [hqQ0]
    omega
  let L : Subgroup G := twoPrimeResidual G
  letI : L.Normal := by
    simpa [L] using
      (PFchapter1section3.twoPrimeResidual_normal (G := G))
  have hodd : Odd (Nat.card (G ⧸ L)) := by
    simpa [L] using
      (PFchapter1section3.odd_card_quotient_twoPrimeResidual (G := G))
  have hQ_le_L : Q ≤ L := by
    rw [hQ_eq_Pambient]
    change (Pambient : Subgroup G) ≤ twoPrimeResidual G
    rw [twoPrimeResidual]
    exact le_iSup (fun P : Sylow 2 G => (P : Subgroup G)) Pambient
  obtain ⟨base, hHbase⟩ := hA1.point_stabilizer
  letI : MulAction.IsPreprimitive G Omega :=
    MulAction.isPreprimitive_of_is_two_pretransitive hA1.two_transitive
  have hL_fixed_ne_univ : MulAction.fixedPoints L Omega ≠ Set.univ := by
    intro hfixed
    have hsL : s ∈ L :=
      hQ_le_L (hsection3.section2.Q0_le_Q hsQ0)
    have hsfix : ∀ x : Omega, (⟨s, hsL⟩ : L) • x = x := by
      intro x
      have hx : x ∈ MulAction.fixedPoints L Omega := by
        rw [hfixed]
        trivial
      exact hx ⟨s, hsL⟩
    apply hsection3.2.2.1.ne_one
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Omega)
    intro x
    simpa using hsfix x
  letI : MulAction.IsPretransitive L Omega :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hL_fixed_ne_univ
  let QL : Subgroup L := Q.subgroupOf L
  have hnormalizer_QL_iff : ∀ l : L,
      l ∈ Subgroup.normalizer (QL : Set L) ↔
        (l : G) ∈ Subgroup.normalizer (Q : Set G) := by
    intro l
    rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro hl x
      constructor
      · intro hxQ
        let xL : L := ⟨x, hQ_le_L hxQ⟩
        have hxQL : xL ∈ QL := hxQ
        exact (hl xL).1 hxQL
      · intro hxconjQ
        have hxL : x ∈ L := by
          have hconjL : (l : G) * x * (l : G)⁻¹ ∈ L :=
            hQ_le_L hxconjQ
          have hback :
              x = (l : G)⁻¹ * ((l : G) * x * (l : G)⁻¹) * (l : G) := by
            group
          rw [hback]
          exact L.mul_mem (L.mul_mem (L.inv_mem l.property) hconjL) l.property
        let xL : L := ⟨x, hxL⟩
        have hxconjQL : l * xL * l⁻¹ ∈ QL := hxconjQ
        exact (hl xL).2 hxconjQL
    · intro hl x
      constructor
      · intro hxQL
        exact (hl (x : G)).1 hxQL
      · intro hxconjQL
        exact (hl (x : G)).2 hxconjQL
  have hNQ_eq_H : Subgroup.normalizer (Q : Set G) = H :=
    (PFchapter1section1.proposition_1_d H D Q t hA1).1
  have hsource_stabilizer :
      MulAction.stabilizer L base = Subgroup.normalizer (QL : Set L) := by
    ext l
    rw [hnormalizer_QL_iff l, hNQ_eq_H, hHbase]
    rfl
  let Pproj := ℙ E0 (Fin 3 → E0)
  let Aunitary : Set Pproj :=
    {x | ∃ (v : Fin 3 → E0) (hv : v ≠ 0),
      x = Projectivization.mk E0 v hv ∧
        dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
  let X := {x : Pproj // x ∈ Aunitary}
  rcases External.huppert_II_10_12 J q hE0card hfixedCard hJstandard with
    ⟨_hXcard, rhoU, pinf, hrhoU_injective, hnatural,
      _hUcard, hroot_exists, htwo_target, _hPSUcard,
      _hthree_fixed⟩
  letI : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective rhoU hrhoU_injective
  letI : MulAction (ProjectiveSpecialUnitaryMatrixGroup J) X :=
    MulAction.compHom X rhoU
  have htwo_target' : MulAction.IsMultiplyPretransitive
      (ProjectiveSpecialUnitaryMatrixGroup J) X 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    exact htwo_target a b c d hab hcd
  letI : MulAction.IsMultiplyPretransitive
      (ProjectiveSpecialUnitaryMatrixGroup J) X 2 := htwo_target'
  letI : MulAction.IsPretransitive
      (ProjectiveSpecialUnitaryMatrixGroup J) X :=
    MulAction.isPretransitive_of_is_two_pretransitive
  rcases hroot_exists with
    ⟨R, HR, hR_le_U, _hHR_le_U, hU_le_normalizer_R,
      _hR_disjoint_HR, _hR_sup_HR, _hHR_cyclic, hRcard,
      _hcommutator_center, _hcommutator_card, _hHRcard,
      hRregular, _hcoordR, _hHRcoord, _hHRcoord_surjective⟩
  have hPambient_le_L : (Pambient : Subgroup G) ≤ L := by
    rw [← hQ_eq_Pambient]
    exact hQ_le_L
  let PL : Sylow 2 L := Pambient.subtype hPambient_le_L
  have hPL_eq_QL : (PL : Subgroup L) = QL := by
    ext x
    change (x : G) ∈ (Pambient : Subgroup G) ↔ (x : G) ∈ Q
    rw [hQ_eq_Pambient]
  let e0 : L ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
    Classical.choice hresidualIso
  let Pmodel : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J) :=
    PL.mapSurjective (f := e0.toMonoidHom) e0.surjective
  have hPmodel_eq :
      (Pmodel : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) =
        QL.map e0.toMonoidHom := by
    change (PL : Subgroup L).map e0.toMonoidHom =
      QL.map e0.toMonoidHom
    rw [hPL_eq_QL]
  have hQcard : Nat.card Q = Nat.card Q0 ^ 3 :=
    PFchapter4section2.natCard_eq_cube_of_isSuzukiTwoTypeB H Q Q0 S
      hC2.S_type_B hsection3.section2.S_le_Q hA1.Q_le_H
      hsection3.section2.Q0_le_Q hsection3.section2.Q0_def hSQ
  have hQLcard : Nat.card QL = q ^ 3 := by
    calc
      Nat.card QL = Nat.card Q :=
        natCard_subgroupOf_eq Q L hQ_le_L
      _ = Nat.card Q0 ^ 3 := hQcard
      _ = q ^ 3 := by rw [hqQ0]
  have hPmodel_card : Nat.card Pmodel = q ^ 3 := by
    calc
      Nat.card Pmodel = Nat.card (QL.map e0.toMonoidHom) := by
        rw [← hPmodel_eq]
      _ = Nat.card QL :=
        Subgroup.card_map_of_injective e0.injective
      _ = q ^ 3 := hQLcard
  obtain ⟨nq, hnq⟩ := hq_pow
  have hR_two : IsPGroup 2 R := by
    apply IsPGroup.of_card (n := nq * 3)
    rw [hRcard, hnq, pow_mul]
  obtain ⟨PR, hR_le_PR⟩ := hR_two.exists_le_sylow
  have hPRcard : Nat.card PR = q ^ 3 := by
    calc
      Nat.card PR = Nat.card Pmodel :=
        Nat.card_congr (Sylow.equiv PR Pmodel).toEquiv
      _ = q ^ 3 := hPmodel_card
  have hR_eq_PR :
      R = (PR : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    Subgroup.eq_of_le_of_card_ge hR_le_PR (by rw [hPRcard, hRcard])
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq
    (ProjectiveSpecialUnitaryMatrixGroup J) Pmodel PR
  have hc_subgroup :
      (Pmodel : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map
          (MulAut.conj c).toMonoidHom = R := by
    calc
      (Pmodel : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map
          (MulAut.conj c).toMonoidHom =
          ((c • Pmodel : Sylow 2
            (ProjectiveSpecialUnitaryMatrixGroup J)) :
              Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := rfl
      _ = (PR : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
        rw [hc]
      _ = R := hR_eq_PR.symm
  let eL : L ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
    e0.trans (MulAut.conj c)
  have heL_map_QL : QL.map eL.toMonoidHom = R := by
    change QL.map ((MulAut.conj c).toMonoidHom.comp e0.toMonoidHom) = R
    rw [← Subgroup.map_map, ← hPmodel_eq]
    exact hc_subgroup
  have hR_ne_bot : R ≠ ⊥ := by
    intro hRbot
    have hRcard_one : Nat.card R = 1 := by rw [hRbot]; simp
    have hqcube_one : q ^ 3 = 1 := hRcard.symm.trans hRcard_one
    have hq_one : q = 1 :=
      (pow_eq_one_iff_left (by norm_num : (3 : ℕ) ≠ 0)).mp hqcube_one
    omega
  have hR_fixed_pinf : ∀ r : R,
      (r : ProjectiveSpecialUnitaryMatrixGroup J) • pinf = pinf := by
    intro r
    exact hR_le_U r.property
  have htarget_stabilizer_le_normalizer :
      MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) pinf ≤
        Subgroup.normalizer (R : Set
          (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    intro x hx
    exact hU_le_normalizer_R hx
  have hnormalizer_le_target_stabilizer :
      Subgroup.normalizer (R : Set
          (ProjectiveSpecialUnitaryMatrixGroup J)) ≤
        MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) pinf := by
    intro x hx
    rw [MulAction.mem_stabilizer_iff]
    by_contra hxmove
    have hxnormal := Subgroup.mem_normalizer_iff.mp hx
    have hfix_moved : ∀ r : R,
        (r : ProjectiveSpecialUnitaryMatrixGroup J) • (x • pinf) =
          x • pinf := by
      intro r
      have hconj_mem :
          x⁻¹ * (r : ProjectiveSpecialUnitaryMatrixGroup J) * x ∈ R := by
        apply (hxnormal
          (x⁻¹ * (r : ProjectiveSpecialUnitaryMatrixGroup J) * x)).2
        have hconj_back :
            x * (x⁻¹ * (r : ProjectiveSpecialUnitaryMatrixGroup J) * x) *
                x⁻¹ = (r : ProjectiveSpecialUnitaryMatrixGroup J) := by
          group
        rw [hconj_back]
        exact r.property
      let rconj : R :=
        ⟨x⁻¹ * (r : ProjectiveSpecialUnitaryMatrixGroup J) * x,
          hconj_mem⟩
      calc
        (r : ProjectiveSpecialUnitaryMatrixGroup J) • (x • pinf) =
            ((r : ProjectiveSpecialUnitaryMatrixGroup J) * x) • pinf := by
              rw [mul_smul]
        _ = (x * (rconj : ProjectiveSpecialUnitaryMatrixGroup J)) • pinf := by
              congr 1
              dsimp [rconj]
              group
        _ = x • ((rconj : ProjectiveSpecialUnitaryMatrixGroup J) • pinf) :=
              mul_smul _ _ _
        _ = x • pinf := by rw [hR_fixed_pinf rconj]
    obtain ⟨r0, _hr0, hr_unique⟩ :=
      hRregular (x • pinf) (x • pinf) hxmove hxmove
    obtain ⟨r, hr_ne_one⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR_ne_bot
    have hr_solution :
        rhoU (r : ProjectiveSpecialUnitaryMatrixGroup J) (x • pinf) =
          x • pinf := by
      have hfix := hfix_moved r
      change rhoU (r : ProjectiveSpecialUnitaryMatrixGroup J) (x • pinf) =
        x • pinf at hfix
      exact hfix
    have hone_solution :
        rhoU ((1 : R) : ProjectiveSpecialUnitaryMatrixGroup J) (x • pinf) =
          x • pinf := by
      change rhoU (1 : ProjectiveSpecialUnitaryMatrixGroup J) (x • pinf) =
        x • pinf
      rw [map_one]
      rfl
    apply hr_ne_one
    exact (hr_unique r hr_solution).trans
      (hr_unique 1 hone_solution).symm
  have htarget_stabilizer :
      MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) pinf =
        Subgroup.normalizer (R : Set
          (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    le_antisymm htarget_stabilizer_le_normalizer
      hnormalizer_le_target_stabilizer
  have hstabilizer_map :
      (MulAction.stabilizer L base).map eL.toMonoidHom =
        MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) pinf := by
    calc
      (MulAction.stabilizer L base).map eL.toMonoidHom =
          (Subgroup.normalizer (QL : Set L)).map eL.toMonoidHom := by
            rw [hsource_stabilizer]
      _ = Subgroup.normalizer (QL.map eL.toMonoidHom : Set
          (ProjectiveSpecialUnitaryMatrixGroup J)) :=
            Subgroup.map_equiv_normalizer_eq QL eL
      _ = Subgroup.normalizer (R : Set
          (ProjectiveSpecialUnitaryMatrixGroup J)) := by rw [heL_map_QL]
      _ = MulAction.stabilizer
          (ProjectiveSpecialUnitaryMatrixGroup J) pinf :=
            htarget_stabilizer.symm
  obtain ⟨eOmega, hequivariant⟩ :=
    PFchapter4section1.exists_equivariant_equiv_of_stabilizer_map_eq
      eL base pinf hstabilizer_map
  have hunitaryModel : unitaryActionModel.{u, v} G Omega L q := by
    refine ⟨E0, hE0Field, hE0Finite, J, hJstandard, hE0card,
      hfixedCard, ?_⟩
    refine ⟨eL, rhoU, eOmega, hnatural, ?_⟩
    intro l omega
    have heq := hequivariant l omega
    change eOmega ((l : G) • omega) =
      rhoU (eL l) (eOmega omega) at heq
    exact heq
  exact ⟨L, inferInstance, q, rfl, hodd, ⟨nq, hnq⟩, hq_gt,
    hunitaryModel⟩

/--
The source hypothesis of the Section 3 proposition, followed by its
action-level Corollary 1.  This is the interface used by the `V ≠ W` branch
after Section 4 constructs the displayed seed.
-/
public theorem corollary_1_of_seed
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [Finite Omega]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G) (f g h : G → G)
    (hsection3 : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA
      G Omega H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧
      _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔
                x = 1 ∨ (x ∈ H ∧
                  _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q,
                      S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ a : G, a ∈ S → ∀ b : G, b ∈ Q1 →
                            a * b = b * a) ∧
                            S ⊔ Q1 = Q) ∧
      s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
        ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hC1 : HypothesisC1 G V) (hC2 : HypothesisC2 G S W t s)
    (hC3 : TypeBChapter3Data G K Q0 S W s)
    (hQ_two : IsPGroup 2 Q)
    (hf_mem : ∀ x : G, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : G, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : G, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : G, x ∈ Q → x ≠ 1 →
      t * x * t = g x * h x * t * f x)
    (omega zeta : G)
    (homega_mem_Q : omega ∈ Q) (homega_not_mem_Q0 : omega ∉ Q0)
    (hzeta_mem_W : zeta ∈ W) (hzeta_ne_one : zeta ≠ 1)
    (hf_omega_eq : f omega = rightConjugateElem omega⁻¹ zeta)
    (hh_omega_mem_W : h omega ∈ W) :
    unitaryConclusion.{u, v} G Omega := by
  exact corollary_1_core H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
    hC3 hQ_two hf_mem hg_mem hh_mem hcanonical_eq
    (Or.inr ⟨omega, zeta, homega_mem_Q, homega_not_mem_Q0,
      hzeta_mem_W, hzeta_ne_one, hf_omega_eq, hh_omega_mem_W⟩)

/-- The Section 2 proposition followed by Section 3 Corollary 1, in the
source's opening alternative where `D` acts fixed-point-freely on
`(Q / Q0)\#`. -/
public theorem corollary_1_of_fixed_point_free
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [Finite Omega]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G) (f g h : G → G)
    (hsection3 : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA
      G Omega H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧
      _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔
                x = 1 ∨ (x ∈ H ∧
                  _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q,
                      S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ a : G, a ∈ S → ∀ b : G, b ∈ Q1 →
                            a * b = b * a) ∧
                            S ⊔ Q1 = Q) ∧
      s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
        ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hC1 : HypothesisC1 G V) (hC2 : HypothesisC2 G S W t s)
    (hC3 : TypeBChapter3Data G K Q0 S W s)
    (hQ_two : IsPGroup 2 Q)
    (hf_mem : ∀ x : G, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : G, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : G, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : G, x ∈ Q → x ≠ 1 →
      t * x * t = g x * h x * t * f x)
    (hD_fixed_point_free : ∀ d : G, d ∈ D → d ≠ 1 →
      ∀ x : G, x ∈ Q → x ∉ Q0 →
        rightConjugateElem x d * x⁻¹ ∉ Q0) :
    unitaryConclusion.{u, v} G Omega := by
  exact corollary_1_core H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
    hC3 hQ_two hf_mem hg_mem hh_mem hcanonical_eq
    (Or.inl (Or.inr hD_fixed_point_free))

/--
The action-level form of Corollary 1 in the case `V = W`.

The Section 2 proposition constructs and normalizes the orbit coordinates,
Section 3 identifies the two-prime residual with the unitary model, and the
rank-one reconstruction lemma transports its natural action. None of those
choices is input data for this endpoint.
-/
public theorem corollary_1_b
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [Finite Omega]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G) (f g h : G → G)
    (hsection3 : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA
      G Omega H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧
      _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔
                x = 1 ∨ (x ∈ H ∧
                  _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q,
                      S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ a : G, a ∈ S → ∀ b : G, b ∈ Q1 →
                            a * b = b * a) ∧
                            S ⊔ Q1 = Q) ∧
      s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
        ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hC1 : HypothesisC1 G V) (hC2 : HypothesisC2 G S W t s)
    (hC3 : TypeBChapter3Data G K Q0 S W s)
    (hQ_two : IsPGroup 2 Q)
    (hf_mem : ∀ x : G, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : G, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : G, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : G, x ∈ Q → x ≠ 1 →
      t * x * t = g x * h x * t * f x)
    (hVW : V = W) : unitaryConclusion.{u, v} G Omega := by
  exact corollary_1_core H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
    hC3 hQ_two hf_mem hg_mem hh_mem hcanonical_eq (Or.inl (Or.inl hVW))

end PFchapter4section3
end CFSG.BenderSuzuki
