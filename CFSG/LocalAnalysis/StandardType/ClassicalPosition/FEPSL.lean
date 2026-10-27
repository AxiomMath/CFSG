module

public import CFSG.LocalAnalysis.StandardType.GGSixPositionDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDegreeParity
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.ReducedAlgebra
public import CFSG.RankThree.PartOne.CTP.PhanBridge
public import CFSG.Dihedral.GorensteinWalter.FieldTransport
public import CFSG.ClassicalInvolution.WeakCT.StandardPair
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Families
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S10.Defs
public import CFSG.RankThree.PartOne.S12.Hyp

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
open scoped commutatorElement

private lemma fePSL_blockField
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra (GaloisField 2 f) K) (_ : Finite K)
      (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →ₐ[GaloisField 2 f] K),
      Function.Surjective π ∧ (∀ a, π a = 0 ↔ (a : Matrix (Fin (m + 1)) (Fin (m + 1))
        (GaloisField 2 f)) * e = 0) ∧
      Module.finrank (GaloisField 2 f) K =
        blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e :=
  exists_blockField hS hodd he

lemma fePSL_blockCard (f d : ℕ) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    [Algebra (GaloisField 2 f) K] (h : Module.finrank (GaloisField 2 f) K = d) :
    Nat.card K = 2 ^ (f * d) := by
  rw [Module.natCard_eq_pow_finrank (K := GaloisField 2 f) (V := K), h,
    GaloisField.card 2 f (by omega : f ≠ 0), pow_mul]

private lemma fePSL_blockCard_ge_four (f d : ℕ) (hf : 1 ≤ f) (hd : 2 ≤ d) {K : Type}
      (h : Nat.card K = 2 ^ (f * d)) : 4 ≤ Nat.card K := by
  rw [h]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (f * d) := Nat.pow_le_pow_right (by norm_num) (by
        have h' : 1 * 2 ≤ f * d := Nat.mul_le_mul hf hd
        simpa using h')

private instance fePSL_instModule (F V : Type*) [Field F] [AddCommGroup V] [Module F V]
    (A : Subalgebra F (Module.End F V)) : Module A V :=
  Module.compHom V (Subalgebra.val A).toRingHom

private instance fePSL_instTower (F V : Type*) [Field F] [AddCommGroup V] [Module F V]
    (A : Subalgebra F (Module.End F V)) : IsScalarTower F A V :=
  ⟨fun c a v => by
    change (Subalgebra.val A (c • a)) v = c • ((Subalgebra.val A a) v)
    rw [map_smul]
    rfl⟩

private lemma fePSL_centralizer_semisimple
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s)) :
    IsSemisimpleRing (Subalgebra.centralizer (GaloisField 2 f) (Units.val '' S)) := by
  classical
  let F := GaloisField 2 f
  let V := Fin (m + 1) → F
  let e : Matrix (Fin (m + 1)) (Fin (m + 1)) F ≃ₐ[F] Module.End F V := Matrix.toLinAlgEquiv'
  let T : Set (Module.End F V) :=
    (fun s : GL (Fin (m + 1)) F => (e (Units.val s) : Module.End F V)) '' S
  let A := Algebra.adjoin F T
  have hcommT : ∀ t ∈ T, ∀ t' ∈ T, Commute t t' := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩
    exact (hS s hs s' hs').map (e.toMulEquiv.toMonoidHom.comp
      (Units.coeHom (Matrix (Fin (m + 1)) (Fin (m + 1)) F)))
  have hpair : T.Pairwise Commute := by
    rintro a ha b hb -
    exact hcommT a ha b hb
  have hTodd : ∀ t ∈ T, ∃ o : ℕ, Odd o ∧ t ^ o = 1 := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨orderOf s, hodd s hs, ?_⟩
    have h1 : ((s : GL (Fin (m + 1)) F) ^ orderOf s : GL (Fin (m + 1)) F) = 1 :=
      pow_orderOf_eq_one s
    calc (e (Units.val s) : Module.End F V) ^ orderOf s
        = e ((Units.val s) ^ orderOf s : Matrix _ _ F) := by rw [map_pow]
      _ = e (Units.val (s ^ orderOf s)) := by rw [Units.val_pow_eq_pow_val]
      _ = e (Units.val (1 : GL _ F)) := by rw [h1]
      _ = 1 := by rw [Units.val_one, map_one]
  have hredT : IsReduced (Algebra.adjoin F T) :=
    isReduced_adjoin_of_commute_of_odd T hcommT hTodd
  letI : CommRing A := Algebra.adjoinCommRingOfComm F (s := T) hpair
  haveI : Module.Finite F A := inferInstance
  haveI : IsArtinianRing A := IsArtinianRing.of_finite F A
  haveI hAsemi : IsSemisimpleRing A := IsArtinianRing.isSemisimpleRing_of_isReduced A
  haveI : IsSemisimpleModule A V := IsSemisimpleRing.isSemisimpleModule
  haveI : Finite V := inferInstance
  haveI : Module.Finite A V := Module.Finite.of_finite
  haveI hEsemi : IsSemisimpleRing (Module.End A V) := IsSemisimpleRing.moduleEnd A V
  let Ψ₁ : Subalgebra.centralizer F (Units.val '' S) ≃+* Subalgebra.centralizer F T :=
  { toFun := fun g => ⟨e (g : Matrix _ _ F), by
      rw [Subalgebra.mem_centralizer_iff]
      rintro _ ⟨s, hs, rfl⟩
      rw [← map_mul, ← map_mul,
        (Subalgebra.mem_centralizer_iff F).mp g.2 (Units.val s) ⟨s, hs, rfl⟩]⟩
    invFun := fun g => ⟨e.symm (g : Module.End F V), by
      rw [Subalgebra.mem_centralizer_iff]
      rintro _ ⟨s, hs, rfl⟩
      apply e.injective
      simp only [map_mul, e.apply_symm_apply]
      exact (Subalgebra.mem_centralizer_iff F).mp g.2 (e (Units.val s)) ⟨s, hs, rfl⟩⟩
    left_inv := fun g => by ext; simp
    right_inv := fun g => by ext; simp
    map_mul' := fun g h => by ext; simp
    map_add' := fun g h => by ext; simp }
  let Ψ₂ : Subalgebra.centralizer F T ≃+* Module.End A V :=
  { toFun := fun g =>
      { toFun := (g : Module.End F V),
        map_add' := map_add (g : Module.End F V),
        map_smul' := fun a v => by
          have h := Algebra.commute_of_mem_adjoin_of_forall_mem_commute a.2
            (fun t ht => ((Subalgebra.mem_centralizer_iff F).mp g.2 t ht).symm)
          exact congrArg (fun f : Module.End F V => f v) h.eq }
    invFun := fun g =>
      ⟨{ toFun := g,
         map_add' := map_add g,
         map_smul' := fun c v => by
           have h := g.map_smul (algebraMap F A c) v
           have hc : (algebraMap F A c) • v = c • v := by
             simpa only [Algebra.algebraMap_eq_smul_one, one_smul] using
               (fePSL_instTower F V A).smul_assoc c 1 v
           have hc' : (algebraMap F A c) • (g v) = c • (g v) := by
             simpa only [Algebra.algebraMap_eq_smul_one, one_smul] using
               (fePSL_instTower F V A).smul_assoc c 1 (g v)
           rw [← hc]
           change g ((algebraMap F A c) • v) = c • g v
           rw [← hc']
           exact h },
       by
         rw [Subalgebra.mem_centralizer_iff]
         intro t ht
         apply LinearMap.ext
         intro v
         exact (g.map_smul ⟨t, Algebra.subset_adjoin ht⟩ v).symm⟩
    left_inv := fun g => by ext v; rfl
    right_inv := fun g => by ext v; rfl
    map_mul' := fun g h => by ext v; rfl
    map_add' := fun g h => by ext v; rfl }
  exact (Ψ₁.trans Ψ₂).symm.isSemisimpleRing

private lemma fePSL_centralizer_wedderburn
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s)) :
    ∃ (n : ℕ) (D : Fin n → Type) (_ : ∀ i, DivisionRing (D i))
      (_ : ∀ i, Algebra (GaloisField 2 f) (D i))
      (_ : ∀ i, Module.Finite (GaloisField 2 f) (D i)) (d : Fin n → ℕ),
      (∀ i, NeZero (d i)) ∧
      Nonempty ((Subalgebra.centralizer (GaloisField 2 f) (Units.val '' S)) ≃ₐ[GaloisField 2 f]
        (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i))) := by
  classical
  let F := GaloisField 2 f
  let C := Subalgebra.centralizer F (Units.val '' S)
  haveI : IsSemisimpleRing C := fePSL_centralizer_semisimple m f S hS hodd
  haveI : Module.Finite F C := inferInstance
  obtain ⟨n, D, d, hDdiv, hDalg, hRest⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite F C
  obtain ⟨hDfinF, hd, ⟨Φ⟩⟩ := hRest
  exact ⟨n, D, hDdiv, hDalg, hDfinF, d, hd, ⟨Φ⟩⟩

private lemma fePSL_wedderburn_factors_finite
    (f : ℕ) (n : ℕ) (D : Fin n → Type) [∀ i, DivisionRing (D i)]
    [∀ i, Algebra (GaloisField 2 f) (D i)] [∀ i, Module.Finite (GaloisField 2 f) (D i)] :
    ∀ i, Finite (D i) := by
  intro i
  haveI : Finite (GaloisField 2 f) := inferInstance
  obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin' (GaloisField 2 f) (D i)
  exact Finite.of_surjective (g : (Fin k → GaloisField 2 f) → D i) hg

private lemma fePSL_wedderburn_ringEquiv
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (n : ℕ) (D : Fin n → Type) [∀ i, DivisionRing (D i)]
    [∀ i, Algebra (GaloisField 2 f) (D i)] [_inst : ∀ i, Module.Finite (GaloisField 2 f) (D i)]
    [∀ i, Finite (D i)] (d : Fin n → ℕ)
    (h : Nonempty ((Subalgebra.centralizer (GaloisField 2 f) (Units.val '' S)) ≃ₐ[GaloisField 2 f]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)))) :
    Nonempty ((Subalgebra.centralizer (GaloisField 2 f) (Units.val '' S)) ≃+*
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i))) := by
  obtain ⟨e⟩ := h
  exact ⟨e.toRingEquiv⟩

private lemma fePSL_centralizer_pi_matrix
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s)) :
    ∃ (n : ℕ) (D : Fin n → Type) (_ : ∀ i, Field (D i)) (_ : ∀ i, Finite (D i))
      (d : Fin n → ℕ),
      (∀ i, 0 < d i) ∧
      Nonempty ((Subalgebra.centralizer (GaloisField 2 f) (Units.val '' S)) ≃+*
        (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i))) := by
  obtain ⟨n, D, hDdiv, hDalg, hDfinF, d, hd, hAlg⟩ :=
    fePSL_centralizer_wedderburn m f S hS hodd
  have hFinite := @fePSL_wedderburn_factors_finite f n D hDdiv hDalg hDfinF
  obtain ⟨e⟩ := @fePSL_wedderburn_ringEquiv m f S n D hDdiv hDalg hDfinF hFinite d hAlg
  exact ⟨n, D, fun i => littleWedderburn (D i), hFinite, d,
    fun i => Nat.pos_of_ne_zero (NeZero.ne (d i)), ⟨e⟩⟩

private lemma fePSL_centralizer_units_pi_GL
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (n : ℕ) (D : Fin n → Type) [∀ i, Field (D i)]  (d : Fin n → ℕ)
    (hiso : Nonempty ((Subalgebra.centralizer (GaloisField 2 f) (Units.val '' S)) ≃+*
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)))) :
    Nonempty (((Subalgebra.centralizer (GaloisField 2 f) (Units.val '' S))ˣ) ≃*
      (∀ i, GL (Fin (d i)) (D i))) := by
  obtain ⟨e⟩ := hiso
  exact ⟨(Units.mapEquiv e.toMulEquiv).trans MulEquiv.piUnits⟩

private lemma fePSL_centralizer_units_centralizer
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f))) :
    Nonempty (((Subalgebra.centralizer (GaloisField 2 f) (Units.val '' S))ˣ) ≃*
      Subgroup.centralizer
        (Subgroup.closure S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))) := by
  let F := GaloisField 2 f
  let C := Subalgebra.centralizer F (Units.val '' S)
  have hunits : C.toSubmonoid.units =
      Subgroup.centralizer (Subgroup.closure S : Set (GL (Fin (m + 1)) F)) := by
    rw [Subgroup.centralizer_closure]
    ext x
    rw [Submonoid.mem_units_iff, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨h, -⟩
      intro s hs
      exact Units.ext ((Subalgebra.mem_centralizer_iff F).mp h s ⟨s, hs, rfl⟩)
    · intro h
      refine ⟨(Subalgebra.mem_centralizer_iff F).mpr (fun g hg => ?_),
        (Subalgebra.mem_centralizer_iff F).mpr (fun g hg => ?_)⟩
      · obtain ⟨s, hs, rfl⟩ := hg
        exact congrArg (fun u : (Matrix (Fin (m + 1)) (Fin (m + 1)) F)ˣ =>
          (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) (h s hs)
      · obtain ⟨s, hs, rfl⟩ := hg
        have hx : x⁻¹ ∈ Subgroup.centralizer S :=
          Subgroup.inv_mem _ ((Subgroup.mem_centralizer_iff).mpr h)
        simpa using congrArg (fun u : (Matrix (Fin (m + 1)) (Fin (m + 1)) F)ˣ =>
          (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F))
          ((Subgroup.mem_centralizer_iff).mp hx s hs)
  exact ⟨(Submonoid.unitsEquivUnitsType C.toSubmonoid).symm.trans
    (MulEquiv.subgroupCongr hunits)⟩

private lemma fePSL_centralizer_units_GL
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (n : ℕ) (D : Fin n → Type) [∀ i, Field (D i)] [_inst : ∀ i, Finite (D i)] (d : Fin n → ℕ)
    (hiso : Nonempty ((Subalgebra.centralizer (GaloisField 2 f) (Units.val '' S)) ≃+*
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)))) :
    ∃ θ : (∀ i, GL (Fin (d i)) (D i)) →* GL (Fin (m + 1)) (GaloisField 2 f),
      Function.Injective θ ∧
      θ.range = Subgroup.centralizer
        (Subgroup.closure S : Set (GL (Fin (m + 1)) (GaloisField 2 f))) := by
  obtain ⟨e1⟩ := fePSL_centralizer_units_pi_GL m f S n D d hiso
  obtain ⟨e2⟩ := fePSL_centralizer_units_centralizer m f S
  let E : (∀ i, GL (Fin (d i)) (D i)) ≃* Subgroup.centralizer
      (Subgroup.closure S : Set (GL (Fin (m + 1)) (GaloisField 2 f))) := e1.symm.trans e2
  refine ⟨(Subgroup.subtype _).comp E.toMonoidHom,
    fun a b h => E.injective (Subtype.ext h), ?_⟩
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr E.surjective]
  rw [Subgroup.map_top, Subgroup.range_subtype]

private lemma fePSL_blockFactor_centralizer
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s)) :
    ∃ (n : ℕ) (D : Fin n → Type) (_ : ∀ i, Field (D i)) (_ : ∀ i, Finite (D i))
      (d : Fin n → ℕ)
      (θ : (∀ i, GL (Fin (d i)) (D i)) →* GL (Fin (m + 1)) (GaloisField 2 f)),
      (∀ i, 0 < d i) ∧ Function.Injective θ ∧
      θ.range = Subgroup.centralizer
        (Subgroup.closure S : Set (GL (Fin (m + 1)) (GaloisField 2 f))) := by
  obtain ⟨n, D, hfield, hfin, d, hd, hiso⟩ := fePSL_centralizer_pi_matrix m f S hS hodd
  obtain ⟨θ, hinj, hrange⟩ :=
    @fePSL_centralizer_units_GL m f S n D hfield hfin d hiso
  exact ⟨n, D, hfield, hfin, d, θ, hd, hinj, hrange⟩

private lemma fePSL_blockAction
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) :
    ∃ actA : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →ₐ[GaloisField 2 f]
        Module.End (GaloisField 2 f) (LinearMap.range (Matrix.mulVecLin e)),
      ∀ (a : Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
        (w : LinearMap.range (Matrix.mulVecLin e)),
        (actA a w : Fin (m + 1) → GaloisField 2 f) =
          Matrix.mulVec (a : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) w := by
  classical
  let F := GaloisField 2 f
  let A := Algebra.adjoin F (Units.val '' S)
  let W : Submodule F (Fin (m + 1) → F) := LinearMap.range (Matrix.mulVecLin e)
  have hpair : (Units.val '' S : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) F)).Pairwise Commute := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩ _
    exact (hS s hs s' hs').map (Units.coeHom (Matrix (Fin (m + 1)) (Fin (m + 1)) F))
  letI : CommRing A := Algebra.adjoinCommRingOfComm F (s := Units.val '' S) hpair
  have hcomm : ∀ a : A, (a : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * e =
      e * (a : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
    intro a
    exact congrArg Subtype.val (mul_comm a (⟨e, he.1⟩ : A))
  let actA : A →ₐ[F] Module.End F W :=
  { toFun := fun a =>
      ((Matrix.mulVecLin (a : Matrix (Fin (m + 1)) (Fin (m + 1)) F)).comp W.subtype).codRestrict W
        (fun v => by
          rw [LinearMap.comp_apply, Submodule.coe_subtype]
          obtain ⟨u, hu⟩ := v.2
          rw [← hu]
          refine ⟨Matrix.mulVec (a : Matrix (Fin (m + 1)) (Fin (m + 1)) F) u, ?_⟩
          calc Matrix.mulVecLin e (Matrix.mulVec (a : Matrix (Fin (m + 1)) (Fin (m + 1)) F) u)
              = Matrix.mulVec e
                  (Matrix.mulVec (a : Matrix (Fin (m + 1)) (Fin (m + 1)) F) u) := rfl
            _ = Matrix.mulVec (e * (a : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) u :=
                  Matrix.mulVec_mulVec u e (a : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
            _ = Matrix.mulVec ((a : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * e) u := by
                  rw [hcomm a]
            _ = Matrix.mulVec (a : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
                  (Matrix.mulVec e u) :=
                  (Matrix.mulVec_mulVec u (a : Matrix (Fin (m + 1)) (Fin (m + 1)) F) e).symm
            _ = Matrix.mulVecLin a (Matrix.mulVecLin e u) := rfl)
    map_one' := by ext w; simp
    map_mul' := by intro a b; ext w; simp
    map_zero' := by ext w; simp
    map_add' := by intro a b; ext w; simp
    commutes' := by
      intro c
      ext w
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.codRestrict_apply,
        Submodule.coe_subtype, Matrix.mulVecLin_apply, Subalgebra.coe_algebraMap,
        Module.algebraMap_end_apply, Matrix.algebraMap_eq_diagonal, Submodule.coe_smul]
      rw [show algebraMap F (Fin (m + 1) → F) c = fun _ => c from rfl,
        Matrix.diagonal_const_mulVec] }
  refine ⟨actA, ?_⟩
  intro a w
  rfl

private lemma fePSL_blockAction_ker
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (_hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (_he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K]
    (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →ₐ[GaloisField 2 f] K)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (Fin (m + 1)) (Fin (m + 1))
      (GaloisField 2 f)) * e = 0)
    (actA : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →ₐ[GaloisField 2 f]
      Module.End (GaloisField 2 f) (LinearMap.range (Matrix.mulVecLin e)))
    (hact : ∀ (a : Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
      (w : LinearMap.range (Matrix.mulVecLin e)),
      (actA a w : Fin (m + 1) → GaloisField 2 f) =
        Matrix.mulVec (a : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) w) :
    RingHom.ker (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →+* K) ≤
      RingHom.ker (actA : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →+*
        Module.End (GaloisField 2 f) (LinearMap.range (Matrix.mulVecLin e))) := by
  intro a ha
  rw [RingHom.mem_ker] at ha ⊢
  have hae : (a : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * e = 0 :=
    (hπker a).mp ha
  refine LinearMap.ext fun w => Subtype.ext ?_
  change (actA a w : Fin (m + 1) → GaloisField 2 f) = 0
  rw [hact a w]
  obtain ⟨v, hv⟩ := w.2
  rw [← hv, Matrix.mulVecLin_apply,
    Matrix.mulVec_mulVec v (a : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) e, hae,
    Matrix.zero_mulVec]

lemma fePSL_blockCentralizer_commute_adjoin
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e)
    {a : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (ha : a ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) :
    ((u : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * a =
      a * ((u : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) := by
  let M : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f) :=
    ((u : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))
  have hT : Matrix.SpecialLinearGroup.toGL
      (u : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) ∈
      Subgroup.centralizer S :=
    (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp u.2)).1
  have hgen : (Units.val '' S : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))) ⊆
      (Subalgebra.centralizer (GaloisField 2 f) ({M} : Set (Matrix (Fin (m + 1)) (Fin (m + 1))
        (GaloisField 2 f))) : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))) := by
    rintro x ⟨s, hs, rfl⟩
    refine (Subalgebra.mem_centralizer_iff (GaloisField 2 f)).mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact congrArg (fun g : GL (Fin (m + 1)) (GaloisField 2 f) =>
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)))
      ((Subgroup.mem_centralizer_iff.mp hT) s hs).symm
  have hA : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) ≤
      Subalgebra.centralizer (GaloisField 2 f) ({M} : Set (Matrix (Fin (m + 1)) (Fin (m + 1))
        (GaloisField 2 f))) :=
    Algebra.adjoin_le hgen
  exact (Subalgebra.mem_centralizer_iff (GaloisField 2 f)).mp (hA ha) M (Set.mem_singleton M)

lemma fePSL_blockCentralizer_stable
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e) :
    ∀ w ∈ LinearMap.range (Matrix.mulVecLin e),
      Matrix.mulVecLin ((u : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) w ∈
        LinearMap.range (Matrix.mulVecLin e) := by
  let M : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f) :=
    ((u : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))
  intro w hw
  obtain ⟨v, hv⟩ := hw
  refine ⟨Matrix.mulVec M v, ?_⟩
  rw [← hv]
  calc Matrix.mulVecLin e (Matrix.mulVec M v)
      = Matrix.mulVec e (Matrix.mulVec M v) := rfl
    _ = Matrix.mulVec (e * M) v := Matrix.mulVec_mulVec v e M
    _ = Matrix.mulVec (M * e) v := by
          rw [fePSL_blockCentralizer_commute_adjoin m f S u he.1]
    _ = Matrix.mulVec M (Matrix.mulVec e v) := (Matrix.mulVec_mulVec v M e).symm
    _ = Matrix.mulVecLin M (Matrix.mulVecLin e v) := rfl

lemma fePSL_blockKAction
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (K : Type) [Field K]  [Algebra (GaloisField 2 f) K]
    (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →ₐ[GaloisField 2 f] K)
    (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (Fin (m + 1)) (Fin (m + 1))
      (GaloisField 2 f)) * e = 0) :
    ∃ (_ : Module K (LinearMap.range (Matrix.mulVecLin e)))
      (_ : IsScalarTower (GaloisField 2 f) K (LinearMap.range (Matrix.mulVecLin e)))
      (actK : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e →*
        Module.End K (LinearMap.range (Matrix.mulVecLin e))),
      (∀ (a : Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
        (w : LinearMap.range (Matrix.mulVecLin e)),
        ((π a • w : LinearMap.range (Matrix.mulVecLin e)) :
            Fin (m + 1) → GaloisField 2 f) =
          Matrix.mulVec (a : Matrix (Fin (m + 1)) (Fin (m + 1))
            (GaloisField 2 f)) (w : Fin (m + 1) → GaloisField 2 f)) ∧
      ∀ (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e)
        (w : LinearMap.range (Matrix.mulVecLin e)),
        (actK u w : Fin (m + 1) → GaloisField 2 f) =
          Matrix.mulVec ((u : Matrix.SpecialLinearGroup (Fin (m + 1))
            (GaloisField 2 f)) : Matrix (Fin (m + 1)) (Fin (m + 1))
            (GaloisField 2 f)) w := by
  classical
  obtain ⟨actA, hact⟩ := fePSL_blockAction m f S hS he
  have hker : RingHom.ker (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →+* K) ≤
      RingHom.ker (actA : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →+*
        Module.End (GaloisField 2 f) (LinearMap.range (Matrix.mulVecLin e))) :=
    fePSL_blockAction_ker m f S hS he K π hπker actA hact
  have hp : Function.Surjective (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →+* K) :=
    fun k => hπsurj k
  let ψ : K →+* Module.End (GaloisField 2 f) (LinearMap.range (Matrix.mulVecLin e)) :=
    (Ideal.Quotient.lift
      (RingHom.ker (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →+* K))
      (actA : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →+*
        Module.End (GaloisField 2 f) (LinearMap.range (Matrix.mulVecLin e)))
      (fun a ha => RingHom.mem_ker.mp (hker ha))).comp
      (RingHom.quotientKerEquivOfSurjective
        (f := (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →+* K)) hp).symm.toRingHom
  have hψ : ∀ a : Algebra.adjoin (GaloisField 2 f) (Units.val '' S), ψ (π a) = actA a :=
    fun a => by
    change (Ideal.Quotient.lift
      (RingHom.ker (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →+* K))
      (actA : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →+*
        Module.End (GaloisField 2 f) (LinearMap.range (Matrix.mulVecLin e)))
      (fun a ha => RingHom.mem_ker.mp (hker ha)))
      ((RingHom.quotientKerEquivOfSurjective
        (f := (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →+* K)) hp).symm
        ((π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →+* K) a)) = actA a
    rw [RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.Quotient.lift_mk]
    rfl
  letI : Module K (LinearMap.range (Matrix.mulVecLin e)) :=
    Module.compHom (LinearMap.range (Matrix.mulVecLin e)) ψ
  have htower : IsScalarTower (GaloisField 2 f) K (LinearMap.range (Matrix.mulVecLin e)) :=
    ⟨fun c k w => by
    change (ψ (c • k)) w = c • ((ψ k) w)
    obtain ⟨a, rfl⟩ := hπsurj k
    rw [← map_smul π c a, hψ (c • a), hψ a, map_smul]
    rfl⟩
  let rhoF (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e) :
      LinearMap.range (Matrix.mulVecLin e) →ₗ[GaloisField 2 f]
        LinearMap.range (Matrix.mulVecLin e) :=
    ((Matrix.mulVecLin ((u : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))).comp
      (LinearMap.range (Matrix.mulVecLin e)).subtype).codRestrict
        (LinearMap.range (Matrix.mulVecLin e)) (fun v => by
          rw [LinearMap.comp_apply, Submodule.coe_subtype]
          exact fePSL_blockCentralizer_stable m f S he u v v.2)
  have hrhoF_apply (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e)
      (v : LinearMap.range (Matrix.mulVecLin e)) :
      (rhoF u v : Fin (m + 1) → GaloisField 2 f) =
        Matrix.mulVec ((u : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) v := rfl
  have hrhoF_smul (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e) (k : K)
      (v : LinearMap.range (Matrix.mulVecLin e)) : rhoF u (k • v) = k • rhoF u v := by
    obtain ⟨a, ha⟩ := hπsurj k
    have hψk : ψ k = actA a := by rw [← ha, hψ a]
    apply Subtype.ext
    change (rhoF u (ψ k v) : Fin (m + 1) → GaloisField 2 f) =
      (ψ k (rhoF u v) : Fin (m + 1) → GaloisField 2 f)
    rw [hψk]
    have h1 : (rhoF u (actA a v) : Fin (m + 1) → GaloisField 2 f) =
        Matrix.mulVec ((u : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))
          (Matrix.mulVec (a : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))
            (v : Fin (m + 1) → GaloisField 2 f)) := by
      rw [hrhoF_apply, hact a v]
    have h2 : (actA a (rhoF u v) : Fin (m + 1) → GaloisField 2 f) =
        Matrix.mulVec (a : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))
          (Matrix.mulVec ((u : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))
            (v : Fin (m + 1) → GaloisField 2 f)) := by
      rw [hact a (rhoF u v), hrhoF_apply]
    rw [h1, h2]
    calc Matrix.mulVec ((u : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))
            (Matrix.mulVec (a : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))
              (v : Fin (m + 1) → GaloisField 2 f))
        = Matrix.mulVec (((u : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) *
            (a : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)))
            (v : Fin (m + 1) → GaloisField 2 f) :=
          Matrix.mulVec_mulVec (v : Fin (m + 1) → GaloisField 2 f)
            ((u : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :
              Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))
            (a : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))
      _ = Matrix.mulVec ((a : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) *
            ((u : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)))
            (v : Fin (m + 1) → GaloisField 2 f) := by
          rw [fePSL_blockCentralizer_commute_adjoin m f S u a.2]
      _ = Matrix.mulVec (a : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))
            (Matrix.mulVec ((u : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))
            (v : Fin (m + 1) → GaloisField 2 f)) :=
          (Matrix.mulVec_mulVec (v : Fin (m + 1) → GaloisField 2 f)
            (a : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))
            ((u : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :
              Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))).symm
  let rhoK (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e) :
      LinearMap.range (Matrix.mulVecLin e) →ₗ[K] LinearMap.range (Matrix.mulVecLin e) :=
    { toFun := fun v => rhoF u v
      map_add' := fun v v' => (rhoF u).map_add v v'
      map_smul' := fun k v => hrhoF_smul u k v }
  refine ⟨inferInstance, htower, ?_, ?_, ?_⟩
  · refine
      { toFun := rhoK
        map_one' := ?_
        map_mul' := ?_ }
    · refine LinearMap.ext fun v => Subtype.ext ?_
      change (rhoF 1 v : Fin (m + 1) → GaloisField 2 f) =
        (v : Fin (m + 1) → GaloisField 2 f)
      rw [hrhoF_apply]
      change Matrix.mulVec (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) v =
        (v : Fin (m + 1) → GaloisField 2 f)
      rw [Matrix.one_mulVec]
    · intro u u'
      refine LinearMap.ext fun v => Subtype.ext ?_
      change (rhoF (u * u') v : Fin (m + 1) → GaloisField 2 f) =
        (rhoF u (rhoF u' v) : Fin (m + 1) → GaloisField 2 f)
      rw [hrhoF_apply, hrhoF_apply, hrhoF_apply]
      have hcoe : (((u * u' : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e) :
            Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) =
          ((u : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) *
          ((u' : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) := rfl
      rw [hcoe, Matrix.mulVec_mulVec]
  · intro a w
    change (ψ (π a) (w : LinearMap.range (Matrix.mulVecLin e)) :
        Fin (m + 1) → GaloisField 2 f) =
      Matrix.mulVec (a : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) w
    rw [hψ a, hact a w]
  · intro u w
    exact hrhoF_apply u w

lemma fePSL_blockKAction_injective
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (_he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (K : Type) [Field K]  
    [Module K (LinearMap.range (Matrix.mulVecLin e))]
    (actK : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e →*
      Module.End K (LinearMap.range (Matrix.mulVecLin e)))
    (hact : ∀ (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e)
      (w : LinearMap.range (Matrix.mulVecLin e)),
      (actK u w : Fin (m + 1) → GaloisField 2 f) =
        Matrix.mulVec ((u : Matrix.SpecialLinearGroup (Fin (m + 1))
          (GaloisField 2 f)) : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 f)) w) :
    Function.Injective actK := by
  classical
  let M (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f) :=
    ((u : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))
  have hfix (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e) :
      M u * (1 - e) = 1 - e :=
    (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp u.2)).2
  intro u v huv
  have hW : ∀ w : LinearMap.range (Matrix.mulVecLin e),
      Matrix.mulVec (M u) (w : Fin (m + 1) → GaloisField 2 f) =
        Matrix.mulVec (M v) (w : Fin (m + 1) → GaloisField 2 f) := by
    intro w
    have h := congrArg (fun (x : LinearMap.range (Matrix.mulVecLin e)) =>
      (x : Fin (m + 1) → GaloisField 2 f)) (congrArg (fun g => g w) huv)
    rwa [hact u w, hact v w] at h
  have hMe : M u * e = M v * e := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    change Matrix.mulVec (M u * e) x = Matrix.mulVec (M v * e) x
    rw [← Matrix.mulVec_mulVec (x : Fin (m + 1) → GaloisField 2 f) (M u) e,
      ← Matrix.mulVec_mulVec (x : Fin (m + 1) → GaloisField 2 f) (M v) e]
    exact hW ⟨Matrix.mulVec e x, ⟨x, rfl⟩⟩
  have hM : M u = M v := by
    calc M u = M u * 1 := (Matrix.mul_one (M u)).symm
      _ = M u * (e + (1 - e)) := by rw [add_sub_cancel]
      _ = M u * e + M u * (1 - e) := Matrix.mul_add (M u) e (1 - e)
      _ = M v * e + M v * (1 - e) := by rw [hMe, hfix u, hfix v]
      _ = M v * (e + (1 - e)) := (Matrix.mul_add (M v) e (1 - e)).symm
      _ = M v * 1 := by rw [add_sub_cancel]
      _ = M v := Matrix.mul_one (M v)
  exact Subtype.ext (Subtype.ext hM)

lemma fePSL_blockKAction_extension
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (K : Type) [Field K] [Finite K] [Algebra (GaloisField 2 f) K]
    [Module K (LinearMap.range (Matrix.mulVecLin e))]
    [IsScalarTower (GaloisField 2 f) K (LinearMap.range (Matrix.mulVecLin e))]
    (g : LinearMap.range (Matrix.mulVecLin e) →ₗ[K] LinearMap.range (Matrix.mulVecLin e))
    (hg : LinearMap.det g = 1) :
    ∃ u : (Fin (m + 1) → GaloisField 2 f) →ₗ[GaloisField 2 f]
        (Fin (m + 1) → GaloisField 2 f),
      (∀ w : LinearMap.range (Matrix.mulVecLin e),
        u (w : Fin (m + 1) → GaloisField 2 f) = (g w : Fin (m + 1) → GaloisField 2 f)) ∧
      (∀ x : Fin (m + 1) → GaloisField 2 f, Matrix.mulVecLin e x = 0 → u x = x) ∧
      LinearMap.det u = 1 := by
  classical
  have hE : IsIdempotentElem (Matrix.mulVecLin e) := by
    change (Matrix.mulVecLin e).comp (Matrix.mulVecLin e) = Matrix.mulVecLin e
    rw [← Matrix.mulVecLin_mul, he.2.1.eq]
  let W : Submodule (GaloisField 2 f) (Fin (m + 1) → GaloisField 2 f) :=
    LinearMap.range (Matrix.mulVecLin e)
  let W' : Submodule (GaloisField 2 f) (Fin (m + 1) → GaloisField 2 f) :=
    LinearMap.ker (Matrix.mulVecLin e)
  have hcompl : IsCompl W W' := LinearMap.IsIdempotentElem.isCompl hE
  let ψ := Submodule.prodEquivOfIsCompl W W' hcompl
  let fmap : W × W' →ₗ[GaloisField 2 f] W × W' :=
    (g.restrictScalars (GaloisField 2 f)).prodMap (LinearMap.id : W' →ₗ[GaloisField 2 f] W')
  let u : (Fin (m + 1) → GaloisField 2 f) →ₗ[GaloisField 2 f]
      (Fin (m + 1) → GaloisField 2 f) :=
    (ψ : W × W' →ₗ[GaloisField 2 f] (Fin (m + 1) → GaloisField 2 f)) ∘ₗ fmap ∘ₗ
      (ψ.symm : (Fin (m + 1) → GaloisField 2 f) →ₗ[GaloisField 2 f] W × W')
  refine ⟨u, ?_, ?_, ?_⟩
  · intro w
    have hφ : (ψ.symm : (Fin (m + 1) → GaloisField 2 f) →ₗ[GaloisField 2 f] W × W')
        (w : Fin (m + 1) → GaloisField 2 f) = (w, 0) := by
      simpa [ψ] using Submodule.prodEquivOfIsCompl_symm_apply_left W W' hcompl w
    have hf : fmap (w, 0) = (g w, 0) := by
      simp [fmap, LinearMap.prodMap_apply]
    have hφs : (ψ : W × W' →ₗ[GaloisField 2 f] (Fin (m + 1) → GaloisField 2 f)) (g w, 0) =
        (g w : Fin (m + 1) → GaloisField 2 f) := by
      simp [ψ, Submodule.coe_prodEquivOfIsCompl']
    simp only [u, LinearMap.comp_apply, hφ, hf, hφs]
  · intro x hx
    have hφ : (ψ.symm : (Fin (m + 1) → GaloisField 2 f) →ₗ[GaloisField 2 f] W × W') x =
        (0, ⟨x, hx⟩) := by
      simpa [ψ] using
        Submodule.prodEquivOfIsCompl_symm_apply_right W W' hcompl (⟨x, hx⟩ : W')
    have hf : fmap (0, ⟨x, hx⟩) = (0, ⟨x, hx⟩) := by
      simp [fmap, LinearMap.prodMap_apply]
    have hφs : (ψ : W × W' →ₗ[GaloisField 2 f] (Fin (m + 1) → GaloisField 2 f))
        (0, ⟨x, hx⟩) = x := by
      simp [ψ, Submodule.coe_prodEquivOfIsCompl']
    simp only [u, LinearMap.comp_apply, hφ, hf, hφs]
  · change LinearMap.det ((ψ : W × W' →ₗ[GaloisField 2 f]
        (Fin (m + 1) → GaloisField 2 f)) ∘ₗ fmap ∘ₗ
      (ψ.symm : (Fin (m + 1) → GaloisField 2 f) →ₗ[GaloisField 2 f] W × W')) = 1
    rw [LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_restrictScalars, hg]
    simp

lemma fePSL_blockKAction_extension_commute
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (K : Type) [Field K]  [Algebra (GaloisField 2 f) K]
    [Module K (LinearMap.range (Matrix.mulVecLin e))]
    (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →ₐ[GaloisField 2 f] K)
    (hcomp : ∀ (a : Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
      (w : LinearMap.range (Matrix.mulVecLin e)),
      ((π a • w : LinearMap.range (Matrix.mulVecLin e)) : Fin (m + 1) → GaloisField 2 f) =
        Matrix.mulVec (a : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 f)) (w : Fin (m + 1) → GaloisField 2 f))
    (g : LinearMap.range (Matrix.mulVecLin e) →ₗ[K] LinearMap.range (Matrix.mulVecLin e))
    (u : (Fin (m + 1) → GaloisField 2 f) →ₗ[GaloisField 2 f]
      (Fin (m + 1) → GaloisField 2 f))
    (huW : ∀ w : LinearMap.range (Matrix.mulVecLin e),
      u (w : Fin (m + 1) → GaloisField 2 f) = (g w : Fin (m + 1) → GaloisField 2 f))
    (huK : ∀ x : Fin (m + 1) → GaloisField 2 f, Matrix.mulVecLin e x = 0 → u x = x) :
    ∀ (a : Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
      (x : Fin (m + 1) → GaloisField 2 f),
      u (Matrix.mulVec (a : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) x) =
        Matrix.mulVec (a : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 f)) (u x) := by
  classical
  let F := GaloisField 2 f
  let A := Algebra.adjoin F (Units.val '' S)
  have hpair : (Units.val '' S : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) F)).Pairwise Commute := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩ _
    exact (hS s hs s' hs').map (Units.coeHom (Matrix (Fin (m + 1)) (Fin (m + 1)) F))
  letI : CommRing A := Algebra.adjoinCommRingOfComm F (s := Units.val '' S) hpair
  have hcomm (a : A) : (a : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * e =
      e * (a : Matrix (Fin (m + 1)) (Fin (m + 1)) F) :=
    congrArg Subtype.val (mul_comm a (⟨e, he.1⟩ : A))
  have hu_form (x : Fin (m + 1) → F) :
      u x = (g ⟨Matrix.mulVec e x, ⟨x, rfl⟩⟩ : Fin (m + 1) → F) +
        Matrix.mulVec (1 - e) x := by
    have hdecomp : x = Matrix.mulVec e x + Matrix.mulVec (1 - e) x := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      abel
    have hker : Matrix.mulVecLin e (Matrix.mulVec (1 - e) x) = 0 := by
      rw [Matrix.mulVecLin_apply]
      rw [Matrix.mulVec_mulVec (x : Fin (m + 1) → F) e (1 - e)]
      rw [show e * (1 - e) = 0 by rw [Matrix.mul_sub, Matrix.mul_one, he.2.1.eq, sub_self]]
      exact Matrix.zero_mulVec x
    conv_lhs => rw [hdecomp]
    rw [map_add, huW ⟨Matrix.mulVec e x, ⟨x, rfl⟩⟩, huK _ hker]
  intro a x
  rw [hu_form (Matrix.mulVec (a : Matrix (Fin (m + 1)) (Fin (m + 1)) F) x), hu_form x]
  rw [Matrix.mulVec_add]
  congr 1
  · have hw : (⟨Matrix.mulVec e (Matrix.mulVec (a : Matrix (Fin (m + 1)) (Fin (m + 1)) F) x),
          ⟨_, rfl⟩⟩ : LinearMap.range (Matrix.mulVecLin e)) =
        π a • (⟨Matrix.mulVec e x, ⟨x, rfl⟩⟩ : LinearMap.range (Matrix.mulVecLin e)) := by
      apply Subtype.ext
      simp only [hcomp a (⟨Matrix.mulVec e x, ⟨x, rfl⟩⟩ : LinearMap.range (Matrix.mulVecLin e)),
        Matrix.mulVec_mulVec, hcomm a]
    rw [hw, map_smul]
    exact hcomp a (g ⟨Matrix.mulVec e x, ⟨x, rfl⟩⟩)
  · rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hcomm a]

lemma fePSL_blockKAction_extension_mem
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (K : Type) [Field K]  
    [Module K (LinearMap.range (Matrix.mulVecLin e))]
    (_g : LinearMap.range (Matrix.mulVecLin e) →ₗ[K] LinearMap.range (Matrix.mulVecLin e))
    (u : (Fin (m + 1) → GaloisField 2 f) →ₗ[GaloisField 2 f]
      (Fin (m + 1) → GaloisField 2 f))
    (hcomm : ∀ (a : Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
      (x : Fin (m + 1) → GaloisField 2 f),
      u (Matrix.mulVec (a : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) x) =
        Matrix.mulVec (a : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 f)) (u x))
    (hfix : ∀ x : Fin (m + 1) → GaloisField 2 f, Matrix.mulVecLin e x = 0 → u x = x)
    (hdet : LinearMap.det u = 1) :
    ∃ uM : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      ∀ x : Fin (m + 1) → GaloisField 2 f,
        Matrix.mulVec ((uM : Matrix.SpecialLinearGroup (Fin (m + 1))
          (GaloisField 2 f)) : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 f)) x = u x := by
  let F := GaloisField 2 f
  let M : Matrix (Fin (m + 1)) (Fin (m + 1)) F := Matrix.toLinAlgEquiv'.symm u
  have hMmul : Matrix.mulVecLin M = u := by
    change Matrix.toLin' M = u
    rw [show M = Matrix.toLinAlgEquiv'.symm u from rfl]
    exact Matrix.toLinAlgEquiv'.apply_symm_apply u
  have hMdet : M.det = 1 := by
    change Matrix.det (LinearMap.toMatrix' u) = 1
    rw [LinearMap.det_toMatrix']
    exact hdet
  let uSL : Matrix.SpecialLinearGroup (Fin (m + 1)) F := ⟨M, hMdet⟩
  have hker (x : Fin (m + 1) → F) : Matrix.mulVecLin e (Matrix.mulVec (1 - e) x) = 0 := by
    rw [Matrix.mulVecLin_apply]
    rw [Matrix.mulVec_mulVec (x : Fin (m + 1) → F) e (1 - e)]
    rw [show e * (1 - e) = 0 by rw [Matrix.mul_sub, Matrix.mul_one, he.2.1.eq, sub_self]]
    exact Matrix.zero_mulVec x
  have hMs (s : GL (Fin (m + 1)) F) (hs : s ∈ S) :
      (s : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * M =
        M * (s : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
    have hsA : (s : Matrix (Fin (m + 1)) (Fin (m + 1)) F) ∈
        Algebra.adjoin F (Units.val '' S) := Algebra.subset_adjoin ⟨s, hs, rfl⟩
    have hmul : Matrix.mulVecLin ((s : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * M) =
        Matrix.mulVecLin (M * (s : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) := by
      rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, hMmul]
      apply LinearMap.ext
      intro x
      exact (hcomm ⟨(s : Matrix (Fin (m + 1)) (Fin (m + 1)) F), hsA⟩ x).symm
    exact Matrix.toLin'.injective (by simpa only [Matrix.toLin'_apply'] using hmul)
  have hMfix : M * (1 - e) = 1 - e := by
    have hmul : Matrix.mulVecLin (M * (1 - e)) = Matrix.mulVecLin (1 - e) := by
      rw [Matrix.mulVecLin_mul, hMmul]
      apply LinearMap.ext
      intro x
      exact hfix (Matrix.mulVec (1 - e) x) (hker x)
    exact Matrix.toLin'.injective (by simpa only [Matrix.toLin'_apply'] using hmul)
  have hmem : uSL ∈ glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e := by
    rw [glBlockCentralizer, Subgroup.mem_comap, Subgroup.mem_inf]
    constructor
    · rw [Subgroup.mem_centralizer_iff]
      intro s hs
      apply Units.ext
      show (s : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * M =
        M * (s : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
      exact hMs s hs
    · show ((Matrix.SpecialLinearGroup.toGL uSL : GL (Fin (m + 1)) F) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) F) * (1 - e) = 1 - e
      show M * (1 - e) = 1 - e
      exact hMfix
  refine ⟨⟨uSL, hmem⟩, ?_⟩
  intro x
  show Matrix.mulVec (uSL : Matrix (Fin (m + 1)) (Fin (m + 1)) F) x = u x
  show Matrix.mulVec M x = u x
  rw [← hMmul]
  rfl

private lemma fePSL_blockKAction_extension_actK
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (_he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (K : Type) [Field K]  
    [Module K (LinearMap.range (Matrix.mulVecLin e))]
    (g : LinearMap.range (Matrix.mulVecLin e) →ₗ[K] LinearMap.range (Matrix.mulVecLin e))
    (uM : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e)
    (huM : ∀ w : LinearMap.range (Matrix.mulVecLin e),
      Matrix.mulVec ((uM : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))
        (w : Fin (m + 1) → GaloisField 2 f) = (g w : Fin (m + 1) → GaloisField 2 f))
    (actK : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e →*
      Module.End K (LinearMap.range (Matrix.mulVecLin e)))
    (hact : ∀ (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e)
      (w : LinearMap.range (Matrix.mulVecLin e)),
      (actK u w : Fin (m + 1) → GaloisField 2 f) =
        Matrix.mulVec ((u : Matrix.SpecialLinearGroup (Fin (m + 1))
          (GaloisField 2 f)) : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 f)) w) :
    actK uM = g := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  show ((actK uM w : LinearMap.range (Matrix.mulVecLin e)) :
      Fin (m + 1) → GaloisField 2 f) =
    ((g w : LinearMap.range (Matrix.mulVecLin e)) : Fin (m + 1) → GaloisField 2 f)
  rw [hact uM w, huM w]

lemma fePSL_blockKAction_det_one_mem
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (K : Type) [Field K] [Finite K] [Algebra (GaloisField 2 f) K]
    [Module K (LinearMap.range (Matrix.mulVecLin e))]
    [IsScalarTower (GaloisField 2 f) K (LinearMap.range (Matrix.mulVecLin e))]
    (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →ₐ[GaloisField 2 f] K)
    (hcomp : ∀ (a : Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
      (w : LinearMap.range (Matrix.mulVecLin e)),
      ((π a • w : LinearMap.range (Matrix.mulVecLin e)) : Fin (m + 1) → GaloisField 2 f) =
        Matrix.mulVec (a : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 f)) (w : Fin (m + 1) → GaloisField 2 f))
    (actK : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e →*
      Module.End K (LinearMap.range (Matrix.mulVecLin e)))
    (hact : ∀ (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e)
      (w : LinearMap.range (Matrix.mulVecLin e)),
      (actK u w : Fin (m + 1) → GaloisField 2 f) =
        Matrix.mulVec ((u : Matrix.SpecialLinearGroup (Fin (m + 1))
          (GaloisField 2 f)) : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 f)) w) :
    ∀ g : LinearMap.range (Matrix.mulVecLin e) →ₗ[K] LinearMap.range (Matrix.mulVecLin e),
      LinearMap.det g = 1 → g ∈ Set.range actK := by
  intro g hg
  obtain ⟨u, huW, huK, hdet⟩ :=
    fePSL_blockKAction_extension m f S he K g hg
  have hcomm :=
    fePSL_blockKAction_extension_commute m f S hS he K π hcomp g u huW huK
  obtain ⟨uM, huM⟩ :=
    fePSL_blockKAction_extension_mem m f S he K g u hcomm huK hdet
  refine ⟨uM, ?_⟩
  exact fePSL_blockKAction_extension_actK m f S he K g uM
    (fun w => by rw [huM (w : Fin (m + 1) → GaloisField 2 f), huW w]) actK hact

lemma fePSL_blockKAction_commutator_det_one
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (_he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (K : Type) [Field K]  
    [Module K (LinearMap.range (Matrix.mulVecLin e))]
    (actK : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e →*
      Module.End K (LinearMap.range (Matrix.mulVecLin e)))
    (_hact : ∀ (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e)
      (w : LinearMap.range (Matrix.mulVecLin e)),
      (actK u w : Fin (m + 1) → GaloisField 2 f) =
        Matrix.mulVec ((u : Matrix.SpecialLinearGroup (Fin (m + 1))
          (GaloisField 2 f)) : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 f)) w) :
    ∀ u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      (u : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) ∈
        ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
          glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ →
      LinearMap.det (actK u) = 1 := by
  let H := glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e
  let φ : H →* K :=
    (LinearMap.det : (LinearMap.range (Matrix.mulVecLin e) →ₗ[K]
      LinearMap.range (Matrix.mulVecLin e)) →* K).comp actK
  let ψ : H →* Kˣ := φ.toHomUnits
  have htop : (⊤ : Subgroup H).map H.subtype = H := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨y, -, hy⟩ := hx
      exact hy ▸ y.2
    · intro hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  have hmap : (⁅(⊤ : Subgroup H), ⊤⁆ : Subgroup H).map H.subtype = ⁅H, H⁆ := by
    rw [Subgroup.map_commutator, htop]
  have hker : ⁅(⊤ : Subgroup H), ⊤⁆ ≤ (⊥ : Subgroup Kˣ).comap ψ := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_comap, Subgroup.mem_bot, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  intro u hu
  have hu' : H.subtype u ∈ (⁅(⊤ : Subgroup H), ⊤⁆ : Subgroup H).map H.subtype := by
    rw [hmap]
    exact hu
  rw [Subgroup.mem_map] at hu'
  obtain ⟨v, hv, hvu⟩ := hu'
  have hvu' : v = u := Subtype.ext hvu
  rw [hvu'] at hv
  have h1 : ψ u = 1 := by
    have := hker hv
    rwa [Subgroup.mem_comap, Subgroup.mem_bot] at this
  have h2 : (ψ u : K) = 1 := by rw [h1]; rfl
  simpa [φ, ψ] using h2

private lemma fePSL_blockKAction_blockK_pos
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (K : Type) [Field K]  [Algebra (GaloisField 2 f) K]
    [Module K (LinearMap.range (Matrix.mulVecLin e))]
    [IsScalarTower (GaloisField 2 f) K (LinearMap.range (Matrix.mulVecLin e))]
    (actK : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e →*
      Module.End K (LinearMap.range (Matrix.mulVecLin e)))
    (_hact : ∀ (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e)
      (w : LinearMap.range (Matrix.mulVecLin e)),
      (actK u w : Fin (m + 1) → GaloisField 2 f) =
        Matrix.mulVec ((u : Matrix.SpecialLinearGroup (Fin (m + 1))
          (GaloisField 2 f)) : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 f)) w)
    (_hinj : Function.Injective actK) :
    1 ≤ Module.finrank K (LinearMap.range (Matrix.mulVecLin e)) := by
  have hne : LinearMap.range (Matrix.mulVecLin e) ≠ ⊥ := by
    intro hbot
    have hf : Matrix.mulVecLin e = 0 := LinearMap.range_eq_bot.mp hbot
    have h2 : e = 0 := by
      ext i j
      have h := congrFun (congrArg (fun g : (Fin (m + 1) → GaloisField 2 f) →ₗ[GaloisField 2 f]
          (Fin (m + 1) → GaloisField 2 f) => g (Pi.single j (1 : GaloisField 2 f))) hf) i
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply] using h
    exact he.2.2.1 h2
  haveI : Module.Finite K (LinearMap.range (Matrix.mulVecLin e)) :=
    Module.Finite.of_restrictScalars_finite (GaloisField 2 f) K
      (LinearMap.range (Matrix.mulVecLin e))
  haveI : Nontrivial (LinearMap.range (Matrix.mulVecLin e)) :=
    Submodule.nontrivial_iff_ne_bot.mpr hne
  exact (Module.finrank_pos_iff_of_free (R := K)
    (M := LinearMap.range (Matrix.mulVecLin e))).mpr inferInstance

private lemma fePSL_blockKAction_det_one_range
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (K : Type) [Field K] [Finite K] [Algebra (GaloisField 2 f) K]
    [Module K (LinearMap.range (Matrix.mulVecLin e))]
    [IsScalarTower (GaloisField 2 f) K (LinearMap.range (Matrix.mulVecLin e))]
    (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →ₐ[GaloisField 2 f] K)
    (hcomp : ∀ (a : Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
      (w : LinearMap.range (Matrix.mulVecLin e)),
      ((π a • w : LinearMap.range (Matrix.mulVecLin e)) : Fin (m + 1) → GaloisField 2 f) =
        Matrix.mulVec (a : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 f)) (w : Fin (m + 1) → GaloisField 2 f))
    (actK : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e →*
      Module.End K (LinearMap.range (Matrix.mulVecLin e)))
    (hact : ∀ (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e)
      (w : LinearMap.range (Matrix.mulVecLin e)),
      (actK u w : Fin (m + 1) → GaloisField 2 f) =
        Matrix.mulVec ((u : Matrix.SpecialLinearGroup (Fin (m + 1))
          (GaloisField 2 f)) : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 f)) w) :
    ∀ g : LinearMap.range (Matrix.mulVecLin e) →ₗ[K] LinearMap.range (Matrix.mulVecLin e),
      LinearMap.det g = 1 → g ∈ Set.range actK := by
  exact fePSL_blockKAction_det_one_mem m f S hS he K π hcomp actK hact

private lemma fePSL_blockKAction_commutator_iso_group
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (K : Type) [Field K] [Finite K] [Algebra (GaloisField 2 f) K]
    [Module K (LinearMap.range (Matrix.mulVecLin e))]
    [IsScalarTower (GaloisField 2 f) K (LinearMap.range (Matrix.mulVecLin e))]
    (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →ₐ[GaloisField 2 f] K)
    (hcomp : ∀ (a : Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
      (w : LinearMap.range (Matrix.mulVecLin e)),
      ((π a • w : LinearMap.range (Matrix.mulVecLin e)) : Fin (m + 1) → GaloisField 2 f) =
        Matrix.mulVec (a : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 f)) (w : Fin (m + 1) → GaloisField 2 f))
    (hK4 : 4 ≤ Nat.card K)
    (actK : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e →*
      Module.End K (LinearMap.range (Matrix.mulVecLin e)))
    (hact : ∀ (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e)
      (w : LinearMap.range (Matrix.mulVecLin e)),
      (actK u w : Fin (m + 1) → GaloisField 2 f) =
        Matrix.mulVec ((u : Matrix.SpecialLinearGroup (Fin (m + 1))
          (GaloisField 2 f)) : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 f)) w)
    (hinj : Function.Injective actK) :
    Nonempty
      ((⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
        glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ :
        Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))) ≃*
      Matrix.SpecialLinearGroup
        (Fin (Module.finrank K (LinearMap.range (Matrix.mulVecLin e)))) K) := by
  classical
  let W := LinearMap.range (Matrix.mulVecLin e)
  haveI hWfinite : Module.Finite K W :=
    Module.Finite.of_restrictScalars_finite (GaloisField 2 f) K W
  haveI hWfree : Module.Free K W := Module.Free.of_divisionRing K W
  let d := Module.finrank K W
  let b : Module.Basis (Fin d) K W := Module.finBasis K W
  let SLsub : Subgroup (Module.End K W)ˣ :=
    (LinearMap.det.comp (Units.coeHom (Module.End K W))).ker
  have hpos : 1 ≤ d :=
    fePSL_blockKAction_blockK_pos m f S he K actK hact hinj
  have hK2 : Nat.card K ≠ 2 := by omega
  have hK3 : Nat.card K ≠ 3 := by omega
  haveI hperfSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin d) K) := by
    by_cases hd : 2 ≤ d
    · exact CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_perfect d K hd
        (Or.inr hK2) (Or.inr hK3)
    · have hd1 : d = 1 := by omega
      rw [hd1]
      infer_instance
  let eGL : (Module.End K W)ˣ ≃* Matrix.GeneralLinearGroup (Fin d) K :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv
  have hmapSL : SLsub.map eGL.toMonoidHom =
      (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin d) K →* Kˣ).ker := by
    ext A
    rw [Subgroup.mem_map_equiv]
    change eGL.symm A ∈ (LinearMap.det.comp (Units.coeHom (Module.End K W))).ker ↔
      A ∈ (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin d) K →* Kˣ).ker
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Units.coeHom_apply, MonoidHom.mem_ker,
      Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    change LinearMap.det (Matrix.toLin b b (A : Matrix (Fin d) (Fin d) K)) = 1 ↔
      (A : Matrix (Fin d) (Fin d) K).det = 1
    rw [LinearMap.det_toLin]
  let eSLsub : SLsub ≃* (Matrix.GeneralLinearGroup.det :
      Matrix.GeneralLinearGroup (Fin d) K →* Kˣ).ker :=
    (SLsub.equivMapOfInjective eGL.toMonoidHom eGL.injective).trans
      (MulEquiv.subgroupCongr hmapSL)
  let eFinal : SLsub ≃* Matrix.SpecialLinearGroup (Fin d) K :=
    eSLsub.trans Matrix.SpecialLinearGroup.toGLKerEquiv.symm
  haveI hPerfSub : Group.IsPerfect SLsub :=
    Group.IsPerfect.ofSurjective (f := eFinal.symm.toMonoidHom) eFinal.symm.surjective
  let H := glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e
  let φ : H →* (Module.End K W)ˣ := actK.toHomUnits
  have hφinj : Function.Injective φ := by
    intro u v huv
    apply hinj
    have h : (φ u : Module.End K W) = (φ v : Module.End K W) :=
      congrArg (fun x : (Module.End K W)ˣ => (x : Module.End K W)) huv
    simpa only [φ, MonoidHom.coe_toHomUnits] using h
  have hSLsub_le_range : SLsub ≤ φ.range := by
    intro u hu
    have hdet : LinearMap.det (u : Module.End K W) = 1 := by
      simpa only [SLsub, MonoidHom.mem_ker,
        MonoidHom.comp_apply, Units.coeHom_apply] using hu
    obtain ⟨v, hv⟩ :=
      fePSL_blockKAction_det_one_range m f S hS he K π hcomp actK hact
        (u : Module.End K W) hdet
    refine MonoidHom.mem_range.mpr ⟨v, ?_⟩
    apply Units.ext
    rw [MonoidHom.coe_toHomUnits]
    exact hv
  have hmapTop : (⊤ : Subgroup H).map H.subtype = H := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hmapSub : (⁅(⊤ : Subgroup H), ⊤⁆ : Subgroup H).map H.subtype = ⁅H, H⁆ := by
    rw [Subgroup.map_commutator, hmapTop]
  have hmapPhi : (⁅(⊤ : Subgroup H), ⊤⁆ : Subgroup H).map φ = SLsub := by
    apply le_antisymm
    · rw [Subgroup.map_commutator, Subgroup.map_top]
      rw [Subgroup.commutator_le]
      intro x hx y hy
      obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hx
      obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp hy
      have hmem : (((⁅u, v⁆ : H) : Matrix.SpecialLinearGroup (Fin (m + 1))
          (GaloisField 2 f))) ∈ ⁅H, H⁆ := by
        rw [← hmapSub, Subgroup.mem_map]
        exact ⟨⁅u, v⁆,
          Subgroup.commutator_mem_commutator (Subgroup.mem_top u) (Subgroup.mem_top v), rfl⟩
      have hdet := fePSL_blockKAction_commutator_det_one m f S he K actK hact
        (⁅u, v⁆ : H) hmem
      change LinearMap.det
        ((⁅φ u, φ v⁆ : (Module.End K W)ˣ) : Module.End K W) = 1
      rw [← map_commutatorElement φ u v]
      change LinearMap.det (actK (⁅u, v⁆ : H)) = 1
      exact hdet
    · rw [Subgroup.map_commutator, Subgroup.map_top]
      have hperf := Subgroup.commutator_eq_self (H := SLsub)
      rw [← hperf]
      exact Subgroup.commutator_mono hSLsub_le_range hSLsub_le_range
  let ePhi : (⁅(⊤ : Subgroup H), ⊤⁆ : Subgroup H) ≃* SLsub :=
    ((⁅(⊤ : Subgroup H), ⊤⁆ : Subgroup H).equivMapOfInjective φ hφinj).trans
      (MulEquiv.subgroupCongr hmapPhi)
  let eH : (⁅(⊤ : Subgroup H), ⊤⁆ : Subgroup H) ≃*
      (⁅H, H⁆ : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1))
        (GaloisField 2 f))) :=
    ((⁅(⊤ : Subgroup H), ⊤⁆ : Subgroup H).equivMapOfInjective H.subtype
      H.subtype_injective).trans (MulEquiv.subgroupCongr hmapSub)
  exact ⟨eH.symm.trans (ePhi.trans eFinal)⟩

private lemma fePSL_blockKAction_commutator_iso_basis
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (K : Type) [Field K] [Finite K] [Algebra (GaloisField 2 f) K]
    [Module K (LinearMap.range (Matrix.mulVecLin e))]
    [IsScalarTower (GaloisField 2 f) K (LinearMap.range (Matrix.mulVecLin e))]
    (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →ₐ[GaloisField 2 f] K)
    (hcomp : ∀ (a : Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
      (w : LinearMap.range (Matrix.mulVecLin e)),
      ((π a • w : LinearMap.range (Matrix.mulVecLin e)) : Fin (m + 1) → GaloisField 2 f) =
        Matrix.mulVec (a : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 f)) (w : Fin (m + 1) → GaloisField 2 f))
    (hK4 : 4 ≤ Nat.card K)
    (actK : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e →*
      Module.End K (LinearMap.range (Matrix.mulVecLin e)))
    (hact : ∀ (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e)
      (w : LinearMap.range (Matrix.mulVecLin e)),
      (actK u w : Fin (m + 1) → GaloisField 2 f) =
        Matrix.mulVec ((u : Matrix.SpecialLinearGroup (Fin (m + 1))
          (GaloisField 2 f)) : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 f)) w)
    (hinj : Function.Injective actK) :
    1 ≤ Module.finrank K (LinearMap.range (Matrix.mulVecLin e)) ∧ Nonempty
      ((⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
        glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ :
        Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))) ≃*
      Matrix.SpecialLinearGroup
        (Fin (Module.finrank K (LinearMap.range (Matrix.mulVecLin e)))) K) := by
  exact ⟨fePSL_blockKAction_blockK_pos m f S he K actK hact hinj,
    fePSL_blockKAction_commutator_iso_group m f S hS he K π hcomp hK4 actK hact hinj⟩

private lemma fePSL_blockKAction_commutator_iso
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (K : Type) [Field K] [Finite K] [Algebra (GaloisField 2 f) K]
    [Module K (LinearMap.range (Matrix.mulVecLin e))]
    [IsScalarTower (GaloisField 2 f) K (LinearMap.range (Matrix.mulVecLin e))]
    (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →ₐ[GaloisField 2 f] K)
    (hcomp : ∀ (a : Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
      (w : LinearMap.range (Matrix.mulVecLin e)),
      ((π a • w : LinearMap.range (Matrix.mulVecLin e)) : Fin (m + 1) → GaloisField 2 f) =
        Matrix.mulVec (a : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 f)) (w : Fin (m + 1) → GaloisField 2 f))
    (hK4 : 4 ≤ Nat.card K)
    (actK : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e →*
      Module.End K (LinearMap.range (Matrix.mulVecLin e)))
    (hact : ∀ (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e)
      (w : LinearMap.range (Matrix.mulVecLin e)),
      (actK u w : Fin (m + 1) → GaloisField 2 f) =
        Matrix.mulVec ((u : Matrix.SpecialLinearGroup (Fin (m + 1))
          (GaloisField 2 f)) : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 f)) w)
    (hinj : Function.Injective actK) :
    ∃ m' : ℕ, 1 ≤ m' ∧ Nonempty
      ((⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
        glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ :
        Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))) ≃*
      Matrix.SpecialLinearGroup (Fin m') K) := by
  obtain ⟨h1, iso⟩ :=
    fePSL_blockKAction_commutator_iso_basis m f S hS he K π hcomp hK4 actK hact hinj
  exact ⟨Module.finrank K (LinearMap.range (Matrix.mulVecLin e)), h1, iso⟩

private lemma fePSL_blockGroup_commutator_slK
    (m f : ℕ) (hf : 1 ≤ f) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (_hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (K : Type) [Field K] [Finite K] [Algebra (GaloisField 2 f) K]
    (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →ₐ[GaloisField 2 f] K)
    (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (Fin (m + 1)) (Fin (m + 1))
      (GaloisField 2 f)) * e = 0)
    (hπdeg : Module.finrank (GaloisField 2 f) K =
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) :
    ∃ m' : ℕ, 1 ≤ m' ∧ Nonempty
      ((⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
        glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ :
        Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))) ≃*
      Matrix.SpecialLinearGroup (Fin m') K) := by
  obtain ⟨hmod, htower, actK, hcomp, hact⟩ :=
    fePSL_blockKAction m f S hS he K π hπsurj hπker
  letI : Module K (LinearMap.range (Matrix.mulVecLin e)) := hmod
  letI : IsScalarTower (GaloisField 2 f) K (LinearMap.range (Matrix.mulVecLin e)) := htower
  have hKcard : Nat.card K = 2 ^ (f * blockDegree
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) :=
    fePSL_blockCard f _ hf hπdeg
  have hK4 : 4 ≤ Nat.card K :=
    fePSL_blockCard_ge_four f _ hf hdeg hKcard
  exact fePSL_blockKAction_commutator_iso m f S hS he K π hcomp hK4 actK hact
    (fePSL_blockKAction_injective m f S he K actK hact)

private lemma fePSL_blockFactor_coordinate
    (m f : ℕ) (hf : 1 ≤ f) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (K : Type) [Field K] [Finite K] [Algebra (GaloisField 2 f) K]
    (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →ₐ[GaloisField 2 f] K)
    (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (Fin (m + 1)) (Fin (m + 1))
      (GaloisField 2 f)) * e = 0)
    (hπdeg : Module.finrank (GaloisField 2 f) K =
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (n : ℕ) (D : Fin n → Type) [∀ i, Field (D i)]  (d : Fin n → ℕ)
    (θ : (∀ i, GL (Fin (d i)) (D i)) →* GL (Fin (m + 1)) (GaloisField 2 f))
    (_hd : ∀ i, 0 < d i) (_hθinj : Function.Injective θ)
    (_hθrange : θ.range = Subgroup.centralizer
      (Subgroup.closure S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))) :
    ∃ (m' : ℕ) (D' : Type) (_ : Field D') (_ : Finite D'),
      1 ≤ m' ∧ Nat.card D' = Nat.card K ∧
      Nonempty ((⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
        glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ :
        Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))) ≃*
      Matrix.SpecialLinearGroup (Fin m') D') := by
  obtain ⟨m', hm'1, iso⟩ :=
    fePSL_blockGroup_commutator_slK m f hf S hS hodd he hdeg K π hπsurj hπker hπdeg
  exact ⟨m', K, inferInstance, inferInstance, hm'1, rfl, iso⟩

private lemma fePSL_blockFactorField
    (m f : ℕ) (hf : 1 ≤ f) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (K : Type) [Field K] [Finite K] [Algebra (GaloisField 2 f) K]
    (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →ₐ[GaloisField 2 f] K)
    (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (Fin (m + 1)) (Fin (m + 1))
      (GaloisField 2 f)) * e = 0)
    (hπdeg : Module.finrank (GaloisField 2 f) K =
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) :
    ∃ (m' : ℕ) (D : Type) (_ : Field D) (_ : Finite D),
      1 ≤ m' ∧ Nat.card D = Nat.card K ∧
      Nonempty ((⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
        glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ :
        Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))) ≃*
      Matrix.SpecialLinearGroup (Fin m') D) := by
  obtain ⟨n, D, hDfield, hDfin, d, θ, hd, hθinj, hθrange⟩ :=
    fePSL_blockFactor_centralizer m f S hS hodd
  letI : ∀ i, Field (D i) := hDfield
  letI : ∀ i, Finite (D i) := hDfin
  exact fePSL_blockFactor_coordinate m f hf S hS hodd he hdeg K π hπsurj hπker hπdeg
    n D d θ hd hθinj hθrange

private lemma fePSL_blockFactor_fieldIso
    {D K : Type} [Field D] [Finite D] [Field K] [Finite K]
    (h : Nat.card D = Nat.card K) : Nonempty (D ≃+* K) :=
  CFSG.RankThree.PartOne.CTP.nonempty_ringEquiv_of_natCard_eq h

private lemma fePSL_blockFactor_transport
    {D K : Type} [Field D] [Field K] {m' : ℕ} (σ : D ≃+* K)
    {G : Type} [Group G] (hiso : Nonempty (G ≃* Matrix.SpecialLinearGroup (Fin m') D)) :
    Nonempty (G ≃* Matrix.SpecialLinearGroup (Fin m') K) :=
  hiso.map fun e =>
    e.trans (CFSG.GorensteinWalter.FieldTransport.specialLinearGroupMulEquiv σ)

private lemma fePSL_blockGroup_commutator_sl
    (m f : ℕ) (hf : 1 ≤ f) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (K : Type) [Field K] [Finite K] [Algebra (GaloisField 2 f) K]
    (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →ₐ[GaloisField 2 f] K)
    (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (Fin (m + 1)) (Fin (m + 1))
      (GaloisField 2 f)) * e = 0)
    (hπdeg : Module.finrank (GaloisField 2 f) K =
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) :
    ∃ m' : ℕ, 1 ≤ m' ∧ Nonempty
      ((⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
        glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ :
        Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))) ≃*
      Matrix.SpecialLinearGroup (Fin m') K) := by
  obtain ⟨m', D, hDfield, hDfin, hm'1, hDcard, hiso⟩ :=
    fePSL_blockFactorField m f hf S hS hodd he hdeg K π hπsurj hπker hπdeg
  letI : Field D := hDfield
  letI : Finite D := hDfin
  obtain ⟨σ⟩ := fePSL_blockFactor_fieldIso hDcard
  exact ⟨m', hm'1, fePSL_blockFactor_transport σ hiso⟩

private lemma fePSL_blockGroup_rank_two
    (m f : ℕ) {S : Set (GL (Fin (m + 1)) (GaloisField 2 f))}
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    {J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))}
    {K : Type} [Field K] {m' : ℕ}
    (hJe : IsComponentOf J' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆)
    (hiso : Nonempty ((⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ :
      Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))) ≃*
      Matrix.SpecialLinearGroup (Fin m') K)) :
    2 ≤ m' := by
  by_contra h
  have hm' : m' ≤ 1 := by omega
  haveI : Subsingleton (Fin m') :=
    ⟨fun i j => Fin.ext (by have := i.isLt; have := j.isLt; omega)⟩
  haveI : Subsingleton (Matrix.SpecialLinearGroup (Fin m') K) := inferInstance
  let H := ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
    glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆
  obtain ⟨φ⟩ := hiso
  haveI : Subsingleton H := ⟨fun a b => φ.injective (Subsingleton.elim (φ a) (φ b))⟩
  haveI : Nontrivial (J' ⧸ Subgroup.center J') := hJe.2.2.2.toNontrivial
  haveI : Nontrivial J' := (QuotientGroup.mk'_surjective (Subgroup.center J')).nontrivial
  obtain ⟨x, y, hxy⟩ := (inferInstance : Nontrivial J')
  exact hxy (Subtype.ext (congrArg (fun z : H => (z :
      Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)))
    (Subsingleton.elim (⟨(x : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)),
      hJe.1 x.2⟩ : H) ⟨(y : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)),
      hJe.1 y.2⟩)))

private lemma fePSL_blockGroup_commutator_iso_blockField
    (m f : ℕ) (hf : 1 ≤ f) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    {J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))}
    (hJe : IsComponentOf J' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆)
    (K : Type) [Field K] [Finite K] [Algebra (GaloisField 2 f) K]
    (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →ₐ[GaloisField 2 f] K)
    (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (Fin (m + 1)) (Fin (m + 1))
      (GaloisField 2 f)) * e = 0)
    (hπdeg : Module.finrank (GaloisField 2 f) K =
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) :
    ∃ m' : ℕ, 2 ≤ m' ∧ Nonempty
      ((⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
        glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ :
        Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))) ≃*
      Matrix.SpecialLinearGroup (Fin m') K) := by
  obtain ⟨m', _hm'1, hiso⟩ :=
    fePSL_blockGroup_commutator_sl m f hf S hS hodd he hdeg K π hπsurj hπker hπdeg
  exact ⟨m', fePSL_blockGroup_rank_two (m := m) (f := f) (S := S) hJe hiso, hiso⟩

private lemma fePSL_blockGroup_commutator_iso
    (m f : ℕ) (hf : 1 ≤ f) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    {J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))}
    (hJe : IsComponentOf J' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆)
    (K : Type) [Field K] [Finite K]
    (hKcard : Nat.card K = 2 ^ (f * blockDegree
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)) :
    ∃ m' : ℕ, 2 ≤ m' ∧ Nonempty
      ((⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
        glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ :
        Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))) ≃*
      Matrix.SpecialLinearGroup (Fin m') K) := by
  classical
  obtain ⟨K₀, hK₀field, hK₀alg, hK₀fin, π, hπsurj, hπker, hπdeg⟩ :=
    exists_blockField hS hodd he
  letI : Field K₀ := hK₀field
  letI : Finite K₀ := hK₀fin
  have hK₀card : Nat.card K₀ = 2 ^ (f * blockDegree
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) :=
    fePSL_blockCard f _ hf hπdeg
  obtain ⟨m', hm'2, ⟨φ⟩⟩ :=
    fePSL_blockGroup_commutator_iso_blockField m f hf S hS hodd he hdeg hJe K₀
      π hπsurj hπker hπdeg
  have hcard : Nat.card K₀ = Nat.card K := by rw [hK₀card, hKcard]
  obtain ⟨σ⟩ := CFSG.RankThree.PartOne.CTP.nonempty_ringEquiv_of_natCard_eq hcard
  exact ⟨m', hm'2, ⟨φ.trans
    (CFSG.GorensteinWalter.FieldTransport.specialLinearGroupMulEquiv σ)⟩⟩

lemma fePSL_dualPair_blockGroup_iso
    (m f : ℕ) (hf : 1 ≤ f) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    {J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))}
    (hJe : IsComponentOf J' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆)
    (K : Type) [Field K] [Finite K]
    (hKcard : Nat.card K = 2 ^ (f * blockDegree
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)) :
    ∃ m' : ℕ, 2 ≤ m' ∧ Nonempty
      ((⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
        glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ :
        Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))) ≃*
      Matrix.SpecialLinearGroup (Fin m') K) :=
  fePSL_blockGroup_commutator_iso m f hf S hS hodd he hdeg hJe K hKcard

lemma fePSL_component_eq
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    {J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))}
    (hJe : IsComponentOf J' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆)
    {K : Type} [Field K] {m' : ℕ} (hm' : 2 ≤ m') (hK4 : 4 ≤ Nat.card K)
    (hiso : Nonempty ((⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ :
      Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))) ≃*
      Matrix.SpecialLinearGroup (Fin m') K)) :
    J' = ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ := by
  let H := ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
    glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆
  have h22 : m' ≠ 2 ∨ Nat.card K ≠ 2 := Or.inr (by omega)
  have h23 : m' ≠ 2 ∨ Nat.card K ≠ 3 := Or.inr (by omega)
  obtain ⟨φ⟩ := hiso
  haveI : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have hSLq : CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin m') K) :=
    ⟨(CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple
        m' K hm' h22 h23).1.commutator_eq_top,
      (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple
        m' K hm' h22 h23).2.1⟩
  have hHq : CFSG.Open.IsQuasisimple H := CFSG.Open.IsQuasisimple.of_mulEquiv φ hSLq
  have hsub : CFSG.Open.IsSubnormal (J'.subgroupOf H) ⊤ :=
    CFSG.Open.IsSubnormal.of_mathlib (CFSG.Assembly.IsSubnormal.subgroupOf hJe.2.1)
  haveI : Group.IsPerfect J' := ⟨hJe.2.2.1⟩
  haveI : Group.IsPerfect (J'.subgroupOf H) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hJe.1).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJe.1).symm.surjective
  rcases CFSG.ComponentClassification.Quasisimple.perfect_subnormal_eq_bot_or_eq_top
    hHq (J'.subgroupOf H) hsub with hbot | htop
  · exfalso
    have hJ'bot : J' = ⊥ := by
      have hdisj : Disjoint J' H := Subgroup.subgroupOf_eq_bot.mp hbot
      rwa [disjoint_iff, inf_eq_left.mpr hJe.1] at hdisj
    have hnt : Nontrivial J' := CFSG.ComponentClassification.Quasisimple.nontrivial hJe.2.2
    rw [hJ'bot] at hnt
    exact not_nontrivial_iff_subsingleton.mpr inferInstance hnt
  · exact le_antisymm hJe.1 (Subgroup.subgroupOf_eq_top.mp htop)

private lemma fePSL_component_iso
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    {J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))}
    {K : Type} [Field K] {m' : ℕ} (_hm' : 2 ≤ m')
    (hiso : Nonempty ((⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ :
      Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))) ≃*
      Matrix.SpecialLinearGroup (Fin m') K))
    (hJeq : J' = ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆) :
    Nonempty (J' ≃* Matrix.SpecialLinearGroup (Fin m') K) := by
  rw [hJeq]
  exact hiso

private lemma fePSL_statedProj
    (m f : ℕ) {J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))}
    {K : Type} [Field K] {m' : ℕ}
    (hiso : Nonempty (J' ≃* Matrix.SpecialLinearGroup (Fin m') K)) :
    Nonempty (↥J' ⧸ Subgroup.center ↥J' ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSL m' K)) := by
  obtain ⟨φ⟩ := hiso
  exact ⟨(QuotientGroup.congr (Subgroup.center J')
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin m') K)) φ
    (Subgroup.map_center_eq φ)).trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj m' K)⟩

private lemma fePSL_quotientCenter
    (m f : ℕ) {X : Type} [Group X] 
    (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* X)
    (hψ : ψ.ker ≤ Subgroup.center
      (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)))
    {J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))}
    (hperf : _root_.commutator ↥J' = ⊤) :
    Nonempty (↥J' ⧸ Subgroup.center ↥J' ≃*
      ↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ)) := by
  let fmap : ↥J' →* ↥(J'.map ψ) :=
    (ψ.comp J'.subtype).codRestrict (J'.map ψ) (fun x => Subgroup.mem_map_of_mem ψ x.2)
  have hf : Function.Surjective fmap := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hkerf : fmap.ker ≤ Subgroup.center ↥J' := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx1 : (x : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      have h := congrArg (fun z : ↥(J'.map ψ) => (z : X)) hx
      simpa [fmap] using h
    have hxc := hψ hx1
    apply Subtype.ext
    simpa using (Subgroup.mem_center_iff.mp hxc
      (y : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)))
  haveI : Group.IsPerfect ↥J' := ⟨hperf⟩
  have hcen : Subgroup.center (↥J' ⧸ fmap.ker) =
      (Subgroup.center ↥J').map (QuotientGroup.mk' fmap.ker) :=
    (CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel
      (QuotientGroup.mk' fmap.ker) (QuotientGroup.mk'_surjective fmap.ker)
      (by rwa [QuotientGroup.ker_mk'])).symm
  let e1 : ↥J' ⧸ fmap.ker ≃* ↥(J'.map ψ) := QuotientGroup.quotientKerEquivOfSurjective fmap hf
  let e2 : ↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ) ≃*
      (↥J' ⧸ fmap.ker) ⧸ Subgroup.center (↥J' ⧸ fmap.ker) :=
    QuotientGroup.congr (Subgroup.center ↥(J'.map ψ)) (Subgroup.center (↥J' ⧸ fmap.ker))
      e1.symm (Subgroup.map_center_eq e1.symm)
  exact ⟨(e2.trans ((QuotientGroup.quotientMulEquivOfEq hcen).trans
    (QuotientGroup.quotientQuotientEquivQuotient _ _ hkerf))).symm⟩

private lemma fePSL_fieldExtModel
    (f d m' : ℕ) (hf : 1 ≤ f) (hd : 2 ≤ d) (hm' : 2 ≤ m')
    {X : Type} [Group X]  (J : Subgroup X)
    {K : Type} [Field K] [Finite K] (hKcard : Nat.card K = 2 ^ (f * d))
    (hproj : Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSL m' K))) :
    ∃ (m'' f' : ℕ), f < f' ∧ LieModel (↥J ⧸ Subgroup.center ↥J) .PSL m'' 2 f' := by
  have hfd : 2 ≤ f * d := by simpa using Nat.mul_le_mul hf hd
  have hpow2 : 2 ^ (f * d) ≠ 2 := by
    intro h2
    have hle : 2 ^ 2 ≤ 2 ^ (f * d) := Nat.pow_le_pow_right (by norm_num) hfd
    omega
  have hpow3 : 2 ^ (f * d) ≠ 3 := by
    intro h3
    have hle : 2 ^ 2 ≤ 2 ^ (f * d) := Nat.pow_le_pow_right (by norm_num) hfd
    omega
  have hadm : CFSG.Open.StatedLieAdmissible .PSL m' 2 (f * d) :=
    ⟨Nat.prime_two, by omega, hm', fun h => hpow2 (congrArg Prod.snd h),
      fun h => hpow3 (congrArg Prod.snd h)⟩
  have hPSL : StatedLieTag.PSL ∈ CFSG.Blueprint.classicalTags := by decide
  have hclass : CFSG.Open.StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL m' 2 (f * d) := by
    refine ⟨hadm, K, ‹Field K›, ‹Finite K›, hKcard, ?_⟩
    exact hproj
  refine ⟨m', f * d, ?_, ?_⟩
  · have hf0 : 0 < f := by omega
    have hd1 : 1 < d := by omega
    simpa using Nat.mul_lt_mul_of_pos_left hd1 hf0
  · exact Or.inl ⟨hPSL, hclass⟩

theorem ggSixLSevenFieldExtModel_PSL (m f : ℕ) (hf : 1 ≤ f) {X : Type} [Group X] 
    (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))}
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hJe : IsComponentOf J' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) :
    ∃ (m'' f' : ℕ), f < f' ∧
      LieModel (↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ)) .PSL m'' 2 f' := by
  classical
  obtain ⟨K, hKfield, hKalg, hKfinite, π, hπsurj, hπker, hπdeg⟩ :=
    fePSL_blockField m f S hS hodd he
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  have hKcard : Nat.card K = 2 ^ (f * blockDegree
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) :=
    fePSL_blockCard f _ hf hπdeg
  have hK4 : 4 ≤ Nat.card K :=
    fePSL_blockCard_ge_four f _ hf hdeg hKcard
  obtain ⟨m', hm'2, hiso⟩ :=
    fePSL_dualPair_blockGroup_iso m f hf S hS hodd he hdeg hJe K hKcard
  have hJeq := fePSL_component_eq m f S hJe hm'2 hK4 hiso
  have hisoJ : Nonempty (J' ≃* Matrix.SpecialLinearGroup (Fin m') K) :=
    fePSL_component_iso m f S hm'2 hiso hJeq
  obtain ⟨η⟩ := fePSL_statedProj m f hisoJ
  obtain ⟨ξ⟩ := fePSL_quotientCenter m f ψ hψ hJe.2.2.1
  exact fePSL_fieldExtModel f (blockDegree (Algebra.adjoin (GaloisField 2 f)
      (Units.val '' S)) e) m' hf hdeg hm'2 (J'.map ψ) hKcard ⟨ξ.symm.trans η⟩

theorem ggSixLSevenFieldExtCase_PSL (m f : ℕ) (hf : 1 ≤ f) {X : Type} [Group X] 
    (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))}
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hJe : IsComponentOf J' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) :
    GGSixLSevenFieldExtCase (J'.map ψ) .PSL f := by
  obtain ⟨m'', f', hlt, hM⟩ := ggSixLSevenFieldExtModel_PSL m f hf ψ hψ S hS hodd he hJe hdeg
  exact ⟨.PSL, m'', f', hlt, hM, by rintro ⟨-, -, h | h⟩ <;> exact absurd h (by decide)⟩

end CFSG.StandardType.ClassicalPosition
