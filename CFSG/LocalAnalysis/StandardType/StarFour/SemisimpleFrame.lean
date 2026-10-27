module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Maschke
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.FiniteLength

public section

namespace CFSG.StandardType.StarFour

open scoped DirectSum

structure SemiFrame (F : Type) [Field F] {P : Type} [CommGroup P] {V : Type} [AddCommGroup V]
    [Module F V] (ρ : P →* (V ≃ₗ[F] V)) where
  r : ℕ
  E : Fin r → Type
  [instField : ∀ i, Field (E i)]
  [instAlgebra : ∀ i, Algebra F (E i)]
  [instFinite : ∀ i, Finite (E i)]
  m : Fin r → ℕ
  Φ : V ≃ₗ[F] (∀ i, Fin (m i) → E i)
  χ : ∀ i, P →* (E i)ˣ
  act : ∀ (p : P) (v : V) (i : Fin r), Φ (ρ p v) i = ((χ i p : (E i)ˣ) : E i) • Φ v i
  gen : ∀ i, Algebra.adjoin F (Set.range fun p : P => ((χ i p : (E i)ˣ) : E i)) = ⊤
  comm : ∀ g : V ≃ₗ[F] V, (∀ p : P, g * ρ p = ρ p * g) ↔
    ∀ i, ∃ B : (Fin (m i) → E i) →ₗ[E i] (Fin (m i) → E i), ∀ v, Φ (g v) i = B (Φ v i)

attribute [instance] SemiFrame.instField SemiFrame.instAlgebra SemiFrame.instFinite

private noncomputable def monoidAlgebraOfUnit {F : Type} [CommSemiring F] {P : Type} [Group P] :
    P →* (MonoidAlgebra F P)ˣ where
  toFun p :=
    ⟨MonoidAlgebra.of F P p, MonoidAlgebra.of F P p⁻¹,
      by rw [← map_mul, mul_inv_cancel, map_one],
      by rw [← map_mul, inv_mul_cancel, map_one]⟩
  map_one' := Units.ext (map_one (MonoidAlgebra.of F P))
  map_mul' p q := Units.ext (map_mul (MonoidAlgebra.of F P) p q)

private lemma of_smul_eq_mk_smul {F : Type} [CommRing F] {P : Type} [CommGroup P]
    (I : Ideal (MonoidAlgebra F P)) (p : P) (y : MonoidAlgebra F P ⧸ I) :
    (MonoidAlgebra.of F P p) • y =
      (Ideal.Quotient.mk I (MonoidAlgebra.of F P p)) • y := rfl

private lemma adjoin_range_of_eq_top {F : Type} [Field F] {P : Type} [CommGroup P] :
    Algebra.adjoin F (Set.range fun p : P => MonoidAlgebra.of F P p) = ⊤ := by
  have hrange : (fun p : P => MonoidAlgebra.of F P p) = MonoidAlgebra.basis P F := by
    funext p
    rw [MonoidAlgebra.basis_apply, MonoidAlgebra.of_apply]
  have hspan : Submodule.span F (Set.range fun p : P => MonoidAlgebra.of F P p) = ⊤ := by
    rw [hrange, (MonoidAlgebra.basis P F).span_eq]
  have hle : Submodule.span F (Set.range fun p : P => MonoidAlgebra.of F P p) ≤
      (Algebra.adjoin F (Set.range fun p : P => MonoidAlgebra.of F P p)).toSubmodule :=
    Submodule.span_le.mpr fun x hx => Algebra.subset_adjoin hx
  rw [hspan] at hle
  exact eq_top_iff.mpr hle

private lemma adjoin_range_quotient {F : Type} [Field F] {P : Type} [CommGroup P]
    (I : Ideal (MonoidAlgebra F P)) [I.IsMaximal] :
    Algebra.adjoin F (Set.range fun p : P =>
      Ideal.Quotient.mk I (MonoidAlgebra.of F P p)) = ⊤ := by
  have hmap : (Algebra.adjoin F (Set.range fun p : P => MonoidAlgebra.of F P p)).map
      (Ideal.Quotient.mkₐ F I) = ⊤ := by
    rw [adjoin_range_of_eq_top, Algebra.map_top]
    exact (AlgHom.range_eq_top _).mpr (Ideal.Quotient.mkₐ_surjective F I)
  rw [AlgHom.map_adjoin] at hmap
  simpa only [Set.range_comp', Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk] using hmap

theorem exists_semiFrame {F : Type} [Field F] [Finite F] {P : Type} [CommGroup P] [Finite P]
    (hP : (Nat.card P : F) ≠ 0) {V : Type} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : P →* (V ≃ₗ[F] V)) : Nonempty (SemiFrame F ρ) := by
  classical
  haveI : NeZero (Nat.card P : F) := ⟨hP⟩
  let A := MonoidAlgebra F P
  haveI hss : IsSemisimpleRing A := inferInstance
  haveI : IsReduced A := inferInstance
  haveI : IsArtinianRing A := inferInstance
  haveI : IsNoetherianRing A := inferInstance
  haveI : Module.Finite F A := inferInstance
  haveI : Finite A := Module.finite_of_finite F
  haveI : Finite (MaximalSpectrum A) := inferInstance
  haveI : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  let ρ' : Representation F P V :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := F) (M := V)).comp ρ
  let M := ρ'.asModule
  haveI : Module.Finite F M := inferInstance
  haveI : Module.Finite A M := Module.Finite.of_restrictScalars_finite F A M
  let r : ℕ := Fintype.card (MaximalSpectrum A)
  let eqv : Fin r ≃ MaximalSpectrum A := (Fintype.equivFin (MaximalSpectrum A)).symm
  let Ept : MaximalSpectrum A → Type := fun I => A ⧸ I.asIdeal
  letI hEfield : ∀ I, Field (Ept I) := fun I => Ideal.Quotient.field I.asIdeal
  letI hEalg : ∀ I, Algebra F (Ept I) := fun I => inferInstance
  letI hEmod : ∀ I, Module F (Ept I) := fun I => Algebra.toModule
  haveI hEfin : ∀ I, Finite (Ept I) := fun I =>
    Finite.of_surjective (Ideal.Quotient.mk I.asIdeal) Ideal.Quotient.mk_surjective
  let T : MaximalSpectrum A → Submodule A M := fun I => Submodule.torsionBySet A M I.asIdeal
  haveI hTfin : ∀ I, Module.Finite A (T I) := fun I =>
    Module.Finite.iff_fg.mpr (Submodule.FG.of_le
      (Module.Finite.iff_fg.mp (inferInstance : Module.Finite A (⊤ : Submodule A M))) le_top)
  haveI hTEfin : ∀ I, Module.Finite (Ept I) (T I) := fun I =>
    Module.Finite.of_restrictScalars_finite A (Ept I) (T I)
  haveI hTEfree : ∀ I, Module.Free (Ept I) (T I) := fun I =>
    Module.Free.of_basis (Module.Basis.ofVectorSpace (Ept I) (T I))
  let m : MaximalSpectrum A → ℕ := fun I => Module.finrank (Ept I) (T I)
  let coordA : ∀ I, T I ≃ₗ[A] (Fin (m I) → Ept I) := fun I =>
    ((Module.finBasis (Ept I) (T I)).equivFun).restrictScalars A
  have hp : ((Finset.univ : Finset (MaximalSpectrum A)) : Set (MaximalSpectrum A)).Pairwise
      fun I J => I.asIdeal ⊔ J.asIdeal = ⊤ :=
    fun I _ J _ hIJ => I.isMaximal.coprime_of_ne J.isMaximal fun h => hIJ (MaximalSpectrum.ext h)
  have hbot : (⨅ I : MaximalSpectrum A, I.asIdeal) = ⊥ := by
    rw [← IsArtinianRing.nilradical_eq_iInf (R := A), nilradical_eq_zero]
    rfl
  have htors : Submodule.torsionBySet A M (⊥ : Ideal A) = ⊤ :=
    (Module.isTorsionBySet_iff_torsionBySet_eq_top _).mp (by
      intro x a
      have ha : (a : A) = 0 := Ideal.mem_bot.mp a.2
      rw [ha, zero_smul])
  have hind : iSupIndep T := iSupIndep_iff_supIndep_univ.mpr
    (Submodule.supIndep_torsionBySet_ideal (R := A) (M := M)
      (p := fun I : MaximalSpectrum A => I.asIdeal) (S := Finset.univ) hp)
  have hsup : iSup T = ⊤ := by
    have h := Submodule.iSup_torsionBySet_ideal_eq_torsionBySet_iInf (R := A) (M := M)
      (p := fun I : MaximalSpectrum A => I.asIdeal) (S := Finset.univ) hp
    simp only [Finset.mem_univ, iSup_true, iInf_true] at h
    rw [h, hbot, htors]
  have hint : DirectSum.IsInternal T :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hsup
  let eDS : (⨁ I : MaximalSpectrum A, T I) ≃ₗ[A] M :=
    LinearEquiv.ofBijective (DirectSum.coeLinearMap T) hint
  let eProd : (⨁ I : MaximalSpectrum A, T I) ≃ₗ[A] (∀ I, T I) :=
    DirectSum.linearEquivFunOnFintype A (MaximalSpectrum A) (fun I => ↥(T I))
  let Ebig : M ≃ₗ[A] (∀ I, T I) := eDS.symm.trans eProd
  let Ψ : M ≃ₗ[A] (∀ I, Fin (m I) → Ept I) :=
    Ebig.trans (LinearEquiv.piCongrRight coordA)
  let φ : MaximalSpectrum A → Type := fun I => Fin (m I) → Ept I
  let reindexA : (∀ I, φ I) ≃ₗ[A] (∀ i : Fin r, φ (eqv i)) :=
    (LinearEquiv.piCongrLeft (R := A) (φ := φ) eqv).symm
  let Ψr : M ≃ₗ[A] (∀ i : Fin r, φ (eqv i)) := Ψ.trans reindexA
  let Efun : Fin r → Type := fun i => Ept (eqv i)
  let mfun : Fin r → ℕ := fun i => m (eqv i)
  let Φ : V ≃ₗ[F] (∀ i, Fin (mfun i) → Efun i) :=
    (Representation.asModuleEquiv ρ').symm.trans (Ψr.restrictScalars F)
  let χfun : ∀ i : Fin r, P →* (Efun i)ˣ := fun i =>
    (Units.map (Ideal.Quotient.mk (eqv i).asIdeal).toMonoidHom).comp
      (monoidAlgebraOfUnit (F := F) (P := P))
  let frame : SemiFrame F ρ :=
    { r := r
      E := Efun
      m := mfun
      Φ := Φ
      χ := χfun
      act := by
        intro p v i
        have hsymm : (Representation.asModuleEquiv ρ').symm (ρ p v) =
            MonoidAlgebra.of F P p • (Representation.asModuleEquiv ρ').symm v := by
          rw [show ρ p v = ρ' p v from rfl, Representation.asModuleEquiv_symm_map_rho]
        change (Ψr ((Representation.asModuleEquiv ρ').symm (ρ p v))) i =
          ((χfun i p : (Efun i)ˣ) : Efun i) •
            (Ψr ((Representation.asModuleEquiv ρ').symm v)) i
        rw [hsymm, map_smul, Pi.smul_apply]
        funext j
        exact of_smul_eq_mk_smul (F := F) (P := P) _ p _
      gen := by
        intro i
        exact adjoin_range_quotient (F := F) (P := P) (eqv i).asIdeal
      comm := by
        intro g
        constructor
        · intro hg
          have hX : ∀ p : P, Commute (g : Module.End F V) (ρ' p) := by
            intro p
            have h := congrArg (fun e : V ≃ₗ[F] V => (e : Module.End F V)) (hg p)
            show (g : Module.End F V) * ρ' p = ρ' p * (g : Module.End F V)
            simpa [ρ', LinearEquiv.coe_toLinearMap_mul] using h
          have hcomm : ∀ r : A, Commute (g : Module.End F V) ((ρ').asAlgebraHom r) := by
            intro r
            induction r using MonoidAlgebra.induction_on with
            | of p => simpa using hX p
            | add a b ha hb => rw [map_add]; exact ha.add_right hb
            | smul c a ha => rw [map_smul]; exact ha.smul_right c
          let gM : M →ₗ[A] M :=
            { toFun := fun x => (g : Module.End F V) x
              map_add' := fun x y => map_add _ x y
              map_smul' := fun r x => by
                change (g : Module.End F V) ((ρ').asAlgebraHom r x) =
                  (ρ').asAlgebraHom r ((g : Module.End F V) x)
                exact LinearMap.congr_fun (hcomm r).eq x }
          let hlin : (∀ i : Fin r, Fin (mfun i) → Efun i) →ₗ[A]
              (∀ i : Fin r, Fin (mfun i) → Efun i) :=
            (Ψr : M ≃ₗ[A] _).toLinearMap.comp
              (gM.comp (Ψr.symm : _ ≃ₗ[A] M).toLinearMap)
          have hlin_apply : ∀ x : M, hlin (Ψr x) = Ψr (gM x) := by
            intro x
            change (Ψr : M ≃ₗ[A] _) (gM ((Ψr.symm : _ ≃ₗ[A] M)
              ((Ψr : M ≃ₗ[A] _) x))) = (Ψr : M ≃ₗ[A] _) (gM x)
            rw [LinearEquiv.symm_apply_apply]
          let e : Fin r → A := fun i =>
            (IsArtinianRing.equivPi A).symm (Pi.single (M := Ept) (eqv i) 1)
          have he_apply : ∀ (i : Fin r) (I : MaximalSpectrum A),
              Ideal.Quotient.mk I.asIdeal (e i) = Pi.single (M := Ept) (eqv i) 1 I := by
            intro i I
            rw [← IsArtinianRing.equivPi_apply (R := A) (x := e i) (m := I),
              AlgEquiv.apply_symm_apply]
          have he_i : ∀ (i j : Fin r),
              Ideal.Quotient.mk (eqv j).asIdeal (e i) = if j = i then 1 else 0 := by
            intro i j
            rw [he_apply i (eqv j)]
            by_cases h : j = i
            · subst h; simp
            · have h' : eqv j ≠ eqv i := fun hh => h (eqv.injective hh)
              simp [Pi.single_eq_of_ne (Ne.symm h'), h]
          have he_smul : ∀ (i : Fin r) (y : ∀ j : Fin r, Fin (mfun j) → Efun j),
              e i • y = Pi.single i (y i) := by
            intro i y
            funext j k
            have hact : (e i • y) j k = (Ideal.Quotient.mk (eqv j).asIdeal (e i)) •
                (y j k) := rfl
            rw [hact, he_i i j]
            by_cases h : j = i
            · subst h; simp
            · simp [Pi.single_eq_of_ne h, h]
          intro i
          refine ⟨{ toFun := fun w => hlin (Pi.single i w) i
                    map_add' := ?_
                    map_smul' := ?_ }, ?_⟩
          · intro w w'
            simp only [Pi.single_add, map_add, Pi.add_apply]
          · intro c w
            obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := (eqv i).asIdeal) c
            have h1 : c • w = a • w := by rw [← ha]; rfl
            rw [h1]
            have h2 : Pi.single (M := fun j => Fin (mfun j) → Efun j) i (a • w) =
                a • Pi.single (M := fun j => Fin (mfun j) → Efun j) i w := by
              funext j
              by_cases hj : j = i
              · subst hj; simp
              · simp [Pi.single_eq_of_ne hj]
            rw [h2, hlin.map_smul, Pi.smul_apply, ← ha]
            rfl
          · intro v
            change (Ψr ((Representation.asModuleEquiv ρ').symm (g v))) i =
              hlin (Pi.single (M := fun j => Fin (mfun j) → Efun j) i
                ((Ψr ((Representation.asModuleEquiv ρ').symm v)) i)) i
            have hsymm : (Representation.asModuleEquiv ρ').symm (g v) =
                gM ((Representation.asModuleEquiv ρ').symm v) := rfl
            have hb : hlin (Pi.single (M := fun j => Fin (mfun j) → Efun j) i
                ((Ψr ((Representation.asModuleEquiv ρ').symm v)) i)) i =
                (Ψr ((Representation.asModuleEquiv ρ').symm (g v))) i := by
              have h1 : Pi.single (M := fun j => Fin (mfun j) → Efun j) i
                  (Ψr ((Representation.asModuleEquiv ρ').symm v) i) =
                  e i • Ψr ((Representation.asModuleEquiv ρ').symm v) :=
                (he_smul i _).symm
              rw [h1, hlin.map_smul]
              rw [hlin_apply ((Representation.asModuleEquiv ρ').symm v)]
              rw [he_smul, Pi.single_eq_same, hsymm]
            exact hb.symm
        · intro hB
          choose B hBv using hB
          let gBig : (∀ i : Fin r, Fin (mfun i) → Efun i) →ₗ[A]
              (∀ i : Fin r, Fin (mfun i) → Efun i) :=
            { toFun := fun y i => B i (y i)
              map_add' := by
                intro y z
                funext i
                exact map_add (B i) (y i) (z i)
              map_smul' := by
                intro a y
                funext i
                show B i (a • y i) = a • B i (y i)
                have h1 : a • y i = (Ideal.Quotient.mk (eqv i).asIdeal a) • y i := rfl
                rw [h1, (B i).map_smul]
                rfl }
          let gM : M →ₗ[A] M :=
            (Ψr.symm : _ ≃ₗ[A] M).toLinearMap.comp
              (gBig.comp (Ψr : M ≃ₗ[A] _).toLinearMap)
          have hgm : ∀ x : M, Ψr (gM x) = gBig (Ψr x) := by
            intro x
            change (Ψr : M ≃ₗ[A] _) ((Ψr.symm : _ ≃ₗ[A] M)
              (gBig ((Ψr : M ≃ₗ[A] _) x))) = gBig ((Ψr : M ≃ₗ[A] _) x)
            rw [LinearEquiv.apply_symm_apply]
          have hgM : ∀ v : V, (Representation.asModuleEquiv ρ').symm (g v) =
              gM ((Representation.asModuleEquiv ρ').symm v) := by
            intro v
            apply Ψr.injective
            rw [hgm]
            funext i
            change (Ψr ((Representation.asModuleEquiv ρ').symm (g v))) i =
              B i ((Ψr ((Representation.asModuleEquiv ρ').symm v)) i)
            exact hBv i v
          have hg_apply : ∀ v : V, g v =
              (Representation.asModuleEquiv ρ')
                (gM ((Representation.asModuleEquiv ρ').symm v)) := by
            intro v
            have := congrArg (Representation.asModuleEquiv ρ') (hgM v)
            simpa using this
          intro p
          ext v
          have h1 : (Representation.asModuleEquiv ρ')
              (MonoidAlgebra.of F P p • (Representation.asModuleEquiv ρ').symm v) = ρ p v := by
            rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]
            rfl
          calc g (ρ p v)
              = g ((Representation.asModuleEquiv ρ')
                  (MonoidAlgebra.of F P p • (Representation.asModuleEquiv ρ').symm v)) := by
                rw [h1]
            _ = (Representation.asModuleEquiv ρ')
                  (gM (MonoidAlgebra.of F P p • (Representation.asModuleEquiv ρ').symm v)) :=
                hg_apply _
            _ = (Representation.asModuleEquiv ρ')
                  (MonoidAlgebra.of F P p • gM ((Representation.asModuleEquiv ρ').symm v)) := by
                rw [gM.map_smul]
            _ = ρ p ((Representation.asModuleEquiv ρ')
                  (gM ((Representation.asModuleEquiv ρ').symm v))) := by
                rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]
                rfl
            _ = ρ p (g v) := by rw [← hg_apply] }
  exact ⟨frame⟩

end CFSG.StandardType.StarFour
