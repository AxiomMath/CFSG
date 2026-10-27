module

public import CFSG.LocalAnalysis.StandardType.GGSporKLieZReduce
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.StandardType.GGSporKLieZBlockO2
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.ReducedAlgebra

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.Open Matrix

private instance l937z_gl_instModule (F V : Type*) [Field F] [AddCommGroup V] [Module F V]
    (A : Subalgebra F (Module.End F V)) : Module A V :=
  Module.compHom V (Subalgebra.val A).toRingHom

private instance l937z_gl_instTower (F V : Type*) [Field F] [AddCommGroup V] [Module F V]
    (A : Subalgebra F (Module.End F V)) : IsScalarTower F A V :=
  ⟨fun c a v => by
    change (Subalgebra.val A (c • a)) v = c • ((Subalgebra.val A a) v)
    rw [map_smul]
    rfl⟩

private lemma l937z_gl_centralizer_semisimple
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (S : Set (GL (Fin n) K))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s)) :
    IsSemisimpleRing (Subalgebra.centralizer K (Units.val '' S)) := by
  classical
  let V := Fin n → K
  let e : Matrix (Fin n) (Fin n) K ≃ₐ[K] Module.End K V := Matrix.toLinAlgEquiv'
  let T : Set (Module.End K V) :=
    (fun s : GL (Fin n) K => (e (Units.val s) : Module.End K V)) '' S
  let A := Algebra.adjoin K T
  have hcommT : ∀ t ∈ T, ∀ t' ∈ T, Commute t t' := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩
    exact (hS s hs s' hs').map (e.toMulEquiv.toMonoidHom.comp
      (Units.coeHom (Matrix (Fin n) (Fin n) K)))
  have hpair : T.Pairwise Commute := by
    rintro a ha b hb -
    exact hcommT a ha b hb
  have hTodd : ∀ t ∈ T, ∃ o : ℕ, Odd o ∧ t ^ o = 1 := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨orderOf s, hodd s hs, ?_⟩
    have h1 : ((s : GL (Fin n) K) ^ orderOf s : GL (Fin n) K) = 1 :=
      pow_orderOf_eq_one s
    calc (e (Units.val s) : Module.End K V) ^ orderOf s
        = e ((Units.val s) ^ orderOf s : Matrix _ _ K) := by rw [map_pow]
      _ = e (Units.val (s ^ orderOf s)) := by rw [Units.val_pow_eq_pow_val]
      _ = e (Units.val (1 : GL _ K)) := by rw [h1]
      _ = 1 := by rw [Units.val_one, map_one]
  have hredT : IsReduced (Algebra.adjoin K T) :=
    CFSG.StandardType.ClassicalPosition.isReduced_adjoin_of_commute_of_odd T hcommT hTodd
  letI : CommRing A := Algebra.adjoinCommRingOfComm K (s := T) hpair
  haveI : Module.Finite K A := inferInstance
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  haveI hAsemi : IsSemisimpleRing A := IsArtinianRing.isSemisimpleRing_of_isReduced A
  haveI : IsSemisimpleModule A V := IsSemisimpleRing.isSemisimpleModule
  haveI : Finite V := inferInstance
  haveI : Module.Finite A V := Module.Finite.of_finite
  haveI hEsemi : IsSemisimpleRing (Module.End A V) := IsSemisimpleRing.moduleEnd A V
  let Ψ₁ : Subalgebra.centralizer K (Units.val '' S) ≃+* Subalgebra.centralizer K T :=
  { toFun := fun g => ⟨e (g : Matrix (Fin n) (Fin n) K), by
      rw [Subalgebra.mem_centralizer_iff]
      rintro _ ⟨s, hs, rfl⟩
      rw [← map_mul, ← map_mul,
        (Subalgebra.mem_centralizer_iff K).mp g.2 (Units.val s) ⟨s, hs, rfl⟩]⟩
    invFun := fun g => ⟨e.symm (g : Module.End K V), by
      rw [Subalgebra.mem_centralizer_iff]
      rintro _ ⟨s, hs, rfl⟩
      apply e.injective
      simp only [map_mul, e.apply_symm_apply]
      exact (Subalgebra.mem_centralizer_iff K).mp g.2 (e (Units.val s)) ⟨s, hs, rfl⟩⟩
    left_inv := fun g => by ext; simp
    right_inv := fun g => by ext; simp
    map_mul' := fun g h => by ext; simp
    map_add' := fun g h => by ext; simp }
  let Ψ₂ : Subalgebra.centralizer K T ≃+* Module.End A V :=
  { toFun := fun g =>
      { toFun := (g : Module.End K V),
        map_add' := map_add (g : Module.End K V),
        map_smul' := fun a v => by
          have h := Algebra.commute_of_mem_adjoin_of_forall_mem_commute a.2
            (fun t ht => ((Subalgebra.mem_centralizer_iff K).mp g.2 t ht).symm)
          exact congrArg (fun f : Module.End K V => f v) h.eq }
    invFun := fun g =>
      ⟨{ toFun := g,
         map_add' := map_add g,
         map_smul' := fun c v => by
           have h := g.map_smul (algebraMap K A c) v
           have hc : (algebraMap K A c) • v = c • v := by
             simpa only [Algebra.algebraMap_eq_smul_one, one_smul] using
               (l937z_gl_instTower K V A).smul_assoc c 1 v
           have hc' : (algebraMap K A c) • (g v) = c • (g v) := by
             simpa only [Algebra.algebraMap_eq_smul_one, one_smul] using
               (l937z_gl_instTower K V A).smul_assoc c 1 (g v)
           rw [← hc]
           change g ((algebraMap K A c) • v) = c • g v
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

private lemma l937z_gl_centralizer_wedderburn
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (S : Set (GL (Fin n) K))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s)) :
    ∃ (r : ℕ) (D : Fin r → Type) (_ : ∀ i, DivisionRing (D i))
      (_ : ∀ i, Algebra K (D i))
      (_ : ∀ i, Module.Finite K (D i)) (d : Fin r → ℕ),
      (∀ i, NeZero (d i)) ∧
      Nonempty ((Subalgebra.centralizer K (Units.val '' S)) ≃ₐ[K]
        (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i))) := by
  classical
  let C := Subalgebra.centralizer K (Units.val '' S)
  haveI : IsSemisimpleRing C := l937z_gl_centralizer_semisimple S hS hodd
  haveI : Module.Finite K C := inferInstance
  obtain ⟨r, D, d, hDdiv, hDalg, hRest⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite K C
  obtain ⟨hDfinF, hd, ⟨Φ⟩⟩ := hRest
  exact ⟨r, D, hDdiv, hDalg, hDfinF, d, hd, ⟨Φ⟩⟩

private lemma l937z_gl_wedderburn_factors_finite
    {K : Type} [Field K] [Finite K] {r : ℕ} (D : Fin r → Type) [∀ i, DivisionRing (D i)]
    [∀ i, Algebra K (D i)] [∀ i, Module.Finite K (D i)] :
    ∀ i, Finite (D i) := by
  intro i
  haveI : Finite K := inferInstance
  obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin' K (D i)
  exact Finite.of_surjective (g : (Fin k → K) → D i) hg

private lemma l937z_gl_wedderburn_ringEquiv
    {K : Type} [Field K] {n : ℕ} (S : Set (GL (Fin n) K))
    {r : ℕ} (D : Fin r → Type) [∀ i, DivisionRing (D i)]
    [∀ i, Algebra K (D i)] [∀ i, Module.Finite K (D i)]
    [∀ i, Finite (D i)] (d : Fin r → ℕ)
    (h : Nonempty ((Subalgebra.centralizer K (Units.val '' S)) ≃ₐ[K]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)))) :
    Nonempty ((Subalgebra.centralizer K (Units.val '' S)) ≃+*
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i))) := by
  obtain ⟨e⟩ := h
  exact ⟨e.toRingEquiv⟩

private lemma l937z_gl_centralizer_pi_matrix
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (S : Set (GL (Fin n) K))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s)) :
    ∃ (r : ℕ) (D : Fin r → Type) (_ : ∀ i, Field (D i)) (_ : ∀ i, Finite (D i))
      (_ : ∀ i, Algebra K (D i)) (d : Fin r → ℕ),
      (∀ i, 0 < d i) ∧
      Nonempty ((Subalgebra.centralizer K (Units.val '' S)) ≃+*
        (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i))) := by
  obtain ⟨r, D, hDdiv, hDalg, hDfinF, d, hd, hAlg⟩ :=
    l937z_gl_centralizer_wedderburn S hS hodd
  letI : ∀ i, DivisionRing (D i) := hDdiv
  letI : ∀ i, Algebra K (D i) := hDalg
  letI : ∀ i, Module.Finite K (D i) := hDfinF
  have hFinite : ∀ i, Finite (D i) := l937z_gl_wedderburn_factors_finite (K := K) D
  haveI : ∀ i, Finite (D i) := hFinite
  have hRing : Nonempty ((Subalgebra.centralizer K (Units.val '' S)) ≃+*
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i))) :=
    l937z_gl_wedderburn_ringEquiv (S := S) (D := D) (d := d) hAlg
  exact ⟨r, D, fun i => littleWedderburn (D i), hFinite, hDalg, d,
    fun i => Nat.pos_of_ne_zero (NeZero.ne (d i)), hRing⟩

private lemma l937z_gl_centralizer_units_pi_GL
    {K : Type} [Field K] {n : ℕ} (S : Set (GL (Fin n) K))
    {r : ℕ} (D : Fin r → Type) [∀ i, Field (D i)] (d : Fin r → ℕ)
    (hiso : Nonempty ((Subalgebra.centralizer K (Units.val '' S)) ≃+*
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)))) :
    Nonempty (((Subalgebra.centralizer K (Units.val '' S))ˣ) ≃*
      (∀ i, GL (Fin (d i)) (D i))) := by
  obtain ⟨e⟩ := hiso
  exact ⟨(Units.mapEquiv e.toMulEquiv).trans MulEquiv.piUnits⟩

private lemma l937z_gl_centralizer_units_centralizer
    {K : Type} [Field K] {n : ℕ} (S : Set (GL (Fin n) K)) :
    Nonempty (((Subalgebra.centralizer K (Units.val '' S))ˣ) ≃*
      Subgroup.centralizer (Subgroup.closure S : Set (GL (Fin n) K))) := by
  let C := Subalgebra.centralizer K (Units.val '' S)
  have hunits : C.toSubmonoid.units =
      Subgroup.centralizer (Subgroup.closure S : Set (GL (Fin n) K)) := by
    rw [Subgroup.centralizer_closure]
    ext x
    rw [Submonoid.mem_units_iff, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨h, -⟩
      intro s hs
      exact Units.ext ((Subalgebra.mem_centralizer_iff K).mp h s ⟨s, hs, rfl⟩)
    · intro h
      refine ⟨(Subalgebra.mem_centralizer_iff K).mpr (fun g hg => ?_),
        (Subalgebra.mem_centralizer_iff K).mpr (fun g hg => ?_)⟩
      · obtain ⟨s, hs, rfl⟩ := hg
        exact congrArg (fun u : (Matrix (Fin n) (Fin n) K)ˣ =>
          (u : Matrix (Fin n) (Fin n) K)) (h s hs)
      · obtain ⟨s, hs, rfl⟩ := hg
        have hx : x⁻¹ ∈ Subgroup.centralizer S :=
          Subgroup.inv_mem _ ((Subgroup.mem_centralizer_iff).mpr h)
        simpa using congrArg (fun u : (Matrix (Fin n) (Fin n) K)ˣ =>
          (u : Matrix (Fin n) (Fin n) K))
          ((Subgroup.mem_centralizer_iff).mp hx s hs)
  exact ⟨(Submonoid.unitsEquivUnitsType C.toSubmonoid).symm.trans
    (MulEquiv.subgroupCongr hunits)⟩

private lemma l937z_gl_algebraMap_injective
    {K D : Type*} [Field K] [DivisionRing D] [Algebra K D] :
    Function.Injective (algebraMap K D) := by
  intro a b hab
  have h0 : algebraMap K D (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have hz : a - b = 0 := by
    by_contra hne
    have h1 : algebraMap K D ((a - b) * (a - b)⁻¹) = 1 := by
      rw [mul_inv_cancel₀ hne, map_one]
    have h2 : algebraMap K D ((a - b) * (a - b)⁻¹) = 0 := by
      rw [map_mul, h0, zero_mul]
    exact one_ne_zero (h1.symm.trans h2)
  exact sub_eq_zero.mp hz

private lemma l937z_gl_charP_of_algebra
    {K D : Type*} [Field K] [CharP K 2] [DivisionRing D] [Algebra K D] : CharP D 2 :=
  charP_of_injective_algebraMap (l937z_gl_algebraMap_injective (K := K) (D := D)) 2

private theorem l937z_gl_pCoreOf_centralizer_eq_bot
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (S : Set (GL (Fin n) K))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s)) :
    pCoreOf 2 (Subgroup.centralizer S) = ⊥ := by
  obtain ⟨r, D, hDfield, hDfin, hDalg, d, hd, hiso⟩ :=
    l937z_gl_centralizer_pi_matrix S hS hodd
  letI : ∀ i, Field (D i) := hDfield
  letI : ∀ i, Finite (D i) := hDfin
  letI : ∀ i, Algebra K (D i) := hDalg
  haveI hchar : ∀ i, CharP (D i) 2 := fun i => l937z_gl_charP_of_algebra (K := K) (D := D i)
  have hGLbot : ∀ i, pCore 2 (GL (Fin (d i)) (D i)) = ⊥ := fun i =>
    pCore_two_GL_eq_bot (E := D i) (m := d i)
  have hPib : pCore 2 (∀ i, GL (Fin (d i)) (D i)) = ⊥ :=
    pCore_trivial_pi hGLbot
  obtain ⟨e1⟩ := l937z_gl_centralizer_units_pi_GL S D d hiso
  obtain ⟨e2⟩ := l937z_gl_centralizer_units_centralizer S
  have hClosure : pCore 2 (Subgroup.centralizer (Subgroup.closure S : Set (GL (Fin n) K))) = ⊥ :=
    pCore_trivial_of_mulEquiv (e2.symm.trans e1).symm hPib
  have hCbot : pCore 2 (Subgroup.centralizer S) = ⊥ :=
    (Subgroup.centralizer_closure S) ▸ hClosure
  simp [pCoreOf, hCbot]

theorem pCoreOf_centralizer_GL_eq_bot {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (x : GL (Fin n) K) (hodd : Odd (orderOf x)) :
    pCoreOf 2 (Subgroup.centralizer ({x} : Set (GL (Fin n) K))) = ⊥ := by
  have hS : ∀ s ∈ ({x} : Set (GL (Fin n) K)), ∀ s' ∈ ({x} : Set (GL (Fin n) K)),
      Commute s s' := by
    rintro s hs s' hs'
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  have hodd' : ∀ s ∈ ({x} : Set (GL (Fin n) K)), Odd (orderOf s) := by
    rintro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    exact hodd
  exact l937z_gl_pCoreOf_centralizer_eq_bot ({x} : Set (GL (Fin n) K)) hS hodd'

end CFSG.StandardType.SporadicShape
