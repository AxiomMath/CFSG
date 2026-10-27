module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2CoreKAux
import CFSG.GroupTheory.CoprimeActionSupport.PrimeCyclicNormalizerIrreducibleRestriction

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.GroupTheory.CoprimeActionSupport.PrimeCyclicNormalizerIrreducibleRestriction

variable {k : Type} [Field k] {G : Type} [Group G] {Q : Type} [AddCommGroup Q] [Module k Q]

private noncomputable def w183b2AsSubmodule {N : Type} [Group N] {ρ : Representation k N Q}
    {U : Submodule k ρ.asModule} (hU : ∀ n, ∀ v ∈ U, ρ n v ∈ U) :
    Submodule (MonoidAlgebra k N) ρ.asModule where
  carrier := U
  zero_mem' := U.zero_mem
  add_mem' := fun ha hb => U.add_mem ha hb
  smul_mem' := fun r x hx => by
    have h : r • x = ρ.asAlgebraHom r x :=
      Representation.asModuleEquiv_map_smul ρ r x
    rw [h]
    exact Representation.asAlgebraHom_mem_of_forall_mem ρ U hU x hx r

private lemma w183b2AsSubmodule_eq_bot_iff {N : Type} [Group N] {ρ : Representation k N Q}
    {U : Submodule k ρ.asModule} (hU : ∀ n, ∀ v ∈ U, ρ n v ∈ U) :
    w183b2AsSubmodule (ρ := ρ) hU = ⊥ ↔ U = ⊥ := by
  rw [Submodule.eq_bot_iff, Submodule.eq_bot_iff]
  exact ⟨fun h x hx => h x hx, fun h x hx => h x hx⟩

private lemma w183b2_isSimpleModule {N : Type} [Group N] {ρ : Representation k N Q}
    {U : Submodule k ρ.asModule} (hU : ∀ n, ∀ v ∈ U, ρ n v ∈ U) (hbot : U ≠ ⊥)
    (hmax : ∀ V : Submodule k ρ.asModule, (∀ n, ∀ v ∈ V, ρ n v ∈ V) → V ≤ U →
      V = ⊥ ∨ V = U) :
    IsSimpleModule (MonoidAlgebra k N) (w183b2AsSubmodule (ρ := ρ) hU) := by
  rw [isSimpleModule_iff_isAtom]
  refine ⟨?_, fun b hb => ?_⟩
  · rw [ne_eq, w183b2AsSubmodule_eq_bot_iff]
    exact hbot
  · have hbU : (b.restrictScalars k : Submodule k ρ.asModule) ≤ U := fun x hx => hb.1 hx
    have hinv : ∀ n, ∀ v ∈ (b.restrictScalars k : Submodule k ρ.asModule), ρ n v ∈ b := by
      intro n v hv
      have hsmul : (MonoidAlgebra.of k N n) • v = ρ n v := by
        change ρ.asAlgebraHom (MonoidAlgebra.of k N n) v = ρ n v
        rw [Representation.asAlgebraHom_of]
      have : (MonoidAlgebra.of k N n) • v ∈ b := b.smul_mem _ hv
      rwa [hsmul] at this
    rcases hmax (b.restrictScalars k) hinv hbU with hbot | htop
    · rw [Submodule.eq_bot_iff]
      intro x hx
      have hx' : x ∈ (b.restrictScalars k : Submodule k ρ.asModule) := hx
      rw [hbot] at hx'
      simpa using hx'
    · exfalso
      apply hb.2
      intro x hx
      have hx' : x ∈ (b.restrictScalars k : Submodule k ρ.asModule) := by rw [htop]; exact hx
      exact hx'

private lemma w183b2NIso_of_linearEquiv {N : Type} [Group N] {ρ : Representation k N Q}
    {U V : Submodule k ρ.asModule} (hU : ∀ n, ∀ v ∈ U, ρ n v ∈ U)
    (hV : ∀ n, ∀ v ∈ V, ρ n v ∈ V)
    (e : w183b2AsSubmodule (ρ := ρ) hU ≃ₗ[MonoidAlgebra k N]
      w183b2AsSubmodule (ρ := ρ) hV) :
    ∃ f : U →ₗ[k] Q, Function.Injective f ∧ LinearMap.range f = V ∧
      (∀ n, ∀ u v' : U, MonoidAlgebra.of k N n • (u : ρ.asModule) = (v' : ρ.asModule) →
        f v' = ρ n (f u)) := by
  let f : U →ₗ[k] Q :=
    { toFun := fun u => ρ.asModuleEquiv (e ⟨u, u.property⟩ : ρ.asModule)
      map_add' := fun u v => by
        have h : (⟨(u + v : U), (u + v).property⟩ : w183b2AsSubmodule (ρ := ρ) hU)
            = ⟨u, u.property⟩ + ⟨v, v.property⟩ := rfl
        rw [h, map_add]
        exact map_add ρ.asModuleEquiv _ _
      map_smul' := fun c u => by
        let w : U := c • u
        have hw : (w : ρ.asModule) = c • (u : ρ.asModule) := rfl
        have h : (⟨w, w.property⟩ : w183b2AsSubmodule (ρ := ρ) hU)
            = algebraMap k (MonoidAlgebra k N) c • ⟨u, u.property⟩ := by
          ext
          show (w : ρ.asModule) = algebraMap k (MonoidAlgebra k N) c • (u : ρ.asModule)
          rw [IsScalarTower.algebraMap_smul]
          exact hw
        rw [h, map_smul]
        show ρ.asModuleEquiv (algebraMap k (MonoidAlgebra k N) c •
            (e ⟨u, u.property⟩ : ρ.asModule)) =
          c • ρ.asModuleEquiv (e ⟨u, u.property⟩ : ρ.asModule)
        rw [IsScalarTower.algebraMap_smul]
        exact map_smul ρ.asModuleEquiv c _ }
  refine ⟨f, ?_, ?_, ?_⟩
  · intro u v huv
    have h1 : (e ⟨u, u.property⟩ : ρ.asModule) = (e ⟨v, v.property⟩ : ρ.asModule) :=
      ρ.asModuleEquiv.injective huv
    have h2 : (⟨u, u.property⟩ : w183b2AsSubmodule (ρ := ρ) hU) = ⟨v, v.property⟩ :=
      e.injective (Subtype.ext h1)
    exact Subtype.ext (Subtype.ext_iff.mp h2)
  · ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact (e ⟨u, u.property⟩).property
    · intro hx
      obtain ⟨y, hy⟩ := e.surjective ⟨x, hx⟩
      refine ⟨y, ?_⟩
      have hy' : e y = ⟨x, hx⟩ := hy
      show ρ.asModuleEquiv (e y : ρ.asModule) = x
      rw [hy']
      rfl
  · intro n u v huv
    have hsmul : (⟨v, v.property⟩ : w183b2AsSubmodule (ρ := ρ) hU)
        = MonoidAlgebra.of k N n • (⟨u, u.property⟩ :
            w183b2AsSubmodule (ρ := ρ) hU) := by
      ext
      rw [← huv]
      rfl
    change ρ.asModuleEquiv (e ⟨v, v.property⟩ : ρ.asModule) = ρ n (f u)
    rw [hsmul, map_smul]
    show ρ.asModuleEquiv (MonoidAlgebra.of k N n • (e ⟨u, u.property⟩ : ρ.asModule)) =
      ρ n (f u)
    rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]
    rfl

theorem w183b2_simple_indep (ρ : Representation k G Q) (N : Subgroup G) {ι : Type} [Fintype ι]
    (S : ι → Submodule k Q) (hS : ∀ i, w183b2SimpleSub ρ N (S i))
    (hne : ∀ i j, i ≠ j → ¬ w183b2NIso ρ N (S i) (S j)) (x : ι → Q) (hx : ∀ i, x i ∈ S i)
    (hsum : ∑ i, x i = 0) : ∀ i, x i = 0 := by
  classical
  have hInv : ∀ i, ∀ n : N, ∀ v ∈ S i, (ρ.comp N.subtype) n v ∈ S i :=
    fun i n v hv => (hS i).2.1 n n.property v hv
  have hsimple : ∀ i, IsSimpleModule (MonoidAlgebra k N)
      (w183b2AsSubmodule (ρ := ρ.comp N.subtype) (hInv i)) :=
    fun i => w183b2_isSimpleModule (hInv i) (hS i).1
      (fun V hV hVU => (hS i).2.2 V (fun n hn v hv => hV ⟨n, hn⟩ v hv) hVU)
  let U : ι → Submodule (MonoidAlgebra k N) (Representation.asModule (ρ.comp N.subtype)) :=
    fun i => w183b2AsSubmodule (ρ := ρ.comp N.subtype) (hInv i)
  have hnoniso : ∀ i j, i ≠ j → IsEmpty (U i ≃ₗ[MonoidAlgebra k N] U j) := by
    intro i j hij
    refine ⟨fun e => ?_⟩
    apply hne i j hij
    obtain ⟨f, hinj, hrange, hnlin⟩ := w183b2NIso_of_linearEquiv (ρ := ρ.comp N.subtype)
      (hInv i) (hInv j) e
    refine ⟨f, hinj, hrange, fun n hn u v hv => ?_⟩
    have hv' : MonoidAlgebra.of k N ⟨n, hn⟩ •
          (Representation.asModuleEquiv (ρ.comp N.subtype)).symm (u : Q) =
        (Representation.asModuleEquiv (ρ.comp N.subtype)).symm (v : Q) := by
      apply (Representation.asModuleEquiv (ρ.comp N.subtype)).injective
      rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of,
        LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      exact hv
    exact hnlin ⟨n, hn⟩ u v hv'
  have hSU : iSupIndep U := iSupIndep_of_noniso hsimple hnoniso
  intro i
  exact (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero U).mp hSU Finset.univ x
    (fun i _ => hx i) hsum i (Finset.mem_univ i)

end CFSG.LocalAnalysis.WeakClosure81

end
