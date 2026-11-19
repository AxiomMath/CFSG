module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.GroupTheory.Subgroup.Center

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups LinearAlgebra.Projectivization Pointwise

private theorem pgl_mk_action_eq_of_projective_fixed (K : Type*) [Field K] [Finite K]
    (A : Matrix.GeneralLinearGroup (Fin 2) K)
    (h : ∀ x : ℙ K (Fin 2 → K), (Matrix.ProjGenLinGroup.mk A : PGL(2, K)) • x = x) :
    ∀ x : ℙ K (Fin 2 → K), A • x = x := by
  intro x
  have hx := h x
  change A • x = x at hx
  exact hx

private theorem gl_center_of_projective_fixed (K : Type*) [Field K] [Finite K]
    (A : Matrix.GeneralLinearGroup (Fin 2) K)
    (h : ∀ x : ℙ K (Fin 2 → K), A • x = x) :
    A ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) K) := by
  let f : (Fin 2 → K) →ₗ[K] (Fin 2 → K) := Matrix.toLin' A.1
  have hAf : ∀ v : Fin 2 → K, A • v = f v := by intro v; rfl
  have hcol : ∀ v : Fin 2 → K, v ≠ 0 → ∃ a : K, f v = a • v := by
    intro v hv
    have hvproj := h (Projectivization.mk K v hv)
    rw [Projectivization.smul_mk] at hvproj
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp hvproj
    exact ⟨a, by rw [← hAf v]; exact ha.symm⟩
  have hne0 : (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) ≠ 0 := by
    intro hh; have := congrFun hh 0; simp at this
  have hne1 : (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) ≠ 0 := by
    intro hh; have := congrFun hh 1; simp at this
  have hne01 :
      (Pi.single (0 : Fin 2) (1 : K) + Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) ≠ 0 := by
    intro hh; have := congrFun hh 1; simp at this
  obtain ⟨a, ha⟩ := hcol (Pi.single (0 : Fin 2) (1 : K)) hne0
  obtain ⟨b, hb⟩ := hcol (Pi.single (1 : Fin 2) (1 : K)) hne1
  obtain ⟨c, hc⟩ :=
    hcol (Pi.single (0 : Fin 2) (1 : K) + Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) hne01
  have hsum :
      a • (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) +
          b • (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) =
        c • (Pi.single (0 : Fin 2) (1 : K) + Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) := by
    rw [← ha, ← hb, ← hc, map_add]
  have hab : a = b := by
    have h0 : a = c := by simpa using congrFun hsum 0
    have h1 : b = c := by simpa using congrFun hsum 1
    rw [h0, h1]
  have ha' : f = a • 1 := by
    apply (Pi.basisFun K (Fin 2)).ext
    intro i
    fin_cases i
    · simpa [Pi.basisFun_apply] using ha
    · simpa [Pi.basisFun_apply, ← hab] using hb
  have hscalar : A.1 = Matrix.scalar (Fin 2) a := by
    calc
      A.1 = LinearMap.toMatrix' f := by
        change A.1 = LinearMap.toMatrix' (Matrix.toLin' A.1)
        rw [LinearMap.toMatrix'_toLin']
      _ = (algebraMap K (Module.End K (Fin 2 → K)) a).toMatrix' :=
        congrArg LinearMap.toMatrix' ha'
      _ = Matrix.scalar (Fin 2) a := LinearMap.toMatrix'_algebraMap a
  rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  exact ⟨a, hscalar.symm⟩

private theorem pgl_action_trivial_eq_one (K : Type*) [Field K] [Finite K] :
    ∀ g : PGL2 K, (∀ x : ℙ K (Fin 2 → K), g • x = x) → g = 1 := by
  intro g hg
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | mk A =>
      rw [Matrix.ProjGenLinGroup.mk_eq_one]
      apply gl_center_of_projective_fixed K A
      intro x
      exact (pgl_mk_action_eq_of_projective_fixed K A hg) x

private theorem pgl_two_pretransitive (K : Type*) [Field K] [Finite K] :
    MulAction.IsMultiplyPretransitive (PGL2 K)
      (ℙ K (Fin 2 → K)) 2 := by
  let q : LinearMap.GeneralLinearGroup K (Fin 2 → K) →* PGL2 K :=
    Matrix.ProjGenLinGroup.mk.comp Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom
  let f : (ℙ K (Fin 2 → K)) →ₑ[q] (ℙ K (Fin 2 → K)) := {
    toFun := id
    map_smul' := by
      intro g x
      change g • x = (q g) • x
      change g • x = Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.toLin.symm g) • x
      rw [Matrix.ProjGenLinGroup.mk_smul]
      induction x using Projectivization.ind with
      | h v hv =>
          simp only [Projectivization.smul_mk]
          have hvact :
              g • v = (Matrix.GeneralLinearGroup.toLin.symm g) • v := by
            change (g : (Fin 2 → K) →ₗ[K] (Fin 2 → K)) v = _
            calc
              (g : (Fin 2 → K) →ₗ[K] (Fin 2 → K)) v =
                  (Matrix.GeneralLinearGroup.toLin
                    (Matrix.GeneralLinearGroup.toLin.symm g) :
                      (Fin 2 → K) →ₗ[K] (Fin 2 → K)) v := by
                rw [Matrix.GeneralLinearGroup.toLin.apply_symm_apply]
              _ = (Matrix.GeneralLinearGroup.toLin.symm g) • v := by
                rw [Matrix.GeneralLinearGroup.toLin_apply]
                rfl
          simp only [hvact] }
  exact @MulAction.IsPretransitive.of_embedding _ _ _ _ _ _ _ _ q f (Fin 2)
    Function.surjective_id inferInstance

public theorem center_eq_bot_of_two_pretransitive
    {G X : Type*} [Group G] [MulAction G X] [FaithfulSMul G X]
    (h2 : MulAction.IsMultiplyPretransitive G X 2)
    (hcard : 3 ≤ Nat.card X) :
    Subgroup.center G = ⊥ := by
  apply le_bot_iff.mp
  intro z hz
  apply Subgroup.mem_bot.mpr
  apply (@FaithfulSMul.eq_of_smul_eq_smul G X _
    (inferInstance : FaithfulSMul G X) z (1 : G))
  intro x
  by_contra hzx
  have hpair : ({x, z • x} : Set X).ncard = 2 :=
    Set.ncard_pair (show x ≠ z • x by
      intro h
      apply hzx
      simpa using h.symm)
  have hlt : ({x, z • x} : Set X).ncard < (Set.univ : Set X).ncard := by
    rw [hpair, Set.ncard_univ]
    omega
  obtain ⟨y, hy⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
  have hyx : y ≠ x := by
    intro h
    exact hy.2 (by simp [h])
  obtain ⟨g, hgx, hgy⟩ :=
    (MulAction.is_two_pretransitive_iff.mp h2) hzx hyx
  have hfix : g • (z • x) = z • x := by
    calc
      g • (z • x) = (g * z) • x := by rw [smul_smul]
      _ = (z * g) • x := by rw [Subgroup.mem_center_iff.mp hz g]
      _ = z • (g • x) := by rw [smul_smul]
      _ = z • x := by simpa using congrArg (fun q : X => z • q) hgy
  exact hy.2 (by simp [hgx.symm.trans hfix])

/-- The center of `PGL₂(K)` is trivial for every finite field `K`. -/
public theorem pgl2_center_eq_bot (K : Type*) [Field K] [Finite K] :
    Subgroup.center (PGL2 K) = ⊥ := by
  let : MulAction (PGL2 K) (ℙ K (Fin 2 → K)) := inferInstance
  let : FaithfulSMul (PGL2 K) (ℙ K (Fin 2 → K)) :=
    faithfulSMul_iff.2 (pgl_action_trivial_eq_one K)
  have hcard : 3 ≤ Nat.card (ℙ K (Fin 2 → K)) := by
    have hfinrank : Module.finrank K (Fin 2 → K) = 2 := by simp
    rw [Projectivization.card_of_finrank_two K (Fin 2 → K) hfinrank]
    have hK : 2 ≤ Nat.card K := by
      have h := (Finite.one_lt_card : 1 < Nat.card K)
      omega
    omega
  exact center_eq_bot_of_two_pretransitive (pgl_two_pretransitive K) hcard

end CFSG.GorensteinWalter
