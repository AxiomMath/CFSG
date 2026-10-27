module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartOne.CTP.SpPos
public import CFSG.RankThree.PartOne.CTP.Su4Geom

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem det_eq_of_eigenpair {V : Type*} [AddCommGroup V] [Module K V]
    (hdim : Module.finrank K V = 2) (f : Module.End K V) {a c : V} {α ν : K}
    (hli : LinearIndependent K ![a, c]) (ha : f a = α • a) (hc : f c = ν • c) :
    LinearMap.det f = α * ν := by
  let b : Module.Basis (Fin 2) K V :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim])
  rw [← LinearMap.det_toMatrix b f]
  have hb : ∀ i, f (b i) = ![α, ν] i • b i := by
    intro i
    fin_cases i
    · simpa [b] using ha
    · simpa [b] using hc
  have : LinearMap.toMatrix b b f = Matrix.diagonal ![α, ν] := by
    ext i j
    rw [LinearMap.toMatrix_apply, hb j, map_smul, Module.Basis.repr_self]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  rw [this, Matrix.det_diagonal]
  simp [Fin.prod_univ_two]

@[expose] noncomputable def restrictAct (A : Subgroup (SUid σ 4)) (S : Submodule K (Fin 4 → K))
    (hS : ∀ a ∈ A, ∀ v ∈ S, a • v ∈ S) : A →* Module.End K S where
  toFun a := (actU σ 4 (a : SUid σ 4)).restrict (fun v hv => hS a a.2 v hv)
  map_one' := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    simp
  map_mul' a b := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    simp
    rfl

@[expose] noncomputable def detOn (A : Subgroup (SUid σ 4)) (S : Submodule K (Fin 4 → K))
    (hS : ∀ a ∈ A, ∀ v ∈ S, a • v ∈ S) : A →* K :=
  LinearMap.det.comp (restrictAct A S hS)

theorem detOn_eq_one (A : Subgroup (SUid σ 4)) [Group.IsPerfect A] (S : Submodule K (Fin 4 → K))
    (hS : ∀ a ∈ A, ∀ v ∈ S, a • v ∈ S) (a : A) : detOn A S hS a = 1 :=
  perfect_hom_eq_one (detOn A S hS) a

theorem eigenvalue_mul_eq_one (A : Subgroup (SUid σ 4)) [Group.IsPerfect A]
    (S : Submodule K (Fin 4 → K)) (hdim : Module.finrank K S = 2)
    (hS : ∀ a ∈ A, ∀ v ∈ S, a • v ∈ S) {z : SUid σ 4} (hz : z ∈ A) {a c : Fin 4 → K}
    (ha : a ∈ S) (hc : c ∈ S) {α ν : K} (haz : z • a = α • a) (hcz : z • c = ν • c)
    (hli : LinearIndependent K ![a, c]) : α * ν = 1 := by
  have h1 := detOn_eq_one A S hS ⟨z, hz⟩
  have hli' : LinearIndependent K ![(⟨a, ha⟩ : S), ⟨c, hc⟩] := by
    rw [LinearIndependent.pair_iff] at hli ⊢
    intro s t hst
    apply hli s t
    have := congrArg Subtype.val hst
    simpa using this
  have h2 := det_eq_of_eigenpair hdim (restrictAct A S hS ⟨z, hz⟩) hli'
    (a := ⟨a, ha⟩) (c := ⟨c, hc⟩) (α := α) (ν := ν) (Subtype.ext haz) (Subtype.ext hcz)
  rw [← h2]
  exact h1

end CFSG.RankThree.PartOne.CTP
