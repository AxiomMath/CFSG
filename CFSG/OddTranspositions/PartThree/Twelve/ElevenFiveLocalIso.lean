module

public import CFSG.Fischer.Uniq.Graph
public import CFSG.Timmesfeld.Bridge.Asc72Basic
public import CFSG.Timmesfeld.Bridge.OddLocalDefs
public import CFSG.Timmesfeld.Bridge.OddLocalBlock
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.Bridge.Asc72Triangle
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Fischer

variable {G G' : Type} [Group G] [Group G']

structure LocalIso (D : Set G) (u : G) (D' : Set G') (u' : G') where
  toMulEquiv : Subgroup.closure (commSet D u) ≃* Subgroup.closure (commSet D' u')
  mem_iff : ∀ y : Subgroup.closure (commSet D u),
    (y : G) ∈ commSet D u ↔ (toMulEquiv y : G') ∈ commSet D' u'

open scoped Classical in
@[expose] noncomputable def LocalIso.app {D : Set G} {u : G} {D' : Set G'} {u' : G'}
    (θ : LocalIso D u D' u') (x : G) : G' :=
  if h : x ∈ Subgroup.closure (commSet D u) then (θ.toMulEquiv ⟨x, h⟩ : G') else 1

@[expose] def patchSlice (D : Set G) (u v : G) : Set G :=
  {s | s ∈ commSet D v ∧ ¬ Commute s u}

theorem mem_commSet_symm {D : Set G} {u v : G} (hu : u ∈ D) (hv : v ∈ commSet D u) :
    u ∈ commSet D v :=
  ⟨hu, hv.2.1.symm, hv.2.2.symm⟩

namespace LocalIso

variable {D : Set G} {u : G} {D' : Set G'} {u' : G'} (θ : LocalIso D u D' u')

theorem app_of_mem {y : G} (hy : y ∈ Subgroup.closure (commSet D u)) :
    θ.app y = (θ.toMulEquiv ⟨y, hy⟩ : G') := by
  unfold LocalIso.app
  rw [dif_pos hy]

theorem app_mem {y : G} (hy : y ∈ Subgroup.closure (commSet D u)) :
    θ.app y ∈ Subgroup.closure (commSet D' u') := by
  rw [app_of_mem θ hy]
  exact (θ.toMulEquiv ⟨y, hy⟩).2

theorem app_mul {x y : G} (hx : x ∈ Subgroup.closure (commSet D u))
    (hy : y ∈ Subgroup.closure (commSet D u)) : θ.app (x * y) = θ.app x * θ.app y := by
  rw [app_of_mem θ hx, app_of_mem θ hy, app_of_mem θ (Subgroup.mul_mem _ hx hy)]
  exact congrArg Subtype.val (θ.toMulEquiv.map_mul ⟨x, hx⟩ ⟨y, hy⟩)

theorem app_inv {x : G} (hx : x ∈ Subgroup.closure (commSet D u)) :
    θ.app x⁻¹ = (θ.app x)⁻¹ := by
  rw [app_of_mem θ hx, app_of_mem θ (Subgroup.inv_mem _ hx)]
  exact congrArg Subtype.val (θ.toMulEquiv.map_inv ⟨x, hx⟩)

theorem app_one : θ.app 1 = 1 := by
  rw [app_of_mem θ (Subgroup.one_mem _)]
  exact congrArg Subtype.val (θ.toMulEquiv.map_one)

theorem app_injOn {x y : G} (hx : x ∈ Subgroup.closure (commSet D u))
    (hy : y ∈ Subgroup.closure (commSet D u)) (h : θ.app x = θ.app y) : x = y := by
  rw [app_of_mem θ hx, app_of_mem θ hy] at h
  exact congrArg Subtype.val (θ.toMulEquiv.injective (Subtype.ext h))

theorem app_mem_commSet {y : G} (hy : y ∈ commSet D u) : θ.app y ∈ commSet D' u' := by
  have hy' : y ∈ Subgroup.closure (commSet D u) := Subgroup.subset_closure hy
  rw [app_of_mem θ hy']
  exact (θ.mem_iff ⟨y, hy'⟩).1 hy

theorem exists_app_eq {z : G'} (hz : z ∈ commSet D' u') :
    ∃ y ∈ commSet D u, θ.app y = z := by
  have hz' : z ∈ Subgroup.closure (commSet D' u') := Subgroup.subset_closure hz
  refine ⟨((θ.toMulEquiv.symm ⟨z, hz'⟩ : Subgroup.closure (commSet D u)) : G), ?_, ?_⟩
  · rw [θ.mem_iff, MulEquiv.apply_symm_apply]
    exact hz
  · rw [app_of_mem θ (θ.toMulEquiv.symm ⟨z, hz'⟩).2]
    simp

theorem commute_iff {x y : G} (hx : x ∈ Subgroup.closure (commSet D u))
    (hy : y ∈ Subgroup.closure (commSet D u)) :
    Commute (θ.app x) (θ.app y) ↔ Commute x y := by
  have hxy := Subgroup.mul_mem _ hx hy
  have hyx := Subgroup.mul_mem _ hy hx
  constructor
  · intro h
    have h1 : θ.app (x * y) = θ.app (y * x) := by
      rw [app_mul θ hx hy, app_mul θ hy hx]
      exact h.eq
    exact app_injOn θ hxy hyx h1
  · intro h
    have h1 : θ.app x * θ.app y = θ.app y * θ.app x := by
      rw [← app_mul θ hx hy, ← app_mul θ hy hx, h.eq]
    exact h1

end LocalIso

end CFSG.OddTranspositions.PartThree

end
