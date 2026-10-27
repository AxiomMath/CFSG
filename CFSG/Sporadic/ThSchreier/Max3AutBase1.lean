
module

public import CFSG.Sporadic.ThSchreier.Max3AutBase

public import CFSG.Sporadic.ThSchreier.AutCoreBase
public import CFSG.Sporadic.ThSchreier.Max3ActionBase1
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.Th.Max3.CoreBase1
public import CFSG.Sporadic.Th.Max3.AltNine
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Sporadic.Th.Max3.QuotientInputs
public import CFSG.Sporadic.Th.Max3.Data
public import CFSG.Sporadic.ThSchreier.RigidityInputs
public meta import CFSG.Sporadic.ThSchreier.Enc8
public import CFSG.Sporadic.Th.Max3.PacketBase1
public import CFSG.Sporadic.ThSchreier.PerfectBase1
public import CFSG.Sporadic.ThSchreier.Rigidity

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Certificates
open scoped commutatorElement

@[expose] noncomputable def zM : ↥M := ⟨z, z_mem_M⟩

theorem closure_xM_yM :
    Subgroup.closure ({xM, yM} : Set ↥M) = ⊤ := by
  have h := Subgroup.closure_closure_coe_preimage (k := ({x, y} : Set J))
  have e : (((↑) : ↥M → J) ⁻¹' ({x, y} : Set J)) = ({xM, yM} : Set ↥M) := by
    ext m
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
  rw [← e]
  exact h

noncomputable abbrev eQ :
    Q.subgroupOf M ≃* Q := Subgroup.subgroupOfEquivOfLe Q_le_M

theorem eQ_coe
    (g : Q.subgroupOf M) : ((eQ g : Q) : J) = ((g : ↥M) : J) :=
  Subgroup.subgroupOfEquivOfLe_apply_coe Q_le_M g

theorem mem_center_QM_iff (g : Q.subgroupOf M) :
    g ∈ Subgroup.center (Q.subgroupOf M) ↔ eQ g ∈ Subgroup.center Q := by
  simp only [Subgroup.mem_center_iff]
  constructor
  · intro h k
    have := congrArg eQ (h (eQ.symm k))
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
  · intro h k
    apply eQ.injective
    rw [map_mul, map_mul]
    exact h (eQ k)

theorem mem_zpowers_zM
    (m : ↥M) : m ∈ Subgroup.zpowers zM ↔ (m : J) ∈ Subgroup.zpowers z := by
  simp only [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by rw [Subgroup.coe_zpow]; rfl⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩

theorem Q_gen_M : Q.subgroupOf M =
    Subgroup.closure (insert zM (Set.range fun j : Fin 8 => nfM (Pi.single j 1))) := by
  apply Subgroup.map_injective (f := M.subtype) Subtype.val_injective
  rw [Subgroup.map_subgroupOf_eq_of_le Q_le_M, MonoidHom.map_closure, Set.image_insert_eq,
    ← Set.range_comp]
  have h1 : (M.subtype ∘ fun j : Fin 8 => nfM (Pi.single j 1)) = q := by
    funext j
    rw [Function.comp_apply, Subgroup.coe_subtype]
    exact ExtraspecialNF.nf_single z q j
  have h2 : M.subtype zM = z := by
    rw [Subgroup.coe_subtype]
    rfl
  rw [h1, h2]
  rfl

end CFSG.Sporadic.ThSchreier
