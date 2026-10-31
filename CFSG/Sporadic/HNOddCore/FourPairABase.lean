
module

public import CFSG.Sporadic.HNOddCore.ThreeInvolBase
public import CFSG.Sporadic.HNOddCore.QCheck
public import CFSG.Sporadic.HNOddCore.CCheckInputs
public meta import CFSG.Sporadic.HNSchreier.ThreeCheck
public import CFSG.Sporadic.HNOddCore.DCheckInputs
public import CFSG.Sporadic.HNOddCore.NatCheckInputs
public meta import CFSG.Sporadic.HNOddCore.InvData
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public import CFSG.Sporadic.HNOddCore.QCheckInputs
public import CFSG.Sporadic.HNOddCore.SCheckInputs
public import CFSG.Sporadic.HNOddCore.XCheckInputs
public meta import CFSG.Sporadic.HNOddCore.CCheck
public meta import CFSG.Sporadic.HNOddCore.InvArrays
public meta import Certificates.Data.CFSGNative.ONSchreier.Tools
public import CFSG.Sporadic.HNSchreier.ChainCheckInputs
public import CFSG.Sporadic.HNSchreier.LevelInputs
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
public import CFSG.Sporadic.HNSchreier.InvolCheckInputs
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck
public import CFSG.Sporadic.HNSchreier.LocalCheckInputs
public meta import CFSG.Sporadic.HNSchreier.PrimCheck
public meta import CFSG.Sporadic.HNSchreier.LocalData
public meta import CFSG.Sporadic.HNSchreier.MaskCheck
public import CFSG.Sporadic.HNSchreier.OrbitCheckInputs
public import CFSG.Sporadic.HNSchreier.PrimCheckInputs
public meta import Certificates.Data.CFSGNative.Perm.Chain
public import CFSG.Sporadic.HNSchreier.VectorData

@[expose] public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv

theorem prep_cast {m n : ℕ} (h : m = n) {t : Array ℕ} {σ : Perm (Fin m)} (ht : PRep m t σ) :
    PRep n t (Equiv.permCongrHom (finCongr h) σ) := by
  intro x
  have := ht ((finCongr h).symm x)
  simpa [Equiv.permCongrHom, Equiv.permCongr_apply] using this

theorem card_ker_mul_card_map {G M : Type*} [Group G] [Group M] (f : G →* M) {K : Subgroup G}
    (hK : f.ker ≤ K) : Nat.card f.ker * Nat.card (K.map f) = Nat.card K := by
  have h1 := (f.domRestrict K).ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.domRestrict_range, MonoidHom.ker_domRestrict] at h1
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv]
  exact h1

theorem closure_preimage_eq_top {G ι : Type*} [Group G] {C : Subgroup G} {g : ι → G}
    (hg : ∀ i, g i ∈ C) (hC : C = Subgroup.closure (Set.range g)) :
    Subgroup.closure (Set.range fun i => (⟨g i, hg i⟩ : C)) = ⊤ := by
  apply Subgroup.map_injective C.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype, ← Set.range_comp]
  exact hC.symm

theorem range_eq_closure {G M ι : Type*} [Group G] [Group M] (f : G →* M) {g : ι → G}
    (hg : Subgroup.closure (Set.range g) = ⊤) :
    f.range = Subgroup.closure (Set.range fun i => f (g i)) := by
  rw [MonoidHom.range_eq_map, ← hg, MonoidHom.map_closure, ← Set.range_comp]
  rfl

abbrev C4 :
    Subgroup RH := Subgroup.centralizer {jR t4J}

def gC
    (s : ℕ) : RH := if s < 10 then jR (g4 s) else cR

theorem cR_mem_C4 :
    cR ∈ C4 :=
  Subgroup.mem_centralizer_singleton_iff.2 cR_comm_t4.symm

theorem jR_mem_C4
    {g : JH} (hg : g ∈ Subgroup.centralizer {t4J}) : jR g ∈ C4 :=
  (mem_centralizer_t4_iff _).2 (Or.inl ⟨g, hg, rfl⟩)

theorem toPerm_jR
    (g : JH) : MulAction.toPerm (jR g) = permJ g := permR_jR g

abbrev Cv :
    Subgroup C4 := RV.subgroupOf C4

theorem t4R_mem_RV :
    jR t4J ∈ RV := (jR_mem_RV_iff t4J).2 t4J_mem_HJ

theorem card_subgroupOf_centralizer_le {G G' : Type*} [Group G] [Group G'] [Finite G']
    {V : Subgroup G} (e : V ≃* G') {t : G} (ht : t ∈ V) :
    Nat.card (V.subgroupOf (Subgroup.centralizer {t})) ≤
      Nat.card (Subgroup.centralizer {e ⟨t, ht⟩}) := by
  let f : V.subgroupOf (Subgroup.centralizer {t}) → Subgroup.centralizer {e ⟨t, ht⟩} := fun x =>
    ⟨e ⟨(x : Subgroup.centralizer {t}), x.2⟩, by
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact Subgroup.mem_centralizer_singleton_iff.1 (x : Subgroup.centralizer {t}).2⟩
  refine Nat.card_le_card_of_injective f fun a b hab => ?_
  have h1 := congrArg Subtype.val hab
  have h2 := e.injective h1
  exact Subtype.ext (Subtype.ext (congrArg (fun r : V => (r : G)) h2))

theorem card_Cv_le :
    Nat.card Cv ≤ 9216 := by
  have hθ : thetaR ⟨jR t4J, t4R_mem_RV⟩ = sig4 := by
    rw [thetaR_jR t4J_mem_HJ]
    exact thetaJ_t4H
  have h := card_subgroupOf_centralizer_le thetaR t4R_mem_RV
  rw [hθ, card_centralizer_sig4] at h
  exact h

def t4C :
    C4 := ⟨jR t4J, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

theorem t4J_sq :
    t4J * t4J = 1 := by
  have h : (t4H * t4H : HJ) = 1 := by
    apply thetaJ.injective
    apply Subtype.ext
    rw [map_mul, Subgroup.coe_mul, thetaJ_t4H, map_one, Subgroup.coe_one, ← pow_two, sig4_sq]
  have h' := congrArg Subtype.val h
  rw [Subgroup.coe_mul, Subgroup.coe_one] at h'
  exact h'

theorem t4J_ne_one :
    t4J ≠ 1 := by
  intro h
  have e : t4H = 1 := Subtype.ext h
  have := thetaJ_t4H
  rw [e, map_one, Subgroup.coe_one] at this
  exact absurd this.symm (by unfold sig4; decide)

theorem t4C_ne_one :
    t4C ≠ 1 := by
  intro h
  have h' := congrArg Subtype.val h
  rw [Subgroup.coe_one] at h'
  apply t4J_ne_one
  apply jR_injective
  rw [map_one]
  exact h'

theorem orderOf_t4C :
    orderOf t4C = 2 := by
  apply orderOf_eq_prime
  · rw [pow_two]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one]
    show jR t4J * jR t4J = 1
    rw [← map_mul, t4J_sq, map_one]
  · exact t4C_ne_one

end CFSG.Sporadic.HNOddCore
