
module

public import CFSG.Sporadic.FischerOddCore.Fi24R2Order
public import CFSG.Sporadic.FischerOddCore.Fi24R2CheckBase
public import CFSG.Sporadic.FischerOddCore.Fi23T2Card
public import CFSG.Sporadic.FischerOddCore.Fi24Cent
public import CFSG.Sporadic.FischerOddCore.NoCompLemmas
public import CFSG.Sporadic.Fi24.Involutions
public import CFSG.Sporadic.Fi23.InvCover
public import CFSG.Fischer.Polar.Facts
public import Certificates.Data.Kernel.Fi22.CentChecks
public import Certificates.Data.CFSGNative.Fi22.Certificate
public import Certificates.Data.CFSGNative.Fi23.Centralizer
public import Certificates.Data.CFSGNative.Fi23.Certificate
public import Certificates.Data.CFSGNative.Fi23.Classes
public import CFSG.Sporadic.Fi23.InvCertInputs
public import Certificates.Data.Fi24Core
public import Certificates.Data.CFSGNative.Fi24.Certificate
public import Certificates.Data.CFSGNative.Fi23.Data
public import CFSG.Sporadic.Fi24.ExtCertInputs
public import CFSG.Sporadic.Fi24.Simple
public import CFSG.Sporadic.FischerOddCore.Fi22CentCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22CentData
public meta import CFSG.Monster.B.Fischer.Fi22OuterCheck
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.FischerOddCore.Fi22CentOrderCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22Cent
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheck
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtData
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCoverCheckInputs
public meta import Certificates.Data.CFSGNative.FischerOddCore.Checks
public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtCheck
public meta import CFSG.Monster.B.Fischer.Fi22CoverCheck
public meta import CFSG.Monster.B.Fischer.Fi22OrderCheck
public meta import CFSG.Monster.B.Fischer.Fi22GraphCheck
public import CFSG.Sporadic.FischerOddCore.Fi22RelBoundCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22CentCheck
public meta import CFSG.Monster.B.Fischer.Fi22GraphBoundCheck
public import CFSG.Sporadic.FischerOddCore.Fi22SearchCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22RelBoundCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi22CentOrderCheck
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCheck
public import CFSG.Monster.B.Fischer.Fi22OuterCheck
public import CFSG.Sporadic.FischerOddCore.Fi23UniqCheckInputs
public import CFSG.Sporadic.FischerOddCore.Fi23WitCheckInputs
public import CFSG.Sporadic.FischerOddCore.Fi24G2dFacts
public import CFSG.Sporadic.FischerOddCore.Fi24R2KCheckInputs
public import CFSG.Monster.B.Fischer.Fi22GraphCheckInputs
public import CFSG.Monster.B.Fischer.Fi22OuterCheckInputs
public import CFSG.Monster.B.Fischer.PinnedChainInputs
public import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
public import CFSG.Monster.B.Fischer.Fi22CentralizerCheckInputs
public import CFSG.Monster.B.Fischer.Fi22OuterArrays
public import CFSG.Monster.B.Fischer.Fi22OrderCheck
public import CFSG.Monster.B.Fischer.Fi22CoverCheckInputs
public import CFSG.Monster.B.Fischer.Fi22FaithfulCheckInputs
public import CFSG.Monster.B.Fischer.Fi22GraphBoundCheckInputs
public import Certificates.Data.CFSGNative.FischerOddCore.Checks
public import CFSG.Monster.B.Fischer.Fi22GraphCheck
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.SolvableCoreComponents
public import CFSG.Sporadic.FischerOddCore.Fi24R2CheckInputs

@[expose] public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG CFSG.LocalCores
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.Fi24.Native
open CFSG.Sporadic.Fi24 (R J M MR tR D24 jR)

attribute [local instance] CFSG.Sporadic.Fi24.rAction

section Generic

theorem not_isComponent_of_selfCentralizing {L : Type*} [Group L] [Finite L] {Q : Subgroup L}
    (hQn : Q.Normal) (hQ2 : IsPGroup 2 Q) (hQc : Subgroup.centralizer (Q : Set L) ≤ Q)
    (B : Subgroup L) : ¬ IsComponent B :=
  not_isComponent_of_surj_selfCentralizing (MonoidHom.id L) Function.surjective_id
    (fun x hx => by rw [show x = 1 from hx, one_mul]) hQn hQ2 hQc B

theorem exists_selfCentralizing_card_of_mulEquiv {L M : Type*} [Group L] [Group M] (e : L ≃* M)
    {Q : Subgroup M} (hQn : Q.Normal) (hQc : Subgroup.centralizer (Q : Set M) ≤ Q) :
    ∃ Q' : Subgroup L, Q'.Normal ∧ Nat.card Q' = Nat.card Q ∧
      Subgroup.centralizer (Q' : Set L) ≤ Q' := by
  refine ⟨Q.comap e.toMonoidHom, hQn.comap _, Nat.card_congr
    { toFun := fun x => ⟨e x, x.2⟩
      invFun := fun y => ⟨e.symm y, by
        show e (e.symm y) ∈ Q
        rw [MulEquiv.apply_symm_apply]
        exact y.2⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y) }, ?_⟩
  intro y hy
  show e y ∈ Q
  apply hQc
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  have := Subgroup.mem_centralizer_iff.1 hy (e.symm m)
    (by show e (e.symm m) ∈ Q; rwa [MulEquiv.apply_symm_apply])
  have h := congrArg e this
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h

theorem comap_selfCentralizing {L M : Type*} [Group L] [Group M] (ρ : L →* M)
    (hρ : Function.Surjective ρ) {N : Subgroup M}
    (hNc : Subgroup.centralizer (N : Set M) ≤ N) :
    Subgroup.centralizer ((N.comap ρ : Subgroup L) : Set L) ≤ N.comap ρ := by
  intro y hy
  show ρ y ∈ N
  apply hNc
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  obtain ⟨x, rfl⟩ := hρ m
  have := Subgroup.mem_centralizer_iff.1 hy x hm
  rw [← map_mul, ← map_mul, this]

theorem rep_brayElt {G : Type*} [Group G] [MulAction G (Fin 306936)] {T Gt Gi : Table} {r g : G}
    (hT : Rep 306936 T r) (hG : Rep 306936 Gt g) (hGi : Rep 306936 Gi g⁻¹) (e : ℕ) :
    Rep 306936 (fi24BrayT T Gt Gi e true) (brayElt r g e) := by
  have hBB := Rep.powT (n := 306936) (by norm_num)
    (Rep.compT hT (Rep.compT hGi (Rep.compT hT hG))) e
  simp only [fi24BrayT, ↓reduceIte]
  exact Rep.compT hG hBB

theorem card_fix_eq_fi24Fix {G : Type*} [Group G] [MulAction G (Fin 306936)] {T : Table} {g : G}
    (hT : Rep 306936 T g) : Nat.card {k : Fin 306936 // g • k = k} = fi24Fix T := by
  classical
  have e1 : {k : Fin 306936 // g • k = k} ≃ {k : Fin 306936 // ap T k.val = k.val} :=
    Equiv.subtypeEquivRight fun k => by
      rw [hT k.val k.isLt, idx_of_lt g k.isLt]
      exact ⟨fun h => by rw [h], fun h => Fin.ext h⟩
  have e2 : {k : Fin 306936 // ap T k.val = k.val} ≃
      ((Finset.range 306936).filter fun i => ap T i = i) :=
    { toFun := fun k => ⟨k.1.1, Finset.mem_filter.2 ⟨Finset.mem_range.2 k.1.2, k.2⟩⟩
      invFun := fun i => ⟨⟨i.1, Finset.mem_range.1 (Finset.mem_filter.1 i.2).1⟩,
        (Finset.mem_filter.1 i.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr (e1.trans e2), Nat.card_eq_finsetCard, ← Nat.count_eq_card_filter_range]
  unfold Nat.count fi24Fix
  exact List.countP_congr fun i _ => by simp

theorem card_fix_conj {G : Type*} [Group G] [MulAction G (Fin 306936)] (c g : G) :
    Nat.card {k : Fin 306936 // (c * g * c⁻¹) • k = k} = Nat.card {k : Fin 306936 // g • k = k} :=
  Nat.card_congr
    { toFun := fun k => ⟨c⁻¹ • k.1, by
        have h := k.2
        rw [mul_smul, mul_smul] at h
        exact eq_inv_smul_iff.2 h⟩
      invFun := fun k => ⟨c • k.1, by rw [mul_smul, mul_smul, inv_smul_smul, k.2]⟩
      left_inv := fun k => Subtype.ext (smul_inv_smul c k.1)
      right_inv := fun k => Subtype.ext (inv_smul_smul c k.1) }

end Generic

theorem fi24R2_mem_M :
    fi24R2 ∈ M := (Fi24.fi23EquivM.symm fi23U3).2

theorem fi23EquivM_fi24R2 :
    Fi24.fi23EquivM ⟨fi24R2, fi24R2_mem_M⟩ = fi23U3 :=
  MulEquiv.apply_symm_apply _ _

theorem fi24R2_ne_one :
    fi24R2 ≠ 1 := fun h => by
  have h1 : Fi24.fi23EquivM.symm fi23U3 = 1 := Subtype.ext h
  rw [MulEquiv.map_eq_one_iff] at h1
  exact fi23U3_facts.2 h1

theorem smul_val_of_rep {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)] {T : Table} {g : G}
    (hT : Rep n T g) (k : Fin n) : (g • k).val = ap T k.val := by
  rw [hT k.val k.isLt, idx_of_lt g k.isLt]

theorem rep_of_rep_jR
    {T : Table} {g : J} (h : Rep 306936 T (jR g)) : Rep 306936 T g := by
  intro i hi
  rw [h i hi, Fi24.idx_jR]

theorem rep_fi24R2 :
    Rep 306936 fi24U3T fi24R2 := rep_of_rep_jR rep_fi24U3T

theorem fi24J_rep_unique
    {T : Table} {g h : J} (hg : Rep 306936 T g) (hh : Rep 306936 T h) :
    g = h :=
  Fi24.jR_injective (fi24_rep_unique (Fi24.rep_jR hg) (Fi24.rep_jR hh))

abbrev fi24GaT : Table := wordT nPts (letterJ fi24L) fi24BrayWordA

abbrev fi24GbT : Table := wordT nPts (letterJ fi24L) fi24BrayWordB

abbrev fi24CaT : Table := fi24BrayT fi24U3T fi24GaT (invT nPts fi24GaT) fi24BrayExpA true

abbrev fi24CbT : Table := fi24BrayT fi24U3T fi24GbT (invT nPts fi24GbT) fi24BrayExpB true

abbrev fi24C :
    Subgroup J := Subgroup.centralizer ({fi24R2} : Set J)

theorem fi24R2_mem_C :

    fi24R2 ∈ fi24C := (Subgroup.mem_centralizer_singleton_iff (G := J)).2 rfl

theorem fi24C_smul_fixed
    (c : fi24C) (k : Fin 306936) (hk : fi24R2 • k = k) :
    fi24R2 • ((c : J) • k) = (c : J) • k := by
  have hc : (c : J) * fi24R2 = fi24R2 * (c : J) :=
    (Subgroup.mem_centralizer_singleton_iff (G := J)).1 c.2
  rw [smul_smul, ← hc, mul_smul, hk]

theorem fi24BrayWordA_letters : ∀ z ∈ fi24BrayWordA, z.natAbs ≤ 13 := by decide

theorem fi24BrayWordB_letters : ∀ z ∈ fi24BrayWordB, z.natAbs ≤ 13 := by decide

theorem rep_fi24Ca :
    Rep 306936 fi24CaT fi24Ca := by
  have hG := Rep.wordT (n := 306936) (G := J) (by norm_num) fi24BrayWordA
    fun z hz => Fi24.rep_letterJ (fi24BrayWordA_letters z hz)
  exact rep_brayElt rep_fi24R2 hG (rep_invT24 hG) _

theorem rep_fi24Cb :
    Rep 306936 fi24CbT fi24Cb := by
  have hG := Rep.wordT (n := 306936) (G := J) (by norm_num) fi24BrayWordB
    fun z hz => Fi24.rep_letterJ (fi24BrayWordB_letters z hz)
  exact rep_brayElt rep_fi24R2 hG (rep_invT24 hG) _

end CFSG.Sporadic.FischerOddCore
