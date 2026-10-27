
module

public import CFSG.Monster.B.TwoA.Sp8.GenActionOrbitBase

public import CFSG.Monster.B.TwoA.Sp8.GenActionHom
public import CFSG.Monster.B.TwoA.Census.NatCert
public import CFSG.Monster.B.TwoA.Co2Inv.ConjCert
public meta import CFSG.Monster.B.TwoA.Sp8.GenActionHom
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.TwoA.Co2Inv.ConjCert
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Sp8.GenActionOrbitInputs
public import Certificates.Certificate3076
public import CFSG.Monster.B.TwoA.Sp8.LiftsInputs
public import CFSG.Monster.B.TwoA.Sp8.A8Inputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionLiftsInputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionDiffInputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionConjInputs
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.Rep4371.SmallFaithful
public import CFSG.Monster.B.Gen.Max2Assembly
public import CFSG.Monster.B.Gen.PacketGeneration
public import CFSG.Monster.B.Gen.EbarPairing
public import CFSG.Monster.B.Cbar.SimpleAux
public import CFSG.Monster.B.Rep4371.FaithfulImageInputs
public import CFSG.Monster.B.TwoA.Base.WCls
public import CFSG.Monster.B.TwoA.Census.PermBFS
public import CFSG.Monster.B.TwoA.Co2Inv.Data
public import CFSG.Monster.B.TwoA.Co2Inv.RowsInputs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.Co2
  CFSG.Monster.B.TwoA.Census

theorem exists_bvec8 : ∀ v : V8, ∃ x < 256, bvec 8 x = v :=
  Certificates.certificate3076.1

@[expose] def gensL
    (k : ℕ) : V8 ≃ₗ[ZMod 2] V8 := if h : k < 45 then xGenL ⟨k, h⟩
    else 1

theorem gensL_of_lt
    {k : ℕ} (h : k < 45) : gensL k = xGenL ⟨k, h⟩ := dite_eq_left h

theorem gensL_image
    {n : ℕ} (hn : n ≤ 45) :
    gensL '' {k | k < n} = Set.range fun i : Fin n => xGenL ⟨i, by omega⟩ := by
  ext f
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, (gensL_of_lt (by simp at hk; omega)).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.2, gensL_of_lt (by omega)⟩

theorem vecCheck :
    natCertOK vecAct 45 vecValid 1 vecCert = true ∧ vecCert.pts.size = 255 ∧
    ∀ x < 256, x ≠ 0 → ∃ i < 255, vecCert.pts[i]! = x :=
  Certificates.certificate3076.2.1

theorem vecAct_spec
    (k : ℕ) (hk : k < 45) (a : ℕ) (_ : vecValid a = true) :
    bvec 8 (vecAct k a) = gensL k • bvec 8 a := by
  rw [gensL_of_lt hk, LinearEquiv.smul_def, xGenL_bvec]
  rfl

theorem exists_conjImage_X
    {v : V8} (hv : v ≠ 0) :
    ∃ f ∈ Subgroup.closure (Set.range xGenL), f (Pi.single 0 1) = v := by
  obtain ⟨x, hx, rfl⟩ := exists_bvec8 v
  have hx0 : x ≠ 0 := fun h => hv (by rw [h, bvec_zero])
  obtain ⟨i, hi, hix⟩ := vecCheck.2.2 x hx hx0
  have horb := orbit_of_natCertOK (G := V8 ≃ₗ[ZMod 2] V8) (dec := bvec 8) vecCheck.1
    (fun k hk a ha => vecAct_spec k hk a ha)
  have hmem : bvec 8 vecCert.pts[i]! ∈ MulAction.orbit
      (Subgroup.closure (gensL '' {k | k < 45})) (bvec 8 1) := by
    rw [horb]
    exact ⟨i, by rw [vecCheck.2.1]; exact hi, rfl⟩
  have hcl : Subgroup.closure (gensL '' {k | k < 45}) = Subgroup.closure (Set.range xGenL) := by
    rw [gensL_image le_rfl]
  obtain ⟨g, hg⟩ := hmem
  refine ⟨(g : V8 ≃ₗ[ZMod 2] V8), hcl ▸ g.2, ?_⟩
  rw [← bvec8_one, ← hix]
  exact hg

theorem tupCheck :
    natCertOK tupAct 23 tupValid tupRoot tupCert = true ∧
    tupCert.pts.size = 128 :=
  Certificates.certificate3076.2.2

theorem tupAct_spec
    (k : ℕ) (hk : k < 45) (a : ℕ) (_ : tupValid a = true) :
    tupDec (tupAct k a) = gensL k • tupDec a := by
  funext t
  rw [Pi.smul_apply, tupDec, tupDec, tupAct, Co2Inv.rowOf_encL, bvec8_mod,
    getD_range_map _ t.2, gensL_of_lt hk, LinearEquiv.smul_def, xGenL_bvec]

abbrev pauliImg :
    Subgroup (V8 ≃ₗ[ZMod 2] V8) :=
  Subgroup.closure (Set.range fun i : Fin 23 => xGenL ⟨i, by omega⟩)

theorem stabilizer_root_eq_bot :
    MulAction.stabilizer pauliImg (fun t => (Pi.single t 1 : V8)) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_
  rw [MulAction.mem_stabilizer_iff] at hg
  apply Subtype.ext
  refine (Pi.basisFun (ZMod 2) (Fin 8)).ext' fun t => ?_
  have := congrFun hg t
  rw [Pi.basisFun_apply]
  exact this

theorem natCard_conjImage_Ehat :
    Nat.card
    ((Ehat.subgroupOf NA8).map conjHom) = 128 := by
  have hcl : Subgroup.closure (gensL '' {k | k < 23}) = pauliImg := by
    rw [gensL_image (by norm_num)]
  have h := ncard_orbit_of_natCertOK (G := V8 ≃ₗ[ZMod 2] V8) (dec := tupDec) tupCheck.1
    (fun k hk a ha => tupAct_spec k (by omega) a ha) tupDec_injective
  rw [tupCheck.2, hcl, tupDec_root] at h
  have hi := MulAction.index_stabilizer pauliImg (fun t => (Pi.single t 1 : V8))
  rw [stabilizer_root_eq_bot, Subgroup.index_bot, h] at hi
  rw [conjImage_Ehat]
  exact hi

end CFSG.Monster.B.TwoA.Sp8
