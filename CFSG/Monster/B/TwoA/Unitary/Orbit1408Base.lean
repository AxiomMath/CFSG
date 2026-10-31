
module

public import CFSG.Monster.B.TwoA.Unitary.SemilinearBase
public import CFSG.Monster.B.Generic.RankThree
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Data
public meta import CFSG.Monster.B.TwoA.Unitary.Orbit1408Data
public meta import CFSG.Monster.B.TwoA.Unitary.NData
public meta import CFSG.Monster.B.TwoA.Unitary.OrbitBase
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Inputs
public import CFSG.Monster.B.TwoA.Unitary.OrbitInputs
public import CFSG.Monster.B.TwoA.Unitary.WStabInputs
public import CFSG.Monster.B.TwoA.Unitary.Stab891Inputs
public import CFSG.Monster.B.TwoA.Unitary.BData
public import CFSG.Monster.B.TwoA.Unitary.PlanesInputs
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Unitary.Bridge
public import CFSG.Monster.B.TwoA.Unitary.ActionInputs

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Fischer CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census CFSG.Monster.B.Generic

attribute [local irreducible] Native.vectors

def OmegaW :
    Set (Wv v0) := wOrbit sigmaW

def tauW : Wv v0 := decW o14Tau

def DeltaW :
    Set (Wv v0) := {x | ∃ j : Fin 891, sigmaW + n6vec j = x}

def usigOrbit
    (x : Wv v0) : Set (Wv v0) := {y | ∃ u ∈ Usig, wAct v0 u x = y}

def Atau :
    Subgroup Usig := (wStab tauW).subgroupOf Usig

theorem mem_Atau
    {u : Usig} : u ∈ Atau ↔ wAct v0 u tauW = tauW := Iff.rfl

theorem wAct_mem_OmegaW
    (k : Kstab v0) {x : Wv v0} (hx : x ∈ OmegaW) : wAct v0 k x ∈
    OmegaW := by
  obtain ⟨k₀, hk₀⟩ := hx
  refine ⟨k₀ * k, ?_⟩
  change wAct v0 (k₀ * k) sigmaW = wAct v0 k x
  rw [wAct_mul, Module.End.mul_apply, ← hk₀]

theorem sigmaW_mem_OmegaW :
    sigmaW ∈ OmegaW :=
  ⟨1, by change wAct v0 1 sigmaW = sigmaW; rw [wAct_one, Module.End.one_apply]⟩

theorem sigmaW_add_n6vec
    (j : Fin 891) :
    sigmaW + n6vec j = decW (6144 ^^^ n6VecArr[(j : ℕ)]!) := by
  rw [sigmaW_eq_decW, n6vec, decW_xor]

attribute [local instance] wLeftAction

theorem usigOrbit_eq_orbit
    (x : Wv v0) : usigOrbit x = MulAction.orbit Usig x := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u, hu⟩⁻¹, ?_⟩
    change wAct v0 ((⟨u, hu⟩⁻¹ : Usig) : Kstab v0)⁻¹ x = wAct v0 u x
    rw [Subgroup.coe_inv, inv_inv]
  · rintro ⟨u, rfl⟩
    exact ⟨(u : Kstab v0)⁻¹, Usig.inv_mem u.2, rfl⟩

theorem usigOrbit_eq_of_mem
    {x y : Wv v0} (h : y ∈ usigOrbit x) : usigOrbit y = usigOrbit
    x := by
  rw [usigOrbit_eq_orbit] at h ⊢
  rw [usigOrbit_eq_orbit]
  exact MulAction.orbit_eq_iff.2 h

theorem mem_usigOrbit_self
    (x : Wv v0) : x ∈ usigOrbit x :=
    ⟨1, Usig.one_mem, by rw [wAct_one]; rfl⟩

theorem usigOrbit_subset_OmegaW
    {x : Wv v0} (hx : x ∈ OmegaW) : usigOrbit x ⊆ OmegaW := by
  rintro _ ⟨u, -, rfl⟩
  exact wAct_mem_OmegaW u hx

theorem usigOrbit_sigma :
    usigOrbit sigmaW = {sigmaW} := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact mem_Usig.1 hu
  · rintro rfl
    exact mem_usigOrbit_self _

theorem wAct_sigmaW_add
    {u : Kstab v0} (hu : u ∈ Usig) (z : Wv v0) :
    wAct v0 u (sigmaW + z) = sigmaW + wAct v0 u z := by
  rw [map_add, mem_Usig.1 hu]

theorem sigmaW_add_wFr_mem :
    sigmaW + wFr ∈ DeltaW := ⟨0, by rw [n6vec_zero]⟩

theorem o14VecArr_size : o14VecArr.size = 1408 := by decide +kernel

abbrev tauP (i : ℕ) : Wv v0 := decW tauCert.pts[i]!

abbrev tauPar (i : ℕ) : ℕ := tauCert.par[i]!

abbrev tauLab (i : ℕ) : ℕ := tauCert.lab[i]!

theorem stabilizer_tauW :
    MulAction.stabilizer Usig tauW = Atau := by
  ext u
  rw [MulAction.mem_stabilizer_iff, mem_Atau]
  change wAct v0 (u : Kstab v0)⁻¹ tauW = tauW ↔ _
  constructor
  · intro h
    conv_lhs => rw [← h]
    exact wAct_apply_inv _ _
  · intro h
    conv_lhs => rw [← h]
    exact wAct_inv_apply _ _

def deltaIdx
    (x : Wv v0) : Fin 891 :=
  Function.invFun (fun j : Fin 891 => sigmaW + n6vec j) x

def shiftPlane
    (x : Wv v0) : Submodule F4 V6 := plane (b6Iso (deltaIdx x))

abbrev OmegaPt :
    Type := ↥OmegaW

instance mulActionOmegaPt :
    MulAction (Kstab v0) OmegaPt where
  smul k x := ⟨wAct v0 k⁻¹ x, wAct_mem_OmegaW k⁻¹ x.2⟩
  one_smul x := Subtype.ext (by
    change wAct v0 1⁻¹ (x : Wv v0) = x
    rw [inv_one, wAct_one, Module.End.one_apply])
  mul_smul k k' x := Subtype.ext (by
    change wAct v0 (k * k')⁻¹ (x : Wv v0) = wAct v0 k⁻¹ (wAct v0 k'⁻¹ x)
    rw [mul_inv_rev, wAct_mul, Module.End.mul_apply])

theorem coe_smul_OmegaPt
    (k : Kstab v0) (x : OmegaPt) :
    ((k • x : OmegaPt) : Wv v0) = wAct v0 k⁻¹ x := rfl

noncomputable instance :
    Fintype OmegaPt := Fintype.ofFinite _

def sigmaPt :
    OmegaPt := ⟨sigmaW, sigmaW_mem_OmegaW⟩

theorem stabilizer_sigmaPt :
    MulAction.stabilizer (Kstab v0) sigmaPt = Usig := by
  ext k
  rw [MulAction.mem_stabilizer_iff, mem_Usig]
  constructor
  · intro h
    have h' : wAct v0 k⁻¹ sigmaW = sigmaW := congrArg Subtype.val h
    conv_lhs => rw [← h']
    exact wAct_apply_inv k _
  · intro h
    apply Subtype.ext
    change wAct v0 k⁻¹ sigmaW = sigmaW
    conv_lhs => rw [← h]
    exact wAct_inv_apply k _

theorem val_image_orbit_sigmaPt
    (β : OmegaPt) :
    Subtype.val '' MulAction.orbit (MulAction.stabilizer (Kstab v0) sigmaPt) β =
      usigOrbit β := by
  rw [stabilizer_sigmaPt]
  ext y
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨(u : Kstab v0)⁻¹, Usig.inv_mem u.2, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨(⟨u, hu⟩⁻¹ : Usig) • β, ⟨⟨u, hu⟩⁻¹, rfl⟩, ?_⟩
    change wAct v0 (u⁻¹)⁻¹ β = wAct v0 u β
    rw [inv_inv]

theorem card_orbit_sigmaPt
    (β : OmegaPt) :
    Nat.card (MulAction.orbit (MulAction.stabilizer (Kstab v0) sigmaPt) β) =
      (usigOrbit β).ncard := by
  rw [← val_image_orbit_sigmaPt, Set.ncard_image_of_injective _ Subtype.val_injective,
    Nat.card_coe_set_eq]

def omegaGraph :
    SimpleGraph OmegaPt := suborbitGraph (Kstab v0) OmegaPt 891

end CFSG.Monster.B.TwoA.Unitary
