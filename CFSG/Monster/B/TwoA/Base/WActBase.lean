module

public import CFSG.Monster.B.Co2.MatrixWBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B.Co2

instance finite_W :

    Finite (Wv v0) := Finite.of_equiv _ qbWBasis.equivFun.toEquiv.symm

def wStab (x : Wv v0) : Subgroup (Kstab v0) where
  carrier := {k | wAct v0 k x = x}
  one_mem' := by
    change wAct v0 1 x = x
    rw [wAct_one, Module.End.one_apply]
  mul_mem' {k k'} hk hk' := by
    change wAct v0 (k * k') x = x
    rw [wAct_mul, Module.End.mul_apply]
    rw [show wAct v0 k x = x from hk, show wAct v0 k' x = x from hk']
  inv_mem' {k} hk := by
    change wAct v0 k⁻¹ x = x
    conv_lhs => rw [← show wAct v0 k x = x from hk]
    exact wAct_inv_apply k x

theorem mem_wStab {x : Wv v0} {k : Kstab v0} : k ∈ wStab x ↔ wAct v0 k x = x := Iff.rfl

def wSetStab
    (U : Submodule (ZMod 2) (Wv v0)) : Subgroup (Kstab v0) where
  carrier := {k | ∀ x ∈ U, wAct v0 k x ∈ U}
  one_mem' := fun x hx => by
    rw [wAct_one, Module.End.one_apply]
    exact hx
  mul_mem' {k k'} hk hk' := fun x hx => by
    rw [wAct_mul, Module.End.mul_apply]
    exact hk' _ (hk x hx)
  inv_mem' {k} hk := fun x hx => by
    have hinj : Set.InjOn (wAct v0 k) (U : Set (Wv v0)) := fun a _ b _ hab => by
      rw [← wAct_inv_apply k a, ← wAct_inv_apply k b, hab]
    have hfin : (U : Set (Wv v0)).Finite := Set.toFinite _
    have hsurj := (Set.Finite.injOn_iff_bijOn_of_mapsTo hfin (fun a ha => hk a ha)).1 hinj
    obtain ⟨y, hy, rfl⟩ := hsurj.surjOn hx
    rw [wAct_inv_apply]
    exact hy

theorem mem_wSetStab
    {U : Submodule (ZMod 2) (Wv v0)} {k : Kstab v0} :
    k ∈ wSetStab U ↔ ∀ x ∈ U, wAct v0 k x ∈ U := Iff.rfl

def wFix (S : Set (Wv v0)) : Subgroup (Kstab v0) := ⨅ x ∈ S, wStab x

theorem mem_wFix {S : Set (Wv v0)} {k : Kstab v0} : k ∈ wFix S ↔ ∀ x ∈ S, wAct v0 k x = x := by
  simp only [wFix, Subgroup.mem_iInf, mem_wStab]

def wOrbit (x : Wv v0) : Set (Wv v0) := Set.range fun k : Kstab v0 => wAct v0 k x

@[instance_reducible] def wLeftAction : MulAction (Kstab v0) (Wv v0) where
  smul k x := wAct v0 k⁻¹ x
  one_smul x := by
    change wAct v0 1⁻¹ x = x
    rw [inv_one, wAct_one, Module.End.one_apply]
  mul_smul k k' x := by
    change wAct v0 (k * k')⁻¹ x = wAct v0 k⁻¹ (wAct v0 k'⁻¹ x)
    rw [mul_inv_rev, wAct_mul, Module.End.mul_apply]

theorem stabilizer_wLeftAction (x : Wv v0) :
    @MulAction.stabilizer (Kstab v0) (Wv v0) _ wLeftAction x = wStab x := by
  ext k
  change wAct v0 k⁻¹ x = x ↔ wAct v0 k x = x
  constructor
  · intro h
    conv_lhs => rw [← h]
    exact wAct_apply_inv k x
  · intro h
    conv_lhs => rw [← h]
    exact wAct_inv_apply k x

theorem orbit_wLeftAction (x : Wv v0) :
    @MulAction.orbit (Kstab v0) (Wv v0) wLeftAction.toSMul x = wOrbit x := by
  ext y
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k⁻¹, rfl⟩
  · rintro ⟨k, rfl⟩
    refine ⟨k⁻¹, ?_⟩
    change wAct v0 k⁻¹⁻¹ x = wAct v0 k x
    rw [inv_inv]

theorem index_wStab
    (x : Wv v0) : (wStab x).index = (wOrbit x).ncard := by
  rw [← stabilizer_wLeftAction, ← orbit_wLeftAction]
  exact @MulAction.index_stabilizer (Kstab v0) (Wv v0) _ wLeftAction x

end CFSG.Monster.B.TwoA
