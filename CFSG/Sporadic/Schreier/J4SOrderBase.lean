
module

public import CFSG.Sporadic.Schreier.J4SOrbitCheckBase
public import CFSG.Sporadic.Schreier.J4SChain
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbitsBase
public meta import CFSG.Sporadic.Schreier.J4SOrbitsBase
public import CFSG.Sporadic.J4.Local

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.SectionRank CFSG.SectionRank.Native
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

@[expose] def kvec (i : ℕ) : Row := toRow (toVecD 112 ksetVectors[i]!)

theorem inv_smul_toRow {g : J} {G : Pair} (hg : Rep Sp φ g G) (s : ℕ) :
    g⁻¹ • toRow (toVecD 112 s) = toRow (toVecD 112 (O.vmul s G.1)) := by
  rw [← ofRow_inj, inv_smul_row]
  have h := Sp.toVec_vmul (v := s) trivial hg.1
  rw [hg.2.2.1] at h
  exact h.symm

abbrev ksetRows : Set Row := kvec '' Set.Iio ksetSize

@[expose] def withZero (pts : Array ℕ) (i : ℕ) : ℕ := if i = 0 then 0 else pts[i - 1]!

abbrev ρN : NN →* MulAut N := N.normalizerMonoidHom

@[expose] def ηN (a : ℕ) : N := ⟨η a, η_mem_N a⟩

@[expose] def sgenK (m : ℕ) : K := ⟨sgen m, sgen_mem_K m⟩

theorem gens1_eq (g : ℕ) (hg : g < 8) : gens1[g]! = sCols idx1[g]! := by
  interval_cases g <;> rfl

theorem gens2_eq (g : ℕ) (hg : g < 5) : gens2[g]! = sCols idx2[g]! := by
  interval_cases g <;> rfl

theorem toVecD_rootBits : toVecD 112 rootBits = Native.rootV.toVec := by
  funext j
  rw [toVecD_apply, Native.V2.toVec_apply, ← Native.V2.testBit_toNat _ (by omega), rootV_toNat]
  where rootV_toNat : Native.rootV.toNat = rootBits := by decide

theorem smul_v_of {g : J} {G : Pair} (hg : Rep Sp φ g G) (h : O.vmul rootBits G.1 = rootBits) :
    g • v = v := by
  have h1 := inv_smul_toRow hg rootBits
  rw [h] at h1
  calc g • v = g • (g⁻¹ • v) := by rw [v, h1]
    _ = v := smul_inv_smul g v

theorem card_ker_mul_card_range {G G' : Type*} [Group G] [Group G'] [Finite G] (f : G →* G') :
    Nat.card f.ker * Nat.card f.range = Nat.card G := by
  rw [← Subgroup.index_ker, Subgroup.card_mul_index]

end CFSG.Sporadic.J4Schreier
