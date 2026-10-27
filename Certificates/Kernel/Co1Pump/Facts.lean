module

public import Certificates.Kernel.Co1Pump.Glue
public import Certificates.Kernel.Co1Pump.GlueFix
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeDefs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1SevenBase
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1FiveBase
public import CFSG.Sporadic.Co1Block.Perm
public import Certificates.Data.CFSGNative.Timmesfeld.Co1Leaf
public import Certificates.Certificate2043
public import Certificates.Certificate2133
public import Certificates.Certificate2135
public import Certificates.Certificate2147
public import Certificates.Certificate2148
public import Certificates.Certificate2150
public import Certificates.Certificate3024
public import Certificates.Certificate13665
public import Certificates.Certificate13697
public import Certificates.Certificate13698

public section

namespace CertificateChecks.KernelCo1Pump

open CFSG.KC.Co1Pairs

theorem expVecs_eq : Timmesfeld.Co1Leaf.expVecs 3 6 = (List.range 729).map dig3 := by
  decide +kernel

theorem dig3_eq {k : ℕ} (hk : k < 729) : (Timmesfeld.Co1Leaf.expVecs 3 6).getD k [] = dig3 k := by
  rw [expVecs_eq, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
    List.getElem_range]

open Certificates in
open CFSG.Sporadic.Co1Schreier CFSG.HardMathSupport.Timmesfeld.SporadicBalance in
open CFSG.Sporadic.Co1Block (certX) in
open CFSG.Sporadic.SmallF2 (rowsMatrix) in
open scoped Matrix in
theorem facts36909 :
    (
      ∀ k < 729, k ≠ 0 → ∃ h r : ↥GA,
        (r = Co1T.eltG Co1T.aGA [1, 0, 0, 0, 0, 0] ∨ r = Co1T.eltG Co1T.aGA [0, 1, 0, 0, 0, 0] ∨
          r = Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0]) ∧
        h * r * h⁻¹ = Co1T.eltG Co1T.aGA ((Timmesfeld.Co1Leaf.expVecs 3 6).getD k [])) ∧
    (
      (∃ c : ↥GA, c * Co1T.eltG Co1T.aGA [0, 1, 0, 0, 0, 0] = Co1T.root 1 * c) ∧
      (∃ c : ↥GA, c * Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0] = Co1T.root 0 * c) ∧
      (∃ v : ↥GA, v * Co1T.eltG Co1T.aGA [1, 0, 0, 0, 0, 0] =
        Co1T.eltG Co1T.aGA [1, 0, 0, 0, 0, 0] * v ∧ orderOf v = 13) ∧
      (∃ v c : ↥GA, v * Co1T.eltG Co1T.aGA [0, 1, 0, 0, 0, 0] =
        Co1T.eltG Co1T.aGA [0, 1, 0, 0, 0, 0] * v ∧ orderOf v = 7 ∧ c * v = Co1S.sE * c) ∧
      (∃ v c : ↥GA, v * Co1T.root 2 = Co1T.root 2 * v ∧ orderOf v = 7 ∧ c * v = Co1S.tE * c)) ∧
    (
      Nat.card ↥{v : Vec24 | ((Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0] : GL24) :
        Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v} = 64 ∧
      (certX ∩ {v : Vec24 | ((Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0] : GL24) :
        Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v}).ncard = 27 ∧
      ∀ x ∈ certX, x ∉ {v : Vec24 | ((Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0] : GL24) :
        Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v} →
        {y | y ∈ certX ∧ y - x ∈ {v : Vec24 | ((Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0] : GL24) :
          Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v}}.ncard ≤ 9) ∧
    (
      ∀ k < 125, k ≠ 0 →
      Nat.card ↥{v : Vec24 | rowsMatrix 24 (Timmesfeld.Co1Five.a0Row Co1F.gRows k) *ᵥ v = v} ≤ 256 ∧
      ((certX ∩ {v : Vec24 | rowsMatrix 24 (Timmesfeld.Co1Five.a0Row Co1F.gRows k) *ᵥ v = v}).ncard
          < 27 ∨
        54 < (certX ∩
          {v : Vec24 | rowsMatrix 24 (Timmesfeld.Co1Five.a0Row Co1F.gRows k) *ᵥ v = v}).ncard)) ∧
    (
      ∃ u₁ u₂ : ↥GA,
        u₁ * Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0] = Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0] * u₁ ∧
        u₂ * Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0] = Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0] * u₂ ∧
        orderOf u₁ = 5 ∧ orderOf u₂ = 5 ∧
        1080 < Nat.card ↥(Subgroup.closure ({u₁, u₂} : Set ↥GA))) := by
  refine ⟨fun k hk hk0 => ?_, kill_facts, w_facts, a0_facts, pair_facts⟩
  rw [dig3_eq hk]
  exact fus_facts k (Nat.pos_of_ne_zero hk0) hk

end CertificateChecks.KernelCo1Pump

end
