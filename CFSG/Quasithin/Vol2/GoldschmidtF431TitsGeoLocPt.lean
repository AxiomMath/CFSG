module

public import Certificates.Data.RuF45Geom
public import Certificates.Data.TitsF46Words
public import CFSG.Monster.B.Co2.PermArr
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoDAct
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoElt
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoPtLoc
public import CFSG.Quasithin.Vol2.GoldschmidtF45RuPoly

public noncomputable section

namespace CFSG.Quasithin.TitsGeo

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.H13.F45Ru CFSG.RuF45 CFSG.TitsF46
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

section Aff

@[expose] def labV (i : ZMod 5) : Vtx := ofCode (titsLabPt[i.val]!)

theorem val_affine (α β : ℕ) (i : ZMod 5) :
    (((α : ZMod 5) * i + (β : ZMod 5)).val) = (α * i.val + β) % 5 := by
  have : ((α : ZMod 5) * i + (β : ZMod 5)) = ((α * i.val + β : ℕ) : ZMod 5) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [this, ZMod.val_natCast]

theorem arith_mul : ∀ a b : ZMod 5, a ≠ 0 → b ≠ 0 → a * b ≠ 0 := by decide

theorem arith_inv : ∀ a : ZMod 5, a ≠ 0 → ∃ c : ZMod 5, a * c = 1 := by decide

@[expose] def affSub : Subgroup ↥titsD where
  carrier := {x | ∃ α β : ZMod 5, α ≠ 0 ∧ ∀ i, x • labV i = labV (α * i + β)}
  one_mem' := ⟨1, 0, by decide, fun i => by simp⟩
  mul_mem' := by
    rintro x y ⟨α, β, hα, hx⟩ ⟨α', β', hα', hy⟩
    refine ⟨α * α', α * β' + β, arith_mul _ _ hα hα', fun i => ?_⟩
    rw [mul_smul, hy, hx]
    congr 1
    ring
  inv_mem' := by
    rintro x ⟨α, β, hα, hx⟩
    obtain ⟨γ, hγ⟩ := arith_inv α hα
    have hγ0 : γ ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hγ
      exact absurd hγ (by decide)
    refine ⟨γ, -(γ * β), hγ0, fun i => ?_⟩
    rw [inv_smul_eq_iff, hx]
    congr 1
    linear_combination (-i + β) * hγ

end Aff

end CFSG.Quasithin.TitsGeo
