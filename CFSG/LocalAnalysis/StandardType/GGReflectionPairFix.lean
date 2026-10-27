module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGen
public import CFSG.LocalAnalysis.StandardType.GGTypeAReflOverCoord
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofLin
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG
open scoped IsMulCommutative

theorem ggFixG_mul_mem_of_commute {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} (hBs : CFSG.Open.IsElemAbelian p Bs) (hp2 : p ≠ 2)
    {t u : MulAut ↥Bs} (ht : GGIsReflection p t) (hu : GGIsReflection p u)
    (hc : t * u = u * t) (hne : t ≠ u) {x : G} (hx : x ∈ ggFixG Bs (t * u)) :
    x ∈ ggFixG Bs t ∧ x ∈ ggFixG Bs u := by
  have hFin : Finite ↥Bs := Subtype.finite
  have hEA : CFSG.IsElementaryAbelian p ↥Bs := hBs.isElementaryAbelian
  rw [ggFixG, Subgroup.mem_map] at hx
  obtain ⟨b, hb, rfl⟩ := hx
  let T : Additive ↥Bs ≃ₗ[ZMod p] Additive ↥Bs :=
    ggLin (p := p) (AddEquiv.refl (Additive ↥Bs)) t
  let U : Additive ↥Bs ≃ₗ[ZMod p] Additive ↥Bs :=
    ggLin (p := p) (AddEquiv.refl (Additive ↥Bs)) u
  have hT : IsLinRefl T := isLinRefl_ggLin (p := p) (AddEquiv.refl (Additive ↥Bs)) ht
  have hU : IsLinRefl U := isLinRefl_ggLin (p := p) (AddEquiv.refl (Additive ↥Bs)) hu
  have hcL : T * U = U * T := by
    dsimp only [T, U]
    rw [← map_mul, ← map_mul, hc]
  have hneL : T ≠ U := by
    intro h
    exact hne (ggLin_injective (p := p) (AddEquiv.refl (Additive ↥Bs)) (by simpa [T, U] using h))
  let v : Additive ↥Bs := Additive.ofMul b
  have hTUv : T (U v) = v := by
    have h2 : T * U = ggLin (p := p) (AddEquiv.refl (Additive ↥Bs)) (t * u) := by
      dsimp only [T, U]
      rw [map_mul]
    calc T (U v) = (T * U) v := (LinearEquiv.mul_apply T U v).symm
      _ = ggLin (p := p) (AddEquiv.refl (Additive ↥Bs)) (t * u) v := by rw [h2]
      _ = v := by
            dsimp only [v]
            rw [ggLin_apply]
            change Additive.ofMul ((t * u) b) = Additive.ofMul b
            rw [show (t * u) b = b from hb]
  have hUv : U v = T v := by
    calc U v = T (T (U v)) := (hT.apply_apply (U v)).symm
      _ = T v := by rw [hTUv]
  let w : Additive ↥Bs := T v
  have hcomm : T (U v) = U (T v) := by
    have h := congrArg (fun S : Additive ↥Bs ≃ₗ[ZMod p] Additive ↥Bs => S v) hcL
    simpa only [LinearEquiv.mul_apply] using h
  have hUw : U w = v := by
    dsimp only [w]
    rw [← hcomm, hTUv]
  have hTw : T w = v := by
    dsimp only [w]
    exact hT.apply_apply v
  have hTz : T (v - w) = -(v - w) := by
    rw [map_sub, hTw, neg_sub]
  have hUz : U (v - w) = -(v - w) := by
    rw [map_sub, hUv, hUw, neg_sub]
  have hfix : U (v - w) = v - w :=
    IsLinRefl.comm_fix hp2 hT hU hcL hneL hTz
  have hz : v - w = 0 := by
    have hneg : v - w = -(v - w) := hfix.symm.trans hUz
    have h2z : (2 : ZMod p) • (v - w) = 0 := by
      rw [two_smul]
      exact eq_neg_iff_add_eq_zero.mp hneg
    rcases smul_eq_zero.mp h2z with h2 | h0
    · exact absurd h2 (zmod_two_ne_zero hp2)
    · exact h0
  have hvw : v = w := sub_eq_zero.mp hz
  have hTv : T v = v := (show T v = w from rfl).trans hvw.symm
  have hUv' : U v = v := by rw [hUv, hTv]
  have htb : t b = b :=
    (ggLin_fix_iff (p := p) (AddEquiv.refl (Additive ↥Bs)) t b).mpr
      (by simpa [T, v] using hTv)
  have hub : u b = b :=
    (ggLin_fix_iff (p := p) (AddEquiv.refl (Additive ↥Bs)) u b).mpr
      (by simpa [U, v] using hUv')
  exact ⟨Subgroup.mem_map.mpr ⟨b, htb, rfl⟩, Subgroup.mem_map.mpr ⟨b, hub, rfl⟩⟩

end CFSG.StandardType
