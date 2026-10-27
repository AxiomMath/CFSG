module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueRootModel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosureRefl
public import Certificates.Certificate709545
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueIdentW
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueIdentSSigned
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueIdentSRoot
import Mathlib.GroupTheory.GroupAction.Quotient

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.OddStandard.SmallF3.Omega.E7RootSet E7WeightRoot

namespace E7WeightRoot

theorem rhoLinear_apply
    (w : WeylGroup Tag.E7) (v : FEVec 7) : rhoLinear w v = rhoEquiv w v := rfl

end E7WeightRoot

variable {G : Type} [Group G] {Bs : Subgroup G} {x : G}

theorem card_stabilizer_full_automizer (hx : x ∈ Bs) :
    Nat.card (MulAction.stabilizer ↥(ggAutomizer (⊤ : Subgroup G) Bs)
      (⟨x, hx⟩ : ↥Bs)) =
      Nat.card (ggAutomizer (Subgroup.centralizer ({x} : Set G)) Bs) := by
  classical
  let A := ggAutomizer (⊤ : Subgroup G) Bs
  let C := ggAutomizer (Subgroup.centralizer ({x} : Set G)) Bs
  let b : ↥Bs := ⟨x, hx⟩
  let f : ↥C → ↥(MulAction.stabilizer ↥A b) := fun φ =>
    ⟨⟨(φ : MulAut ↥Bs), ggAutomizer_mono Bs le_top φ.2⟩, by
      change (φ : MulAut ↥Bs) b = b
      apply Subtype.ext
      obtain ⟨g, hgC, _, hg⟩ := mem_ggAutomizer_iff.mp φ.2
      have hc : x * g = g * x :=
        Subgroup.mem_centralizer_iff.mp hgC x (Set.mem_singleton x)
      rw [hg]
      change g * x * g⁻¹ = x
      rw [← hc]
      group⟩
  have hinj : Function.Injective f := by
    intro φ ψ h
    apply Subtype.ext
    exact congrArg (fun a : ↥(MulAction.stabilizer ↥A b) => (a.1.1 : MulAut ↥Bs)) h
  have hsurj : Function.Surjective f := by
    intro a
    let φ : MulAut ↥Bs := a.1.1
    have hφA : φ ∈ A := a.1.2
    have hfix : φ b = b := a.2
    have hφC : φ ∈ C := mem_ggAutomizer_centralizer_of_apply_eq hx hφA hfix
    refine ⟨⟨φ, hφC⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm

theorem card_full_automizer_le [Finite G] (hx : x ∈ Bs) (hx1 : x ≠ 1) :
    Nat.card (ggAutomizer (⊤ : Subgroup G) Bs) ≤
      (Nat.card Bs - 1) * Nat.card (ggAutomizer (Subgroup.centralizer ({x} : Set G)) Bs) := by
  let A := ggAutomizer (⊤ : Subgroup G) Bs
  let b : ↥Bs := ⟨x, hx⟩
  have hnot : (1 : ↥Bs) ∉ MulAction.orbit ↥A b := by
    rintro ⟨φ, hφ⟩
    change (φ : MulAut ↥Bs) b = 1 at hφ
    have hb : b = 1 := (φ : MulAut ↥Bs).injective
      (hφ.trans (map_one (φ : MulAut ↥Bs)).symm)
    exact hx1 (congrArg Subtype.val hb)
  have hproper : MulAction.orbit ↥A b ⊂ (Set.univ : Set ↥Bs) := by
    refine ⟨Set.subset_univ _, ?_⟩
    intro h
    exact hnot (h (Set.mem_univ 1))
  have horbit : (MulAction.orbit ↥A b).ncard < Nat.card Bs := by
    simpa only [Set.ncard_univ] using Set.ncard_lt_ncard hproper
  have hbound : (MulAction.orbit ↥A b).ncard ≤ Nat.card Bs - 1 := by omega
  have hcard := Subgroup.card_mul_index (MulAction.stabilizer ↥A b)
  rw [MulAction.index_stabilizer] at hcard
  have hstab : Nat.card (MulAction.stabilizer ↥A b) =
      Nat.card (ggAutomizer (Subgroup.centralizer ({x} : Set G)) Bs) :=
    card_stabilizer_full_automizer hx
  rw [hstab] at hcard
  calc
    Nat.card A = Nat.card (ggAutomizer (Subgroup.centralizer ({x} : Set G)) Bs) *
        (MulAction.orbit ↥A b).ncard := hcard.symm
    _ ≤ Nat.card (ggAutomizer (Subgroup.centralizer ({x} : Set G)) Bs) *
        (Nat.card Bs - 1) := Nat.mul_le_mul_left _ hbound
    _ = (Nat.card Bs - 1) *
        Nat.card (ggAutomizer (Subgroup.centralizer ({x} : Set G)) Bs) := Nat.mul_comm _ _

namespace GGFrameModelData

theorem card_full_rootCoordinates_lt [Finite G] (M : GGFrameModelData Bs 7)
    (hx : x ∈ Bs) (hx1 : x ≠ 1)
    (hHx : Nat.card (ggAutomizer (Subgroup.centralizer ({x} : Set G)) Bs) ≤ 103680) :
    Nat.card ((ggAutomizer (⊤ : Subgroup G) Bs).map
      (ggLin (p := 3) M.rootCoordinates)) < 4585351680 := by
  rw [Subgroup.card_map_of_injective (ggLin_injective M.rootCoordinates)]
  have hBs : Nat.card Bs = 3 ^ 7 :=
    (card_eq_of_ggLin M.ψ).trans (by simp)
  have h := card_full_automizer_le hx hx1
  rw [hBs] at h
  calc
    Nat.card (ggAutomizer (⊤ : Subgroup G) Bs) ≤
        (3 ^ 7 - 1) * Nat.card (ggAutomizer (Subgroup.centralizer ({x} : Set G)) Bs) := h
    _ ≤ (3 ^ 7 - 1) * 103680 := Nat.mul_le_mul_left _ hHx
    _ < 4585351680 := by decide +kernel

end GGFrameModelData

namespace GGFrameModelData

theorem exists_weyl_conj_rootCoordinates
    (M : GGFrameModelData Bs 7)
    (hA : Nat.card M.A = 2903040)
    (hgen : ∀ φ : ↥M.A, M.ρ φ ∈ Submonoid.closure (Set.range (feS 7)))
    {z : G} (hz : z ∈ Bs) (h : MulAut ↥Bs)
    (hnorm : ∀ k ∈ M.A ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨z, hz⟩ : ↥Bs),
      h * k * h⁻¹ ∈ M.A ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨z, hz⟩ : ↥Bs))
    (w : WeylGroup Tag.E7)
    (hw : rhoEquiv w (M.rootCoordinates (Additive.ofMul (⟨z, hz⟩ : ↥Bs))) =
      M.rootCoordinates (Additive.ofMul (⟨z, hz⟩ : ↥Bs))) :
    ∃ w' : WeylGroup Tag.E7, ∀ v : FEVec 7,
      ggLin (p := 3) M.rootCoordinates h
          (rhoEquiv w ((ggLin (p := 3) M.rootCoordinates h).symm v)) = rhoEquiv w' v := by
  let Φ := ggLin (p := 3) M.rootCoordinates
  have hwA : rhoLinear w ∈ M.A.map Φ := by
    rw [show M.A.map Φ = rhoLinear.range from M.map_rootCoordinates_eq_weyl hA hgen]
    exact ⟨w, rfl⟩
  obtain ⟨k, hkA, hkW⟩ := Subgroup.mem_map.mp hwA
  have hkfix : k (⟨z, hz⟩ : ↥Bs) = ⟨z, hz⟩ := by
    apply (ggLin_fix_iff (p := 3) M.rootCoordinates k (⟨z, hz⟩ : ↥Bs)).mpr
    change Φ k _ = _
    rw [hkW, rhoLinear_apply]
    exact hw
  have hkK : k ∈ M.A ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨z, hz⟩ : ↥Bs) :=
    ⟨hkA, hkfix⟩
  have hconjA := (hnorm k hkK).1
  obtain ⟨w', hw'⟩ := M.exists_weyl_rootCoordinates hgen ⟨h * k * h⁻¹, hconjA⟩
  refine ⟨w', ?_⟩
  have heq : Φ h * rhoLinear w * (Φ h)⁻¹ = rhoLinear w' := by
    rw [← hkW, ← map_inv, ← map_mul, ← map_mul]
    exact hw'
  intro v
  have hpt := congrArg (fun f : FEVec 7 ≃ₗ[ZMod 3] FEVec 7 => f v) heq
  simp only [LinearEquiv.mul_apply] at hpt
  change Φ h (rhoLinear w ((Φ h).symm v)) = rhoLinear w' v at hpt
  simpa only [rhoLinear_apply] using hpt

theorem rootCoordinates_ne_weyl
    (M : GGFrameModelData Bs 7)
    (hA : Nat.card M.A = 2903040)
    (hgen : ∀ φ : ↥M.A, M.ρ φ ∈ Submonoid.closure (Set.range (feS 7)))
    {z : G} (hz : z ∈ Bs) (h : MulAut ↥Bs)
    (hfix : h (⟨z, hz⟩ : ↥Bs) = ⟨z, hz⟩)
    (hout : h ∉ M.A ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨z, hz⟩ : ↥Bs))
    (w : WeylGroup Tag.E7) :
    ggLin (p := 3) M.rootCoordinates h ≠ rhoEquiv w := by
  intro heq
  have hmem : ggLin (p := 3) M.rootCoordinates h ∈ M.A.map
      (ggLin (p := 3) M.rootCoordinates) := by
    rw [M.map_rootCoordinates_eq_weyl hA hgen, heq]
    exact ⟨w, LinearEquiv.ext (fun v => rhoLinear_apply w v)⟩
  obtain ⟨k, hkA, hk⟩ := Subgroup.mem_map.mp hmem
  have hkh : k = h := ggLin_injective M.rootCoordinates hk
  subst k
  exact hout ⟨hkA, hfix⟩

end GGFrameModelData

theorem false_of_signedB6At
    [Finite G]
    (M : GGFrameModelData Bs 7) (hA : Nat.card M.A = 2903040)
    (hgen : ∀ φ : ↥M.A, M.ρ φ ∈ Submonoid.closure (Set.range (feS 7)))
    (hBs : IsElemAbelian 3 Bs) (hNT : GGNoTransvection 3 Bs) {x z : G}
    (hxBs : x ∈ Bs) (hx1 : x ≠ 1)
    (hHx : Nat.card (ggAutomizer (Subgroup.centralizer ({x} : Set G)) Bs) ≤ 103680)
    (hz : M.IsRoot z) (hsgn : GGSignedB6At Bs z) : False := by
  let b : ↥Bs := ⟨z, hz.1⟩
  let K := M.A ⊓ MulAction.stabilizer (MulAut ↥Bs) b
  have hW : Nat.card K = 23040 := by
    simpa [K, b] using card_stabilizer_isRoot M (Or.inl rfl)
      (by simpa using hA) hgen hz
  have hK : K ≤ ggAutomizer (Subgroup.centralizer ({z} : Set G)) Bs := by
    intro k hk
    apply mem_ggAutomizer_centralizer_of_apply_eq hz.1
    · exact Subgroup.subset_closure (M.induced k hk.1)
    · exact hk.2
  obtain ⟨h, hh, hout, hrefl, hnorm⟩ :=
    exists_reflection_not_mem_of_signedB6At hBs hNT hz.1 hz.2.1 hsgn hK hW
  have hfix : h b = b := by
    obtain ⟨a, ha, _, hact⟩ := mem_ggAutomizer_iff.mp hh
    apply Subtype.ext
    rw [hact]
    change a * z * a⁻¹ = z
    rw [Subgroup.mem_centralizer_singleton_iff.mp ha]
    group
  let Φ := ggLin (p := 3) M.rootCoordinates
  let S := (ggAutomizer (⊤ : Subgroup G) Bs).map Φ
  let zz := M.rootCoordinates (Additive.ofMul b)
  let g := Φ h
  have hWS : ∀ w : WeylGroup Tag.E7, rhoEquiv w ∈ S := by
    intro w
    have hw : rhoLinear w ∈ S := M.weyl_le_full_rootCoordinates hA hgen ⟨w, rfl⟩
    have heq : rhoLinear w = rhoEquiv w := LinearEquiv.ext (fun v => rhoLinear_apply w v)
    rwa [heq] at hw
  have hS : Nat.card S < 4585351680 := M.card_full_rootCoordinates_lt hxBs hx1 hHx
  have hzz : zz ∈ rootSet := M.rootCoordinates_mem_rootSet hz.1 hz
  have hgS : g ∈ S := ⟨h, ggAutomizer_mono Bs le_top hh, rfl⟩
  have hgzz : g zz = zz := by
    change ggLin (p := 3) M.rootCoordinates h
      (M.rootCoordinates (Additive.ofMul b)) = M.rootCoordinates (Additive.ofMul b)
    rw [ggLin_apply_ofMul, hfix]
  have hcard : Nat.card {v : FEVec 7 // g v = v} * 3 = 3 ^ 7 := by
    have hc := ((ggIsReflection_iff (p := 3) M.rootCoordinates h).mp hrefl).2
    simpa only [Nat.card_fun, Nat.card_fin, Nat.card_zmod] using hc
  have hnormR : ∀ w : WeylGroup Tag.E7, rhoEquiv w zz = zz →
      ∃ w' : WeylGroup Tag.E7, ∀ v : FEVec 7,
        g (rhoEquiv w (g.symm v)) = rhoEquiv w' v := by
    intro w hw
    exact M.exists_weyl_conj_rootCoordinates hA hgen hz.1 h hnorm w hw
  have houtR : ∀ w : WeylGroup Tag.E7, g ≠ rhoEquiv w :=
    M.rootCoordinates_ne_weyl hA hgen hz.1 h hfix hout
  exact e7_false_of_reflection_normalizes_stabilizer S hWS hS hzz g hgS hgzz hcard
    hnormR houtR

end CFSG.StandardType.FrameRoute

end
