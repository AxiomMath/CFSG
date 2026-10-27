module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CCoordDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7CKCoordBAux

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7CKCoordAux_support
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hrow : GGResRowAt ggRowCorank2C p J K) (n : ℕ) (hy : y ∈ Bs) (hx : x ∈ Bs)
    (τ : (Fin (n + 1) → Multiplicative (ZMod p)) ≃* ↥Bs) (hp3 : p = 3) (hn : 5 ≤ n)
    (h0 : τ (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod p))) = ⟨y, hy⟩)
    (hmodel : C2CoordModel p Bs K n τ)
    (hmem : ∀ f : Fin (n + 1) → Multiplicative (ZMod p), ((τ f : ↥Bs) : G) ∈ K ↔ f 0 = 1) :
    ∃ i j : Fin (n + 1), i ≠ 0 ∧ j ≠ 0 ∧ i ≠ j ∧
      ∀ l : Fin (n + 1), l ≠ 0 → (Multiplicative.toAdd (τ.symm ⟨x, hx⟩ l) ≠ 0 ↔ l = i ∨ l = j) := by
  obtain ⟨m, φ, -, hinj, hrange⟩ := hdRo7CKCoordAux_spLift hRig hH hrow
  obtain ⟨c, z, hz, hxz⟩ := hdRo7CKCoordAux_x_decomp hRig hH hrow n hy τ hp3 h0 hmodel hx
  have hJz := hdRo7CKCoordAux_component_K_z hLB hH hrow z hz c hxz
  obtain ⟨i, j, hi, hj, hij, hsupp_z⟩ :=
    hdRo7CKCoordAux_support_of_statedSp hRig hH hrow n hy τ hp3 hn h0 hmodel hmem m φ hinj hrange
      z hz hJz
  refine ⟨i, j, hi, hj, hij, fun l hl => ?_⟩
  exact (hdRo7CKCoordAux_support_transfer n hy hx hz.1 τ h0 c hxz l hl).trans (hsupp_z l hl)

end CFSG.StandardType.HdRo7C

end
