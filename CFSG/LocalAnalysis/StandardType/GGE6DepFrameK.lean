module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKnownDataOf
public import CFSG.LocalAnalysis.StandardType.GGE6DepKCoord
public import CFSG.LocalAnalysis.StandardType.GGE6DepKAut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly E6Dep

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

theorem ggE6Dep_frameK (hRig : GGLabelRigidInput) (hM : GGE6DepModelKnown)
    {Bs X : Subgroup G} {y : G} (hy1 : y ≠ 1) (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hcardBs : Nat.card Bs = 3 ^ 6) {lab₀ : LargeEvenLabel} (hlab₀ : GGE6DepLabel lab₀)
    (hmark : LargeEvenMarking X (fun lab _ _ _ _ _ => lab = lab₀)) (hinn : GGInnerDiagOn Bs X)
    (hker : Bs ⊓ Subgroup.centralizer (X : Set G) = Subgroup.zpowers y) :
    ∃ κ : Additive ↥Bs →+ Vec6, GGE6DepKFrame Bs X y κ := by
  classical
  have hyinf : y ∈ Bs ⊓ Subgroup.centralizer (X : Set G) := by
    rw [hker]
    exact Subgroup.mem_zpowers y
  have hyBs : y ∈ Bs := hyinf.1
  have hy3 : y ^ 3 = 1 := hBs.2 y hyBs
  have hcard3 : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) = 3 := by
    rw [hker, Nat.card_zpowers]
    exact orderOf_eq_prime hy3 hy1
  obtain ⟨hBsN, R, _, I, ψ, hTB, hcard, hmodel⟩ :=
    ggE6Dep_known_data_model_of hRig hM hBs hSC hcardBs hlab₀ hmark hinn hcard3
  obtain ⟨Φ, T, w, hwith⟩ := hmodel
  obtain ⟨h1, h2, h3⟩ := kappaOf_frame_base hBsN hwith hcard hker
  obtain ⟨h4, h5⟩ := kappaOf_aut hBsN hwith hcard hSC
  exact ⟨kappaOf hBsN Φ, h1, h2, h3, h4, h5⟩

end CFSG.StandardType

end
