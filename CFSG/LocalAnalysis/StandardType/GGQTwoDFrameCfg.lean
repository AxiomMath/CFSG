module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteQTwo
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteJoin
public import CFSG.LocalAnalysis.StandardType.GGPhanSmallStrict
public import CFSG.LocalAnalysis.StandardType.GGHdRo7DSideCoord
public import CFSG.LocalAnalysis.StandardType.GGHdRo7DFrameOmega
public import CFSG.LocalAnalysis.StandardType.GGForkA8NotRefl
public import CFSG.LocalAnalysis.StandardType.GGTableBBstar

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.StandardType CFSG.Assembly CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem ggQTwoD_p_eq_three (hRig : GGLabelRigidInput) {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L)) (hn : lab.n = 1) : p = 3 := by
  have hC : GGConfig p B Bs x L D J := hcfg.1.1
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  obtain ⟨lab₂, hΛ₂, hS, hhas₂⟩ := FrameRoute.ggFrameQTwo_exists_hasLabel
    (P := fun lab => LargeEvenSplit p lab)
    (largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hC.1.2.2.2.2.2.2.2.1)
  exact FrameRoute.ggFrameQTwo_eq_three_of_split hp hS
    (FrameRoute.ggFrameQTwo_qTwoCompat_of_iso hn (hRig lab lab₂ _ hΛ hΛ₂ hhas hhas₂))

theorem ggQTwoD_nonempty (hWI : GGNbrInnerWeylInput) {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) :
    𝒦.Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  subst h
  have hlt := ggPhanSmall_card_lt_join hWI hcfg
  simp [ggAutomizerJoin] at hlt

theorem ggQTwoD_fix (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) :
    ∀ b : ↥Bs, (∀ φ ∈ ggAutomizerJoin L Bs 𝒦, φ b = b) → b = 1 := fun b hb =>
  FrameRoute.eq_one_of_fix_ggAutomizerJoin hTBF hWI hcfg.1
    (ggSecFiveWeylCase_of_prime_three hcfg.1.1 hcfg.2.1) hcfg.2.2.2.1
    (ggQTwoD_nonempty hWI hcfg) b hb

theorem ggQTwoD_sideCoord (hRig : GGLabelRigidInput) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L)) (hn : lab.n = 1) (hr : 4 ≤ lab.rank)
    (htag : lab.tag = .D ∨ lab.tag = .twD) :
    ∃ (n : ℕ) (τ : (Fin (n + 1) → Multiplicative (ZMod 3)) ≃* ↥Bs),
      (n = lab.rank ∧ HdRo7D.DCoordModel 3 Bs L n τ) ∨
        (n + 1 = lab.rank ∧ HdRo7C.C2CoordModel 3 Bs L n τ) := by
  have hconf : GGConfig 3 B Bs x L D J := hcfg.1.1
  obtain ⟨hp, hEA, hxBs, -, h4⟩ := hconf.tableB_facts
  have hS : LargeEvenSStar 3 B x L := hconf.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hBs : GGBstar 3 B Bs := hconf.2.1
  have hM : GGInnerDiagOn Bs L := hcfg.1.2.2.1.1
  have hC : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_elemAbelian hp hBs.2.1 (hBs.1 hS.2.1) hS.2.2.1
      hS.2.2.2.1.1 hS.2.2.2.2
  obtain ⟨n, τ, -, hmod⟩ := HdRo7D.d_sideCoord_exact HdRo7D.d_frameOmega_holds hRig hxBs rfl
    hBs hM hΛ hhas htag hn hr hx1 hC h4
  exact ⟨n, τ, hmod⟩

end CFSG.StandardType.QTwo

end
