module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitTableP
public import CFSG.LocalAnalysis.StandardType.GGOrthFrameCore
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigO
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigS7

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {G : Type} [Group G] [Finite G]


variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ}
  {e' : Fin m ≃ ι} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
  {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} {βL : Additive ↥Bs ≃+ DVec m} {ω : F0ˣ}
  {a b c : Fin m} {α : MulAut ↥Bs} {g : G} {b' : ↥Bs}

theorem qtwoDB26_case_symplectic
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (hm : 7 ≤ m)
    (hbase : QTwoUnitBase p B Bs x L ψ ε) (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω)
    (hdel : QTwoUnitDel Bs βL a b c α g b') (hb'B : (b' : G) ∈ B) {N : Subgroup G}
    (hN : LargeEvenPComponent 3 (Subgroup.centralizer ({(b' : G)} : Set G)) N)
    (hJ₁ : qtwoDelJ ψ c ≤ N) (hJ₂ : (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ N)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hlab : GGHasLabel lab (↥N ⧸ Subgroup.center ↥N))
    (hC : lab = ⟨.C, m - 1, 1⟩) :
    ∃ Y : Subgroup G, qtwoDelJ ψ c ≤ Y ∧ (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ Y ∧
      ∃ Φ : OrthTorus.OrthFrameCore 3 Bs Y, Nat.card Φ.F = 2 ∧ Φ.r = m - 1 ∧
        Subgroup.center ↥Y = ⊥ :=
  qtwoDB44_case_symplectic hcfg hm hbase hcoords hdel hb'B hN hJ₁ hJ₂ hΛ hlab hC

theorem qtwoDB26_case_plus
    (hRig : GGLabelRigidInput)
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (hm : 7 ≤ m)
    (hbase : QTwoUnitBase p B Bs x L ψ ε) (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω)
    (hdel : QTwoUnitDel Bs βL a b c α g b') (hb'B : (b' : G) ∈ B) {N : Subgroup G}
    (hN : LargeEvenPComponent 3 (Subgroup.centralizer ({(b' : G)} : Set G)) N)
    (hJ₁ : qtwoDelJ ψ c ≤ N) (hJ₂ : (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ N)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hlab : GGHasLabel lab (↥N ⧸ Subgroup.center ↥N))
    (hD : Even (m - 1) ∧ lab = ⟨.D, m, 1⟩) :
    ∃ Y : Subgroup G, qtwoDelJ ψ c ≤ Y ∧ (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ Y ∧
      ∃ Φ : OrthTorus.OrthFrameCore 3 Bs Y, Nat.card Φ.F = 2 ∧ Φ.r = m - 1 ∧
        Subgroup.center ↥Y = ⊥ := by
  refine qtwoDB43_case_orth_big hRig hm hcfg hbase hcoords hdel hb'B hN hJ₁ hJ₂ hΛ hlab
    (Or.inl ⟨?_, hD.2⟩)
  obtain ⟨k, hk⟩ := hD.1
  exact ⟨k, by omega⟩

theorem qtwoDB26_case_minus
    (hRig : GGLabelRigidInput)
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (hm : 7 ≤ m)
    (hbase : QTwoUnitBase p B Bs x L ψ ε) (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω)
    (hdel : QTwoUnitDel Bs βL a b c α g b') (hb'B : (b' : G) ∈ B) {N : Subgroup G}
    (hN : LargeEvenPComponent 3 (Subgroup.centralizer ({(b' : G)} : Set G)) N)
    (hJ₁ : qtwoDelJ ψ c ≤ N) (hJ₂ : (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ N)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hlab : GGHasLabel lab (↥N ⧸ Subgroup.center ↥N))
    (hD : Odd (m - 1) ∧ lab = ⟨.twD, m, 1⟩) :
    ∃ Y : Subgroup G, qtwoDelJ ψ c ≤ Y ∧ (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ Y ∧
      ∃ Φ : OrthTorus.OrthFrameCore 3 Bs Y, Nat.card Φ.F = 2 ∧ Φ.r = m - 1 ∧
        Subgroup.center ↥Y = ⊥ := by
  refine qtwoDB43_case_orth_big hRig hm hcfg hbase hcoords hdel hb'B hN hJ₁ hJ₂ hΛ hlab
    (Or.inr ⟨?_, hD.2⟩)
  obtain ⟨k, hk⟩ := hD.1
  exact ⟨k + 1, by omega⟩

theorem ggQTwoDUnit_orthY_big
    (hRig : GGLabelRigidInput) (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (hm : 7 ≤ m)
    (hbase : QTwoUnitBase p B Bs x L ψ ε) (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω)
    (hdel : QTwoUnitDel Bs βL a b c α g b') (hb'B : (b' : G) ∈ B) {N : Subgroup G}
    (hN : LargeEvenPComponent 3 (Subgroup.centralizer ({(b' : G)} : Set G)) N)
    (hJ₁ : qtwoDelJ ψ c ≤ N) (hJ₂ : (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ N)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hlab : GGHasLabel lab (↥N ⧸ Subgroup.center ↥N))
    (hC : lab = ⟨.C, m - 1, 1⟩ ∨ (Even (m - 1) ∧ lab = ⟨.D, m, 1⟩) ∨
      (Odd (m - 1) ∧ lab = ⟨.twD, m, 1⟩)) :
    ∃ Y : Subgroup G, qtwoDelJ ψ c ≤ Y ∧ (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ Y ∧
      ∃ Φ : OrthTorus.OrthFrameCore 3 Bs Y, Nat.card Φ.F = 2 ∧ Φ.r = m - 1 ∧
        Subgroup.center ↥Y = ⊥ := by
  rcases hC with hC | hD
  · exact qtwoDB26_case_symplectic hcfg hm hbase hcoords hdel hb'B hN hJ₁ hJ₂ hΛ hlab hC
  · rcases hD with hD | hD
    · exact qtwoDB26_case_plus hRig hcfg hm hbase hcoords hdel hb'B hN hJ₁ hJ₂ hΛ hlab hD
    · exact qtwoDB26_case_minus hRig hcfg hm hbase hcoords hdel hb'B hN hJ₁ hJ₂ hΛ hlab hD

end CFSG.StandardType.QTwo

end
