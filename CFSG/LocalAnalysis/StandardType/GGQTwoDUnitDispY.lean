module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDispO
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDispBig
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDispU
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDispE
public import Certificates.Certificate1952

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

theorem ggQTwoDUnit_orthY
    (hTP : GGNbrTablePNbrInputI1On GGRegimeDeletedUnitary1836)
    (hRig : GGLabelRigidInput)
    (hBal : GGLBalanceInput) (hEA : GGQTwoEdgeAmbientInput)
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (hm : 7 ≤ m)
    (hM : M = (ggCoxeterMatrixD m).reindex e') (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) (hdel : QTwoUnitDel Bs βL a b c α g b')
    (hb'B : (b' : G) ∈ B) :
    ∃ Y : Subgroup G, qtwoDelJ ψ c ≤ Y ∧ (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ Y ∧
      ∃ Φ : OrthTorus.OrthFrameCore 3 Bs Y, Nat.card Φ.F = 2 ∧ Φ.r = m - 1 ∧
        Subgroup.center ↥Y = ⊥ := by
  obtain ⟨N, hN, hJ₁, hJ₂⟩ :=
    ggQTwoDUnit_exists_N hBal hEA hcfg hm hM hbase hcoords hdel hb'B
  obtain ⟨lab, hΛ, hlab, hcand⟩ :=
    ggQTwoDUnit_candidate hTP hRig hcfg hm hbase hcoords hdel hb'B hN hJ₁ hJ₂
  unfold QTwoDeletedUnitaryCandidate at hcand
  rcases hcand with h | ⟨h, h3⟩ | h | hD | hE | ⟨h6, h⟩ | ⟨h7, h⟩ | ⟨h9, h⟩
  ·
    exact (ggQTwoDUnit_not_unitary hm hbase hcoords hdel hN hJ₁ hJ₂ hlab (Or.inl h)).elim
  ·
    have h1 : (m - 1) + 1 = m := by omega
    have h2 : (m - 1) + 2 = m + 1 := by omega
    rw [h1] at h
    rw [h2] at h3
    exact (ggQTwoDUnit_not_unitary hm hbase hcoords hdel hN hJ₁ hJ₂ hlab
      (Or.inr ⟨h, h3⟩)).elim
  ·
    exact ggQTwoDUnit_orthY_big hRig hcfg hm hbase hcoords hdel hb'B hN hJ₁ hJ₂ hΛ hlab
      (Or.inl h)
  ·
    rcases hD with ⟨he, h | h⟩
    · exact ⟨N, hJ₁, hJ₂,
        ggQTwoDUnit_orthY_eq hRig hcfg hm hbase hcoords hdel hb'B hN hJ₁ hJ₂ hΛ hlab
          (Or.inl ⟨he, h⟩)⟩
    · have h1 : (m - 1) + 1 = m := by omega
      rw [h1] at h
      exact ggQTwoDUnit_orthY_big hRig hcfg hm hbase hcoords hdel hb'B hN hJ₁ hJ₂ hΛ hlab
        (Or.inr (Or.inl ⟨he, h⟩))
  ·
    rcases hE with ⟨ho, h | h⟩
    · exact ⟨N, hJ₁, hJ₂,
        ggQTwoDUnit_orthY_eq hRig hcfg hm hbase hcoords hdel hb'B hN hJ₁ hJ₂ hΛ hlab
          (Or.inr ⟨ho, h⟩)⟩
    · have h1 : (m - 1) + 1 = m := by omega
      rw [h1] at h
      exact ggQTwoDUnit_orthY_big hRig hcfg hm hbase hcoords hdel hb'B hN hJ₁ hJ₂ hΛ hlab
        (Or.inr (Or.inr ⟨ho, h⟩))
  ·
    exact (ggQTwoDUnit_not_exceptional hm hbase hcoords hdel hN hJ₁ hJ₂ hlab
      (Or.inl ⟨by omega, h⟩)).elim
  ·
    exact (ggQTwoDUnit_not_exceptional hm hbase hcoords hdel hN hJ₁ hJ₂ hlab
      (Or.inr (Or.inl ⟨by omega, h⟩))).elim
  ·
    exact (ggQTwoDUnit_not_exceptional hm hbase hcoords hdel hN hJ₁ hJ₂ hlab
      (Or.inr (Or.inr ⟨by omega, h⟩))).elim

end CFSG.StandardType.QTwo

end
