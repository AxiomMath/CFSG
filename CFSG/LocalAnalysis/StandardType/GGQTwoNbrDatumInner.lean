module

public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrDatumDet
public import CFSG.LocalAnalysis.StandardType.GGQTwoPmWDatum
public import CFSG.LocalAnalysis.StandardType.GGQTwoWDatumTransport
public import CFSG.LocalAnalysis.StandardType.GGQTwoPosInLCells
public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112K

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

theorem GGQ2WDatum.coroot_linearIndependent_of_det {p : ℕ} [Fact p.Prime] (D : GGQ2WDatum p)
    (hdet : ((D.cartan.det : ℤ) : ZMod p) ≠ 0) : LinearIndependent (ZMod p) D.coroot := by
  rw [Fintype.linearIndependent_iff]
  intro κ hκ i
  have hmat : ((Int.castRingHom (ZMod p)).mapMatrix D.cartan).det ≠ 0 := by
    rw [← RingHom.map_det]
    exact hdet
  have h0 : ((Int.castRingHom (ZMod p)).mapMatrix D.cartan).mulVec κ = 0 := by
    funext j
    have h := congrArg (D.root j) hκ
    simp only [map_sum, map_smul, smul_eq_mul, D.pairing, map_zero] at h
    simpa [Matrix.mulVec, dotProduct, mul_comm] using h
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hmat h0) i

theorem GGQ2WDatum.pmW_of_det (D : GGQ2WDatum 3) (u : D.V)
    (hfix : ∀ v : D.V, (∀ g ∈ D.weyl, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {u})
    (hcard : 3 ≤ Fintype.card D.Λ) (hdet : ((D.cartan.det : ℤ) : ZMod 3) ≠ 0)
    {n : ℕ} (C₀ : Matrix (Fin n) (Fin n) ℤ) (e : Fin n ≃ D.Λ)
    (hC : ∀ i j, D.cartan (e i) (e j) = C₀ i j) (hW : GGQ2WeylInner n C₀)
    (T : D.V ≃ₗ[ZMod 3] D.V)
    (hT : T ∈ Subgroup.normalizer (D.weyl : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    ∃ w ∈ D.weyl, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧
      ∀ v : D.V, T (w v) - ε • v ∈ Submodule.span (ZMod 3) {u} :=
  D.pmW_of_inner u hfix hcard T
    (D.inner_of_transport C₀ e hC (D.coroot_linearIndependent_of_det hdet) hW T hT)

theorem ggQ2_gammaNbr_of_innerDatum (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hI1 : GGQTwoI1 Bs D J) [Fact p.Prime] {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (N : GGQ2NbrDatum p Bs K) (hdet : ((N.cartan.det : ℤ) : ZMod p) ≠ 0)
    {n : ℕ} (C₀ : Matrix (Fin n) (Fin n) ℤ) (e : Fin n ≃ N.Λ)
    (hC : ∀ i j, N.cartan (e i) (e j) = C₀ i j) (hW : GGQ2WeylInner n C₀)
    {u : ↥Bs} (hu : Subgroup.zpowers (u : G) = Subgroup.zpowers y) :
    GGGammaAt p B Bs x L D J u := by
  subst hp
  exact ggQ2_gammaNbr_of_datumPM hLB hP h5 hS rfl hI1 hnb N
    (fun u₀ _ hfix hdim h4 _ T hT =>
      N.toWDatum.pmW_of_det u₀ hfix (by omega) hdet C₀ e hC hW T hT) hu

@[expose] def GGQ2SelInner : GGQ2PosSel := fun _ _ _ p _ Bs _ _ K =>
  ∃ N : GGQ2NbrDatum p Bs K, ((N.cartan.det : ℤ) : ZMod p) ≠ 0 ∧
    ∃ (n : ℕ) (C₀ : Matrix (Fin n) (Fin n) ℤ) (e : Fin n ≃ N.Λ),
      (∀ i j, N.cartan (e i) (e j) = C₀ i j) ∧ (p = 3 → GGQ2WeylInner n C₀)

@[expose] def GGQ2GammaNbrPosNotInLOn (S : GGQ2PosSel) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∉ L → ∀ [Fact p.Prime]
    {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
    ¬ (GGQTwoTwoNodeRowAt p L J ∨ GGQTwoTwoNodeRowAt p K J) →
    (∀ M : GGQTwoModel p Bs x y D L J K, ¬ ∃! c, c ≠ M.b ∧ M.cartan M.b c ≠ 0) →
    S G p Bs y J K →
    ∀ {u : ↥Bs}, Subgroup.zpowers (u : G) = Subgroup.zpowers y → GGGammaAt p B Bs x L D J u

theorem ggQ2_posNbr_innerCell (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) : GGQ2GammaNbrPosNotInLOn GGQ2SelInner := by
  intro G _ _ p B Bs x L D J hS hp hI _ _ y K hnb _ _ hsel u hu
  obtain ⟨N, hdet, n, C₀, e, hC, hW⟩ := hsel
  exact ggQ2_gammaNbr_of_innerDatum hLB hP h5 hS hp hI hnb N hdet C₀ e hC (hW hp) hu

end CFSG.StandardType

end
