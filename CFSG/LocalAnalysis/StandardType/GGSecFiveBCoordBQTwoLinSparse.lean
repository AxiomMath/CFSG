module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBOffQTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrType
import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrAxis
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpSp
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylNS
import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.Open.StatedAPI

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank

theorem GGSecFiveRouteCfg.leviCase_of_bCoordinateBlock_psl {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {n m : ℕ} (hn : 3 ≤ n) (hm : 5 ≤ m)
    (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) {i0 j : Fin n} (hj : j ≠ i0)
    (h𝒦 : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n 3)
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0)
    (hLm : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL (m + 1) 2 1) {K : Subgroup G}
    (hK𝒦 : K ∈ 𝒦) (hKm : StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) .PSL (m + 1) 2 1)
    (hK : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 j) :
    GGSecFiveLeviCase 3 B Bs x L D J := by
  obtain ⟨y, hy⟩ := hR.2.2.2.1.2 K hK𝒦
  have hsup : ggAutomizer L Bs ⊔ ggAutomizer K Bs = ggAutomizerJoin L Bs 𝒦 := by
    apply Subgroup.map_injective (f := (MulAut.congr eta).toMonoidHom) (MulAut.congr eta).injective
    rw [Subgroup.map_sup, hL, hK, h𝒦, bCoordinateBlock_sup_bCoordinateBlock 3 hn hj]
  exact Or.inr (Or.inl ⟨m, y, K, hLm, rfl, hm, ggScalarsPmOne_of_prime_three hR.1.1 rfl, hy, hKm,
    n, e.trans (MulEquiv.subgroupCongr hsup.symm), fun i => hP.2 i⟩)

theorem GGSecFiveRouteCfg.false_of_qTwoLin_sparse {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ} (hn : 4 ≤ n)
    (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {i0 j : Fin n} (hj : j ≠ i0)
    (h𝒦 : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧
      (lab.n = 1 ∧ lab.tag = .A)) p Bs L)
    {K : Subgroup G} (hK𝒦 : K ∈ 𝒦)
    (eLK : (↥L ⧸ Subgroup.center ↥L) ≃* (↥K ⧸ Subgroup.center ↥K))
    (hK : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j) :
    False := by
  obtain ⟨lab, hΛ, hlab, _, _, _, _, _, ⟨hBL, hk1, ht⟩, -⟩ := largeEvenMarking_exists_hasLabel hLab
  obtain ⟨t, r, k⟩ := lab
  obtain rfl : k = 1 := hk1
  obtain rfl : t = .A := ht
  obtain ⟨hr, hp3⟩ : (r = 2 * n - 3 ∨ r = 2 * n - 2) ∧ p = 3 := by
    rcases hBL with ⟨htw, -⟩ | ⟨htw, -⟩ | ⟨htw, -⟩ | ⟨-, hr, -, h3⟩
    · simp at htw
    · simp at htw
    · simp at htw
    · exact ⟨hr, h3⟩
  subst hp3
  have hLm := statedClassicalModel_of_hasLabel_typeA hΛ hlab
  have hKm := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eLK hLm
  have hr5 : 5 ≤ r := by rcases hr with rfl | rfl <;> omega
  exact hR.2.2.1
    (hR.leviCase_of_bCoordinateBlock_psl (by omega) hr5 e hP eta hj h𝒦 hL hLm hK𝒦 hKm hK)

section Inputs


@[expose] def GGSecFiveBCoordBOffQTwoLinRestInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → 4 ≤ n →
      ∀ (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0 →
        GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧
          (lab.n = 1 ∧ lab.tag = .A)) p Bs L →
        B = Bs →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
        (¬ ∃ (f : ℕ) (K : Subgroup G), GGSecFiveBCoordBSpCell p Bs L 𝒦 n f K i0) →
        (5 ≤ n → ∀ K ∈ 𝒦, ¬ ggAutomizer K Bs ≤ ggAutomizer L Bs →
          (∃ δ ∈ bSignedFull n p, (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
            (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom) ∧
          ∀ (y : G) (hy : y ∈ Bs), GGNbr p B x D J y K → ∀ k, eta ⟨y, hy⟩ k ≠ 1) →
          GGSecFiveData p B x L D J

theorem ggSecFiveBCoordBOffQTwoLinInput_of_rest
    (hE : GGSecFiveBCoordBSparseEndpointOn fun _ _ lab => lab.n = 1 ∧ lab.tag = .A)
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hFC : GGResNbrFixCentralizesInput)
    (h : GGSecFiveBCoordBOffQTwoLinRestInput) : GGSecFiveBCoordBOffQTwoLinInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL hLab hB hRM hG0 hcell
  refine h G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL hLab hB hRM hG0 hcell ?_
  intro hn5 K hK𝒦 hKL
  have hd : ∀ (y : G) (hy : y ∈ Bs), GGNbr p B x D J y K →
      (∃ δ ∈ bSignedFull n p, (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
        (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom) ∧ ∀ k, eta ⟨y, hy⟩ k ≠ 1 := by
    intro y hy hyK
    refine (hR.nbr_axis_or_dense hX hTCJ hRig hTPn hA8 hraw hiso hFC hB (by omega) eta h𝒦 hL hyK
      (hRM y K hyK) hKL hy).resolve_left ?_
    rintro ⟨j, hj, hblk, hax⟩
    obtain ⟨hK, ⟨eLK⟩⟩ :=
      hE G p B Bs x L D J 𝒦 hR n e hP hn5 eta i0 h𝒦 hL hLab hB hRM y hy K j hK𝒦 hyK hj hax hblk
    exact hR.false_of_qTwoLin_sparse hn e hP eta hj h𝒦 hL hLab hK𝒦 eLK hK
  obtain ⟨y, hyK⟩ := hR.2.2.2.1.2 K hK𝒦
  exact ⟨(hd y (hB ▸ hyK.1.2.1) hyK).1, fun y hy hyK => (hd y hy hyK).2⟩

end Inputs

end CFSG.StandardType

end
