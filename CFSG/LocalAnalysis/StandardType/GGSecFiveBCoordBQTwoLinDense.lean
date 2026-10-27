module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBQTwoLinSparse
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
import CFSG.LocalAnalysis.StandardType.GGClassicalCentralImageLabel
import CFSG.LocalAnalysis.StandardType.GGNbrBalanceBasic
import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseCoords
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseRows
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpSp
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSp
import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthKSLSchur
import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagClassical
import CFSG.LocalAnalysis.StandardType.GGSignedCoordFix

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.Universal
open scoped MatrixGroups

@[expose] def GGSecFiveBCoordBLinQTwoCell {G : Type} [Group G] (p : ℕ) (Bs L : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (n m : ℕ) (K : Subgroup G) (i0 : Fin n) : Prop :=
  p = 3 ∧ (m = 2 * n - 2 ∨ m = 2 * n - 1) ∧ K ∈ 𝒦 ∧
    (∃ ψ : SL(n, GaloisField 2 2) →* G,
      ψ.ker ≤ Subgroup.center SL(n, GaloisField 2 2) ∧ ψ.range = K) ∧
    Nonempty (↥L ≃* SL(m, ZMod 2)) ∧
    ∃ eta' : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)),
      (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta').toMonoidHom = bSignedFull n p ∧
      (ggAutomizer L Bs).map (MulAut.congr eta').toMonoidHom = bCoordinateBlock n p i0 ∧
      (ggAutomizer K Bs).map (MulAut.congr eta').toMonoidHom = aPermutationFull n p

theorem ggG0_eq_sup_of_aPermutationFull (hJ : BMaxJoinInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ}
    (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e) (hn : 2 ≤ n)
    (hRM : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (h𝒦 : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    {i0 : Fin n}
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    {K : Subgroup G} (hK : K ∈ 𝒦)
    (hA : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p) :
    ggG0 p B x L D J = L ⊔ K := by
  refine ggG0_eq_sup_of_ggAutomizerJoin_eq hJ hR e hP hn hRM hK ?_
  apply Subgroup.map_injective (f := (MulAut.congr eta).toMonoidHom) (MulAut.congr eta).injective
  rw [h𝒦]
  simp only [ggAutomizerJoin, Finset.iSup_singleton, Subgroup.map_sup, hL, hA]
  rw [sup_comm]
  exact aPermutationFull_sup_bCoordinateBlock p hn i0

theorem GGInnerDiagOnLabel.linQTwo_label {G : Type} [Group G] {p n : ℕ} {Bs L : Subgroup G}
    (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧
      (lab.n = 1 ∧ lab.tag = .A)) p Bs L) :
    p = 3 ∧ ∃ r : ℕ, (r = 2 * n - 3 ∨ r = 2 * n - 2) ∧
      GGHasLabel ⟨.A, r, 1⟩ (↥L ⧸ Subgroup.center ↥L) := by
  obtain ⟨lab, -, ⟨hrow, hn1, htag⟩, hlabL, -⟩ := hLab.exists_label_eq
  obtain ⟨t, r, k⟩ := lab
  obtain rfl : k = 1 := hn1
  obtain rfl : t = .A := htag
  rcases hrow with ⟨htw, -⟩ | ⟨htw, -⟩ | ⟨htw, -⟩ | ⟨-, hr, -, h3⟩
  · simp at htw
  · simp at htw
  · simp at htw
  · exact ⟨h3, r, hr, hlabL⟩

section Inputs


theorem ggSecFiveData_of_injective_slZModTwo {G : Type} [Group G] [Finite G] {p : ℕ}
    {B : Subgroup G} {x : G} {L D J : Subgroup G} {N : ℕ} (hN : 4 ≤ N)
    (Ψ : SL(N, ZMod 2) →* G) (hΨ : Function.Injective Ψ)
    (hrange : Ψ.range = ggG0 p B x L D J) : GGSecFiveData p B x L D J := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
  let φ : GaloisField 2 1 ≃+* ZMod 2 := (GaloisField.equivZmodP 2).toRingEquiv
  let μ : SL(M + 2, GaloisField 2 1) →* SL(M + 2, ZMod 2) :=
    Matrix.SpecialLinearGroup.map φ.toRingHom
  have hμinj : Function.Injective μ := by
    intro A A' h
    apply Subtype.ext
    ext i j
    have h' := congrArg (fun X : SL(M + 2, ZMod 2) => (X : Matrix (Fin (M + 2)) (Fin (M + 2))
      (ZMod 2)) i j) h
    exact φ.injective (by simpa [μ] using h')
  have hμsurj : Function.Surjective μ := by
    intro A
    refine ⟨Matrix.SpecialLinearGroup.map φ.symm.toRingHom A, ?_⟩
    apply Subtype.ext
    ext i j
    simp [μ]
  let Φ : SL(M + 2, GaloisField 2 1) →* G := Ψ.comp μ
  have hΦrange : Φ.range = ggG0 p B x L D J := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hμsurj, Subgroup.map_top, hrange]
  have hadm : StatedLieAdmissible .PSL (M + 2) 2 1 :=
    ⟨Nat.prime_two, le_rfl, by omega, fun h => by simp at h; omega, fun h => by simp at h⟩
  refine Or.inr (Or.inr ⟨.PSL, M + 2, 1, ggSecFivePres_of_psi_PSL hadm ?_ Φ ?_ hΦrange⟩)
  · simp only [bnRank]
    omega
  · intro k hk
    have hk' : Ψ (μ k) = Ψ (μ 1) := by
      rw [map_one, map_one]
      exact hk
    rw [hΨ.comp hμinj hk']
    exact Subgroup.one_mem _

@[expose] def GGSecFiveBCoordBDenseNbrLinQTwoLabelInput : Prop :=
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
      ∀ K : Subgroup G, GGSecFiveBCoordBDenseNbr p Bs 𝒦 n eta K →
        GGHasLabel ⟨.A, n - 1, 2⟩ (↥K ⧸ Subgroup.center ↥K)

@[expose] def GGSecFiveBCoordBLinQTwoRecInput : Prop :=
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
      ∀ (m : ℕ) (K : Subgroup G), GGSecFiveBCoordBLinQTwoCell p Bs L 𝒦 n m K i0 →
        ∃ Ψ : SL(m + 2, ZMod 2) →* G, Function.Injective Ψ ∧ Ψ.range = L ⊔ K

@[expose] def GGSecFiveBCoordBOffQTwoLinFourInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → n = 4 →
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
        (¬ ∃ K : Subgroup G, GGSecFiveBCoordBDenseNbr p Bs 𝒦 n eta K) →
          GGSecFiveData p B x L D J

end Inputs

section Rows


theorem GGSecFiveRouteCfg.exists_linQTwoCell {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ} (hn : 4 ≤ n)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {i0 : Fin n}
    (h𝒦 : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧
      (lab.n = 1 ∧ lab.tag = .A)) p Bs L)
    {K : Subgroup G} (hKd : GGSecFiveBCoordBDenseNbr p Bs 𝒦 n eta K)
    (hKl : GGHasLabel ⟨.A, n - 1, 2⟩ (↥K ⧸ Subgroup.center ↥K)) :
    ∃ m : ℕ, GGSecFiveBCoordBLinQTwoCell p Bs L 𝒦 n m K i0 := by
  obtain ⟨hp3, r, hr, hlabL⟩ := hLab.linQTwo_label
  have hq := isQuasisimple_of_largeEvenMarking hLab
  obtain ⟨-, ⟨eL⟩⟩ := ggKSL_sl_of_hasLabel hq.1 hq.2 (by omega) hlabL
  obtain ⟨eta', h1, h2, h3⟩ := GGSecFiveBCoordBDenseNbr.exists_coords h𝒦 hL hKd
  obtain ⟨y, hS, -⟩ := hR.2.2.2.1.2 K hKd.1
  obtain ⟨-, -, -, -, hKy, -⟩ := hS
  have hKperf : commutator ↥K = ⊤ :=
    (CFSG.ComponentClassification.LBalance.pComponent_perfect p _ K
      ((largeEvenPComponent_iff_lBalance p _ K).1 hKy).2).commutator_eq_top
  exact ⟨r + 1, hp3, by omega, hKd.1, exists_sl_centralImage_of_hasLabel hKperf hn le_rfl hKl,
    ⟨eL.trans (specialLinearGroupEquivStatedSL (r + 1) (ZMod 2)).symm⟩, eta', h1, h2, h3⟩

theorem ggSecFiveBCoordBOffQTwoLinRestInput_of_rec (hJ : BMaxJoinInput)
    (hK : GGSecFiveBCoordBDenseNbrLinQTwoLabelInput) (hRec : GGSecFiveBCoordBLinQTwoRecInput)
    (h4 : GGSecFiveBCoordBOffQTwoLinFourInput) : GGSecFiveBCoordBOffQTwoLinRestInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL hLab hB hRM hG0 hcell hdense
  by_cases hd : ∃ K : Subgroup G, GGSecFiveBCoordBDenseNbr p Bs 𝒦 n eta K
  · obtain ⟨K, hKd⟩ := hd
    obtain ⟨m, hc⟩ := hR.exists_linQTwoCell hn h𝒦 hL hLab hKd
      (hK G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL hLab hB hRM hG0 K hKd)
    obtain ⟨Ψ, hΨ, hrange⟩ :=
      hRec G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL hLab hB hRM hG0 m K hc
    obtain ⟨-, hm, hK𝒦, -, -, eta', h1, h2, h3⟩ := hc
    refine ggSecFiveData_of_injective_slZModTwo (N := m + 2) (by omega) Ψ hΨ ?_
    rw [hrange, ggG0_eq_sup_of_aPermutationFull hJ hR e hP (by omega) hRM eta' h1 h2 hK𝒦 h3]
  rcases Nat.lt_or_ge n 5 with h5 | h5
  · exact h4 G p B Bs x L D J 𝒦 hR hT1 n e hP (by omega) eta i0 h𝒦 hL hLab hB hRM hG0 hcell hd
  exfalso
  have hle : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer L Bs := by
    refine sup_le le_rfl (iSup₂_le fun K hK𝒦 => ?_)
    by_contra hKL
    exact hd ⟨K, hK𝒦, (hdense h5 K hK𝒦 hKL).1⟩
  obtain ⟨rfl, -⟩ := hLab.linQTwo_label
  have hmem : SpCoord.sgnAut i0 ∈ bSignedFull n 3 := Subgroup.subset_closure (Or.inl ⟨i0, rfl⟩)
  rw [← h𝒦] at hmem
  have hmem' := Subgroup.map_mono hle hmem
  rw [hL] at hmem'
  exact sgnAut_not_mem_bCoordinateBlock Nat.prime_three (by norm_num) i0 hmem'

end Rows

end CFSG.StandardType

end
