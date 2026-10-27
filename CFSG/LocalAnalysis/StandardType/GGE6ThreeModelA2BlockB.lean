module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeA2BlockTwoCore

public noncomputable section

namespace CFSG.StandardType.E6ThreeModel

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.StandardType.TableBExc.E6Three CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE
  CFSG.RankThree.E6 CFSG.RankThree.CentralCover
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three CFSG.Quasithin.F134.LieOdd
  CFSG.HardMathSupport.Lang.E6Descent CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three
open scoped MatrixGroups
open Matrix


@[expose] noncomputable def frobE6 {Ω : Type} [Field Ω] (Fr : Ω →+* Ω) :
    ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω :=
  Units.map (entrywiseHom Fr)

theorem blockGroup_comm_rootDiagUnit_zetaVec {Ω : Type} [Field Ω] {ζ : Ωˣ} (hζo : orderOf ζ = 3)
    (hζ : ζ ^ 3 = 1) (i : Fin 3) (v : Fin Tag.E6.rank → ZMod 3) (hv : adAct .E6 3 (gE6 i) v = v) :
    ∀ y ∈ rootSpan Tag.E6 Ω (a2Roots (a2PairE6 i).1 (a2PairE6 i).2),
      y * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) = rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * y := by
  obtain ⟨ρ, σ, hfr, h01, h12⟩ := exists_frame_a2PairE6 Ω i
  have hform := (adAct_gE6_eq_iff i v).1 hv
  have hα : rootChar (zetaVec ζ hζ v) (a2PairE6 i).1 = 1 :=
    (rootChar_zetaVec_eq_one_iff hζo hζ v _).2 hform.1
  have hβ : rootChar (zetaVec ζ hζ v) (a2PairE6 i).2 = 1 :=
    (rootChar_zetaVec_eq_one_iff hζo hζ v _).2 hform.2
  have hα' : rootChar (zetaVec ζ hζ v) (σ 0 1) = 1 := by rw [h01]; exact hα
  have hβ' : rootChar (zetaVec ζ hζ v) (σ 1 2) = 1 := by rw [h12]; exact hβ
  have h0 : σ 0 0 = 0 := by
    have h := hfr.eq_sub 0 0
    rw [sub_self] at h
    exact h
  have h1 : σ 1 0 = -σ 0 1 := by
    have h := hfr.neg 1 0
    rw [h, neg_neg]
  have h2 : σ 2 0 = -(σ 0 1 + σ 1 2) := by
    have h := hfr.add 2 1 0
    have h21 : σ 2 1 = -σ 1 2 := by
      have h := hfr.neg 2 1
      rw [h, neg_neg]
    rw [h21, h1] at h
    calc σ 2 0 = -σ 1 2 + -σ 0 1 := h.symm
      _ = -(σ 0 1 + σ 1 2) := by abel
  have hdd : (fun i => rootChar (zetaVec ζ hζ v) (σ i 0)) = 1 := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    rcases hi with rfl | rfl | rfl
    · simp only [h0, rootChar_zero, Pi.one_apply]
    · simp only [h1, rootChar_neg' (b := zetaVec ζ hζ v) (x := σ 0 1), hα', inv_one,
        Pi.one_apply]
    · simp only [h2, rootChar_neg' (b := zetaVec ζ hζ v) (x := σ 0 1 + σ 1 2), rootChar_add,
        hα', hβ', one_mul, inv_one, Pi.one_apply]
  intro y hy
  have hset : a2Roots (a2PairE6 i).1 (a2PairE6 i).2 = a2Roots (σ 0 1) (σ 1 2) := by
    rw [h01, h12]
  rw [hset] at hy
  obtain ⟨A, rfl⟩ := (rootSpan_a2Roots_eq_range hfr) ▸ hy
  have hconj := hfr.torus (zetaVec ζ hζ v) A
  rw [hdd] at hconj
  have hconj1 : conjDiag3 (1 : Fin 3 → Ωˣ) A = A := by
    apply Subtype.ext
    rw [coe_conjDiag3]
    simp [diagGL3]
  rw [hconj1] at hconj
  calc ρ A * rootDiagUnit Tag.E6 (zetaVec ζ hζ v)
      = (rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * ρ A *
          (rootDiagUnit Tag.E6 (zetaVec ζ hζ v))⁻¹) *
            rootDiagUnit Tag.E6 (zetaVec ζ hζ v) := by rw [hconj]
    _ = rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * ρ A := by group

end CFSG.StandardType.E6ThreeModel
