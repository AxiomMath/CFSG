module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
import CFSG.ClassicalInvolution.WeakCT.SpCharts
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpSp
import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagClassical
import CFSG.LocalAnalysis.StandardType.GGTBRowSignedFrameAux
import CFSG.LocalAnalysis.StandardType.GGSignedCoordFix

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (blockSL2)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock shortBlock)
open scoped MatrixGroups

theorem aPermutationFull_sup_bCoordinateBlock (p : ℕ) {n : ℕ} (hn : 2 ≤ n) (i0 : Fin n) :
    aPermutationFull n p ⊔ bCoordinateBlock n p i0 = bSignedFull n p := by
  refine le_antisymm (sup_le aPermutationFull_le_bSignedFull (bCoordinateBlock_le_bSignedFull i0))
    ((Subgroup.closure_le _).2 ?_)
  rintro r (⟨i, rfl⟩ | ⟨a, b, hab, rfl⟩)
  · by_cases hi : i = i0
    · subst hi
      have := Fin.nontrivial_iff_two_le.2 hn
      obtain ⟨j, hj⟩ := exists_ne i
      have hτ : SpCoord.permAut (p := p) (Equiv.swap j i) ∈
          aPermutationFull n p ⊔ bCoordinateBlock n p i :=
        Subgroup.mem_sup_left (Subgroup.subset_closure ⟨j, i, hj, rfl⟩)
      have hs : SpCoord.sgnAut (p := p) j ∈ aPermutationFull n p ⊔ bCoordinateBlock n p i :=
        Subgroup.mem_sup_right (Subgroup.subset_closure (Or.inl ⟨j, hj, rfl⟩))
      have h := ggSpSigned_conj_permAut_sgnAut p n (Equiv.swap j i) j
      rw [Equiv.swap_apply_left] at h
      rw [← h]
      exact mul_mem (mul_mem hτ hs) (inv_mem hτ)
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (Or.inl ⟨i, hi, rfl⟩))
  · exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨a, b, hab, rfl⟩)

theorem ggG0_eq_sup_of_bCoordinateBlock (hJ : BMaxJoinInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ}
    (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e) (hn : 2 ≤ n)
    (hRM : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (h𝒦 : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    {K : Subgroup G} (hK : K ∈ 𝒦) {i0 : Fin n}
    (hA : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0) :
    ggG0 p B x L D J = L ⊔ K := by
  refine ggG0_eq_sup_of_ggAutomizerJoin_eq hJ hR e hP hn hRM hK ?_
  apply Subgroup.map_injective (f := (MulAut.congr eta).toMonoidHom) (MulAut.congr eta).injective
  rw [h𝒦]
  simp only [ggAutomizerJoin, Finset.iSup_singleton, Subgroup.map_sup, hL, hA]
  exact aPermutationFull_sup_bCoordinateBlock p hn i0


theorem ggSecFiveData_of_spCharts {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G}
    {x : G} {L D J : Subgroup G} {r f : ℕ} (hr : 1 ≤ r) (hf : 2 ≤ f)
    (σ : SL(r + 2, GaloisField 2 f) →* G) (hσ : σ.ker ≤ Subgroup.center SL(r + 2, GaloisField 2 f))
    (κ : StatedSp (r + 1) (GaloisField 2 f) →* G) (hκ : Function.Injective κ)
    (hagree : ∀ k : Fin r, (σ.comp (blockSL2 (GaloisField 2 f) (r + 1) k.succ)).range =
      (κ.comp (shortBlock (GaloisField 2 f) (Fin.castSucc_lt_succ (i := k)).ne)).range)
    (hcross : ∀ a ∈ (σ.comp (blockSL2 (GaloisField 2 f) (r + 1) 0)).range,
      ∀ b ∈ (κ.comp (longBlock (GaloisField 2 f) (r + 1) (Fin.last r))).range, a * b = b * a)
    (hG0 : ggG0 p B x L D J = σ.range ⊔ κ.range) :
    GGSecFiveData p B x L D J := by
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hq : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨Ψ, hker, hrange⟩ := CFSG.ClassicalInvolution.WeakCT.weakCT_symplectic_even_of_charts hr
    hcard hq σ hσ κ hκ hagree hcross
  have hadm : StatedLieAdmissible .PSp (r + 2) 2 f :=
    ⟨Nat.prime_two, by omega, by omega, by simp only [ne_eq, Prod.mk.injEq]; omega⟩
  refine Or.inr (Or.inr ⟨.PSp, r + 2, f, ggSecFivePres_of_psi_PSp hadm ?_ Ψ hker
    (hrange.trans hG0.symm)⟩)
  simp only [bnRank]
  omega

theorem ggSecFiveBPermDataInput_of_sp (hC : GGSecFiveBPermSpChartInput)
    (hJ : GGSecFiveBPermSpJoinInput) (hO : GGSecFiveBPermOffSpInput) :
    GGSecFiveBPermDataInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hT1 n e hpres hn eta hjoin hL hRM hG0
  by_cases hcell : ∃ (f : ℕ) (K : Subgroup G) (i0 : Fin n),
      GGSecFiveBPermSpCell p Bs L 𝒦 n eta f K i0
  · obtain ⟨f, K, i0, hc⟩ := hcell
    have hLK := hJ G p B Bs x L D J 𝒦 hcfg hT1 n e hpres hn eta hjoin hL hRM hG0 f K i0 hc
    obtain ⟨r, rfl, σ, κ, hσ, hσL, hκ, hκK, hagree, hcross⟩ :=
      hC G p B Bs x L D J 𝒦 hcfg hT1 n e hpres hn eta hjoin hL hRM hG0 f K i0 hc
    exact ggSecFiveData_of_spCharts (by omega) hc.1 σ hσ κ hκ hagree hcross
      (by rw [hLK, hσL, hκK])
  · exact hO G p B Bs x L D J 𝒦 hcfg hT1 n e hpres hn eta hjoin hL hRM hG0 hcell

theorem ggSecFiveBPermSpJoinInput_of_bMaxJoin (hJ : BMaxJoinInput) :
    GGSecFiveBPermSpJoinInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hP hn eta h𝒦 hLeta hRM hG0 f K i0 hc
  exact ggG0_eq_sup_of_bCoordinateBlock hJ hR e hP (by omega) hRM eta h𝒦 hLeta hc.2.1 hc.2.2.2.2

end CFSG.StandardType

end
