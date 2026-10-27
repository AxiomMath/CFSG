module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpSpDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
import CFSG.ClassicalInvolution.WeakCT.SpSpCharts
import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagClassical
import CFSG.LocalAnalysis.StandardType.GGSignedCoordFix
import CFSG.LocalAnalysis.StandardType.GGSignedCoordReflGroup
import CFSG.LocalAnalysis.StandardType.GGSignedCoordSwaps
import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrType
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow
public import CFSG.LocalAnalysis.StandardType.GGForkA8NotRefl
public import CFSG.LocalAnalysis.StandardType.GGTBRowR5Defs
import CFSG.LocalAnalysis.StandardType.GGTBJOrthLeft
import CFSG.LocalAnalysis.StandardType.GGNbrBalance
import CFSG.LocalAnalysis.StandardType.GGRowKFrame

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock shortBlock)
open scoped MatrixGroups

theorem bCoordinateBlock_sup_bCoordinateBlock (p : ℕ) {n : ℕ} (hn : 3 ≤ n) {i0 j : Fin n}
    (hij : j ≠ i0) : bCoordinateBlock n p i0 ⊔ bCoordinateBlock n p j = bSignedFull n p := by
  refine le_antisymm
    (sup_le (bCoordinateBlock_le_bSignedFull i0) (bCoordinateBlock_le_bSignedFull j))
    ((Subgroup.closure_le _).2 ?_)
  have hmem : SpCoord.permAut (p := p) (Equiv.swap i0 j) ∈
      bCoordinateBlock n p i0 ⊔ bCoordinateBlock n p j := by
    obtain ⟨c, hc0, hcj⟩ := SpCoord.coord_exists_ne_ne hn i0 j
    have e : Equiv.swap c i0 * Equiv.swap j c * Equiv.swap c i0 = Equiv.swap i0 j :=
      Equiv.swap_mul_swap_mul_swap (Ne.symm hcj) hij
    have h1 : SpCoord.permAut (p := p) (Equiv.swap c i0) ∈
        bCoordinateBlock n p i0 ⊔ bCoordinateBlock n p j :=
      Subgroup.mem_sup_right
        (Subgroup.subset_closure (Or.inr ⟨c, i0, hc0, hcj, Ne.symm hij, rfl⟩))
    have h2 : SpCoord.permAut (p := p) (Equiv.swap j c) ∈
        bCoordinateBlock n p i0 ⊔ bCoordinateBlock n p j :=
      Subgroup.mem_sup_left
        (Subgroup.subset_closure (Or.inr ⟨j, c, Ne.symm hcj, hij, hc0, rfl⟩))
    have hmul : SpCoord.permAut (p := p) (Equiv.swap i0 j) =
        SpCoord.permAut (Equiv.swap c i0) * SpCoord.permAut (Equiv.swap j c) *
          SpCoord.permAut (Equiv.swap c i0) := by
      rw [← e]
      exact MulEquiv.ext fun _ => rfl
    rw [hmul]
    exact mul_mem (mul_mem h1 h2) h1
  rintro r (⟨i, rfl⟩ | ⟨a, b, hab, rfl⟩)
  · by_cases hi : i = i0
    · subst hi
      exact Subgroup.mem_sup_right (Subgroup.subset_closure (Or.inl ⟨i, Ne.symm hij, rfl⟩))
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (Or.inl ⟨i, hi, rfl⟩))
  · by_cases h0 : a ≠ i0 ∧ b ≠ i0
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (Or.inr ⟨a, b, hab, h0.1, h0.2, rfl⟩))
    by_cases h1 : a ≠ j ∧ b ≠ j
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (Or.inr ⟨a, b, hab, h1.1, h1.2, rfl⟩))
    have hswap : Equiv.swap a b = Equiv.swap i0 j := by
      push Not at h0 h1
      by_cases ha : a = i0
      · subst ha
        rw [h1 (Ne.symm hij)]
      · have hb : b = i0 := h0 ha
        have ha' : a = j := by
          by_contra ha'
          exact hij ((h1 ha').symm.trans hb)
        rw [ha', hb, Equiv.swap_comm]
    rw [hswap]
    exact hmem

theorem ggAutomizer_eq_bCoordinateBlock_of_common_sgn {G : Type} [Group G] {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {Bs J K : Subgroup G} (hJK : J ≤ K)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (j : Fin n)
    (hK : IsSignedBlockOn n p (Finset.univ.erase j)
      ((ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom)) {i : Fin n}
    (hJ : SpCoord.sgnAut i ∈ (ggAutomizer J Bs).map (MulAut.congr eta).toMonoidHom) :
    (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j := by
  have hle : (ggAutomizer J Bs).map (MulAut.congr eta).toMonoidHom ≤
      (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom :=
    Subgroup.map_mono (ggAutomizer_mono Bs hJK)
  rcases hK.le_coordProdStab_or with hprod | ⟨hblock, -⟩
  · exact absurd (hprod (hle hJ)) (sgnAut_not_mem_coordProdStab hp hp2 i)
  · rw [hblock, bBlockOn_univ_erase]

theorem ggG0_eq_sup_of_ggAutomizerJoin_eq (hJ : BMaxJoinInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ}
    (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e) (hn : 2 ≤ n)
    (hRM : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    {K : Subgroup G} (hK : K ∈ 𝒦) (hEq : ggAutomizerJoin L Bs {K} = ggAutomizerJoin L Bs 𝒦) :
    ggG0 p B x L D J = L ⊔ K := by
  have hR' : GGSecFiveRouteCfg p B Bs x L D J {K} := by
    refine ⟨hR.1, hR.2.1, hR.2.2.1, ⟨by simp, fun K' hK' => ?_⟩, ?_, fun 𝒦' h1 h2 => ?_⟩
    · rw [Finset.mem_singleton.1 hK']
      exact hR.2.2.2.1.2 K hK
    · rw [hEq]
      exact hR.2.2.2.2.1
    · rw [hEq]
      exact hR.2.2.2.2.2 𝒦' h1 h2
  have hM : GGIsWeylMatrixB (CoxeterMatrix.B n) :=
    ⟨n, Equiv.refl _, by omega, CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)⟩
  obtain ⟨e', hP'⟩ : ∃ e' : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs {K}),
      GGCoxeterPres p (ggAutomizerJoin L Bs {K}) (CoxeterMatrix.B n) e' := by
    rw [hEq]
    exact ⟨e, hP⟩
  have h := hJ G p B Bs x L D J {K} hR' (Fin n) (CoxeterMatrix.B n) e' hP' hM fun y K' hK' => by
    rw [hEq]
    exact hRM y K' hK'
  simpa only [Finset.iSup_singleton] using h

theorem ggG0_eq_sup_of_bCoordinateBlocks (hJ : BMaxJoinInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ}
    (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e) (hn : 3 ≤ n)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {i0 : Fin n}
    (h𝒦 : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hLeta : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (hRM : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    {K : Subgroup G} (hK : K ∈ 𝒦) {j : Fin n} (hj : j ≠ i0)
    (hKeta : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j) :
    ggG0 p B x L D J = L ⊔ K := by
  refine ggG0_eq_sup_of_ggAutomizerJoin_eq hJ hR e hP (by omega) hRM hK ?_
  apply Subgroup.map_injective (f := (MulAut.congr eta).toMonoidHom) (MulAut.congr eta).injective
  rw [h𝒦]
  simp only [ggAutomizerJoin, Finset.iSup_singleton, Subgroup.map_sup, hLeta, hKeta]
  exact bCoordinateBlock_sup_bCoordinateBlock p hn hj

theorem GGSecFiveBCoordBSpSpCell.ggG0_eq (hJ : BMaxJoinInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ}
    (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {i0 : Fin n}
    (h𝒦 : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hLeta : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (hRM : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    {f : ℕ} {K : Subgroup G} (hc : GGSecFiveBCoordBSpSpCell p Bs L 𝒦 n eta f K i0) :
    ggG0 p B x L D J = L ⊔ K := by
  obtain ⟨-, hn, hK, -, -, j, hj, hKeta⟩ := hc
  exact ggG0_eq_sup_of_bCoordinateBlocks hJ hR e hP (by omega) h𝒦 hLeta hRM hK hj hKeta

section Split

theorem ggSecFiveData_of_spSpCharts {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G}
    {x : G} {L D J : Subgroup G} {s f : ℕ} (hs : 1 ≤ s) (hf : 2 ≤ f)
    (κ₁ κ₂ : StatedSp (s + 2) (GaloisField 2 f) →* G) (hκ₁ : Function.Injective κ₁)
    (hκ₂ : Function.Injective κ₂)
    (hagree : ∀ k : Fin s,
      (κ₁.comp (shortBlock (GaloisField 2 f) (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
        (κ₂.comp (shortBlock (GaloisField 2 f)
          (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range)
    (hlong : (κ₁.comp (longBlock (GaloisField 2 f) (s + 2) (Fin.last (s + 1)))).range =
      (κ₂.comp (longBlock (GaloisField 2 f) (s + 2) (Fin.last s).castSucc)).range)
    (hcross₁ : ∀ a ∈ (κ₁.comp (shortBlock (GaloisField 2 f)
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₂.comp (shortBlock (GaloisField 2 f)
        (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range, a * b = b * a)
    (hcross₂ : ∀ a ∈ (κ₁.comp (shortBlock (GaloisField 2 f)
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₂.comp (longBlock (GaloisField 2 f) (s + 2) (Fin.last (s + 1)))).range,
        a * b = b * a)
    (hG0 : ggG0 p B x L D J = κ₁.range ⊔ κ₂.range) :
    GGSecFiveData p B x L D J := by
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hq : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨Ψ, hker, hrange⟩ :=
    CFSG.ClassicalInvolution.WeakCT.weakCT_symplectic_even_of_spSpCharts hs hcard hq κ₁ κ₂ hκ₁
      hκ₂ hagree hlong hcross₁ hcross₂
  have hadm : StatedLieAdmissible .PSp (s + 3) 2 f :=
    ⟨Nat.prime_two, by omega, by omega, by simp only [ne_eq, Prod.mk.injEq]; omega⟩
  refine Or.inr (Or.inr ⟨.PSp, s + 3, f, ggSecFivePres_of_psi_PSp hadm ?_ Ψ hker
    (hrange.trans hG0.symm)⟩)
  simp only [bnRank]
  omega

theorem ggSecFiveBCoordBOffSpInput_of_spSp (hC : GGSecFiveBCoordBSpSpChartInput)
    (hO : GGSecFiveBCoordBOffSpSpInput) (hJ : BMaxJoinInput) : GGSecFiveBCoordBOffSpInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL hLab hB hRM hG0 hdense
  by_cases hcell : ∃ (f : ℕ) (K : Subgroup G), GGSecFiveBCoordBSpSpCell p Bs L 𝒦 n eta f K i0
  · obtain ⟨f, K, hc⟩ := hcell
    have hLK := hc.ggG0_eq hJ hR e hP h𝒦 hL hRM
    have hn5 := hc.2.1
    obtain ⟨s, rfl, κ₁, κ₂, hκ₁, hκ₁L, hκ₂, hκ₂K, hagree, hlong, hcross₁, hcross₂⟩ :=
      hC G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL hLab hB hRM hG0 f K hc
    exact ggSecFiveData_of_spSpCharts (by omega) hc.1 κ₁ κ₂ hκ₁ hκ₂ hagree hlong hcross₁ hcross₂
      (by rw [hLK, hκ₁L, hκ₂K])
  · exact hO G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL hLab hB hRM hG0 hdense hcell

end Split

end CFSG.StandardType

end
