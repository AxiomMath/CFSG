module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermProperQTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermProper
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUni
import CFSG.LocalAnalysis.StandardType.GGSecFiveBProperNbr
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpSp
import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagClassical
import CFSG.LocalAnalysis.StandardType.GGQTwoSpinEndpoint
import CFSG.LocalAnalysis.StandardType.GGSignedCoordFix
import CFSG.LocalAnalysis.StandardType.GGTBRowSignedFrameAux
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpBstar

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

private theorem bBlockOn_le_bSignedFull {n p : ℕ} (I : Finset (Fin n)) :
    bBlockOn n p I ≤ bSignedFull n p := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro r (⟨i, _, rfl⟩ | ⟨a, _, b, _, hab, rfl⟩)
  · exact Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)
  · exact Subgroup.subset_closure (Or.inr ⟨a, b, hab, rfl⟩)

theorem aPermutationFull_sup_bBlockOn (p : ℕ) {n : ℕ} {I : Finset (Fin n)} (hI : I.Nonempty) :
    aPermutationFull n p ⊔ bBlockOn n p I = bSignedFull n p := by
  refine le_antisymm (sup_le aPermutationFull_le_bSignedFull (bBlockOn_le_bSignedFull I))
    ((Subgroup.closure_le _).2 ?_)
  rintro r (⟨i, rfl⟩ | ⟨a, b, hab, rfl⟩)
  · obtain ⟨j, hj⟩ := hI
    by_cases hij : i = j
    · subst hij
      exact Subgroup.mem_sup_right (Subgroup.subset_closure (Or.inl ⟨i, hj, rfl⟩))
    have hτ : SpCoord.permAut (p := p) (Equiv.swap j i) ∈
        aPermutationFull n p ⊔ bBlockOn n p I :=
      Subgroup.mem_sup_left (Subgroup.subset_closure ⟨j, i, Ne.symm hij, rfl⟩)
    have hs : SpCoord.sgnAut (p := p) j ∈ aPermutationFull n p ⊔ bBlockOn n p I :=
      Subgroup.mem_sup_right (Subgroup.subset_closure (Or.inl ⟨j, hj, rfl⟩))
    have h := ggSpSigned_conj_permAut_sgnAut p n (Equiv.swap j i) j
    rw [Equiv.swap_apply_left] at h
    rw [← h]
    exact mul_mem (mul_mem hτ hs) (inv_mem hτ)
  · exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨a, b, hab, rfl⟩)

private theorem nonempty_compl_pair {n : ℕ} (hn : 3 ≤ n) (a a' : Fin n) :
    ({a, a'} : Finset (Fin n))ᶜ.Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty, Finset.compl_eq_empty_iff] at h
  have h2 := Finset.card_le_two (a := a) (b := a')
  rw [h, Finset.card_univ, Fintype.card_fin] at h2
  omega

theorem ggG0_eq_sup_of_spPairCell (hJ : BMaxJoinInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ}
    (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e) (hn : 3 ≤ n)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    (hJoin : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hAut : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hNbr : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    {K : Subgroup G} {a a' : Fin n}
    (hC : GGSecFiveBPermProperQTwoSpPairCell p Bs L 𝒦 n eta K a a') :
    ggG0 p B x L D J = L ⊔ K := by
  refine ggG0_eq_sup_of_ggAutomizerJoin_eq hJ hR e hpres (by omega) hNbr hC.2.1 ?_
  apply Subgroup.map_injective (f := (MulAut.congr eta).toMonoidHom) (MulAut.congr eta).injective
  rw [hJoin]
  simp only [ggAutomizerJoin, Finset.iSup_singleton, Subgroup.map_sup, hAut, hC.2.2.2]
  exact aPermutationFull_sup_bBlockOn p (nonempty_compl_pair hn a a')

section Rows


theorem ggSecFiveData_of_uniCell_one (hS : GGSecFiveBPermUniQTwoSpInput)
    (hO : GGSecFiveBPermUniQTwoOmInput) (hJ : BMaxJoinInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hT : ¬ GGSecFiveTier1Region p B Bs x L D J)
    {n : ℕ} (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e) (hn : 5 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hJoin : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hAut : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hNbr : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hG0 : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K)
    (hCell : ¬ ∃ (f : ℕ) (K : Subgroup G) (i0 : Fin n),
      GGSecFiveBPermSpCell p Bs L 𝒦 n eta f K i0)
    (hZ : Line63.H5.twoCenter L = ⊥) {K : Subgroup G} {i0 : Fin n}
    (hSO : GGSecFiveBPermUniSpCell p Bs L 𝒦 n eta 1 K i0 ∨
      GGSecFiveBPermUniOmCell p Bs L 𝒦 n eta 1 K i0) :
    GGSecFiveData p B x L D J := by
  have hLK := ggG0_eq_sup_of_uniCell hJ hR e hpres (by omega) hJoin hAut hNbr hSO
  rcases hSO with hSp | hOm
  · exact hS G p B Bs x L D J 𝒦 hR hT n e hpres hn eta hJoin hAut hNbr hG0 hCell hZ K i0 hSp hLK
  rcases hO G p B Bs x L D J 𝒦 hR hT n e hpres hn eta hJoin hAut hNbr hG0 hCell hZ K i0 hOm with
    ⟨ψ, hker, hrange⟩ | ⟨ψ, hker, hrange⟩
  · exact ggSecFiveData_of_psi_POmegaPlus ⟨Nat.prime_two, le_rfl, by omega⟩
      (by rw [bnRank]; omega) ψ hker (hrange.trans hLK.symm)
  · exact ggSecFiveData_of_psi_POmegaMinus ⟨Nat.prime_two, le_rfl, by omega⟩
      (by rw [bnRank]; omega) ψ hker (hrange.trans hLK.symm)

theorem ggSecFiveData_of_spPairCell (hP : GGSecFiveBPermProperQTwoSpPairInput)
    (hJ : BMaxJoinInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hT : ¬ GGSecFiveTier1Region p B Bs x L D J) {n : ℕ}
    (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e) (hn : 7 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hJoin : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hAut : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hNbr : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hG0 : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K)
    (hCell : ¬ ∃ (f : ℕ) (K : Subgroup G) (i0 : Fin n),
      GGSecFiveBPermSpCell p Bs L 𝒦 n eta f K i0)
    {K : Subgroup G} {a a' : Fin n} (haa' : a ≠ a')
    (hroot : ∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b a = eta b a'))
    (hC : GGSecFiveBPermProperQTwoSpPairCell p Bs L 𝒦 n eta K a a') :
    GGSecFiveData p B x L D J := by
  have hLK := ggG0_eq_sup_of_spPairCell hJ hR e hpres (by omega) hJoin hAut hNbr hC
  obtain ⟨ψ, hker, hrange⟩ :=
    hP G p B Bs x L D J 𝒦 hR hT n e hpres hn eta hJoin hAut hNbr hG0 hCell K a a' haa' hroot hC hLK
  have hadm : StatedLieAdmissible .PSp n 2 1 := ⟨Nat.prime_two, le_rfl, by omega, fun h => by
    have h1 : n = 2 := congrArg Prod.fst h
    omega⟩
  exact Or.inr (Or.inr ⟨.PSp, n, 1, ggSecFivePres_of_psi_PSp hadm (by simp only [bnRank]; omega)
    ψ hker (hrange.trans hLK.symm)⟩)

theorem ggSecFiveBPermProperQTwoInput_of_rows (hN : GGSecFiveBPermProperQTwoNbrInput)
    (hS : GGSecFiveBPermUniQTwoSpInput) (hO : GGSecFiveBPermUniQTwoOmInput)
    (hP : GGSecFiveBPermProperQTwoSpPairInput) (hJ : BMaxJoinInput) :
    GGSecFiveBPermProperQTwoInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT n e hpres hn eta hJoin hAut hNbr hG0 hCell hB hU
  rcases hN G p B Bs x L D J 𝒦 hR hT n e hpres hn eta hJoin hAut hNbr hG0 hCell hB hU with
    ⟨K, i0, hSO⟩ | ⟨hn7, K, a, a', haa', hroot, hC⟩
  · have hz : Line63.H5.twoCenter L = ⊥ := hR.1.1.twoCenter_eq_bot_of_B_lt_Bs
      (lt_of_le_of_ne hR.1.1.2.1.1 hB) hR.1.2.2.1.1.le_normalizer
    exact ggSecFiveData_of_uniCell_one hS hO hJ hR hT e hpres (hR.1.1.five_le_of_ne hB eta) eta
      hJoin hAut hNbr hG0 hCell hz hSO
  · exact ggSecFiveData_of_spPairCell hP hJ hR hT e hpres hn7 eta hJoin hAut hNbr hG0 hCell haa'
      hroot hC

theorem ggSecFiveBPermOffSpProperInput_of_allRows (hN : GGSecFiveBPermProperNbrInput)
    (hS : GGSecFiveBPermUniSpChartInput) (hO : GGSecFiveBPermUniOmInput)
    (hN2 : GGSecFiveBPermProperQTwoNbrInput) (hS2 : GGSecFiveBPermUniQTwoSpInput)
    (hO2 : GGSecFiveBPermUniQTwoOmInput) (hP2 : GGSecFiveBPermProperQTwoSpPairInput)
    (hJ : BMaxJoinInput) : GGSecFiveBPermOffSpProperInput :=
  ggSecFiveBPermOffSpProperInput_of_rows hN hS hO
    (ggSecFiveBPermProperQTwoInput_of_rows hN2 hS2 hO2 hP2 hJ) hJ

end Rows

end CFSG.StandardType

end
