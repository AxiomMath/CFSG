module

public import CFSG.LocalAnalysis.StandardType.GGKGForkRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkLattice
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorus
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpModel
public import CFSG.ClassicalGroups.Symplectic.StandardForm
public import CFSG.ClassicalGroups.Alternating.PointRadicalFixedCard

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableBSymp
open CFSG.ClassicalGroups.Alternating CFSG.ClassicalGroups.Symplectic

theorem ggKGSp_two_dvd_card {K : Type} [Field K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n) :
    2 ∣ Nat.card (LargeEvenProj (LargeEvenSpGroup K n)) := by
  have : NeZero n := ⟨by omega⟩
  rw [Nat.card_congr (spProjEquivSp.trans spEquiv).toEquiv]
  have hB : (spForm n K).IsAlt := spForm_isAlt
  obtain ⟨v, hv⟩ : ∃ v : Fin n ⊕ Fin n → K, v ≠ 0 :=
    ⟨Pi.single (Sum.inl ⟨0, by omega⟩) 1, fun h => one_ne_zero (Pi.single_eq_zero_iff.mp h)⟩
  obtain ⟨w, hw⟩ : ∃ w, spForm n K v w ≠ 0 := by
    by_contra h
    exact hv (spForm_nondegenerate.1 v fun w => not_not.mp fun hw => h ⟨w, hw⟩)
  have h1 : Tsp hB v 1 ≠ 1 := by
    intro h
    have h' := congrArg (fun g : Gsp (spForm n K) => g.app w) h
    simp only [Tsp_app, one_mul, Gsp.app_one, add_eq_left, smul_eq_zero] at h'
    rcases h' with h' | h'
    · exact hw (by rw [← hB.neg_eq w v, h', neg_zero])
    · exact hv h'
  have h2 : Tsp hB v 1 ^ 2 = 1 := by rw [pow_two, Tsp_mul_self]
  exact orderOf_eq_prime h2 h1 ▸ orderOf_dvd_natCard _

theorem ggKGTwoOn_spNonsplit :
    GGKGTwoOn fun p lab => (lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n + 1 := by
  intro p lab hp hlab hl hs Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := hs
  dsimp only at htag hpn
  have hn : 1 ≤ n := hlab.1
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpn
  rcases htag with rfl | rfl <;>
  · have hl2 : 2 ≤ l := hlab.2.1
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have := charP_two_of_card hK
    have : NeZero l := ⟨by omega⟩
    have hpK : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
    obtain ⟨hT, hcp⟩ := ggSpNonsplitTorusInput_holds K l p hl2 hp hpK
    exact ⟨K, inferInstance, inferInstance, hK, hQ', 0,
      TypeA.ggTorusLift_zero (ggKGSp_two_dvd_card (by omega)),
      ggTorusLattice_of_signedEltSC hp hp2 TableBSymp.sp_I_subset_inn
        TableBSymp.center_spProj_eq_bot hcp hT⟩

theorem recipeSymplectic_lattice {l n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1)
    (hl : 1 ≤ l) {Q : LargeEvenRawCont} (h : LargeEvenRecipeSymplectic l (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusLattice p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  have : NeZero l := ⟨by omega⟩
  exact ⟨K, inferInstance, inferInstance, hK, hQ, l, ggTorusLift_symplectic hp hp2 hpq hl,
    ggTorusLattice_of_signedElt hp hp2 sp_I_subset_inn center_spProj_eq_bot
      (SpModel.ggTorusSignedElt_sp hp hp2 hpq)⟩

theorem ggKGTwoOn_spSplit :
    GGKGTwoOn fun p lab => (lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1 := by
  intro p lab hp hlab hl hs Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := hs
  dsimp only at htag hpn
  have hn : 1 ≤ n := hlab.1
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  rcases htag with rfl | rfl <;>
  · have hl2 : 2 ≤ l := hlab.2.1
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact recipeSymplectic_lattice hp hp2 hpn (by omega) hQ

end CFSG.StandardType
