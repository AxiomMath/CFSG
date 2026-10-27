module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthMemberTrans
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthPaths
import CFSG.LocalAnalysis.StandardType.GGQTwoDModelMain
import CFSG.LocalAnalysis.StandardType.GGQTwoSU34Aux5

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.OrthTorus CFSG.ClassicalInvolution.Phan CFSG.Open

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs Y : Subgroup G}
  (Φ : OrthFrameCore p Bs Y)

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.BorelTits in
private theorem pmop_card_qtwoStdW {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K]
    [CharP K 2] (E : QuadExt F K (unitaryInvolution K 2 1)) (hK : Nat.card K = 4) (m : ℕ)
    (hm : 3 ≤ m) (i j : Fin (m + 1)) (h : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 3) :
    Nat.card ↥(qtwoStdW E m hm i j) = 216 := by
  have hij : i ≠ j := by
    rintro rfl
    rw [qtwoLabel_self] at h
    omega
  have hMji : CFSG.StandardType.ggCoxeterMatrixD (m + 1) j i = 3 := by
    rw [((CFSG.StandardType.ggCoxeterMatrixD (m + 1)).isSymm.apply i j)]
    exact h
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hinj := CFSG.ClassicalInvolution.PhanDn.stdFamilyV_θ_inj E hm i j hlt h
    unfold qtwoStdW
    rw [if_pos h, if_pos hlt, ← qTwoS34_card_Su_three hK]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  · have hinj := CFSG.ClassicalInvolution.PhanDn.stdFamilyV_θ_inj E hm j i hgt hMji
    unfold qtwoStdW
    rw [if_pos h, if_neg (not_lt_of_gt hgt), ← qTwoS34_card_Su_three hK]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem qtwoOrth_pair_card_core (hF : Nat.card Φ.F = 2) {ρ ρ' : MulAut ↥Bs}
    (hρ : ρ ∈ ggAutomizer Y Bs) (hρ' : ρ' ∈ ggAutomizer Y Bs) (hr : GGIsReflection p ρ)
    (hr' : GGIsReflection p ρ') (hnc : ρ * ρ' ≠ ρ' * ρ) :
    UnitaryBlockStandardPair (GaloisField 2 2) 2 1 (ggRankTwoIn Y Bs ρ ρ')
      (ggRankOneIn Y Bs ρ) (ggRankOneIn Y Bs ρ') ∧
      Nat.card ↥(ggRankTwoIn Y Bs ρ ρ') = 216 := by
  have h4 := Φ.hr
  obtain ⟨x, hx⟩ := qtwoOrth_exists_acts_core Φ hF hρ hr
  obtain ⟨y, hy⟩ := qtwoOrth_exists_acts_core Φ hF hρ' hr'
  have hxy : omPlusRefl p x * omPlusRefl p y ≠ omPlusRefl p y * omPlusRefl p x :=
    fun h => hnc ((qtwoOrth_comm_iff_core Φ hF hρ hρ' hx hy).mpr h)
  rw [qtwoOrth_rankTwoIn_core Φ hF hρ hρ' hr hr' hx hy hnc,
    qtwoOrth_rankOneIn_core Φ hF hρ hr hx,
    qtwoOrth_rankOneIn_core Φ hF hρ' hr' hy]
  obtain ⟨w, hw, hw0, hw1⟩ := omSigned_conj_pair (Fact.out : p.Prime) (by omega : 3 ≤ Φ.r) hxy
  obtain ⟨μ, hμ, hμw⟩ := qtwoOrth_realize Φ hF hw
  obtain ⟨m, hm⟩ : ∃ m, Φ.r = m + 1 := ⟨Φ.r - 1, by omega⟩
  have hm3 : 3 ≤ m := by omega
  obtain ⟨alg, E, χ, -, -, _hχQ, -, h1, h2⟩ := qtwoOrth_std_torus Φ hF m hm3 hm
  letI := alg
  have hlab : CFSG.StandardType.ggCoxeterMatrixD (m + 1)
      (Fin.cast hm (⟨0, by omega⟩ : Fin Φ.r))
      (Fin.cast hm (⟨1, by omega⟩ : Fin Φ.r)) = 3 := by
    refine (qtwoLabel_three_iff hm3 _ _).mpr (Or.inl ⟨?_, ?_⟩)
    · simp [Fin.val_cast]
    · simp only [Fin.val_cast]
      exact Nat.le_sub_one_of_lt (by omega : 1 < m)
  have hpair := qtwoStd_pair E m hm3 (Fin.cast hm (⟨0, by omega⟩ : Fin Φ.r))
    (Fin.cast hm (⟨1, by omega⟩ : Fin Φ.r)) hlab
  have hR2 : (Φ.rank2 x y).map (orthModelEquiv Φ χ μ).toMonoidHom =
      qtwoStdW E m hm3 (Fin.cast hm (⟨0, by omega⟩ : Fin Φ.r))
        (Fin.cast hm (⟨1, by omega⟩ : Fin Φ.r)) :=
    Φ.rank2_map_model χ hμ hμw hw0 hw1 (h2 (⟨0, by omega⟩ : Fin Φ.r)
      (⟨1, by omega⟩ : Fin Φ.r) hlab)
  have hR1 : (Φ.rank1 x).map (orthModelEquiv Φ χ μ).toMonoidHom =
      qtwoStdU E m hm3 (Fin.cast hm (⟨0, by omega⟩ : Fin Φ.r)) :=
    Φ.rank1_map_model χ hμ hμw hw0 (h1 (⟨0, by omega⟩ : Fin Φ.r))
  have hR1' : (Φ.rank1 y).map (orthModelEquiv Φ χ μ).toMonoidHom =
      qtwoStdU E m hm3 (Fin.cast hm (⟨1, by omega⟩ : Fin Φ.r)) :=
    Φ.rank1_map_model χ hμ hμw hw1 (h1 (⟨1, by omega⟩ : Fin Φ.r))
  refine ⟨Φ.img_standardPair (orthModelEquiv Φ χ μ) (Φ.rank2_le_orthDerived x y)
    (Φ.rank1_le_orthDerived x) (Φ.rank1_le_orthDerived y) hR2 hR1 hR1' hpair, ?_⟩
  have hcardmap : Nat.card ↥((Φ.rank2 x y).map (orthModelEquiv Φ χ μ).toMonoidHom) =
      Nat.card ↥(Φ.rank2 x y) :=
    Subgroup.card_map_of_injective (f := (orthModelEquiv Φ χ μ).toMonoidHom)
      (orthModelEquiv Φ χ μ).injective
  rw [hR2] at hcardmap
  unfold OrthFrameCore.img
  rw [Subgroup.card_map_of_injective Φ.hinj,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Φ.rank2_le_orthDerived x y)).toEquiv,
    ← hcardmap]
  exact pmop_card_qtwoStdW E natCard_galoisField_two_two m hm3 _ _ hlab

theorem qtwoOrth_standardPair (hF : Nat.card Φ.F = 2)
    (hZ : Subgroup.center ↥Y = ⊥) (hBs : IsElemAbelian p Bs) {ρ ρ' : MulAut ↥Bs}
    (hρ : ρ ∈ ggAutomizer Y Bs) (hρ' : ρ' ∈ ggAutomizer Y Bs) (hr : GGIsReflection p ρ)
    (hr' : GGIsReflection p ρ') (hnc : ρ * ρ' ≠ ρ' * ρ) :
    UnitaryBlockStandardPair (GaloisField 2 2) 2 1 (ggRankTwoIn Y Bs ρ ρ')
      (ggRankOneIn Y Bs ρ) (ggRankOneIn Y Bs ρ') :=
  (qtwoOrth_pair_card_core Φ hF hρ hρ' hr hr' hnc).1

end CFSG.StandardType.QTwo

end
