module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JPOrthB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JPBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
import CFSG.Quasithin.Vol2.Ch10SecI1CovO4
public import CFSG.Quasithin.SteinbergCBI16
import CFSG.RankThree.GF2n.Smith81.OrthE1KFSmall
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1Restrict

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.Assembly.LowTwoRank Subgroup

variable {W : Type} [CommGroup W]

theorem s16jp_cover_twistTensor
    {m : ℕ} (hm : 1 ≤ m) {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = 2 ^ (2 * m)) :
    S16C11V1ModelCover (FFModel.twistTensor m (StatedSL 2 K)) := by
  intro W _ _ hW2 H Z hZ hcomm hR
  obtain ⟨-, -, -, -, -, -, tO, -, -, -, -, -, -, -, -, -, -⟩ :=
    SteinbergCB.I16.natural_binary_module_first_cohomology.{0, 0}
  let _ := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 ^ (2 * m) := by
    rw [Fintype.card_eq_nat_card]
    exact hK
  have hcard : Nat.card Z ≤ 1 := by
    simpa using
      CFSG.Quasithin.ASInputs.C10KH.orth4Cover_card_le hm hK hW2 hZ hcomm hR (d := 0)
        fun ρ hρ => by
          have := tO hK' (by omega) hρ
          omega
  haveI : Subsingleton ↥Z := Finite.card_le_one_iff_subsingleton.mp hcard
  exact Z.eq_bot_of_subsingleton

theorem s16jp_row_O4
    [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} {m : ℕ} (hm : 1 ≤ m)
    (h : s16h_H5RowO4 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) m) :
    commSub ⊤ L ⊓ fixV L = ⊥ := by
  obtain ⟨_, hNat⟩ := h
  have hBO4 : BinaryOrthogonalFour L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) m :=
    s16jp_natOmegaMinus_binaryOrthogonalFour hm hNat
  obtain ⟨-, K, hKf, hKfin, b, c, hKcard, hirr, hReal⟩ := hNat
  rw [show 4 / 2 = 2 by norm_num] at hReal
  letI : Field K := hKf
  letI : Finite K := hKfin
  letI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hKcard
  obtain ⟨π, hπ⟩ := hReal
  letI : Group.IsPerfect
      (FFModel.nat (StatedOmega (StatedQuadMinus 2 K b c))).Gam :=
    CFSG.RankThree.GF2n.Smith81.Smith23E1.kfs_perfect_minus hirr
  have hperf : Group.IsPerfect ↥L := Group.IsPerfect.ofSurjective (f := π) hπ.1
  obtain ⟨F, hFf, hFfin, hFch, hFcard, hR⟩ := hBO4
  letI : Field F := hFf
  letI : Finite F := hFfin
  letI : CharP F 2 := hFch
  have hU : ∀ l ∈ L, ∀ u ∈ commSub ⊤ L, l u ∈ commSub ⊤ L :=
    s16jp_commSub_stable (Y := ⊤) fun l _ y _ => Subgroup.mem_top (l y)
  have hc : commSub (commSub ⊤ L) L = commSub ⊤ L :=
    s16jp_commSub_commSub hperf (Y := ⊤) fun l _ y _ => Subgroup.mem_top (l y)
  have hR' : (FFModel.twistTensor m (StatedSL 2 F)).Realizes L (commSub ⊤ L)
      (fixV L ⊓ commSub ⊤ L) := by
    rw [inf_comm]
    exact hR
  have hfix : fixV L ⊓ commSub ⊤ L = ⊥ :=
    s16c11_v1_cover_restrict (s16jp_cover_twistTensor hm hFcard) hW2 hU hc hR'
  rwa [inf_comm]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
