module

public import CFSG.LocalAnalysis.StandardType.GGQ2TableBI1Frame
public import CFSG.LocalAnalysis.StandardType.GGTBRowDSignedFrameSC
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
import CFSG.LocalAnalysis.StandardType.GGHdRo7DFrameOmega
import CFSG.LocalAnalysis.StandardType.GGHdRo7DFrameTransport
import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExc
import CFSG.LocalAnalysis.StandardType.GGKGForkOrthRow
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosWeylSys
import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallE8
import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRankDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


theorem ggOmegaPlus_recipe_frameW {m n p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hm : 4 ≤ m)
    (hme : Even m) {Q : LargeEvenRawCont} (hQ : LargeEvenRecipeOmegaPlus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaPlus m (2 ^ n) fun R _ I F => Q R I F ∧ GGCenterPrime p R ∧
      ∃ r, GGTorusLift p r R ∧ GGTorusWeylFrameW p r R I (ggCoxeterMatrixD m) ∧
        ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
          GGTorusTBGroup p r R I L' ψ A → Nat.card ↥A = p ^ m := by
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  have : CharP K 2 := LayerCC.charP_two_of_natCard hK
  have hpq' : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
  have hp2 : p ≠ 2 := SpNS.ne_two_of_dvd_card_add_one hpq'
  obtain ⟨hZ, hcp⟩ := OrthNs.center_data_omegaPlus (K := K) hp hp2 (by omega : 3 ≤ m)
  have hfin : Module.finrank K (Fin m ⊕ Fin m → K) = 2 * m := by
    rw [Module.finrank_fintype_fun_eq_card (R := K) (η := Fin m ⊕ Fin m)]
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hfrQ := HdRo7D.d_frameOmega_holds K (Fin m ⊕ Fin m → K) (TableBOrth.qPlusForm K m)
    (TableBOrth.nondegenerate_qPlusForm m) p hp hp2 hpq' m hfin hm
  have hF : GGTorusOrthFrameSC p (OrthRest.RPlus K m) m :=
    ggTorusOrthFrameSC_of_mulEquiv (OrthTorus.rPlusEquiv K (by omega)).symm hfrQ
  have hE := ggOrthEvenTorusInput_holds.1 K m p hm hp (Or.inr ⟨hme, hpq'⟩)
  have hI : LargeEvenInnSet (OrthRest.RPlus K m) ⊆
      Set.range (MulAut.conj : OrthRest.RPlus K m →* MulAut (OrthRest.RPlus K m)) :=
    fun _ h => h
  obtain ⟨hfr, hcard⟩ := ggTorusDFrameW_of_evenSignedPermEltSCOf (r := 0) hp hp2 hm hI hZ hcp
    (ggTorusEvenSignedPermEltSCOf_of_orthFrameSC hp hF hE)
  exact ⟨K, inferInstance, inferInstance, hK, hQ, hcp, 0,
    TypeA.ggTorusLift_zero (ggKGOrth_two_dvd_card_plus hm), hfr, hcard⟩

theorem ggOmegaMinus_recipe_frameW {m n p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hm : 4 ≤ m)
    (hme : Even m) {Q : LargeEvenRawCont} (hQ : LargeEvenRecipeOmegaMinus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus m (2 ^ n) fun R _ I F => Q R I F ∧ GGCenterPrime p R ∧
      ∃ r, GGTorusLift p r R ∧ GGTorusWeylFrameW p r R I (ggCoxeterMatrixD (m + 1)) ∧
        ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
          GGTorusTBGroup p r R I L' ψ A → Nat.card ↥A = p ^ (m + 1) := by
  obtain ⟨K, _, _, hK, b, c, hirr, hQ⟩ := hQ
  have : CharP K 2 := LayerCC.charP_two_of_natCard hK
  have hpq' : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
  have hp2 : p ≠ 2 := SpNS.ne_two_of_dvd_card_add_one hpq'
  obtain ⟨hZ, hcp⟩ := OrthExc.center_data_omegaMinus (K := K) hp hp2 (by omega : 3 ≤ m) hirr
  have hfin : Module.finrank K (LargeEvenMinusIdx m → K) = 2 * (m + 1) := by
    rw [Module.finrank_fintype_fun_eq_card (R := K) (η := LargeEvenMinusIdx m)]
    simp only [LargeEvenMinusIdx, Fintype.card_sum, Fintype.card_fin]
    omega
  have hfrQ := HdRo7D.d_frameOmega_holds K (LargeEvenMinusIdx m → K)
    (TableBOrth.qMinusForm K m b c) (TableBOrth.nondegenerate_qMinusForm m hirr) p hp hp2 hpq'
    (m + 1) hfin (by omega)
  have hF : GGTorusOrthFrameSC p (OrthRest.RMinus K m b c) (m + 1) :=
    ggTorusOrthFrameSC_of_mulEquiv (OrthTorus.rMinusEquiv K m b c).symm hfrQ
  have hE := ggOrthEvenTorusInput_holds.2 K m p b c hm hme hirr hp hpq'
  have hI : LargeEvenInnSet (OrthRest.RMinus K m b c) ⊆
      Set.range (MulAut.conj : OrthRest.RMinus K m b c →* MulAut (OrthRest.RMinus K m b c)) :=
    fun _ h => h
  obtain ⟨hfr, hcard⟩ := ggTorusDFrameW_of_evenSignedPermEltSCOf (r := 0) hp hp2 (by omega) hI hZ
    hcp (ggTorusEvenSignedPermEltSCOf_of_orthFrameSC hp hF hE)
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hirr, hQ, hcp, 0,
    TypeA.ggTorusLift_zero (ggKGOrth_two_dvd_card_minus (by omega : 3 ≤ m) b c hirr), hfr, hcard⟩

private theorem ggQ2_omegaPlusLabelAll {l : ℕ} (hl : 4 ≤ l) (hle : Even l) :
    LargeEvenLabelAll ⟨.D, l, 1⟩ fun R _ I _ => GGCenterPrime 3 R ∧
      ∃ r, GGTorusLift 3 r R ∧ GGTorusWeylFrameW 3 r R I (ggCoxeterMatrixD l) ∧
        ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
          GGTorusTBGroup 3 r R I L' ψ A → Nat.card ↥A = 3 ^ Fintype.card (Fin l) := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h3
  · omega
  · simpa only [Fintype.card_fin] using
      ggOmegaPlus_recipe_frameW (m := l) (n := 1) (p := 3) (by norm_num) (by norm_num) hl hle hQ

private theorem ggQ2_omegaMinusLabelAll {m : ℕ} (hm : 4 ≤ m) (hme : Even m) :
    LargeEvenLabelAll ⟨.twD, m + 1, 1⟩ fun R _ I _ => GGCenterPrime 3 R ∧
      ∃ r, GGTorusLift 3 r R ∧ GGTorusWeylFrameW 3 r R I (ggCoxeterMatrixD (m + 1)) ∧
        ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
          GGTorusTBGroup 3 r R I L' ψ A → Nat.card ↥A = 3 ^ Fintype.card (Fin (m + 1)) := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h2 h3
  · omega
  · omega
  · simpa only [Nat.add_sub_cancel, Fintype.card_fin] using
      ggOmegaMinus_recipe_frameW (m := m) (n := 1) (p := 3) (by norm_num) (by norm_num) hm hme hQ

theorem ggQ2TableBI1FailOn_omega : GGQ2TableBI1FailOn GGQ2TBOmegaLabel := by
  refine ggQ2TableBI1FailOn_of_frames ?_ ?_
  · rintro lab (h | h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  intro lab hlab hq2 hsp
  obtain ⟨t, l, n⟩ := lab
  have hn1 : 1 ≤ n := hlab.1
  have hn : n = 1 := by
    have h2 : n < 2 := hq2
    omega
  subst hn
  obtain ⟨ht, hle, hl4⟩ | ⟨ht, hlo, hl4⟩ := hsp
  · dsimp only at ht hle hl4
    subst ht
    have hW : GGQ2LabelWeyl ⟨.D, l, 1⟩ (ggCoxeterMatrixD l) := by
      simp only [GGQ2LabelWeyl]
      exact ⟨Equiv.refl _, rfl⟩
    have hAll : LargeEvenLabelAll ⟨.D, l, 1⟩ fun R _ I _ => GGCenterPrime 3 R ∧
        ∃ r, GGTorusLift 3 r R ∧ GGTorusWeylFrameW 3 r R I (ggCoxeterMatrixD l) ∧
          ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
            GGTorusTBGroup 3 r R I L' ψ A → Nat.card ↥A = 3 ^ Fintype.card (Fin l) :=
      ggQ2_omegaPlusLabelAll hl4 hle
    exact ⟨Fin l, inferInstance, inferInstance, ggCoxeterMatrixD l, CartanMatrix.D l, hW,
      CFSG.TwoNodeSmall.pws_ggIsWeylMatrix_D l hl4, ggIntCartan_D l,
      SecFiveRootRefl.entries_D l, SecFiveRootRefl.cartanTree_D l hl4,
      by rw [CartanMatrix.D_det (n := l) (by omega)]; decide,
      hAll.mono fun _ _ _ _ ⟨hcp, r, hl, hf, hc⟩ => ⟨hcp, r, r, Nat.le_succ r, hl, hf, hc⟩⟩
  · dsimp only at ht hlo hl4
    obtain ⟨k, hk⟩ := hlo
    obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
    have hm4 : 4 ≤ m := by omega
    have hme : Even m := ⟨k, by omega⟩
    subst ht
    have hW : GGQ2LabelWeyl ⟨.twD, m + 1, 1⟩ (ggCoxeterMatrixD (m + 1)) := by
      simp only [GGQ2LabelWeyl]
      exact ⟨Equiv.refl _, rfl⟩
    have hAll : LargeEvenLabelAll ⟨.twD, m + 1, 1⟩ fun R _ I _ => GGCenterPrime 3 R ∧
        ∃ r, GGTorusLift 3 r R ∧ GGTorusWeylFrameW 3 r R I (ggCoxeterMatrixD (m + 1)) ∧
          ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
            GGTorusTBGroup 3 r R I L' ψ A → Nat.card ↥A = 3 ^ Fintype.card (Fin (m + 1)) :=
      ggQ2_omegaMinusLabelAll hm4 hme
    exact ⟨Fin (m + 1), inferInstance, inferInstance, ggCoxeterMatrixD (m + 1),
      CartanMatrix.D (m + 1), hW, CFSG.TwoNodeSmall.pws_ggIsWeylMatrix_D (m + 1) (by omega),
      ggIntCartan_D (m + 1), SecFiveRootRefl.entries_D (m + 1),
      SecFiveRootRefl.cartanTree_D (m + 1) (by omega),
      by rw [CartanMatrix.D_det (n := m + 1) (by omega)]; decide,
      hAll.mono fun _ _ _ _ ⟨hcp, r, hl, hf, hc⟩ => ⟨hcp, r, r, Nat.le_succ r, hl, hf, hc⟩⟩

end CFSG.StandardType

end
