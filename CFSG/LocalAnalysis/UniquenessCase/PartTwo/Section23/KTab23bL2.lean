module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferLevi
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open scoped Pointwise commutatorElement

theorem nonempty_mulEquiv_statedSL_two_of_isL2 {X : Type} [Group X] {n : ℕ}
    (h : IsL2 X n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (X ≃* ↥(CFSG.Open.StatedSL 2 K)) := by
  obtain ⟨⟨-, -, -, -, -⟩, K, hField, hFinite, hK, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0) h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := n) (by
      rw [← Nat.card_eq_fintype_card]
      exact hK)
  have hZ := CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot (K := K)
  let eP : CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 K) ≃*
      ↥(CFSG.Open.StatedSL 2 K) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact ⟨K, hField, hFinite, hK, ⟨e.trans eP⟩⟩

theorem pCore_two_statedSL_eq_bot {K : Type} [Field K] [Finite K] [CharP K 2] :
    CFSG.pCore 2 ↥(CFSG.Open.StatedSL 2 K) = ⊥ := by
  have hSL : CFSG.pCore 2 (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin.pCore_two_specialLinearGroup_eq_bot_of_charTwo 2
  have hmap := CFSG.pCore_map_iso 2
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K)
  rw [hSL, Subgroup.map_bot] at hmap
  exact hmap.symm

theorem pCore_eq_bot_of_isL2 {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : IsL2 X n) : CFSG.pCore 2 X = ⊥ := by
  obtain ⟨K, hField, hFinite, hK, ⟨e⟩⟩ := nonempty_mulEquiv_statedSL_two_of_isL2 h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := n) (by
      rw [← Nat.card_eq_fintype_card]
      exact hK)
  have hStated : CFSG.pCore 2 ↥(CFSG.Open.StatedSL 2 K) = ⊥ :=
    pCore_two_statedSL_eq_bot (K := K)
  have hmap := CFSG.pCore_map_iso 2 e
  rw [hStated] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective (H := CFSG.pCore 2 X)
    (f := e.toMonoidHom) e.injective).mp hmap

theorem nonempty_bar2_top_mulEquiv_of_pCore_eq_bot {X : Type} [Group X] [Finite X]
    (h : CFSG.pCore 2 X = ⊥) : Nonempty (Bar2 (⊤ : Subgroup X) ≃* X) := by
  let eTop : ↥(⊤ : Subgroup X) ≃* X := Subgroup.topEquiv
  have hpcTop : CFSG.pCore 2 ↥(⊤ : Subgroup X) = ⊥ := by
    have hmap := CFSG.pCore_map_iso 2 eTop
    rw [h] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective (H := CFSG.pCore 2 ↥(⊤ : Subgroup X))
      (f := eTop.toMonoidHom) eTop.injective).mp hmap
  refine ⟨?_⟩
  have eQuot : (↥(⊤ : Subgroup X) ⧸ CFSG.pCore 2 ↥(⊤ : Subgroup X)) ≃*
      (X ⧸ CFSG.pCore 2 X) :=
    QuotientGroup.congr _ _ eTop (CFSG.pCore_map_iso 2 eTop)
  exact eQuot.trans
    ((QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot)

theorem Hinf_top_eq_top_of_perfect {X : Type} [Group X] [Finite X]
    (hperf : Group.IsPerfect X) : Hinf (⊤ : Subgroup X) = ⊤ := by
  have hperfTop : Group.IsPerfect (⊤ : Subgroup X) := Group.IsPerfect.top_iff.mpr hperf
  have hResTop : CFSG.perfectResidual ↥(⊤ : Subgroup X) = ⊤ := by
    refine le_antisymm le_top ?_
    have hperfTopTop : Group.IsPerfect (⊤ : Subgroup ↥(⊤ : Subgroup X)) :=
      Group.IsPerfect.top_iff.mpr hperfTop
    exact (CFSG.perfect_residual_transport
      (G := ↥(⊤ : Subgroup X)) (f := MonoidHom.id _)).2.2 ⊤ hperfTopTop
  simp only [Hinf, CFSG.inSubgroup, hResTop]
  exact Subgroup.map_top_of_surjective _
    (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)

@[expose] def L2ParabolicLeStabilizer (W : Type) [CommGroup W] [Finite W]
    (H : Subgroup (MulAut W)) (n : ℕ) : Prop :=
  IsL2 ↥H n → CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 2 n →
    letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
    letI : MulAction ↥H W := MulAction.compHom W H.subtype
    letI : MulAction ↥H (Set W) := Set.mulActionSet
    ∀ S : Sylow 2 ↥H,
      letI : MulDistribMulAction ↥S W :=
        MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
      let ℓ : Subgroup W := fixedPointSubgroup ↥S W
      let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
      ∀ Pstar : Subgroup ↥H,
        IsParabolicTwo ↥H Pstar → (S : Subgroup ↥H) ≤ Pstar →
          Pstar ≠ ⊤ → Pstar ≤ Pℓ

theorem kTab23b_L2_line (W : Type) [CommGroup W] [Finite W]
    (H : Subgroup (MulAut W)) (n : ℕ)
    (hnat : IsNaturalClassicalModule H n) (hperf : ⁅H, H⁆ = H)
    (hL2line : IsL2 ↥H n ∧ CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 2 n)
    (hPar : L2ParabolicLeStabilizer W H n) :
    letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
    letI : MulAction ↥H W := MulAction.compHom W H.subtype
    letI : MulAction ↥H (Set W) := Set.mulActionSet
    ∀ S : Sylow 2 ↥H,
      letI : MulDistribMulAction ↥S W :=
        MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
      let ℓ : Subgroup W := fixedPointSubgroup ↥S W
      let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
      ∀ Tstar : Subgroup (MulAut W),
        Tstar ≤ Subgroup.normalizer (H : Set (MulAut W)) →
        IsPGroup 2 ↥Tstar →
        (S : Subgroup ↥H).map H.subtype ≤ Tstar →
        let Good : Subgroup ↥H → Prop := fun Pstar =>
          IsParabolicTwo ↥H Pstar ∧ (S : Subgroup ↥H) ≤ Pstar ∧
          (∀ t ∈ Tstar,
            (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ∧
          ¬ Pstar ≤ Pℓ
        ∀ Pstar : Subgroup ↥H, Minimal Good Pstar →
          Pstar = ⊤ ∧ IsL2 (Bar2 (Hinf Pstar)) n := by
  have hL2 : IsL2 ↥H n := hL2line.1
  letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
  letI : MulAction ↥H W := MulAction.compHom W H.subtype
  letI : MulAction ↥H (Set W) := Set.mulActionSet
  intro S
  letI : MulDistribMulAction ↥S W :=
    MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
  let ℓ : Subgroup W := fixedPointSubgroup ↥S W
  let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
  dsimp only
  intro Tstar hTnorm hT2 hST
  let Good : Subgroup ↥H → Prop := fun Pstar =>
    IsParabolicTwo ↥H Pstar ∧ (S : Subgroup ↥H) ≤ Pstar ∧
    (∀ t ∈ Tstar,
      (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ∧
    ¬ Pstar ≤ Pℓ
  intro Pstar hmin
  have hgood : Good Pstar := hmin.1
  have htop : Pstar = ⊤ := by
    by_contra hne
    exact hgood.2.2.2 (hPar hL2 hL2line.2 S Pstar hgood.1 hgood.2.1 hne)
  refine ⟨htop, ?_⟩
  have hperfH : Group.IsPerfect ↥H := Subgroup.isPerfect_iff.mpr hperf
  have hHinf : Hinf (⊤ : Subgroup ↥H) = ⊤ := Hinf_top_eq_top_of_perfect hperfH
  have hpCore : CFSG.pCore 2 ↥H = ⊥ := pCore_eq_bot_of_isL2 hL2
  obtain ⟨eBar⟩ := nonempty_bar2_top_mulEquiv_of_pCore_eq_bot hpCore
  have hL2bar : IsL2 (Bar2 (⊤ : Subgroup ↥H)) n :=
    CFSG.Blueprint.LieModel.of_mulEquiv eBar.symm hL2
  rw [htop, hHinf]
  exact hL2bar

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
