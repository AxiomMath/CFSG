module

public import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlockLift
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionNonsplitRestSU

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21 Matrix
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.RankThree.Classical (permGL)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary mem_primeFormUnitary)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

namespace SUTB

theorem card_le_sq_of_forall {G : Type*} [Group G] (H : Subgroup G) {p : ℕ} (y₁ y₂ : G)
    (hH : ∀ g ∈ H, ∃ i j : Fin p, g = y₁ ^ (i : ℕ) * y₂ ^ (j : ℕ)) : Nat.card H ≤ p ^ 2 := by
  choose i j hij using fun g : H => hH g g.2
  have hinj : Function.Injective (fun g : H => (i g, j g)) := by
    intro g g' hgg
    simp only [Prod.mk.injEq] at hgg
    exact Subtype.ext (by rw [hij g, hij g', hgg.1, hgg.2])
  calc Nat.card H ≤ Nat.card (Fin p × Fin p) := Nat.card_le_card_of_injective _ hinj
    _ = p ^ 2 := by rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin, sq]

end SUTB

section Inputs

theorem ggSUNonsplitTwoBlockInput_holds : GGSUNonsplitTwoBlockInput := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 hns
  classical
  have hF : Nat.card (GaloisField 2 (2 * (f + 1))) = (2 ^ (f + 1)) ^ 2 :=
    card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)
  have h : UnitaryFieldData 2 (f + 1) (GaloisField 2 (2 * (f + 1))) :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  have hβ := hctx.1.2.2.2.2.2.1
  have hp : p.Prime := hβ.1
  have hp2 : p ≠ 2 := hβ.2.1
  have hrank : 2 ≤ n / 2 := hctx.2.2.2.1.2
  have hn4 : 4 ≤ n := by omega
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hnq : (n, 2 ^ (f + 1)) ≠ (3, 2) := fun h' => by
    have : n = 3 := congrArg Prod.fst h'
    omega
  obtain ⟨P₀, hP₀⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hF n
  set ψ₁ := SURep.ggFrameU hF ψ P₀ hP₀ with hψ₁
  have hr₁ : ψ₁.range = ψ.range := SURep.range_ggFrameU hF ψ P₀ hP₀
  have hker₁ : ψ₁.ker ≤ Subgroup.center ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n) :=
    SURep.ker_ggFrameU_le hF ψ P₀ hP₀ hker
  have hFk₁ : SURep.GGFrameKer ψ₁ := SURep.ggFrameKer_of_ker_le_center hF (by omega) hnq hker₁
  have hC : Subgroup.centralizer (ψ₁.range : Set G) = ⊥ := by
    rw [hr₁, hrange]
    exact s1.1
  have hBsel : IsElemAbelian p Bs := hctx.2.1.2.1
  have hEB : ∀ b ∈ Bs, ∃ B', B' ∈ primeFormUnitary h (idGram (GaloisField 2 (2 * (f + 1))) n) ∧
      (b, B') ∈ SUTorus.suPairs ψ₁ := by
    intro b hb
    obtain ⟨A, hA, hAc⟩ := InnerDiagSU.suInnerDiagConj hF hn4 G ψ hker b⁻¹
      (hctx.2.2.2.2.2.2.1.2 b⁻¹ (Bs.inv_mem hb))
    refine ⟨P₀ * A * P₀⁻¹,
      SUTorus.mem_primeFormUnitary_of_isIdUnitary h (InnerDiagSU.isIdUnitary_conj hP₀ hA),
      SUTorus.mem_suPairs_transfer P₀ hP₀ (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF n)
        hA fun u => ?_⟩
    have := hAc u
    rwa [inv_inv] at this
  have hlift : ∀ b ∈ Bs, ∃ X : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n),
      X ^ p = 1 ∧ ψ₁ X = b := fun b hb => by
    obtain ⟨B', hB'U, hB'⟩ := hEB b hb
    exact SUTB.exists_lift h (by omega) hnq hp hns hker₁ hC (hBsel.2 b hb) hB'U hB'
  have hcomm : ∀ X Y : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n), X ^ p = 1 →
      ψ₁ X ∈ Bs → ψ₁ Y ∈ Bs → X * Y = Y * X := fun X Y hXp hX hY =>
    SUNS.commute_of_frame_commute h hFk₁ hp hns hXp (TableB.IsElemAbelian.comm hBsel hX hY)
  let A : Subgroup ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n) :=
    { carrier := {X | X ^ p = 1 ∧ ψ₁ X ∈ Bs}
      mul_mem' := fun {X Y} hX hY => ⟨by
        rw [(show Commute X Y from hcomm X Y hX.1 hX.2 hY.2).mul_pow, hX.1, hY.1, one_mul], by rw [map_mul]; exact Bs.mul_mem hX.2 hY.2⟩
      one_mem' := ⟨one_pow p, by rw [map_one]; exact Bs.one_mem⟩
      inv_mem' := fun {X} hX => ⟨by rw [inv_pow, hX.1, inv_one], by
        rw [map_inv]; exact Bs.inv_mem hX.2⟩ }
  have hmemA : ∀ X, X ∈ A ↔ X ^ p = 1 ∧ ψ₁ X ∈ Bs := fun X => Iff.rfl
  have hA : SUTB.MaxElemAb p A :=
    { prime := hp
      ne_two := hp2
      not_dvd := hns
      pow := fun a ha => ((hmemA a).mp ha).1
      comm := fun a ha b hb => hcomm a b ((hmemA a).mp ha).1 ((hmemA a).mp ha).2
        ((hmemA b).mp hb).2
      max := fun g hgp hga => by
        refine (hmemA g).mpr ⟨hgp, hctx.2.1.2.2.2 (ψ₁ g) ?_ (by rw [← map_pow, hgp, map_one])⟩
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        obtain ⟨X, hXp, rfl⟩ := hlift b hb
        rw [← map_mul, ← map_mul, hga X ((hmemA X).mpr ⟨hXp, hb⟩)] }
  have hcard : p ^ 4 ≤ Nat.card A := by
    have hm4 : 4 ≤ LargeEvenTwoLocalRank p G := hβ.2.2.2
    have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.1.2.2.2.2.2.2.1.1.2.1
    have hBle : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hctx.2.1.1
    have hsurj : Function.Surjective (fun X : A => (⟨ψ₁ X, ((hmemA X).mp X.2).2⟩ : Bs)) := by
      intro b
      obtain ⟨X, hXp, hXb⟩ := hlift b b.2
      exact ⟨⟨X, (hmemA X).mpr ⟨hXp, hXb ▸ b.2⟩⟩, Subtype.ext hXb⟩
    calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hp.pos hm4
      _ = Nat.card B := hBcard.symm
      _ ≤ Nat.card Bs := hBle
      _ ≤ Nat.card A := Nat.card_le_card_of_surjective _ hsurj
  obtain ⟨Q, d, xx, a₁, a₂, hQ, hxx, ha₁, ha₂, hd2, hd4, hcomm', hblock, hfix, hfixr, hgen⟩ :=
    SUTB.exists_twoBlock_frame h hA hcard
  have hQi : ((Q⁻¹ : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) :
      Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) =
      ((Q : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))).map h.bar)ᵀ := by
    have h1 : ((Q⁻¹ : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) :
        Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) * Q = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc ((Q⁻¹ : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) :
          Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) =
        ((Q⁻¹ : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) :
          Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
          (Q * ((Q : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))).map h.bar)ᵀ) := by
          rw [mul_eq_one_comm.mp hQ, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hQQ : conjTr (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1))
      (((Q⁻¹ : GL (Fin n) (GaloisField 2 (2 * (f + 1))))) :
        Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
      (((Q⁻¹ : GL (Fin n) (GaloisField 2 (2 * (f + 1))))) :
        Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) = 1 := by
    rw [SURep.conjTr_eq_bar h, hQi]
    have hbb : ((((Q : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))).map h.bar)ᵀ).map
        h.bar)ᵀ = (Q : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) := by
      ext i j
      simp [UnitaryFieldData.bar_bar]
    rw [hbb]
    exact mul_eq_one_comm.mp hQ
  have hP : conjTr (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1))
      (((Q⁻¹ * P₀ : GL (Fin n) (GaloisField 2 (2 * (f + 1))))) :
        Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
      (((Q⁻¹ * P₀ : GL (Fin n) (GaloisField 2 (2 * (f + 1))))) :
        Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) = antidiag n := by
    rw [Units.val_mul, CFSG.LieType.Universal.Unitary.conjTr_mul]
    calc conjTr (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1))
          (P₀ : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
          conjTr (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1))
            (((Q⁻¹ : GL (Fin n) (GaloisField 2 (2 * (f + 1))))) :
              Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
          ((((Q⁻¹ : GL (Fin n) (GaloisField 2 (2 * (f + 1))))) :
            Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
            (P₀ : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1))))) =
        conjTr (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1))
          (P₀ : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
          (conjTr (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1))
            (((Q⁻¹ : GL (Fin n) (GaloisField 2 (2 * (f + 1))))) :
              Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
          (((Q⁻¹ : GL (Fin n) (GaloisField 2 (2 * (f + 1))))) :
            Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1))))) *
            (P₀ : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) := by
          simp only [Matrix.mul_assoc]
      _ = antidiag n := by rw [hQQ, Matrix.mul_one, hP₀]
  have hφs : ∀ (s₀ u₀ : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n)),
      (u₀ : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) = Q * s₀ * Q⁻¹ →
      SURep.ggFrameU hF ψ (Q⁻¹ * P₀) hP s₀ = ψ₁ u₀ := by
    intro s₀ u₀ hu₀
    have hsu : (SURep.ggFrameEquiv hF (Q⁻¹ * P₀) hP).symm s₀ =
        (SURep.ggFrameEquiv hF P₀ hP₀).symm u₀ := by
      apply Subtype.ext
      rw [SURep.coe_ggFrameEquiv_symm, SURep.coe_ggFrameEquiv_symm, hu₀]
      group
    exact (SURep.ggFrameU_apply hF ψ (Q⁻¹ * P₀) hP s₀).trans
      ((congrArg ψ hsu).trans (SURep.ggFrameU_apply hF ψ P₀ hP₀ u₀).symm)
  have hFkφ : SURep.GGFrameKer (SURep.ggFrameU hF ψ (Q⁻¹ * P₀) hP) :=
    SURep.ggFrameKer_ggFrameU hF ψ (Q⁻¹ * P₀) hP (by omega) hnq hker
  have hconj : ∀ X : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n),
      Q⁻¹ * (X : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) * Q ∈
        unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n :=
    fun X => SUTB.conj_mem_unitarySU h hQ X.2
  have hφc : ∀ X : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n),
      SURep.ggFrameU hF ψ (Q⁻¹ * P₀) hP ⟨Q⁻¹ * X * Q, hconj X⟩ = ψ₁ X := fun X =>
    hφs _ X (by
      change (X : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) = Q * (Q⁻¹ * X * Q) * Q⁻¹
      group)
  have hmod : ∀ {y : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n)}, y ∈ A →
      ∀ k : ℕ, y ^ k = y ^ (k % p) := fun hy k => by
    conv_lhs => rw [← Nat.mod_add_div k p, pow_add, pow_mul, hA.pow _ hy, one_pow, mul_one]
  refine ⟨Q⁻¹ * P₀, hP, d, ⟨Q⁻¹ * xx * Q, hconj xx⟩, hd2, hd4, ?_, ?_, hblock, hfix, hfixr, ?_⟩
  · rw [hφc]
    exact ((hmemA xx).mp hxx).2
  · exact Units.ext (by rw [Units.val_mul, Units.val_mul]; exact hcomm')
  ·
    refine SUTB.card_le_sq_of_forall _ (ψ₁ a₁) (ψ₁ a₂) fun b hb => ?_
    obtain ⟨hbB, hbC⟩ := Subgroup.mem_inf.mp hb
    obtain ⟨X, hXp, rfl⟩ := hlift b hbB
    have hXA : X ∈ A := (hmemA X).mpr ⟨hXp, hbB⟩
    have hX'p : (⟨Q⁻¹ * X * Q, hconj X⟩ :
        ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n)) ^ p = 1 := by
      apply Subtype.ext
      change (Q⁻¹ * (X : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) * Q) ^ p = 1
      have h1 := conj_pow (a := Q⁻¹) (b := (X : GL (Fin n) (GaloisField 2 (2 * (f + 1))))) (i := p)
      rw [inv_inv] at h1
      rw [h1, ← SubgroupClass.coe_pow, hXp, OneMemClass.coe_one, mul_one, inv_mul_cancel]
    have hX'c : ∀ s ∈ TableBUE.blockSU (K := GaloisField 2 (2 * (f + 1))) (n := f + 1)
        (SUNS.midSet n d), (⟨Q⁻¹ * X * Q, hconj X⟩ :
          ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n)) * s =
          s * ⟨Q⁻¹ * X * Q, hconj X⟩ := by
      intro s hs
      refine SUNS.commute_of_frame_commute h hFkφ hp hns hX'p ?_
      rw [hφc]
      exact ((Subgroup.mem_centralizer_iff.mp hbC) _ (Subgroup.mem_map_of_mem _ hs)).symm
    have hbl := SUTB.isBlockOn_compl_of_commute_blockSU h hp hns
      (by rw [SUNS.card_midSet]; omega) hX'p hX'c
    obtain ⟨i, j, hij⟩ := hgen X hXA hbl
    refine ⟨⟨i % p, Nat.mod_lt _ hp.pos⟩, ⟨j % p, Nat.mod_lt _ hp.pos⟩, ?_⟩
    rw [hij, hmod ha₁ i, hmod ha₂ j, map_mul, map_pow, map_pow]

theorem ggSixRootFusionSURepNonsplitInput_holds : GGSixRootFusionSURepNonsplitInput :=
  ggSixRootFusionSURepNonsplitInput_of_twoBlock ggSUNonsplitTwoBlockInput_holds

theorem ggSixRootFusionSURepInput_of_known (h1 : GGSUBlockNotExcludedInput)
    (h2 : GGSUSixAlphaInput) : GGSixRootFusionSURepInput :=
  ggSixRootFusionSURepInput_of_twoBlock_known ggSUNonsplitTwoBlockInput_holds h1 h2

end Inputs

end CFSG.StandardType
