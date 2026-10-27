module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCFourteenSevenThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree
public import CFSG.LocalAnalysis.UniquenessCase.UC22Main1
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22tb
public import CFSG.GroupTheory.TwoResidualOddOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s17_45_hcond_C {D : Data G} {V A B : Subgroup G} {i : ℕ}
    (hAB : ⁅A, B⁆ = A) (hAodd : Odd (Nat.card A)) (hBodd : Odd (Nat.card B))
    (hAM : A ≤ D.M) (hBM : B ≤ D.M)
    (hC : ⁅E3.cClos V (i + 1) D.T, twoResidual (A ⊔ B ⊔ D.T)⁆ = ⊥)
    (hU2 : ∀ S : Subgroup G, S ≤ D.T →
      ((B ⊔ A ⊔ S : Subgroup G) : Set G) = (S : Set G) * (A : Set G) * (B : Set G) →
      CFSG.Open.pCoreOf 2 (B ⊔ A ⊔ S) ≠ ⊥ → UniqueMax D.M (B ⊔ A ⊔ S)) :
    InCalU D.M (D.M ⊓ centralizer (E3.cClos V (i + 1) D.T : Set G)) := by
  set Cc := E3.cClos V (i + 1) D.T with hCc
  have hZT : D.Z ≤ D.T := uc22main1_Z_le_T D
  have hZcent : ∀ z ∈ D.Z, ∀ t ∈ D.T, t * z = z * t := fun z hz t ht =>
    (CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.1 hz).2.1 t ht
  have hCcT : Cc ≤ D.T := inf_le_left
  have hZC : D.Z ≤ centralizer (Cc : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact hZcent z hz c (hCcT hc)
  have hZleCc : D.Z ≤ Cc := by
    refine le_inf hZT ?_
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact hZcent z hz w (E3.wClos_le (i + 1) D.T hw)
  have hres : twoResidual (A ⊔ B ⊔ D.T) ≤ centralizer (Cc : Set G) := by
    rw [Subgroup.commutator_comm] at hC
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hC
  have hA : A ≤ twoResidual (A ⊔ B ⊔ D.T) :=
    CFSG.GroupTheory.le_twoResidual_of_odd_card (le_sup_left.trans le_sup_left) hAodd
  have hB : B ≤ twoResidual (A ⊔ B ⊔ D.T) :=
    CFSG.GroupTheory.le_twoResidual_of_odd_card (le_sup_right.trans le_sup_left) hBodd
  have hAZ : A ≤ centralizer (D.Z : Set G) :=
    (hA.trans hres).trans (Subgroup.centralizer_le hZleCc)
  have hBZ : B ≤ centralizer (D.Z : Set G) :=
    (hB.trans hres).trans (Subgroup.centralizer_le hZleCc)
  have hBN : B ≤ normalizer (A : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.2 hAB.le
  have hABset : ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left A B hBN
  have hABZ : A ⊔ B ≤ normalizer (D.Z : Set G) :=
    sup_le (hAZ.trans (Subgroup.centralizer_le_normalizer _))
      (hBZ.trans (Subgroup.centralizer_le_normalizer _))
  have hZset : ((D.Z ⊔ (A ⊔ B) : Subgroup G) : Set G) =
      (D.Z : Set G) * ((A ⊔ B : Subgroup G) : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left D.Z (A ⊔ B) hABZ
  have hsupeq : B ⊔ A ⊔ D.Z = D.Z ⊔ (A ⊔ B) := by
    rw [sup_comm B A, sup_comm]
  have hset : ((B ⊔ A ⊔ D.Z : Subgroup G) : Set G) =
      (D.Z : Set G) * (A : Set G) * (B : Set G) := by
    rw [hsupeq, hZset, hABset, mul_assoc]
  have hZle : D.Z ≤ B ⊔ A ⊔ D.Z := le_sup_right
  have hZn : (D.Z.subgroupOf (B ⊔ A ⊔ D.Z)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hZle, hsupeq]
    exact sup_le Subgroup.le_normalizer hABZ
  have hpc : CFSG.Open.pCoreOf 2 (B ⊔ A ⊔ D.Z) ≠ ⊥ := by
    intro hbot
    have hle := CFSG.LieType.BorelTits.le_pCoreOf (r := 2) hZle hZn (D.sylowM.isPGroup.to_le hZT)
    rw [hbot] at hle
    exact uc22main1_Z_ne_bot D (le_bot_iff.1 hle)
  have hU := hU2 D.Z hZT hset hpc
  refine InCalU.mono D.maxLocal hU (le_inf ?_ ?_) inf_le_left
  · exact sup_le (sup_le hBM hAM) (hZT.trans D.sylowM.le)
  · exact sup_le (sup_le (hB.trans hres) (hA.trans hres)) hZC

theorem s17_45_r_ne_two {D : Data G} {L : Subgroup G} {x : G} {n r p : ℕ} {A₀ X : Subgroup G}
    (h8100 : F08.Hyp8100 D ![L, conjSubgroup L x] ![n, n] r p A₀ X) : r ≠ 2 := by
  obtain ⟨-, -, hsh, -, hdvd, -⟩ := h8100
  have hn1 : 1 ≤ n := by
    rcases hsh 0 with h | h
    · exact (CFSG.Blueprint.LieModel.admissible h).2.1
    · exact (CFSG.Blueprint.LieModel.admissible h).2.1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Nat.gcd_self] at hdvd
  rintro rfl
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h1 : 2 ∣ 2 ^ n - (2 ^ n - 1) := Nat.dvd_sub h2 hdvd
  rw [Nat.sub_sub_self hpos] at h1
  omega

theorem s17_45_bot_false (D : Data G) (h147 : Inputs1719.UC2_14_7Three D)
    (h126 : R126 D) (h111 : W3Thm111 G)
    {V L X : Subgroup G} {p n l r : ℕ} {C Dc : Subgroup G} {Gamma : Set G} {x : G}
    {A₀ A B : Subgroup G}
    (h1669 : Nat.card (⊥ : Subgroup G) ≤ 4 → MBarGT D.M ⊥ V 3)
    (ctx : Ctx17_42 D ⊥ V L X p n l C Dc Gamma) (hp3 : p = 3)
    (h8100 : F08.Hyp8100 D ![L, conjSubgroup L x] ![n, n] r p A₀ X)
    (hc : F08.Case8100ThreeR D ![L, conjSubgroup L x] p X ∨
      F08.Case8100FourR D ![L, conjSubgroup L x] p X)
    (hAsyl : CFSG.ABGLocalTools.IsSylowOf r A X) (hAT : Permutes A D.T) (hBM : B ≤ D.M)
    (hBcard : Nat.card B = p) (hAB : ⁅A, B⁆ = A) (hBT : Permutes B D.T)
    (hInF : InFSq 1 (A ⊔ B ⊔ D.T)) : False := by
  have hV := ctx.hyp125
  rcases hV.1 with ⟨hW, -⟩ | ⟨h0, -, -⟩
  swap
  · exact absurd rfl h0.1.1
  have hV1 : InCalV1 D.M D.T V := hW.1.1
  have hVV : InCalV D.M V := hV1.1
  have hV' : IsElemAbelian 2 V := hVV.2.2.2
  have hm3 : MBarGT D.M ⊥ V 3 := h1669 (by rw [Subgroup.card_bot]; norm_num)
  have hm2 : MBarGT D.M ⊥ V 2 := TwelveShort.mBarGT_mono hm3 (by norm_num)
  have hs : 3 < E3.sParam hV' := TwelveShort.lt_sParam_of_mBarGT D h111 hV1 hm2 hm3
  have hk2 : D.k ≤ 2 := by
    unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
    split_ifs <;> norm_num
  obtain ⟨H₀, hmin⟩ := hV.exists_hyp124Min
  have hS : IsSylowIn 2 D.T H₀ := TwelveShort.isSylowIn_of_le D hmin.1.1
  have hE : E1.InE D.k H₀ := h126 H₀ hmin
  have hW0 : E3.wClos V 0 D.T ≠ ⊥ := TwelveShort.wClos_zero_ne_bot D hVV
  have h147' := h147 ![L, conjSubgroup L x] ![n, n] r p A₀ X B A h8100
    (Inputs1719.case8100Three_of_p_eq_three hp3 hc) hAsyl hAT hBM hBcard hAB hBT
  have hUABT : UniqueMax D.M (A ⊔ B ⊔ D.T) := by
    have h := h147'.1
    rwa [show B ⊔ A ⊔ D.T = A ⊔ B ⊔ D.T by rw [sup_comm B A]] at h
  have hU2 := h147'.2
  have hXM : X ≤ D.M := by
    rw [ctx.X_eq]
    exact TwelveTwentyThree.conjClosure_le ctx.mem_calC.1.le
  have hAM : A ≤ D.M := hAsyl.le.trans hXM
  have hr2 : r ≠ 2 := s17_45_r_ne_two h8100
  have hAodd : Odd (Nat.card A) := by
    obtain ⟨k, hk⟩ := hAsyl.isPGroup.exists_card_dvd_pow
    obtain ⟨m, -, hcard⟩ := (Nat.dvd_prime_pow h8100.2.2.2.1).1 hk
    rw [hcard]
    exact (h8100.2.2.2.1.odd_of_ne_two hr2).pow
  have hBodd : Odd (Nat.card B) := by
    rw [hBcard, hp3]
    decide
  have hABTM : A ⊔ B ⊔ D.T ≤ D.M := sup_le (sup_le hAM hBM) D.sylowM.le
  have hcond : ∀ i : ℕ, i ≤ D.k →
      InCalU D.M (D.M ⊓ normalizer (E3.wClos V i D.T : Set G)) ∨
        InCalU D.M (D.M ⊓ centralizer (E3.cClos V (i + 1) D.T : Set G)) := by
    intro i hi
    rcases uc22p22tb_dich hV' (TwelveShort.isSylowIn_of_le D le_sup_right) hInF
        (i := i) (by omega) with hN | hC
    · exact Or.inl (InCalU.mono D.maxLocal hUABT (le_inf hABTM hN) inf_le_left)
    · exact Or.inr (s17_45_hcond_C hAB hAodd hBodd hAM hBM hC hU2)
  exact hmin.1.2.1 (six_fifteen_four hV' D.maxLocal hS (TwelveShort.one_le_k D) hE hW0
    (by omega) hcond)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
