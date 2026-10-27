module

public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofSplit
public import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofOddModels
public import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofSp4
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.ClassicalGroups.Unitary.Simple
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.RankThree.PartTwo.Census.Classical.Bridges
import CFSG.LieType.Simplicity.Exceptional
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofSymp
public import CFSG.Sporadic.ON.SimpleBase
public import CFSG.Sporadic.Schreier.TitsOther
public import Certificates.Certificate2237
public import Certificates.Certificate2239
public import Certificates.Certificate2241
public import Certificates.Certificate2244
public import Certificates.Certificate8057
public import Certificates.Certificate8058
public import Certificates.Certificate8059

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projImage)
open CFSG.Assembly.LowTwoRank (StatedSL StatedSU StatedSp StatedProj StatedScalars
  StatedClassicalModel)
open Matrix

@[expose] def PSp4OddCentThree : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p → (p % 5 = 1 ∨ p % 5 = 4) →
    ∀ y : projSp 2 (GaloisField p 1), orderOf y = 3 →
      Nonempty (inSubgroup perfectResidual (Subgroup.centralizer ({y} : Set (projSp 2
          (GaloisField p 1)))) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField p 1)) ∨
        Nonempty (inSubgroup perfectResidual (Subgroup.centralizer ({y} : Set (projSp 2
          (GaloisField p 1)))) ≃* projSL 2 (GaloisField p 1))

@[expose] def U4OddCentThree : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 1 → ∀ y : projSU 4 p 1, orderOf y = 3 →
    Nonempty (inSubgroup perfectResidual (Subgroup.centralizer ({y} : Set (projSU 4 p 1))) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (GaloisField p 1)) ∨
      Nonempty (inSubgroup perfectResidual (Subgroup.centralizer ({y} : Set (projSU 4 p 1))) ≃*
        projSL 2 (GaloisField p 2))

@[expose] def L4OddCentThree : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 2 → ∀ y : projSL 4 (GaloisField p 1), orderOf y = 3 →
    Nonempty (inSubgroup perfectResidual (Subgroup.centralizer ({y} : Set (projSL 4
        (GaloisField p 1)))) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField p 1)) ∨
      Nonempty (inSubgroup perfectResidual (Subgroup.centralizer ({y} : Set (projSL 4
        (GaloisField p 1)))) ≃* projSL 2 (GaloisField p 2))

namespace Item228Census2Proof

theorem noL2Normal228_of_simple_noL2Config {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (h : ∀ y : S, orderOf y = 3 →
      NoL2Config228 (inSubgroup perfectResidual (Subgroup.centralizer ({y} : Set S)))) :
    NoL2Normal228 S := by
  intro y N Kb m hyZ
  have hZ : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with hb | ht
    · exact hb
    · exact (hyZ (ht ▸ Subgroup.mem_top y)).elim
  exact noL2Normal228_of_noL2Config hZ h y N Kb m hyZ

theorem two_ne_zero_galoisField {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : GaloisField p e) ≠ 0 := by
  intro h
  have := (CharP.cast_eq_zero_iff (GaloisField p e) p 2).mp (by exact_mod_cast h)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp this)

theorem noL2Config228_SL2_galois {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    NoL2Config228 (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p 1)) :=
  noL2Config228_SL2 (two_ne_zero_galoisField hp2)

theorem noL2Config228_projSL_two_galois {p e : ℕ} [Fact p.Prime] (he : e ≠ 0) (hp2 : p ≠ 2)
    (h7 : 7 ≤ p ^ e) : NoL2Config228 (projSL 2 (GaloisField p e)) := by
  have hK : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e he
  refine noL2Config228_projSL_two
    (by rw [hK]; exact Odd.pow ((Fact.out : p.Prime).odd_of_ne_two hp2))
    (by rw [hK]; exact h7)

theorem orderOf_ne_fifteen_projSp_two {K : Type} [Field K] [Fintype K]
    (hq5 : Fintype.card K % 5 = 2 ∨ Fintype.card K % 5 = 3) (hq3 : Fintype.card K % 3 ≠ 0)
    (g : projSp 2 K) : orderOf g ≠ 15 := by
  intro hg
  obtain ⟨A, hA, hAg⟩ := g.2
  have hAsp : A ∈ StatedSp 2 K := hA
  have hmk : ∀ k : ℕ, g ^ k = 1 ↔ A ^ k ∈ Subgroup.center (GL (Fin 2 ⊕ Fin 2) K) := by
    intro k
    rw [← OneMemClass.coe_eq_one, Subgroup.coe_pow, ← hAg, ← map_pow,
      Matrix.ProjGenLinGroup.mk_eq_one]
  have hc := (hmk 15).mp (hg ▸ pow_orderOf_eq_one g)
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
  obtain ⟨l, hl⟩ := hc
  have hlsp : Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) l ∈ StatedSp 2 K :=
    hl ▸ (StatedSp 2 K).pow_mem hAsp 15
  have hl2 : (l : K) ^ 2 = 1 := by
    have h := mem_statedSp_iff_gram.mp hlsp
    rw [Matrix.GeneralLinearGroup.coe_scalar] at h
    have h' := congrArg (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K =>
      M (Sum.inl 0) (Sum.inr 0)) h
    simp [Matrix.scalar_apply, Matrix.fromBlocks] at h'
    linear_combination h'
  obtain ⟨B, hBsp, hBg, hB15⟩ : ∃ B : GL (Fin 2 ⊕ Fin 2) K, B ∈ StatedSp 2 K ∧
      Matrix.ProjGenLinGroup.mk B = (g : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2) K) ∧
      B ^ 15 = 1 := by
    have hl' : l = 1 ∨ l = -1 := by
      have h0 : ((l : K) - 1) * ((l : K) + 1) = 0 := by linear_combination hl2
      rcases mul_eq_zero.mp h0 with h | h
      · exact Or.inl (Units.ext (by rw [Units.val_one]; linear_combination h))
      · exact Or.inr (Units.ext (by rw [Units.val_neg, Units.val_one]; linear_combination h))
    have hs : Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) (-1 : Kˣ) = -1 := by
      ext i j
      simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_neg, Units.val_one,
        Matrix.scalar_apply]
      rw [Matrix.neg_apply, Matrix.one_apply, Matrix.diagonal_apply]
      split_ifs <;> simp
    rcases hl' with rfl | rfl
    · exact ⟨A, hAsp, hAg, by rw [← hl, map_one]⟩
    · refine ⟨-A, ?_, ?_, ?_⟩
      · have hneg : (-1 : GL (Fin 2 ⊕ Fin 2) K) ∈ StatedSp 2 K := by
          rw [mem_statedSp_iff_gram]
          simp
        rw [show -A = (-1) * A by rw [neg_one_mul]]
        exact (StatedSp 2 K).mul_mem hneg hAsp
      · rw [← hAg, show -A = Matrix.GeneralLinearGroup.scalar _ (-1) * A by
          ext i j
          simp [Matrix.GeneralLinearGroup.coe_scalar], map_mul,
          Matrix.ProjGenLinGroup.mk_eq_one.mpr (by
            rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
            exact ⟨-1, rfl⟩), one_mul]
      · rw [Odd.neg_pow (by decide), ← hl, hs, neg_neg]
  have hBpow : ∀ k : ℕ, B ^ k = 1 → g ^ k = 1 := by
    intro k hk
    apply Subtype.ext
    rw [Subgroup.coe_pow, OneMemClass.coe_one, ← hBg, ← map_pow, hk, map_one]
  have hne : ∀ k : ℕ, ¬ 15 ∣ k → B ^ k ≠ 1 := fun k hk h1 =>
    hk (hg ▸ orderOf_dvd_of_pow_eq_one (hBpow k h1))
  set M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := (B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
  have hcoe : ∀ k : ℕ, ((B ^ k : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
      = M ^ k := fun k => Units.val_pow_eq_pow_val B k
  have hsp : ∀ k : ℕ, (M ^ k)ᵀ * fromBlocks 0 1 (-1) 0 * M ^ k = fromBlocks 0 1 (-1) 0 := by
    intro k
    rw [← hcoe]
    exact mem_statedSp_iff_gram.mp ((StatedSp 2 K).pow_mem hBsp k)
  have hM15 : M ^ 15 = 1 := by rw [← hcoe, hB15]; rfl
  have hMne : ∀ k : ℕ, ¬ 15 ∣ k → M ^ k ≠ 1 := fun k hk h1 =>
    hne k hk (Units.ext (by rw [← hcoe] at h1; exact h1))
  set φ := (Matrix.toLinAlgEquiv' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K ≃ₐ[K]
    Module.End K (Fin 2 ⊕ Fin 2 → K)) with hφ
  have hφM : ∀ k : ℕ, φ (M ^ k) = Matrix.toLin' (M ^ k) := fun k => rfl
  have hV : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 4 := by simp
  refine no_commuting_isometries_three_five hV hq5 hq3
    (Matrix.toBilin' (fromBlocks 0 1 (-1) 0)) (sympJ_nondegenerate)
    (a := φ (M ^ 5)) (c := φ (M ^ 3)) (fun x y => by rw [hφM]; exact sympJ_isometry (hsp 5) x y)
    (fun x y => by rw [hφM]; exact sympJ_isometry (hsp 3) x y) ?_ ?_ ?_ ?_ ?_
  · rw [← map_mul, ← map_mul, ← pow_add, ← pow_add, add_comm]
  · rw [← map_pow, ← pow_mul, hM15, map_one]
  · exact fun h1 => hMne 5 (by norm_num) (φ.injective (h1.trans (map_one φ).symm))
  · rw [← map_pow, ← pow_mul, hM15, map_one]
  · exact fun h1 => hMne 3 (by norm_num) (φ.injective (h1.trans (map_one φ).symm))

theorem seven_le_of_prime {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hp5 : p ≠ 5) : 7 ≤ p := by
  have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
  have h6 : p ≠ 6 := by rintro rfl; norm_num at hp
  omega

theorem mod_three_ne_zero_of_prime {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) : p % 3 ≠ 0 := by
  intro h
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h)
  omega

end Item228Census2Proof

open Item228Census2Proof

theorem census228PSp4Odd_of (hK : PSp4OddCentThree) : Census228PSp4Odd := by
  intro p _ hp hp5 Y _ _ ⟨eY⟩
  have hp' : p.Prime := Fact.out
  have hKc : Nat.card (GaloisField p 1) = p := by rw [GaloisField.card p 1 one_ne_zero, pow_one]
  have hS : IsSimpleGroup (projSp 2 (GaloisField p 1)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ 2 p 1
      ⟨⟨hp', le_rfl, le_rfl, by
        intro h
        simp only [pow_one, Prod.mk.injEq, true_and] at h
        omega⟩, GaloisField p 1, inferInstance, inferInstance, by rw [hKc, pow_one],
        ⟨(CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage
          (StatedSp 2 (GaloisField p 1))).symm⟩⟩
  have : Finite (projSp 2 (GaloisField p 1)) := Finite.of_equiv _ eY.toEquiv
  refine Or.inr (Item228CensusProof.noL2Normal228_of_mulEquiv eY ?_)
  have hp2 : p ≠ 2 := by omega
  have h7 : 7 ≤ p ^ 1 := by rw [pow_one]; exact seven_le_of_prime hp' hp hp5
  have hcase : p % 5 = 1 ∨ p % 5 = 4 ∨ p % 5 = 2 ∨ p % 5 = 3 := by
    have : p % 5 ≠ 0 := fun h0 => hp5 ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp').mp
      (Nat.dvd_of_mod_eq_zero h0)).symm
    omega
  rcases hcase with h | h | h | h
  · refine noL2Normal228_of_simple_noL2Config fun y hy => ?_
    rcases hK p hp (Or.inl h) y hy with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact noL2Config228_of_mulEquiv e (noL2Config228_SL2_galois hp2)
    · exact noL2Config228_of_mulEquiv e (noL2Config228_projSL_two_galois one_ne_zero hp2 h7)
  · refine noL2Normal228_of_simple_noL2Config fun y hy => ?_
    rcases hK p hp (Or.inr h) y hy with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact noL2Config228_of_mulEquiv e (noL2Config228_SL2_galois hp2)
    · exact noL2Config228_of_mulEquiv e (noL2Config228_projSL_two_galois one_ne_zero hp2 h7)
  all_goals
    have : Fintype (GaloisField p 1) := Fintype.ofFinite _
    have hq5 : Fintype.card (GaloisField p 1) % 5 = 2 ∨ Fintype.card (GaloisField p 1) % 5 = 3 := by
      rw [Fintype.card_eq_nat_card, hKc]
      omega
    have hq3 : Fintype.card (GaloisField p 1) % 3 ≠ 0 := by
      rw [Fintype.card_eq_nat_card, hKc]
      exact mod_three_ne_zero_of_prime hp' hp
    have h15 := orderOf_ne_fifteen_projSp_two hq5 hq3
    exact noL2Normal228_of_simple_perfectResidual fun y hy h5 =>
      Item22Res4Proof.not_five_dvd_centralizer_of_no15 h15 hy
        (h5.trans (Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _)))

theorem census228U4Odd_of (hK : U4OddCentThree) : Census228U4Odd := by
  intro p _ hp hp1 Y _ _ ⟨eY⟩
  have hp' : p.Prime := Fact.out
  have e : StatedProj (StatedSU 4 (p ^ 1) (GaloisField p (2 * 1))) ≃* projSU 4 p 1 :=
    (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage _).trans
      (MulEquiv.subgroupCongr (CFSG.RankThree.PartTwo.Census.projImage_statedSU 4 p 1))
  have hS : IsSimpleGroup (projSU 4 p 1) :=
    (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 4 p 1
      ⟨⟨hp', le_rfl, by norm_num, by simp⟩, GaloisField p (2 * 1), inferInstance, inferInstance,
        by rw [GaloisField.card p (2 * 1) (by norm_num)]; ring, ⟨e.symm⟩⟩).2
  have : Finite (projSU 4 p 1) := Finite.of_equiv _ eY.toEquiv
  have hp2 : p ≠ 2 := by omega
  refine Or.inr (Item228CensusProof.noL2Normal228_of_mulEquiv eY
    (noL2Normal228_of_simple_noL2Config fun y hy => ?_))
  rcases hK p hp hp1 y hy with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact noL2Config228_of_mulEquiv e (noL2Config228_SL2_galois hp2)
  · exact noL2Config228_of_mulEquiv e (noL2Config228_projSL_two_galois (by norm_num) hp2
      (by have := Nat.pow_le_pow_left (show 4 ≤ p by omega) 2; omega))

theorem census228L4Odd_of (hK : L4OddCentThree) : Census228L4Odd := by
  intro p _ hp hp2' Y _ _ ⟨eY⟩
  have hp' : p.Prime := Fact.out
  have hS : IsSimpleGroup (projSL 4 (GaloisField p 1)) := by
    have := CFSG.BenderSuzuki.External.huppert_II_6_13 (K := GaloisField p 1) 4 (by norm_num)
      (Or.inl (by norm_num)) (Or.inl (by norm_num))
    exact (Sec4.projSLEquivPSLn 4 (GaloisField p 1)).isSimpleGroup
  have : Finite (projSL 4 (GaloisField p 1)) := Finite.of_equiv _ eY.toEquiv
  have hp2 : p ≠ 2 := by omega
  refine Or.inr (Item228CensusProof.noL2Normal228_of_mulEquiv eY
    (noL2Normal228_of_simple_noL2Config fun y hy => ?_))
  rcases hK p hp hp2' y hy with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact noL2Config228_of_mulEquiv e (noL2Config228_SL2_galois hp2)
  · exact noL2Config228_of_mulEquiv e (noL2Config228_projSL_two_galois (by norm_num) hp2
      (by have := Nat.pow_le_pow_left (show 4 ≤ p by omega) 2; omega))

end CFSG.RankThree.PartTwo.Sec21
