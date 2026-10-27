module

public import CFSG.LocalAnalysis.StandardType.GGSporKLieZBlockO2
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpDecomp
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpIsoOneLinear
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpIsoUnitary
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepA2
import CFSG.LocalAnalysis.StandardType.TableC.GramBlockRank

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.Open CFSG.StandardType.ClassicalBlocks CFSG.StandardType.ClassicalPosition
  CFSG.StandardType.TableC Matrix

private abbrev l937z_sp_J (n : ℕ) (K : Type) [Field K] :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K)
    (-1 : Matrix (Fin n) (Fin n) K) 0

private lemma l937z_sp_neg_one {n : ℕ} {K : Type} [Field K] [CharP K 2] :
    (-1 : Matrix (Fin n) (Fin n) K) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [CharTwo.neg_eq]
  · simp [h]

private lemma l937z_sp_J_eq {n : ℕ} {K : Type} [Field K] [CharP K 2] :
    l937z_sp_J n K = Matrix.J (Fin n) K := by
  have hneg : (-1 : Matrix (Fin n) (Fin n) K) = 1 := l937z_sp_neg_one
  rw [l937z_sp_J, Matrix.J, Matrix.fromBlocks_inj]
  exact ⟨rfl, hneg.symm, hneg, rfl⟩

private lemma l937z_sp_J_transpose {n : ℕ} {K : Type} [Field K] [CharP K 2] :
    Matrix.transpose ((l937z_sp_J n K).map (RingHom.id K)) = l937z_sp_J n K := by
  have hneg : (-1 : Matrix (Fin n) (Fin n) K) = 1 := l937z_sp_neg_one
  rw [show (⇑(RingHom.id K) : K → K) = id from rfl, Matrix.map_id, l937z_sp_J,
    Matrix.fromBlocks_transpose, Matrix.fromBlocks_inj]
  refine ⟨rfl, ?_, ?_, rfl⟩
  · simpa [Matrix.transpose_neg, Matrix.transpose_one] using hneg
  · simpa [Matrix.transpose_one] using hneg.symm

private lemma l937z_sp_J_symm {n : ℕ} {K : Type} [Field K] [CharP K 2] :
    Matrix.transpose (l937z_sp_J n K) = l937z_sp_J n K := by
  have hneg : (-1 : Matrix (Fin n) (Fin n) K) = 1 := l937z_sp_neg_one
  rw [l937z_sp_J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_inj]
  refine ⟨rfl, ?_, ?_, rfl⟩
  · simpa [Matrix.transpose_neg, Matrix.transpose_one] using hneg
  · simpa [Matrix.transpose_one] using hneg.symm

private lemma l937z_sp_J_isUnit_det {n : ℕ} {K : Type} [Field K] [CharP K 2] :
    IsUnit (l937z_sp_J n K).det := by
  rw [l937z_sp_J_eq]
  exact Matrix.isUnit_det_J (Fin n) K

private lemma l937z_sp_exists_prim {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K) (hodd : Odd (orderOf b))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (l937z_sp_J n K)
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) ε) :
    ∃ e, IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) e ∧
      e * ε = e ∧ (e = ε ∨ (e ≠ ε ∧ formAdj (RingHom.id K) (l937z_sp_J n K) e ≠ e ∧
        ε = e + formAdj (RingHom.id K) (l937z_sp_J n K) e)) := by
  refine exists_isPrimIdemIn_of_isPrimAdjIdemIn (RingHom.id K) (fun x => rfl)
    l937z_sp_J_isUnit_det l937z_sp_J_transpose (S := ({b} : Set (GL (Fin n ⊕ Fin n) K)))
    ?_ ?_ hε
  · intro s hs s' hs'
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  · intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    simpa using CFSG.Open.StatedAPI.mem_statedSp_iff.mp hb

private lemma l937z_sp_pCore_eq_bot_of_mulEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (h : pCore 2 H = ⊥) : pCore 2 G = ⊥ :=
  pCore_trivial_of_mulEquiv e.symm h

private lemma l937z_sp_block_pCoreOf_eq_bot {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K) (hodd : Odd (orderOf b))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (l937z_sp_J n K)
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) ε) :
    pCoreOf 2 (glBlockCentralizer (StatedSp n K).subtype ({b} : Set (GL (Fin n ⊕ Fin n) K)) ε)
      = ⊥ := by
  classical
  obtain ⟨e, he, -, hcase⟩ := l937z_sp_exists_prim b hb hodd hε
  have hmain : pCore 2 ↥(glBlockCentralizer (StatedSp n K).subtype
      ({b} : Set (GL (Fin n ⊕ Fin n) K)) ε) = ⊥ := by
    rcases hcase with heq | ⟨hne, hstarne, hsum⟩
    · have heprim : IsPrimIdemIn (Algebra.adjoin K
          (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) ε := heq ▸ he
      by_cases h1 : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε = ε
      · obtain ⟨n₁, -, ⟨iso⟩⟩ := blockGroup_iso_Sp_one b hb hodd hε h1
        exact l937z_sp_pCore_eq_bot_of_mulEquiv iso (pCore_two_StatedSp_eq_bot n₁)
      · obtain ⟨d, m, E, hEfield, hEfin, -, hEcard, -, -, ⟨iso⟩⟩ :=
          blockGroup_iso_Sp_unitary b hb hodd hε heprim h1
        letI : Field E := hEfield
        letI : Fintype E := hEfin
        haveI : Finite E := Fintype.finite hEfin
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        obtain ⟨f, -, hKcard⟩ := FiniteField.card K 2
        have hEtwo : Fintype.card E = 2 ^ (2 * ((f : ℕ) * d)) := by
          rw [hEcard, hKcard, ← pow_mul, ← pow_mul]
          congr 1
          ring
        haveI : CharP E 2 := charP_of_card_eq_prime_pow (p := 2)
          (f := 2 * ((f : ℕ) * d)) hEtwo
        have hEnat : Nat.card E = (Fintype.card K ^ d) ^ 2 := by
          rw [Nat.card_eq_fintype_card]
          exact hEcard
        exact l937z_sp_pCore_eq_bot_of_mulEquiv iso
          (pCore_two_GUFull_eq_bot m (Fintype.card K ^ d) hEnat)
    · have hstar : IsPrimIdemIn (Algebra.adjoin K
          (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K))))
          (formAdj (RingHom.id K) (l937z_sp_J n K) e) := by
        refine isPrimIdemIn_formAdj_gram K (l937z_sp_J n K) l937z_sp_J_symm
          l937z_sp_J_isUnit_det (S := ({b} : Set (GL (Fin n ⊕ Fin n) K))) ?_ ?_ he
        · intro s hs
          rw [Set.mem_singleton_iff] at hs
          subst hs
          simpa using CFSG.Open.StatedAPI.mem_statedSp_iff.mp hb
        · intro s hs s' hs'
          rw [Set.mem_singleton_iff] at hs hs'
          rw [hs, hs']
      obtain ⟨d, m, E, hEfield, hEfin, -, hEcard, -, -, ⟨iso⟩⟩ :=
        blockGroup_iso_Sp_linear b hb hodd hε he hstar (Ne.symm hstarne) hsum
      letI : Field E := hEfield
      letI : Fintype E := hEfin
      haveI : Finite E := Fintype.finite hEfin
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨f, -, hKcard⟩ := FiniteField.card K 2
      have hEtwo : Fintype.card E = 2 ^ ((f : ℕ) * d) := by
        rw [hEcard, hKcard, ← pow_mul]
      haveI : CharP E 2 := charP_of_card_eq_prime_pow (p := 2)
        (f := (f : ℕ) * d) hEtwo
      exact l937z_sp_pCore_eq_bot_of_mulEquiv iso (pCore_two_GL_eq_bot m)
  rw [pCoreOf, hmain, Subgroup.map_bot]

theorem pCoreOf_centralizer_StatedSp_eq_bot {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K) (hodd : Odd (orderOf b)) :
    pCoreOf 2 ((Subgroup.centralizer ({b} : Set (GL (Fin n ⊕ Fin n) K))).comap
      (StatedSp n K).subtype) = ⊥ := by
  classical
  haveI : Finite K := Fintype.finite (inferInstance : Fintype K)
  obtain ⟨P, hPprim, _, _, hPcomm, hPsup, hPcard⟩ :=
    centralizer_block_decomp_Sp b hb hodd
  let C : Subgroup ↥(StatedSp n K) :=
    (Subgroup.centralizer ({b} : Set (GL (Fin n ⊕ Fin n) K))).comap (StatedSp n K).subtype
  let Gs : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K → Subgroup ↥(StatedSp n K) :=
    fun ε => glBlockCentralizer (StatedSp n K).subtype ({b} : Set (GL (Fin n ⊕ Fin n) K)) ε
  have hle : ∀ ε ∈ P, Gs ε ≤ C := fun ε _ => Subgroup.comap_mono inf_le_left
  have hO2 : ∀ ε ∈ P, pCoreOf 2 (Gs ε) = ⊥ :=
    fun ε hε => l937z_sp_block_pCoreOf_eq_bot b hb hodd (hPprim ε hε)
  exact pCore_trivial_of_commutingProduct C P Gs hle hPcomm hPsup hPcard hO2

end CFSG.StandardType.SporadicShape
