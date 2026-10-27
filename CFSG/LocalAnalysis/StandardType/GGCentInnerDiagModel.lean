module

public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagBlocks
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagLinear
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagUnitary
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagSp
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagOmega
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpDecomp
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpIsoOneLinear
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpIsoUnitary
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaDecomp
public import CFSG.LocalAnalysis.StandardType.TableC.POmegaBlockDeg
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResU3ThreeSolv
public import CFSG.RankThree.GF2n.Smith81.OrthE1KFLinear
public import CFSG.ClassicalGroups.SpecialLinear.InvariantForms
public import CFSG.ClassicalGroups.SpecialLinear.NaturalDualSum
public import CFSG.GroupTheory.HuppertProduct.Quotient
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassical
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalRows
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.SpTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutTwE6
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512DeltaA
public import CFSG.RankThree.GF2n.Smith81.EStmt
public import CFSG.RankThree.GF2n.Smith81.OrthE2Layer
public import CFSG.RankThree.GF2n.Smith81.TiLane
public import CFSG.RankThree.GF2n.Smith81.TiLemmaC
public import CFSG.RankThree.GF2n.Stroth80.Consumers
public import CFSG.RankThree.GF2n.Stroth80.Sec1110ModuleDual
public import CFSG.RankThree.GF2n.Stroth80.Sec11Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec310Main
public import CFSG.RankThree.GF2n.Stroth80.Sec45
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaPoints
public import CFSG.RankThree.GF2n.Stroth80.Sec6Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7EndDefs
public import CFSG.RankThree.GF2n.Stroth80.Sec7OmegaSign
public import CFSG.RankThree.GF2n.Stroth80.SpHomTrivial
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Gaschutz
public import Certificates.Certificate9530

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open (StatedSp StatedOmega)
open CFSG.StandardType.ClassicalPosition CFSG.StandardType.ClassicalBlocks

private lemma spBlockNegOne_eq_one {n : ℕ} {K : Type} [Field K] [CharP K 2] :
    (-1 : Matrix (Fin n) (Fin n) K) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h, CharTwo.neg_eq]

private lemma spBlockGram_eq_J {n : ℕ} {K : Type} [Field K] [CharP K 2] :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      Matrix.J (Fin n) K := by
  rw [Matrix.J, Matrix.fromBlocks_inj]
  exact ⟨rfl, spBlockNegOne_eq_one.symm, spBlockNegOne_eq_one, rfl⟩

lemma spBlockGram_isUnit_det {n : ℕ} {K : Type} [Field K] [CharP K 2] :
    IsUnit (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).det := by
  rw [spBlockGram_eq_J]
  exact Matrix.isUnit_det_J (Fin n) K

lemma spBlockGram_transpose {n : ℕ} {K : Type} [Field K] [CharP K 2] :
    Matrix.transpose (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  rw [Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.transpose_one,
    Matrix.transpose_neg (1 : Matrix (Fin n) (Fin n) K), Matrix.transpose_one,
    Matrix.fromBlocks_inj]
  exact ⟨rfl, spBlockNegOne_eq_one, spBlockNegOne_eq_one.symm, rfl⟩

private lemma spBlockGram_isometry {n : ℕ} {K : Type} [Field K] [CharP K 2]
    {b : GL (Fin n ⊕ Fin n) K} (hb : b ∈ StatedSp n K) :
    Matrix.transpose ((b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).map (RingHom.id K)) *
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
      (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  have h := CFSG.Open.StatedAPI.mem_statedSp_iff.mp hb
  simpa [Matrix.map_id] using h

lemma spBlockGroup_moved_eq_unitary {K : Type} [Field K] [Fintype K] [CharP K 2]
    {n : ℕ} (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K) (hodd : Odd (orderOf b))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) ε)
    (heprim : IsPrimIdemIn (Algebra.adjoin K
      (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) ε)
    (h1 : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε) :
    ∃ (m Q : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2),
      Nat.card E = Q ^ 2 ∧
      Nonempty (↥(glBlockCentralizer (StatedSp n K).subtype {b} ε) ≃* ↥(GUFull m Q E)) := by
  obtain ⟨d, m, E, hEfield, hEfin, -, hEcard, -, -, ⟨iso⟩⟩ :=
    blockGroup_iso_Sp_unitary b hb hodd hε heprim h1
  exact
    letI : Field E := hEfield
    letI : Fintype E := hEfin
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    by
      obtain ⟨f, -, hKcard⟩ := FiniteField.card K 2
      have hEtwo : Fintype.card E = 2 ^ (2 * ((f : ℕ) * d)) := by
        rw [hEcard, hKcard, ← pow_mul, ← pow_mul]
        congr 1
        ring
      have hcharE : CharP E 2 := charP_of_card_eq_prime_pow (p := 2)
        (f := 2 * ((f : ℕ) * d)) hEtwo
      refine ⟨m, Fintype.card K ^ d, E, hEfield, Fintype.finite hEfin, hcharE, ?_, ⟨iso⟩⟩
      rw [Nat.card_eq_fintype_card]
      exact hEcard

private lemma spBlockGroup_pair_eq_generalLinear {K : Type} [Field K] [Fintype K] [CharP K 2]
    {n : ℕ} (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K) (hodd : Odd (orderOf b))
    {ε e e' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) ε)
    (he : IsPrimIdemIn (Algebra.adjoin K
      (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) e)
    (he' : IsPrimIdemIn (Algebra.adjoin K
      (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) e')
    (hne : e ≠ e') (hεe : ε = e + e') :
    ∃ (m : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2),
      Nonempty (↥(glBlockCentralizer (StatedSp n K).subtype {b} ε) ≃* GL (Fin m) E) := by
  obtain ⟨d, m, E, hEfield, hEfin, -, hEcard, -, -, ⟨iso⟩⟩ :=
    blockGroup_iso_Sp_linear b hb hodd hε he he' hne hεe
  exact
    letI : Field E := hEfield
    letI : Fintype E := hEfin
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    by
      obtain ⟨f, -, hKcard⟩ := FiniteField.card K 2
      have hEtwo : Fintype.card E = 2 ^ ((f : ℕ) * d) := by
        rw [hEcard, hKcard, ← pow_mul]
      have hcharE : CharP E 2 := charP_of_card_eq_prime_pow (p := 2)
        (f := (f : ℕ) * d) hEtwo
      exact ⟨m, E, hEfield, Fintype.finite hEfin, hcharE, ⟨iso⟩⟩

theorem blockGroup_iso_Sp_cases {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K) (hodd : Odd (orderOf b))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) ε) :
    (∃ n₁ : ℕ,
      Nonempty (↥(glBlockCentralizer (StatedSp n K).subtype {b} ε) ≃* ↥(StatedSp n₁ K))) ∨
    (∃ (m : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2),
      Nonempty (↥(glBlockCentralizer (StatedSp n K).subtype {b} ε) ≃* GL (Fin m) E)) ∨
    (∃ (m Q : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2), Nat.card E = Q ^ 2 ∧
      Nonempty (↥(glBlockCentralizer (StatedSp n K).subtype {b} ε) ≃* ↥(GUFull m Q E))) := by
  classical
  let G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := Matrix.fromBlocks 0 1 (-1) 0
  have hG : IsUnit G.det := spBlockGram_isUnit_det
  have hGt : Matrix.transpose G = G := spBlockGram_transpose
  have hS : ∀ s ∈ ({b} : Set (GL (Fin n ⊕ Fin n) K)),
      ∀ s' ∈ ({b} : Set (GL (Fin n ⊕ Fin n) K)), Commute s s' := by
    intro s hs s' hs'
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  have hSU : ∀ s ∈ ({b} : Set (GL (Fin n ⊕ Fin n) K)),
      Matrix.transpose (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * G *
        (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = G := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    simpa [G] using CFSG.Open.StatedAPI.mem_statedSp_iff.mp hb
  have hSUmap : ∀ s ∈ ({b} : Set (GL (Fin n ⊕ Fin n) K)),
      Matrix.transpose ((s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).map
        (RingHom.id K)) * G * (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = G := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    simpa [G] using spBlockGram_isometry hb
  obtain ⟨e, he, heε, -⟩ := exists_isPrimIdemIn_of_isPrimAdjIdemIn (RingHom.id K)
    (fun _ => rfl) (G := G) hG (by simpa [Matrix.map_id] using hGt) hS hSUmap hε
  rcases CFSG.StandardType.TableC.isPrimIdemIn_cases hG hGt hS hSU hε he heε with
    heq | ⟨-, e', he', hne', hεe⟩
  · have heprim : IsPrimIdemIn (Algebra.adjoin K
        (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) ε := heq ▸ he
    by_cases h1 : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε = ε
    · obtain ⟨n₁, -, ⟨iso⟩⟩ := blockGroup_iso_Sp_one b hb hodd hε h1
      exact Or.inl ⟨n₁, ⟨iso⟩⟩
    · exact Or.inr (Or.inr (spBlockGroup_moved_eq_unitary b hb hodd hε heprim h1))
  · exact Or.inr (Or.inl (spBlockGroup_pair_eq_generalLinear b hb hodd hε he he' hne' hεe))

private lemma omegaPolarGram_isometry {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) {b : GL ι K} (hb : b ∈ StatedOmega ⇑Φ) :
    Matrix.transpose ((b : Matrix ι ι K).map (RingHom.id K)) *
      LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ) * (b : Matrix ι ι K) =
      LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ) := by
  have hg : ∀ v : ι → K, Φ (Matrix.mulVec (b : Matrix ι ι K) v) = Φ v :=
    fun v => CFSG.RankThree.GF2n.Smith81.Smith23E1.KFLin.isometry_of_mem_statedOmega
      (f := ⇑Φ) hb v
  have h := CFSG.RankThree.GF2n.Smith81.Smith23E1.KFLin.gram_invariant (Q := Φ) hg
  simpa [Matrix.map_id,
    CFSG.RankThree.GF2n.Smith81.Smith23E1.KFLin.polarGram_eq_toMatrix₂'] using h

private lemma omegaBlockGroup_fixed_eq_statedOmega {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b)) {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (h1 : (b : Matrix ι ι K) * ε = ε) :
    (∃ (ι₁ : Type) (_ : Fintype ι₁) (_ : DecidableEq ι₁) (Φ₁ : QuadraticForm K (ι₁ → K)),
      (QuadraticMap.polarBilin Φ₁).Nondegenerate ∧
      Nonempty (↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) ≃* ↥(StatedOmega ⇑Φ₁))) ∨
    IsSolvable ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) := by
  obtain ⟨ι₁, hFintype₁, hDecEq₁, Q₁, -, hform, hdisj⟩ :=
    blockGroup_iso_Omega_one Φ hΦ h8 b hb hodd hε h1
  rcases hdisj with ⟨⟨iso⟩, -⟩ | ⟨-, -, hsol, -⟩
  · obtain ⟨Φ₁, hΦ₁eq, hΦ₁nd⟩ := hform
    exact Or.inl ⟨ι₁, hFintype₁, hDecEq₁, Φ₁, hΦ₁nd,
      by rw [hΦ₁eq]; exact ⟨iso⟩⟩
  · exact Or.inr hsol

private lemma omegaBlockGroup_moved_eq_unitary {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b)) {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (heprim : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (h1 : (b : Matrix ι ι K) * ε ≠ ε) :
    ∃ (m Q : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2),
      Nat.card E = Q ^ 2 ∧
      Nonempty (↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) ≃* ↥(GUFull m Q E)) := by
  obtain ⟨d, m, E, hEfield, hEfin, -, hEcard, -, -, ⟨iso⟩⟩ :=
    blockGroup_iso_Omega_unitary Φ hΦ h8 b hb hodd hε heprim h1
  exact
    letI : Field E := hEfield
    letI : Fintype E := hEfin
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    by
      obtain ⟨f, -, hKcard⟩ := FiniteField.card K 2
      have hEtwo : Fintype.card E = 2 ^ (2 * ((f : ℕ) * d)) := by
        rw [hEcard, hKcard, ← pow_mul, ← pow_mul]
        congr 1
        ring
      have hcharE : CharP E 2 := charP_of_card_eq_prime_pow (p := 2)
        (f := 2 * ((f : ℕ) * d)) hEtwo
      refine ⟨m, Fintype.card K ^ d, E, hEfield, Fintype.finite hEfin, hcharE, ?_, ⟨iso⟩⟩
      rw [Nat.card_eq_fintype_card]
      exact hEcard

private lemma omegaBlockGroup_pair_eq_generalLinear {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b)) {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    {e e' : Matrix ι ι K}
    (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e)
    (he' : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e')
    (hne : e ≠ e') (hεe : ε = e + e') :
    ∃ (m : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2),
      Nonempty (↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) ≃* GL (Fin m) E) := by
  obtain ⟨d, m, E, hEfield, hEfin, -, hEcard, -, -, ⟨iso⟩⟩ :=
    blockGroup_iso_Omega_linear Φ hΦ h8 b hb hodd hε he he' hne hεe
  exact
    letI : Field E := hEfield
    letI : Fintype E := hEfin
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    by
      obtain ⟨f, -, hKcard⟩ := FiniteField.card K 2
      have hEtwo : Fintype.card E = 2 ^ ((f : ℕ) * d) := by
        rw [hEcard, hKcard, ← pow_mul]
      have hcharE : CharP E 2 := charP_of_card_eq_prime_pow (p := 2)
        (f := (f : ℕ) * d) hEtwo
      exact ⟨m, E, hEfield, Fintype.finite hEfin, hcharE, ⟨iso⟩⟩

theorem blockGroup_iso_Omega_cases {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b)) {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε) :
    (∃ (ι₁ : Type) (_ : Fintype ι₁) (_ : DecidableEq ι₁) (Φ₁ : QuadraticForm K (ι₁ → K)),
      (QuadraticMap.polarBilin Φ₁).Nondegenerate ∧
      Nonempty (↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) ≃* ↥(StatedOmega ⇑Φ₁))) ∨
    IsSolvable ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) ∨
    (∃ (m : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2),
      Nonempty (↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) ≃* GL (Fin m) E)) ∨
    (∃ (m Q : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2), Nat.card E = Q ^ 2 ∧
      Nonempty (↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) ≃* ↥(GUFull m Q E))) := by
  classical
  let G : Matrix ι ι K := LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)
  have hG : IsUnit G.det := CFSG.StandardType.TableC.polarGram_isUnit_det Φ hΦ
  have hGt : Matrix.transpose G = G := CFSG.StandardType.TableC.polarGram_transpose Φ
  have hS : ∀ s ∈ ({b} : Set (GL ι K)), ∀ s' ∈ ({b} : Set (GL ι K)), Commute s s' := by
    intro s hs s' hs'
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  have hSU : ∀ s ∈ ({b} : Set (GL ι K)),
      Matrix.transpose (s : Matrix ι ι K) * G * (s : Matrix ι ι K) = G := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    simpa [G, Matrix.map_id] using omegaPolarGram_isometry Φ hb
  have hSUmap : ∀ s ∈ ({b} : Set (GL ι K)),
      Matrix.transpose ((s : Matrix ι ι K).map (RingHom.id K)) * G *
        (s : Matrix ι ι K) = G := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    simpa [G] using omegaPolarGram_isometry Φ hb
  obtain ⟨e, he, heε, -⟩ := exists_isPrimIdemIn_of_isPrimAdjIdemIn (RingHom.id K)
    (fun _ => rfl) (G := G) hG (by simpa [Matrix.map_id] using hGt) hS hSUmap hε
  rcases CFSG.StandardType.TableC.isPrimIdemIn_cases hG hGt hS hSU hε he heε with
    heq | ⟨-, e', he', hne', hεe⟩
  · have heprim : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε :=
      heq ▸ he
    by_cases h1 : (b : Matrix ι ι K) * ε = ε
    · rcases omegaBlockGroup_fixed_eq_statedOmega Φ hΦ h8 b hb hodd hε h1 with hΩ | hsol
      · exact Or.inl hΩ
      · exact Or.inr (Or.inl hsol)
    · exact Or.inr (Or.inr (Or.inr
        (omegaBlockGroup_moved_eq_unitary Φ hΦ h8 b hb hodd hε heprim h1)))
  · exact Or.inr (Or.inr (Or.inl
      (omegaBlockGroup_pair_eq_generalLinear Φ hΦ h8 b hb hodd hε he he' hne' hεe)))

theorem ggE0Concl_centralizer_statedSp {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (u : ↥(StatedSp n K)) (hu : Odd (orderOf u)) (C : Subgroup ↥(StatedSp n K))
    (hC : IsComponentOf C (Subgroup.centralizer {u})) :
    GGE0Concl (Subgroup.centralizer {u}) C := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hodd : Odd (orderOf (u : GL (Fin n ⊕ Fin n) K)) := by rwa [Subgroup.orderOf_coe]
  obtain ⟨P, hP, -, -, hc, hsup, -⟩ := centralizer_block_decomp_Sp
    (u : GL (Fin n ⊕ Fin n) K) u.2 hodd
  have hcent : Subgroup.centralizer ({u} : Set ↥(StatedSp n K)) =
      (Subgroup.centralizer {(u : GL (Fin n ⊕ Fin n) K)}).comap (StatedSp n K).subtype := by
    ext g
    simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_subtype,
      Subtype.ext_iff, Subgroup.coe_mul]
  rw [hcent, ← hsup] at hC ⊢
  refine ggE0Concl_biSup P _ hc (fun ε hε C' hC' => ?_) hC
  rcases blockGroup_iso_Sp_cases (u : GL (Fin n ⊕ Fin n) K) u.2 hodd (hP ε hε) with
    ⟨n₁, ⟨e⟩⟩ | ⟨m, E, _, _, _, ⟨e⟩⟩ | ⟨m, Q, E, _, _, _, hE, ⟨e⟩⟩
  · exact ggE0Concl_of_mulEquiv e (fun C hC => ggE0Concl_statedSp C hC) hC'
  · exact ggE0Concl_of_mulEquiv (e.trans Subgroup.topEquiv.symm)
      (fun C hC => ggE0Concl_top_generalLinear C hC) hC'
  · exact ggE0Concl_of_mulEquiv e (fun C hC => ggE0Concl_unitaryFull hE C hC) hC'

theorem ggE0Concl_centralizer_statedOmega {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Finite K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (u : ↥(StatedOmega ⇑Φ)) (hu : Odd (orderOf u)) (C : Subgroup ↥(StatedOmega ⇑Φ))
    (hC : IsComponentOf C (Subgroup.centralizer {u})) :
    GGE0Concl (Subgroup.centralizer {u}) C := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hodd : Odd (orderOf (u : GL ι K)) := by rwa [Subgroup.orderOf_coe]
  obtain ⟨P, hP, -, -, hc, hsup, -⟩ := centralizer_block_decomp_Omega Φ hΦ h8 (u : GL ι K) u.2 hodd
  have hcent : Subgroup.centralizer ({u} : Set ↥(StatedOmega ⇑Φ)) =
      (Subgroup.centralizer {(u : GL ι K)}).comap (StatedOmega ⇑Φ).subtype := by
    ext g
    simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_subtype,
      Subtype.ext_iff, Subgroup.coe_mul]
  rw [hcent, ← hsup] at hC ⊢
  refine ggE0Concl_biSup P _ hc (fun ε hε C' hC' => ?_) hC
  rcases blockGroup_iso_Omega_cases Φ hΦ h8 (u : GL ι K) u.2 hodd (hP ε hε) with
    ⟨ι₁, _, _, Φ₁, hΦ₁, ⟨e⟩⟩ | hsol | ⟨m, E, _, _, _, ⟨e⟩⟩ | ⟨m, Q, E, _, _, _, hE, ⟨e⟩⟩
  · exact ggE0Concl_of_mulEquiv e (fun C hC => ggE0Concl_statedOmega Φ₁ hΦ₁ C hC) hC'
  · exact absurd hC' (ResU3Three.not_isComponentOf_of_isSolvable hsol)
  · exact ggE0Concl_of_mulEquiv (e.trans Subgroup.topEquiv.symm)
      (fun C hC => ggE0Concl_top_generalLinear C hC) hC'
  · exact ggE0Concl_of_mulEquiv e (fun C hC => ggE0Concl_unitaryFull hE C hC) hC'

theorem largeEvenMarking_of_isComponentOf_centralizer_statedOmega {ι K : Type} [Fintype ι]
    [DecidableEq ι] [Field K] [Finite K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (u : ↥(StatedOmega ⇑Φ)) (hu : Odd (orderOf u)) (C : Subgroup ↥(StatedOmega ⇑Φ))
    (hC : IsComponentOf C (Subgroup.centralizer {u})) :
    LargeEvenMarking ↥C (fun _ _ _ _ _ _ => True) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hodd : Odd (orderOf (u : GL ι K)) := by rwa [Subgroup.orderOf_coe]
  obtain ⟨P, hP, -, -, hc, hsup, -⟩ := centralizer_block_decomp_Omega Φ hΦ h8 (u : GL ι K) u.2 hodd
  have hcent : Subgroup.centralizer ({u} : Set ↥(StatedOmega ⇑Φ)) =
      (Subgroup.centralizer {(u : GL ι K)}).comap (StatedOmega ⇑Φ).subtype := by
    ext g
    simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_subtype,
      Subtype.ext_iff, Subgroup.coe_mul]
  rw [hcent, ← hsup] at hC
  obtain ⟨ε, hε, hCε⟩ := exists_isComponentOf_block P _ hc hC
  rcases blockGroup_iso_Omega_cases Φ hΦ h8 (u : GL ι K) u.2 hodd (hP ε hε) with
    ⟨ι₁, _, _, Φ₁, hΦ₁, ⟨e⟩⟩ | hsol | ⟨m, E, _, _, _, ⟨e⟩⟩ | ⟨m, Q, E, _, _, _, hE, ⟨e⟩⟩
  · exact largeEvenMarking_of_isComponentOf_mulEquiv e
      (fun D hD => largeEvenMarking_of_isComponentOf_statedOmega Φ₁ hΦ₁ D hD) hCε
  · exact (ResU3Three.not_isComponentOf_of_isSolvable hsol hCε).elim
  · exact largeEvenMarking_of_isComponentOf_mulEquiv (e.trans Subgroup.topEquiv.symm)
      (fun D hD => largeEvenMarking_of_isComponentOf_top_generalLinear hD) hCε
  · exact largeEvenMarking_of_isComponentOf_mulEquiv e
      (fun D hD => largeEvenMarking_of_isComponentOf_unitaryFull hE hD) hCε

noncomputable def omegaLinearBlockRhoGL {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    (ε : Matrix ι ι K)
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    {m : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2]
    (e : ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε) ≃*
      GL (Fin m) E) :
    ((Subgroup.centralizer ({b} : Set (GL ι K))).comap (StatedOmega ⇑Φ).subtype) →*
      GL (Fin m) E :=
  e.toMonoidHom.comp (omegaBlockHom Φ hΦ h8 b hb hodd ε hε)

theorem omegaLinearBlock_quotientMarking_square {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    (ε : Matrix ι ι K)
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    {m : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2]
    (e : ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε) ≃*
      GL (Fin m) E)
    {C0 : Subgroup ↥(StatedOmega ⇑Φ)}
    (hC0 : IsComponentOf C0
      (glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε))
    (g : ((Subgroup.centralizer ({b} : Set (GL ι K))).comap
      (StatedOmega ⇑Φ).subtype)) (c c' : ↥C0)
    (h : (c' : ↥(StatedOmega ⇑Φ)) =
      (g : ↥(StatedOmega ⇑Φ)) * (c : ↥(StatedOmega ⇑Φ)) *
        (g : ↥(StatedOmega ⇑Φ))⁻¹) :
    TableB.linConjAut (Fin m) E
        (omegaLinearBlockRhoGL Φ hΦ h8 b hb hodd ε hε e g)
        (linearBlockQuotientMarking e hC0 (QuotientGroup.mk c)) =
      linearBlockQuotientMarking e hC0 (QuotientGroup.mk c') := by
  exact linearBlockQuotientMarking_square (H := ↥(StatedOmega ⇑Φ))
    (F := glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε)
    (C := (Subgroup.centralizer ({b} : Set (GL ι K))).comap (StatedOmega ⇑Φ).subtype)
    e hC0 (omegaBlockHom Φ hΦ h8 b hb hodd ε hε)
    (fun g c => by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
        omegaBlockHom_conj Φ hΦ h8 b hb hodd ε hε g c) g c c' h

theorem ggE0Concl_centralizer_statedOmega_strong {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [Finite K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (u : ↥(StatedOmega ⇑Φ)) (hu : Odd (orderOf u)) (C : Subgroup ↥(StatedOmega ⇑Φ))
    (hC : IsComponentOf C (Subgroup.centralizer {u})) :
    Subgroup.centralizer {u} ≤ Subgroup.normalizer (C : Set ↥(StatedOmega ⇑Φ)) ∧
      LargeEvenMarking ↥C (fun lab _R _ I _F θ => GGChevStTag lab ∧
        ∀ ε ∈ Subgroup.centralizer {u}, ∃ φ ∈ I,
          LargeEvenInduces θ (fun l l' : ↥C =>
            (l' : ↥(StatedOmega ⇑Φ)) = ε⁻¹ * l * ε) φ) := by
  obtain ⟨hnorm, hact⟩ := ggE0Concl_centralizer_statedOmega Φ hΦ h8 u hu C hC
  exact ⟨hnorm, hact
    (largeEvenMarking_of_isComponentOf_centralizer_statedOmega Φ hΦ h8 u hu C hC)⟩

theorem ggAutFixedSubgroup_inner_actor_statedOmega {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [Finite K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (hconj : Function.Injective
      (MulAut.conj : ↥(StatedOmega ⇑Φ) →* MulAut ↥(StatedOmega ⇑Φ)))
    {A : Subgroup (MulAut ↥(StatedOmega ⇑Φ))}
    (hA : (A : Set (MulAut ↥(StatedOmega ⇑Φ))) ⊆ LargeEvenInnSet ↥(StatedOmega ⇑Φ))
    {u : MulAut ↥(StatedOmega ⇑Φ)} (hu : u ∈ A) (huodd : Odd (orderOf u))
    (hcomm : ∀ a ∈ A, Commute a u)
    {C : Subgroup ↥(StatedOmega ⇑Φ)} (hC : IsComponentOf C (ggAutFixedSubgroup u)) :
    (∀ a ∈ A, ∀ c ∈ C, a c ∈ C) ∧
      LargeEvenMarking ↥C (fun _ _ _ I _ θ => GGAutsInduceOn A C θ I) := by
  classical
  obtain ⟨s, hs⟩ := hA hu
  have hord : orderOf u = orderOf s := by
    rw [← hs]
    exact orderOf_injective
      (MulAut.conj : ↥(StatedOmega ⇑Φ) →* MulAut ↥(StatedOmega ⇑Φ)) hconj s
  have hodd : Odd (orderOf s) := hord ▸ huodd
  have hfix : ggAutFixedSubgroup u =
      Subgroup.centralizer ({s} : Set ↥(StatedOmega ⇑Φ)) := by
    rw [← hs]
    exact ggAutFixedSubgroup_mulAut_conj s
  refine ggAutFixedSubgroup_inner_actor hconj hA hs hcomm ?_ hC
  intro C' hC'
  have hC'' : IsComponentOf C' (Subgroup.centralizer ({s} : Set ↥(StatedOmega ⇑Φ))) := by
    rwa [← hfix]
  obtain ⟨hnorm, hmark⟩ :=
    ggE0Concl_centralizer_statedOmega_strong Φ hΦ h8 s hodd C' hC''
  exact ⟨hnorm, largeEvenMarking_mono (fun _ _ _ _ _ _ hθ => hθ.2) hmark⟩

theorem largeEvenMarking_of_isComponentOf_centralizer_statedSp {K : Type} [Field K] [Finite K]
    [CharP K 2] {n : ℕ} (u : ↥(StatedSp n K)) (hu : Odd (orderOf u))
    (C : Subgroup ↥(StatedSp n K)) (hC : IsComponentOf C (Subgroup.centralizer {u})) :
    LargeEvenMarking ↥C (fun _ _ _ _ _ _ => True) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hodd : Odd (orderOf (u : GL (Fin n ⊕ Fin n) K)) := by rwa [Subgroup.orderOf_coe]
  obtain ⟨P, hP, -, -, hc, hsup, -⟩ := centralizer_block_decomp_Sp
    (u : GL (Fin n ⊕ Fin n) K) u.2 hodd
  have hcent : Subgroup.centralizer ({u} : Set ↥(StatedSp n K)) =
      (Subgroup.centralizer {(u : GL (Fin n ⊕ Fin n) K)}).comap (StatedSp n K).subtype := by
    ext g
    simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_subtype,
      Subtype.ext_iff, Subgroup.coe_mul]
  rw [hcent, ← hsup] at hC
  obtain ⟨ε, hε, hCε⟩ := exists_isComponentOf_block P _ hc hC
  rcases blockGroup_iso_Sp_cases (u : GL (Fin n ⊕ Fin n) K) u.2 hodd (hP ε hε) with
    ⟨n₁, ⟨e⟩⟩ | ⟨m, E, _, _, _, ⟨e⟩⟩ | ⟨m, Q, E, _, _, _, hE, ⟨e⟩⟩
  · exact largeEvenMarking_of_isComponentOf_mulEquiv e
      (fun D hD => largeEvenMarking_of_isComponentOf_statedSp D hD) hCε
  · exact largeEvenMarking_of_isComponentOf_mulEquiv (e.trans Subgroup.topEquiv.symm)
      (fun D hD => largeEvenMarking_of_isComponentOf_top_generalLinear hD) hCε
  · exact largeEvenMarking_of_isComponentOf_mulEquiv e
      (fun D hD => largeEvenMarking_of_isComponentOf_unitaryFull hE hD) hCε

end CFSG.StandardType
