module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPSU
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompPSU
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepToral
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepACore
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.HeisenbergRank
public import CFSG.LocalAnalysis.StandardType.GGE0PSUComp
public import CFSG.LocalAnalysis.StandardType.GGE0RigidCount
public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.StandardType.ClassicalPosition
open CFSG.LieType.BorelTits (unitaryInvolution)

private abbrev suId (F : Type) [Field F] (f n : ℕ) : Subgroup (GL (Fin n) F) :=
  CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f F n

private lemma isGLLift_of_mem_suPairs {F : Type} [Field F] {f n : ℕ} {G : Type} [Group G]
    {ψ : ↥(suId F f n) →* G} {e : G} {A : GL (Fin n) F}
    (h : (e, A) ∈ CFSG.StandardType.SUTorus.suPairs ψ) :
    IsGLLift (suId F f n).subtype ψ A e⁻¹ := by
  intro u
  have hu : A * (u : GL (Fin n) F) * A⁻¹ ∈ suId F f n :=
    (Subgroup.mem_normalizer_iff.mp h.1 u).mp u.2
  refine ⟨⟨A * u * A⁻¹, hu⟩, rfl, ?_⟩
  simpa using h.2 u ⟨A * u * A⁻¹, hu⟩ rfl

private lemma isGLLift_of_comp_conj {U₁ U₂ X ι F : Type} [Group U₁] [Group U₂] [Group X]
    [Fintype ι] [DecidableEq ι] [Field F] (j₁ : U₁ →* GL ι F) (j₂ : U₂ →* GL ι F)
    (φ : U₂ ≃* U₁) {A : GL ι F} (hA : ∀ u : U₂, j₁ (φ u) = A * j₂ u * A⁻¹)
    {ψ : U₁ →* X} {s : GL ι F} {b : X}
    (hs : IsGLLift j₂ (ψ.comp φ.toMonoidHom) s b) :
    IsGLLift j₁ ψ (A * s * A⁻¹) b := by
  intro u
  obtain ⟨u₂, hu₂j, hu₂b⟩ := hs (φ.symm u)
  refine ⟨φ u₂, ?_, ?_⟩
  · have h1 := hA (φ.symm u)
    rw [φ.apply_symm_apply] at h1
    rw [hA u₂, hu₂j, h1]
    group
  · simpa using hu₂b

private theorem suFieldData {F : Type} [Field F] {f : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2)
    (hf : 1 ≤ f) : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F :=
  ⟨Nat.prime_two, hf, by rw [hc, ← pow_mul, mul_comm]⟩

private lemma one_le_of_dvd_two_pow_add_one {f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ f + 1) : 1 ≤ f := by
  rcases Nat.eq_zero_or_pos f with h0 | hpos
  · exfalso
    rw [h0] at hpq
    have h2 : p ∣ 2 := by simpa using hpq
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  · exact hpos

private lemma pow_div_add_one_lt_card {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {N : ℕ}
    (h4 : p ^ 4 ≤ N) (hN : p ^ (n - 3) ≤ N) (hn : 4 ≤ n) : p ^ (n / p + 1) < N := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hdiv : n / p ≤ n / 3 := Nat.div_le_div_left hp3 (by norm_num)
  have hlt : n / 3 + 1 < max 4 (n - 3) := by
    by_cases h8 : n ≤ 8
    · have h2 : n / 3 ≤ 2 := by omega
      omega
    · have h2 : n / 3 < n - 4 := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 3)]
        omega
      omega
  have hmax : p ^ max 4 (n - 3) ≤ N := by
    rcases Nat.le_total 4 (n - 3) with h | h
    · rw [max_eq_right h]; exact hN
    · rw [max_eq_left h]; exact h4
  exact lt_of_lt_of_le (Nat.pow_lt_pow_right hp.one_lt (lt_of_le_of_lt (by omega) hlt)) hmax

private lemma exists_witt_unitary_lifts {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (n : ℕ) (hn : 4 ≤ n) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {B₁ : Subgroup X}
    (hB₁ : ∀ b ∈ B₁, GGPsiInnerDiag (Unitary.rootDatum hc n) ψ b) :
    ∃ (P₀ : GL (Fin n) F) (hP₀ : Unitary.conjTr (unitaryInvolution F 2 f)
        (P₀ : Matrix (Fin n) (Fin n) F) * (P₀ : Matrix (Fin n) (Fin n) F) =
          Unitary.antidiag n),
      ∀ b ∈ B₁, ∃ B' : GL (Fin n) F,
        B' ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary
            (suFieldData hc hf) (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F n) ∧
        (b, B') ∈ CFSG.StandardType.SUTorus.suPairs (SURep.ggFrameU hc ψ P₀ hP₀) := by
  obtain ⟨P₀, hP₀⟩ := Unitary.exists_wittMatrix (p := 2) hc n
  refine ⟨P₀, hP₀, fun b hb => ?_⟩
  obtain ⟨A, hA, hAc⟩ := InnerDiagSU.suInnerDiagConj hc hn X ψ hψ b⁻¹ (hB₁ b⁻¹ (B₁.inv_mem hb))
  refine ⟨P₀ * A * P₀⁻¹,
    SUTorus.mem_primeFormUnitary_of_isIdUnitary (suFieldData hc hf) (InnerDiagSU.isIdUnitary_conj
      hP₀ hA),
    SUTorus.mem_suPairs_transfer P₀ hP₀ (Unitary.SUid_eq_statedSU hc n) hA fun u => ?_⟩
  have := hAc u
  rwa [inv_inv] at this

private lemma exists_diagonal_frame {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (n : ℕ) (hn : 4 ≤ n) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) (hC : Subgroup.centralizer (ψ.range : Set X) = ⊥)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1) {B₁ : Subgroup X}
    (hab : IsElemAbelian p B₁) (hbig : p ^ (n / p + 1) < Nat.card B₁)
    {P₀ : GL (Fin n) F} (hP₀ : Unitary.conjTr (unitaryInvolution F 2 f)
      (P₀ : Matrix (Fin n) (Fin n) F) * (P₀ : Matrix (Fin n) (Fin n) F) = Unitary.antidiag n)
    (hEB : ∀ b ∈ B₁, ∃ B' : GL (Fin n) F,
      B' ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary
          (suFieldData hc hf) (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F n) ∧
      (b, B') ∈ CFSG.StandardType.SUTorus.suPairs (SURep.ggFrameU hc ψ P₀ hP₀)) :
    ∃ Q : GL (Fin n) F,
      Q ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary
          (suFieldData hc hf) (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F n) ∧
      ∀ (b : X) (B' : GL (Fin n) F), b ∈ B₁ →
        B' ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary
            (suFieldData hc hf) (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F n) →
        (b, B') ∈ CFSG.StandardType.SUTorus.suPairs (SURep.ggFrameU hc ψ P₀ hP₀) →
        ∃ d : Fin n → Fˣ, Q⁻¹ * B' * Q = CFSG.SectionRank.OddCover.diagHom n d := by
  classical
  have : NeZero n := ⟨by omega⟩
  have hnq : (n, 2 ^ f) ≠ (3, 2) := fun h' => by
    have h1 : n = 3 := congrArg Prod.fst h'
    omega
  have hker₁ : (SURep.ggFrameU hc ψ P₀ hP₀).ker ≤ Subgroup.center ↥(suId F f n) :=
    SURep.ker_ggFrameU_le hc ψ P₀ hP₀ hψ
  have hr₁ : (SURep.ggFrameU hc ψ P₀ hP₀).range = ψ.range := SURep.range_ggFrameU hc ψ P₀ hP₀
  have hEA : ∀ b ∈ B₁, ∃ A, (b, A) ∈
      CFSG.StandardType.SUTorus.suPairs (SURep.ggFrameU hc ψ P₀ hP₀) := by
    intro b hb
    obtain ⟨B', -, hB'⟩ := hEB b hb
    exact ⟨B', hB'⟩
  have hEC : B₁ ⊓ Subgroup.centralizer ((SURep.ggFrameU hc ψ P₀ hP₀).range : Set X) = ⊥ := by
    rw [hr₁, hC, inf_bot_eq]
  have hT := SUTorus.isToral_inducedMatrices (suFieldData hc hf) (by omega) hnq hp hp2 hpq
    hker₁ hab hbig hEA hEC
  obtain ⟨Q, hQ, hQd⟩ := SUTorus.exists_unitary_frame (suFieldData hc hf) (n := n) hp hp2 hpq
    (SUTorus.isProjElem_inducedMatrices (suFieldData hc hf) (by omega) hnq hp hpq hker₁ hab) hT
  exact ⟨Q, hQ, fun b B' hb hB'U hB' =>
    hQd B' (SUTorus.mem_inducedMatrices.mpr ⟨b, hb, hB'⟩) hB'U⟩

private lemma isWitt_mul_inv {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) {n : ℕ} {P₀ Q : GL (Fin n) F}
    (hP₀ : Unitary.conjTr (unitaryInvolution F 2 f) (P₀ : Matrix (Fin n) (Fin n) F) *
      (P₀ : Matrix (Fin n) (Fin n) F) = Unitary.antidiag n)
    (hQ : Q ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary
      (suFieldData hc hf) (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F n)) :
    Unitary.conjTr (unitaryInvolution F 2 f)
        (((Q⁻¹ * P₀ : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) *
      (((Q⁻¹ * P₀ : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) = Unitary.antidiag n := by
  have hQQ : Unitary.conjTr (unitaryInvolution F 2 f)
      (((Q⁻¹ : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) *
      (((Q⁻¹ : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) = 1 := by
    have h1 := (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary).mp
      ((CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary
        (suFieldData hc hf) _).inv_mem hQ)
    rw [CFSG.RankThree.PartOne.KCUnitaryModel.idGram, Units.val_one, Matrix.mul_one] at h1
    rw [SURep.conjTr_eq_bar (suFieldData hc hf)]
    exact h1
  calc Unitary.conjTr (unitaryInvolution F 2 f)
        (((Q⁻¹ * P₀ : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) *
        (((Q⁻¹ * P₀ : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F)
      = Unitary.conjTr (unitaryInvolution F 2 f) (P₀ : Matrix (Fin n) (Fin n) F) *
        (Unitary.conjTr (unitaryInvolution F 2 f) ((Q⁻¹ : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F) * ((Q⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) *
        (P₀ : Matrix (Fin n) (Fin n) F) := by
        rw [Units.val_mul, Unitary.conjTr_mul]; simp only [Matrix.mul_assoc]
    _ = Unitary.conjTr (unitaryInvolution F 2 f) (P₀ : Matrix (Fin n) (Fin n) F) *
        (P₀ : Matrix (Fin n) (Fin n) F) := by rw [hQQ, Matrix.mul_one]
    _ = Unitary.antidiag n := hP₀

private lemma mem_primeFormUnitary_conj {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) {n : ℕ} {Q B' : GL (Fin n) F}
    (hQ : Q ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary
      (suFieldData hc hf) (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F n))
    (hB : B' ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary
      (suFieldData hc hf) (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F n)) :
    Q⁻¹ * B' * Q ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary
      (suFieldData hc hf) (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F n) :=
  (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary (suFieldData hc hf) _).mul_mem
    ((CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary
      (suFieldData hc hf) _).mul_mem
      ((CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary
        (suFieldData hc hf) _).inv_mem hQ) hB) hQ

private lemma mem_suPairs_frame_change {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (n : ℕ) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (unitaryInvolution F 2 f) n) →* X)
    {P₀ Q : GL (Fin n) F} (hP₀ : Unitary.conjTr (unitaryInvolution F 2 f)
      (P₀ : Matrix (Fin n) (Fin n) F) * (P₀ : Matrix (Fin n) (Fin n) F) = Unitary.antidiag n)
    (hQ : Q ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary
      (suFieldData hc hf) (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F n))
    (hP : Unitary.conjTr (unitaryInvolution F 2 f)
      (((Q⁻¹ * P₀ : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) *
      (((Q⁻¹ * P₀ : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) = Unitary.antidiag n) :
    ∀ (b : X) (B' : GL (Fin n) F),
      (b, B') ∈ CFSG.StandardType.SUTorus.suPairs (SURep.ggFrameU hc ψ P₀ hP₀) →
      (b, Q⁻¹ * B' * Q) ∈
        CFSG.StandardType.SUTorus.suPairs (SURep.ggFrameU hc ψ (Q⁻¹ * P₀) hP) := by
  intro b B' hB'
  have hφs : ∀ (s₀ u₀ : ↥(suId F f n)), (u₀ : GL (Fin n) F) = Q * s₀ * Q⁻¹ →
      SURep.ggFrameU hc ψ (Q⁻¹ * P₀) hP s₀ = SURep.ggFrameU hc ψ P₀ hP₀ u₀ := by
    intro s₀ u₀ hu₀
    have hsu : (SURep.ggFrameEquiv hc (Q⁻¹ * P₀) hP).symm s₀ =
        (SURep.ggFrameEquiv hc P₀ hP₀).symm u₀ := by
      apply Subtype.ext
      rw [SURep.coe_ggFrameEquiv_symm, SURep.coe_ggFrameEquiv_symm, hu₀]
      group
    exact (SURep.ggFrameU_apply hc ψ (Q⁻¹ * P₀) hP s₀).trans
      ((congrArg ψ hsu).trans (SURep.ggFrameU_apply hc ψ P₀ hP₀ u₀).symm)
  have hQN := SUTorus.mem_normalizer_of_mem_primeFormUnitary (suFieldData hc hf) hQ
  have hmem := SUTorus.mem_suPairs_frame (suFieldData hc hf) hQ hB'
  rwa [show (SURep.ggFrameU hc ψ P₀ hP₀).comp
      (CFSG.StandardType.TableBUE.conjSU (suFieldData hc hf) Q hQ).symm.toMonoidHom =
    SURep.ggFrameU hc ψ (Q⁻¹ * P₀) hP from MonoidHom.ext fun s₀ => (hφs s₀ _ rfl).symm] at hmem

private lemma diagHom_norm_eq_one_of_mem_primeFormUnitary {F : Type} [Field F] [Finite F]
    [CharP F 2] {f : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) {n : ℕ}
    {d : Fin n → Fˣ}
    (hd : CFSG.SectionRank.OddCover.diagHom n d ∈
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary
        (suFieldData hc hf) (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F n)) :
    ∀ i, unitaryInvolution F 2 f ((d i : F)) * (d i : F) = 1 := by
  have hF := suFieldData hc hf
  have h1 := (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary).mp hd
  rw [CFSG.RankThree.PartOne.KCUnitaryModel.idGram, Units.val_one, Matrix.mul_one,
    CFSG.SectionRank.OddCover.coe_diagHom] at h1
  rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one] at h1
  intro i
  have h3 : hF.bar ((d i : F)) * (d i : F) = 1 := congrFun (Matrix.diagonal_injective h1) i
  rw [show unitaryInvolution F 2 f ((d i : F)) = hF.bar (d i) from by
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply]]
  exact h3

private lemma exists_witt_diagonal_lifts {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) (hn : 4 ≤ n) {X : Type} [Group X] [Finite X]
    (ψ : ↥(Unitary.SU (unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) (hC : Subgroup.centralizer (ψ.range : Set X) = ⊥)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1) {B₁ : Subgroup X}
    (hB₁ : ∀ b ∈ B₁, GGPsiInnerDiag (Unitary.rootDatum hc n) ψ b)
    (hab : IsElemAbelian p B₁) (h4 : p ^ 4 ≤ Nat.card B₁) (hN : p ^ (n - 3) ≤ Nat.card B₁) :
    ∃ R : GL (Fin n) F, Unitary.conjTr (unitaryInvolution F 2 f)
        (R : Matrix (Fin n) (Fin n) F) * (R : Matrix (Fin n) (Fin n) F) = Unitary.antidiag n ∧
      ∀ b ∈ B₁, ∃ d : Fin n → Fˣ,
        (∀ i, unitaryInvolution F 2 f ((d i : F)) * (d i : F) = 1) ∧
        IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ
          (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n d * R) b := by
  classical
  have hf : 1 ≤ f := one_le_of_dvd_two_pow_add_one hp hp2 hpq
  have hbig := pow_div_add_one_lt_card hp hp2 h4 hN hn
  obtain ⟨P₀, hP₀, hEB⟩ := exists_witt_unitary_lifts hc hf n hn ψ hψ hB₁
  obtain ⟨Q, hQ, hQd⟩ := exists_diagonal_frame hc hf n hn ψ hψ hC hp hp2 hpq hab hbig hP₀ hEB
  have hP := isWitt_mul_inv hc hf hP₀ hQ
  refine ⟨Q⁻¹ * P₀, hP, fun b hb => ?_⟩
  obtain ⟨B', hB'U, hB'⟩ := hEB b⁻¹ (B₁.inv_mem hb)
  obtain ⟨d, hd⟩ := hQd b⁻¹ B' (B₁.inv_mem hb) hB'U hB'
  have hDmem : CFSG.SectionRank.OddCover.diagHom n d ∈
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary
        (suFieldData hc hf) (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F n) := by
    rw [← hd]
    exact mem_primeFormUnitary_conj hc hf hQ hB'U
  have hnorm : ∀ i, unitaryInvolution F 2 f ((d i : F)) * (d i : F) = 1 :=
    diagHom_norm_eq_one_of_mem_primeFormUnitary hc hf hDmem
  refine ⟨d, hnorm, ?_⟩
  have hframe : (b⁻¹, CFSG.SectionRank.OddCover.diagHom n d) ∈
      CFSG.StandardType.SUTorus.suPairs (SURep.ggFrameU hc ψ (Q⁻¹ * P₀) hP) := by
    have h := mem_suPairs_frame_change hc hf n ψ hP₀ hQ hP (b⁻¹) B' hB'
    rwa [hd] at h
  simpa only [inv_inv] using
    isGLLift_of_comp_conj (Unitary.SU (unitaryInvolution F 2 f) n).subtype
      (suId F f n).subtype
      (SURep.ggFrameEquiv hc (Q⁻¹ * P₀) hP).symm
      (A := (Q⁻¹ * P₀)⁻¹) (fun u => by
        simpa only [Subgroup.coe_subtype, inv_inv] using
          SURep.coe_ggFrameEquiv_symm hc (Q⁻¹ * P₀) hP u)
      (s := CFSG.SectionRank.OddCover.diagHom n d) (isGLLift_of_mem_suPairs hframe)

private lemma scalar_eq_diagHom {F : Type} [Field F] {n : ℕ} (u : Fˣ) :
    (Matrix.GeneralLinearGroup.scalar (Fin n) u : GL (Fin n) F) =
      CFSG.SectionRank.OddCover.diagHom n (fun _ => u) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, CFSG.SectionRank.OddCover.coe_diagHom,
    Matrix.scalar_apply]

private lemma exists_diagHom_of_inv_mul_eq_scalar {F : Type} [Field F] {n : ℕ}
    {R t : GL (Fin n) F} {d : Fin n → Fˣ} {u : Fˣ}
    (h : t⁻¹ * (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n d * R) =
      Matrix.GeneralLinearGroup.scalar (Fin n) u) :
    ∃ τ : Fin n → Fˣ, R * t * R⁻¹ = CFSG.SectionRank.OddCover.diagHom n τ := by
  have hconj : (R * t * R⁻¹)⁻¹ * CFSG.SectionRank.OddCover.diagHom n d =
      Matrix.GeneralLinearGroup.scalar (Fin n) u := by
    have hc := congrArg (fun x : GL (Fin n) F => R * x * R⁻¹) h
    have h1 : R * (t⁻¹ * (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n d * R)) * R⁻¹ =
        (R * t * R⁻¹)⁻¹ * CFSG.SectionRank.OddCover.diagHom n d := by group
    have h2 : R * Matrix.GeneralLinearGroup.scalar (Fin n) u * R⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin n) u := by
      rw [← (TypeA.PGLTor.commute_scalar u R).eq]
      group
    rw [h1, h2] at hc
    exact hc
  have hD : CFSG.SectionRank.OddCover.diagHom n d =
      (R * t * R⁻¹) * Matrix.GeneralLinearGroup.scalar (Fin n) u := by
    rw [← hconj]
    group
  refine ⟨fun i => d i * u⁻¹, ?_⟩
  have hT : R * t * R⁻¹ =
      CFSG.SectionRank.OddCover.diagHom n d *
        Matrix.GeneralLinearGroup.scalar (Fin n) u⁻¹ := by
    rw [hD]
    have h1 : Matrix.GeneralLinearGroup.scalar (Fin n) u *
        Matrix.GeneralLinearGroup.scalar (Fin n) u⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    rw [show R * t * R⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin n) u *
        Matrix.GeneralLinearGroup.scalar (Fin n) u⁻¹ = R * t * R⁻¹ by
      rw [mul_assoc, h1, mul_one]]
  rw [hT, scalar_eq_diagHom (F := F) (n := n) u⁻¹, ← map_mul]
  rfl

private lemma exists_diagonal_of_isGLLift {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) (hn : 0 < n) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {R : GL (Fin n) F} {B₁ : Subgroup X}
    (hdlift : ∀ b ∈ B₁, ∃ d : Fin n → Fˣ,
      IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ
        (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n d * R) b)
    {z : X} (hz : z ∈ B₁) {t : GL (Fin n) F}
    (ht : IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ t z) :
    ∃ τ : Fin n → Fˣ, R * t * R⁻¹ = CFSG.SectionRank.OddCover.diagHom n τ := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨d, hd⟩ := hdlift z hz
  obtain ⟨γ, hγ⟩ := isGLLift_unique_PSU hc n ψ hψ hd ht
  have hγ0 : γ ≠ 0 := by
    intro h0
    rw [h0] at hγ
    have hunit : IsUnit ((t⁻¹ * (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n d * R) :
        GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
      ⟨t⁻¹ * (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n d * R), rfl⟩
    exact hunit.ne_zero (by simpa [Matrix.scalar_apply] using hγ)
  set u : Fˣ := Units.mk0 γ hγ0
  have hγgl : t⁻¹ * (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n d * R) =
      Matrix.GeneralLinearGroup.scalar (Fin n) u := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar]
    exact hγ
  exact exists_diagHom_of_inv_mul_eq_scalar hγgl

private lemma diagHom_mem_heldGU {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {d : Fin n → Fˣ}
    (hd : ∀ i, unitaryInvolution F 2 f ((d i : F)) * (d i : F) = 1) :
    CFSG.SectionRank.OddCover.diagHom n d ∈
      CFSG.LieType.SemisimpleCentralizers.Held.heldGU n F (unitaryInvolution F 2 f)
        (CFSG.LieType.BorelTits.unitaryInvolution_involutive hc) := by
  rw [CFSG.LieType.SemisimpleCentralizers.Held.mem_heldGU,
    CFSG.SectionRank.OddCover.coe_diagHom, Matrix.diagonal_map (map_zero _),
    Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  have h : (fun i => unitaryInvolution F 2 f ((d i : F)) * (d i : F)) = (fun _ => 1) :=
    funext fun i => hd i
  exact congrArg (fun x : Fin n → F => Matrix.diagonal x) h

private lemma commute_diagHom {F : Type} [Field F] {n : ℕ} {g h : GL (Fin n) F}
    (hg : ∃ d : Fin n → Fˣ, g = CFSG.SectionRank.OddCover.diagHom n d)
    (hh : ∃ e : Fin n → Fˣ, h = CFSG.SectionRank.OddCover.diagHom n e) : Commute g h := by
  obtain ⟨d, rfl⟩ := hg
  obtain ⟨e, rfl⟩ := hh
  show CFSG.SectionRank.OddCover.diagHom n d * CFSG.SectionRank.OddCover.diagHom n e =
    CFSG.SectionRank.OddCover.diagHom n e * CFSG.SectionRank.OddCover.diagHom n d
  rw [← map_mul, ← map_mul, mul_comm]

private lemma smul_single_one {F : Type} [Field F] {n : ℕ} (i : Fin n) (a : F) :
    a • (Pi.single i (1 : F) : Fin n → F) = Pi.single i a := by
  funext r
  by_cases h : r = i <;> simp [h]

private def eigScalarSubgroup {F : Type} [Field F] {n : ℕ} (T : GL (Fin n) F) (lam : F)
    (H : Subgroup (GL (Fin n) F)) : Subgroup (GL (Fin n) F) where
  carrier := {g | g ∈ H ∧ ∃ ν : F, ∀ v : Fin n → F,
    Matrix.mulVec (T : Matrix (Fin n) (Fin n) F) v = lam • v →
      Matrix.mulVec (g : Matrix (Fin n) (Fin n) F) v = ν • v}
  one_mem' := ⟨H.one_mem, 1, fun v _ => by
    rw [Units.val_one, Matrix.one_mulVec, one_smul]⟩
  mul_mem' := by
    rintro g h ⟨hgH, νg, hg⟩ ⟨hhH, νh, hh⟩
    refine ⟨H.mul_mem hgH hhH, νh * νg, fun v hv => ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hh v hv, Matrix.mulVec_smul, hg v hv, smul_smul]
  inv_mem' := by
    rintro g ⟨hgH, ν, hg⟩
    refine ⟨H.inv_mem hgH, ?_⟩
    by_cases hν : ν = 0
    · refine ⟨0, fun v hv => ?_⟩
      have hgv : Matrix.mulVec (g : Matrix (Fin n) (Fin n) F) v = 0 := by
        rw [hg v hv, hν, zero_smul]
      have h1 : Matrix.mulVec ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
          (Matrix.mulVec (g : Matrix (Fin n) (Fin n) F) v) = v := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]
      rw [hgv, Matrix.mulVec_zero] at h1
      have hv0 : v = 0 := h1.symm
      simp [hv0]
    · refine ⟨ν⁻¹, fun v hv => ?_⟩
      have h1 : Matrix.mulVec (g : Matrix (Fin n) (Fin n) F) (ν⁻¹ • v) = v := by
        rw [Matrix.mulVec_smul, hg v hv, smul_smul, inv_mul_cancel₀ hν, one_smul]
      have h2 : Matrix.mulVec ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) v =
          ν⁻¹ • v := by
        conv_lhs => rw [← h1]
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]
      exact h2

private lemma eigScalarSubgroup_normal {F : Type} [Field F] {n : ℕ} {T : GL (Fin n) F} {lam : F}
    {H : Subgroup (GL (Fin n) F)} (hT : H ≤ Subgroup.centralizer {T}) :
    ∀ x ∈ eigScalarSubgroup T lam H, ∀ h ∈ H, h * x * h⁻¹ ∈ eigScalarSubgroup T lam H := by
  rintro x ⟨hxH, ν, hx⟩ h hhH
  have hhT : Commute h T :=
    show h * T = T * h from (Subgroup.mem_centralizer_iff.mp (hT hhH) T (by simp)).symm
  have hhinv : Commute h⁻¹ T := hhT.inv_left
  refine ⟨H.mul_mem (H.mul_mem hhH hxH) (H.inv_mem hhH), ν, fun v hv => ?_⟩
  have hmat : (T : Matrix (Fin n) (Fin n) F) * ((h : Matrix (Fin n) (Fin n) F))⁻¹ =
      ((h : Matrix (Fin n) (Fin n) F))⁻¹ * (T : Matrix (Fin n) (Fin n) F) := by
    have h1 := congrArg (fun y : GL (Fin n) F => (y : Matrix (Fin n) (Fin n) F)) hhinv.eq
    simpa only [Units.val_mul, Matrix.coe_units_inv] using h1.symm
  have hw : Matrix.mulVec (T : Matrix (Fin n) (Fin n) F)
      (Matrix.mulVec ((h : Matrix (Fin n) (Fin n) F))⁻¹ v) = lam •
        Matrix.mulVec ((h : Matrix (Fin n) (Fin n) F))⁻¹ v := by
    rw [Matrix.mulVec_mulVec, hmat, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  have hxv := hx _ hw
  calc Matrix.mulVec ((h * x * h⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) v
      = Matrix.mulVec (h : Matrix (Fin n) (Fin n) F) (Matrix.mulVec
          (x : Matrix (Fin n) (Fin n) F)
          (Matrix.mulVec ((h : Matrix (Fin n) (Fin n) F))⁻¹ v)) := by
        rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, ← Matrix.mulVec_mulVec,
          ← Matrix.mulVec_mulVec]
    _ = Matrix.mulVec (h : Matrix (Fin n) (Fin n) F)
          (ν • Matrix.mulVec ((h : Matrix (Fin n) (Fin n) F))⁻¹ v) := by rw [hxv]
    _ = ν • Matrix.mulVec (h : Matrix (Fin n) (Fin n) F)
          (Matrix.mulVec ((h : Matrix (Fin n) (Fin n) F))⁻¹ v) := by rw [Matrix.mulVec_smul]
    _ = ν • v := by
        rw [Matrix.mulVec_mulVec, ← Matrix.coe_units_inv, ← Units.val_mul, mul_inv_cancel,
          Units.val_one, Matrix.one_mulVec]

private lemma diagHom_mulVec_single {F : Type} [Field F] {n : ℕ} (τ : Fin n → Fˣ)
    (i : Fin n) :
    Matrix.mulVec (CFSG.SectionRank.OddCover.diagHom n τ : Matrix (Fin n) (Fin n) F)
      (Pi.single i 1) = (τ i : F) • Pi.single i 1 := by
  rw [CFSG.SectionRank.OddCover.coe_diagHom, Matrix.diagonal_mulVec_single, mul_one,
    smul_single_one]

private lemma exists_diagHom_of_forall_le_eigScalar {F : Type} [Field F] {n : ℕ}
    {τ : Fin n → Fˣ} {H J : Subgroup (GL (Fin n) F)}
    (hJ : ∀ lam : F, J ≤ eigScalarSubgroup (CFSG.SectionRank.OddCover.diagHom n τ) lam H) :
    ∀ g ∈ J, ∃ d : Fin n → Fˣ, g = CFSG.SectionRank.OddCover.diagHom n d := by
  intro g hg
  have hcol : ∀ i : Fin n, ∃ ν : F, ν ≠ 0 ∧ ∀ r : Fin n,
      (g : Matrix (Fin n) (Fin n) F) r i = if r = i then ν else 0 := by
    intro i
    obtain ⟨ν, hν⟩ := (hJ ((τ i : Fˣ) : F) hg).2
    have hgi := hν (Pi.single i 1) (diagHom_mulVec_single τ i)
    rw [Matrix.mulVec_single_one] at hgi
    refine ⟨ν, ?_, fun r => ?_⟩
    · intro h0
      rw [h0, zero_smul] at hgi
      have h1 : Matrix.mulVec ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
          (Matrix.mulVec (g : Matrix (Fin n) (Fin n) F) (Pi.single i 1)) = Pi.single i 1 := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]
      rw [Matrix.mulVec_single_one, hgi, Matrix.mulVec_zero] at h1
      have h2 := congrFun h1 i
      simp at h2
    · rw [show (g : Matrix (Fin n) (Fin n) F) r i = ((g : Matrix (Fin n) (Fin n) F).col i) r
        from rfl, hgi, Pi.smul_apply]
      by_cases hri : r = i <;> simp [hri]
  choose ν hν0 hνr using hcol
  refine ⟨fun i => Units.mk0 (ν i) (hν0 i), ?_⟩
  apply Units.ext
  rw [CFSG.SectionRank.OddCover.coe_diagHom]
  ext r c
  rw [hνr c r]
  by_cases hrc : r = c
  · subst hrc; rw [if_pos rfl, Matrix.diagonal_apply_eq, Units.val_mk0]
  · rw [if_neg hrc, Matrix.diagonal_apply_ne _ hrc]

private lemma exists_not_le_eigScalar {F : Type} [Field F] {n : ℕ} {τ : Fin n → Fˣ}
    {H J : Subgroup (GL (Fin n) F)}
    (hJq : CFSG.Assembly.IsQuasisimple ↥J) :
    ∃ lam : F, ¬ J ≤ eigScalarSubgroup (CFSG.SectionRank.OddCover.diagHom n τ) lam H := by
  classical
  by_contra hcon
  push Not at hcon
  have hdiag := exists_diagHom_of_forall_le_eigScalar hcon
  have habel : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a := by
    intro a ha b hb
    exact (commute_diagHom (hdiag a ha) (hdiag b hb)).eq
  have hbot : ⁅J, J⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (habel x hx y hy).symm
  exact commutator_ne_bot_of_isQuasisimple hJq hbot


private lemma commute_of_commutator_eq_bot {G : Type*} [Group G] {J N : Subgroup G}
    (h : ⁅J, N⁆ = ⊥) {j : G} (hj : j ∈ J) {n : G} (hn : n ∈ N) : Commute j n :=
  show j * n = n * j from
    (Subgroup.mem_centralizer_iff.mp
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp h) hj) n hn).symm

private lemma diagHom_mem_eigScalar {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {τ : Fin n → Fˣ} {lam : F} {i₀ : Fin n}
    {d : Fin n → Fˣ} (hd : ∀ i, unitaryInvolution F 2 f ((d i : F)) * (d i : F) = 1)
    (hconst : ∀ i : Fin n, τ i = lam → (d i : F) = (d i₀ : F)) :
    CFSG.SectionRank.OddCover.diagHom n d ∈
      eigScalarSubgroup (CFSG.SectionRank.OddCover.diagHom n τ) lam
        (Subgroup.centralizer ({CFSG.SectionRank.OddCover.diagHom n τ} :
          Set (GL (Fin n) F)) ⊓
          CFSG.LieType.SemisimpleCentralizers.Held.heldGU n F (unitaryInvolution F 2 f)
            (CFSG.LieType.BorelTits.unitaryInvolution_involutive hc)) := by
  refine ⟨⟨?_, diagHom_mem_heldGU hc hd⟩, (d i₀ : F), fun v hv => ?_⟩
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact (commute_diagHom ⟨d, rfl⟩ ⟨τ, rfl⟩).eq.symm
  · have hv1 : ∀ i, (τ i : F) * v i = lam * v i := by
      intro i
      have h := congrFun hv i
      rwa [CFSG.SectionRank.OddCover.coe_diagHom, Matrix.mulVec_diagonal,
        Pi.smul_apply] at h
    rw [CFSG.SectionRank.OddCover.coe_diagHom]
    funext i
    rw [Matrix.mulVec_diagonal, Pi.smul_apply]
    by_cases hi : τ i = lam
    · rw [hconst i hi, smul_eq_mul]
    · have hvi : v i = 0 := by
        have h := hv1 i
        have h2 : ((τ i : F) - lam) * v i = 0 := by rw [sub_mul, h, sub_self]
        have h3 : (τ i : F) - lam ≠ 0 := sub_ne_zero.mpr fun h' => hi h'
        exact (mul_eq_zero.mp h2).resolve_left h3
      rw [hvi, mul_zero, smul_zero]

private lemma mem_centralizer_of_lift_commutes {F : Type} [Field F] [Finite F] [CharP F 2]
    {f n : ℕ} {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (unitaryInvolution F 2 f) n) →* X) {b : X} {L : GL (Fin n) F}
    {J' : Subgroup ↥(Unitary.SU (unitaryInvolution F 2 f) n)}
    (hb : IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ L b)
    (hcomm : ∀ u ∈ J', Commute L ((u : GL (Fin n) F))) :
    b ∈ Subgroup.centralizer ((J'.map ψ : Subgroup X) : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨u', hu'j, hu'b⟩ := hb u
  have hu'j' : ((u' : ↥(Unitary.SU (unitaryInvolution F 2 f) n)) : GL (Fin n) F) =
      L * ((u : ↥(Unitary.SU (unitaryInvolution F 2 f) n)) : GL (Fin n) F) * L⁻¹ := by
    simpa only [Subgroup.coe_subtype] using hu'j
  have hL : L * ((u : ↥(Unitary.SU (unitaryInvolution F 2 f) n)) : GL (Fin n) F) * L⁻¹ =
      ((u : ↥(Unitary.SU (unitaryInvolution F 2 f) n)) : GL (Fin n) F) := by
    rw [(hcomm u hu).eq]; group
  have hu' : u' = u := Subtype.ext (by rw [hu'j', hL])
  have h := hu'b
  rw [hu'] at h
  show ψ u * b = b * ψ u
  have h2 : b⁻¹ * ψ u * b = ψ u := h
  calc ψ u * b = b * (b⁻¹ * ψ u * b) := by group
    _ = b * ψ u := by rw [h2]



private lemma exists_scalar_conj_diagHom_ratio {F : Type} [Field F] [Finite F] [CharP F 2]
    {f n : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) (hn : 0 < n) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {R : GL (Fin n) F} {b : X} {d d' : Fin n → Fˣ}
    (h1 : IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ
      (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n d * R) b)
    (h2 : IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ
      (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n d' * R) b) :
    ∃ u : Fˣ, R⁻¹ * CFSG.SectionRank.OddCover.diagHom n (fun i => (d' i)⁻¹ * d i) * R =
      Matrix.GeneralLinearGroup.scalar (Fin n) u := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨a, ha⟩ := isGLLift_unique_PSU hc n ψ hψ h1 h2
  have hDinv : ((CFSG.SectionRank.OddCover.diagHom n d' : GL (Fin n) F)⁻¹) =
      CFSG.SectionRank.OddCover.diagHom n (fun i => (d' i)⁻¹) := (map_inv _ _).symm
  have hmulD : CFSG.SectionRank.OddCover.diagHom n (fun i => (d' i)⁻¹) *
      CFSG.SectionRank.OddCover.diagHom n d =
      CFSG.SectionRank.OddCover.diagHom n (fun i => (d' i)⁻¹ * d i) := by
    rw [← map_mul]; rfl
  have hU : ((R⁻¹ * CFSG.SectionRank.OddCover.diagHom n d' * R)⁻¹ *
      (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n d * R) : GL (Fin n) F) =
      R⁻¹ * CFSG.SectionRank.OddCover.diagHom n (fun i => (d' i)⁻¹ * d i) * R := by
    calc (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n d' * R)⁻¹ *
          (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n d * R)
        = R⁻¹ * ((CFSG.SectionRank.OddCover.diagHom n d')⁻¹ *
            CFSG.SectionRank.OddCover.diagHom n d) * R := by group
      _ = R⁻¹ * CFSG.SectionRank.OddCover.diagHom n (fun i => (d' i)⁻¹ * d i) * R := by
          rw [hDinv, hmulD]
  have ha' : ((R⁻¹ * CFSG.SectionRank.OddCover.diagHom n (fun i => (d' i)⁻¹ * d i) * R :
      GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = Matrix.scalar (Fin n) a := by
    rw [← hU]
    exact ha
  have ha0 : a ≠ 0 := by
    intro h0
    have hunit : IsUnit (((R⁻¹ * CFSG.SectionRank.OddCover.diagHom n
        (fun i => (d' i)⁻¹ * d i) * R) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
      ⟨_, rfl⟩
    have hz : ((R⁻¹ * CFSG.SectionRank.OddCover.diagHom n
        (fun i => (d' i)⁻¹ * d i) * R : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) = 0 := by
      rw [ha', h0, Matrix.scalar_apply, Matrix.diagonal_zero]
    exact hunit.ne_zero hz
  refine ⟨Units.mk0 a ha0, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar]
  exact ha'

private lemma exists_unit_smul_of_conj_diagHom_eq_scalar {F : Type} [Field F] {n : ℕ}
    {R : GL (Fin n) F} {d d' : Fin n → Fˣ} {u : Fˣ}
    (h : R⁻¹ * CFSG.SectionRank.OddCover.diagHom n (fun i => (d' i)⁻¹ * d i) * R =
      Matrix.GeneralLinearGroup.scalar (Fin n) u) :
    ∃ γ : Fˣ, d = fun i => γ * d' i := by
  have hc := congrArg (fun x : GL (Fin n) F => R * x * R⁻¹) h
  have h1 : R * (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n
      (fun i => (d' i)⁻¹ * d i) * R) * R⁻¹ =
      CFSG.SectionRank.OddCover.diagHom n (fun i => (d' i)⁻¹ * d i) := by group
  have h2 : R * Matrix.GeneralLinearGroup.scalar (Fin n) u * R⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin n) u := by
    rw [← (TypeA.PGLTor.commute_scalar u R).eq]
    group
  rw [h1, h2] at hc
  have hD : ((CFSG.SectionRank.OddCover.diagHom n (fun i => (d' i)⁻¹ * d i) :
      GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = Matrix.scalar (Fin n) (u : F) := by
    have := congrArg (fun x : GL (Fin n) F => (x : Matrix (Fin n) (Fin n) F)) hc
    rwa [Matrix.GeneralLinearGroup.coe_scalar] at this
  refine ⟨u, ?_⟩
  funext i
  apply Units.ext
  have hentry : ((↑(d' i))⁻¹ * ↑(d i) : F) = (u : F) := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) F => M i i) hD
    rw [CFSG.SectionRank.OddCover.coe_diagHom, Matrix.diagonal_apply_eq,
      Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h
    simpa using h
  calc (↑(d i) : F) = ↑(d' i) * ((↑(d' i))⁻¹ * ↑(d i)) := by
        rw [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero (d' i)), one_mul]
    _ = ↑(d' i) * (u : F) := by rw [hentry]
    _ = (u : F) * ↑(d' i) := mul_comm _ _

private lemma diagHom_eq_smul_of_isGLLift {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (hn : 0 < n) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {R : GL (Fin n) F} {b : X} {d d' : Fin n → Fˣ}
    (h1 : IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ
      (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n d * R) b)
    (h2 : IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ
      (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n d' * R) b) :
    ∃ γ : Fˣ, d = fun i => γ * d' i := by
  obtain ⟨u, hu⟩ := exists_scalar_conj_diagHom_ratio hc hn ψ hψ h1 h2
  exact exists_unit_smul_of_conj_diagHom_eq_scalar hu

private lemma exists_unit_smul_of_lift_mul {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (hn : 0 < n) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {B₁ : Subgroup X} {R : GL (Fin n) F}
    {dOf : ↥B₁ → (Fin n → Fˣ)}
    (hdlift : ∀ b : ↥B₁, IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ
      (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n (dOf b) * R) (b : X))
    (b b' : ↥B₁) :
    ∃ γ : Fˣ, dOf (b * b') = fun i => γ * (dOf b i * dOf b' i) := by
  have h1 := hdlift (b * b')
  have hD : CFSG.SectionRank.OddCover.diagHom n (fun i => dOf b i * dOf b' i) =
      CFSG.SectionRank.OddCover.diagHom n (dOf b') *
        CFSG.SectionRank.OddCover.diagHom n (dOf b) := by
    rw [← map_mul]
    congr 1
    funext i
    exact mul_comm _ _
  have hmat : (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n (fun i => dOf b i * dOf b' i) * R :
      GL (Fin n) F) = (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n (dOf b') * R) *
        (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n (dOf b) * R) := by
    rw [hD]
    group
  have h2 : IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ
      (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n (fun i => dOf b i * dOf b' i) * R)
      (b * b') := by
    have hm := IsGLLift.mul (hdlift b) (hdlift b')
    rw [← Subgroup.coe_mul, ← hmat] at hm
    exact hm
  exact diagHom_eq_smul_of_isGLLift hc hn ψ hψ h1 h2

private lemma exists_scalar_of_isGLLift_one {F : Type} [Field F] [Finite F] [CharP F 2]
    {f n : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) (hn : 0 < n) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {t : GL (Fin n) F}
    (ht : IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ t 1) :
    ∃ u : Fˣ, t = Matrix.GeneralLinearGroup.scalar (Fin n) u := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨a, ha⟩ := isGLLift_unique_PSU hc n ψ hψ ht (isGLLift_one (ψ := ψ))
  rw [inv_one, one_mul] at ha
  have ha0 : a ≠ 0 := by
    intro h0
    have hunit : IsUnit ((t : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := ⟨t, rfl⟩
    rw [h0, Matrix.scalar_apply, Matrix.diagonal_zero] at ha
    exact hunit.ne_zero ha
  refine ⟨Units.mk0 a ha0, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
  exact ha

private lemma diagHom_pow_entries_eq {F : Type} [Field F] {n p : ℕ} {R : GL (Fin n) F}
    {d : Fin n → Fˣ} {u : Fˣ}
    (hu : (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n d * R) ^ p =
      Matrix.GeneralLinearGroup.scalar (Fin n) u) :
    ∀ j : Fin n, ((d j : F) ^ p) = (u : F) := by
  intro j
  have hL : R * (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n d * R) ^ p * R⁻¹ =
      (CFSG.SectionRank.OddCover.diagHom n d) ^ p := by
    rw [← conj_pow]
    congr 1
    group
  have hR : R * Matrix.GeneralLinearGroup.scalar (Fin n) u * R⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin n) u := by
    rw [← (TypeA.PGLTor.commute_scalar u R).eq]
    group
  have hconj : R * (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n d * R) ^ p * R⁻¹ =
      R * Matrix.GeneralLinearGroup.scalar (Fin n) u * R⁻¹ := by rw [hu]
  rw [hL, hR] at hconj
  have h := congrArg (fun x : GL (Fin n) F => ((x : Matrix (Fin n) (Fin n) F)) j j) hconj
  rw [Units.val_pow_eq_pow_val, CFSG.SectionRank.OddCover.coe_diagHom, Matrix.diagonal_pow,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h
  simpa only [Pi.pow_apply, Matrix.diagonal_apply_eq, Units.val_pow_eq_pow_val] using h

private lemma liftRatio_mul {F : Type} [Field F] {n k : ℕ} {B : Type} [Group B]
    {dOf : B → (Fin n → Fˣ)} {e : Fin k → Fin n} {j₀ : Fin k}
    (hmul : ∀ b b' : B, ∃ γ : Fˣ, dOf (b * b') = fun i => γ * (dOf b i * dOf b' i))
    (b b' : B) :
    (fun j => dOf (b * b') (e j) * (dOf (b * b') (e j₀))⁻¹) =
      (fun j => dOf b (e j) * (dOf b (e j₀))⁻¹) *
        (fun j => dOf b' (e j) * (dOf b' (e j₀))⁻¹) := by
  obtain ⟨γ, hγ⟩ := hmul b b'
  funext j
  show dOf (b * b') (e j) * (dOf (b * b') (e j₀))⁻¹ =
    (dOf b (e j) * (dOf b (e j₀))⁻¹) * (dOf b' (e j) * (dOf b' (e j₀))⁻¹)
  rw [hγ]
  apply Units.ext
  push_cast
  field_simp

private lemma dOf_one_apply_eq {F : Type} [Field F] {n : ℕ} {B : Type} [Group B]
    {dOf : B → (Fin n → Fˣ)}
    (hmul : ∀ b b' : B, ∃ γ : Fˣ, dOf (b * b') = fun i => γ * (dOf b i * dOf b' i))
    (i i₀ : Fin n) : dOf 1 i = dOf 1 i₀ := by
  obtain ⟨γ, hγ⟩ := hmul 1 1
  rw [one_mul] at hγ
  have h1 : (dOf 1 i : F) = (γ : F) * ((dOf 1 i : F) * (dOf 1 i : F)) :=
    congrArg (fun x : Fˣ => (x : F)) (congrFun hγ i)
  have h2 : (dOf 1 i₀ : F) = (γ : F) * ((dOf 1 i₀ : F) * (dOf 1 i₀ : F)) :=
    congrArg (fun x : Fˣ => (x : F)) (congrFun hγ i₀)
  have hx : (dOf 1 i : F) ≠ 0 := Units.ne_zero _
  have hy : (dOf 1 i₀ : F) ≠ 0 := Units.ne_zero _
  have h3 : (γ : F) * (dOf 1 i : F) = 1 := by
    apply mul_right_cancel₀ hx
    rw [one_mul, mul_assoc]
    exact h1.symm
  have h4 : (γ : F) * (dOf 1 i₀ : F) = 1 := by
    apply mul_right_cancel₀ hy
    rw [one_mul, mul_assoc]
    exact h2.symm
  apply Units.ext
  calc (dOf 1 i : F) = (dOf 1 i : F) * 1 := by rw [mul_one]
    _ = (dOf 1 i : F) * ((γ : F) * (dOf 1 i₀ : F)) := by rw [h4]
    _ = ((γ : F) * (dOf 1 i : F)) * (dOf 1 i₀ : F) := by ring
    _ = (dOf 1 i₀ : F) := by rw [h3, one_mul]

private lemma mem_ker_liftRatioHom_iff {F : Type} [Field F] {n k : ℕ} {B : Type} [Group B]
    {dOf : B → (Fin n → Fˣ)} (e : Fin k → Fin n) (j₀ : Fin k)
    {Ψ : B →* GL (Fin k) F}
    (hΨ : ∀ b, Ψ b = CFSG.SectionRank.OddCover.diagHom k
      (fun j => dOf b (e j) * (dOf b (e j₀))⁻¹))
    (b : B) : b ∈ Ψ.ker ↔ ∀ j : Fin k, dOf b (e j) = dOf b (e j₀) := by
  rw [MonoidHom.mem_ker, hΨ b]
  constructor
  · intro h j
    have h1 : (fun j => dOf b (e j) * (dOf b (e j₀))⁻¹) j = 1 := by
      have := congrArg (fun x : GL (Fin k) F => ((x : Matrix (Fin k) (Fin k) F)) j j) h
      rw [CFSG.SectionRank.OddCover.coe_diagHom, Matrix.diagonal_apply_eq,
        Units.val_one, Matrix.one_apply_eq] at this
      exact Units.ext this
    have h2 : dOf b (e j) * (dOf b (e j₀))⁻¹ = 1 := by simpa using h1
    calc dOf b (e j) = dOf b (e j) * (dOf b (e j₀))⁻¹ * dOf b (e j₀) := by group
      _ = dOf b (e j₀) := by rw [h2, one_mul]
  · intro h
    have he : (fun j => dOf b (e j) * (dOf b (e j₀))⁻¹) = 1 := by
      funext j
      show dOf b (e j) * (dOf b (e j₀))⁻¹ = 1
      rw [h j]
      exact mul_inv_cancel _
    rw [he, map_one]

private lemma card_ker_le_card_centralizer {F : Type} [Field F] {X : Type} [Group X]
    [Finite X] {B₁ L' : Subgroup X} {k : ℕ} {Ψ : ↥B₁ →* GL (Fin k) F}
    (hker : ∀ b : ↥B₁, b ∈ Ψ.ker → (b : X) ∈ Subgroup.centralizer (L' : Set X)) :
    Nat.card ↥Ψ.ker ≤ Nat.card ↥(B₁ ⊓ Subgroup.centralizer (L' : Set X)) := by
  have : Finite ↥(B₁ ⊓ Subgroup.centralizer (L' : Set X)) := Subtype.finite
  have hinj : Function.Injective (fun x : ↥Ψ.ker => (⟨((x : ↥B₁) : X),
    Subgroup.mem_inf.mpr ⟨((x : ↥B₁)).2, hker ((x : ↥B₁)) x.2⟩⟩ :
      ↥(B₁ ⊓ Subgroup.centralizer (L' : Set X)))) := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(B₁ ⊓ Subgroup.centralizer (L' : Set X)) => (z : X)) hxy
  exact Nat.card_le_card_of_injective _ hinj

private lemma liftRatioHom_pow_mem_center {F : Type} [Field F] {n k p : ℕ} {B : Type} [Group B]
    {dOf : B → (Fin n → Fˣ)} {e : Fin k → Fin n} {j₀ : Fin k}
    {Ψ : B →* GL (Fin k) F}
    (hΨ : ∀ b, Ψ b = CFSG.SectionRank.OddCover.diagHom k
      (fun j => dOf b (e j) * (dOf b (e j₀))⁻¹))
    (hpow : ∀ (b : B) (i : Fin n), (dOf b i : F) ^ p = (dOf b (e j₀) : F) ^ p)
    {a : GL (Fin k) F} (ha : a ∈ Ψ.range) :
    a ^ p ∈ Subgroup.center (GL (Fin k) F) := by
  obtain ⟨b, rfl⟩ := ha
  have h1 : (CFSG.SectionRank.OddCover.diagHom k
      (fun j => dOf b (e j) * (dOf b (e j₀))⁻¹)) ^ p =
      CFSG.SectionRank.OddCover.diagHom k
        ((fun j => dOf b (e j) * (dOf b (e j₀))⁻¹) ^ p) :=
    (map_pow (CFSG.SectionRank.OddCover.diagHom k) _ p).symm
  have h2 : (fun j => dOf b (e j) * (dOf b (e j₀))⁻¹) ^ p = (1 : Fin k → Fˣ) := by
    funext j
    apply Units.ext
    show (((dOf b (e j) * (dOf b (e j₀))⁻¹ : Fˣ)) : F) ^ p = 1
    have hje : (((dOf b (e j) * (dOf b (e j₀))⁻¹ : Fˣ)) : F) =
        (dOf b (e j) : F) * ((dOf b (e j₀) : F))⁻¹ := by push_cast; ring
    rw [hje, mul_pow, inv_pow, ← hpow b (e j)]
    exact mul_inv_cancel₀ (pow_ne_zero p (Units.ne_zero (dOf b (e j))))
  rw [hΨ b, h1, h2, map_one]
  exact Subgroup.one_mem _

private lemma center_subgroupOf_liftRatio_range_eq_bot {F : Type} [Field F] {n k : ℕ}
    {B : Type} [Group B] {dOf : B → (Fin n → Fˣ)} {e : Fin k → Fin n} {j₀ : Fin k}
    {Ψ : B →* GL (Fin k) F}
    (hΨ : ∀ b, Ψ b = CFSG.SectionRank.OddCover.diagHom k
      (fun j => dOf b (e j) * (dOf b (e j₀))⁻¹)) :
    (Subgroup.center (GL (Fin k) F)).subgroupOf Ψ.range = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨a, ha⟩ hacent
  have h1 : a ∈ Subgroup.center (GL (Fin k) F) := hacent
  obtain ⟨u, hu⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp h1
  obtain ⟨b, rfl⟩ := ha
  rw [hΨ b] at hu
  have h2 : ((CFSG.SectionRank.OddCover.diagHom k
      (fun j => dOf b (e j) * (dOf b (e j₀))⁻¹) : GL (Fin k) F) :
      Matrix (Fin k) (Fin k) F) = Matrix.scalar (Fin k) u := hu.symm
  have h3 : (((fun j => dOf b (e j) * (dOf b (e j₀))⁻¹) j₀ : Fˣ) : F) = u := by
    have h := congrArg (fun M : Matrix (Fin k) (Fin k) F => M j₀ j₀) h2
    rwa [CFSG.SectionRank.OddCover.coe_diagHom, Matrix.diagonal_apply_eq,
      Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h
  have h4 : (fun j => dOf b (e j) * (dOf b (e j₀))⁻¹) j₀ = 1 := by
    show dOf b (e j₀) * (dOf b (e j₀))⁻¹ = 1
    exact mul_inv_cancel _
  have hu1 : u = 1 := by
    rw [← h3]
    exact congrArg (fun x : Fˣ => (x : F)) h4
  apply Subtype.ext
  apply Units.ext
  show ((Ψ b : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) = (1 : Matrix (Fin k) (Fin k) F)
  rw [hΨ b, h2, hu1, Matrix.scalar_apply, Matrix.diagonal_one]

private lemma liftRatio_pow_eq {F : Type} [Field F] [Finite F] [CharP F 2] {f n p : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (hn : 0 < n) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {B₁ : Subgroup X} (hab : IsElemAbelian p B₁)
    {R : GL (Fin n) F} {dOf : ↥B₁ → (Fin n → Fˣ)}
    (hdlift : ∀ b : ↥B₁, IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ
      (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n (dOf b) * R) (b : X))
    (j₀ : Fin n) :
    ∀ (b : ↥B₁) (i : Fin n), (dOf b i : F) ^ p = (dOf b j₀ : F) ^ p := by
  intro b i
  have hbp : (b : X) ^ p = 1 := hab.2 b.1 b.2
  have h1 : IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ
      ((R⁻¹ * CFSG.SectionRank.OddCover.diagHom n (dOf b) * R) ^ p) (1 : X) := by
    have := (hdlift b).pow p
    rwa [hbp] at this
  obtain ⟨u, hu⟩ := exists_scalar_of_isGLLift_one hc hn ψ hψ h1
  rw [diagHom_pow_entries_eq hu i, diagHom_pow_entries_eq hu j₀]

private lemma exists_liftRatioHom {F : Type} [Field F] {n k : ℕ} {B : Type} [Group B]
    {dOf : B → (Fin n → Fˣ)} (e : Fin k → Fin n) (j₀ : Fin k)
    (hmul : ∀ b b' : B, ∃ γ : Fˣ, dOf (b * b') = fun i => γ * (dOf b i * dOf b' i)) :
    ∃ Ψ : B →* GL (Fin k) F, ∀ b,
      Ψ b = CFSG.SectionRank.OddCover.diagHom k
        (fun j => dOf b (e j) * (dOf b (e j₀))⁻¹) := by
  have heOf_mul : ∀ b b' : B, (fun j => dOf (b * b') (e j) * (dOf (b * b') (e j₀))⁻¹) =
      (fun j => dOf b (e j) * (dOf b (e j₀))⁻¹) *
        (fun j => dOf b' (e j) * (dOf b' (e j₀))⁻¹) :=
    fun b b' => liftRatio_mul (e := e) (j₀ := j₀) hmul b b'
  have heOf_one : (fun j => dOf 1 (e j) * (dOf 1 (e j₀))⁻¹) = 1 := by
    funext j
    show dOf 1 (e j) * (dOf 1 (e j₀))⁻¹ = 1
    rw [dOf_one_apply_eq hmul (e j) (e j₀), mul_inv_cancel]
  exact ⟨(CFSG.SectionRank.OddCover.diagHom k).comp
    { toFun := fun b j => dOf b (e j) * (dOf b (e j₀))⁻¹,
      map_one' := heOf_one, map_mul' := heOf_mul }, fun _ => rfl⟩

private lemma card_ker_liftRatioHom_le {F : Type} [Field F] {X : Type} [Group X] [Finite X]
    {B₁ L' : Subgroup X} {n k : ℕ} {dOf : ↥B₁ → (Fin n → Fˣ)} {e : Fin k → Fin n}
    {j₀ : Fin k} {Ψ : ↥B₁ →* GL (Fin k) F}
    (hΨ : ∀ b, Ψ b = CFSG.SectionRank.OddCover.diagHom k
      (fun j => dOf b (e j) * (dOf b (e j₀))⁻¹))
    (hker : ∀ b : ↥B₁, (∀ j : Fin k, dOf b (e j) = dOf b (e j₀)) →
      (b : X) ∈ Subgroup.centralizer (L' : Set X)) :
    Nat.card ↥Ψ.ker ≤ Nat.card ↥(B₁ ⊓ Subgroup.centralizer (L' : Set X)) :=
  card_ker_le_card_centralizer fun b hb =>
    hker b ((mem_ker_liftRatioHom_iff e j₀ hΨ b).mp hb)

private lemma card_range_liftRatioHom_le {F : Type} [Field F] [CharP F 2] {n k p : ℕ}
    {B : Type} [Group B] {dOf : B → (Fin n → Fˣ)} {e : Fin k → Fin n} {j₀ : Fin k}
    {Ψ : B →* GL (Fin k) F} (hp : p.Prime) (hp2 : p ≠ 2)
    (hΨ : ∀ b, Ψ b = CFSG.SectionRank.OddCover.diagHom k
      (fun j => dOf b (e j) * (dOf b (e j₀))⁻¹))
    (hpow : ∀ (b : B) (i : Fin n), (dOf b i : F) ^ p = (dOf b (e j₀) : F) ^ p) :
    Nat.card ↥Ψ.range ≤ p ^ (k - 1) := by
  have hpF : (p : F) ≠ 0 := by
    intro h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      ((CharP.cast_eq_zero_iff F 2 p).mp h0)).symm
  have hle := card_le_of_commute_lifts (K := F) (N := k) (p := p) hpF Ψ.range
    (fun a ha => liftRatioHom_pow_mem_center hΨ hpow ha)
    (by
      rintro a ⟨b, rfl⟩ c ⟨b', rfl⟩
      exact (commute_diagHom ⟨fun j => dOf b (e j) * (dOf b (e j₀))⁻¹, hΨ b⟩
        ⟨fun j => dOf b' (e j) * (dOf b' (e j₀))⁻¹, hΨ b'⟩).eq)
  have hbot := center_subgroupOf_liftRatio_range_eq_bot hΨ
  rw [hbot] at hle
  rwa [Nat.card_congr (QuotientGroup.quotientBot (G := ↥Ψ.range)).toEquiv] at hle

private lemma card_le_of_lift_ratios {F : Type} [Field F] [Finite F] [CharP F 2] {f n p k : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (hn : 0 < n) {X : Type} [Group X] [Finite X]
    (ψ : ↥(Unitary.SU (unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {B₁ : Subgroup X} (hab : IsElemAbelian p B₁)
    (hp : p.Prime) (hp2 : p ≠ 2) {R : GL (Fin n) F} {τ : Fin n → Fˣ} {lam : F}
    (e : Fin k ≃ {i : Fin n // τ i = lam}) (j₀ : Fin k)
    {dOf : ↥B₁ → (Fin n → Fˣ)}
    (hdlift : ∀ b : ↥B₁, IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ
      (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n (dOf b) * R) (b : X))
    {L' : Subgroup X}
    (hker : ∀ b : ↥B₁, (∀ j : Fin k, dOf b (e j) = dOf b (e j₀)) →
      (b : X) ∈ Subgroup.centralizer (L' : Set X)) :
    Nat.card ↥B₁ ≤ Nat.card ↥(B₁ ⊓ Subgroup.centralizer (L' : Set X)) * p ^ (k - 1) := by
  classical
  let e' : Fin k → Fin n := fun j => (e j : Fin n)
  have hmul : ∀ b b' : ↥B₁, ∃ γ : Fˣ, dOf (b * b') = fun i => γ * (dOf b i * dOf b' i) :=
    fun b b' => exists_unit_smul_of_lift_mul hc hn ψ hψ hdlift b b'
  have hpow : ∀ (b : ↥B₁) (i : Fin n), (dOf b i : F) ^ p = (dOf b (e' j₀) : F) ^ p :=
    liftRatio_pow_eq hc hn ψ hψ hab hdlift (e' j₀)
  obtain ⟨Ψ, hΨ_apply⟩ := exists_liftRatioHom (dOf := dOf) e' j₀ hmul
  have hker_card : Nat.card ↥Ψ.ker ≤ Nat.card ↥(B₁ ⊓ Subgroup.centralizer (L' : Set X)) :=
    card_ker_liftRatioHom_le hΨ_apply hker
  have hrange : Nat.card ↥Ψ.range ≤ p ^ (k - 1) :=
    card_range_liftRatioHom_le hp hp2 hΨ_apply hpow
  have hcard := Subgroup.card_ker_mul_card_range Ψ
  rw [← hcard]
  exact Nat.mul_le_mul hker_card hrange

private lemma exists_primitive_scalar_of_not_commute {F : Type} [Field F] [Finite F]
    [CharP F 2] {f : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) (hn : 0 < n) {X : Type}
    [Group X] (ψ : ↥(Unitary.SU (unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {p : ℕ} (hp : p.Prime) {B₁ : Subgroup X}
    (hab : IsElemAbelian p B₁) {z : X} (hz : z ∈ B₁) {c : X} (hcz : Commute c z)
    {s t : GL (Fin n) F}
    (hs : IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ s c)
    (ht : IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ t z)
    (hnc : ¬ Commute s t) :
    ∃ a : F, IsPrimitiveRoot a p ∧
      (((t * s)⁻¹ * (s * t) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        Matrix.scalar (Fin n) a := by
  classical
  have hzpow : z ^ p = 1 := hab.2 z hz
  have hst : IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ (s * t) (z * c) :=
    ht.mul hs
  have hts : IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ (t * s) (c * z) :=
    hs.mul ht
  rw [← hcz.eq] at hst
  obtain ⟨a, ha⟩ := isGLLift_unique_PSU hc n ψ hψ hst hts
  have htp : ∃ μ : F, ((t ^ p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.scalar (Fin n) μ := by
    have hlift : IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ (t ^ p) (1 : X) := by
      rw [← hzpow]
      exact ht.pow p
    obtain ⟨μ, hμ⟩ := isGLLift_unique_PSU hc n ψ hψ hlift
      (isGLLift_one (j := (Unitary.SU (unitaryInvolution F 2 f) n).subtype) (ψ := ψ))
    exact ⟨μ, by simpa using hμ⟩
  have hpa : a ^ p = 1 :=
    @pow_eq_one_of_commutator_eq_scalar (Fin n) F _ _ _ ⟨⟨0, hn⟩⟩ s t a p ha htp
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.pos.ne'] at hpa
    exact zero_ne_one hpa
  have ha1 : a ≠ 1 := by
    intro ha1
    apply hnc
    have hζ : ((t * s)⁻¹ * (s * t) : GL (Fin n) F) = 1 := by
      apply Units.ext
      rw [ha, ha1, map_one, Units.val_one]
    exact (inv_mul_eq_one.mp hζ).symm
  refine ⟨a, ⟨hpa, fun l hl => ?_⟩, ha⟩
  have h1 : orderOf a ∣ l := orderOf_dvd_iff_pow_eq_one.mpr hl
  have h2 : orderOf a ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hpa
  rcases hp.eq_one_or_self_of_dvd (orderOf a) h2 with h3 | h3
  · exact absurd (orderOf_eq_one_iff.mp h3) ha1
  · rwa [h3] at h1

private lemma le_eigScalarSubgroup_of_forall_tau_ne {F : Type} [Field F] {n : ℕ}
    {τ : Fin n → Fˣ} {lam : F} {H : Subgroup (GL (Fin n) F)}
    (h : ∀ i, τ i ≠ lam) : H ≤ eigScalarSubgroup (CFSG.SectionRank.OddCover.diagHom n τ) lam H := by
  intro g hg
  refine ⟨hg, 0, fun v hv => ?_⟩
  have hv0 : v = 0 := by
    funext i
    have h1 : (τ i : F) * v i = lam * v i := by
      simpa [CFSG.SectionRank.OddCover.coe_diagHom, Matrix.mulVec_diagonal] using congrFun hv i
    have h2 : ((τ i : F) - lam) * v i = 0 := by rw [sub_mul, h1, sub_self]
    have h3 : (τ i : F) - lam ≠ 0 := sub_ne_zero.mpr (h i)
    exact (mul_eq_zero.mp h2).resolve_left h3
  rw [hv0, Matrix.mulVec_zero, zero_smul]

private lemma diagHom_mem_eigScalar_of_fiber_constant {F : Type} [Field F] [Finite F] [CharP F 2]
    {f n : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) {τ : Fin n → Fˣ} {lam : F} {d : Fin n → Fˣ}
    (hd : ∀ i, unitaryInvolution F 2 f ((d i : F)) * (d i : F) = 1)
    {k : ℕ} (e : Fin k ≃ {i : Fin n // τ i = lam}) (j₀ : Fin k)
    (hconst : ∀ j : Fin k, d (e j) = d (e j₀)) :
    CFSG.SectionRank.OddCover.diagHom n d ∈
      eigScalarSubgroup (CFSG.SectionRank.OddCover.diagHom n τ) lam
        (Subgroup.centralizer ({CFSG.SectionRank.OddCover.diagHom n τ} :
          Set (GL (Fin n) F)) ⊓
          CFSG.LieType.SemisimpleCentralizers.Held.heldGU n F (unitaryInvolution F 2 f)
            (CFSG.LieType.BorelTits.unitaryInvolution_involutive hc)) := by
  refine diagHom_mem_eigScalar (i₀ := (e j₀ : Fin n)) hc hd ?_
  intro i hi
  have h1 : e (e.symm ⟨i, hi⟩) = ⟨i, hi⟩ := e.apply_symm_apply _
  have h2 : (e (e.symm ⟨i, hi⟩) : Fin n) = i := by rw [h1]
  calc (d i : F) = (d (e (e.symm ⟨i, hi⟩)) : F) := by rw [h2]
    _ = (d (e j₀) : F) := by rw [hconst (e.symm ⟨i, hi⟩)]

private lemma mem_centralizer_of_fiber_constant {F : Type} [Field F] [Finite F] [CharP F 2]
    {f n : ℕ} {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (unitaryInvolution F 2 f) n) →* X)
    {R : GL (Fin n) F} {τ : Fin n → Fˣ} {lam : F} {B₁ L' : Subgroup X}
    {J' : Subgroup ↥(Unitary.SU (unitaryInvolution F 2 f) n)} (hJ'ψ : J'.map ψ = L')
    {k : ℕ} (e : Fin k ≃ {i : Fin n // τ i = lam}) (j₀ : Fin k)
    {N : Subgroup (GL (Fin n) F)} {dOf : ↥B₁ → (Fin n → Fˣ)}
    (hmem : ∀ b : ↥B₁, (∀ j : Fin k, dOf b (e j) = dOf b (e j₀)) →
      CFSG.SectionRank.OddCover.diagHom n (dOf b) ∈ N)
    (hlift : ∀ b : ↥B₁, IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ
      (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n (dOf b) * R) (b : X))
    (hcomm : ⁅J'.map ((MulAut.conj R).toMonoidHom.comp
        (Unitary.SU (unitaryInvolution F 2 f) n).subtype), N⁆ = ⊥) :
    ∀ b : ↥B₁, (∀ j : Fin k, dOf b (e j) = dOf b (e j₀)) →
      (b : X) ∈ Subgroup.centralizer (L' : Set X) := by
  intro b hb
  have hJcomm : ∀ u ∈ J'.map ((MulAut.conj R).toMonoidHom.comp
      (Unitary.SU (unitaryInvolution F 2 f) n).subtype),
      Commute (CFSG.SectionRank.OddCover.diagHom n (dOf b)) u := fun u hu =>
    (commute_of_commutator_eq_bot hcomm hu (hmem b hb)).symm
  have hconj : ∀ u ∈ J', Commute (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n (dOf b) * R)
      ((u : ↥(Unitary.SU (unitaryInvolution F 2 f) n)) : GL (Fin n) F) := by
    intro u hu
    have hju := Subgroup.mem_map_of_mem (K := J')
      ((MulAut.conj R).toMonoidHom.comp
        (Unitary.SU (unitaryInvolution F 2 f) n).subtype) hu
    have hh := hJcomm _ hju
    have hval : (((MulAut.conj R).toMonoidHom.comp
        (Unitary.SU (unitaryInvolution F 2 f) n).subtype) u : GL (Fin n) F) =
        R * ((u : ↥(Unitary.SU (unitaryInvolution F 2 f) n)) : GL (Fin n) F) * R⁻¹ := rfl
    rw [hval] at hh
    have hc := hh.conj R⁻¹
    convert hc using 1
    all_goals group
  have hbcent := mem_centralizer_of_lift_commutes ψ (hlift b) hconj
  rwa [hJ'ψ] at hbcent

private lemma diagonal_mul_eq_smul_of_conj {F : Type} [Field F] {n : ℕ}
    {s t R : GL (Fin n) F} {a : F} (ha0 : a ≠ 0)
    (ha : (((t * s)⁻¹ * (s * t) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.scalar (Fin n) a)
    {τ : Fin n → Fˣ} (hτ : R * t * R⁻¹ = CFSG.SectionRank.OddCover.diagHom n τ) :
    ((R * s * R⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        Matrix.diagonal (fun i => (τ i : F)) =
      a • (Matrix.diagonal (fun i => (τ i : F)) *
        ((R * s * R⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
  classical
  set u : Fˣ := Units.mk0 a ha0 with hu
  have hζ : ((t * s)⁻¹ * (s * t) : GL (Fin n) F) =
      Matrix.GeneralLinearGroup.scalar (Fin n) u := by
    apply Units.ext
    rw [ha, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
  have hconj : (R * ((t * s)⁻¹ * (s * t)) * R⁻¹ : GL (Fin n) F) =
      Matrix.GeneralLinearGroup.scalar (Fin n) u := by
    rw [hζ, ← (TypeA.PGLTor.commute_scalar u R).eq]
    group
  have hDS : (((R * t * R⁻¹) * (R * s * R⁻¹))⁻¹ *
      ((R * s * R⁻¹) * (R * t * R⁻¹)) : GL (Fin n) F) =
      Matrix.GeneralLinearGroup.scalar (Fin n) u := by
    calc (((R * t * R⁻¹) * (R * s * R⁻¹))⁻¹ *
          ((R * s * R⁻¹) * (R * t * R⁻¹)) : GL (Fin n) F)
        = R * ((t * s)⁻¹ * (s * t)) * R⁻¹ := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin n) u := hconj
  rw [hτ] at hDS
  have hSD : (R * s * R⁻¹ : GL (Fin n) F) * CFSG.SectionRank.OddCover.diagHom n τ =
      CFSG.SectionRank.OddCover.diagHom n τ * (R * s * R⁻¹) *
        Matrix.GeneralLinearGroup.scalar (Fin n) u := by
    calc (R * s * R⁻¹ : GL (Fin n) F) * CFSG.SectionRank.OddCover.diagHom n τ
        = (CFSG.SectionRank.OddCover.diagHom n τ * (R * s * R⁻¹)) *
            ((CFSG.SectionRank.OddCover.diagHom n τ * (R * s * R⁻¹))⁻¹ *
              ((R * s * R⁻¹) * CFSG.SectionRank.OddCover.diagHom n τ)) := by group
      _ = (CFSG.SectionRank.OddCover.diagHom n τ * (R * s * R⁻¹)) *
            Matrix.GeneralLinearGroup.scalar (Fin n) u := by rw [hDS]
      _ = CFSG.SectionRank.OddCover.diagHom n τ * (R * s * R⁻¹) *
            Matrix.GeneralLinearGroup.scalar (Fin n) u := rfl
  have hmat := congrArg (fun x : GL (Fin n) F => (x : Matrix (Fin n) (Fin n) F)) hSD
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, hu,
    Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal,
    CFSG.SectionRank.OddCover.coe_diagHom] at hmat
  simpa [CFSG.SectionRank.OddCover.coe_diagHom] using hmat


private lemma exists_frame_of_not_commute {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) (hn : 4 ≤ n) {X : Type} [Group X] [Finite X]
    (ψ : ↥(Unitary.SU (unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) (hC : Subgroup.centralizer (ψ.range : Set X) = ⊥)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1) {B₁ : Subgroup X}
    (hB₁ : ∀ b ∈ B₁, GGPsiInnerDiag (Unitary.rootDatum hc n) ψ b) (hab : IsElemAbelian p B₁)
    (h4 : p ^ 4 ≤ Nat.card B₁) (hN : p ^ (n - 3) ≤ Nat.card B₁) {z : X} (hz : z ∈ B₁)
    {c : X} (hcz : Commute c z) {s t : GL (Fin n) F}
    (hs : IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ s c)
    (ht : IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ t z)
    (hnc : ¬ Commute s t) :
    ∃ (a : F) (R : GL (Fin n) F) (τ : Fin n → Fˣ),
      IsPrimitiveRoot a p ∧
      Unitary.conjTr (unitaryInvolution F 2 f) (R : Matrix (Fin n) (Fin n) F) *
        (R : Matrix (Fin n) (Fin n) F) = Unitary.antidiag n ∧
      R * t * R⁻¹ = CFSG.SectionRank.OddCover.diagHom n τ ∧
      (∀ b ∈ B₁, ∃ d : Fin n → Fˣ,
        (∀ i, unitaryInvolution F 2 f ((d i : F)) * (d i : F) = 1) ∧
        IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ
          (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n d * R) b) ∧
      (((R * s * R⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          Matrix.diagonal (fun i => (τ i : F)) =
        a • (Matrix.diagonal (fun i => (τ i : F)) *
          ((R * s * R⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))) := by
  obtain ⟨a, hroot, ha⟩ :=
    exists_primitive_scalar_of_not_commute hc n (by omega) ψ hψ hp hab hz hcz hs ht hnc
  have ha0 : a ≠ 0 := (hroot.isUnit hp.ne_zero).ne_zero
  obtain ⟨R, hR, hdlift⟩ :=
    exists_witt_diagonal_lifts hc n hn ψ hψ hC hp hp2 hpq hB₁ hab h4 hN
  have hdlift' : ∀ b ∈ B₁, ∃ d : Fin n → Fˣ,
      IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ
        (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n d * R) b := by
    intro b hb
    obtain ⟨d, -, hd⟩ := hdlift b hb
    exact ⟨d, hd⟩
  obtain ⟨τ, hτ⟩ := exists_diagonal_of_isGLLift hc n (by omega) ψ hψ hdlift' hz ht
  exact ⟨a, R, τ, hroot, hR, hτ, hdlift, diagonal_mul_eq_smul_of_conj ha0 ha hτ⟩


private lemma exists_eigScalar_commutator_of_component {F : Type} [Field F] [Finite F]
    [CharP F 2] {f : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) {X : Type}
    [Group X] [Finite X] (ψ : ↥(Unitary.SU (unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {z : X} {L' : Subgroup X}
    (hL' : IsComponentOf L' (ψ.range ⊓ Subgroup.centralizer {z}))
    {t : GL (Fin n) F} (ht : IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ t z)
    {R : GL (Fin n) F}
    (hR : Unitary.conjTr (unitaryInvolution F 2 f) (R : Matrix (Fin n) (Fin n) F) *
      (R : Matrix (Fin n) (Fin n) F) = Unitary.antidiag n)
    {τ : Fin n → Fˣ} (hτ : R * t * R⁻¹ = CFSG.SectionRank.OddCover.diagHom n τ) :
    ∃ (J' : Subgroup ↥(Unitary.SU (unitaryInvolution F 2 f) n)) (lam : F) (i₀ : Fin n),
      J'.map ψ = L' ∧ τ i₀ = lam ∧
      ⁅J'.map ((MulAut.conj R).toMonoidHom.comp
          (Unitary.SU (unitaryInvolution F 2 f) n).subtype),
        eigScalarSubgroup (CFSG.SectionRank.OddCover.diagHom n τ) lam
          (Subgroup.centralizer ({CFSG.SectionRank.OddCover.diagHom n τ} :
            Set (GL (Fin n) F)) ⊓
            CFSG.LieType.SemisimpleCentralizers.Held.heldGU n F (unitaryInvolution F 2 f)
              (CFSG.LieType.BorelTits.unitaryInvolution_involutive hc))⁆ = ⊥ := by
  classical
  obtain ⟨J', -, hJ'comp, hJ'ψ⟩ :=
    ggE0Comp_PSU hc n ψ hψ (P := R) hR (b := z) (s := t) ht (C₀ := L') hL'
  let j : ↥(Unitary.SU (unitaryInvolution F 2 f) n) →* GL (Fin n) F :=
    (MulAut.conj R).toMonoidHom.comp (Unitary.SU (unitaryInvolution F 2 f) n).subtype
  let H : Subgroup (GL (Fin n) F) :=
    Subgroup.centralizer ({CFSG.SectionRank.OddCover.diagHom n τ} : Set (GL (Fin n) F)) ⊓
      CFSG.LieType.SemisimpleCentralizers.Held.heldGU n F (unitaryInvolution F 2 f)
        (CFSG.LieType.BorelTits.unitaryInvolution_involutive hc)
  have hJcomp : IsComponentOf (J'.map j) H := by
    rw [hτ] at hJ'comp
    simpa [H, j] using hJ'comp
  obtain ⟨lam, hlam⟩ := exists_not_le_eigScalar (H := H) (J := J'.map j) hJcomp.2.2
  let N : Subgroup (GL (Fin n) F) :=
    eigScalarSubgroup (CFSG.SectionRank.OddCover.diagHom n τ) lam H
  have hHcent : H ≤ Subgroup.centralizer
      ({CFSG.SectionRank.OddCover.diagHom n τ} : Set (GL (Fin n) F)) := by
    intro x hx
    simpa [H] using hx.1
  have hNle : N ≤ H := by
    intro x hx
    simpa [N] using hx.1
  have hNnormal : (N.subgroupOf H).Normal := by
    refine (Subgroup.normal_subgroupOf_iff hNle).mpr ?_
    intro x y hx hy
    simpa [N] using eigScalarSubgroup_normal (T := CFSG.SectionRank.OddCover.diagHom n τ)
      (lam := lam) (H := H) hHcent x (by simpa [N] using hx) y hy
  have hNsub : IsSubnormal N H := IsSubnormal.step hNle hNnormal (IsSubnormal.refl H)
  have hcommJN : ⁅J'.map j, N⁆ = ⊥ := by
    rcases isComponentOf_le_or_commutator_eq_bot hJcomp hNsub with hle | hbot
    · exact absurd hle hlam
    · exact hbot
  obtain ⟨i₀, hτi₀⟩ : ∃ i₀ : Fin n, τ i₀ = lam := by
    by_contra hcon
    push Not at hcon
    exact hlam (hJcomp.1.trans (le_eigScalarSubgroup_of_forall_tau_ne hcon))
  exact ⟨J', lam, i₀, hJ'ψ, hτi₀, by simpa [j, N, H] using hcommJN⟩

private lemma card_le_pow_of_rigid_component {F : Type} [Field F] [Finite F] [CharP F 2]
    [DecidableEq F] {f : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) (hn : 4 ≤ n)
    {X : Type} [Group X] [Finite X] (ψ : ↥(Unitary.SU (unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B₁ : Subgroup X}
    (hab : IsElemAbelian p B₁) {z : X} {L' : Subgroup X}
    (hL' : IsComponentOf L' (ψ.range ⊓ Subgroup.centralizer {z}))
    (hcent : Nat.card ↥(B₁ ⊓ Subgroup.centralizer (L' : Set X)) ≤ p ^ 2)
    {t : GL (Fin n) F}
    (ht : IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ t z)
    {R : GL (Fin n) F}
    (hR : Unitary.conjTr (unitaryInvolution F 2 f) (R : Matrix (Fin n) (Fin n) F) *
      (R : Matrix (Fin n) (Fin n) F) = Unitary.antidiag n)
    {τ : Fin n → Fˣ} (hτ : R * t * R⁻¹ = CFSG.SectionRank.OddCover.diagHom n τ)
    (hdlift : ∀ b ∈ B₁, ∃ d : Fin n → Fˣ,
      (∀ i, unitaryInvolution F 2 f ((d i : F)) * (d i : F) = 1) ∧
      IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ
        (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n d * R) b) :
    ∃ (k : ℕ) (i₀ : Fin n), 0 < k ∧
      k = (Finset.univ.filter (fun i : Fin n => (τ i : F) = (τ i₀ : F))).card ∧
      Nat.card ↥B₁ ≤ p ^ (k + 1) := by
  classical

  obtain ⟨J', lam, i₀, hJ'ψ, hτi₀, hcommJN⟩ :=
    exists_eigScalar_commutator_of_component hc n ψ hψ hL' ht hR hτ
  let fiber := {i : Fin n // τ i = lam}
  let k := Fintype.card fiber
  let e : Fin k ≃ fiber := (Fintype.equivFin fiber).symm
  let j₀ : Fin k := e.symm ⟨i₀, hτi₀⟩
  let dOf : ↥B₁ → (Fin n → Fˣ) := fun b => (hdlift b.1 b.2).choose
  have hdOf : ∀ b : ↥B₁, ∀ i, unitaryInvolution F 2 f ((dOf b i : F)) * (dOf b i : F) = 1 :=
    fun b i => ((hdlift b.1 b.2).choose_spec).1 i
  have hliftOf : ∀ b : ↥B₁, IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ
      (R⁻¹ * CFSG.SectionRank.OddCover.diagHom n (dOf b) * R) (b : X) :=
    fun b => ((hdlift b.1 b.2).choose_spec).2
  have hmem : ∀ b : ↥B₁, (∀ jj : Fin k, dOf b (e jj) = dOf b (e j₀)) →
      CFSG.SectionRank.OddCover.diagHom n (dOf b) ∈
        eigScalarSubgroup (CFSG.SectionRank.OddCover.diagHom n τ) lam
          (Subgroup.centralizer ({CFSG.SectionRank.OddCover.diagHom n τ} :
            Set (GL (Fin n) F)) ⊓
            CFSG.LieType.SemisimpleCentralizers.Held.heldGU n F (unitaryInvolution F 2 f)
              (CFSG.LieType.BorelTits.unitaryInvolution_involutive hc)) :=
    fun b hb => diagHom_mem_eigScalar_of_fiber_constant hc (hdOf b) e j₀ hb
  have hker : ∀ b : ↥B₁, (∀ jj : Fin k, dOf b (e jj) = dOf b (e j₀)) →
      (b : X) ∈ Subgroup.centralizer (L' : Set X) :=
    mem_centralizer_of_fiber_constant ψ hJ'ψ e j₀ hmem hliftOf hcommJN
  have hcard := card_le_of_lift_ratios (F := F) (f := f) (n := n) (p := p) (k := k)
    hc (by omega) ψ hψ hab hp hp2 (R := R) (τ := τ) (lam := lam) e j₀
    (dOf := dOf) hliftOf (L' := L') hker
  have hkpos : 0 < k := Fintype.card_pos_iff.mpr ⟨⟨i₀, hτi₀⟩⟩
  refine ⟨k, i₀, hkpos, ?_, ?_⟩
  · change Fintype.card fiber =
      (Finset.univ.filter (fun i : Fin n => (τ i : F) = (τ i₀ : F))).card
    rw [Fintype.card_subtype]
    congr 1
    apply Finset.filter_congr
    intro i _
    rw [← hτi₀]
  · calc Nat.card ↥B₁ ≤
        Nat.card ↥(B₁ ⊓ Subgroup.centralizer (L' : Set X)) * p ^ (k - 1) := hcard
      _ ≤ p ^ 2 * p ^ (k - 1) := Nat.mul_le_mul_right _ hcent
      _ = p ^ (k + 1) := by rw [← pow_add]; congr 1; omega

theorem isGLLift_commute_of_rigid_PSU {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) (hn : 4 ≤ n) {X : Type} [Group X] [Finite X]
    (ψ : ↥(Unitary.SU (unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) (hC : Subgroup.centralizer (ψ.range : Set X) = ⊥)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1)
    {B₁ : Subgroup X} (hB₁ : ∀ b ∈ B₁, GGPsiInnerDiag (Unitary.rootDatum hc n) ψ b)
    (hab : IsElemAbelian p B₁) (h4 : p ^ 4 ≤ Nat.card B₁) (hN : p ^ (n - 3) ≤ Nat.card B₁)
    {z : X} (hz : z ∈ B₁) {L' : Subgroup X}
    (hL' : IsComponentOf L' (ψ.range ⊓ Subgroup.centralizer {z}))
    (hcent : Nat.card ↥(B₁ ⊓ Subgroup.centralizer (L' : Set X)) ≤ p ^ 2)
    {c : X} (hcz : Commute c z) {s t : GL (Fin n) F}
    (hs : IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ s c)
    (ht : IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ t z) :
    Commute s t := by
  classical
  by_contra hnc
  obtain ⟨a, R, τ, hroot, hR, hτ, hdlift, hcommSD⟩ :=
    exists_frame_of_not_commute hc n hn ψ hψ hC hp hp2 hpq hB₁ hab h4 hN hz hcz hs ht hnc
  obtain ⟨k, i₀, hkpos, hk_eq, hB_le⟩ :=
    card_le_pow_of_rigid_component hc n hn ψ hψ hp hp2 hab hL' hcent ht hR hτ hdlift
  have hS : IsUnit (((R * s * R⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :=
    ⟨R * s * R⁻¹, rfl⟩
  have hd : ((fun i => (τ i : F)) i₀) ≠ 0 := Units.ne_zero (τ i₀)
  have hleaf := card_mul_card_fiber_le_of_mul_diagonal_eq_smul (ι := Fin n) (F := F)
    hp hroot (fun i => (τ i : F)) i₀ hd hS hcommSD
  have hpk : p * k ≤ n := by
    rw [hk_eq]
    simpa using hleaf
  have hk_le : k ≤ n / p := by
    rw [Nat.le_div_iff_mul_le hp.pos]
    rwa [mul_comm]
  have hpow_le : p ^ (k + 1) ≤ p ^ (n / p + 1) :=
    Nat.pow_le_pow_right hp.pos (by omega)
  exact (not_lt_of_ge (le_trans hB_le hpow_le)) (pow_div_add_one_lt_card hp hp2 h4 hN hn)

end CFSG.StandardType
