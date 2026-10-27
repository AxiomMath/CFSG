module

public import CFSG.RankThree.PartOne.MB3.FieldLmThree
public import CFSG.RankThree.PartOne.N143.JTorus
public import CFSG.Quasithin.Vol2.KGFactC31LieSylGL
public import CFSG.RankThree.PartTwo.Sec21.Item224KFactsProofSL3BT
import CFSG.RankThree.PartOne.KF.ClsD4Torus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Matrix Subgroup Module

open CFSG.RankThree.PartOne.KFOUT3 (SL3 Tor diagSL mem_Tor_iff diagSL_mem_Tor coe_diagSL IsZeta)
open CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3Mat (cycMat cyc cyc_coe)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation toGL_slConjugation)
open CFSG.Quasithin.KGC31 (diagTorusA coe_diagHomA exists_conj_le_diagTorusA)
open CFSG.RankThree.PartOne.N143 (exists_isZeta Tor_pow_eq_one)

variable {K : Type} [Field K] {r : ℕ}

private def fixV (K : Type) [Field K] (B : Subgroup (SL3 K)) : Submodule K (Fin 3 → K) where
  carrier := {v | ∀ b : B, ((b : SL3 K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v}
  add_mem' := by
    intro x y hx hy b
    rw [mulVec_add, hx b, hy b]
  zero_mem' := by
    intro b
    exact mulVec_zero _
  smul_mem' := by
    intro c x hx b
    rw [mulVec_smul, hx b]

private lemma fixedPoints_eq_fixV (B : Subgroup (SL3 K)) :
    (MulAction.fixedPoints B (Fin 3 → K)) = (fixV K B : Set (Fin 3 → K)) := by
  ext v
  rfl

private lemma finrank_eq_three {q d : ℕ} (hr : r.Prime) (hq1 : 1 ≤ q) (hq : ¬ r ∣ q)
    (hr1 : ¬ r ∣ q - 1) (hr2 : ¬ r ∣ q + 1) (hd0 : 0 < d) (hd3 : d ≤ 3)
    (h : q ^ 3 ≡ q ^ d [MOD r]) : d = 3 := by
  have : Fact r.Prime := ⟨hr⟩
  have hq0 : ((q : ZMod r)) ≠ 0 := by
    intro h0
    exact hq ((ZMod.natCast_eq_zero_iff q r).mp h0)
  have hEq : ((q : ZMod r)) ^ 3 = ((q : ZMod r)) ^ d := by
    rw [← Nat.cast_pow, ← Nat.cast_pow, ZMod.natCast_eq_natCast_iff]
    exact h
  interval_cases d
  · exfalso
    have h2 : ((q : ZMod r)) ^ 2 = 1 := by
      refine mul_right_cancel₀ hq0 ?_
      rw [show ((q : ZMod r)) ^ 3 = ((q : ZMod r)) ^ 2 * (q : ZMod r) from by ring] at hEq
      rw [hEq]
      ring
    have h3 : ((q : ZMod r) - 1) * ((q : ZMod r) + 1) = 0 := by
      linear_combination h2
    rcases mul_eq_zero.mp h3 with h' | h'
    · have h1 : ((q : ZMod r)) = 1 := sub_eq_zero.mp h'
      have h0 : ((q - 1 : ℕ) : ZMod r) = 0 := by
        rw [Nat.cast_sub hq1, h1]
        norm_num
      exact hr1 ((ZMod.natCast_eq_zero_iff (q - 1) r).mp h0)
    · have h1 : ((q : ZMod r)) = -1 := eq_neg_of_add_eq_zero_left h'
      have h0 : ((q + 1 : ℕ) : ZMod r) = 0 := by
        push_cast
        rw [h1]
        exact neg_add_cancel 1
      exact hr2 ((ZMod.natCast_eq_zero_iff (q + 1) r).mp h0)
  · exfalso
    have h1 : ((q : ZMod r)) = 1 := by
      refine mul_right_cancel₀ (pow_ne_zero 2 hq0) ?_
      rw [show ((q : ZMod r)) ^ 3 = ((q : ZMod r)) * ((q : ZMod r)) ^ 2 from by ring] at hEq
      rw [hEq]
      ring
    have h0 : ((q - 1 : ℕ) : ZMod r) = 0 := by
      rw [Nat.cast_sub hq1, h1]
      norm_num
    exact hr1 ((ZMod.natCast_eq_zero_iff (q - 1) r).mp h0)
  · rfl

private lemma eigenvalue_eq_one [Finite K] (hr : r.Prime) (hr1 : ¬ r ∣ Nat.card K - 1)
    {M : Matrix (Fin 3) (Fin 3) K} (hMr : M ^ r = 1) {v : Fin 3 → K} (hv : v ≠ 0) {μ : K}
    (hMv : M *ᵥ v = μ • v) : μ = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hpow : ∀ k : ℕ, (M ^ k) *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hMv, Matrix.mulVec_smul, ih, smul_smul, pow_succ]
      rw [mul_comm]
  have hr' := hpow r
  rw [hMr, Matrix.one_mulVec] at hr'
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    exact hv (funext fun i => by simpa using not_exists.mp h i)
  have hμr : μ ^ r = 1 := by
    have := congrFun hr' i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact (mul_left_eq_self₀.mp this.symm).resolve_right hi
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow hr.pos.ne'] at hμr
    exact zero_ne_one hμr
  have hμu : (Units.mk0 μ hμ0 : Kˣ) ^ r = 1 := by
    apply Units.ext
    simpa [Units.val_mk0, Units.val_pow_eq_pow_val] using hμr
  have hμ1 : (Units.mk0 μ hμ0 : Kˣ) = 1 :=
    CFSG.RankThree.PartOne.KFU.eq_one_of_pow_eq_one_of_not_dvd (p := r) hr hr1 hμu
  simpa [Units.val_mk0] using congrArg Units.val hμ1

private lemma eq_bot_of_fixV_eq_top (B : Subgroup (SL3 K)) (h : fixV K B = ⊤) : B = ⊥ := by
  rw [eq_bot_iff]
  intro b hb
  rw [Subgroup.mem_bot]
  have hfix : ∀ v : Fin 3 → K, ((b : SL3 K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v := by
    intro v
    have hv : v ∈ fixV K B := by rw [h]; trivial
    exact hv ⟨b, hb⟩
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  have h1 := congrFun (hfix (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at h1
  simpa [Matrix.one_apply, Pi.single_apply] using h1

private lemma fixV_ne_bot_of_invariant [Finite K] (hr : r.Prime) (hr1 : ¬ r ∣ Nat.card K - 1)
    {B : Subgroup (SL3 K)} (hBr : Nat.card B = r)
    {Z : Submodule K (Fin 3 → K)} (hZbot : Z ≠ ⊥) (hZtop : Z ≠ ⊤)
    (hZ : ∀ s ∈ B, ∀ v ∈ Z, (s : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ Z) :
    fixV K B ≠ ⊥ := by
  intro hfixbot
  have : Fintype K := Fintype.ofFinite K
  have hBne : B ≠ ⊥ := by
    intro h
    rw [h] at hBr
    rw [Subgroup.card_bot] at hBr
    exact hr.ne_one hBr.symm
  obtain ⟨b, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
  have hbr_sub : (b : ↥B) ^ r = 1 := by
    rw [← hBr]
    exact pow_card_eq_one'
  have hbr : (b : SL3 K) ^ r = 1 := by
    simpa using congrArg (fun x : ↥B => (x : SL3 K)) hbr_sub
  have hMr : (((b : SL3 K) : Matrix (Fin 3) (Fin 3) K)) ^ r = 1 := by
    have h := congrArg (fun x : SL3 K => (x : Matrix (Fin 3) (Fin 3) K)) hbr
    simpa [Matrix.SpecialLinearGroup.coe_pow] using h
  have hgen : Subgroup.zpowers (b : SL3 K) = B := by
    have : Fact r.Prime := ⟨hr⟩
    have htop : Subgroup.zpowers b = ⊤ :=
      zpowers_eq_top_of_prime_card (p := r) hBr hb1
    have hmap : (Subgroup.zpowers b).map B.subtype = B := by
      rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [MonoidHom.map_zpowers B.subtype b] at hmap
    simpa using hmap
  obtain ⟨x, hx0, μ, hxμ⟩ :=
    CFSG.RankThree.PartOne.MB3.exists_eigenvector_of_invariant (M :=
      ((b : SL3 K) : Matrix (Fin 3) (Fin 3) K)) hZbot hZtop
      (fun w hw => hZ (b : SL3 K) b.2 w hw)
  have hμ1 : μ = 1 := eigenvalue_eq_one hr hr1 hMr hx0 hxμ
  rw [hμ1, one_smul] at hxμ
  have hxfix : x ∈ fixV K B := by
    have hbstab : (b : SL3 K) ∈ MulAction.stabilizer (SL3 K) x := by
      rw [MulAction.mem_stabilizer_iff, Matrix.SpecialLinearGroup.smul_def]
      exact hxμ
    have hle : Subgroup.zpowers (b : SL3 K) ≤ MulAction.stabilizer (SL3 K) x :=
      Subgroup.zpowers_le.mpr hbstab
    intro g
    have hgb : (g : SL3 K) ∈ Subgroup.zpowers (b : SL3 K) := by
      rw [hgen]
      exact g.2
    have hgstab := hle hgb
    rw [MulAction.mem_stabilizer_iff, Matrix.SpecialLinearGroup.smul_def] at hgstab
    exact hgstab
  rw [hfixbot] at hxfix
  exact hx0 ((Submodule.mem_bot K).mp hxfix)

private lemma finrank_fixV_eq_three [Finite K] (hr : r.Prime) (hrK : ¬ r ∣ Nat.card K)
    (hr1 : ¬ r ∣ Nat.card K - 1) (hr2 : ¬ r ∣ Nat.card K + 1)
    {B : Subgroup (SL3 K)} (hBr : Nat.card B = r) (hfixne : fixV K B ≠ ⊥) :
    finrank K (fixV K B) = 3 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact r.Prime := ⟨hr⟩
  have hBpg : IsPGroup r ↥B := IsPGroup.of_card (n := 1) (by rw [hBr, pow_one])
  have hcardV := hBpg.card_modEq_card_fixedPoints (Fin 3 → K)
  rw [fixedPoints_eq_fixV] at hcardV
  have hmodV : (Nat.card K) ^ (finrank K (Fin 3 → K)) ≡
      (Nat.card K) ^ (finrank K (fixV K B)) [MOD r] := by
    rw [← Module.natCard_eq_pow_finrank (K := K) (V := Fin 3 → K),
      ← Module.natCard_eq_pow_finrank (K := K) (V := fixV K B)]
    exact hcardV
  have hzmodV : ((Nat.card K : ZMod r)) ^ (finrank K (Fin 3 → K)) =
      ((Nat.card K : ZMod r)) ^ (finrank K (fixV K B)) := by
    have h : (((Nat.card K ^ finrank K (Fin 3 → K) : ℕ)) : ZMod r) =
        (((Nat.card K ^ finrank K (fixV K B) : ℕ)) : ZMod r) := by
      rw [ZMod.natCast_eq_natCast_iff]
      exact hmodV
    simpa [Nat.cast_pow] using h
  have hle : finrank K (fixV K B) ≤ 3 := by
    simpa [Module.finrank_fin_fun] using Submodule.finrank_le (fixV K B)
  have hpos : 0 < finrank K (fixV K B) := by
    rcases Nat.eq_zero_or_pos (finrank K (fixV K B)) with h | h
    · exact absurd (Submodule.finrank_eq_zero.mp h) hfixne
    · exact h
  have hcong : Nat.card K ^ 3 ≡ Nat.card K ^ (finrank K (fixV K B)) [MOD r] := by
    refine (ZMod.natCast_eq_natCast_iff (Nat.card K ^ 3)
      (Nat.card K ^ finrank K (fixV K B)) r).mp ?_
    rw [Nat.cast_pow, Nat.cast_pow]
    simpa [Module.finrank_fin_fun] using hzmodV
  exact finrank_eq_three (r := r) hr (by
    have : Nonempty K := ⟨0⟩
    exact Nat.card_pos (α := K)) hrK hr1 hr2 hpos hle hcong

theorem sl3_irreducible_of_prime_of_not_dvd {K : Type} [Field K] [Finite K] {r : ℕ}
    (hr : r.Prime) (hrK : ¬ r ∣ Nat.card K) (hr1 : ¬ r ∣ Nat.card K - 1)
    (hr2 : ¬ r ∣ Nat.card K + 1) {B : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (hBr : Nat.card B = r) (Z : Submodule K (Fin 3 → K))
    (hZ : ∀ s ∈ B, ∀ v ∈ Z, (s : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ Z) : Z = ⊥ ∨ Z = ⊤ := by
  classical
  by_cases hZbot : Z = ⊥
  · exact Or.inl hZbot
  right
  by_contra hZtop
  have hfixne : fixV K B ≠ ⊥ := fixV_ne_bot_of_invariant hr hr1 hBr hZbot hZtop hZ
  have hd3 : finrank K (fixV K B) = 3 := finrank_fixV_eq_three hr hrK hr1 hr2 hBr hfixne
  have hfixVeq : finrank K (fixV K B) = finrank K (Fin 3 → K) := by
    rw [hd3, Module.finrank_fin_fun]
  have hfixVtop : fixV K B = ⊤ := Submodule.eq_top_of_finrank_eq hfixVeq
  have hBbot : B = ⊥ := eq_bot_of_fixV_eq_top B hfixVtop
  rw [hBbot, Subgroup.card_bot] at hBr
  exact hr.ne_one hBr.symm

private lemma cyc_mul_diagSL (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1)
    (hw : ∏ i, (![v 2, v 0, v 1] : Fin 3 → Kˣ) i = 1) :
    cyc * diagSL v hv = diagSL ![v 2, v 0, v 1] hw * cyc := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, cyc_coe,
    coe_diagSL, coe_diagSL]
  have h1 : (diagonal fun i => ((v i : K))) =
      diagonal ![((v 0 : K)), ((v 1 : K)), ((v 2 : K))] := by
    congr 1
    funext i
    fin_cases i <;> rfl
  have h2 : (diagonal fun i => ((![v 2, v 0, v 1] : Fin 3 → Kˣ) i : K)) =
      diagonal ![((v 2 : K)), ((v 0 : K)), ((v 1 : K))] := by
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [h1, h2, CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3Mat.cycMat_mul_diagonal]

private lemma cyc_mem_normalizer_Tor [Finite K] {p : ℕ} :
    cyc ∈ Subgroup.normalizer (Tor p K : Set (SL3 K)) := by
  refine Subgroup.mem_normalizer_fintype fun t ht => ?_
  obtain ⟨v, hv1, hv, rfl⟩ := mem_Tor_iff.1 ht
  let w : Fin 3 → Kˣ := ![v 2, v 0, v 1]
  have hw1 : ∀ i, w i ^ p = 1 := by
    intro i
    fin_cases i <;> simpa [w] using hv1 _
  have hw : ∏ i, w i = 1 := by
    rw [Fin.prod_univ_three]
    simpa [w, Fin.prod_univ_three, mul_comm, mul_assoc, mul_left_comm] using hv
  show cyc * diagSL v hv * (cyc)⁻¹ ∈ Tor p K
  rw [cyc_mul_diagSL v hv hw, mul_assoc, mul_inv_cancel, mul_one]
  exact diagSL_mem_Tor (p := p) w hw1 hw

private lemma mem_Tor_of_mem_diagTorusA {p : ℕ} [Fact p.Prime] {b : SL3 K}
    (hb : Matrix.SpecialLinearGroup.toGL b ∈ diagTorusA (Fin 3) K)
    (hbp : b ^ p = 1) : b ∈ Tor p K := by
  obtain ⟨a, ha⟩ := hb
  have hmat : ((b : SL3 K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal (fun i => (a i : K)) := by
    have h := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) ha
    simpa [coe_diagHomA] using h.symm
  have hap : ∀ i, a i ^ p = 1 := by
    intro i
    have h1 := congrArg (fun x : SL3 K => (x : Matrix (Fin 3) (Fin 3) K)) hbp
    rw [Matrix.SpecialLinearGroup.coe_pow, hmat, Matrix.diagonal_pow,
      Matrix.SpecialLinearGroup.coe_one] at h1
    have h2 := congrFun (congrFun h1 i) i
    simp only [Matrix.diagonal_apply_eq, Pi.pow_apply, Matrix.one_apply_eq] at h2
    exact Units.ext h2
  have hprod : ∏ i, a i = 1 := by
    apply Units.ext
    have hdet := b.2
    rw [hmat, Matrix.det_diagonal] at hdet
    simpa using hdet
  exact mem_Tor_iff.mpr ⟨a, hap, hprod, by
    apply Subtype.ext
    rw [coe_diagSL, hmat]⟩

private lemma slConj_symm_matrix (A : GL (Fin 3) K) (x : SL3 K) :
    (((slConjugation 3 K A).symm x : SL3 K) : Matrix (Fin 3) (Fin 3) K) =
      (A⁻¹ : Matrix (Fin 3) (Fin 3) K) * (x : Matrix (Fin 3) (Fin 3) K) *
        (A : Matrix (Fin 3) (Fin 3) K) := by
  let α : MulAut (SL3 K) := slConjugation 3 K A
  have h := toGL_slConjugation 3 K A (α.symm x)
  rw [show slConjugation 3 K A (α.symm x) = α (α.symm x) from rfl,
    MulEquiv.apply_symm_apply] at h
  have h' : Matrix.SpecialLinearGroup.toGL (α.symm x) =
      A⁻¹ * Matrix.SpecialLinearGroup.toGL x * A := by
    rw [h]; group
  have h'' := congrArg (fun y : GL (Fin 3) K => (y : Matrix (Fin 3) (Fin 3) K)) h'
  rw [Units.val_mul, Units.val_mul] at h''
  simpa [Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using h''

private lemma mem_Tor_of_le_diagTorusA (hr : r.Prime) {B : Subgroup (SL3 K)} {g : GL (Fin 3) K}
    (hBpow : ∀ b ∈ B, b ^ r = 1)
    (hg : ∀ b ∈ B, g * Matrix.SpecialLinearGroup.toGL b * g⁻¹ ∈ diagTorusA (Fin 3) K) :
    ∀ b ∈ B, slConjugation 3 K g b ∈ Tor r K := by
  have : Fact r.Prime := ⟨hr⟩
  intro b hb
  have hmem : Matrix.SpecialLinearGroup.toGL (slConjugation 3 K g b) ∈
      diagTorusA (Fin 3) K := by
    rw [toGL_slConjugation]
    exact hg b hb
  have hbp : (slConjugation 3 K g b) ^ r = 1 := by
    rw [← map_pow, hBpow b hb, map_one]
  exact mem_Tor_of_mem_diagTorusA hmem hbp

private lemma exists_conj_Tor [Finite K] (hr : r.Prime) (hr5 : 5 ≤ r) (hr1 : r ∣ Nat.card K - 1)
    {B : Subgroup (SL3 K)} (hBr : Nat.card B = r) :
    ∃ (g : GL (Fin 3) K) (α : MulAut (SL3 K)),
      α = slConjugation 3 K g ∧ ∀ b ∈ B, α b ∈ Tor r K := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact r.Prime := ⟨hr⟩
  have hBpow : ∀ b ∈ B, b ^ r = 1 := by
    intro b hb
    have hr' : (⟨b, hb⟩ : ↥B) ^ r = 1 := by
      rw [← hBr]
      exact pow_card_eq_one'
    simpa using congrArg Subtype.val hr'
  let R : Subgroup (GL (Fin 3) K) :=
    B.map (Matrix.SpecialLinearGroup.toGL (n := Fin 3) (R := K))
  have hBpg : IsPGroup r ↥B := IsPGroup.of_card (n := 1) (by rw [hBr, pow_one])
  have hR : IsPGroup r ↥R :=
    IsPGroup.map hBpg (Matrix.SpecialLinearGroup.toGL (n := Fin 3) (R := K))
  obtain ⟨g, hg⟩ := exists_conj_le_diagTorusA (ι := Fin 3) (K := K) (ℓ := r)
    (by rw [Fintype.card_fin]; omega)
    (by rw [Fintype.card_eq_nat_card]; exact hr1) hR
  exact ⟨g, slConjugation 3 K g, rfl,
    mem_Tor_of_le_diagTorusA hr hBpow (fun b hb =>
      hg _ (Subgroup.mem_map_of_mem _ hb))⟩

private lemma invariant_of_conj_matrix {g : GL (Fin 3) K} {x : SL3 K}
    {M : Matrix (Fin 3) (Fin 3) K}
    (hβ : (x : Matrix (Fin 3) (Fin 3) K) =
      (g⁻¹ : Matrix (Fin 3) (Fin 3) K) * M * (g : Matrix (Fin 3) (Fin 3) K))
    {Z : Submodule K (Fin 3 → K)} {W : Subgroup (SL3 K)} (hxW : x ∈ W)
    (hZ : ∀ s ∈ W, ∀ z ∈ Z, (s : Matrix (Fin 3) (Fin 3) K) *ᵥ z ∈ Z) :
    ∀ w ∈ Z.map (g : Matrix (Fin 3) (Fin 3) K).mulVecLin,
      M *ᵥ w ∈ Z.map (g : Matrix (Fin 3) (Fin 3) K).mulVecLin := by
  intro w hw
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hw
  have hgg' : (g : Matrix (Fin 3) (Fin 3) K) * (g⁻¹ : Matrix (Fin 3) (Fin 3) K) = 1 := by
    simp
  have hMg : M * (g : Matrix (Fin 3) (Fin 3) K) =
      (g : Matrix (Fin 3) (Fin 3) K) * (x : Matrix (Fin 3) (Fin 3) K) := by
    rw [hβ]
    rw [show (g : Matrix (Fin 3) (Fin 3) K) *
          ((g⁻¹ : Matrix (Fin 3) (Fin 3) K) * M * (g : Matrix (Fin 3) (Fin 3) K))
        = ((g : Matrix (Fin 3) (Fin 3) K) * (g⁻¹ : Matrix (Fin 3) (Fin 3) K)) *
            M * (g : Matrix (Fin 3) (Fin 3) K) by noncomm_ring, hgg', one_mul]
  refine ⟨(x : Matrix (Fin 3) (Fin 3) K) *ᵥ z, hZ x hxW z hz, ?_⟩
  calc (g : Matrix (Fin 3) (Fin 3) K) *ᵥ ((x : Matrix (Fin 3) (Fin 3) K) *ᵥ z)
      = ((g : Matrix (Fin 3) (Fin 3) K) * (x : Matrix (Fin 3) (Fin 3) K)) *ᵥ z :=
          Matrix.mulVec_mulVec z (g : Matrix (Fin 3) (Fin 3) K) _
    _ = (M * (g : Matrix (Fin 3) (Fin 3) K)) *ᵥ z := by rw [← hMg]
    _ = M *ᵥ ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ z) :=
          (Matrix.mulVec_mulVec z M (g : Matrix (Fin 3) (Fin 3) K)).symm

private lemma submodule_eq_top_of_diag_cyc {v : Fin 3 → Kˣ}
    (hv : Function.Injective (fun i => (v i : K))) {Z' : Submodule K (Fin 3 → K)}
    (hne : Z' ≠ ⊥)
    (hD : ∀ w ∈ Z', diagonal (fun i => (v i : K)) *ᵥ w ∈ Z')
    (hC : ∀ w ∈ Z', cycMat *ᵥ w ∈ Z') : Z' = ⊤ := by
  refine CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3BT.eq_top_of_invariant
    (d := fun i => (v i : K)) (c := fun _ => 1) hv ?_ hne hD ?_
  · intro i
    exact one_ne_zero
  · intro w hw
    rw [show cycMat * diagonal (fun _ : Fin 3 => (1 : K)) = cycMat by
      rw [Matrix.diagonal_one, mul_one]]
    exact hC w hw

private lemma isPGroup_comap_Tor (p : ℕ) (α : MulAut (SL3 K)) :
    IsPGroup p ↥((Tor p K).comap α.toMonoidHom) := by
  intro x
  refine ⟨1, ?_⟩
  rw [pow_one]
  have hx : α (x : SL3 K) ∈ Tor p K := x.2
  have hxt : (α (x : SL3 K)) ^ p = 1 := Tor_pow_eq_one hx
  apply Subtype.ext
  change (x : SL3 K) ^ p = 1
  apply α.injective
  rw [map_pow, hxt, map_one]

private lemma conj_mem_normalizer_comap (p : ℕ) (α : MulAut (SL3 K)) {x : SL3 K}
    (hx : x ∈ Tor p K) :
    α.symm x ∈ Subgroup.normalizer ((Tor p K).comap α.toMonoidHom : Set (SL3 K)) := by
  refine Subgroup.le_normalizer ?_
  change α (α.symm x) ∈ Tor p K
  rwa [α.apply_symm_apply]

private lemma conj_cyc_mem_normalizer_comap [Finite K] (p : ℕ) (α : MulAut (SL3 K)) :
    α.symm (cyc) ∈
      Subgroup.normalizer (((Tor p K).comap α.toMonoidHom : Subgroup (SL3 K)) : Set (SL3 K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  change α h ∈ Tor p K ↔ α (α.symm (cyc) * h * (α.symm (cyc))⁻¹) ∈ Tor p K
  rw [show α (α.symm (cyc) * h * (α.symm (cyc))⁻¹) =
      cyc * α h * (cyc)⁻¹ by
    simp only [map_mul, map_inv, α.apply_symm_apply]]
  exact Subgroup.mem_normalizer_iff.mp (cyc_mem_normalizer_Tor (K := K) (p := p)) (α h)

private lemma exists_isZeta_vec [Finite K] (hr : r.Prime) (hr5 : 5 ≤ r) (hr1 : r ∣ Nat.card K - 1) :
    ∃ ζ : Kˣ, IsZeta r ζ ∧
      (∏ i, (![ζ, ζ⁻¹, 1] : Fin 3 → Kˣ) i = 1) ∧
      (∀ i, (![ζ, ζ⁻¹, 1] : Fin 3 → Kˣ) i ^ r = 1) ∧
      Function.Injective (fun i : Fin 3 => ((![ζ, ζ⁻¹, 1] : Fin 3 → Kˣ) i : K)) := by
  obtain ⟨ζ, hζ⟩ := exists_isZeta (p := r) hr hr5 hr1
  have hζ1 : ζ ≠ 1 := fun h => hζ.sq (by rw [h, one_pow])
  have hζinv1 : ζ⁻¹ ≠ 1 := fun h => hζ1 (inv_eq_one.mp h)
  have hζ_ne : ζ ≠ ζ⁻¹ := by
    intro h
    apply hζ.sq
    have h2 : ζ * ζ = 1 := by
      calc ζ * ζ = ζ * ζ⁻¹ := congrArg (fun t => ζ * t) h
        _ = 1 := mul_inv_cancel ζ
    simpa [pow_two] using h2
  refine ⟨ζ, hζ, ?_, ?_, ?_⟩
  · rw [Fin.prod_univ_three]
    simp
  · intro i
    fin_cases i <;> simp [hζ.pow]
  · intro i j hij
    have hu : (![ζ, ζ⁻¹, 1] : Fin 3 → Kˣ) i = (![ζ, ζ⁻¹, 1] : Fin 3 → Kˣ) j := Units.ext hij
    fin_cases i <;> fin_cases j <;> simp_all

private lemma eq_top_of_conj_data [Finite K] {g : GL (Fin 3) K} {W : Subgroup (SL3 K)}
    (hnorm : normalizer (((Tor r K).comap (slConjugation 3 K g).toMonoidHom) : Set (SL3 K)) ≤ W)
    {v : Fin 3 → Kˣ} (hv_prod : ∏ i, v i = 1) (hv_pow : ∀ i, v i ^ r = 1)
    (hv_inj : Function.Injective (fun i => (v i : K)))
    {Z : Submodule K (Fin 3 → K)} (hZbot : Z ≠ ⊥)
    (hZ : ∀ s ∈ W, ∀ z ∈ Z, (s : Matrix (Fin 3) (Fin 3) K) *ᵥ z ∈ Z) :
    Z = ⊤ := by
  let α : MulAut (SL3 K) := slConjugation 3 K g
  let d : SL3 K := diagSL v hv_prod
  let y : SL3 K := cyc
  have hdW : α.symm d ∈ W :=
    hnorm (conj_mem_normalizer_comap r α (diagSL_mem_Tor v hv_pow hv_prod))
  have hyW : α.symm y ∈ W := hnorm (conj_cyc_mem_normalizer_comap r α)
  let gM : Matrix (Fin 3) (Fin 3) K := g
  let Z' : Submodule K (Fin 3 → K) := Z.map gM.mulVecLin
  have hβd : ((α.symm d : SL3 K) : Matrix (Fin 3) (Fin 3) K) =
      (g⁻¹ : Matrix (Fin 3) (Fin 3) K) * diagonal (fun i => (v i : K)) * gM := by
    simpa [α, gM, d, coe_diagSL] using slConj_symm_matrix g d
  have hβy : ((α.symm y : SL3 K) : Matrix (Fin 3) (Fin 3) K) =
      (g⁻¹ : Matrix (Fin 3) (Fin 3) K) * cycMat * gM := by
    simpa [α, gM, y, cyc_coe] using slConj_symm_matrix g y
  have hinvD : ∀ w ∈ Z', diagonal (fun i => (v i : K)) *ᵥ w ∈ Z' :=
    invariant_of_conj_matrix (g := g) (x := α.symm d) (M := diagonal (fun i => (v i : K)))
      hβd hdW hZ
  have hinvC : ∀ w ∈ Z', cycMat *ᵥ w ∈ Z' :=
    invariant_of_conj_matrix (g := g) (x := α.symm y) (M := cycMat) hβy hyW hZ
  have hinj : Function.Injective (gM.mulVecLin) :=
    Matrix.mulVec_injective_iff_isUnit.mpr (Units.isUnit g)
  have hZ'ne : Z' ≠ ⊥ := by
    intro hbot
    apply hZbot
    exact Submodule.map_injective_of_injective hinj
      (by rw [show Submodule.map gM.mulVecLin Z = Z' from rfl, hbot, Submodule.map_bot])
  have hZ'top : Z' = ⊤ := submodule_eq_top_of_diag_cyc hv_inj hZ'ne hinvD hinvC
  have hcomap : Z'.comap gM.mulVecLin = Z :=
    Submodule.comap_map_eq_of_injective hinj Z
  rw [hZ'top, Submodule.comap_top] at hcomap
  exact hcomap.symm

theorem sl3_irreducible_of_prime_dvd {K : Type} [Field K] [Finite K] {r : ℕ} (hr : r.Prime)
    (hr5 : 5 ≤ r) (hr1 : r ∣ Nat.card K - 1) {W B : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (hBr : Nat.card B = r)
    (hN : ∀ P : Subgroup (SpecialLinearGroup (Fin 3) K), IsPGroup r ↥P → B ≤ P →
      normalizer (P : Set (SpecialLinearGroup (Fin 3) K)) ≤ W)
    (Z : Submodule K (Fin 3 → K))
    (hZ : ∀ s ∈ W, ∀ v ∈ Z, (s : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ Z) : Z = ⊥ ∨ Z = ⊤ := by
  classical
  by_cases hZbot : Z = ⊥
  · exact Or.inl hZbot
  right
  by_contra hZtop
  obtain ⟨g, α, rfl, hαTor⟩ := exists_conj_Tor hr hr5 hr1 hBr
  let α : MulAut (SL3 K) := slConjugation 3 K g
  let P : Subgroup (SL3 K) := (Tor r K).comap α.toMonoidHom
  have hBP : B ≤ P := hαTor
  have hP : IsPGroup r ↥P := isPGroup_comap_Tor r α
  have hnormP : normalizer (P : Set (SL3 K)) ≤ W := hN P hP hBP
  obtain ⟨ζ, hζ, hv_prod0, hv_pow0, hv_inj0⟩ := exists_isZeta_vec hr hr5 hr1
  let v : Fin 3 → Kˣ := ![ζ, ζ⁻¹, 1]
  have hv_prod : ∏ i, v i = 1 := hv_prod0
  have hv_pow : ∀ i, v i ^ r = 1 := hv_pow0
  have hv_inj : Function.Injective (fun i => (v i : K)) := hv_inj0
  have hZtop' : Z = ⊤ :=
    eq_top_of_conj_data (g := g) (W := W) (v := v) hnormP hv_prod hv_pow hv_inj hZbot hZ
  exact hZtop hZtop'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
