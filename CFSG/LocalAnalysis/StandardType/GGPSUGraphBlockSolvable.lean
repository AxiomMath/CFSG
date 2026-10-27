module

public import CFSG.LocalAnalysis.StandardType.GGPSUGraphAlgebra
public import CFSG.LocalAnalysis.StandardType.GGBlockEmbed
public import CFSG.LocalAnalysis.StandardType.GGHermTools
public import CFSG.LocalAnalysis.StandardType.GGFormTransvection

public section

namespace CFSG.StandardType

open CFSG.StandardType.ClassicalPosition Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.Universal.Unitary

private lemma psuC2d_blockDegree_pos {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) :
    0 < blockDegree (psuAlg B) e := by
  classical
  have hS : ∀ s ∈ ({B} : Set (GL (Fin n) K)), ∀ s' ∈ ({B} : Set (GL (Fin n) K)),
      Commute s s' := by
    intro s hs s' hs'
    simp only [Set.mem_singleton_iff] at hs hs'
    subst hs
    subst hs'
    exact Commute.refl _
  have hodd : ∀ s ∈ ({B} : Set (GL (Fin n) K)), Odd (orderOf s) := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact S.odd
  have heprim : IsPrimIdemIn (psuAlg B) e := (hP.1 e).mp he
  obtain ⟨L, hLfield, hLalg, hLfin, π, hπsurj, hπker, hrank⟩ :=
    exists_blockField (F := K) (ι := Fin n) hS hodd heprim
  rw [← hrank]
  exact Module.finrank_pos

private lemma psuC2d_SL_nontrivial {F : Type} [Field F] {k : ℕ} (hk : 2 ≤ k) :
    Nontrivial (Matrix.SpecialLinearGroup (Fin k) F) := by
  classical
  have h01 : (⟨0, by omega⟩ : Fin k) ≠ ⟨1, by omega⟩ := by
    intro h
    exact absurd (congrArg Fin.val h) (by simp)
  let M : Matrix (Fin k) (Fin k) F := Matrix.of fun i j =>
    if i = j then 1 else if i.val = 0 ∧ j.val = 1 then 1 else 0
  have htri : M.IsUpperTriangular := by
    intro i j hj
    have hji : j < i := hj
    have hne : i ≠ j := by omega
    have hnot : ¬ (i.val = 0 ∧ j.val = 1) := by omega
    simp [M, hne, hnot]
  have hdiag : ∀ i, M i i = 1 := by
    intro i
    simp [M]
  have hdet : M.det = 1 := by
    rw [Matrix.det_of_upperTriangular htri]
    exact Finset.prod_eq_one fun i _ => hdiag i
  let g : Matrix.SpecialLinearGroup (Fin k) F := ⟨M, hdet⟩
  refine ⟨g, 1, ?_⟩
  intro h
  have hval := congrArg (fun x : Matrix.SpecialLinearGroup (Fin k) F =>
    (x : Matrix (Fin k) (Fin k) F)) h
  have h01' := congrFun (congrFun hval ⟨0, by omega⟩) ⟨1, by omega⟩
  simp [g, M, h01] at h01'

private lemma psuC2d_SL_nonsolvable {F : Type} [Field F] [Finite F] {k : ℕ} (hk : 2 ≤ k)
    (hF : 4 ≤ Nat.card F) :
    ¬ Group.IsSolvable (Matrix.SpecialLinearGroup (Fin k) F) := by
  classical
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin k) F) := by
    refine CFSG.LinearGroups.special_linear_isPerfect hk ?_
    by_cases h3 : 3 ≤ k
    · exact Or.inl h3
    · refine Or.inr ?_
      have : Fintype F := Fintype.ofFinite F
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
        (s := (Finset.univ : Finset F)) (n := 4)
        (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hF)
      exact ⟨s, hs⟩
  haveI : Nontrivial (Matrix.SpecialLinearGroup (Fin k) F) := psuC2d_SL_nontrivial hk
  intro hsolv
  exact Group.IsPerfect.not_isSolvable _ hsolv

private lemma psuC2d_sigma_eq_unitaryInvolution {E : Type} [Field E] [Finite E] [CharP E 2]
    (σ : E ≃+* E) (hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ) {Q : ℕ}
    (hQ : Nat.card E = Q ^ 2) :
    ∃ m : ℕ, Q = 2 ^ m ∧ σ = CFSG.LieType.BorelTits.unitaryInvolution E 2 m := by
  classical
  have hσ2 : σ ^ 2 = 1 := by
    ext x
    change σ (σ x) = x
    exact hσ.invol x
  have hσ1 : σ ≠ 1 := by
    intro h
    obtain ⟨c, hc⟩ := hσ.exists_ne
    exact hc (by rw [h]; rfl)
  letI : Fintype E := Fintype.ofFinite E
  obtain ⟨n, -, hcard⟩ := FiniteField.card E 2
  have hcard' : Nat.card E = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hcard
  obtain ⟨e, h, hσe⟩ :=
    CFSG.ComponentClassification.Burgoyne.O.exists_unitaryFieldData_of_involution
      (p := 2) (f := (n : ℕ)) Nat.prime_two (Nat.succ_le_of_lt n.pos) hcard' hσ2 hσ1
  have hcardE : Nat.card E = (2 ^ e) ^ 2 := by
    calc Nat.card E = 2 ^ (2 * e) := h.card
      _ = 2 ^ (e * 2) := by rw [mul_comm]
      _ = (2 ^ e) ^ 2 := by rw [pow_mul, pow_two]
  have hQe : Q = 2 ^ e := by
    exact Nat.pow_left_injective (n := 2) (by norm_num) (hQ.symm.trans hcardE)
  refine ⟨e, hQe, ?_⟩
  have hbar : CFSG.ComponentClassification.Burgoyne.U.barEq h =
      CFSG.LieType.BorelTits.unitaryInvolution E 2 e := by
    ext x
    rw [CFSG.ComponentClassification.Burgoyne.U.barEq_apply, h.bar_apply,
      CFSG.LieType.BorelTits.unitaryInvolution_apply]
  rw [hσe, hbar]

private lemma psuC2d_SUid_nontrivial {E : Type} [Field E] [CharP E 2]
    (σ : E ≃+* E) (hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ)
    {k : ℕ} (hk : 2 ≤ k) : Nontrivial ↥(CFSG.LieType.Universal.Unitary.SUid σ k) := by
  classical
  let i0 : Fin k := ⟨0, by omega⟩
  let i1 : Fin k := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by
    intro h
    exact absurd (congrArg Fin.val h) (by simp [i0, i1])
  let a : Fin k → E := Pi.single i0 1 + Pi.single i1 1
  have hchar : (1 : E) + 1 = 0 := by
    have h2 : (2 : E) = 0 := CharP.cast_eq_zero E 2
    rw [show (2 : E) = 1 + 1 by norm_num] at h2
    exact h2
  have hc : (1 : E) + σ 1 = 0 := by
    rw [map_one]
    exact hchar
  have ha : CFSG.ClassicalGroups.Unitary.herm σ a a = 0 := by
    dsimp only [a]
    rw [CFSG.ClassicalGroups.Unitary.herm_add_left,
      CFSG.ClassicalGroups.Unitary.herm_single_left,
      CFSG.ClassicalGroups.Unitary.herm_single_left]
    simp [h01, hσ.invol, hchar]
  let g : ↥(CFSG.LieType.Universal.Unitary.SUid σ k) :=
    CFSG.ClassicalGroups.Unitary.tv hσ.invol ha hc
  refine ⟨g, 1, ?_⟩
  intro h
  let v : Fin k → E := Pi.single i0 1
  have hv := congrArg (fun x : ↥(CFSG.LieType.Universal.Unitary.SUid σ k) => x • v) h
  rw [CFSG.ClassicalGroups.Unitary.tv_smul hσ.invol ha hc, one_smul] at hv
  have hherm : CFSG.ClassicalGroups.Unitary.herm σ a v = 1 := by
    dsimp only [a, v]
    rw [CFSG.ClassicalGroups.Unitary.herm_add_left,
      CFSG.ClassicalGroups.Unitary.herm_single_left,
      CFSG.ClassicalGroups.Unitary.herm_single_left]
    simp [h01, hσ.invol]
  rw [hherm] at hv
  have h1 := congrFun hv i1
  simp [v, a, i0, i1, h01, Pi.single_eq_same, Pi.single_eq_of_ne] at h1

private lemma psuC2d_SU_equiv_SUid {E : Type} [Field E] [CharP E 2]
    (σ : E ≃+* E) (hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ) (k : ℕ) :
    Nonempty (↥(CFSG.LieType.Universal.Unitary.SU σ k) ≃*
      ↥(CFSG.LieType.Universal.Unitary.SUid σ k)) := by
  classical
  obtain ⟨c, hc⟩ := hσ.exists_ne
  have hchar : (1 : E) + 1 = 0 := by
    have h2 : (2 : E) = 0 := CharP.cast_eq_zero E 2
    rw [show (2 : E) = 1 + 1 by norm_num] at h2
    exact h2
  have hone : (1 : E) = -1 := eq_neg_of_add_eq_zero_left hchar
  have hc0 : c ≠ 0 := by
    intro h0
    exact hc (by rw [h0, map_zero])
  have hσc0 : σ c ≠ 0 := fun h0 => hc0 (σ.injective (by rw [h0, map_zero]))
  let ω : E := c * (σ c)⁻¹
  have hω : σ ω * ω = 1 := by
    dsimp only [ω]
    rw [map_mul, map_inv₀, hσ.invol]
    field_simp [hc0, hσc0]
  have hω1 : ω ≠ 1 := by
    intro h
    apply hc
    dsimp only [ω] at h
    rw [mul_inv_eq_one₀ hσc0] at h
    exact h.symm
  have hu : σ (1 : E) * 1 = -1 := by
    simpa only [map_one, one_mul] using hone
  obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix_of σ hu hω hω1
  exact ⟨CFSG.LieType.Universal.Unitary.conjEquiv P hP⟩

private lemma psuC2d_SU_nonsolvable {E : Type} [Field E] [Finite E] [CharP E 2] (σ : E ≃+* E)
    (hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ) {k Q : ℕ}
    (hQ : Nat.card E = Q ^ 2) (hk : 2 ≤ k) (hex : ¬ (Q = 2 ∧ (k = 2 ∨ k = 3))) :
    ¬ Group.IsSolvable ↥(SU σ k) := by
  classical
  obtain ⟨m, hQm, hσm⟩ := psuC2d_sigma_eq_unitaryInvolution σ hσ hQ
  rw [hσm]
  have hK : Nat.card E = (2 ^ m) ^ 2 := by rw [hQ, hQm]
  have hσ' : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution
      (CFSG.LieType.BorelTits.unitaryInvolution E 2 m) :=
    CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨eSU⟩ := psuC2d_SU_equiv_SUid
    (CFSG.LieType.BorelTits.unitaryInvolution E 2 m) hσ' k
  by_cases hk2 : k = 2
  · subst k
    have hchar : (1 : E) + 1 = 0 := by
      have h2 : (2 : E) = 0 := CharP.cast_eq_zero E 2
      rw [show (2 : E) = 1 + 1 by norm_num] at h2
      exact h2
    have hone : (1 : E) = -1 := eq_neg_of_add_eq_zero_left hchar
    have hone' : CFSG.LieType.BorelTits.unitaryInvolution E 2 m (1 : E) = -1 := by
      rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, one_pow]
      exact hone
    have hcard2 : 2 ≤ Nat.card E := by
      haveI : Fintype E := Fintype.ofFinite E
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    have hQne2 : Q ≠ 2 := fun h => hex ⟨h, Or.inl rfl⟩
    have hm_ne0 : m ≠ 0 := by
      intro hm0
      rw [hm0, pow_zero] at hQm
      rw [hQm] at hQ
      omega
    have hm_ne1 : m ≠ 1 := by
      intro hm1
      rw [hm1, pow_one] at hQm
      exact hQne2 hQm
    have hm2 : 2 ≤ m := by omega
    have hQ4 : 4 ≤ Q := by
      rw [hQm]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    obtain ⟨eSU2⟩ := psuC2d_SU_equiv_SUid
      (CFSG.LieType.BorelTits.unitaryInvolution E 2 m) hσ' 2
    let eSL := CFSG.LieType.Steinberg.hypEquiv (p := 2) (f := m)
      (ζ := 1) one_ne_zero hone'
    have hnsSL : ¬ Group.IsSolvable
        (Matrix.SpecialLinearGroup (Fin 2)
          (CFSG.LieType.Steinberg.fixedSubfield E 2 m)) :=
      psuC2d_SL_nonsolvable (k := 2) le_rfl
        (by rw [CFSG.LieType.Steinberg.card_fixedSubfield hK, ← hQm]; exact hQ4)
    have hnsSU : ¬ Group.IsSolvable
        ↥(CFSG.LieType.Universal.Unitary.SU
          (CFSG.LieType.BorelTits.unitaryInvolution E 2 m) 2) := by
      intro hsolv
      exact hnsSL (solvable_of_solvable_injective (f := eSL.toMonoidHom) eSL.injective)
    have hnsSUid : ¬ Group.IsSolvable
        ↥(CFSG.LieType.Universal.Unitary.SUid
          (CFSG.LieType.BorelTits.unitaryInvolution E 2 m) 2) := by
      intro hsolv
      exact hnsSU (solvable_of_solvable_injective (f := eSU2.toMonoidHom) eSU2.injective)
    intro hsolv
    exact hnsSUid (solvable_of_solvable_injective (f := eSU2.symm.toMonoidHom) eSU2.symm.injective)
  · have hk3 : 3 ≤ k := by omega
    have hnq : (k, 2 ^ m) ≠ (3, 2) := by
      intro h
      have hk3' : k = 3 := congrArg Prod.fst h
      have hq2 : 2 ^ m = 2 := congrArg Prod.snd h
      exact hex ⟨hQm.trans hq2, Or.inr hk3'⟩
    haveI : Nontrivial
        ↥(CFSG.LieType.Universal.Unitary.SUid
          (CFSG.LieType.BorelTits.unitaryInvolution E 2 m) k) :=
      psuC2d_SUid_nontrivial (CFSG.LieType.BorelTits.unitaryInvolution E 2 m) hσ' hk
    have hperf : Group.IsPerfect
        ↥(CFSG.LieType.Universal.Unitary.SUid
          (CFSG.LieType.BorelTits.unitaryInvolution E 2 m) k) := by
      rw [CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK k]
      exact CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK hk3 hnq
    have hnsSUid : ¬ Group.IsSolvable
        ↥(CFSG.LieType.Universal.Unitary.SUid
          (CFSG.LieType.BorelTits.unitaryInvolution E 2 m) k) :=
      Group.IsPerfect.not_isSolvable _
    intro hsolv
    exact hnsSUid (solvable_of_solvable_injective (f := eSU.symm.toMonoidHom) eSU.symm.injective)

private noncomputable def psuC2dS_hf {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (u v : Fin n → K) : K :=
  (fun i => h.bar (u i)) ⬝ᵥ (psuJ n K *ᵥ v)

private abbrev psuC2dS_V {n : ℕ} {K : Type} [Field K] (e : Matrix (Fin n) (Fin n) K) :
    Submodule K (Fin n → K) :=
  LinearMap.range e.mulVecLin

private lemma psuC2dS_J_mul_self (n : ℕ) (K : Type) [Field K] :
    psuJ n K * psuJ n K = (1 : Matrix (Fin n) (Fin n) K) := by
  simpa [psuJ, AutPSU.coe_gramJ] using
    (CFSG.LieType.Universal.Unitary.antidiag_mul_self (F := K) n)

private lemma psuC2dS_J_inv (n : ℕ) (K : Type) [Field K] :
    (psuJ n K)⁻¹ = psuJ n K :=
  Matrix.inv_eq_right_inv (psuC2dS_J_mul_self n K)

private lemma psuC2dS_J_transpose (n : ℕ) (K : Type) [Field K] :
    (psuJ n K)ᵀ = psuJ n K := by
  simpa [psuJ] using (AutPSU.isPrimeFormGram_gramJ (K := K) (n := n)).symm

private lemma psuC2dS_J_map {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) :
    (psuJ n K).map h.bar = psuJ n K := by
  simpa [psuJ] using (AutPSU.isPrimeFormGram_gramJ (K := K) (n := n)).map_eq h.bar

private lemma psuC2dS_J_apply {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (i j : Fin n) : h.bar (psuJ n K i j) = psuJ n K i j := by
  have h := congrFun (congrFun (psuC2dS_J_map (h := h) (n := n)) i) j
  simpa [Matrix.map_apply] using h

private lemma psuC2dS_dot_symm {n : ℕ} {K : Type} [Field K] (u v : Fin n → K) :
    v ⬝ᵥ (psuJ n K *ᵥ u) = u ⬝ᵥ (psuJ n K *ᵥ v) := by
  calc v ⬝ᵥ (psuJ n K *ᵥ u)
      = (psuJ n K *ᵥ u) ⬝ᵥ v := dotProduct_comm _ _
    _ = (u ᵥ* psuJ n K) ⬝ᵥ v := by
          rw [(mulVec_transpose (psuJ n K) u).symm, psuC2dS_J_transpose]
    _ = u ⬝ᵥ (psuJ n K *ᵥ v) := (dotProduct_mulVec u (psuJ n K) v).symm

private lemma psuC2dS_bar_dotProduct {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (u v : Fin n → K) :
    h.bar (u ⬝ᵥ (psuJ n K *ᵥ v)) =
      (fun i => h.bar (u i)) ⬝ᵥ (psuJ n K *ᵥ (fun i => h.bar (v i))) := by
  simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, psuC2dS_J_apply h]

private lemma psuC2dS_hf_add_left {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (x y z : Fin n → K) :
    psuC2dS_hf h (x + y) z = psuC2dS_hf h x z + psuC2dS_hf h y z := by
  rw [psuC2dS_hf, psuC2dS_hf, psuC2dS_hf]
  rw [show (fun i => h.bar ((x + y) i)) =
      (fun i => h.bar (x i)) + (fun i => h.bar (y i)) from by
        funext i; exact map_add h.bar (x i) (y i)]
  rw [add_dotProduct]

private lemma psuC2dS_hf_add_right {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (x y z : Fin n → K) :
    psuC2dS_hf h x (y + z) = psuC2dS_hf h x y + psuC2dS_hf h x z := by
  simp only [psuC2dS_hf, Matrix.mulVec_add, dotProduct_add]

private lemma psuC2dS_hf_smul_left {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (c : K) (x y : Fin n → K) :
    psuC2dS_hf h (c • x) y = h.bar c * psuC2dS_hf h x y := by
  rw [psuC2dS_hf, psuC2dS_hf]
  rw [show (fun i => h.bar ((c • x) i)) = h.bar c • (fun i => h.bar (x i)) from by
        funext i; simp only [Pi.smul_apply, smul_eq_mul, map_mul]]
  rw [smul_dotProduct, smul_eq_mul]

private lemma psuC2dS_hf_smul_right {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (c : K) (x y : Fin n → K) :
    psuC2dS_hf h x (c • y) = c * psuC2dS_hf h x y := by
  simp only [psuC2dS_hf, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private lemma psuC2dS_hf_zero_right {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (x : Fin n → K) : psuC2dS_hf h x 0 = 0 := by
  simp only [psuC2dS_hf, Matrix.mulVec_zero, dotProduct_zero]

private lemma psuC2dS_hf_herm {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (x y : Fin n → K) :
    psuC2dS_hf h x y = h.bar (psuC2dS_hf h y x) := by
  rw [psuC2dS_hf, psuC2dS_hf]
  rw [psuC2dS_bar_dotProduct h (fun i => h.bar (y i)) x]
  rw [show (fun i => h.bar (h.bar (y i))) = y from funext fun i => h.bar_bar (y i)]
  exact (psuC2dS_dot_symm (fun i => h.bar (x i)) y).symm

private lemma psuC2dS_hf_props {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) :
    (∀ x y z : Fin n → K, psuC2dS_hf h (x + y) z = psuC2dS_hf h x z + psuC2dS_hf h y z) ∧
    (∀ x y z : Fin n → K, psuC2dS_hf h x (y + z) = psuC2dS_hf h x y + psuC2dS_hf h x z) ∧
    (∀ (c : K) (x y : Fin n → K), psuC2dS_hf h (c • x) y = h.bar c * psuC2dS_hf h x y) ∧
    (∀ (c : K) (x y : Fin n → K), psuC2dS_hf h x (c • y) = c * psuC2dS_hf h x y) ∧
    (∀ x y : Fin n → K, psuC2dS_hf h x y = h.bar (psuC2dS_hf h y x)) := by
  exact ⟨psuC2dS_hf_add_left h, psuC2dS_hf_add_right h, psuC2dS_hf_smul_left h,
    psuC2dS_hf_smul_right h, psuC2dS_hf_herm h⟩

private lemma psuC2dS_dag_zero {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) : psuDag h (0 : Matrix (Fin n) (Fin n) K) = 0 := by
  simp [psuDag, formAdj]

private lemma psuC2dS_comm {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K) :
    ∀ a ∈ psuAlg B, ∀ b ∈ psuAlg B, a * b = b * a := by
  have hcommP : (Units.val '' ({B} : Set (GL (Fin n) K)) :
      Set (Matrix (Fin n) (Fin n) K)).Pairwise Commute := by
    rintro a ⟨s, hs, rfl⟩ b ⟨s', hs', rfl⟩ _
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  letI : CommSemiring (psuAlg B) := Algebra.adjoinCommSemiringOfComm K hcommP
  intro a ha b hb
  have h := congrArg Subtype.val (mul_comm (⟨a, ha⟩ : psuAlg B) (⟨b, hb⟩ : psuAlg B))
  simpa using h

private lemma psuC2dS_factor {A B E : Type*} [Ring A] [Ring B] [Ring E]
    (π : A →+* B) (hπ : Function.Surjective π) (ρ : A →+* E)
    (hker : ∀ a, π a = 0 → ρ a = 0) :
    ∃ φ : B →+* E, ∀ a, φ (π a) = ρ a :=
  ⟨RingHom.liftOfSurjective π hπ ⟨ρ, fun a ha => hker a ha⟩,
    fun a => RingHom.liftOfSurjective_comp_apply π hπ ⟨ρ, fun a ha => hker a ha⟩ a⟩

private lemma psuC2dS_dag_algebraMap {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (B : GL (Fin n) K) (c : K) :
    psuDag h ((algebraMap K (psuAlg B) c) : Matrix (Fin n) (Fin n) K) =
      ((algebraMap K (psuAlg B) (h.bar c)) : Matrix (Fin n) (Fin n) K) := by
  simp only [Algebra.algebraMap_eq_smul_one, Subalgebra.coe_smul, Subalgebra.coe_one,
    psuDag_smul, psuDag_one]

private lemma psuC2dS_tau {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    {e : Matrix (Fin n) (Fin n) K} (he : e ∈ psuAlg B) (hde : psuDag h e = e)
    {F : Type} [Field F] [Algebra K F] (π : psuAlg B →ₐ[K] F) (hπ : Function.Surjective π)
    (hker : ∀ a : psuAlg B, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e = 0) :
    ∃ τ : F ≃+* F, (∀ x, τ (τ x) = x) ∧
      (∀ c : K, τ (algebraMap K F c) = algebraMap K F (h.bar c)) ∧
      ∀ a : psuAlg B, τ (π a) = π ⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a a.2).1⟩ := by
  let ρ : psuAlg B →+* F :=
    { toFun := fun a => π ⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a a.2).1⟩
      map_one' := by
        have h1 : (⟨psuDag h ((1 : psuAlg B) : Matrix (Fin n) (Fin n) K),
            (psuGraph_star_mem S (1 : psuAlg B) (1 : psuAlg B).2).1⟩ : psuAlg B) = 1 :=
          Subtype.ext (psuDag_one h)
        rw [h1, map_one]
      map_mul' := by
        intro a b
        have h1 : (⟨psuDag h ((a * b : psuAlg B) : Matrix (Fin n) (Fin n) K),
            (psuGraph_star_mem S (a * b) (a * b).2).1⟩ : psuAlg B) =
            ⟨psuDag h (b : Matrix (Fin n) (Fin n) K),
              (psuGraph_star_mem S b b.2).1⟩ *
            ⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
              (psuGraph_star_mem S a a.2).1⟩ :=
          Subtype.ext (psuDag_mul h (a : Matrix (Fin n) (Fin n) K)
            (b : Matrix (Fin n) (Fin n) K))
        rw [h1, map_mul, mul_comm]
      map_zero' := by
        have h1 : (⟨psuDag h ((0 : psuAlg B) : Matrix (Fin n) (Fin n) K),
            (psuGraph_star_mem S (0 : psuAlg B) (0 : psuAlg B).2).1⟩ : psuAlg B) = 0 :=
          Subtype.ext (psuC2dS_dag_zero h)
        rw [h1, map_zero]
      map_add' := by
        intro a b
        have h1 : (⟨psuDag h ((a + b : psuAlg B) : Matrix (Fin n) (Fin n) K),
            (psuGraph_star_mem S (a + b) (a + b).2).1⟩ : psuAlg B) =
            ⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
              (psuGraph_star_mem S a a.2).1⟩ +
            ⟨psuDag h (b : Matrix (Fin n) (Fin n) K),
              (psuGraph_star_mem S b b.2).1⟩ :=
          Subtype.ext (psuDag_add h (a : Matrix (Fin n) (Fin n) K)
            (b : Matrix (Fin n) (Fin n) K))
        rw [h1, map_add] }
  have hkerρ : ∀ a : psuAlg B, π.toRingHom a = 0 → ρ a = 0 := by
    intro a h0
    have hae : (a : Matrix (Fin n) (Fin n) K) * e = 0 := (hker a).mp h0
    have h1 : psuDag h ((a : Matrix (Fin n) (Fin n) K) * e) = 0 := by
      rw [hae, psuC2dS_dag_zero]
    rw [psuDag_mul, hde] at h1
    have h2 : psuDag h (a : Matrix (Fin n) (Fin n) K) * e = 0 := by
      rw [psuC2dS_comm B (psuDag h (a : Matrix (Fin n) (Fin n) K))
        (psuGraph_star_mem S a a.2).1 e he]
      exact h1
    exact (hker ⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
      (psuGraph_star_mem S a a.2).1⟩).mpr h2
  obtain ⟨φ, hφ⟩ := psuC2dS_factor π.toRingHom hπ ρ hkerρ
  have hφ' : ∀ a : psuAlg B, φ (π a) =
      π ⟨psuDag h (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a a.2).1⟩ :=
    fun a => hφ a
  have hφφa : ∀ a : psuAlg B, φ (φ (π a)) = π a := by
    intro a
    rw [hφ' a, hφ' ⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
      (psuGraph_star_mem S a a.2).1⟩]
    congr 1
    exact Subtype.ext (psuDag_dag h (a : Matrix (Fin n) (Fin n) K))
  have hφφ : ∀ x : F, φ (φ x) = x := by
    intro x
    obtain ⟨a, rfl⟩ := hπ x
    exact hφφa a
  refine ⟨RingEquiv.ofBijective φ (Function.Involutive.bijective hφφ), ?_, ?_, ?_⟩
  · intro x
    simpa only [RingEquiv.ofBijective_apply] using hφφ x
  · intro c
    rw [RingEquiv.ofBijective_apply, ← AlgHom.commutes π c, hφ' (algebraMap K (psuAlg B) c)]
    have hdag := psuC2dS_dag_algebraMap (h := h) (B := B) c
    rw [show (⟨psuDag h ((algebraMap K (psuAlg B) c) : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S (algebraMap K (psuAlg B) c)
          (algebraMap K (psuAlg B) c).2).1⟩ : psuAlg B) =
        algebraMap K (psuAlg B) (h.bar c) from Subtype.ext hdag]
    exact AlgHom.commutes π (h.bar c)
  · intro a
    rw [RingEquiv.ofBijective_apply]
    exact hφ' a

private lemma psuC2dS_J_dag {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (a : Matrix (Fin n) (Fin n) K) :
    (a.map h.bar)ᵀ * psuJ n K = psuJ n K * psuDag h a := by
  have hdag : psuDag h a = psuJ n K * (a.map h.bar)ᵀ * psuJ n K := by
    simp only [psuDag, formAdj, psuC2dS_J_inv]
  calc (a.map h.bar)ᵀ * psuJ n K
      = (psuJ n K * psuJ n K) * (a.map h.bar)ᵀ * psuJ n K := by
          rw [psuC2dS_J_mul_self, Matrix.one_mul]
    _ = psuJ n K * (psuJ n K * (a.map h.bar)ᵀ * psuJ n K) := by noncomm_ring
    _ = psuJ n K * psuDag h a := by rw [hdag]

private lemma psuC2dS_bar_mulVec {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (a : Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    (fun i => h.bar ((a *ᵥ x) i)) = (a.map h.bar) *ᵥ (fun i => h.bar (x i)) := by
  funext i
  simp only [Matrix.mulVec, Matrix.map_apply, dotProduct, map_sum, map_mul]

private lemma psuC2dS_mulVec_dot {n : ℕ} {K : Type} [Field K]
    (A : Matrix (Fin n) (Fin n) K) (u w : Fin n → K) :
    (A *ᵥ u) ⬝ᵥ w = u ⬝ᵥ (Aᵀ *ᵥ w) := by
  calc (A *ᵥ u) ⬝ᵥ w
      = w ⬝ᵥ (A *ᵥ u) := dotProduct_comm _ _
    _ = (w ᵥ* A) ⬝ᵥ u := dotProduct_mulVec w A u
    _ = u ⬝ᵥ (w ᵥ* A) := dotProduct_comm _ _
    _ = u ⬝ᵥ (Aᵀ *ᵥ w) := by rw [← mulVec_transpose]

private lemma psuC2dS_hf_dag {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (a : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    psuC2dS_hf h (a *ᵥ x) y = psuC2dS_hf h x (psuDag h a *ᵥ y) := by
  rw [psuC2dS_hf, psuC2dS_hf, psuC2dS_bar_mulVec h a x, psuC2dS_mulVec_dot,
    Matrix.mulVec_mulVec, psuC2dS_J_dag, Matrix.mulVec_mulVec]

private lemma psuC2dS_mulVec_eq_of_mem {n : ℕ} {K : Type} [Field K]
    {e : Matrix (Fin n) (Fin n) K} (hee : e * e = e) {w : Fin n → K}
    (hw : w ∈ psuC2dS_V e) : e *ᵥ w = w := by
  obtain ⟨v, hv⟩ := hw
  rw [← hv, Matrix.mulVecLin_apply]
  change e *ᵥ (e *ᵥ v) = e *ᵥ v
  rw [Matrix.mulVec_mulVec, hee]

private lemma psuC2dS_e_mul_one_sub {n : ℕ} {K : Type} [Field K]
    {e : Matrix (Fin n) (Fin n) K} (hee : e * e = e) (v : Fin n → K) :
    e *ᵥ ((1 - e) *ᵥ v) = 0 := by
  rw [Matrix.mulVec_mulVec]
  have h : e * (1 - e) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hee, sub_self]
  rw [h, Matrix.zero_mulVec]

private lemma psuC2dS_add_one_sub {n : ℕ} {K : Type} [Field K]
    (e : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    e *ᵥ v + (1 - e) *ᵥ v = v := by
  rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]

private lemma psuC2dS_hf_single {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (x : Fin n → K) (i : Fin n) :
    psuC2dS_hf h x (Pi.single i 1) =
      ((fun j => h.bar (x j)) ᵥ* psuJ n K) i := by
  rw [psuC2dS_hf, Matrix.mulVec_single_one]
  simp [dotProduct, Matrix.vecMul]

private lemma psuC2dS_eq_zero_of_forall_hf {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (x : Fin n → K)
    (hx : ∀ v : Fin n → K, psuC2dS_hf h x v = 0) : x = 0 := by
  have hu : (fun j => h.bar (x j)) = 0 := by
    have hvec : (fun j => h.bar (x j)) ᵥ* psuJ n K = 0 := by
      funext i
      rw [← psuC2dS_hf_single h x i]
      exact hx (Pi.single i 1)
    calc (fun j => h.bar (x j))
        = (fun j => h.bar (x j)) ᵥ* 1 := by rw [Matrix.vecMul_one]
      _ = (fun j => h.bar (x j)) ᵥ* (psuJ n K * psuJ n K) := by rw [psuC2dS_J_mul_self]
      _ = ((fun j => h.bar (x j)) ᵥ* psuJ n K) ᵥ* psuJ n K := by
            rw [Matrix.vecMul_vecMul]
      _ = 0 := by rw [hvec, Matrix.zero_vecMul]
  funext i
  refine h.bar.injective ?_
  have hi := congrFun hu i
  simpa using hi

private lemma psuC2dS_compat {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    {e : Matrix (Fin n) (Fin n) K} (hee : e * e = e)
    (hde : psuDag h e = e)
    {F : Type} [Field F] [Algebra K F] (π : psuAlg B →ₐ[K] F) (hπ : Function.Surjective π)
    [Module F (psuC2dS_V e)]
    (hact : ∀ (a : psuAlg B) (w : psuC2dS_V e),
      ((π a • w : psuC2dS_V e) : Fin n → K) = (a : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K))
    (τ : F ≃+* F)
    (hτπ : ∀ a : psuAlg B, τ (π a) = π ⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a a.2).1⟩) :
    (∀ (a : F) (x y : psuC2dS_V e),
      psuC2dS_hf h ((a • x : psuC2dS_V e) : Fin n → K) (y : Fin n → K) =
        psuC2dS_hf h (x : Fin n → K) ((τ a • y : psuC2dS_V e) : Fin n → K)) ∧
    (∀ x : psuC2dS_V e,
      (∀ y : psuC2dS_V e, psuC2dS_hf h (x : Fin n → K) (y : Fin n → K) = 0) → x = 0) := by
  refine ⟨?_, ?_⟩
  · intro a x y
    obtain ⟨a', ha'⟩ := hπ a
    rw [← ha', hact a' x, hτπ a']
    rw [hact ⟨psuDag h (a' : Matrix (Fin n) (Fin n) K),
      (psuGraph_star_mem S a' a'.2).1⟩ y]
    exact psuC2dS_hf_dag h (a' : Matrix (Fin n) (Fin n) K) (x : Fin n → K) (y : Fin n → K)
  · intro x hx
    apply Subtype.ext
    exact psuC2dS_eq_zero_of_forall_hf h (x : Fin n → K) (fun v => by
      have hev : e *ᵥ v ∈ psuC2dS_V e := ⟨v, Matrix.mulVecLin_apply e v⟩
      have h1 : psuC2dS_hf h (x : Fin n → K) (e *ᵥ v) = 0 := hx ⟨e *ᵥ v, hev⟩
      have h2 : psuC2dS_hf h (x : Fin n → K) ((1 - e) *ᵥ v) = 0 := by
        have hxmem : e *ᵥ (x : Fin n → K) = (x : Fin n → K) :=
          psuC2dS_mulVec_eq_of_mem hee x.2
        calc psuC2dS_hf h (x : Fin n → K) ((1 - e) *ᵥ v)
            = psuC2dS_hf h (e *ᵥ (x : Fin n → K)) ((1 - e) *ᵥ v) := by rw [hxmem]
          _ = psuC2dS_hf h (x : Fin n → K) (psuDag h e *ᵥ ((1 - e) *ᵥ v)) :=
                psuC2dS_hf_dag h e (x : Fin n → K) ((1 - e) *ᵥ v)
          _ = psuC2dS_hf h (x : Fin n → K) (e *ᵥ ((1 - e) *ᵥ v)) := by rw [hde]
          _ = psuC2dS_hf h (x : Fin n → K) 0 := by rw [psuC2dS_e_mul_one_sub hee v]
          _ = 0 := psuC2dS_hf_zero_right h (x : Fin n → K)
      calc psuC2dS_hf h (x : Fin n → K) v
          = psuC2dS_hf h (x : Fin n → K) (e *ᵥ v + (1 - e) *ᵥ v) := by
              rw [psuC2dS_add_one_sub]
        _ = psuC2dS_hf h (x : Fin n → K) (e *ᵥ v) +
              psuC2dS_hf h (x : Fin n → K) ((1 - e) *ᵥ v) :=
              psuC2dS_hf_add_right h _ _ _
        _ = 0 := by rw [h1, h2, add_zero])

private lemma psuC2dG_eq_unitaryInvolution {E : Type} [Field E] [Finite E] [CharP E 2]
    (σ : E ≃+* E) (hσ2 : ∀ x, σ (σ x) = x) (hσ1 : ∃ x, σ x ≠ x) {Q : ℕ}
    (hQ : Nat.card E = Q ^ 2) :
    ∃ m : ℕ, Q = 2 ^ m ∧ σ = CFSG.LieType.BorelTits.unitaryInvolution E 2 m := by
  classical
  have hσ2' : σ ^ 2 = 1 := by
    ext x
    change σ (σ x) = x
    exact hσ2 x
  have hσ1' : σ ≠ 1 := by
    intro h
    obtain ⟨c, hc⟩ := hσ1
    exact hc (by rw [h]; rfl)
  letI : Fintype E := Fintype.ofFinite E
  obtain ⟨n, -, hcard⟩ := FiniteField.card E 2
  have hcard' : Nat.card E = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hcard
  obtain ⟨e, h, hσe⟩ :=
    CFSG.ComponentClassification.Burgoyne.O.exists_unitaryFieldData_of_involution
      (p := 2) (f := (n : ℕ)) Nat.prime_two (Nat.succ_le_of_lt n.pos) hcard' hσ2' hσ1'
  have hcardE : Nat.card E = (2 ^ e) ^ 2 := by
    calc Nat.card E = 2 ^ (2 * e) := h.card
      _ = 2 ^ (e * 2) := by rw [mul_comm]
      _ = (2 ^ e) ^ 2 := by rw [pow_mul, pow_two]
  have hQe : Q = 2 ^ e := by
    exact Nat.pow_left_injective (n := 2) (by norm_num) (hQ.symm.trans hcardE)
  refine ⟨e, hQe, ?_⟩
  have hbar : CFSG.ComponentClassification.Burgoyne.U.barEq h =
      CFSG.LieType.BorelTits.unitaryInvolution E 2 e := by
    ext x
    rw [CFSG.ComponentClassification.Burgoyne.U.barEq_apply, h.bar_apply,
      CFSG.LieType.BorelTits.unitaryInvolution_apply]
  rw [hσe, hbar]

private lemma psuC2dS_isUnitaryInvolution {F : Type} [Field F] [Finite F] [CharP F 2]
    (τ : F ≃+* F) (hττ : ∀ x, τ (τ x) = x) (hne : ∃ x, τ x ≠ x) :
    CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution τ := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨n, -, hcard⟩ := FiniteField.card F 2
  have hcard' : Nat.card F = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hcard
  have hτ2' : τ ^ 2 = 1 := by
    ext x
    change τ (τ x) = x
    exact hττ x
  have hne' : τ ≠ 1 := by
    intro h
    obtain ⟨c, hc⟩ := hne
    exact hc (by rw [h]; rfl)
  obtain ⟨e, he, hτe⟩ :=
    CFSG.ComponentClassification.Burgoyne.O.exists_unitaryFieldData_of_involution
      (p := 2) (f := (n : ℕ)) Nat.prime_two (Nat.succ_le_of_lt n.pos) hcard' hτ2' hne'
  have hcardE : Nat.card F = (2 ^ e) ^ 2 := by
    calc Nat.card F = 2 ^ (2 * e) := he.card
      _ = 2 ^ (e * 2) := by rw [mul_comm]
      _ = (2 ^ e) ^ 2 := by rw [pow_mul, pow_two]
  have hbar : CFSG.ComponentClassification.Burgoyne.U.barEq he =
      CFSG.LieType.BorelTits.unitaryInvolution F 2 e := by
    ext x
    rw [CFSG.ComponentClassification.Burgoyne.U.barEq_apply, he.bar_apply,
      CFSG.LieType.BorelTits.unitaryInvolution_apply]
  rw [hτe, hbar]
  exact CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hcardE

private lemma psuC2dG_SU_equiv_SUid {E : Type} [Field E] [CharP E 2]
    (σ : E ≃+* E) (hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ) (k : ℕ) :
    Nonempty (↥(CFSG.LieType.Universal.Unitary.SU σ k) ≃*
      ↥(CFSG.LieType.Universal.Unitary.SUid σ k)) := by
  classical
  obtain ⟨c, hc⟩ := hσ.exists_ne
  have hchar : (1 : E) + 1 = 0 := by
    have h2 : (2 : E) = 0 := CharP.cast_eq_zero E 2
    rw [show (2 : E) = 1 + 1 by norm_num] at h2
    exact h2
  have hone : (1 : E) = -1 := eq_neg_of_add_eq_zero_left hchar
  have hc0 : c ≠ 0 := by
    intro h0
    exact hc (by rw [h0, map_zero])
  have hσc0 : σ c ≠ 0 := fun h0 => hc0 (σ.injective (by rw [h0, map_zero]))
  let ω : E := c * (σ c)⁻¹
  have hω : σ ω * ω = 1 := by
    dsimp only [ω]
    rw [map_mul, map_inv₀, hσ.invol]
    field_simp [hc0, hσc0]
  have hω1 : ω ≠ 1 := by
    intro h
    apply hc
    dsimp only [ω] at h
    rw [mul_inv_eq_one₀ hσc0] at h
    exact h.symm
  have hu : σ (1 : E) * 1 = -1 := by
    simpa only [map_one, one_mul] using hone
  obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix_of σ hu hω hω1
  exact ⟨CFSG.LieType.Universal.Unitary.conjEquiv P hP⟩

private lemma psuC2dS_SUid_perfect {E : Type} [Field E] [Finite E] [CharP E 2] (σ : E ≃+* E)
    (hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ) {Q k : ℕ}
    (hcard : Nat.card E = Q ^ 2) (hk : 2 ≤ k) (hex : ¬ (Q = 2 ∧ (k = 2 ∨ k = 3))) :
    Group.IsPerfect ↥(CFSG.LieType.Universal.Unitary.SUid σ k) := by
  classical
  obtain ⟨m, hQm, hσm⟩ := psuC2dG_eq_unitaryInvolution σ hσ.invol hσ.exists_ne hcard
  rw [hσm]
  have hK : Nat.card E = (2 ^ m) ^ 2 := by rw [hcard, hQm]
  have hσ' : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution
      (CFSG.LieType.BorelTits.unitaryInvolution E 2 m) :=
    CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK
  by_cases hk2 : k = 2
  · subst k
    have hQne2 : Q ≠ 2 := fun h => hex ⟨h, Or.inl rfl⟩
    have hm0 : m ≠ 0 := by
      intro hm
      rw [hm] at hK
      norm_num at hK
      have h1 : 1 < Nat.card E := Finite.one_lt_card
      omega
    have hm1 : m ≠ 1 := by
      intro hm
      rw [hm, pow_one] at hQm
      exact hQne2 hQm
    have hm2 : 2 ≤ m := by omega
    have hQ4 : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    have hcardFix : Nat.card (CFSG.LieType.Steinberg.fixedSubfield E 2 m) = 2 ^ m :=
      CFSG.LieType.Steinberg.card_fixedSubfield hK
    haveI : Fintype (CFSG.LieType.Steinberg.fixedSubfield E 2 m) := Fintype.ofFinite _
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (CFSG.LieType.Steinberg.fixedSubfield E 2 m))) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcardFix]; exact hQ4)
    haveI hSL : Group.IsPerfect
        (Matrix.SpecialLinearGroup (Fin 2) (CFSG.LieType.Steinberg.fixedSubfield E 2 m)) :=
      CFSG.LinearGroups.special_linear_isPerfect (n := 2) le_rfl (Or.inr ⟨s, hs⟩)
    have hchar : (1 : E) + 1 = 0 := by
      have h2 : (2 : E) = 0 := CharP.cast_eq_zero E 2
      rw [show (2 : E) = 1 + 1 by norm_num] at h2
      exact h2
    have hone : (1 : E) = -1 := eq_neg_of_add_eq_zero_left hchar
    have hone' : CFSG.LieType.BorelTits.unitaryInvolution E 2 m (1 : E) = -1 := by
      rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, one_pow]
      exact hone
    have eSL := CFSG.LieType.Steinberg.hypEquiv (p := 2) (f := m) (ζ := 1)
      one_ne_zero hone'
    haveI hSU : Group.IsPerfect
        ↥(CFSG.LieType.Universal.Unitary.SU
          (CFSG.LieType.BorelTits.unitaryInvolution E 2 m) 2) :=
      Group.IsPerfect.ofSurjective (f := eSL.toMonoidHom) eSL.surjective
    obtain ⟨eSU2⟩ := psuC2dG_SU_equiv_SUid
      (CFSG.LieType.BorelTits.unitaryInvolution E 2 m) hσ' 2
    exact Group.IsPerfect.ofSurjective (f := eSU2.toMonoidHom) eSU2.surjective
  · have hk3 : 3 ≤ k := by omega
    have hnq : (k, 2 ^ m) ≠ (3, 2) := by
      intro h
      have hk3' : k = 3 := congrArg Prod.fst h
      have hq2 : 2 ^ m = 2 := congrArg Prod.snd h
      exact hex ⟨hQm.trans hq2, Or.inr hk3'⟩
    rw [CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK k]
    exact CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK hk3 hnq

private lemma psuC2dE_hf_add_left {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (u₁ u₂ v : Fin n → K) :
    psuC2dS_hf h (u₁ + u₂) v = psuC2dS_hf h u₁ v + psuC2dS_hf h u₂ v := by
  simp only [psuC2dS_hf, dotProduct, Pi.add_apply, map_add, add_mul,
    Finset.sum_add_distrib]

private lemma psuC2dE_hf_add_right {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (u v₁ v₂ : Fin n → K) :
    psuC2dS_hf h u (v₁ + v₂) = psuC2dS_hf h u v₁ + psuC2dS_hf h u v₂ := by
  simp only [psuC2dS_hf, dotProduct, Matrix.mulVec_add, Pi.add_apply, mul_add,
    Finset.sum_add_distrib]

private lemma psuC2dE_hf_zero_right {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (u : Fin n → K) : psuC2dS_hf h u 0 = 0 := by
  simp [psuC2dS_hf, dotProduct]

private lemma psuC2dE_J_mul_self {n : ℕ} {K : Type} [Field K] :
    psuJ n K * psuJ n K = 1 := by
  rw [psuJ, AutPSU.coe_gramJ]
  exact antidiag_mul_self n

private lemma psuC2dE_J_det_isUnit {n : ℕ} {K : Type} [Field K] :
    IsUnit (psuJ n K).det := by
  refine ⟨⟨(psuJ n K).det, (psuJ n K).det, ?_, ?_⟩, rfl⟩
  · rw [← Matrix.det_mul, psuC2dE_J_mul_self, Matrix.det_one]
  · rw [← Matrix.det_mul, psuC2dE_J_mul_self, Matrix.det_one]

private lemma psuC2dE_dag_one {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) :
    psuDag h (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [psuDag, formAdj, Matrix.map_one h.bar (map_zero h.bar) (map_one h.bar),
    Matrix.transpose_one, Matrix.mul_one, Matrix.nonsing_inv_mul _ psuC2dE_J_det_isUnit]

private lemma psuC2dE_dag_one_sub {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    {e : Matrix (Fin n) (Fin n) K} (hde : psuDag h e = e) :
    psuDag h (1 - e) = 1 - e := by
  have h1 : psuDag h (1 - e) = psuDag h 1 + (-1 : K) • psuDag h e := by
    rw [sub_eq_add_neg, show -e = (-1 : K) • e from (neg_one_smul K e).symm, psuDag, psuDag,
      psuDag, Geo.formAdj_add, Geo.formAdj_smul, map_neg, map_one]
  rw [h1, psuC2dE_dag_one h, hde, neg_one_smul, sub_eq_add_neg]

private lemma psuC2dE_dotProduct_mulVec_mul {k : ℕ} {F : Type} [Field F]
    (A : Matrix (Fin k) (Fin k) F) (x y : Fin k → F) :
    (A *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (Aᵀ *ᵥ y) := by
  have hL : (A *ᵥ x) ⬝ᵥ y = ∑ j, ∑ i, (A j i * x i) * y j := by
    simp only [dotProduct, Matrix.mulVec, Finset.sum_mul]
  have hR : x ⬝ᵥ (Aᵀ *ᵥ y) = ∑ i, ∑ j, x i * (A j i * y j) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.transpose_apply]
  rw [hL, hR, Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

private lemma psuC2dE_hf_dag {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (a : Matrix (Fin n) (Fin n) K) (u v : Fin n → K) :
    psuC2dS_hf h (a *ᵥ u) v = psuC2dS_hf h u (psuDag h a *ᵥ v) := by
  have hJmul : psuJ n K * psuDag h a = (a.map h.bar)ᵀ * psuJ n K := by
    have hJdet := psuC2dE_J_det_isUnit (n := n) (K := K)
    calc psuJ n K * psuDag h a
        = psuJ n K * ((psuJ n K)⁻¹ * ((a.map h.bar)ᵀ * psuJ n K)) := by
            simp only [psuDag, formAdj, Matrix.mul_assoc]
      _ = (psuJ n K * (psuJ n K)⁻¹) * ((a.map h.bar)ᵀ * psuJ n K) := by
            rw [Matrix.mul_assoc]
      _ = 1 * ((a.map h.bar)ᵀ * psuJ n K) := by rw [Matrix.mul_nonsing_inv _ hJdet]
      _ = (a.map h.bar)ᵀ * psuJ n K := by rw [Matrix.one_mul]
  have hmap : (fun i => h.bar ((a *ᵥ u) i)) =
      (a.map h.bar) *ᵥ (fun i => h.bar (u i)) := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
  change (fun i => h.bar ((a *ᵥ u) i)) ⬝ᵥ (psuJ n K *ᵥ v) =
    (fun i => h.bar (u i)) ⬝ᵥ (psuJ n K *ᵥ (psuDag h a *ᵥ v))
  rw [hmap, psuC2dE_dotProduct_mulVec_mul]
  congr 1
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hJmul]

private lemma psuC2dE_add_one_sub_mulVec {n : ℕ} {K : Type} [Field K]
    (e : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    e *ᵥ v + (1 - e) *ᵥ v = v := by
  rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]

private lemma psuC2dE_mulVec_eq_of_mem_Ve {n : ℕ} {K : Type} [Field K]
    {e : Matrix (Fin n) (Fin n) K} (hee : e * e = e) {w : Fin n → K}
    (hw : w ∈ psuC2dS_V e) : e *ᵥ w = w := by
  obtain ⟨v, hv⟩ := hw
  rw [← hv, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hee]

private lemma psuC2dE_one_sub_mulVec_eq_zero_of_mem_Ve {n : ℕ} {K : Type} [Field K]
    {e : Matrix (Fin n) (Fin n) K} (hee : e * e = e) {w : Fin n → K}
    (hw : w ∈ psuC2dS_V e) : (1 - e) *ᵥ w = 0 := by
  obtain ⟨v, hv⟩ := hw
  rw [← hv, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
  have h : (1 - e) * e = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hee, sub_self]
  rw [h, Matrix.zero_mulVec]

private lemma psuC2dE_e_mulVec_one_sub {n : ℕ} {K : Type} [Field K]
    {e : Matrix (Fin n) (Fin n) K} (hee : e * e = e) (v : Fin n → K) :
    e *ᵥ ((1 - e) *ᵥ v) = 0 := by
  rw [Matrix.mulVec_mulVec]
  have h : e * (1 - e) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hee, sub_self]
  rw [h, Matrix.zero_mulVec]

private lemma psuC2dE_one_sub_mulVec_e {n : ℕ} {K : Type} [Field K]
    {e : Matrix (Fin n) (Fin n) K} (hee : e * e = e) (v : Fin n → K) :
    (1 - e) *ᵥ (e *ᵥ v) = 0 := by
  rw [Matrix.mulVec_mulVec]
  have h : (1 - e) * e = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hee, sub_self]
  rw [h, Matrix.zero_mulVec]

private lemma psuC2dE_one_sub_mulVec_one_sub {n : ℕ} {K : Type} [Field K]
    {e : Matrix (Fin n) (Fin n) K} (hee : e * e = e) (v : Fin n → K) :
    (1 - e) *ᵥ ((1 - e) *ᵥ v) = (1 - e) *ᵥ v := by
  rw [Matrix.mulVec_mulVec]
  have h : (1 - e) * (1 - e) = 1 - e := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hee]
    abel
  rw [h]

private lemma psuC2dE_hf_Ve_ker {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    {e : Matrix (Fin n) (Fin n) K} (hee : e * e = e) (hde : psuDag h e = e)
    (u v : Fin n → K) :
    psuC2dS_hf h (e *ᵥ u) ((1 - e) *ᵥ v) = 0 := by
  rw [psuC2dE_hf_dag h e u ((1 - e) *ᵥ v), hde, psuC2dE_e_mulVec_one_sub hee,
    psuC2dE_hf_zero_right h]

private lemma psuC2dE_hf_ker_Ve {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    {e : Matrix (Fin n) (Fin n) K} (hee : e * e = e) (hde : psuDag h e = e)
    (u v : Fin n → K) :
    psuC2dS_hf h ((1 - e) *ᵥ u) (e *ᵥ v) = 0 := by
  rw [psuC2dE_hf_dag h (1 - e) u (e *ᵥ v), psuC2dE_dag_one_sub h hde,
    psuC2dE_one_sub_mulVec_e hee, psuC2dE_hf_zero_right h]

private lemma psuC2dE_hf_decomp {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    {e : Matrix (Fin n) (Fin n) K} (hee : e * e = e) (hde : psuDag h e = e)
    (u v : Fin n → K) :
    psuC2dS_hf h u v = psuC2dS_hf h (e *ᵥ u) (e *ᵥ v) +
      psuC2dS_hf h ((1 - e) *ᵥ u) ((1 - e) *ᵥ v) := by
  conv_lhs => rw [← psuC2dE_add_one_sub_mulVec e u, ← psuC2dE_add_one_sub_mulVec e v]
  rw [psuC2dE_hf_add_left, psuC2dE_hf_add_right, psuC2dE_hf_add_right,
    psuC2dE_hf_Ve_ker h hee hde, psuC2dE_hf_ker_Ve h hee hde, add_zero, zero_add]

private lemma psuC2dE_H_zero_left {V : Type} {F : Type} [AddCommGroup V] [Field F]
    (H : V → V → F) (hHaddL : ∀ x y z, H (x + y) z = H x z + H y z) (y : V) :
    H 0 y = 0 := by
  have h := hHaddL 0 0 y
  rw [zero_add] at h
  have h2 : H 0 y + 0 = H 0 y + H 0 y := by rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

private lemma psuC2dE_H_zero_right {V : Type} {F : Type} [AddCommGroup V] [Field F]
    (H : V → V → F) (hHaddR : ∀ x y z, H x (y + z) = H x y + H x z) (x : V) :
    H x 0 = 0 := by
  have h := hHaddR x 0 0
  rw [add_zero] at h
  have h2 : H x 0 + 0 = H x 0 + H x 0 := by rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

private lemma psuC2dE_H_sum_left {k : ℕ} {F : Type} [Field F] {τ : F ≃+* F} {V : Type}
    [AddCommGroup V] [Module F V] (H : V → V → F)
    (hHaddL : ∀ x y z, H (x + y) z = H x z + H y z)
    (hHsmulL : ∀ (a : F) x y, H (a • x) y = τ a * H x y)
    (hH0 : ∀ y, H 0 y = 0)
    (s : Finset (Fin k)) (c : Fin k → F) (bs : Fin k → V) (y : V) :
    H (∑ i ∈ s, c i • bs i) y = ∑ i ∈ s, τ (c i) * H (bs i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hH0]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hHaddL, hHsmulL, ih]

private lemma psuC2dE_H_sum_right {k : ℕ} {F : Type} [Field F] {V : Type}
    [AddCommGroup V] [Module F V] (H : V → V → F)
    (hHaddR : ∀ x y z, H x (y + z) = H x y + H x z)
    (hHsmulR : ∀ (a : F) x y, H x (a • y) = a * H x y)
    (hH0 : ∀ y, H y 0 = 0)
    (s : Finset (Fin k)) (c : Fin k → F) (bs : Fin k → V) (x : V) :
    H x (∑ i ∈ s, c i • bs i) = ∑ i ∈ s, c i * H x (bs i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hH0]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hHaddR, hHsmulR, ih]

private noncomputable def psuC2dE_Hc {k : ℕ} {F : Type} [Field F] (τ : F ≃+* F)
    (u v : Fin k → F) : F :=
  ∑ i, τ (u i) * v i

private lemma psuC2dE_Hc_mulVec {k : ℕ} {F : Type} [Field F] {τ : F ≃+* F}
    (A : SUid τ k) (u v : Fin k → F) :
    psuC2dE_Hc τ (((A : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) *ᵥ u)
      (((A : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) *ᵥ v) = psuC2dE_Hc τ u v := by
  have hstar : (fun i => τ ((((A : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) *ᵥ u) i)) =
      ((A : GL (Fin k) F) : Matrix (Fin k) (Fin k) F).map τ *ᵥ (fun i => τ (u i)) := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
  change (fun i => τ ((((A : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) *ᵥ u) i)) ⬝ᵥ
    (((A : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) *ᵥ v) =
    (fun i => τ (u i)) ⬝ᵥ v
  rw [hstar, psuC2dE_dotProduct_mulVec_mul]
  congr 1
  rw [Matrix.mulVec_mulVec,
    show ((((A : GL (Fin k) F)) : Matrix (Fin k) (Fin k) F).map τ)ᵀ *
      (((A : GL (Fin k) F)) : Matrix (Fin k) (Fin k) F) = 1 from A.2.2,
    Matrix.one_mulVec]

private lemma psuC2dE_H_eq_Hc {k : ℕ} {F : Type} [Field F] {τ : F ≃+* F} {V : Type}
    [AddCommGroup V] [Module F V] (H : V → V → F)
    (hHaddL : ∀ x y z, H (x + y) z = H x z + H y z)
    (hHaddR : ∀ x y z, H x (y + z) = H x y + H x z)
    (hHsmulL : ∀ (a : F) x y, H (a • x) y = τ a * H x y)
    (hHsmulR : ∀ (a : F) x y, H x (a • y) = a * H x y)
    (b : Module.Basis (Fin k) F V)
    (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0) (x y : V) :
    H x y = psuC2dE_Hc τ (b.equivFun x) (b.equivFun y) := by
  have hxy : H x y = H (b.equivFun.symm (b.equivFun x)) (b.equivFun.symm (b.equivFun y)) := by
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  rw [hxy, Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply,
    psuC2dE_H_sum_left H hHaddL hHsmulL (psuC2dE_H_zero_left H hHaddL) Finset.univ
      (b.equivFun x) b]
  rw [psuC2dE_Hc]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hinner : H (b i) (∑ j, b.equivFun y j • b j) = b.equivFun y i := by
    rw [psuC2dE_H_sum_right H hHaddR hHsmulR (psuC2dE_H_zero_right H hHaddR) Finset.univ
      (b.equivFun y) b]
    rw [Finset.sum_eq_single i]
    · simp [hb]
    · intro j _ hji
      rw [hb, if_neg (Ne.symm hji), mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [hinner]

private noncomputable def psuC2dE_conjEquiv {k : ℕ} {F : Type} [Field F] {V : Type}
    [AddCommGroup V] [Module F V] (b : Module.Basis (Fin k) F V) :
    ((Fin k → F) ≃ₗ[F] (Fin k → F)) ≃* (V ≃ₗ[F] V) where
  toFun L := b.equivFun.trans (L.trans b.equivFun.symm)
  invFun L := b.equivFun.symm.trans (L.trans b.equivFun)
  left_inv L := by
    ext x
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.apply_symm_apply]
  right_inv L := by
    ext x
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.apply_symm_apply]
  map_mul' L L' := by
    ext x
    simp only [LinearEquiv.trans_apply, LinearEquiv.mul_apply]
    rw [LinearEquiv.apply_symm_apply]

private noncomputable def psuC2dE_gA {k : ℕ} {F : Type} [Field F] {V : Type}
    [AddCommGroup V] [Module F V] (b : Module.Basis (Fin k) F V) (A : GL (Fin k) F) :
    V ≃ₗ[F] V :=
  psuC2dE_conjEquiv b ((LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin k → F))
    (Matrix.GeneralLinearGroup.toLin A))

private lemma psuC2dE_gA_equivFun {k : ℕ} {F : Type} [Field F] {V : Type}
    [AddCommGroup V] [Module F V] (b : Module.Basis (Fin k) F V) (A : GL (Fin k) F) (x : V) :
    b.equivFun (psuC2dE_gA b A x) =
      ((A : Matrix (Fin k) (Fin k) F)) *ᵥ b.equivFun x := by
  change b.equivFun (b.equivFun.symm
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin k → F))
      (Matrix.GeneralLinearGroup.toLin A) (b.equivFun x))) = _
  rw [LinearEquiv.apply_symm_apply]
  change (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv (b.equivFun x) = _
  rw [LinearMap.GeneralLinearGroup.coe_toLinearEquiv, Matrix.GeneralLinearGroup.toLin_apply,
    Matrix.mulVecLin_apply]

private lemma psuC2dE_gA_isometry {k : ℕ} {F : Type} [Field F] {τ : F ≃+* F} {V : Type}
    [AddCommGroup V] [Module F V] (H : V → V → F)
    (hHaddL : ∀ x y z, H (x + y) z = H x z + H y z)
    (hHaddR : ∀ x y z, H x (y + z) = H x y + H x z)
    (hHsmulL : ∀ (a : F) x y, H (a • x) y = τ a * H x y)
    (hHsmulR : ∀ (a : F) x y, H x (a • y) = a * H x y)
    (b : Module.Basis (Fin k) F V)
    (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0)
    (A : SUid τ k) (x y : V) :
    H (psuC2dE_gA b (A : GL (Fin k) F) x) (psuC2dE_gA b (A : GL (Fin k) F) y) = H x y := by
  rw [psuC2dE_H_eq_Hc H hHaddL hHaddR hHsmulL hHsmulR b hb x y,
    psuC2dE_H_eq_Hc H hHaddL hHaddR hHsmulL hHsmulR b hb
      (psuC2dE_gA b (A : GL (Fin k) F) x) (psuC2dE_gA b (A : GL (Fin k) F) y)]
  rw [psuC2dE_gA_equivFun b (A : GL (Fin k) F) x,
    psuC2dE_gA_equivFun b (A : GL (Fin k) F) y]
  exact psuC2dE_Hc_mulVec A (b.equivFun x) (b.equivFun y)

private lemma psuC2dE_e_psi_mulVec {n : ℕ} {K : Type} [Field K]
    {F : Type} [Field F]
    {e : Matrix (Fin n) (Fin n) K} (hee : e * e = e)
    [Module F (psuC2dS_V e)]
    (ψ : (psuC2dS_V e ≃ₗ[F] psuC2dS_V e) →* GL (Fin n) K)
    (hψw : ∀ (g : psuC2dS_V e ≃ₗ[F] psuC2dS_V e) (w : psuC2dS_V e),
      (ψ g : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) = ((g w : psuC2dS_V e) : Fin n → K))
    (hψfix : ∀ g, (ψ g : Matrix (Fin n) (Fin n) K) * (1 - e) = 1 - e)
    (g : psuC2dS_V e ≃ₗ[F] psuC2dS_V e) (u : Fin n → K) :
    e *ᵥ ((ψ g : Matrix (Fin n) (Fin n) K) *ᵥ u) =
      ((g ⟨e *ᵥ u, ⟨u, Matrix.mulVecLin_apply e u⟩⟩ : psuC2dS_V e) : Fin n → K) := by
  set w : psuC2dS_V e := ⟨e *ᵥ u, ⟨u, Matrix.mulVecLin_apply e u⟩⟩ with hw
  have h1 : (ψ g : Matrix (Fin n) (Fin n) K) *ᵥ (e *ᵥ u) = ((g w : psuC2dS_V e) : Fin n → K) :=
    hψw g w
  have h2 : (ψ g : Matrix (Fin n) (Fin n) K) *ᵥ ((1 - e) *ᵥ u) = (1 - e) *ᵥ u := by
    rw [Matrix.mulVec_mulVec, hψfix g]
  have hdecomp : (ψ g : Matrix (Fin n) (Fin n) K) *ᵥ u =
      (ψ g : Matrix (Fin n) (Fin n) K) *ᵥ (e *ᵥ u) +
        (ψ g : Matrix (Fin n) (Fin n) K) *ᵥ ((1 - e) *ᵥ u) := by
    rw [← Matrix.mulVec_add, psuC2dE_add_one_sub_mulVec]
  calc e *ᵥ ((ψ g : Matrix (Fin n) (Fin n) K) *ᵥ u)
      = e *ᵥ ((ψ g : Matrix (Fin n) (Fin n) K) *ᵥ (e *ᵥ u)) +
          e *ᵥ ((ψ g : Matrix (Fin n) (Fin n) K) *ᵥ ((1 - e) *ᵥ u)) := by
          rw [hdecomp, Matrix.mulVec_add]
    _ = e *ᵥ ((g w : psuC2dS_V e) : Fin n → K) + e *ᵥ ((1 - e) *ᵥ u) := by rw [h1, h2]
    _ = ((g w : psuC2dS_V e) : Fin n → K) + 0 := by
          rw [psuC2dE_mulVec_eq_of_mem_Ve hee (g w).2, psuC2dE_e_mulVec_one_sub hee]
    _ = ((g w : psuC2dS_V e) : Fin n → K) := by rw [add_zero]

private lemma psuC2dE_one_sub_psi_mulVec {n : ℕ} {K : Type} [Field K]
    {F : Type} [Field F]
    {e : Matrix (Fin n) (Fin n) K} (hee : e * e = e)
    [Module F (psuC2dS_V e)]
    (ψ : (psuC2dS_V e ≃ₗ[F] psuC2dS_V e) →* GL (Fin n) K)
    (hψw : ∀ (g : psuC2dS_V e ≃ₗ[F] psuC2dS_V e) (w : psuC2dS_V e),
      (ψ g : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) = ((g w : psuC2dS_V e) : Fin n → K))
    (hψfix : ∀ g, (ψ g : Matrix (Fin n) (Fin n) K) * (1 - e) = 1 - e)
    (g : psuC2dS_V e ≃ₗ[F] psuC2dS_V e) (u : Fin n → K) :
    (1 - e) *ᵥ ((ψ g : Matrix (Fin n) (Fin n) K) *ᵥ u) = (1 - e) *ᵥ u := by
  set w : psuC2dS_V e := ⟨e *ᵥ u, ⟨u, Matrix.mulVecLin_apply e u⟩⟩ with hw
  have h1 : (ψ g : Matrix (Fin n) (Fin n) K) *ᵥ (e *ᵥ u) = ((g w : psuC2dS_V e) : Fin n → K) :=
    hψw g w
  have h2 : (ψ g : Matrix (Fin n) (Fin n) K) *ᵥ ((1 - e) *ᵥ u) = (1 - e) *ᵥ u := by
    rw [Matrix.mulVec_mulVec, hψfix g]
  have hdecomp : (ψ g : Matrix (Fin n) (Fin n) K) *ᵥ u =
      (ψ g : Matrix (Fin n) (Fin n) K) *ᵥ (e *ᵥ u) +
        (ψ g : Matrix (Fin n) (Fin n) K) *ᵥ ((1 - e) *ᵥ u) := by
    rw [← Matrix.mulVec_add, psuC2dE_add_one_sub_mulVec]
  calc (1 - e) *ᵥ ((ψ g : Matrix (Fin n) (Fin n) K) *ᵥ u)
      = (1 - e) *ᵥ ((ψ g : Matrix (Fin n) (Fin n) K) *ᵥ (e *ᵥ u)) +
          (1 - e) *ᵥ ((ψ g : Matrix (Fin n) (Fin n) K) *ᵥ ((1 - e) *ᵥ u)) := by
          rw [hdecomp, Matrix.mulVec_add]
    _ = (1 - e) *ᵥ ((g w : psuC2dS_V e) : Fin n → K) + (1 - e) *ᵥ ((1 - e) *ᵥ u) := by
          rw [h1, h2]
    _ = 0 + (1 - e) *ᵥ u := by
          rw [psuC2dE_one_sub_mulVec_eq_zero_of_mem_Ve hee (g w).2,
            psuC2dE_one_sub_mulVec_one_sub hee]
    _ = (1 - e) *ᵥ u := by rw [zero_add]

private lemma psuC2dE_hf_psi_Ve {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    {e : Matrix (Fin n) (Fin n) K}
    {F : Type} [Field F] [Algebra K F]
    [Module F (psuC2dS_V e)]
    (g : psuC2dS_V e ≃ₗ[F] psuC2dS_V e)
    (H : psuC2dS_V e → psuC2dS_V e → F)
    (hg : ∀ x y, H (g x) (g y) = H x y)
    (htr : ∀ x y : psuC2dS_V e,
      psuC2dS_hf h (x : Fin n → K) (y : Fin n → K) = Algebra.trace K F (H x y))
    (x y : psuC2dS_V e) :
    psuC2dS_hf h ((g x : psuC2dS_V e) : Fin n → K) ((g y : psuC2dS_V e) : Fin n → K) =
      psuC2dS_hf h (x : Fin n → K) (y : Fin n → K) := by
  rw [htr (g x) (g y), hg x y, ← htr x y]

private lemma psuC2dE_psi_hf {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K}
    {e : Matrix (Fin n) (Fin n) K} (hee : e * e = e) (hde : psuDag h e = e)
    {F : Type} [Field F] [Algebra K F]
    [Module F (psuC2dS_V e)]
    (ψ : (psuC2dS_V e ≃ₗ[F] psuC2dS_V e) →* GL (Fin n) K)
    (hψw : ∀ (g : psuC2dS_V e ≃ₗ[F] psuC2dS_V e) (w : psuC2dS_V e),
      (ψ g : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) = ((g w : psuC2dS_V e) : Fin n → K))
    (hψfix : ∀ g, (ψ g : Matrix (Fin n) (Fin n) K) * (1 - e) = 1 - e)
    (g : psuC2dS_V e ≃ₗ[F] psuC2dS_V e)
    (H : psuC2dS_V e → psuC2dS_V e → F)
    (hg : ∀ x y : psuC2dS_V e, H (g x) (g y) = H x y)
    (htr : ∀ x y : psuC2dS_V e,
      psuC2dS_hf h (x : Fin n → K) (y : Fin n → K) = Algebra.trace K F (H x y))
    (u v : Fin n → K) :
    psuC2dS_hf h ((ψ g : Matrix (Fin n) (Fin n) K) *ᵥ u)
      ((ψ g : Matrix (Fin n) (Fin n) K) *ᵥ v) = psuC2dS_hf h u v := by
  rw [psuC2dE_hf_decomp h hee hde u v,
    psuC2dE_hf_decomp h hee hde ((ψ g : Matrix (Fin n) (Fin n) K) *ᵥ u)
      ((ψ g : Matrix (Fin n) (Fin n) K) *ᵥ v),
    psuC2dE_e_psi_mulVec hee ψ hψw hψfix g u,
    psuC2dE_e_psi_mulVec hee ψ hψw hψfix g v,
    psuC2dE_one_sub_psi_mulVec hee ψ hψw hψfix g u,
    psuC2dE_one_sub_psi_mulVec hee ψ hψw hψfix g v,
    psuC2dE_hf_psi_Ve h g H hg htr
      ⟨e *ᵥ u, ⟨u, Matrix.mulVecLin_apply e u⟩⟩ ⟨e *ᵥ v, ⟨v, Matrix.mulVecLin_apply e v⟩⟩]

private lemma psuC2dE_hf_entry {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (M : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    ((M.map h.bar)ᵀ * psuJ n K * M) i j =
      psuC2dS_hf h (M *ᵥ Pi.single i 1) (M *ᵥ Pi.single j 1) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, psuC2dS_hf, dotProduct]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.transpose_apply, Matrix.map_apply, Matrix.mulVec_single_one,
    Matrix.mulVec_single_one]
  simp only [Matrix.col_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct]

private lemma psuC2dE_hf_single {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (i j : Fin n) :
    psuC2dS_hf h (Pi.single i (1 : K)) (Pi.single j (1 : K)) = psuJ n K i j := by
  rw [psuC2dS_hf, dotProduct, Matrix.mulVec_single_one]
  simp only [Matrix.col_apply]
  exact (Finset.sum_eq_single i
    (fun k _ hki => by simp [Pi.single_eq_of_ne, hki])
    (fun hi => absurd (Finset.mem_univ i) hi)).trans (by simp)

private lemma psuC2dE_hf_matrix {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (M : Matrix (Fin n) (Fin n) K)
    (hM : ∀ u v, psuC2dS_hf h (M *ᵥ u) (M *ᵥ v) = psuC2dS_hf h u v) :
    (M.map h.bar)ᵀ * psuJ n K * M = psuJ n K := by
  ext i j
  rw [psuC2dE_hf_entry h M i j, ← psuC2dE_hf_single h i j]
  exact hM _ _

private lemma psuC2dE_psi_unitary {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K}
    {e : Matrix (Fin n) (Fin n) K} (hee : e * e = e) (hde : psuDag h e = e)
    {F : Type} [Field F] [Algebra K F]
    [Module F (psuC2dS_V e)]
    (ψ : (psuC2dS_V e ≃ₗ[F] psuC2dS_V e) →* GL (Fin n) K)
    (hψw : ∀ (g : psuC2dS_V e ≃ₗ[F] psuC2dS_V e) (w : psuC2dS_V e),
      (ψ g : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) = ((g w : psuC2dS_V e) : Fin n → K))
    (hψfix : ∀ g, (ψ g : Matrix (Fin n) (Fin n) K) * (1 - e) = 1 - e)
    (g : psuC2dS_V e ≃ₗ[F] psuC2dS_V e)
    (H : psuC2dS_V e → psuC2dS_V e → F)
    (hg : ∀ x y : psuC2dS_V e, H (g x) (g y) = H x y)
    (htr : ∀ x y : psuC2dS_V e,
      psuC2dS_hf h (x : Fin n → K) (y : Fin n → K) = Algebra.trace K F (H x y)) :
    ψ g ∈ primeFormUnitary h (psuJ n K) := by
  rw [mem_primeFormUnitary]
  apply psuC2dE_hf_matrix h ((ψ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  intro u v
  exact psuC2dE_psi_hf (K := K) (h := h) (e := e) (F := F) hee hde ψ hψw hψfix g H hg htr u v

private lemma psuC2dE_hom_trivial_of_perfect {G A : Type} [Group G] [CommGroup A]
    [Group.IsPerfect G] (f : G →* A) : f = 1 := by
  rw [← MonoidHom.ker_eq_top_iff]
  apply top_le_iff.mp
  rw [← Group.IsPerfect.commutator_eq_top (G := G)]
  change ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ f.ker
  rw [Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, mul_comm (f a) (f b),
    mul_assoc (f b) (f a) ((f a)⁻¹), mul_inv_cancel (f a), mul_one, mul_inv_cancel (f b)]

private noncomputable def psuC2dE_psiA {n k : ℕ} {K : Type} [Field K]
    {F : Type} [Field F] {τ : F ≃+* F} {V : Type} [AddCommGroup V] [Module F V]
    (b : Module.Basis (Fin k) F V) (ψ : (V ≃ₗ[F] V) →* GL (Fin n) K) :
    SUid τ k →* GL (Fin n) K :=
  ψ.comp ((psuC2dE_conjEquiv b).toMonoidHom.comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin k → F)).toMonoidHom.comp
      ((Matrix.GeneralLinearGroup.toLin).toMonoidHom.comp (SUid τ k).subtype)))

private lemma psuC2dE_psiA_apply {n k : ℕ} {K : Type} [Field K]
    {F : Type} [Field F] {τ : F ≃+* F} {V : Type} [AddCommGroup V] [Module F V]
    (b : Module.Basis (Fin k) F V) (ψ : (V ≃ₗ[F] V) →* GL (Fin n) K) (A : SUid τ k) :
    psuC2dE_psiA b ψ A = ψ (psuC2dE_gA b (A : GL (Fin k) F)) := by
  rfl

private lemma psuC2dE_psiA_det {n k : ℕ} {K : Type} [Field K]
    {F : Type} [Field F] {τ : F ≃+* F} {V : Type} [AddCommGroup V] [Module F V]
    (b : Module.Basis (Fin k) F V) (ψ : (V ≃ₗ[F] V) →* GL (Fin n) K)
    (hperf : Group.IsPerfect (SUid τ k)) (A : SUid τ k) :
    ((psuC2dE_psiA b ψ A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
  haveI : Group.IsPerfect (SUid τ k) := hperf
  have htriv : Matrix.GeneralLinearGroup.det.comp (psuC2dE_psiA (τ := τ) b ψ) = 1 :=
    psuC2dE_hom_trivial_of_perfect _
  have h := congrArg (fun f : SUid τ k →* Kˣ => f A) htriv
  simpa using congrArg Units.val h

private noncomputable def psuC2dE_phi {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {B : GL (Fin n) K}
    {e : Matrix (Fin n) (Fin n) K} (hee : e * e = e) (hde : psuDag h e = e)
    {F : Type} [Field F] [Algebra K F]
    [Module F (psuC2dS_V e)]
    (ψ : (psuC2dS_V e ≃ₗ[F] psuC2dS_V e) →* GL (Fin n) K)
    (hψw : ∀ (g : psuC2dS_V e ≃ₗ[F] psuC2dS_V e) (w : psuC2dS_V e),
      (ψ g : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) = ((g w : psuC2dS_V e) : Fin n → K))
    (hψfix : ∀ g, (ψ g : Matrix (Fin n) (Fin n) K) * (1 - e) = 1 - e)
    (hψB : ∀ g, (ψ g : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * (ψ g : Matrix (Fin n) (Fin n) K))
    (τ : F ≃+* F) (H : psuC2dS_V e → psuC2dS_V e → F)
    (hHaddL : ∀ x y z, H (x + y) z = H x z + H y z)
    (hHaddR : ∀ x y z, H x (y + z) = H x y + H x z)
    (hHsmulL : ∀ (a : F) x y, H (a • x) y = τ a * H x y)
    (hHsmulR : ∀ (a : F) x y, H x (a • y) = a * H x y)
    (htr : ∀ x y : psuC2dS_V e,
      psuC2dS_hf h (x : Fin n → K) (y : Fin n → K) = Algebra.trace K F (H x y))
    (k : ℕ) (b : Module.Basis (Fin k) F (psuC2dS_V e))
    (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0)
    (hperf : Group.IsPerfect (SUid τ k)) :
    SUid τ k →* ↥(psuBlock h B e) := by
  have hunit : ∀ A : SUid τ k, (psuC2dE_psiA b ψ A : GL (Fin n) K) ∈
      primeFormUnitary h (psuJ n K) := fun A =>
    psuC2dE_psi_unitary hee hde ψ hψw hψfix
      (psuC2dE_gA b (A : GL (Fin k) F)) H
      (fun x y => psuC2dE_gA_isometry H hHaddL hHaddR hHsmulL hHsmulR b hb A x y) htr
  have hdet : ∀ A : SUid τ k,
      ((psuC2dE_psiA b ψ A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 :=
    fun A => psuC2dE_psiA_det b ψ hperf A
  have hXJ : ∀ A : SUid τ k, (psuC2dE_psiA b ψ A : GL (Fin n) K) ∈ AutPSU.XJ h n := by
    intro A
    change (psuC2dE_psiA b ψ A : GL (Fin n) K) ∈ gramSU h (psuJ n K)
    rw [mem_gramSU_iff_unitary]
    exact ⟨hunit A, hdet A⟩
  have hmem : ∀ A : SUid τ k,
      (⟨(psuC2dE_psiA b ψ A : GL (Fin n) K), hXJ A⟩ : AutPSU.XJ h n) ∈
        psuBlock h B e := by
    intro A
    refine Subgroup.mem_comap.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · rw [Subgroup.mem_centralizer_iff]
      intro bB hbB
      rw [Set.mem_singleton_iff] at hbB
      rw [hbB]
      apply Units.ext
      change (B : Matrix (Fin n) (Fin n) K) *
          (psuC2dE_psiA b ψ A : Matrix (Fin n) (Fin n) K) =
        (psuC2dE_psiA b ψ A : Matrix (Fin n) (Fin n) K) *
          (B : Matrix (Fin n) (Fin n) K)
      rw [psuC2dE_psiA_apply]
      exact (hψB (psuC2dE_gA b (A : GL (Fin k) F))).symm
    · have hε : psuOrbitIdem h e = e := by
        rw [psuOrbitIdem, if_pos hde]
      change ((psuC2dE_psiA b ψ A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (1 - psuOrbitIdem h e) = 1 - psuOrbitIdem h e
      rw [hε, psuC2dE_psiA_apply]
      exact hψfix (psuC2dE_gA b (A : GL (Fin k) F))
  exact
    { toFun := fun A => ⟨⟨(psuC2dE_psiA b ψ A : GL (Fin n) K), hXJ A⟩, hmem A⟩
      map_one' := Subtype.ext (Subtype.ext (map_one (psuC2dE_psiA b ψ)))
      map_mul' := fun A C => Subtype.ext (Subtype.ext (map_mul (psuC2dE_psiA b ψ) A C)) }

private lemma psuC2dS_embed {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {B : GL (Fin n) K}
    {e : Matrix (Fin n) (Fin n) K} (hee : e * e = e)
    (hde : psuDag h e = e)
    {F : Type} [Field F] [Algebra K F]
    [Module F (psuC2dS_V e)]
    (ψ : (psuC2dS_V e ≃ₗ[F] psuC2dS_V e) →* GL (Fin n) K)
    (hψinj : Function.Injective ψ)
    (hψw : ∀ (g : psuC2dS_V e ≃ₗ[F] psuC2dS_V e) (w : psuC2dS_V e),
      (ψ g : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) = ((g w : psuC2dS_V e) : Fin n → K))
    (hψfix : ∀ g, (ψ g : Matrix (Fin n) (Fin n) K) * (1 - e) = 1 - e)
    (hψB : ∀ g, (ψ g : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * (ψ g : Matrix (Fin n) (Fin n) K))
    (τ : F ≃+* F) (H : psuC2dS_V e → psuC2dS_V e → F)
    (hHaddL : ∀ x y z, H (x + y) z = H x z + H y z)
    (hHaddR : ∀ x y z, H x (y + z) = H x y + H x z)
    (hHsmulL : ∀ (a : F) x y, H (a • x) y = τ a * H x y)
    (hHsmulR : ∀ (a : F) x y, H x (a • y) = a * H x y)
    (htr : ∀ x y : psuC2dS_V e,
      psuC2dS_hf h (x : Fin n → K) (y : Fin n → K) = Algebra.trace K F (H x y))
    (k : ℕ) (b : Module.Basis (Fin k) F (psuC2dS_V e))
    (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0)
    (hperf : Group.IsPerfect ↥(CFSG.LieType.Universal.Unitary.SUid τ k)) :
    ∃ Y : Subgroup ↥(psuBlock h B e),
      Nonempty (↥Y ≃* ↥(CFSG.LieType.Universal.Unitary.SUid τ k)) := by
  let φ : SUid τ k →* ↥(psuBlock h B e) :=
    psuC2dE_phi hee hde ψ hψw hψfix hψB τ H hHaddL hHaddR hHsmulL hHsmulR htr k b hb hperf
  have hφinj : Function.Injective φ := by
    intro A C hAC
    have h1 : (psuC2dE_psiA b ψ A : GL (Fin n) K) = psuC2dE_psiA b ψ C := by
      have h' := congrArg (fun x : ↥(psuBlock h B e) =>
        ((x : AutPSU.XJ h n) : GL (Fin n) K)) hAC
      exact h'
    rw [psuC2dE_psiA_apply, psuC2dE_psiA_apply] at h1
    have h2 : psuC2dE_gA b (A : GL (Fin k) F) = psuC2dE_gA b (C : GL (Fin k) F) :=
      hψinj h1
    have h3 : Matrix.GeneralLinearGroup.toLin (A : GL (Fin k) F) =
        Matrix.GeneralLinearGroup.toLin (C : GL (Fin k) F) :=
      (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin k → F)).injective
        ((psuC2dE_conjEquiv b).injective h2)
    exact Subtype.ext (Matrix.GeneralLinearGroup.toLin.injective h3)
  exact ⟨φ.range, ⟨(MonoidHom.ofInjective hφinj).symm⟩⟩

private lemma psuC2dD_dual_facts {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hde : psuDag h e ≠ e) :
    psuDag h e ∈ P ∧ e * psuDag h e = 0 ∧ psuDag h e * e = 0 ∧
      psuOrbitIdem h e = e + psuDag h e ∧ IsIdempotentElem (psuOrbitIdem h e) := by
  obtain ⟨P', hP', hperm⟩ := psuGraph_primFamily S
  have hedP : psuDag h e ∈ P := by
    have heP' : e ∈ P' := (hP'.1 e).mpr ((hP.1 e).mp he)
    exact (hP.1 (psuDag h e)).mpr ((hP'.1 (psuDag h e)).mp ((hperm e heP').1))
  have horth : e * psuDag h e = 0 := hP.2.1 e he (psuDag h e) hedP (Ne.symm hde)
  have horth' : psuDag h e * e = 0 := hP.2.1 (psuDag h e) hedP e he hde
  have horb : psuOrbitIdem h e = e + psuDag h e := by
    unfold psuOrbitIdem
    rw [if_neg hde]
  refine ⟨hedP, horth, horth', horb, ?_⟩
  have hee : e * e = e := ((hP.1 e).mp he).2.1
  have hdd : psuDag h e * psuDag h e = psuDag h e := ((hP.1 (psuDag h e)).mp hedP).2.1
  rw [horb, IsIdempotentElem]
  simp only [mul_add, add_mul, hee, hdd, horth, horth', add_zero, zero_add]

private lemma psuC2dD_card {f d : ℕ} {K F : Type} [Field K]
    (h : UnitaryFieldData 2 f K)
    (hcard : Nat.card F = Nat.card K ^ d) :
    Nat.card F = (2 ^ f) ^ (2 * d) := by
  rw [hcard, UnitaryFieldData.card_eq_sq h, ← pow_mul]

private lemma psuC2dD_card_ge_four {f d : ℕ} {F : Type} [Field F] [Finite F]
    (hcard : Nat.card F = (2 ^ f) ^ (2 * d)) : 4 ≤ Nat.card F := by
  haveI : Fintype F := Fintype.ofFinite F
  have h2 : 2 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hf : 1 ≤ f := by
    by_contra hf
    have hf0 : f = 0 := by omega
    rw [hf0, pow_zero, one_pow] at hcard
    omega
  have hd : 1 ≤ d := by
    by_contra hd
    have hd0 : d = 0 := by omega
    rw [hd0, Nat.mul_zero, pow_zero] at hcard
    omega
  rw [hcard]
  have hf2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h2d : 2 ≤ 2 * d := by omega
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left hf2 2
    _ ≤ (2 ^ f) ^ (2 * d) := Nat.pow_le_pow_right (by positivity) h2d

private lemma psuC2dD_k_ge_two {d k r : ℕ} (hrank : r = d * k) (hr : r ≠ d) (hkpos : 0 < k) :
    2 ≤ k := by
  by_contra h
  have hk1 : k = 1 := by omega
  exact hr (by rw [hrank, hk1, mul_one])

private lemma psuC2dD_SL_isPerfect {k : ℕ} {F : Type} [Field F] [Finite F]
    (hk : 2 ≤ k) (hbig : 4 ≤ Nat.card F) :
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin k) F) := by
  refine CFSG.LinearGroups.special_linear_isPerfect hk ?_
  by_cases hk3 : 3 ≤ k
  · exact Or.inl hk3
  · right
    haveI : Fintype F := Fintype.ofFinite F
    have h4 : 4 ≤ (Finset.univ : Finset F).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact hbig
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := Finset.univ) h4
    exact ⟨s, hs⟩

private lemma psuC2dD_hom_trivial_of_perfect {G M : Type} [Group G] [Group.IsPerfect G]
    [CommGroup M] (f : G →* M) : ∀ g : G, f g = 1 := by
  have h : f = 1 := by
    rw [← MonoidHom.ker_eq_top_iff]
    apply top_le_iff.mp
    rw [← Group.IsPerfect.commutator_eq_top (G := G)]
    change ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ f.ker
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def,
      mul_comm (f a) (f b), mul_assoc (f b) (f a) ((f a)⁻¹), mul_inv_cancel (f a), mul_one,
      mul_inv_cancel (f b)]
  intro g
  rw [h]
  rfl

private lemma psuC2dD_SL_to_lin {k : ℕ} {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (b : Module.Basis (Fin k) F V) :
    ∃ ι : Matrix.SpecialLinearGroup (Fin k) F →* (V ≃ₗ[F] V), Function.Injective ι := by
  let A0 : Type := Fin k → F
  let iotaBar : Matrix.SpecialLinearGroup (Fin k) F →* (A0 ≃ₗ[F] A0) :=
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv F A0).toMonoidHom).comp
      ((Matrix.GeneralLinearGroup.toLin).toMonoidHom.comp (Matrix.SpecialLinearGroup.toGL))
  have hIotaBar : Function.Injective iotaBar := by
    intro g h hgh
    exact SpecialLinearGroup.toGL_injective
      (Matrix.GeneralLinearGroup.toLin.injective
        ((LinearMap.GeneralLinearGroup.generalLinearEquiv F A0).injective hgh))
  let c : A0 ≃ₗ[F] V := b.equivFun.symm
  let conjC : (A0 ≃ₗ[F] A0) ≃* (V ≃ₗ[F] V) :=
    { toFun := fun e => c.symm.trans (e.trans c)
      invFun := fun e => c.trans (e.trans c.symm)
      left_inv := fun e => by
        apply LinearEquiv.ext
        intro w
        simp [LinearEquiv.trans_apply]
      right_inv := fun e => by
        apply LinearEquiv.ext
        intro w
        simp [LinearEquiv.trans_apply]
      map_mul' := fun e f => by
        apply LinearEquiv.ext
        intro w
        simp [LinearEquiv.trans_apply, map_mul] }
  let iota : Matrix.SpecialLinearGroup (Fin k) F →* (V ≃ₗ[F] V) := conjC.toMonoidHom.comp iotaBar
  exact ⟨iota, conjC.injective.comp hIotaBar⟩

private lemma psuC2dD_B_dag {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B) :
    psuDag h (B : Matrix (Fin n) (Fin n) K) =
      ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have hB : ((B : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * psuJ n K *
      (B : Matrix (Fin n) (Fin n) K) = psuJ n K := (mem_primeFormUnitary).mp S.B_mem
  have hJinv : (psuJ n K)⁻¹ * psuJ n K = 1 := by
    rw [psuJ, ← Matrix.coe_units_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hmul : psuDag h (B : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) = 1 := by
    calc psuDag h (B : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K)
        = (psuJ n K)⁻¹ * (((B : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * psuJ n K *
            (B : Matrix (Fin n) (Fin n) K)) := by
          rw [psuDag, formAdj]
          noncomm_ring
      _ = (psuJ n K)⁻¹ * psuJ n K := by rw [hB]
      _ = 1 := hJinv
  calc psuDag h (B : Matrix (Fin n) (Fin n) K)
      = psuDag h (B : Matrix (Fin n) (Fin n) K) *
          ((B : Matrix (Fin n) (Fin n) K) *
            ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    _ = (psuDag h (B : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K)) *
          ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [Matrix.mul_assoc]
    _ = ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [hmul, Matrix.one_mul]

private lemma psuC2dD_dag_one_sub {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (a : Matrix (Fin n) (Fin n) K) :
    psuDag h (1 - a) = 1 - psuDag h a := by
  rw [sub_eq_add_neg, psuDag_add, psuDag_one, show -a = (-1 : K) • a from by rw [neg_one_smul],
    psuDag_smul, map_neg, map_one, neg_one_smul]
  rw [sub_eq_add_neg]

private noncomputable def psuC2dD_dagUnit {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (M : GL (Fin n) K) : GL (Fin n) K :=
  ⟨psuDag h (M : Matrix (Fin n) (Fin n) K),
   psuDag h ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
   by rw [← psuDag_mul h ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
           (M : Matrix (Fin n) (Fin n) K), ← Units.val_mul, inv_mul_cancel, Units.val_one,
         psuDag_one],
   by rw [← psuDag_mul h (M : Matrix (Fin n) (Fin n) K)
           ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), ← Units.val_mul, mul_inv_cancel,
         Units.val_one, psuDag_one]⟩

private noncomputable def psuC2dD_xUnit {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (M : GL (Fin n) K) : GL (Fin n) K :=
  M * (psuC2dD_dagUnit h M)⁻¹

private lemma psuC2dD_dagUnit_coe {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (M : GL (Fin n) K) :
    ((psuC2dD_dagUnit h M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      psuDag h (M : Matrix (Fin n) (Fin n) K) := rfl

private lemma psuC2dD_xUnit_coe {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (M : GL (Fin n) K) :
    ((psuC2dD_xUnit h M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (M : Matrix (Fin n) (Fin n) K) *
        psuDag h ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl

private lemma psuC2dD_dag_comm_B {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    {M : GL (Fin n) K}
    (hMB : (M : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * (M : Matrix (Fin n) (Fin n) K)) :
    psuDag h (M : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * psuDag h (M : Matrix (Fin n) (Fin n) K) := by
  have hBdag := psuC2dD_B_dag S
  have h1 : psuDag h (M : Matrix (Fin n) (Fin n) K) *
      ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        psuDag h (M : Matrix (Fin n) (Fin n) K) := by
    have h2 : psuDag h (B : Matrix (Fin n) (Fin n) K) *
        psuDag h (M : Matrix (Fin n) (Fin n) K) =
        psuDag h (M : Matrix (Fin n) (Fin n) K) *
          psuDag h (B : Matrix (Fin n) (Fin n) K) := by
      rw [← psuDag_mul, ← psuDag_mul, hMB]
    rw [hBdag] at h2
    exact h2.symm
  have hBBinv : (B : Matrix (Fin n) (Fin n) K) *
      ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hBinvB : ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (B : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc psuDag h (M : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K)
      = ((B : Matrix (Fin n) (Fin n) K) *
          ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
          (psuDag h (M : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K)) := by
        rw [hBBinv, Matrix.one_mul]
    _ = (B : Matrix (Fin n) (Fin n) K) *
          (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            psuDag h (M : Matrix (Fin n) (Fin n) K)) *
          (B : Matrix (Fin n) (Fin n) K) := by noncomm_ring
    _ = (B : Matrix (Fin n) (Fin n) K) *
          (psuDag h (M : Matrix (Fin n) (Fin n) K) *
            ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
          (B : Matrix (Fin n) (Fin n) K) := by rw [← h1]
    _ = (B : Matrix (Fin n) (Fin n) K) * psuDag h (M : Matrix (Fin n) (Fin n) K) *
          (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (B : Matrix (Fin n) (Fin n) K)) := by noncomm_ring
    _ = (B : Matrix (Fin n) (Fin n) K) * psuDag h (M : Matrix (Fin n) (Fin n) K) := by
        rw [hBinvB, Matrix.mul_one]

private lemma psuC2dD_comm_alg {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K)
    {M : Matrix (Fin n) (Fin n) K}
    (hMB : M * (B : Matrix (Fin n) (Fin n) K) = (B : Matrix (Fin n) (Fin n) K) * M) :
    ∀ a ∈ psuAlg B, M * a = a * M := by
  intro a ha
  refine Algebra.adjoin_induction (p := fun x _ => M * x = x * M) ?_ ?_ ?_ ?_ ha
  · rintro x ⟨s, hs, rfl⟩
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact hMB
  · intro r
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul]
  · intro x y _ _ hpx hpy
    rw [mul_add, add_mul, hpx, hpy]
  · intro x y _ _ hpx hpy
    calc M * (x * y) = (M * x) * y := (Matrix.mul_assoc M x y).symm
      _ = (x * M) * y := by rw [hpx]
      _ = x * (M * y) := Matrix.mul_assoc x M y
      _ = x * (y * M) := by rw [hpy]
      _ = (x * y) * M := (Matrix.mul_assoc x y M).symm

private lemma psuC2dD_one_sub_idem {n : ℕ} {K : Type} [Ring K]
    {ε : Matrix (Fin n) (Fin n) K} (h : ε * ε = ε) : (1 - ε) * (1 - ε) = 1 - ε := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, h]
  abel

private lemma psuC2dD_mul_one_sub_of_mul_eq {n : ℕ} {K : Type} [Ring K]
    {p ε : Matrix (Fin n) (Fin n) K} (h : p * ε = p) : p * (1 - ε) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, h, sub_self]

private lemma psuC2dD_one_sub_mul_of_mul_eq {n : ℕ} {K : Type} [Ring K]
    {p ε : Matrix (Fin n) (Fin n) K} (h : ε * p = p) : (1 - ε) * p = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, h, sub_self]

private lemma psuC2dD_M_mul_ed {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hde : psuDag h e ≠ e)
    {G : Type} (Ψ : G → GL (Fin n) K)
    (hΨe : ∀ g, e * (Ψ g : Matrix (Fin n) (Fin n) K) =
      (Ψ g : Matrix (Fin n) (Fin n) K) * e)
    (hΨfix : ∀ g, (Ψ g : Matrix (Fin n) (Fin n) K) * (1 - e) = 1 - e) (g : G) :
    (Ψ g : Matrix (Fin n) (Fin n) K) * psuDag h e = psuDag h e ∧
      psuDag h e * (Ψ g : Matrix (Fin n) (Fin n) K) = psuDag h e := by
  obtain ⟨hedP, horth, horth', horb, hεidem⟩ := psuC2dD_dual_facts S P hP e he hde
  have hMg : (Ψ g : Matrix (Fin n) (Fin n) K) =
      (Ψ g : Matrix (Fin n) (Fin n) K) * e + (1 - e) := by
    calc (Ψ g : Matrix (Fin n) (Fin n) K) = (Ψ g : Matrix (Fin n) (Fin n) K) * 1 :=
          (Matrix.mul_one _).symm
      _ = (Ψ g : Matrix (Fin n) (Fin n) K) * (e + (1 - e)) := by rw [add_sub_cancel]
      _ = (Ψ g : Matrix (Fin n) (Fin n) K) * e + (Ψ g : Matrix (Fin n) (Fin n) K) * (1 - e) := by
          rw [Matrix.mul_add]
      _ = (Ψ g : Matrix (Fin n) (Fin n) K) * e + (1 - e) := by rw [hΨfix g]
  constructor
  · calc (Ψ g : Matrix (Fin n) (Fin n) K) * psuDag h e
        = ((Ψ g : Matrix (Fin n) (Fin n) K) * e + (1 - e)) * psuDag h e := by
            conv_lhs => rw [hMg]
      _ = (Ψ g : Matrix (Fin n) (Fin n) K) * e * psuDag h e + (1 - e) * psuDag h e := by
          rw [Matrix.add_mul]
      _ = (Ψ g : Matrix (Fin n) (Fin n) K) * (e * psuDag h e) + (1 - e) * psuDag h e := by
          rw [Matrix.mul_assoc]
      _ = psuDag h e := by
          rw [horth, Matrix.mul_zero, zero_add, Matrix.sub_mul, Matrix.one_mul, horth, sub_zero]
  · calc psuDag h e * (Ψ g : Matrix (Fin n) (Fin n) K)
        = psuDag h e * ((Ψ g : Matrix (Fin n) (Fin n) K) * e + (1 - e)) := by
            conv_lhs => rw [hMg]
      _ = psuDag h e * ((Ψ g : Matrix (Fin n) (Fin n) K) * e) + psuDag h e * (1 - e) := by
          rw [Matrix.mul_add]
      _ = psuDag h e * (e * (Ψ g : Matrix (Fin n) (Fin n) K)) + psuDag h e * (1 - e) := by
          rw [hΨe g]
      _ = (psuDag h e * e) * (Ψ g : Matrix (Fin n) (Fin n) K) + psuDag h e * (1 - e) := by
          rw [Matrix.mul_assoc]
      _ = psuDag h e := by
          rw [horth', Matrix.zero_mul, zero_add, Matrix.mul_sub, Matrix.mul_one, horth', sub_zero]

private lemma psuC2dD_Mdag_e {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hde : psuDag h e ≠ e)
    {G : Type} (Ψ : G → GL (Fin n) K)
    (hΨe : ∀ g, e * (Ψ g : Matrix (Fin n) (Fin n) K) =
      (Ψ g : Matrix (Fin n) (Fin n) K) * e)
    (hΨfix : ∀ g, (Ψ g : Matrix (Fin n) (Fin n) K) * (1 - e) = 1 - e) (g : G) :
    psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) * e = e ∧
      e * psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) = e := by
  obtain ⟨h1, h2⟩ := psuC2dD_M_mul_ed S P hP e he hde Ψ hΨe hΨfix g
  constructor
  · have h := congrArg (psuDag h) h2
    rw [psuDag_mul, psuDag_dag] at h
    exact h
  · have h := congrArg (psuDag h) h1
    rw [psuDag_mul, psuDag_dag] at h
    exact h

private lemma psuC2dD_M_fix {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hde : psuDag h e ≠ e)
    {G : Type} (Ψ : G → GL (Fin n) K)
    (hΨfix : ∀ g, (Ψ g : Matrix (Fin n) (Fin n) K) * (1 - e) = 1 - e) (g : G) :
    (Ψ g : Matrix (Fin n) (Fin n) K) * (1 - e - psuDag h e) = 1 - e - psuDag h e := by
  obtain ⟨hedP, horth, horth', horb, hεidem⟩ := psuC2dD_dual_facts S P hP e he hde
  have hfac : (1 - e) * (1 - psuDag h e) = 1 - e - psuDag h e := by
    calc (1 - e) * (1 - psuDag h e)
        = 1 * (1 - psuDag h e) - e * (1 - psuDag h e) := by rw [Matrix.sub_mul]
      _ = (1 - psuDag h e) - (e * 1 - e * psuDag h e) := by rw [Matrix.one_mul, Matrix.mul_sub]
      _ = (1 - psuDag h e) - (e - 0) := by rw [Matrix.mul_one, horth]
      _ = 1 - e - psuDag h e := by abel
  rw [← hfac, ← Matrix.mul_assoc, hΨfix g, hfac]

private lemma psuC2dD_Mdag_fix {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hde : psuDag h e ≠ e)
    {G : Type} (Ψ : G → GL (Fin n) K)
    (hΨB : ∀ g, (Ψ g : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * (Ψ g : Matrix (Fin n) (Fin n) K))
    (hΨfix : ∀ g, (Ψ g : Matrix (Fin n) (Fin n) K) * (1 - e) = 1 - e) (g : G) :
    psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) * (1 - e - psuDag h e) =
      1 - e - psuDag h e := by
  obtain ⟨hedP, horth, horth', horb, hεidem⟩ := psuC2dD_dual_facts S P hP e he hde
  have heA : e ∈ psuAlg B := ((hP.1 e).mp he).1
  have hedA : psuDag h e ∈ psuAlg B := (psuGraph_star_mem S e heA).1
  have h1eA : (1 - e) ∈ psuAlg B := Subalgebra.sub_mem _ (Subalgebra.one_mem _) heA
  have hcommA := psuC2dD_comm_alg B (psuC2dD_dag_comm_B S (hΨB g))
  have h1med : psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) * (1 - psuDag h e) = 1 - psuDag h e := by
    have hh := congrArg (psuDag h) (hΨfix g)
    rw [psuDag_mul, psuC2dD_dag_one_sub] at hh
    rw [← hcommA (1 - psuDag h e) (Subalgebra.sub_mem _ (Subalgebra.one_mem _) hedA)] at hh
    exact hh
  have hfac : (1 - e) * (1 - psuDag h e) = 1 - e - psuDag h e := by
    calc (1 - e) * (1 - psuDag h e)
        = 1 * (1 - psuDag h e) - e * (1 - psuDag h e) := by rw [Matrix.sub_mul]
      _ = (1 - psuDag h e) - (e * 1 - e * psuDag h e) := by rw [Matrix.one_mul, Matrix.mul_sub]
      _ = (1 - psuDag h e) - (e - 0) := by rw [Matrix.mul_one, horth]
      _ = 1 - e - psuDag h e := by abel
  rw [← hfac, ← Matrix.mul_assoc, hcommA (1 - e) h1eA, Matrix.mul_assoc, h1med]

private lemma psuC2dD_M_decomp {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hde : psuDag h e ≠ e)
    {G : Type} (Ψ : G → GL (Fin n) K)
    (hΨe : ∀ g, e * (Ψ g : Matrix (Fin n) (Fin n) K) =
      (Ψ g : Matrix (Fin n) (Fin n) K) * e)
    (hΨfix : ∀ g, (Ψ g : Matrix (Fin n) (Fin n) K) * (1 - e) = 1 - e) (g : G) :
    (Ψ g : Matrix (Fin n) (Fin n) K) =
      e * (Ψ g : Matrix (Fin n) (Fin n) K) * e + psuDag h e + (1 - e - psuDag h e) := by
  obtain ⟨hedP, horth, horth', horb, hεidem⟩ := psuC2dD_dual_facts S P hP e he hde
  have hee : e * e = e := ((hP.1 e).mp he).2.1
  have hMed : (Ψ g : Matrix (Fin n) (Fin n) K) * psuDag h e = psuDag h e :=
    (psuC2dD_M_mul_ed S P hP e he hde Ψ hΨe hΨfix g).1
  have hMfix := psuC2dD_M_fix S P hP e he hde Ψ hΨfix g
  have heM : e * (Ψ g : Matrix (Fin n) (Fin n) K) * e = e * (Ψ g : Matrix (Fin n) (Fin n) K) := by
    calc e * (Ψ g : Matrix (Fin n) (Fin n) K) * e = ((Ψ g : Matrix (Fin n) (Fin n) K) * e) * e := by
          rw [hΨe g]
      _ = (Ψ g : Matrix (Fin n) (Fin n) K) * (e * e) := by rw [Matrix.mul_assoc]
      _ = (Ψ g : Matrix (Fin n) (Fin n) K) * e := by rw [hee]
      _ = e * (Ψ g : Matrix (Fin n) (Fin n) K) := (hΨe g).symm
  have hsum : e + psuDag h e + (1 - e - psuDag h e) = 1 := by abel
  calc (Ψ g : Matrix (Fin n) (Fin n) K) = (Ψ g : Matrix (Fin n) (Fin n) K) * 1 :=
        (Matrix.mul_one _).symm
    _ = (Ψ g : Matrix (Fin n) (Fin n) K) * (e + psuDag h e + (1 - e - psuDag h e)) := by rw [hsum]
    _ = (Ψ g : Matrix (Fin n) (Fin n) K) * e + (Ψ g : Matrix (Fin n) (Fin n) K) * psuDag h e +
          (Ψ g : Matrix (Fin n) (Fin n) K) * (1 - e - psuDag h e) := by
        rw [Matrix.mul_add, Matrix.mul_add]
    _ = e * (Ψ g : Matrix (Fin n) (Fin n) K) * e + psuDag h e + (1 - e - psuDag h e) := by
        rw [hMed, hMfix, ← hΨe g]
        rw [heM]

private lemma psuC2dD_Mdag_decomp {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hde : psuDag h e ≠ e)
    {G : Type} (Ψ : G → GL (Fin n) K)
    (hΨB : ∀ g, (Ψ g : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * (Ψ g : Matrix (Fin n) (Fin n) K))
    (hΨe : ∀ g, e * (Ψ g : Matrix (Fin n) (Fin n) K) =
      (Ψ g : Matrix (Fin n) (Fin n) K) * e)
    (hΨfix : ∀ g, (Ψ g : Matrix (Fin n) (Fin n) K) * (1 - e) = 1 - e) (g : G) :
    psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) =
      e + psuDag h e * psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) * psuDag h e +
        (1 - e - psuDag h e) := by
  obtain ⟨hedP, horth, horth', horb, hεidem⟩ := psuC2dD_dual_facts S P hP e he hde
  have hdd : psuDag h e * psuDag h e = psuDag h e := ((hP.1 (psuDag h e)).mp hedP).2.1
  have heA : e ∈ psuAlg B := ((hP.1 e).mp he).1
  have hedA : psuDag h e ∈ psuAlg B := (psuGraph_star_mem S e heA).1
  have hcommA := psuC2dD_comm_alg B (psuC2dD_dag_comm_B S (hΨB g))
  have hdage : psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) * e = e :=
    (psuC2dD_Mdag_e S P hP e he hde Ψ hΨe hΨfix g).1
  have hdagfix := psuC2dD_Mdag_fix S P hP e he hde Ψ hΨB hΨfix g
  have heddag : psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) * psuDag h e =
      psuDag h e * psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) * psuDag h e := by
    calc psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) * psuDag h e
        = psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) * (psuDag h e * psuDag h e) := by rw [hdd]
      _ = (psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) * psuDag h e) * psuDag h e := by
          rw [Matrix.mul_assoc]
      _ = (psuDag h e * psuDag h (Ψ g : Matrix (Fin n) (Fin n) K)) * psuDag h e := by
          rw [hcommA (psuDag h e) hedA]
      _ = psuDag h e * psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) * psuDag h e := by
          rw [Matrix.mul_assoc]
  have hsum : e + psuDag h e + (1 - e - psuDag h e) = 1 := by abel
  calc psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) =
        psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) * 1 := (Matrix.mul_one _).symm
    _ = psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) *
          (e + psuDag h e + (1 - e - psuDag h e)) := by rw [hsum]
    _ = psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) * e +
          psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) * psuDag h e +
          psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) * (1 - e - psuDag h e) := by
        rw [Matrix.mul_add, Matrix.mul_add]
    _ = e + psuDag h e * psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) * psuDag h e +
          (1 - e - psuDag h e) := by rw [hdage, hdagfix, heddag]

private lemma psuC2dD_M_comm_dag {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hde : psuDag h e ≠ e)
    {G : Type} (Ψ : G → GL (Fin n) K)
    (hΨB : ∀ g, (Ψ g : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * (Ψ g : Matrix (Fin n) (Fin n) K))
    (hΨe : ∀ g, e * (Ψ g : Matrix (Fin n) (Fin n) K) =
      (Ψ g : Matrix (Fin n) (Fin n) K) * e)
    (hΨfix : ∀ g, (Ψ g : Matrix (Fin n) (Fin n) K) * (1 - e) = 1 - e) (g g' : G) :
    (Ψ g' : Matrix (Fin n) (Fin n) K) * psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) =
      psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) * (Ψ g' : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨hedP, horth0, horth0', horb, hεidem0⟩ := psuC2dD_dual_facts S P hP e he hde
  set De : Matrix (Fin n) (Fin n) K := psuDag h e with hDe
  have horth : e * De = 0 := by rw [hDe]; exact horth0
  have horth' : De * e = 0 := by rw [hDe]; exact horth0'
  have hee : e * e = e := ((hP.1 e).mp he).2.1
  have hdd : De * De = De := by rw [hDe]; exact ((hP.1 (psuDag h e)).mp hedP).2.1
  have heps : (e + De) * (e + De) = e + De := by
    have hh := hεidem0
    rw [horb, IsIdempotentElem] at hh
    rw [hDe]
    exact hh
  have hr : (1 - e - De) * (1 - e - De) = 1 - e - De := by
    rw [show 1 - e - De = 1 - (e + De) from by abel, psuC2dD_one_sub_idem heps]
  have hpr : e * (1 - e - De) = 0 := by
    rw [show 1 - e - De = 1 - (e + De) from by abel]
    exact psuC2dD_mul_one_sub_of_mul_eq (by rw [Matrix.mul_add, hee, horth, add_zero])
  have hrp : (1 - e - De) * e = 0 := by
    rw [show 1 - e - De = 1 - (e + De) from by abel]
    exact psuC2dD_one_sub_mul_of_mul_eq (by rw [Matrix.add_mul, hee, horth', add_zero])
  have hqr : De * (1 - e - De) = 0 := by
    rw [show 1 - e - De = 1 - (e + De) from by abel]
    exact psuC2dD_mul_one_sub_of_mul_eq (by rw [Matrix.mul_add, horth', hdd, zero_add])
  have hrq : (1 - e - De) * De = 0 := by
    rw [show 1 - e - De = 1 - (e + De) from by abel]
    exact psuC2dD_one_sub_mul_of_mul_eq (by rw [Matrix.add_mul, horth, hdd, zero_add])
  have hp' : ∀ x, e * (e * x) = e * x := fun x => by rw [← Matrix.mul_assoc, hee]
  have hq' : ∀ x, De * (De * x) = De * x := fun x => by rw [← Matrix.mul_assoc, hdd]
  have hr' : ∀ x, (1 - e - De) * ((1 - e - De) * x) = (1 - e - De) * x := fun x => by
    rw [← Matrix.mul_assoc, hr]
  have hpq' : ∀ x, e * (De * x) = 0 := fun x => by rw [← Matrix.mul_assoc, horth, Matrix.zero_mul]
  have hqp' : ∀ x, De * (e * x) = 0 := fun x => by rw [← Matrix.mul_assoc, horth', Matrix.zero_mul]
  have hpr' : ∀ x, e * ((1 - e - De) * x) = 0 := fun x => by
    rw [← Matrix.mul_assoc, hpr, Matrix.zero_mul]
  have hrp' : ∀ x, (1 - e - De) * (e * x) = 0 := fun x => by
    rw [← Matrix.mul_assoc, hrp, Matrix.zero_mul]
  have hqr' : ∀ x, De * ((1 - e - De) * x) = 0 := fun x => by
    rw [← Matrix.mul_assoc, hqr, Matrix.zero_mul]
  have hrq' : ∀ x, (1 - e - De) * (De * x) = 0 := fun x => by
    rw [← Matrix.mul_assoc, hrq, Matrix.zero_mul]
  set Mg' : Matrix (Fin n) (Fin n) K := (Ψ g' : Matrix (Fin n) (Fin n) K) with hMg'
  set Dg : Matrix (Fin n) (Fin n) K := psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) with hDg
  have hd' : Mg' = e * Mg' * e + De + (1 - e - De) := by
    rw [hMg', hDe]
    exact psuC2dD_M_decomp S P hP e he hde Ψ hΨe hΨfix g'
  have hd : Dg = e + De * Dg * De + (1 - e - De) := by
    rw [hDg, hDe]
    exact psuC2dD_Mdag_decomp S P hP e he hde Ψ hΨB hΨe hΨfix g
  have hleft : Mg' * Dg = e * Mg' * e + De * Dg * De + (1 - e - De) := by
    rw [hd', hd]
    simp only [add_mul, mul_add, Matrix.mul_assoc, hee, hdd, hr, horth, horth', hpr, hrp, hqr, hrq,
      hp', hq', hr', hpq', hqp', hpr', hrp', hqr', hrq', mul_zero, zero_mul, add_zero, zero_add]
  have hright : Dg * Mg' = e * Mg' * e + De * Dg * De + (1 - e - De) := by
    rw [hd, hd']
    simp only [add_mul, mul_add, Matrix.mul_assoc, hee, hdd, hr, horth, horth', hpr, hrp, hqr, hrq,
      hp', hq', hr', hpq', hqp', hpr', hrp', hqr', hrq', mul_zero, zero_mul, add_zero, zero_add]
  rw [hleft, hright]

private lemma psuC2dD_dagUnit_mul {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (N K' : GL (Fin n) K) :
    psuC2dD_dagUnit h (N * K') = psuC2dD_dagUnit h K' * psuC2dD_dagUnit h N := by
  apply Units.ext
  rw [psuC2dD_dagUnit_coe,
    Units.val_mul (psuC2dD_dagUnit h K') (psuC2dD_dagUnit h N),
    psuC2dD_dagUnit_coe, psuC2dD_dagUnit_coe,
    Units.val_mul N K', psuDag_mul]

private lemma psuC2dD_xUnit_mul {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {N K' : GL (Fin n) K}
    (hcomm : (K' : Matrix (Fin n) (Fin n) K) * psuDag h (N : Matrix (Fin n) (Fin n) K) =
      psuDag h (N : Matrix (Fin n) (Fin n) K) * (K' : Matrix (Fin n) (Fin n) K)) :
    psuC2dD_xUnit h (N * K') = psuC2dD_xUnit h N * psuC2dD_xUnit h K' := by
  have hcommU : K' * psuC2dD_dagUnit h N = psuC2dD_dagUnit h N * K' := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, psuC2dD_dagUnit_coe]
    exact hcomm
  have hDiK : (psuC2dD_dagUnit h N)⁻¹ * K' = K' * (psuC2dD_dagUnit h N)⁻¹ := by
    calc (psuC2dD_dagUnit h N)⁻¹ * K'
        = (psuC2dD_dagUnit h N)⁻¹ * K' *
            (psuC2dD_dagUnit h N * (psuC2dD_dagUnit h N)⁻¹) := by group
      _ = (psuC2dD_dagUnit h N)⁻¹ * (K' * psuC2dD_dagUnit h N) *
            (psuC2dD_dagUnit h N)⁻¹ := by group
      _ = (psuC2dD_dagUnit h N)⁻¹ * (psuC2dD_dagUnit h N * K') *
            (psuC2dD_dagUnit h N)⁻¹ := by rw [hcommU]
      _ = K' * (psuC2dD_dagUnit h N)⁻¹ := by group
  simp only [psuC2dD_xUnit]
  rw [psuC2dD_dagUnit_mul, mul_inv_rev (psuC2dD_dagUnit h K') (psuC2dD_dagUnit h N)]
  rw [show (N * K') * ((psuC2dD_dagUnit h N)⁻¹ * (psuC2dD_dagUnit h K')⁻¹) =
      N * ((K' * (psuC2dD_dagUnit h N)⁻¹) * (psuC2dD_dagUnit h K')⁻¹) from by group]
  rw [← hDiK]
  group

private noncomputable def psuC2dD_xHom {n : ℕ} {K : Type} [Field K] {f : ℕ}
    (h : UnitaryFieldData 2 f K) {G : Type} [Group G] (Ψ : G →* GL (Fin n) K)
    (hcomm : ∀ g h', (Ψ h' : Matrix (Fin n) (Fin n) K) * psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) =
      psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) * (Ψ h' : Matrix (Fin n) (Fin n) K)) :
    G →* GL (Fin n) K where
  toFun g := psuC2dD_xUnit h (Ψ g)
  map_one' := by
    apply Units.ext
    rw [psuC2dD_xUnit_coe, map_one, inv_one, Units.val_one, psuDag_one, Matrix.mul_one]
  map_mul' g h' := by
    rw [map_mul]
    exact psuC2dD_xUnit_mul h (hcomm g h')

private lemma psuC2dD_xHom_coe {n : ℕ} {K : Type} [Field K] {f : ℕ}
    (h : UnitaryFieldData 2 f K) {G : Type} [Group G] (Ψ : G →* GL (Fin n) K)
    (hcomm : ∀ g h', (Ψ h' : Matrix (Fin n) (Fin n) K) * psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) =
      psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) * (Ψ h' : Matrix (Fin n) (Fin n) K))
    (g : G) :
    ((psuC2dD_xHom h Ψ hcomm g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (Ψ g : Matrix (Fin n) (Fin n) K) *
        psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl

private lemma psuC2dD_xHom_injective {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hde : psuDag h e ≠ e)
    {G : Type} [Group G] (Ψ : G →* GL (Fin n) K)
    (hΨe : ∀ g, e * (Ψ g : Matrix (Fin n) (Fin n) K) =
      (Ψ g : Matrix (Fin n) (Fin n) K) * e)
    (hΨfix : ∀ g, (Ψ g : Matrix (Fin n) (Fin n) K) * (1 - e) = 1 - e)
    (hΨinj : Function.Injective Ψ)
    (hcomm : ∀ g h', (Ψ h' : Matrix (Fin n) (Fin n) K) * psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) =
      psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) * (Ψ h' : Matrix (Fin n) (Fin n) K)) :
    Function.Injective (psuC2dD_xHom h Ψ hcomm) := by
  have hker : ∀ g, psuC2dD_xHom h Ψ hcomm g = 1 → g = 1 := by
    intro g hg
    have hx : ((psuC2dD_xHom h Ψ hcomm g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [hg, Units.val_one]
    rw [psuC2dD_xHom_coe] at hx
    have hee : e * e = e := ((hP.1 e).mp he).2.1
    have hMM : (Ψ g : Matrix (Fin n) (Fin n) K) = psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) := by
      have h1 : psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) = 1 :=
        (psuC2dD_dagUnit h (Ψ g)).inv_val
      calc (Ψ g : Matrix (Fin n) (Fin n) K) =
            (Ψ g : Matrix (Fin n) (Fin n) K) *
              (psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
                psuDag h (Ψ g : Matrix (Fin n) (Fin n) K)) := by
            rw [h1, Matrix.mul_one]
        _ = ((Ψ g : Matrix (Fin n) (Fin n) K) *
              psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
              psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) := by rw [Matrix.mul_assoc]
        _ = 1 * psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) := by rw [hx]
        _ = psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) := by rw [Matrix.one_mul]
    have hMe : (Ψ g : Matrix (Fin n) (Fin n) K) * e = e := by
      rw [hMM]
      exact (psuC2dD_Mdag_e S P hP e he hde Ψ hΨe hΨfix g).1
    have hMe' : e * (Ψ g : Matrix (Fin n) (Fin n) K) * e = e := by
      rw [Matrix.mul_assoc, hMe, hee]
    have hM1 : (Ψ g : Matrix (Fin n) (Fin n) K) = 1 := by
      calc (Ψ g : Matrix (Fin n) (Fin n) K) =
            e * (Ψ g : Matrix (Fin n) (Fin n) K) * e + psuDag h e + (1 - e - psuDag h e) :=
            psuC2dD_M_decomp S P hP e he hde Ψ hΨe hΨfix g
        _ = 1 := by rw [hMe']; abel
    have hΨg : Ψ g = Ψ 1 := by
      rw [map_one]
      exact Units.ext hM1
    exact hΨinj hΨg
  intro g₁ g₂ hgh
  have h1 : psuC2dD_xHom h Ψ hcomm (g₁ * g₂⁻¹) = 1 := by
    rw [map_mul, map_inv, hgh, mul_inv_cancel]
  have h2 : g₁ * g₂⁻¹ = 1 := hker (g₁ * g₂⁻¹) h1
  calc g₁ = g₁ * g₂⁻¹ * g₂ := by group
    _ = 1 * g₂ := by rw [h2]
    _ = g₂ := by rw [one_mul]

private lemma psuC2dD_xHom_unitary {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K}
    {G : Type} [Group G] (Ψ : G →* GL (Fin n) K)
    (hcomm : ∀ g h', (Ψ h' : Matrix (Fin n) (Fin n) K) * psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) =
      psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) * (Ψ h' : Matrix (Fin n) (Fin n) K)) :
    ∀ g, psuC2dD_xHom h Ψ hcomm g ∈ primeFormUnitary h (psuJ n K) := by
  intro g
  have hJinv : (psuJ n K)⁻¹ * psuJ n K = 1 := by
    rw [psuJ, ← Matrix.coe_units_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hJmul : psuJ n K * (psuJ n K)⁻¹ = 1 := by
    rw [psuJ, ← Matrix.coe_units_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hDN := hcomm g g
  have hDDi : psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) *
      psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
    (psuC2dD_dagUnit h (Ψ g)).val_inv
  have hDiD : psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) = 1 :=
    (psuC2dD_dagUnit h (Ψ g)).inv_val
  have hNinvN : (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (Ψ g : Matrix (Fin n) (Fin
      n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hpsix : psuDag h ((psuC2dD_xHom h Ψ hcomm g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * psuDag h (Ψ g : Matrix (Fin n) (Fin
      n) K) := by
    rw [psuC2dD_xHom_coe, psuDag_mul, psuDag_dag]
  have hxx : psuDag h ((psuC2dD_xHom h Ψ hcomm g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((psuC2dD_xHom h Ψ hcomm g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [hpsix, psuC2dD_xHom_coe]
    calc (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * psuDag h (Ψ g : Matrix (Fin n)
      (Fin n) K) *
          ((Ψ g : Matrix (Fin n) (Fin n) K) *
            psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        = (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) * (Ψ g : Matrix (Fin n) (Fin n) K)) *
            psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by noncomm_ring
      _ = (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((Ψ g : Matrix (Fin n) (Fin n) K) * psuDag h (Ψ g : Matrix (Fin n) (Fin n) K)) *
            psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [← hDN]
      _ = ((((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (Ψ g : Matrix (Fin n) (Fin n)
      K)) *
            (psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) *
              psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by noncomm_ring
      _ = 1 := by rw [hNinvN, hDDi, Matrix.one_mul]
  rw [mem_primeFormUnitary]
  have hx_dag : (((psuC2dD_xHom h Ψ hcomm g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ
      *
      psuJ n K * ((psuC2dD_xHom h Ψ hcomm g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = psuJ n K
      := by
    have hh : psuJ n K * (((psuJ n K)⁻¹ *
        (((psuC2dD_xHom h Ψ hcomm g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ) *
        psuJ n K * ((psuC2dD_xHom h Ψ hcomm g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = psuJ n
      K := by
      have h0 := congrArg (fun A => psuJ n K * A) hxx
      simpa only [psuDag, formAdj, Matrix.mul_one] using h0
    calc (((psuC2dD_xHom h Ψ hcomm g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
          psuJ n K * ((psuC2dD_xHom h Ψ hcomm g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        = (psuJ n K * (psuJ n K)⁻¹) *
            ((((psuC2dD_xHom h Ψ hcomm g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
              psuJ n K * ((psuC2dD_xHom h Ψ hcomm g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
      by
            rw [hJmul, Matrix.one_mul]
      _ = psuJ n K * (((psuJ n K)⁻¹ *
            (((psuC2dD_xHom h Ψ hcomm g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ) *
            psuJ n K * ((psuC2dD_xHom h Ψ hcomm g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
            noncomm_ring
      _ = psuJ n K := hh
  exact hx_dag

private lemma psuC2dD_xHom_comm_B {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    {G : Type} [Group G] (Ψ : G →* GL (Fin n) K)
    (hΨB : ∀ g, (Ψ g : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * (Ψ g : Matrix (Fin n) (Fin n) K))
    (hcomm : ∀ g h', (Ψ h' : Matrix (Fin n) (Fin n) K) * psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) =
      psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) * (Ψ h' : Matrix (Fin n) (Fin n) K)) :
    ∀ g, ((psuC2dD_xHom h Ψ hcomm g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * B =
      B * ((psuC2dD_xHom h Ψ hcomm g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  intro g
  have hDDi : psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) *
      psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
    (psuC2dD_dagUnit h (Ψ g)).val_inv
  have hDiD : psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) = 1 :=
    (psuC2dD_dagUnit h (Ψ g)).inv_val
  have hDB : psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) :=
    psuC2dD_dag_comm_B S (hΨB g)
  have hDiB : psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n)
      (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n)
      K) := by
    calc psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin
      n) K)
        = psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin
      n) K) * 1 :=
          (Matrix.mul_one _).symm
      _ = psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin
      n) K) *
            (psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) *
              psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by rw [hDDi]
      _ = psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((B : Matrix (Fin n) (Fin n) K) * psuDag h (Ψ g : Matrix (Fin n) (Fin n) K)) *
            psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by noncomm_ring
      _ = psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K)) *
            psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [← hDB]
      _ = (psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            psuDag h (Ψ g : Matrix (Fin n) (Fin n) K)) * (B : Matrix (Fin n) (Fin n) K) *
            psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by noncomm_ring
      _ = (B : Matrix (Fin n) (Fin n) K) *
            psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [hDiD,
      Matrix.one_mul]
  rw [psuC2dD_xHom_coe]
  calc ((Ψ g : Matrix (Fin n) (Fin n) K) *
        psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * (B : Matrix (Fin n) (Fin
      n) K)
      = (Ψ g : Matrix (Fin n) (Fin n) K) *
          (psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n)
      (Fin n) K)) := by
        rw [Matrix.mul_assoc]
    _ = (Ψ g : Matrix (Fin n) (Fin n) K) *
          ((B : Matrix (Fin n) (Fin n) K) * psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n)
      (Fin n) K)) := by
        rw [hDiB]
    _ = ((Ψ g : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K)) *
          psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [Matrix.mul_assoc]
    _ = ((B : Matrix (Fin n) (Fin n) K) * (Ψ g : Matrix (Fin n) (Fin n) K)) *
          psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [hΨB g]
    _ = (B : Matrix (Fin n) (Fin n) K) *
          ((Ψ g : Matrix (Fin n) (Fin n) K) *
            psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by rw
      [Matrix.mul_assoc]

private lemma psuC2dD_xHom_fix {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hde : psuDag h e ≠ e)
    {G : Type} [Group G] (Ψ : G →* GL (Fin n) K)
    (hΨB : ∀ g, (Ψ g : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * (Ψ g : Matrix (Fin n) (Fin n) K))
    (hΨfix : ∀ g, (Ψ g : Matrix (Fin n) (Fin n) K) * (1 - e) = 1 - e)
    (hcomm : ∀ g h', (Ψ h' : Matrix (Fin n) (Fin n) K) * psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) =
      psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) * (Ψ h' : Matrix (Fin n) (Fin n) K)) :
    ∀ g, ((psuC2dD_xHom h Ψ hcomm g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (1 - psuOrbitIdem h e) = 1 - psuOrbitIdem h e := by
  intro g
  obtain ⟨hedP, horth, horth', horb, hεidem⟩ := psuC2dD_dual_facts S P hP e he hde
  have hMr := psuC2dD_M_fix S P hP e he hde Ψ hΨfix g
  have hDr := psuC2dD_Mdag_fix S P hP e he hde Ψ hΨB hΨfix g
  have hDir : psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (1 - e - psuDag h e)
      =
      1 - e - psuDag h e := by
    have hDDi : psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) *
        psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
      (psuC2dD_dagUnit h (Ψ g)).val_inv
    have hDiD : psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) = 1 :=
      (psuC2dD_dagUnit h (Ψ g)).inv_val
    calc psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (1 - e - psuDag h e)
        = psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (psuDag h (Ψ g : Matrix (Fin n) (Fin n) K) * (1 - e - psuDag h e)) := by rw [hDr]
      _ = (psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            psuDag h (Ψ g : Matrix (Fin n) (Fin n) K)) * (1 - e - psuDag h e) := by
          rw [Matrix.mul_assoc]
      _ = 1 - e - psuDag h e := by rw [hDiD, Matrix.one_mul]
  rw [psuC2dD_xHom_coe, horb, show 1 - (e + psuDag h e) = 1 - e - psuDag h e from by abel]
  calc ((Ψ g : Matrix (Fin n) (Fin n) K) *
        psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * (1 - e - psuDag h e)
      = (Ψ g : Matrix (Fin n) (Fin n) K) *
          (psuDag h (((Ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (1 - e - psuDag h e))
      := by
        rw [Matrix.mul_assoc]
    _ = (Ψ g : Matrix (Fin n) (Fin n) K) * (1 - e - psuDag h e) := by rw [hDir]
    _ = 1 - e - psuDag h e := hMr

private lemma psuC2dD_x_exists {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hde : psuDag h e ≠ e)
    (F : Type) [Field F]
    [Module F (LinearMap.range e.mulVecLin)]
    (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K)
    (hψB : ∀ g, (ψ g : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * (ψ g : Matrix (Fin n) (Fin n) K))
    (hψe : ∀ g, e * (ψ g : Matrix (Fin n) (Fin n) K) =
      (ψ g : Matrix (Fin n) (Fin n) K) * e)
    (hψfix : ∀ g, (ψ g : Matrix (Fin n) (Fin n) K) * (1 - e) = 1 - e)
    (hψinj : Function.Injective ψ) :
    ∃ x : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K,
      (∀ g, (x g : Matrix (Fin n) (Fin n) K) =
        (ψ g : Matrix (Fin n) (Fin n) K) *
          psuDag h (((ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ∧
      Function.Injective x ∧
      (∀ g, x g ∈ primeFormUnitary h (psuJ n K)) ∧
      (∀ g, (x g : Matrix (Fin n) (Fin n) K) * B = B * (x g : Matrix (Fin n) (Fin n) K)) ∧
      (∀ g, (x g : Matrix (Fin n) (Fin n) K) * (1 - psuOrbitIdem h e) = 1 - psuOrbitIdem h e) := by
  have hcomm : ∀ g h', (ψ h' : Matrix (Fin n) (Fin n) K) *
      psuDag h (ψ g : Matrix (Fin n) (Fin n) K) =
      psuDag h (ψ g : Matrix (Fin n) (Fin n) K) * (ψ h' : Matrix (Fin n) (Fin n) K) :=
    fun g h' => psuC2dD_M_comm_dag S P hP e he hde ψ hψB hψe hψfix g h'
  refine ⟨psuC2dD_xHom h ψ hcomm, ?_, ?_, ?_, ?_, ?_⟩
  · intro g
    exact psuC2dD_xHom_coe h ψ hcomm g
  · exact psuC2dD_xHom_injective S P hP e he hde ψ hψe hψfix hψinj hcomm
  · exact psuC2dD_xHom_unitary ψ hcomm
  · exact psuC2dD_xHom_comm_B S ψ hψB hcomm
  · exact psuC2dD_xHom_fix S P hP e he hde ψ hψB hψfix hcomm

private lemma psuC2dD_det_one {n k : ℕ} {K F : Type} [Field K] [Field F]
    {G : Type} [Group G] {x : G →* GL (Fin n) K}
    {ι : Matrix.SpecialLinearGroup (Fin k) F →* G}
    [Group.IsPerfect (Matrix.SpecialLinearGroup (Fin k) F)] :
    ∀ s : Matrix.SpecialLinearGroup (Fin k) F,
      ((x (ι s) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
  have htriv : (Matrix.GeneralLinearGroup.det.comp (x.comp ι)) = 1 :=
    MonoidHom.ext (fun s => psuC2dD_hom_trivial_of_perfect
      (Matrix.GeneralLinearGroup.det.comp (x.comp ι)) s)
  intro s
  have h := congrArg (fun g : Matrix.SpecialLinearGroup (Fin k) F →* Kˣ => g s) htriv
  simpa using congrArg Units.val h

private lemma psuC2dD_assemble {f n k : ℕ} {K F : Type} [Field K]
    [Field F] {h : UnitaryFieldData 2 f K} {B : GL (Fin n) K}
    (e : Matrix (Fin n) (Fin n) K) {G : Type} [Group G]
    (x : G →* GL (Fin n) K)
    (hxU : ∀ g, x g ∈ primeFormUnitary h (psuJ n K))
    (hxB : ∀ g, (x g : Matrix (Fin n) (Fin n) K) * B = B * (x g : Matrix (Fin n) (Fin n) K))
    (hxfix : ∀ g, (x g : Matrix (Fin n) (Fin n) K) * (1 - psuOrbitIdem h e) =
      1 - psuOrbitIdem h e)
    (hxinj : Function.Injective x)
    (ι : Matrix.SpecialLinearGroup (Fin k) F →* G)
    (hιinj : Function.Injective ι)
    (hdet : ∀ s, ((x (ι s) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1) :
    ∃ Y : Subgroup ↥(psuBlock h B e),
      Nonempty (↥Y ≃* Matrix.SpecialLinearGroup (Fin k) F) := by
  have hmem : ∀ s, (⟨x (ι s), hxU (ι s), hdet s⟩ : AutPSU.XJ h n) ∈ psuBlock h B e := by
    intro s
    refine Subgroup.mem_comap.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      subst hb
      apply Units.ext
      rw [Units.val_mul, Units.val_mul]
      exact (hxB (ι s)).symm
    · exact hxfix (ι s)
  let Φ : Matrix.SpecialLinearGroup (Fin k) F →* ↥(psuBlock h B e) :=
    { toFun := fun s => ⟨⟨x (ι s), hxU (ι s), hdet s⟩, hmem s⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        show x (ι 1) = 1
        rw [map_one ι, map_one x]
      map_mul' := fun s t => by
        apply Subtype.ext
        apply Subtype.ext
        show x (ι (s * t)) = x (ι s) * x (ι t)
        rw [map_mul ι, map_mul x] }
  have hΦinj : Function.Injective Φ := by
    intro s t hst
    have h1 : x (ι s) = x (ι t) :=
      congrArg (fun z : ↥(psuBlock h B e) => ((z : AutPSU.XJ h n) : GL (Fin n) K)) hst
    exact hιinj (hxinj h1)
  refine ⟨Φ.range, ?_⟩
  have hbij : Function.Bijective Φ.rangeRestrict :=
    ⟨fun s t hst => hΦinj (by simpa using congrArg Subtype.val hst),
      Φ.rangeRestrict_surjective⟩
  exact ⟨(MulEquiv.ofBijective Φ.rangeRestrict hbij).symm⟩

private theorem psuC2d_dualPair_embed {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hde : psuDag h e ≠ e)
    (hr : Matrix.rank e ≠ blockDegree (psuAlg B) e) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (k : ℕ),
      Nat.card E = (2 ^ f) ^ (2 * blockDegree (psuAlg B) e) ∧ 2 ≤ k ∧
      ∃ Y : Subgroup ↥(psuBlock h B e),
        Nonempty (↥Y ≃* Matrix.SpecialLinearGroup (Fin k) E) := by
  classical
  obtain ⟨F, hFld, hAlg, hFin, hChar, π, hM, hT, ψ, hπ, hker, hdim, hcard, hact, hrank, hpos,
    hψinj, hψw, hψfix, hψe, hψB⟩ :=
    exists_blockEmbed S.odd rfl ((hP.1 e).1 he)
  letI : Field F := hFld
  letI : Algebra K F := hAlg
  letI : Module F (LinearMap.range e.mulVecLin) := hM
  letI : IsScalarTower K F (LinearMap.range e.mulVecLin) := hT
  have hcardF : Nat.card F = (2 ^ f) ^ (2 * blockDegree (psuAlg B) e) :=
    psuC2dD_card (d := blockDegree (psuAlg B) e) h hcard
  have hk : 2 ≤ Module.finrank F (LinearMap.range e.mulVecLin) := by
    refine psuC2dD_k_ge_two (d := blockDegree (psuAlg B) e) ?_ hr hpos
    rw [hrank, hdim]
  have hbig : 4 ≤ Nat.card F := psuC2dD_card_ge_four hcardF
  obtain ⟨x, hx, hxinj, hxU, hxB, hxfix⟩ :=
    psuC2dD_x_exists S P hP e he hde F ψ hψB hψe hψfix hψinj
  obtain ⟨ι, hιinj⟩ :=
    psuC2dD_SL_to_lin (k := Module.finrank F (LinearMap.range e.mulVecLin))
      (Module.finBasis F (LinearMap.range e.mulVecLin))
  haveI : Group.IsPerfect
      (Matrix.SpecialLinearGroup (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F) :=
    psuC2dD_SL_isPerfect hk hbig
  have hdet : ∀ s, ((x (ι s) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 :=
    psuC2dD_det_one (x := x) (ι := ι)
  refine ⟨F, hFld, hFin, Module.finrank F (LinearMap.range e.mulVecLin), hcardF, hk, ?_⟩
  exact psuC2dD_assemble e x hxU hxB hxfix hxinj ι hιinj hdet

private theorem psuC2d_selfDual_embed {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hde : psuDag h e = e)
    (hr : Matrix.rank e ≠ blockDegree (psuAlg B) e)
    (hcon : ¬ ((2 ^ f) ^ blockDegree (psuAlg B) e = 2 ∧
      (Matrix.rank e = 2 * blockDegree (psuAlg B) e ∨
        Matrix.rank e = 3 * blockDegree (psuAlg B) e))) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2) (σ : E ≃+* E) (Q k : ℕ),
      CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ ∧ Nat.card E = Q ^ 2 ∧
      Q = (2 ^ f) ^ blockDegree (psuAlg B) e ∧
      2 ≤ k ∧ ¬ (Q = 2 ∧ (k = 2 ∨ k = 3)) ∧
      ∃ Y : Subgroup ↥(psuBlock h B e),
        Nonempty (↥Y ≃* ↥(SU σ k)) := by
  classical
  obtain ⟨F, hFld, hAlg, hFin, hChar, π, hM, hT, ψ, hπ, hker, hdim, hcard, hact, hrank, hpos,
    hψinj, hψw, hψfix, -, hψB⟩ := exists_blockEmbed S.odd rfl ((hP.1 e).1 he)
  letI : Field F := hFld
  letI : Algebra K F := hAlg
  letI : Module F (psuC2dS_V e) := hM
  letI : IsScalarTower K F (psuC2dS_V e) := hT
  have heA : e ∈ psuAlg B := ((hP.1 e).1 he).1
  have hee : e * e = e := ((hP.1 e).1 he).2.1.eq
  obtain ⟨τ, hττ, hτσ, hτπ⟩ := psuC2dS_tau S heA hde π hπ hker
  obtain ⟨hKF, hKnd⟩ := psuC2dS_compat S hee hde π hπ hact τ hτπ
  obtain ⟨hKaddL, hKaddR, hKsmulL, hKsmulR, hKherm⟩ := psuC2dS_hf_props (n := n) h
  have hne : ∃ x, τ x ≠ x := by
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    refine ⟨algebraMap K F c, ?_⟩
    rw [hτσ c]
    exact fun hh => hc ((algebraMap K F).injective hh)
  have hτU := psuC2dS_isUnitaryInvolution τ hττ hne
  obtain ⟨H, hHaddL, hHaddR, hHsmulL, hHsmulR, hHherm, hHnd, htr⟩ :=
    exists_hermTransfer (K := K) (F := F) (V := psuC2dS_V e) h.bar τ h.bar_bar hττ hτσ
      (fun x y => psuC2dS_hf h (x : Fin n → K) (y : Fin n → K))
      (fun x y z => hKaddL x y z) (fun x y z => hKaddR x y z)
      (fun c x y => hKsmulR c x y)
      (fun x y => hKherm x y) hKnd hKF
  haveI : Module.Finite K (psuC2dS_V e) := Module.Finite.of_finite
  haveI : Module.Finite F (psuC2dS_V e) :=
    Module.Finite.of_restrictScalars_finite K F (psuC2dS_V e)
  obtain ⟨k, hk⟩ : ∃ k, Module.finrank F (psuC2dS_V e) = k := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ := exists_hermOrthonormalBasis τ hτU H k hk hHherm hHaddL hHsmulL hHaddR hHsmulR
    hHnd
  obtain ⟨d, hd⟩ : ∃ d, blockDegree (psuAlg B) e = d := ⟨_, rfl⟩
  rw [hd] at hdim hcard hr hcon ⊢
  have hrank' : Matrix.rank e = d * k := by rw [hrank, hdim, hk]
  rw [hk] at hpos
  have hk2 : 2 ≤ k := by
    have hk1 : k ≠ 1 := by
      intro h1
      apply hr
      rw [hrank', h1, Nat.mul_one]
    omega
  have hcardF : Nat.card F = ((2 ^ f) ^ d) ^ 2 := by
    rw [hcard, h.card]
    ring
  have hexcl : ¬ ((2 ^ f) ^ d = 2 ∧ (k = 2 ∨ k = 3)) := by
    rintro ⟨hQ2, hk23⟩
    apply hcon
    refine ⟨hQ2, ?_⟩
    rcases hk23 with h2 | h3
    · left; rw [hrank', h2]; ring
    · right; rw [hrank', h3]; ring
  have hperf := psuC2dS_SUid_perfect τ hτU hcardF hk2 hexcl
  obtain ⟨Y, hY⟩ := psuC2dS_embed hee hde ψ hψinj hψw hψfix hψB τ H hHaddL hHaddR
    hHsmulL hHsmulR htr k b hb hperf
  obtain ⟨eSU⟩ := psuC2d_SU_equiv_SUid τ hτU k
  exact ⟨F, hFld, hFin, hChar, τ, (2 ^ f) ^ d, k, hτU, hcardF, rfl, hk2, hexcl, Y,
    hY.elim fun g => ⟨g.trans eSU.symm⟩⟩

private lemma psuC2d_dualPair_nonsolvable_subgroup {f n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hde : psuDag h e ≠ e)
    (hr : Matrix.rank e ≠ blockDegree (psuAlg B) e) :
    ∃ Y : Subgroup ↥(psuBlock h B e), ¬ Group.IsSolvable ↥Y := by
  classical
  obtain ⟨E, hEfield, hEfin, k, hEcard, hk, Y, ⟨eY⟩⟩ :=
    psuC2d_dualPair_embed S P hP e he hde hr
  letI : Field E := hEfield
  letI : Finite E := hEfin
  refine ⟨Y, ?_⟩
  have hf1 : 1 ≤ f := h.one_le
  have hdpos : 0 < blockDegree (psuAlg B) e := psuC2d_blockDegree_pos S P hP e he
  have hE4 : 4 ≤ Nat.card E := by
    rw [hEcard]
    have hexp : 2 ≤ f * (2 * blockDegree (psuAlg B) e) := by nlinarith
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (f * (2 * blockDegree (psuAlg B) e)) :=
        Nat.pow_le_pow_right (by norm_num) hexp
      _ = (2 ^ f) ^ (2 * blockDegree (psuAlg B) e) := by rw [pow_mul]
  have hns : ¬ Group.IsSolvable (Matrix.SpecialLinearGroup (Fin k) E) :=
    psuC2d_SL_nonsolvable hk hE4
  intro hsolv
  exact hns (solvable_of_solvable_injective (f := eY.symm.toMonoidHom) eY.symm.injective)

private lemma psuC2d_selfDual_nonsolvable_subgroup {f n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hde : psuDag h e = e)
    (hr : Matrix.rank e ≠ blockDegree (psuAlg B) e)
    (hcon : ¬ ((2 ^ f) ^ blockDegree (psuAlg B) e = 2 ∧
      (Matrix.rank e = 2 * blockDegree (psuAlg B) e ∨
        Matrix.rank e = 3 * blockDegree (psuAlg B) e))) :
    ∃ Y : Subgroup ↥(psuBlock h B e), ¬ Group.IsSolvable ↥Y := by
  classical
  obtain ⟨E, hEfield, hEfin, hEchar, σ, Q, k, hσ, hcardE, hQeq, hk, hex, Y, ⟨eY⟩⟩ :=
    psuC2d_selfDual_embed S P hP e he hde hr hcon
  letI : Field E := hEfield
  letI : Finite E := hEfin
  letI : CharP E 2 := hEchar
  refine ⟨Y, ?_⟩
  have hns : ¬ Group.IsSolvable ↥(CFSG.LieType.Universal.Unitary.SU σ k) :=
    psuC2d_SU_nonsolvable σ hσ hcardE hk hex
  intro hsolv
  exact hns (solvable_of_solvable_injective (f := eY.symm.toMonoidHom) eY.symm.injective)

theorem psuGraph_block_solvable_cases {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) :
    Group.IsSolvable ↥(psuBlock h B e) →
      (Matrix.rank e = blockDegree (psuAlg B) e ∨
        (psuDag h e = e ∧ (2 ^ f) ^ blockDegree (psuAlg B) e = 2 ∧
          (Matrix.rank e = 2 * blockDegree (psuAlg B) e ∨
            Matrix.rank e = 3 * blockDegree (psuAlg B) e))) := by
  intro hsolv
  haveI : Group.IsSolvable ↥(psuBlock h B e) := hsolv
  by_cases hde : psuDag h e = e
  · by_cases hr : Matrix.rank e = blockDegree (psuAlg B) e
    · exact Or.inl hr
    · refine Or.inr ⟨hde, ?_⟩
      by_contra hcon
      obtain ⟨Y, hYns⟩ := psuC2d_selfDual_nonsolvable_subgroup S P hP e he hde hr hcon
      exact hYns (solvable_of_solvable_injective (Subgroup.subtype_injective Y))
  · by_cases hr : Matrix.rank e = blockDegree (psuAlg B) e
    · exact Or.inl hr
    · obtain ⟨Y, hYns⟩ := psuC2d_dualPair_nonsolvable_subgroup S P hP e he hde hr
      exact absurd (solvable_of_solvable_injective (Subgroup.subtype_injective Y)) hYns

open scoped commutatorElement

private structure PsuBD {n : ℕ} {K : Type} [Field K] {B : GL (Fin n) K}
    (e : Matrix (Fin n) (Fin n) K) {F : Type} [Field F] [Algebra K F]
    [Module F (LinearMap.range e.mulVecLin)] [IsScalarTower K F (LinearMap.range e.mulVecLin)]
    (π : psuAlg B →ₐ[K] F)
    (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K) :
    Prop where
  hπ : Function.Surjective π
  hker : ∀ a : psuAlg B, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e = 0
  hdim : Module.finrank K F = blockDegree (psuAlg B) e
  hcard : Nat.card F = Nat.card K ^ blockDegree (psuAlg B) e
  hact : ∀ (a : psuAlg B) (w : LinearMap.range e.mulVecLin),
    ((π a • w : LinearMap.range e.mulVecLin) : Fin n → K) =
      (a : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K)
  hrank : Matrix.rank e = Module.finrank K F * Module.finrank F (LinearMap.range e.mulVecLin)
  hpos : 0 < Module.finrank F (LinearMap.range e.mulVecLin)
  hψinj : Function.Injective ψ
  hψw : ∀ (g : LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin)
    (w : LinearMap.range e.mulVecLin),
    (ψ g : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) =
      ((g w : LinearMap.range e.mulVecLin) : Fin n → K)
  hψfix : ∀ g, (ψ g : Matrix (Fin n) (Fin n) K) * (1 - e) = 1 - e
  hψe : ∀ g, e * (ψ g : Matrix (Fin n) (Fin n) K) = (ψ g : Matrix (Fin n) (Fin n) K) * e
  hψB : ∀ g, (ψ g : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
    (B : Matrix (Fin n) (Fin n) K) * (ψ g : Matrix (Fin n) (Fin n) K)

private lemma psuKg1_theta_inv_XJ {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K) (a : AutPSU.XJ h n) :
    psuTheta h X (((a⁻¹ : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (psuTheta h X (((a : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))⁻¹ := by
  have hAA' : (((a : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((((a⁻¹ : AutPSU.XJ h n) : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, Subgroup.coe_inv, mul_inv_cancel, Units.val_one]
  have h1 : psuTheta h X (((a : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      psuTheta h X (((a⁻¹ : AutPSU.XJ h n) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← psuTheta_mul, hAA', psuTheta_one]
  exact (Matrix.inv_eq_right_inv h1).symm

private def psuKg1_thetaFixed {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K) : Subgroup (AutPSU.XJ h n) where
  carrier := {x | psuTheta h X ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
    ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)}
  one_mem' := by
    simp [psuTheta_one]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [Subgroup.coe_mul, Units.val_mul, psuTheta_mul, ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [psuKg1_theta_inv_XJ, ha, Subgroup.coe_inv, Matrix.coe_units_inv]

private lemma psuKg1_smul_inv_unit {n : ℕ} {K : Type} [Field K] (d : K) (hd : d ≠ 0)
    (A A' : Matrix (Fin n) (Fin n) K) (hA : A * A' = 1) :
    (d • A)⁻¹ = d⁻¹ • A' := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hd, one_smul, hA]

private lemma psuKg1_smul_four {n : ℕ} {K : Type} [Field K] (d d' : K)
    (hd : d ≠ 0) (hd' : d' ≠ 0)
    (A B A' B' : Matrix (Fin n) (Fin n) K) :
    (d • A) * (d' • B) * (d⁻¹ • A') * (d'⁻¹ • B') = A * B * A' * B' := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_assoc]
  have hs : d'⁻¹ * (d⁻¹ * (d' * d)) = 1 := by
    field_simp
  rw [hs, one_smul]

private lemma psuKg1_commutator_mem_thetaFixed {f n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (S : PSUGraphSetting h n X B) (a b : AutPSU.XJ h n) (ha : a ∈ psuChat h B)
    (hb : b ∈ psuChat h B) : ⁅a, b⁆ ∈ psuKg1_thetaFixed h X := by
  obtain ⟨d, hd⟩ := S.fix a ha
  obtain ⟨d', hd'⟩ := S.fix b hb
  have hA' : (((a : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((((a⁻¹ : AutPSU.XJ h n) : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, Subgroup.coe_inv, mul_inv_cancel, Units.val_one]
  have hB' : (((b : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((((b⁻¹ : AutPSU.XJ h n) : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, Subgroup.coe_inv, mul_inv_cancel, Units.val_one]
  have hda : psuTheta h X ((((a⁻¹ : AutPSU.XJ h n) : GL (Fin n) K)) :
      Matrix (Fin n) (Fin n) K) =
      (d : K)⁻¹ • ((((a⁻¹ : AutPSU.XJ h n) : GL (Fin n) K)) :
      Matrix (Fin n) (Fin n) K) := by
    rw [psuKg1_theta_inv_XJ, hd, psuKg1_smul_inv_unit (d : K) (Units.ne_zero d) _ _ hA']
  have hdb : psuTheta h X ((((b⁻¹ : AutPSU.XJ h n) : GL (Fin n) K)) :
      Matrix (Fin n) (Fin n) K) =
      (d' : K)⁻¹ • ((((b⁻¹ : AutPSU.XJ h n) : GL (Fin n) K)) :
      Matrix (Fin n) (Fin n) K) := by
    rw [psuKg1_theta_inv_XJ, hd', psuKg1_smul_inv_unit (d' : K) (Units.ne_zero d') _ _ hB']
  have hcommmat : (((⁅a, b⁆ : AutPSU.XJ h n) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) =
      (((a : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (((b : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((((a⁻¹ : AutPSU.XJ h n) : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *
        ((((b⁻¹ : AutPSU.XJ h n) : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) := by
    rw [commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
  change psuTheta h X (((⁅a, b⁆ : AutPSU.XJ h n) : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K) = (((⁅a, b⁆ : AutPSU.XJ h n) : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K)
  rw [hcommmat]
  simp only [psuTheta_mul]
  rw [hd, hd', hda, hdb]
  exact psuKg1_smul_four (d : K) (d' : K) (Units.ne_zero d) (Units.ne_zero d') _ _ _ _

private lemma psuKg1_dag_mul_self {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (y : AutPSU.XJ h n) :
    psuDag h (((y : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (((y : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
  have hyU : ((((y : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
      psuJ n K * (((y : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      psuJ n K := y.2.1
  have hJ : psuJ n K * psuJ n K = 1 := by
    rw [psuJ, AutPSU.coe_gramJ]
    exact CFSG.LieType.Universal.Unitary.antidiag_mul_self n
  have hJinv : (psuJ n K)⁻¹ = psuJ n K := Matrix.inv_eq_right_inv hJ
  rw [psuDag, formAdj, hJinv]
  calc psuJ n K * ((((y : AutPSU.XJ h n) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * psuJ n K *
        (((y : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      = psuJ n K * (((((y : AutPSU.XJ h n) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * psuJ n K *
          (((y : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
        noncomm_ring
    _ = psuJ n K * psuJ n K := by rw [hyU]
    _ = 1 := hJ

private lemma psuK_block_le_chat {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (B : GL (Fin n) K) (e : Matrix (Fin n) (Fin n) K) :
    psuBlock h B e ≤ psuChat h B := by
  intro x hx
  rw [psuBlock, glBlockCentralizer] at hx
  rw [Subgroup.mem_comap, Subgroup.mem_inf] at hx
  obtain ⟨hc, _⟩ := hx
  have hc' : (x : GL (Fin n) K) ∈ Subgroup.centralizer ({B} : Set (GL (Fin n) K)) := hc
  have hcomm := (Subgroup.mem_centralizer_iff.mp hc') B (Set.mem_singleton B)
  have hmat : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have h := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hcomm
    simpa only [Units.val_mul] using h.symm
  change ∃ c : Kˣ, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (B : Matrix (Fin n) (Fin n) K) = (c : K) • ((B : Matrix (Fin n) (Fin n) K) *
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
  exact ⟨1, by simpa using hmat⟩

private lemma psuK_theta_fixed_of_commutator {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (e : Matrix (Fin n) (Fin n) K) (y : AutPSU.XJ h n)
    (hy : y ∈ ⁅psuBlock h B e, psuBlock h B e⁆) :
    psuTheta h X (((y : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (((y : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have hle : ⁅psuBlock h B e, psuBlock h B e⁆ ≤ psuKg1_thetaFixed h X := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact psuKg1_commutator_mem_thetaFixed S a b (psuK_block_le_chat h B e ha)
      (psuK_block_le_chat h B e hb)
  exact hle hy

private lemma psuK_psi_mul_eq_one_of_theta_fixed {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {X : GL (Fin n) K}
    (y : AutPSU.XJ h n)
    (hθ : psuTheta h X (((y : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (((y : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    psuPsi h X (((y : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (((y : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
  have hdag := psuKg1_dag_mul_self h y
  rw [psuPsi]
  have h1 : psuTheta h X (psuDag h (((y : AutPSU.XJ h n) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) * (((y : AutPSU.XJ h n) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) = psuTheta h X (1 : Matrix (Fin n) (Fin n) K) := by
    rw [hdag]
  rw [psuTheta_mul, psuTheta_one, hθ] at h1
  exact h1

private lemma psuKg2_perfect_le_commutator {G : Type} [Group G] (H : Subgroup G)
    [Group.IsPerfect ↥H] : H ≤ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ := by
  have htop : (commutator ↥H) = ⊤ := Group.IsPerfect.commutator_eq_top
  have hmap : Subgroup.map H.subtype (⊤ : Subgroup ↥H) = H := by
    ext x
    simp [Subgroup.mem_map]
  calc H = Subgroup.map H.subtype (⊤ : Subgroup ↥H) := hmap.symm
    _ = Subgroup.map H.subtype (commutator ↥H) := by rw [htop]
    _ = ⁅H, H⁆ := Subgroup.map_subtype_commutator H
    _ ≤ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ := Subgroup.commutator_mono le_top le_top

private noncomputable def psuKg2_slEquiv {k : ℕ} {F : Type} [Field F] {V : Type}
    [AddCommGroup V] [Module F V] (b : Module.Basis (Fin k) F V) :
    Matrix.SpecialLinearGroup (Fin k) F →* (V ≃ₗ[F] V) :=
  (psuC2dE_conjEquiv b).toMonoidHom.comp
    (((LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin k → F)).toMonoidHom).comp
      ((Matrix.GeneralLinearGroup.toLin (n := Fin k) (R := F)).toMonoidHom.comp
        (Matrix.SpecialLinearGroup.toGL (n := Fin k) (R := F))))

private lemma psuKg2_slEquiv_equivFun {k : ℕ} {F : Type} [Field F] {V : Type}
    [AddCommGroup V] [Module F V] (b : Module.Basis (Fin k) F V)
    (s : Matrix.SpecialLinearGroup (Fin k) F) (x : V) :
    b.equivFun (psuKg2_slEquiv b s x) = (s : Matrix (Fin k) (Fin k) F) *ᵥ b.equivFun x := by
  change b.equivFun (psuC2dE_gA b (Matrix.SpecialLinearGroup.toGL s) x) =
    (s : Matrix (Fin k) (Fin k) F) *ᵥ b.equivFun x
  rw [psuC2dE_gA_equivFun]
  rfl

private lemma psuKg2_slEquiv_surj {k : ℕ} {F : Type} [Field F] {V : Type}
    [AddCommGroup V] [Module F V] (b : Module.Basis (Fin k) F V) (g : V ≃ₗ[F] V)
    (hg : LinearMap.det (g : V →ₗ[F] V) = 1) :
    ∃ s : Matrix.SpecialLinearGroup (Fin k) F, psuKg2_slEquiv b s = g := by
  have hdet : (LinearMap.toMatrix b b (g : V →ₗ[F] V)).det = 1 := by
    rw [LinearMap.det_toMatrix, hg]
  let s : Matrix.SpecialLinearGroup (Fin k) F :=
    ⟨LinearMap.toMatrix b b (g : V →ₗ[F] V), hdet⟩
  refine ⟨s, ?_⟩
  apply LinearEquiv.ext
  intro x
  apply b.equivFun.injective
  rw [psuKg2_slEquiv_equivFun]
  exact LinearMap.toMatrix_mulVec_repr b b (g : V →ₗ[F] V) x

private lemma psuKg2_x_apply {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hde : psuDag h e ≠ e)
    {F : Type} [Field F] [Module F (LinearMap.range e.mulVecLin)]
    (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K)
    (hψe : ∀ g, e * (ψ g : Matrix (Fin n) (Fin n) K) =
      (ψ g : Matrix (Fin n) (Fin n) K) * e)
    (hψfix : ∀ g, (ψ g : Matrix (Fin n) (Fin n) K) * (1 - e) = 1 - e)
    (hψw : ∀ (g : LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin)
      (w : LinearMap.range e.mulVecLin),
      (ψ g : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) =
        ((g w : LinearMap.range e.mulVecLin) : Fin n → K))
    (x : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K)
    (hx : ∀ g, (x g : Matrix (Fin n) (Fin n) K) =
      (ψ g : Matrix (Fin n) (Fin n) K) *
        psuDag h (((ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (g : LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin)
    (w : LinearMap.range e.mulVecLin) :
    (x g : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) =
      ((g w : LinearMap.range e.mulVecLin) : Fin n → K) := by
  rw [hx g, ← Matrix.mulVec_mulVec]
  have h1 : psuDag h (((ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * e = e := by
    rw [← map_inv ψ g]
    exact (psuC2dD_Mdag_e S P hP e he hde ψ hψe hψfix (g⁻¹)).1
  have hD : psuDag h (((ψ g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (w : Fin n → K) = (w : Fin n → K) := by
    obtain ⟨v, hv⟩ := w.2
    have hwv : (w : Fin n → K) = e *ᵥ v := by rw [← hv, Matrix.mulVecLin_apply]
    rw [hwv, Matrix.mulVec_mulVec, h1]
  rw [hD, hψw g w]

private lemma psuK_sl_in_commutator {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hde : psuDag h e ≠ e)
    {F : Type} [Field F] [Algebra K F] [Finite F]
    [Module F (LinearMap.range e.mulVecLin)] [IsScalarTower K F (LinearMap.range e.mulVecLin)]
    (π : psuAlg B →ₐ[K] F)
    (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K)
    (hbd : PsuBD e π ψ) (hk : 2 ≤ Module.finrank F (LinearMap.range e.mulVecLin))
    (g : LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin)
    (hg : LinearMap.det (g : LinearMap.range e.mulVecLin →ₗ[F] LinearMap.range e.mulVecLin) = 1) :
    ∃ y ∈ ⁅psuBlock h B e, psuBlock h B e⁆,
      ∀ w : LinearMap.range e.mulVecLin,
        (((y : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) =
          ((g w : LinearMap.range e.mulVecLin) : Fin n → K) := by
  classical
  haveI : Module.Finite K (LinearMap.range e.mulVecLin) := Module.Finite.of_finite
  haveI : Module.Finite F (LinearMap.range e.mulVecLin) :=
    Module.Finite.of_restrictScalars_finite K F (LinearMap.range e.mulVecLin)
  have hcardF : Nat.card F = (2 ^ f) ^ (2 * blockDegree (psuAlg B) e) :=
    psuC2dD_card (d := blockDegree (psuAlg B) e) h hbd.hcard
  have hbig : 4 ≤ Nat.card F := psuC2dD_card_ge_four hcardF
  haveI : Group.IsPerfect
      (Matrix.SpecialLinearGroup (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F) :=
    psuC2dD_SL_isPerfect hk hbig
  obtain ⟨x, hx, hxinj, hxU, hxB, hxfix⟩ :=
    psuC2dD_x_exists S P hP e he hde F ψ hbd.hψB hbd.hψe hbd.hψfix hbd.hψinj
  let b : Module.Basis (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F
      (LinearMap.range e.mulVecLin) := Module.finBasis F _
  let ι : Matrix.SpecialLinearGroup (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F →*
      (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) := psuKg2_slEquiv b
  obtain ⟨s, hs⟩ := psuKg2_slEquiv_surj b g hg
  have hs' : ι s = g := hs
  have hdet : ∀ t : Matrix.SpecialLinearGroup
      (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F,
      ((x (ι t) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 :=
    psuC2dD_det_one (x := x) (ι := ι)
  have hmem : ∀ t : Matrix.SpecialLinearGroup
      (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F,
      (⟨x (ι t), hxU (ι t), hdet t⟩ : AutPSU.XJ h n) ∈ psuBlock h B e := by
    intro t
    refine Subgroup.mem_comap.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · rw [Subgroup.mem_centralizer_iff]
      intro c hc
      rw [Set.mem_singleton_iff] at hc
      subst hc
      apply Units.ext
      rw [Units.val_mul, Units.val_mul]
      exact (hxB (ι t)).symm
    · exact hxfix (ι t)
  let Φ : Matrix.SpecialLinearGroup (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F →*
      ↥(psuBlock h B e) :=
    { toFun := fun t => ⟨⟨x (ι t), hxU (ι t), hdet t⟩, hmem t⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        show x (ι 1) = 1
        rw [map_one ι, map_one x]
      map_mul' := fun t u => by
        apply Subtype.ext
        apply Subtype.ext
        show x (ι (t * u)) = x (ι t) * x (ι u)
        rw [map_mul ι, map_mul x] }
  haveI : Group.IsPerfect ↥(Φ.range) := Group.IsPerfect.range Φ
  have hle : Φ.range ≤
      ⁅(⊤ : Subgroup ↥(psuBlock h B e)), (⊤ : Subgroup ↥(psuBlock h B e))⁆ :=
    psuKg2_perfect_le_commutator Φ.range
  have hmemCom : Φ s ∈
      ⁅(⊤ : Subgroup ↥(psuBlock h B e)), (⊤ : Subgroup ↥(psuBlock h B e))⁆ :=
    hle ⟨s, rfl⟩
  refine ⟨((Φ s : ↥(psuBlock h B e)) : AutPSU.XJ h n), ?_, ?_⟩
  · have h2 : (psuBlock h B e).subtype (Φ s) ∈
        Subgroup.map (psuBlock h B e).subtype (commutator ↥(psuBlock h B e)) :=
      Subgroup.mem_map.mpr ⟨Φ s, hmemCom, rfl⟩
    rw [Subgroup.map_subtype_commutator (psuBlock h B e)] at h2
    simpa using h2
  · intro w
    change (x (ι s) : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) =
      ((g w : LinearMap.range e.mulVecLin) : Fin n → K)
    rw [psuKg2_x_apply S P hP e he hde ψ hbd.hψe hbd.hψfix hbd.hψw x hx (ι s) w, hs']

private lemma psuKg3_comm_alg {n : ℕ} {K : Type} [Field K] {B : GL (Fin n) K}
    (x : GL (Fin n) K)
    (hxB : (x : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K)) :
    ∀ a ∈ psuAlg B, (x : Matrix (Fin n) (Fin n) K) * a =
      a * (x : Matrix (Fin n) (Fin n) K) := by
  intro a ha
  refine Algebra.adjoin_induction (p := fun a _ =>
    (x : Matrix (Fin n) (Fin n) K) * a = a * (x : Matrix (Fin n) (Fin n) K)) ?_ ?_ ?_ ?_ ha
  · rintro y ⟨u, hu, rfl⟩
    rw [Set.mem_singleton_iff] at hu
    subst hu
    exact hxB
  · intro r
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul]
  · intro a b _ _ ha hb
    rw [mul_add, add_mul, ha, hb]
  · intro a b _ _ ha hb
    calc (x : Matrix (Fin n) (Fin n) K) * (a * b)
        = ((x : Matrix (Fin n) (Fin n) K) * a) * b := by rw [mul_assoc]
      _ = (a * (x : Matrix (Fin n) (Fin n) K)) * b := by rw [ha]
      _ = a * ((x : Matrix (Fin n) (Fin n) K) * b) := by rw [mul_assoc]
      _ = a * (b * (x : Matrix (Fin n) (Fin n) K)) := by rw [hb]
      _ = (a * b) * (x : Matrix (Fin n) (Fin n) K) := by rw [mul_assoc]

private lemma psuKg3_hf_unitary {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} (x : GL (Fin n) K) (hxU : x ∈ AutPSU.XJ h n)
    (u v : Fin n → K) :
    psuC2dS_hf h ((x : Matrix (Fin n) (Fin n) K) *ᵥ u)
      ((x : Matrix (Fin n) (Fin n) K) *ᵥ v) = psuC2dS_hf h u v := by
  have hJ : ((x : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * psuJ n K *
      (x : Matrix (Fin n) (Fin n) K) = psuJ n K := by
    have hmem := hxU
    change x ∈ CFSG.ClassicalGroups.UnitaryFlag.gramSU h (psuJ n K) at hmem
    rw [mem_gramSU_iff_unitary] at hmem
    rw [mem_primeFormUnitary] at hmem
    exact hmem.1
  calc psuC2dS_hf h ((x : Matrix (Fin n) (Fin n) K) *ᵥ u)
        ((x : Matrix (Fin n) (Fin n) K) *ᵥ v)
      = ((x : Matrix (Fin n) (Fin n) K).map h.bar) *ᵥ (fun i => h.bar (u i)) ⬝ᵥ
          (psuJ n K *ᵥ ((x : Matrix (Fin n) (Fin n) K) *ᵥ v)) := by
        simp only [psuC2dS_hf]
        rw [psuC2dS_bar_mulVec]
    _ = (fun i => h.bar (u i)) ⬝ᵥ
          (((x : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *ᵥ
            (psuJ n K *ᵥ ((x : Matrix (Fin n) (Fin n) K) *ᵥ v))) :=
        psuC2dS_mulVec_dot _ _ _
    _ = (fun i => h.bar (u i)) ⬝ᵥ
          ((((x : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * psuJ n K *
            (x : Matrix (Fin n) (Fin n) K)) *ᵥ v) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = (fun i => h.bar (u i)) ⬝ᵥ (psuJ n K *ᵥ v) := by rw [hJ]
    _ = psuC2dS_hf h u v := rfl

private lemma psuKg3_hf_sub_left {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (x y z : Fin n → K) :
    psuC2dS_hf h (x - y) z = psuC2dS_hf h x z - psuC2dS_hf h y z := by
  rw [sub_eq_add_neg, psuC2dS_hf_add_left]
  congr 1
  have : (-y : Fin n → K) = (-1 : K) • y := by
    ext i
    simp
  rw [this, psuC2dS_hf_smul_left, map_neg, map_one, neg_mul, one_mul, sub_eq_add_neg]

private lemma psuKg3_restrict_exists {n : ℕ} {K : Type} [Field K] {B : GL (Fin n) K}
    {e : Matrix (Fin n) (Fin n) K} (heB : e ∈ psuAlg B)
    {F : Type} [Field F] [Algebra K F] (π : psuAlg B →ₐ[K] F) (hπ : Function.Surjective π)
    [Module F (LinearMap.range e.mulVecLin)]
    (hact : ∀ (a : psuAlg B) (w : LinearMap.range e.mulVecLin),
      ((π a • w : LinearMap.range e.mulVecLin) : Fin n → K) =
        (a : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K))
    (x : GL (Fin n) K) (hxB : (x : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K)) :
    ∃ g : LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin,
      ∀ w : LinearMap.range e.mulVecLin,
        (g w : Fin n → K) = (x : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) := by
  have hxcomm := psuKg3_comm_alg x hxB
  have hxe : (x : Matrix (Fin n) (Fin n) K) * e = e * (x : Matrix (Fin n) (Fin n) K) :=
    hxcomm e heB
  have hmem_of : ∀ (y : GL (Fin n) K), (y : Matrix (Fin n) (Fin n) K) * e =
      e * (y : Matrix (Fin n) (Fin n) K) → ∀ w : LinearMap.range e.mulVecLin,
      (y : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) ∈ LinearMap.range e.mulVecLin := by
    intro y hy w
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp w.2
    rw [Matrix.mulVecLin_apply] at hu
    refine ⟨(y : Matrix (Fin n) (Fin n) K) *ᵥ u, ?_⟩
    show e *ᵥ ((y : Matrix (Fin n) (Fin n) K) *ᵥ u) =
      (y : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K)
    rw [← hu, Matrix.mulVec_mulVec, ← hy, Matrix.mulVec_mulVec]
  let gLin : LinearMap.range e.mulVecLin →ₗ[F] LinearMap.range e.mulVecLin :=
    { toFun := fun w => ⟨(x : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K), hmem_of x hxe w⟩
      map_add' := by
        intro w1 w2
        apply Subtype.ext
        show (x : Matrix (Fin n) (Fin n) K) *ᵥ ((w1 : Fin n → K) + (w2 : Fin n → K)) =
          (x : Matrix (Fin n) (Fin n) K) *ᵥ (w1 : Fin n → K) +
            (x : Matrix (Fin n) (Fin n) K) *ᵥ (w2 : Fin n → K)
        rw [Matrix.mulVec_add]
      map_smul' := by
        intro c w
        obtain ⟨a, rfl⟩ := hπ c
        apply Subtype.ext
        show (x : Matrix (Fin n) (Fin n) K) *ᵥ
            (((π a • w : LinearMap.range e.mulVecLin)) : Fin n → K) =
          (((π a • (⟨(x : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K),
            hmem_of x hxe w⟩ : LinearMap.range e.mulVecLin)) : LinearMap.range e.mulVecLin) :
              Fin n → K)
        rw [hact a w, hact a ⟨(x : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K),
          hmem_of x hxe w⟩]
        show (x : Matrix (Fin n) (Fin n) K) *ᵥ ((a : Matrix (Fin n) (Fin n) K) *ᵥ
            (w : Fin n → K)) = (a : Matrix (Fin n) (Fin n) K) *ᵥ
              ((x : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K))
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          hxcomm (a : Matrix (Fin n) (Fin n) K) a.2] }
  have hgLin_inj : Function.Injective gLin := by
    intro w1 w2 h
    apply Subtype.ext
    have h' : (x : Matrix (Fin n) (Fin n) K) *ᵥ (w1 : Fin n → K) =
        (x : Matrix (Fin n) (Fin n) K) *ᵥ (w2 : Fin n → K) :=
      congrArg (fun w : LinearMap.range e.mulVecLin => (w : Fin n → K)) h
    have h2 := congrArg (fun v : Fin n → K =>
      ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) h'
    simpa [Matrix.mulVec_mulVec, ← Units.val_mul, Matrix.one_mulVec] using h2
  have hxe_inv : ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * e =
      e * ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    let a : Matrix (Fin n) (Fin n) K := ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    let b : Matrix (Fin n) (Fin n) K := ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    have hab1 : a * b = 1 := by
      show ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hab2 : b * a = 1 := by
      show ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    change a * e = e * a
    calc a * e
        = (a * e) * 1 := (mul_one _).symm
      _ = (a * e) * (b * a) := by rw [hab2]
      _ = ((a * e) * b) * a := (mul_assoc (a * e) b a).symm
      _ = (a * (e * b)) * a := congrArg (fun z => z * a) (mul_assoc a e b)
      _ = (a * (b * e)) * a := congrArg (fun z => (a * z) * a) hxe.symm
      _ = ((a * b) * e) * a := congrArg (fun z => z * a) (mul_assoc a b e).symm
      _ = e * a := by rw [hab1, one_mul]
  have hgLin_surj : Function.Surjective gLin := by
    intro u
    refine ⟨⟨((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (u : Fin n → K),
      hmem_of x⁻¹ hxe_inv u⟩, ?_⟩
    apply Subtype.ext
    show (x : Matrix (Fin n) (Fin n) K) *ᵥ
        (((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (u : Fin n → K)) =
      (u : Fin n → K)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  refine ⟨LinearEquiv.ofBijective gLin ⟨hgLin_inj, hgLin_surj⟩, fun w => ?_⟩
  rfl

private lemma psuKg3_restrict_block {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {B : GL (Fin n) K}
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P)
    {F : Type} [Field F] [Algebra K F]
    [Module F (LinearMap.range e.mulVecLin)]
    (π : psuAlg B →ₐ[K] F) (hπ : Function.Surjective π)
    (hact : ∀ (a : psuAlg B) (w : LinearMap.range e.mulVecLin),
      ((π a • w : LinearMap.range e.mulVecLin) : Fin n → K) =
        (a : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K))
    (x : ↥(psuBlock h B e)) :
    ∃ g : LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin,
      ∀ w : LinearMap.range e.mulVecLin,
        (g w : Fin n → K) = ((x : AutPSU.XJ h n) : GL (Fin n) K) *ᵥ (w : Fin n → K) := by
  have hxmem : (((x : AutPSU.XJ h n) : GL (Fin n) K)) ∈
      Subgroup.centralizer ({B} : Set (GL (Fin n) K)) ⊓ glFixing (1 - psuOrbitIdem h e) :=
    Subgroup.mem_comap.mp x.2
  obtain ⟨hcent, _⟩ := Subgroup.mem_inf.mp hxmem
  have hxB : (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) *
        (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have h := (Subgroup.mem_centralizer_iff.mp hcent B (Set.mem_singleton B)).symm
    simpa using congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) h
  exact psuKg3_restrict_exists ((hP.1 e).1 he).1
    π hπ hact
    ((x : AutPSU.XJ h n) : GL (Fin n) K) hxB

private lemma psuKg3_eq_one_selfdual {n : ℕ} {K : Type} [Field K]
    {e : Matrix (Fin n) (Fin n) K} (x : GL (Fin n) K)
    (hxfix : (x : Matrix (Fin n) (Fin n) K) * (1 - e) = 1 - e)
    (hxe : ∀ w : LinearMap.range e.mulVecLin,
      (x : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) = (w : Fin n → K)) :
    (x : Matrix (Fin n) (Fin n) K) = 1 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  have h1 : (x : Matrix (Fin n) (Fin n) K) *ᵥ (e *ᵥ v) = e *ᵥ v :=
    hxe ⟨e *ᵥ v, LinearMap.mem_range.mpr ⟨v, rfl⟩⟩
  have h2 : (x : Matrix (Fin n) (Fin n) K) *ᵥ ((1 - e) *ᵥ v) = (1 - e) *ᵥ v := by
    rw [Matrix.mulVec_mulVec, hxfix]
  calc (x : Matrix (Fin n) (Fin n) K) *ᵥ v
      = (x : Matrix (Fin n) (Fin n) K) *ᵥ (e *ᵥ v + (1 - e) *ᵥ v) := by
        rw [psuC2dS_add_one_sub]
    _ = (x : Matrix (Fin n) (Fin n) K) *ᵥ (e *ᵥ v) +
        (x : Matrix (Fin n) (Fin n) K) *ᵥ ((1 - e) *ᵥ v) := by rw [Matrix.mulVec_add]
    _ = e *ᵥ v + (1 - e) *ᵥ v := by rw [h1, h2]
    _ = v := psuC2dS_add_one_sub e v
    _ = (1 : Matrix (Fin n) (Fin n) K) *ᵥ v := by rw [Matrix.one_mulVec]

private lemma psuKg3_eq_one_dual {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    {e : Matrix (Fin n) (Fin n) K} (he : e ∈ P) (x : GL (Fin n) K)
    (hxU : x ∈ AutPSU.XJ h n) (hxde : psuDag h e ≠ e)
    (hxcde : (x : Matrix (Fin n) (Fin n) K) * psuDag h e =
      psuDag h e * (x : Matrix (Fin n) (Fin n) K))
    (hxfix : (x : Matrix (Fin n) (Fin n) K) * (1 - (e + psuDag h e)) =
      1 - (e + psuDag h e))
    (hxe : ∀ w : LinearMap.range e.mulVecLin,
      (x : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) = (w : Fin n → K)) :
    (x : Matrix (Fin n) (Fin n) K) = 1 := by
  obtain ⟨hedP, horth, -, -, -⟩ := psuC2dD_dual_facts S P hP e he hxde
  set d : Matrix (Fin n) (Fin n) K := psuDag h e with hd
  have hee : e * e = e := IsIdempotentElem.eq ((hP.1 e).1 he).2.1
  have hdd : d * d = d := IsIdempotentElem.eq ((hP.1 d).mp hedP).2.1
  have hdag : psuDag h d = e := by rw [hd, psuDag_dag]
  have hsum : (e + d) + (1 - (e + d)) = 1 := by
    rw [sub_eq_add_neg, ← add_assoc, add_comm (e + d) 1, add_assoc,
      add_neg_cancel, add_zero]
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  have hdu : d *ᵥ (d *ᵥ v) = d *ᵥ v := by
    rw [Matrix.mulVec_mulVec, hdd]
  have hMul_mem : d *ᵥ (x *ᵥ (d *ᵥ v)) = x *ᵥ (d *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, ← hxcde, ← Matrix.mulVec_mulVec, hdu]
  set δ : Fin n → K := x *ᵥ (d *ᵥ v) - d *ᵥ v with hδdef
  have hδdag : d *ᵥ δ = δ := by
    rw [hδdef, Matrix.mulVec_sub, hMul_mem, hdu]
  have hzero : ∀ w : Fin n → K, psuC2dS_hf h δ w = 0 := by
    intro w
    have hdec : (e + d) *ᵥ w + (1 - (e + d)) *ᵥ w = w := by
      rw [← Matrix.add_mulVec, hsum, Matrix.one_mulVec]
    rw [← hdec, Matrix.add_mulVec, psuC2dS_hf_add_right, psuC2dS_hf_add_right]
    have e1 : psuC2dS_hf h δ (e *ᵥ w) = 0 := by
      rw [hδdef, psuKg3_hf_sub_left]
      have hpres := psuKg3_hf_unitary (f := f) (K := K) (h := h) x hxU
        (d *ᵥ v) (e *ᵥ w)
      have hew : x *ᵥ (e *ᵥ w) = e *ᵥ w :=
        hxe ⟨e *ᵥ w, LinearMap.mem_range.mpr ⟨w, rfl⟩⟩
      rw [hew] at hpres
      rw [hpres, sub_self]
    have e2 : psuC2dS_hf h δ (d *ᵥ w) = 0 := by
      rw [← hδdag, psuC2dS_hf_dag]
      rw [hdag, Matrix.mulVec_mulVec, horth, Matrix.zero_mulVec, psuC2dS_hf_zero_right]
    have e3 : psuC2dS_hf h δ ((1 - (e + d)) *ᵥ w) = 0 := by
      rw [← hδdag, psuC2dS_hf_dag]
      rw [hdag, Matrix.mulVec_mulVec]
      have hz : e * (1 - (e + d)) = 0 := by
        rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_add, hee, horth, add_zero, sub_self]
      rw [hz, Matrix.zero_mulVec, psuC2dS_hf_zero_right]
    rw [e1, e2, e3]
    ring
  have hδ : x *ᵥ (d *ᵥ v) = d *ᵥ v := by
    have hz := psuC2dS_eq_zero_of_forall_hf h δ hzero
    rw [hδdef] at hz
    exact sub_eq_zero.mp hz
  have hdec : e *ᵥ v + d *ᵥ v + (1 - (e + d)) *ᵥ v = v := by
    rw [← Matrix.add_mulVec, ← Matrix.add_mulVec, hsum, Matrix.one_mulVec]
  have h1 : x *ᵥ (e *ᵥ v) = e *ᵥ v := hxe ⟨e *ᵥ v, LinearMap.mem_range.mpr ⟨v, rfl⟩⟩
  have h2 : x *ᵥ ((1 - (e + d)) *ᵥ v) = (1 - (e + d)) *ᵥ v := by
    rw [Matrix.mulVec_mulVec, hxfix]
  calc x *ᵥ v
      = x *ᵥ (e *ᵥ v + d *ᵥ v + (1 - (e + d)) *ᵥ v) := by rw [hdec]
    _ = x *ᵥ (e *ᵥ v) + x *ᵥ (d *ᵥ v) + x *ᵥ ((1 - (e + d)) *ᵥ v) := by
        rw [Matrix.mulVec_add, Matrix.mulVec_add]
    _ = e *ᵥ v + d *ᵥ v + (1 - (e + d)) *ᵥ v := by rw [h1, hδ, h2]
    _ = v := hdec
    _ = (1 : Matrix (Fin n) (Fin n) K) *ᵥ v := by rw [Matrix.one_mulVec]

private lemma psuKg3_eq_one_of_restrict_trivial {f n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (S : PSUGraphSetting h n X B) (P : Finset (Matrix (Fin n) (Fin n) K))
    (hP : PrimFamily (psuAlg B) P) (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P)
    (x : ↥(psuBlock h B e))
    (hxe : ∀ w : LinearMap.range e.mulVecLin,
      ((x : AutPSU.XJ h n) : GL (Fin n) K) *ᵥ (w : Fin n → K) = (w : Fin n → K)) :
    ((x : AutPSU.XJ h n) : GL (Fin n) K) = 1 := by
  have hxmem : (((x : AutPSU.XJ h n) : GL (Fin n) K)) ∈
      Subgroup.centralizer ({B} : Set (GL (Fin n) K)) ⊓ glFixing (1 - psuOrbitIdem h e) :=
    Subgroup.mem_comap.mp x.2
  obtain ⟨hcent, hfix⟩ := Subgroup.mem_inf.mp hxmem
  have hxB : (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) *
        (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have h := (Subgroup.mem_centralizer_iff.mp hcent B (Set.mem_singleton B)).symm
    simpa using congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) h
  have hxcomm := psuKg3_comm_alg ((x : AutPSU.XJ h n) : GL (Fin n) K) hxB
  have heB : e ∈ psuAlg B := ((hP.1 e).1 he).1
  have hxcde : (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      psuDag h e = psuDag h e *
        (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    hxcomm (psuDag h e) (psuGraph_star_mem S e heB).1
  by_cases hde : psuDag h e = e
  · have hfix' : (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (1 - e) = 1 - e := by
      have hh := hfix
      rw [show psuOrbitIdem h e = e from by rw [psuOrbitIdem, if_pos hde]] at hh
      exact hh
    exact Units.ext (psuKg3_eq_one_selfdual ((x : AutPSU.XJ h n) : GL (Fin n) K) hfix' hxe)
  · have hfix' : (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (1 - (e + psuDag h e)) = 1 - (e + psuDag h e) := by
      have hh := hfix
      rw [show psuOrbitIdem h e = e + psuDag h e from by
        rw [psuOrbitIdem, if_neg hde]] at hh
      exact hh
    exact Units.ext (psuKg3_eq_one_dual S P hP he ((x : AutPSU.XJ h n) : GL (Fin n) K)
      (x : AutPSU.XJ h n).2 hde hxcde hfix' hxe)

private lemma psuKg3_gl_solvable_one {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (h : Module.finrank F V = 1) :
    Group.IsSolvable (V ≃ₗ[F] V) := by
  apply Group.isSolvable_of_comm
  intro f g
  apply LinearEquiv.ext
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · have hspan : Submodule.span F {x} = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [finrank_span_singleton hx, h]
    have hgx : g x ∈ Submodule.span F {x} := by rw [hspan]; trivial
    have hfx : f x ∈ Submodule.span F {x} := by rw [hspan]; trivial
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hgx
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hfx
    have hc' : g x = c • x := hc.symm
    have hd' : f x = d • x := hd.symm
    show f (g x) = g (f x)
    calc f (g x) = f (c • x) := by rw [hc']
      _ = c • f x := by rw [map_smul]
      _ = c • (d • x) := by rw [hd']
      _ = (c * d) • x := by rw [smul_smul]
      _ = (d * c) • x := by rw [mul_comm]
      _ = d • (c • x) := by rw [smul_smul]
      _ = d • g x := by rw [hc']
      _ = g (d • x) := by rw [map_smul]
      _ = g (f x) := by rw [hd']

private lemma psuK_solvable_of_finrank_one {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P)
    {F : Type} [Field F] [Algebra K F]
    [Module F (LinearMap.range e.mulVecLin)] [IsScalarTower K F (LinearMap.range e.mulVecLin)]
    (π : psuAlg B →ₐ[K] F)
    (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K)
    (hbd : PsuBD e π ψ) (hk : Module.finrank F (LinearMap.range e.mulVecLin) = 1) :
    Group.IsSolvable ↥(psuBlock h B e) := by
  classical
  have hφ : ∀ x : ↥(psuBlock h B e),
      ∃ g : LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin,
        ∀ w : LinearMap.range e.mulVecLin,
          (g w : Fin n → K) = ((x : AutPSU.XJ h n) : GL (Fin n) K) *ᵥ (w : Fin n → K) :=
    fun x => psuKg3_restrict_block P hP e he π hbd.hπ hbd.hact x
  let ρ : ↥(psuBlock h B e) →*
      (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) :=
    { toFun := fun x => Classical.choose (hφ x)
      map_one' := by
        apply LinearEquiv.ext
        intro w
        apply Subtype.ext
        rw [Classical.choose_spec (hφ 1) w]
        simp
      map_mul' := by
        intro x y
        apply LinearEquiv.ext
        intro w
        apply Subtype.ext
        rw [Classical.choose_spec (hφ (x * y)) w, LinearEquiv.mul_apply,
          Classical.choose_spec (hφ x) (Classical.choose (hφ y) w),
          Classical.choose_spec (hφ y) w, Matrix.mulVec_mulVec]
        rfl }
  have hρinj : Function.Injective ρ := by
    intro x y hxy
    have hz : ρ (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have hzw : ∀ w : LinearMap.range e.mulVecLin,
        (((x * y⁻¹ : ↥(psuBlock h B e)) : AutPSU.XJ h n) : GL (Fin n) K) *ᵥ
          (w : Fin n → K) = (w : Fin n → K) := by
      intro w
      have h := congrArg (fun g : LinearMap.range e.mulVecLin ≃ₗ[F]
        LinearMap.range e.mulVecLin => (g w : Fin n → K)) hz
      change (Classical.choose (hφ (x * y⁻¹)) w : Fin n → K) = (w : Fin n → K) at h
      rw [Classical.choose_spec (hφ (x * y⁻¹)) w] at h
      simpa using h
    have h1 : (((x * y⁻¹ : ↥(psuBlock h B e)) : AutPSU.XJ h n) : GL (Fin n) K) = 1 :=
      psuKg3_eq_one_of_restrict_trivial S P hP e he (x * y⁻¹) hzw
    have h2 : x * y⁻¹ = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact h1
    calc x = x * y⁻¹ * y := by group
      _ = 1 * y := by rw [h2]
      _ = y := by rw [one_mul]
  haveI : Group.IsSolvable
      (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) :=
    psuKg3_gl_solvable_one hk
  exact solvable_of_solvable_injective hρinj

private lemma psuCKU_alg_comm {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K) :
    ∀ a ∈ psuAlg B, ∀ b ∈ psuAlg B, a * b = b * a := by
  intro a ha b hb
  have hcommP : (Units.val '' ({B} : Set (GL (Fin n) K)) :
      Set (Matrix (Fin n) (Fin n) K)).Pairwise Commute := by
    rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩ _
    rw [Set.mem_singleton_iff] at hs ht
    subst hs
    subst ht
    exact Commute.refl _
  letI : CommRing (psuAlg B) := Algebra.adjoinCommRingOfComm K hcommP
  exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : psuAlg B) (⟨b, hb⟩ : psuAlg B))

private lemma psuCKU_comm_of_centralizes {n : ℕ} {K : Type} [Field K] {B : GL (Fin n) K}
    {z : Matrix (Fin n) (Fin n) K}
    (hz : (B : Matrix (Fin n) (Fin n) K) * z = z * (B : Matrix (Fin n) (Fin n) K)) :
    ∀ a ∈ psuAlg B, z * a = a * z := by
  intro a ha
  refine Algebra.adjoin_induction (p := fun x _ => z * x = x * z) ?_ ?_ ?_ ?_ ha
  · rintro x ⟨s, hs, rfl⟩
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact hz.symm
  · intro r
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul]
  · intro x y hx hy hpx hpy
    rw [mul_add, add_mul, hpx, hpy]
  · intro x y hx hy hpx hpy
    rw [← Matrix.mul_assoc z x y, hpx, Matrix.mul_assoc x z y, hpy,
      ← Matrix.mul_assoc x y z]

private lemma psuCKU_star_mem_of_primFamily {f n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (S : PSUGraphSetting h n X B) (P : Finset (Matrix (Fin n) (Fin n) K))
    (hP : PrimFamily (psuAlg B) P) :
    ∀ e ∈ P, psuDag h e ∈ P ∧ psuPsi h X e ∈ P := by
  intro e he
  refine ⟨?_, ?_⟩
  · exact primFamily_map_mem hP (psuDag h) (psuDag_add h) (psuDag_mul h)
      (fun a ha => (psuGraph_star_mem S a ha).1) (fun a _ => psuDag_dag h a)
      (psuCKU_alg_comm B) e he
  · exact primFamily_map_mem hP (psuPsi h X) (psuPsi_add h X) (psuPsi_mul h X)
      (fun a ha => (psuGraph_star_mem S a ha).2)
      (fun a _ => psuPsi_psi h X S.X_mem S.X_sq a) (psuCKU_alg_comm B) e he

private lemma psuCKU_orbitIdem_mem {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) :
    psuOrbitIdem h e ∈ psuAlg B := by
  have heA : e ∈ psuAlg B := ((hP.1 e).mp he).1
  have hed : psuDag h e ∈ psuAlg B := (psuGraph_star_mem S e heA).1
  unfold psuOrbitIdem
  split_ifs
  · exact heA
  · exact Subalgebra.add_mem _ heA hed

private lemma psuCKU_theta_sub {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K) (a b : Matrix (Fin n) (Fin n) K) :
    psuTheta h X (a - b) = psuTheta h X a - psuTheta h X b := by
  unfold psuTheta
  rw [Matrix.map_sub h.bar (fun x y => map_sub h.bar x y), Matrix.mul_sub, Matrix.sub_mul]

private lemma psuCKU_theta_eq_psi_dag {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (X : GL (Fin n) K) (a : Matrix (Fin n) (Fin n) K) :
    psuTheta h X a = psuPsi h X (psuDag h a) := by
  rw [psuPsi, psuDag_dag]

private lemma psuCKU_psi_dag {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}
    {X : GL (Fin n) K} (hX : X ∈ primeFormUnitary h (psuJ n K))
    (hXs : (X : Matrix (Fin n) (Fin n) K) * (X : Matrix (Fin n) (Fin n) K).map h.bar = 1)
    (a : Matrix (Fin n) (Fin n) K) :
    psuPsi h X (psuDag h a) = psuDag h (psuPsi h X a) := by
  rw [psuPsi, psuPsi, psuDag_dag]
  rw [← psuTheta_dag h X hX hXs (psuDag h a), psuDag_dag]

private lemma psuCKU_kind1_facts {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X B : GL (Fin n) K) (e : Matrix (Fin n) (Fin n) K) (hk : psuKind h X B e = 1) :
    psuDag h e = e ∧ psuPsi h X e ≠ e := by
  rw [psuKind] at hk
  by_cases hde : psuDag h e = e
  · rw [if_pos hde] at hk
    by_cases hpsi : psuPsi h X e = e
    · rw [if_pos hpsi] at hk
      omega
    · rw [if_neg hpsi] at hk
      exact ⟨hde, hpsi⟩
  · rw [if_neg hde] at hk
    by_cases hpsi : psuPsi h X e = e
    · rw [if_pos hpsi] at hk
      by_cases htriv : psuPsiTrivial h X B e
      · rw [if_pos htriv] at hk
        omega
      · rw [if_neg htriv] at hk
        omega
    · rw [if_neg hpsi] at hk
      by_cases hdag : psuPsi h X e = psuDag h e
      · rw [if_pos hdag] at hk
        omega
      · rw [if_neg hdag] at hk
        omega

private lemma psuCKU_kind5_facts {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X B : GL (Fin n) K) (e : Matrix (Fin n) (Fin n) K) (hk : psuKind h X B e = 5) :
    psuDag h e ≠ e ∧ psuPsi h X e ≠ e ∧ psuPsi h X e ≠ psuDag h e := by
  rw [psuKind] at hk
  by_cases hde : psuDag h e = e
  · rw [if_pos hde] at hk
    by_cases hpsi : psuPsi h X e = e
    · rw [if_pos hpsi] at hk
      omega
    · rw [if_neg hpsi] at hk
      omega
  · rw [if_neg hde] at hk
    by_cases hpsi : psuPsi h X e = e
    · rw [if_pos hpsi] at hk
      by_cases htriv : psuPsiTrivial h X B e
      · rw [if_pos htriv] at hk
        omega
      · rw [if_neg htriv] at hk
        omega
    · rw [if_neg hpsi] at hk
      by_cases hdag : psuPsi h X e = psuDag h e
      · rw [if_pos hdag] at hk
        omega
      · rw [if_neg hdag] at hk
        exact ⟨hde, hpsi, hdag⟩

private lemma psuCKU_orbitIdem_mul_theta_eq_zero {f n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P)
    (hk : psuKind h X B e = 1 ∨ psuKind h X B e = 5) :
    psuOrbitIdem h e * psuTheta h X (psuOrbitIdem h e) = 0 := by
  rcases hk with hk1 | hk5
  · obtain ⟨hde, hpsi⟩ := psuCKU_kind1_facts h X B e hk1
    have hstar := psuCKU_star_mem_of_primFamily S P hP
    have hpsiP : psuPsi h X e ∈ P := (hstar e he).2
    have hε : psuOrbitIdem h e = e := by
      unfold psuOrbitIdem
      rw [if_pos hde]
    have hθe : psuTheta h X e = psuPsi h X e := by
      rw [psuCKU_theta_eq_psi_dag h X e, hde]
    rw [hε, hθe]
    exact hP.2.1 e he (psuPsi h X e) hpsiP (Ne.symm hpsi)
  · obtain ⟨hde, hpsi, hpsi_dag⟩ := psuCKU_kind5_facts h X B e hk5
    have hstar := psuCKU_star_mem_of_primFamily S P hP
    have hedP : psuDag h e ∈ P := (hstar e he).1
    have hpsiP : psuPsi h X e ∈ P := (hstar e he).2
    have hpsidP : psuDag h (psuPsi h X e) ∈ P := (hstar (psuPsi h X e) hpsiP).1
    have he_ne_psid : e ≠ psuDag h (psuPsi h X e) := by
      intro hx
      exact hpsi_dag (by
        have h' := congrArg (psuDag h) hx
        rw [psuDag_dag] at h'
        exact h'.symm)
    have hed_ne_psid : psuDag h e ≠ psuDag h (psuPsi h X e) := by
      intro hx
      exact hpsi (by
        have h' := congrArg (psuDag h) hx
        rw [psuDag_dag, psuDag_dag] at h'
        exact h'.symm)
    have hε : psuOrbitIdem h e = e + psuDag h e := by
      unfold psuOrbitIdem
      rw [if_neg hde]
    have hθsum : psuTheta h X (e + psuDag h e) =
        psuDag h (psuPsi h X e) + psuPsi h X e := by
      rw [psuTheta_add, psuCKU_theta_eq_psi_dag h X e,
        psuCKU_theta_eq_psi_dag h X (psuDag h e), psuDag_dag,
        psuCKU_psi_dag S.X_mem S.X_sq e]
    rw [hε, hθsum, add_mul, mul_add, mul_add,
      hP.2.1 e he (psuPsi h X e) hpsiP (Ne.symm hpsi),
      hP.2.1 e he (psuDag h (psuPsi h X e)) hpsidP he_ne_psid,
      hP.2.1 (psuDag h e) hedP (psuPsi h X e) hpsiP (Ne.symm hpsi_dag),
      hP.2.1 (psuDag h e) hedP (psuDag h (psuPsi h X e)) hpsidP hed_ne_psid]
    simp

private lemma psuCKU_block_mem {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (B : GL (Fin n) K) (e : Matrix (Fin n) (Fin n) K) (y : AutPSU.XJ h n)
    (hy : y ∈ psuBlock h B e) :
    (B : Matrix (Fin n) (Fin n) K) * ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (B : Matrix (Fin n) (Fin n) K) ∧
      ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (1 - psuOrbitIdem h e) =
        1 - psuOrbitIdem h e := by
  have hmem := hy
  rw [psuBlock, glBlockCentralizer] at hmem
  obtain ⟨hc, hfix⟩ := Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hmem)
  constructor
  · have h := (Subgroup.mem_centralizer_iff.mp hc) (B : GL (Fin n) K) (by simp)
    exact congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) h
  · exact hfix

private lemma psuCKU_eq_one_of {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}
    {X : GL (Fin n) K} {y : AutPSU.XJ h n} {eps : Matrix (Fin n) (Fin n) K}
    (hθ : psuTheta h X ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hfix : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (1 - eps) = 1 - eps)
    (hcomm : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * eps =
      eps * ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hzero : eps * psuTheta h X eps = 0) : y = 1 := by
  set z := ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hzdef
  have hzero' : eps * psuTheta h X eps = 0 := hzero
  have hthe : psuTheta h X (1 - eps) = 1 - psuTheta h X eps := by
    rw [psuCKU_theta_sub, psuTheta_one]
  have hfixθ : z * (1 - psuTheta h X eps) = 1 - psuTheta h X eps := by
    have h := congrArg (psuTheta h X) hfix
    rw [psuTheta_mul, hθ, hthe] at h
    exact h
  have h1 : z * eps = eps * (1 - psuTheta h X eps) := by
    calc z * eps = z * (eps * ((1 - psuTheta h X eps) + psuTheta h X eps)) := by
          rw [sub_add_cancel, mul_one]
      _ = z * (eps * (1 - psuTheta h X eps)) + z * (eps * psuTheta h X eps) := by
          rw [mul_add, mul_add]
      _ = (z * eps) * (1 - psuTheta h X eps) + z * (eps * psuTheta h X eps) := by
          rw [← mul_assoc, ← mul_assoc]
      _ = (z * eps) * (1 - psuTheta h X eps) + z * 0 := by rw [hzero']
      _ = (z * eps) * (1 - psuTheta h X eps) := by rw [mul_zero, add_zero]
      _ = (eps * z) * (1 - psuTheta h X eps) := by rw [hcomm]
      _ = eps * (z * (1 - psuTheta h X eps)) := by rw [mul_assoc]
      _ = eps * (1 - psuTheta h X eps) := by rw [hfixθ]
  have hz1 : z = 1 := by
    calc z = z * 1 := (mul_one z).symm
      _ = z * ((1 - eps) + eps) := by rw [sub_add_cancel]
      _ = z * (1 - eps) + z * eps := by rw [mul_add]
      _ = (1 - eps) + eps * (1 - psuTheta h X eps) := by rw [hfix, h1]
      _ = (1 - eps) + eps - eps * psuTheta h X eps := by
          rw [mul_sub, mul_one, add_sub_assoc]
      _ = 1 - eps * psuTheta h X eps := by rw [sub_add_cancel]
      _ = 1 := by rw [hzero', sub_zero]
  exact Subtype.ext (Units.ext hz1)

private theorem psuCK_kind_unstable_commutator {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P)
    (hk : psuKind h X B e = 1 ∨ psuKind h X B e = 5) :
    ⁅psuBlock h B e, psuBlock h B e⁆ = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  have hyG : y ∈ psuBlock h B e := Subgroup.commutator_le_self (psuBlock h B e) hy
  have hmem := psuCKU_block_mem h B e y hyG
  have hθ := psuK_theta_fixed_of_commutator S e y hy
  have hcomm := psuCKU_comm_of_centralizes hmem.1 (psuOrbitIdem h e)
    (psuCKU_orbitIdem_mem S P hP e he)
  have hzero := psuCKU_orbitIdem_mul_theta_eq_zero S P hP e he hk
  exact psuCKU_eq_one_of hθ hmem.2 hcomm hzero

private theorem psuCK_kind_unstable_core {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P)
    (hk : psuKind h X B e = 1 ∨ psuKind h X B e = 5) :
    Group.IsSolvable ↥(psuBlock h B e) := by
  have hcomm := psuCK_kind_unstable_commutator S P hP e he hk
  have hle : psuBlock h B e ≤ Subgroup.centralizer (psuBlock h B e) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hab : ∀ a b : ↥(psuBlock h B e), a * b = b * a := by
    intro a b
    have h := (Subgroup.mem_centralizer_iff.mp (hle a.2)) (b : AutPSU.XJ h n) b.2
    exact Subtype.ext h.symm
  exact Group.isSolvable_of_comm hab

private lemma psuCDg1_sadd_zero {V : Type} [AddCommGroup V] (s : V → V)
    (hsadd : ∀ x y, s (x + y) = s x + s y) : s 0 = 0 := by
  have h := hsadd 0 0
  rw [zero_add] at h
  exact add_left_cancel (h.symm.trans (add_zero (s 0)).symm)

private lemma psuCDg1_exists_dual_eq_zero_ne {F V : Type} [Field F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {v z : V} (hv : v ≠ 0) (hz : z ∉ Submodule.span F {v}) :
    ∃ φ : Module.Dual F V, φ v = 0 ∧ φ z ≠ 0 := by
  classical
  let b : Module.Basis (Fin (Module.finrank F V)) F V := Module.finBasis F V
  have hav : b.repr v ≠ 0 := by
    intro h
    apply hv
    have h' := congrArg b.repr.symm h
    simpa using h'
  obtain ⟨j, hj⟩ : ∃ j, b.repr v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hav (Finsupp.ext h)
  have hcross : ∃ p, b.repr v j * b.repr z p - b.repr v p * b.repr z j ≠ 0 := by
    by_contra h
    push Not at h
    apply hz
    rw [Submodule.mem_span_singleton]
    refine ⟨b.repr z j / b.repr v j, ?_⟩
    apply b.repr.injective
    ext p
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    have hp : b.repr v j * b.repr z p = b.repr v p * b.repr z j := sub_eq_zero.mp (h p)
    rw [div_mul_eq_mul_div, div_eq_iff hj, mul_comm (b.repr z j) (b.repr v p),
      mul_comm (b.repr z p) (b.repr v j)]
    exact hp.symm
  obtain ⟨p, hp⟩ := hcross
  refine ⟨b.repr v j • b.coord p - b.repr v p • b.coord j, ?_, ?_⟩
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      Module.Basis.coord_apply]
    ring
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      Module.Basis.coord_apply]
    exact hp

private lemma psuCDg1_smul_right_injective {F V : Type} [Field F]
    [AddCommGroup V] [Module F V] {v : V} (hv : v ≠ 0) :
    Function.Injective (fun a : F => a • v) := by
  intro a b hab
  simp only at hab
  have h : (a - b) • v = 0 := by rw [sub_smul, hab, sub_self]
  have h' : a - b = 0 := (smul_eq_zero.mp h).resolve_right hv
  exact sub_eq_zero.mp h'

private lemma psuCDg1_indep {F V : Type} [Field F]
    [AddCommGroup V] [Module F V]
    (s : V → V) (hsadd : ∀ x y, s (x + y) = s x + s y)
    (μ : V → F) (hμ : ∀ v, s v = μ v • v)
    {v w : V} (hv : v ≠ 0) (hw : w ∉ Submodule.span F {v}) :
    μ v = μ w := by
  have hsum : ∀ a b : F, a • v + b • w = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    have hb : b = 0 := by
      by_contra hb
      apply hw
      rw [Submodule.mem_span_singleton]
      refine ⟨b⁻¹ * (-a), ?_⟩
      have hbw : b • w = -(a • v) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]
        exact hab
      apply (smul_right_injective V hb)
      change b • ((b⁻¹ * (-a)) • v) = b • w
      rw [smul_smul]
      have hcoef : b * (b⁻¹ * (-a)) = -a := by
        rw [← mul_assoc, mul_inv_cancel₀ hb, one_mul]
      rw [hcoef, hbw]
      exact neg_smul a v
    have ha : a = 0 := by
      have h0 : a • v = 0 := by rw [← hab, hb, zero_smul, add_zero]
      exact (smul_eq_zero.mp h0).resolve_right hv
    exact ⟨ha, hb⟩
  have hmain : μ (v + w) • v + μ (v + w) • w = μ v • v + μ w • w := by
    rw [← smul_add, ← hμ (v + w), hsadd v w, hμ v, hμ w]
  have hzero : (μ v - μ (v + w)) • v + (μ w - μ (v + w)) • w = 0 := by
    have hEq : (μ v - μ (v + w)) • v + (μ w - μ (v + w)) • w
        = (μ v • v + μ w • w) - (μ (v + w) • v + μ (v + w) • w) := by
      rw [sub_smul, sub_smul]
      abel
    rw [hEq, hmain, sub_self]
  obtain ⟨h1, h2⟩ := hsum _ _ hzero
  rw [sub_eq_zero] at h1 h2
  rw [h1, h2]

private lemma psuCDg1_exists_notMem_span {F V : Type} [Field F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (k : ℕ) (hk : 2 ≤ k) (hfin : Module.finrank F V = k) (v : V) :
    ∃ z : V, z ∉ Submodule.span F {v} := by
  let b : Module.Basis (Fin k) F V := (Module.finBasis F V).reindex (finCongr hfin)
  by_contra h
  have hmem : ∀ z : V, z ∈ Submodule.span F {v} := by
    intro z
    by_contra hz
    exact h ⟨z, hz⟩
  obtain ⟨c0, hc0⟩ := Submodule.mem_span_singleton.mp (hmem (b ⟨0, by omega⟩))
  obtain ⟨c1, hc1⟩ := Submodule.mem_span_singleton.mp (hmem (b ⟨1, by omega⟩))
  have hc0ne : c0 ≠ 0 := by
    intro h0
    have hb0 : b ⟨0, by omega⟩ = 0 := by rw [← hc0, h0, zero_smul]
    exact b.ne_zero ⟨0, by omega⟩ hb0
  have hrel : b ⟨1, by omega⟩ = (c1 / c0) • b ⟨0, by omega⟩ := by
    rw [← hc1, ← hc0, smul_smul, div_mul_cancel₀ c1 hc0ne]
  have hcoord := congrArg (b.coord ⟨1, by omega⟩) hrel
  simp only [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.smul_apply,
    smul_eq_mul, Finsupp.single_eq_same, mul_one] at hcoord
  have hone : (1 : F) = 0 := by
    simpa using hcoord
  exact one_ne_zero hone

private lemma psuCDg1_const_multiplier {F V : Type} [Field F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (k : ℕ) (hk : 2 ≤ k) (hfin : Module.finrank F V = k)
    (s : V → V) (hsadd : ∀ x y, s (x + y) = s x + s y)
    (hsmul : ∀ v : V, ∃ μ : F, s v = μ • v) :
    ∃ lam : F, ∀ v : V, s v = lam • v := by
  classical
  let μ : V → F := fun v => Classical.choose (hsmul v)
  have hμ : ∀ v, s v = μ v • v := fun v => Classical.choose_spec (hsmul v)
  let b : Module.Basis (Fin k) F V := (Module.finBasis F V).reindex (finCongr hfin)
  let v₀ : V := b ⟨0, by omega⟩
  have hv₀ : v₀ ≠ 0 := b.ne_zero ⟨0, by omega⟩
  refine ⟨μ v₀, fun w => ?_⟩
  by_cases hw : w = 0
  · rw [hw, psuCDg1_sadd_zero s hsadd, smul_zero]
  · by_cases hind : w ∈ Submodule.span F {v₀}
    · obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hind
      obtain ⟨z, hz⟩ := psuCDg1_exists_notMem_span k hk hfin v₀
      have hzw : z ∉ Submodule.span F {w} := by
        intro hmem
        apply hz
        have hle : Submodule.span F {w} ≤ Submodule.span F {v₀} := by
          rw [Submodule.span_singleton_le_iff_mem, ← ha]
          exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self v₀)
        exact hle hmem
      have hvz : μ v₀ = μ z := psuCDg1_indep s hsadd μ hμ hv₀ hz
      have hwz : μ w = μ z := psuCDg1_indep s hsadd μ hμ hw hzw
      rw [hμ w, hwz, ← hvz]
    · have hwv : μ v₀ = μ w := psuCDg1_indep s hsadd μ hμ hv₀ hind
      rw [hμ w, ← hwv]

private lemma psuCKD_smul_mem_of_comm {F V : Type} [Field F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (s : V → V) (hsadd : ∀ x y, s (x + y) = s x + s y)
    (hcomm : ∀ g : V ≃ₗ[F] V, LinearMap.det (g : V →ₗ[F] V) = 1 →
      ∀ x, s (g x) = g (s x)) :
    ∀ v : V, ∃ μ : F, s v = μ • v := by
  intro v
  by_cases hv : v = 0
  · refine ⟨0, ?_⟩
    rw [hv, psuCDg1_sadd_zero s hsadd, zero_smul]
  · by_contra hcon
    push Not at hcon
    have hz : s v ∉ Submodule.span F {v} := by
      intro hmem
      obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hmem
      exact hcon μ hμ.symm
    obtain ⟨φ, hφv, hφsv⟩ := psuCDg1_exists_dual_eq_zero_ne hv hz
    let t : V ≃ₗ[F] V := LinearEquiv.ofLinearMap (ClassicalGroups.Linear.transv v φ)
      (ClassicalGroups.Linear.transv v (-φ))
      (LinearMap.ext fun x => ClassicalGroups.Linear.transv_transv_neg_apply hφv x)
      (LinearMap.ext fun x => ClassicalGroups.Linear.transv_neg_transv_apply hφv x)
    have hdet : LinearMap.det (t : V →ₗ[F] V) = 1 :=
      ClassicalGroups.Linear.det_id_add_smulRight (Module.finBasis F V) hφv
    have hcomm' := hcomm t hdet v
    have htv : t v = v := by
      change ClassicalGroups.Linear.transv v φ v = v
      rw [ClassicalGroups.Linear.transv_apply, hφv, zero_smul, add_zero]
    rw [htv] at hcomm'
    have htsv : t (s v) = s v + φ (s v) • v := by
      change ClassicalGroups.Linear.transv v φ (s v) = s v + φ (s v) • v
      rw [ClassicalGroups.Linear.transv_apply]
    rw [htsv] at hcomm'
    have hc : φ (s v) • v = 0 := by
      have h' : s v + 0 = s v + φ (s v) • v := by rw [add_zero]; exact hcomm'
      exact (add_left_cancel h').symm
    exact hφsv ((smul_eq_zero.mp hc).resolve_right hv)

private lemma psuCKD_eq_zero_of_smul_mem {F V : Type} [Field F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (k : ℕ) (hk : 2 ≤ k) (hfin : Module.finrank F V = k)
    (τ : F ≃+* F) (hτ : τ ≠ RingEquiv.refl F)
    (s : V → V) (hsadd : ∀ x y, s (x + y) = s x + s y)
    (hssmul : ∀ (c : F) (x : V), s (c • x) = τ c • s x)
    (hsmul : ∀ v : V, ∃ μ : F, s v = μ • v) :
    ∀ x : V, s x = 0 := by
  classical
  obtain ⟨lam, hlam⟩ := psuCDg1_const_multiplier k hk hfin s hsadd hsmul
  have hs0 : s 0 = 0 := psuCDg1_sadd_zero s hsadd
  have hτne : ∃ c : F, τ c ≠ c := by
    by_contra h
    apply hτ
    ext c
    by_contra hc
    exact h ⟨c, hc⟩
  obtain ⟨c, hc⟩ := hτne
  have hc0 : c ≠ 0 := by
    intro h0
    apply hc
    rw [h0]
    exact map_zero τ
  let b : Module.Basis (Fin k) F V := (Module.finBasis F V).reindex (finCongr hfin)
  let v₀ : V := b ⟨0, by omega⟩
  have hv₀ : v₀ ≠ 0 := b.ne_zero ⟨0, by omega⟩
  have h1 : s (c • v₀) = lam • (c • v₀) := hlam _
  have h2 : s (c • v₀) = τ c • s v₀ := hssmul c v₀
  have h3 : s v₀ = lam • v₀ := hlam v₀
  have heq : lam • (c • v₀) = τ c • (lam • v₀) := by rw [← h1, h2, h3]
  have heq2 : (lam * c) • v₀ = (τ c * lam) • v₀ := by
    simpa only [smul_smul] using heq
  have hcoef : lam * c = τ c * lam := psuCDg1_smul_right_injective hv₀ heq2
  have hkey : lam * (τ c - c) = 0 := by
    have hcomm : lam * c = lam * τ c := by rw [hcoef, mul_comm]
    rw [mul_sub, hcomm, sub_self]
  have hlam0 : lam = 0 := by
    have hne : τ c - c ≠ 0 := sub_ne_zero.mpr hc
    exact (mul_eq_zero.mp hkey).resolve_right hne
  intro x
  by_cases hx : x = 0
  · rw [hx]
    exact hs0
  · rw [hlam x, hlam0, zero_smul]

private lemma psuCDg2_inv_mul_self {n : ℕ} {K : Type} [Field K] (X : GL (Fin n) K) :
    ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (X : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [← Units.val_mul]
  simp

private lemma psuCDg2_theta_mul_X {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (X : GL (Fin n) K) (a : Matrix (Fin n) (Fin n) K) :
    psuTheta h X a * (X : Matrix (Fin n) (Fin n) K) =
      (X : Matrix (Fin n) (Fin n) K) * a.map h.bar := by
  have hXX : ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (X : Matrix (Fin n) (Fin n) K) = 1 := psuCDg2_inv_mul_self X
  calc psuTheta h X a * (X : Matrix (Fin n) (Fin n) K)
      = ((X : Matrix (Fin n) (Fin n) K) * a.map h.bar *
          ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
            (X : Matrix (Fin n) (Fin n) K) := rfl
    _ = (X : Matrix (Fin n) (Fin n) K) * a.map h.bar *
          (((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (X : Matrix (Fin n) (Fin n) K)) := by noncomm_ring
    _ = (X : Matrix (Fin n) (Fin n) K) * a.map h.bar := by rw [hXX, Matrix.mul_one]

private lemma psuCDg2_theta_eq_mul_X {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (X : GL (Fin n) K) (a : Matrix (Fin n) (Fin n) K)
    (ha : psuTheta h X a = a) :
    (X : Matrix (Fin n) (Fin n) K) * a.map h.bar = a * (X : Matrix (Fin n) (Fin n) K) := by
  have hXX : ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (X : Matrix (Fin n) (Fin n) K) = 1 := psuCDg2_inv_mul_self X
  calc (X : Matrix (Fin n) (Fin n) K) * a.map h.bar
      = (X : Matrix (Fin n) (Fin n) K) * a.map h.bar * 1 := (Matrix.mul_one _).symm
    _ = (X : Matrix (Fin n) (Fin n) K) * a.map h.bar *
          (((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (X : Matrix (Fin n) (Fin n) K)) := by rw [hXX]
    _ = ((X : Matrix (Fin n) (Fin n) K) * a.map h.bar *
          ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
            (X : Matrix (Fin n) (Fin n) K) := by noncomm_ring
    _ = psuTheta h X a * (X : Matrix (Fin n) (Fin n) K) := rfl
    _ = a * (X : Matrix (Fin n) (Fin n) K) := by rw [ha]

private noncomputable def psuCDg2_sFun {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (X : GL (Fin n) K) (w : Fin n → K) : Fin n → K :=
  (X : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => h.bar (w i))

private lemma psuCDg2_sFun_add {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (X : GL (Fin n) K) (x y : Fin n → K) :
    psuCDg2_sFun h X (x + y) = psuCDg2_sFun h X x + psuCDg2_sFun h X y := by
  simp only [psuCDg2_sFun]
  rw [show (fun i => h.bar ((x + y) i)) =
        (fun i => h.bar (x i)) + (fun i => h.bar (y i)) by
      funext i
      simp [Pi.add_apply],
    Matrix.mulVec_add]

private lemma psuCDg2_sFun_mulVec {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (X : GL (Fin n) K)
    (a : Matrix (Fin n) (Fin n) K) (w : Fin n → K) :
    psuCDg2_sFun h X (a *ᵥ w) = psuTheta h X a *ᵥ psuCDg2_sFun h X w := by
  simp only [psuCDg2_sFun]
  rw [psuC2dS_bar_mulVec h a w]
  simp only [Matrix.mulVec_mulVec]
  rw [psuCDg2_theta_mul_X]

private lemma psuCDg2_sFun_mem {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (X : GL (Fin n) K)
    (e : Matrix (Fin n) (Fin n) K) (hθe : psuTheta h X e = e)
    (w : LinearMap.range e.mulVecLin) :
    psuCDg2_sFun h X (w : Fin n → K) ∈ LinearMap.range e.mulVecLin := by
  obtain ⟨u, hu⟩ := w.2
  refine ⟨psuCDg2_sFun h X u, ?_⟩
  rw [Matrix.mulVecLin_apply]
  have hu' : e *ᵥ u = (w : Fin n → K) := by rw [← Matrix.mulVecLin_apply e u, hu]
  simp only [psuCDg2_sFun]
  rw [Matrix.mulVec_mulVec, ← psuCDg2_theta_eq_mul_X h X e hθe, ← Matrix.mulVec_mulVec,
    ← psuC2dS_bar_mulVec h e u, hu']

private lemma psuCKD_theta_mem {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B) :
    ∀ a : psuAlg B, psuTheta h X (a : Matrix (Fin n) (Fin n) K) ∈ psuAlg B := by
  intro a
  refine Algebra.adjoin_induction (p := fun x _ => psuTheta h X x ∈ psuAlg B)
    ?_ ?_ ?_ ?_ a.2
  · rintro x ⟨s, hs, rfl⟩
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    have hB : (B : Matrix (Fin n) (Fin n) K) ∈ psuAlg B :=
      Algebra.subset_adjoin ⟨B, rfl, rfl⟩
    obtain ⟨c, hc⟩ := S.theta_B
    rw [hc]
    exact Subalgebra.smul_mem _ hB c
  · intro r
    rw [Algebra.algebraMap_eq_smul_one, psuTheta_smul, psuTheta_one]
    exact Subalgebra.smul_mem _ (Subalgebra.one_mem _) (h.bar r)
  · intro x y hx hy hpx hpy
    rw [psuTheta_add]
    exact Subalgebra.add_mem _ hpx hpy
  · intro x y hx hy hpx hpy
    rw [psuTheta_mul]
    exact Subalgebra.mul_mem _ hpx hpy

private lemma psuCKD_theta_ringEquiv {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (e : Matrix (Fin n) (Fin n) K) (hθe : psuTheta h X e = e)
    {F : Type} [Field F] [Algebra K F]
    (π : psuAlg B →ₐ[K] F) (hπ : Function.Surjective π)
    (hker : ∀ a : psuAlg B, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e = 0)
    (hθmem : ∀ a : psuAlg B, psuTheta h X (a : Matrix (Fin n) (Fin n) K) ∈ psuAlg B) :
    ∃ τ : F ≃+* F,
      (∀ a : psuAlg B, τ (π a) =
        π ⟨psuTheta h X (a : Matrix (Fin n) (Fin n) K), hθmem a⟩) ∧
      τ ≠ RingEquiv.refl F := by
  classical
  let ρ : psuAlg B →+* F :=
    { toFun := fun a => π ⟨psuTheta h X (a : Matrix (Fin n) (Fin n) K), hθmem a⟩
      map_one' := by
        have h1 : (⟨psuTheta h X ((1 : psuAlg B) : Matrix (Fin n) (Fin n) K),
            hθmem 1⟩ : psuAlg B) = 1 := Subtype.ext (psuTheta_one h X)
        rw [h1, map_one]
      map_mul' := by
        intro a b
        have h1 : (⟨psuTheta h X ((a * b : psuAlg B) : Matrix (Fin n) (Fin n) K),
            hθmem (a * b)⟩ : psuAlg B) =
            ⟨psuTheta h X (a : Matrix (Fin n) (Fin n) K), hθmem a⟩ *
            ⟨psuTheta h X (b : Matrix (Fin n) (Fin n) K), hθmem b⟩ :=
          Subtype.ext (psuTheta_mul h X (a : Matrix (Fin n) (Fin n) K)
            (b : Matrix (Fin n) (Fin n) K))
        rw [h1, map_mul]
      map_zero' := by
        have h1 : (⟨psuTheta h X ((0 : psuAlg B) : Matrix (Fin n) (Fin n) K),
            hθmem 0⟩ : psuAlg B) = 0 := Subtype.ext (by simp [psuTheta])
        rw [h1, map_zero]
      map_add' := by
        intro a b
        have h1 : (⟨psuTheta h X ((a + b : psuAlg B) : Matrix (Fin n) (Fin n) K),
            hθmem (a + b)⟩ : psuAlg B) =
            ⟨psuTheta h X (a : Matrix (Fin n) (Fin n) K), hθmem a⟩ +
            ⟨psuTheta h X (b : Matrix (Fin n) (Fin n) K), hθmem b⟩ :=
          Subtype.ext (psuTheta_add h X (a : Matrix (Fin n) (Fin n) K)
            (b : Matrix (Fin n) (Fin n) K))
        rw [h1, map_add] }
  have hkerρ : ∀ a : psuAlg B, π.toRingHom a = 0 → ρ a = 0 := by
    intro a h0
    have hae : (a : Matrix (Fin n) (Fin n) K) * e = 0 := (hker a).mp h0
    have h1 : psuTheta h X ((a : Matrix (Fin n) (Fin n) K) * e) = 0 := by
      rw [hae]
      simp [psuTheta]
    rw [psuTheta_mul, hθe] at h1
    exact (hker ⟨psuTheta h X (a : Matrix (Fin n) (Fin n) K), hθmem a⟩).mpr h1
  obtain ⟨φ, hφ⟩ := psuC2dS_factor π.toRingHom hπ ρ hkerρ
  have hφ' : ∀ a : psuAlg B, φ (π a) =
      π ⟨psuTheta h X (a : Matrix (Fin n) (Fin n) K), hθmem a⟩ := fun a => hφ a
  have hφφa : ∀ a : psuAlg B, φ (φ (π a)) = π a := by
    intro a
    rw [hφ' a, hφ' ⟨psuTheta h X (a : Matrix (Fin n) (Fin n) K), hθmem a⟩]
    congr 1
    exact Subtype.ext (psuTheta_theta h X S.X_sq (a : Matrix (Fin n) (Fin n) K))
  have hφφ : ∀ x : F, φ (φ x) = x := by
    intro x
    obtain ⟨a, rfl⟩ := hπ x
    exact hφφa a
  refine ⟨RingEquiv.ofBijective φ (Function.Involutive.bijective hφφ), ?_, ?_⟩
  · intro a
    simpa only [RingEquiv.ofBijective_apply] using hφ' a
  · intro hrefl
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    have hτc : (RingEquiv.ofBijective φ (Function.Involutive.bijective hφφ))
        (algebraMap K F c) = algebraMap K F (h.bar c) := by
      rw [RingEquiv.ofBijective_apply, ← AlgHom.commutes π c,
        hφ' (algebraMap K (psuAlg B) c)]
      have hθc : (⟨psuTheta h X ((algebraMap K (psuAlg B) c) : Matrix (Fin n) (Fin n) K),
          hθmem _⟩ : psuAlg B) = algebraMap K (psuAlg B) (h.bar c) := by
        apply Subtype.ext
        show psuTheta h X ((algebraMap K (psuAlg B) c : psuAlg B) : Matrix (Fin n) (Fin n) K) =
          ((algebraMap K (psuAlg B) (h.bar c) : psuAlg B) : Matrix (Fin n) (Fin n) K)
        rw [Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap,
          Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
          psuTheta_smul, psuTheta_one]
      rw [hθc, AlgHom.commutes]
    have h2 : algebraMap K F c = algebraMap K F (h.bar c) := by
      rw [← hτc, hrefl]
      rfl
    exact hc ((algebraMap K F).injective h2).symm

private lemma psuCKD_s_exists {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (e : Matrix (Fin n) (Fin n) K) (hθe : psuTheta h X e = e)
    {F : Type} [Field F] [Algebra K F]
    [Module F (LinearMap.range e.mulVecLin)] [IsScalarTower K F (LinearMap.range e.mulVecLin)]
    (π : psuAlg B →ₐ[K] F)
    (hθmem : ∀ a : psuAlg B, psuTheta h X (a : Matrix (Fin n) (Fin n) K) ∈ psuAlg B)
    (τ : F ≃+* F)
    (hτ : ∀ a : psuAlg B, τ (π a) =
      π ⟨psuTheta h X (a : Matrix (Fin n) (Fin n) K), hθmem a⟩)
    (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K)
    (hbd : PsuBD e π ψ) :
    ∃ s : LinearMap.range e.mulVecLin → LinearMap.range e.mulVecLin,
      (∀ w : LinearMap.range e.mulVecLin,
        ((s w : LinearMap.range e.mulVecLin) : Fin n → K) =
          (X : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => h.bar ((w : Fin n → K) i))) ∧
      (∀ x y, s (x + y) = s x + s y) ∧
      (∀ (c : F) (x : LinearMap.range e.mulVecLin), s (c • x) = τ c • s x) ∧
      (∃ x, s x ≠ 0) := by
  classical
  let s : LinearMap.range e.mulVecLin → LinearMap.range e.mulVecLin :=
    fun w => ⟨psuCDg2_sFun h X (w : Fin n → K), psuCDg2_sFun_mem h X e hθe w⟩
  have hsdef : ∀ w : LinearMap.range e.mulVecLin,
      ((s w : LinearMap.range e.mulVecLin) : Fin n → K) = psuCDg2_sFun h X (w : Fin n → K) :=
    fun w => rfl
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · intro w
    rw [hsdef w]
    rfl
  · intro x y
    apply Subtype.ext
    show psuCDg2_sFun h X ((x : Fin n → K) + (y : Fin n → K)) =
      psuCDg2_sFun h X (x : Fin n → K) + psuCDg2_sFun h X (y : Fin n → K)
    exact psuCDg2_sFun_add h X _ _
  · intro c x
    obtain ⟨a, ha⟩ := hbd.hπ c
    apply Subtype.ext
    have hcx : ((c • x : LinearMap.range e.mulVecLin) : Fin n → K) =
        (a : Matrix (Fin n) (Fin n) K) *ᵥ (x : Fin n → K) := by
      rw [← ha]
      exact hbd.hact a x
    have hτa : τ c = π ⟨psuTheta h X (a : Matrix (Fin n) (Fin n) K), hθmem a⟩ := by
      rw [← ha, hτ a]
    have hR : ((τ c • s x : LinearMap.range e.mulVecLin) : Fin n → K) =
        psuTheta h X (a : Matrix (Fin n) (Fin n) K) *ᵥ psuCDg2_sFun h X (x : Fin n → K) := by
      rw [hτa, hbd.hact, hsdef x]
    rw [hsdef (c • x), hcx, hR, psuCDg2_sFun_mulVec]
  · haveI : FiniteDimensional F (LinearMap.range e.mulVecLin) :=
      FiniteDimensional.of_finrank_pos hbd.hpos
    obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hbd.hpos
    refine ⟨x, ?_⟩
    intro h0
    apply hx
    apply Subtype.ext
    have h1 : psuCDg2_sFun h X (x : Fin n → K) = 0 := by
      have h2 : ((s x : LinearMap.range e.mulVecLin) : Fin n → K) = 0 := by rw [h0]; rfl
      rwa [hsdef x] at h2
    have hσ : (fun i => h.bar ((x : Fin n → K) i)) = 0 := by
      have hXinv : ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          psuCDg2_sFun h X (x : Fin n → K) =
            (fun i => h.bar ((x : Fin n → K) i)) := by
        simp only [psuCDg2_sFun]
        rw [Matrix.mulVec_mulVec, psuCDg2_inv_mul_self, Matrix.one_mulVec]
      rw [h1, Matrix.mulVec_zero] at hXinv
      exact hXinv.symm
    funext i
    exact h.bar.injective (by simpa using congrFun hσ i)

private lemma psuCKD_s_comm {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hne : psuDag h e ≠ e)
    {F : Type} [Field F] [Algebra K F] [Finite F]
    [Module F (LinearMap.range e.mulVecLin)] [IsScalarTower K F (LinearMap.range e.mulVecLin)]
    (π : psuAlg B →ₐ[K] F)
    (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K)
    (hbd : PsuBD e π ψ)
    (hk : 2 ≤ Module.finrank F (LinearMap.range e.mulVecLin))
    (s : LinearMap.range e.mulVecLin → LinearMap.range e.mulVecLin)
    (hs : ∀ w : LinearMap.range e.mulVecLin,
      ((s w : LinearMap.range e.mulVecLin) : Fin n → K) =
        (X : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => h.bar ((w : Fin n → K) i))) :
    ∀ g : LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin,
      LinearMap.det (g : LinearMap.range e.mulVecLin →ₗ[F] LinearMap.range e.mulVecLin) = 1 →
        ∀ x, s (g x) = g (s x) := by
  intro g hg x
  obtain ⟨y, hy, hyact⟩ := psuK_sl_in_commutator S P hP e he hne π ψ hbd hk g hg
  have hθy : psuTheta h X (((y : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (((y : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    psuK_theta_fixed_of_commutator S e y hy
  have hyX : (X : Matrix (Fin n) (Fin n) K) *
      ((((y : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).map h.bar =
      (((y : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (X : Matrix (Fin n) (Fin n) K) :=
    psuCDg2_theta_eq_mul_X h X _ hθy
  apply Subtype.ext
  rw [hs (g x)]
  have hgx : ((g x : LinearMap.range e.mulVecLin) : Fin n → K) =
      (((y : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        (x : Fin n → K) := (hyact x).symm
  rw [hgx, psuC2dS_bar_mulVec h _ (x : Fin n → K), Matrix.mulVec_mulVec, hyX,
    ← Matrix.mulVec_mulVec, ← hs x]
  exact hyact (s x)

private theorem psuCK_kind_D_core {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P)
    (hθe : psuTheta h X e = e) (hne : psuDag h e ≠ e)
    {F : Type} [Field F] [Algebra K F] [Finite F]
    [Module F (LinearMap.range e.mulVecLin)] [IsScalarTower K F (LinearMap.range e.mulVecLin)]
    (π : psuAlg B →ₐ[K] F)
    (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K)
    (hbd : PsuBD e π ψ) :
    Group.IsSolvable ↥(psuBlock h B e) := by
  by_cases hk1 : Module.finrank F (LinearMap.range e.mulVecLin) = 1
  · exact psuK_solvable_of_finrank_one S P hP e he π ψ hbd hk1
  · have hk2 : 2 ≤ Module.finrank F (LinearMap.range e.mulVecLin) := by
      have hpos := hbd.hpos
      have hne1 : Module.finrank F (LinearMap.range e.mulVecLin) ≠ 1 := hk1
      omega
    have hθmem := psuCKD_theta_mem S
    obtain ⟨τ, hτ, hτne⟩ := psuCKD_theta_ringEquiv S e hθe π hbd.hπ hbd.hker hθmem
    obtain ⟨s, hsform, hsadd, hssmul, hsne⟩ :=
      psuCKD_s_exists e hθe π hθmem τ hτ ψ hbd
    have hcomm := psuCKD_s_comm S P hP e he hne π ψ hbd hk2 s hsform
    have hsmul := psuCKD_smul_mem_of_comm s hsadd hcomm
    have hzero := psuCKD_eq_zero_of_smul_mem (Module.finrank F (LinearMap.range e.mulVecLin))
      hk2 rfl τ hτne s hsadd hssmul hsmul
    obtain ⟨x, hx⟩ := hsne
    exact absurd (hzero x) hx

private def psuCKC_b {n : ℕ} {K : Type} [Field K] (X : GL (Fin n) K) (u v : Fin n → K) : K :=
  u ⬝ᵥ ((psuJ n K * ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *ᵥ v)

private noncomputable abbrev psuCKCg1_M {n : ℕ} {K : Type} [Field K] (X : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K :=
  psuJ n K * ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

private lemma psuCKCg1_Msymm {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {X : GL (Fin n) K}
    (hX : X ∈ primeFormUnitary h (psuJ n K))
    (hXs : (X : Matrix (Fin n) (Fin n) K) * (X : Matrix (Fin n) (Fin n) K).map h.bar = 1) :
    (psuCKCg1_M X)ᵀ = psuCKCg1_M X := by
  simpa [psuCKCg1_M] using (psuPsi_eq_adjoint h X hX hXs (0 : Matrix (Fin n) (Fin n) K)).1

private lemma psuCKCg1_Mdet_isUnit {n : ℕ} {K : Type} [Field K] (X : GL (Fin n) K) :
    IsUnit (psuCKCg1_M X).det := by
  refine (Matrix.isUnit_iff_isUnit_det (psuCKCg1_M X)).mp ?_
  simpa [psuCKCg1_M] using ((AutPSU.gramJ n).isUnit.mul (X⁻¹).isUnit)

private lemma psuCKCg1_M_formAdj {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {X : GL (Fin n) K}
    (hX : X ∈ primeFormUnitary h (psuJ n K))
    (hXs : (X : Matrix (Fin n) (Fin n) K) * (X : Matrix (Fin n) (Fin n) K).map h.bar = 1)
    (a : Matrix (Fin n) (Fin n) K) :
    psuPsi h X a = formAdj (RingHom.id K) (psuCKCg1_M X) a := by
  simpa [psuCKCg1_M] using (psuPsi_eq_adjoint h X hX hXs a).2

private lemma psuCKCg1_dotProduct_smul {n : ℕ} {K : Type} [Field K] (c : K) (u w : Fin n → K) :
    u ⬝ᵥ (c • w) = c * (u ⬝ᵥ w) := by
  rw [dotProduct_comm u (c • w), smul_dotProduct, dotProduct_comm w u, smul_eq_mul]

private lemma psuCKCg1_b_addL {n : ℕ} {K : Type} [Field K] (X : GL (Fin n) K)
    (x y z : Fin n → K) : psuCKC_b X (x + y) z = psuCKC_b X x z + psuCKC_b X y z := by
  unfold psuCKC_b
  rw [add_dotProduct]

private lemma psuCKCg1_b_addR {n : ℕ} {K : Type} [Field K] (X : GL (Fin n) K)
    (x y z : Fin n → K) : psuCKC_b X x (y + z) = psuCKC_b X x y + psuCKC_b X x z := by
  unfold psuCKC_b
  rw [Matrix.mulVec_add, dotProduct_add]

private lemma psuCKCg1_b_smulR {n : ℕ} {K : Type} [Field K] (X : GL (Fin n) K)
    (c : K) (x y : Fin n → K) : psuCKC_b X x (c • y) = c * psuCKC_b X x y := by
  unfold psuCKC_b
  rw [Matrix.mulVec_smul, psuCKCg1_dotProduct_smul]

private lemma psuCKCg1_b_symm {n : ℕ} {K : Type} [Field K] (X : GL (Fin n) K)
    (hsymm : (psuCKCg1_M X)ᵀ = psuCKCg1_M X) (x y : Fin n → K) :
    psuCKC_b X x y = psuCKC_b X y x := by
  change x ⬝ᵥ (psuCKCg1_M X *ᵥ y) = y ⬝ᵥ (psuCKCg1_M X *ᵥ x)
  conv_lhs => rw [← hsymm]
  rw [Matrix.dotProduct_transpose_mulVec]

private lemma psuCKCg1_transpose_mul_eq_M_formAdj {n : ℕ} {K : Type} [Field K]
    (X : GL (Fin n) K) (hG : IsUnit (psuCKCg1_M X).det)
    (a : Matrix (Fin n) (Fin n) K) :
    Matrix.transpose a * psuCKCg1_M X =
      psuCKCg1_M X * formAdj (RingHom.id K) (psuCKCg1_M X) a := by
  unfold formAdj
  have hmap : (a.map (RingHom.id K)) = a := by
    ext i j
    rfl
  rw [hmap]
  calc Matrix.transpose a * psuCKCg1_M X
      = (psuCKCg1_M X * (psuCKCg1_M X)⁻¹) * (Matrix.transpose a * psuCKCg1_M X) := by
        rw [Matrix.mul_nonsing_inv (psuCKCg1_M X) hG, Matrix.one_mul]
    _ = psuCKCg1_M X * ((psuCKCg1_M X)⁻¹ * Matrix.transpose a * psuCKCg1_M X) := by
        simp only [Matrix.mul_assoc]

private lemma psuCKCg1_b_adj_formAdj {n : ℕ} {K : Type} [Field K] (X : GL (Fin n) K)
    (a : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    psuCKC_b X (a *ᵥ x) y =
      psuCKC_b X x (formAdj (RingHom.id K) (psuCKCg1_M X) a *ᵥ y) := by
  have hG : IsUnit (psuCKCg1_M X).det := psuCKCg1_Mdet_isUnit X
  change (a *ᵥ x) ⬝ᵥ (psuCKCg1_M X *ᵥ y) =
    x ⬝ᵥ (psuCKCg1_M X *ᵥ (formAdj (RingHom.id K) (psuCKCg1_M X) a *ᵥ y))
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose a x,
      Matrix.vecMul_vecMul, Matrix.dotProduct_mulVec,
      psuCKCg1_transpose_mul_eq_M_formAdj X hG a]

private lemma psuCKCg1_b_adj {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {X : GL (Fin n) K}
    (hX : X ∈ primeFormUnitary h (psuJ n K))
    (hXs : (X : Matrix (Fin n) (Fin n) K) * (X : Matrix (Fin n) (Fin n) K).map h.bar = 1)
    (a : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    psuCKC_b X (a *ᵥ x) y = psuCKC_b X x (psuPsi h X a *ᵥ y) := by
  rw [psuCKCg1_b_adj_formAdj X a x y, ← psuCKCg1_M_formAdj hX hXs a]

private lemma psuCKCg1_b_nd {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {X : GL (Fin n) K}
    (hX : X ∈ primeFormUnitary h (psuJ n K))
    (hXs : (X : Matrix (Fin n) (Fin n) K) * (X : Matrix (Fin n) (Fin n) K).map h.bar = 1)
    {e : Matrix (Fin n) (Fin n) K} (hee : e * e = e) (hstar : psuPsi h X e = e)
    (x : LinearMap.range e.mulVecLin)
    (hx : ∀ y : LinearMap.range e.mulVecLin,
      psuCKC_b X (x : Fin n → K) (y : Fin n → K) = 0) : x = 0 := by
  have hG : IsUnit (psuCKCg1_M X).det := psuCKCg1_Mdet_isUnit X
  have hGe : Matrix.transpose e * psuCKCg1_M X = psuCKCg1_M X * e := by
    have h := hstar
    rw [psuCKCg1_M_formAdj hX hXs e] at h
    rw [formAdj] at h
    have hmap : (e.map (RingHom.id K)) = e := by
      ext i j
      rfl
    rw [hmap] at h
    calc Matrix.transpose e * psuCKCg1_M X
        = (psuCKCg1_M X * (psuCKCg1_M X)⁻¹) * (Matrix.transpose e * psuCKCg1_M X) := by
          rw [Matrix.mul_nonsing_inv (psuCKCg1_M X) hG, Matrix.one_mul]
      _ = psuCKCg1_M X * ((psuCKCg1_M X)⁻¹ * Matrix.transpose e * psuCKCg1_M X) := by
          simp only [Matrix.mul_assoc]
      _ = psuCKCg1_M X * e := by rw [h]
  have hz : ∀ z : Fin n → K, psuCKC_b X (x : Fin n → K) z = 0 := by
    intro z
    have h1 : psuCKC_b X (x : Fin n → K) (e *ᵥ z) = 0 :=
      hx ⟨e *ᵥ z, LinearMap.mem_range.mpr ⟨z, Matrix.mulVecLin_apply e z⟩⟩
    have h2 : psuCKC_b X (x : Fin n → K) ((1 - e) *ᵥ z) = 0 := by
      obtain ⟨v, hv⟩ := x.2
      have hv' : e *ᵥ v = (x : Fin n → K) := by simpa [Matrix.mulVecLin_apply] using hv
      have hxvec : (x : Fin n → K) = v ᵥ* Matrix.transpose e := by
        rw [← hv', Matrix.vecMul_transpose]
      calc psuCKC_b X (x : Fin n → K) ((1 - e) *ᵥ z)
          = ((x : Fin n → K) ᵥ* (psuCKCg1_M X * (1 - e))) ⬝ᵥ z := by
            change (x : Fin n → K) ⬝ᵥ (psuCKCg1_M X *ᵥ ((1 - e) *ᵥ z)) = _
            rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
        _ = 0 := by
            rw [hxvec, Matrix.vecMul_vecMul]
            have hz0 : Matrix.transpose e * (psuCKCg1_M X * (1 - e)) = 0 := by
              rw [← Matrix.mul_assoc, hGe, Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one,
                hee, sub_self, Matrix.mul_zero]
            rw [hz0, Matrix.vecMul_zero, zero_dotProduct]
    have hdecomp : z = e *ᵥ z + (1 - e) *ᵥ z := by
      rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
    calc psuCKC_b X (x : Fin n → K) z
        = psuCKC_b X (x : Fin n → K) (e *ᵥ z) +
            psuCKC_b X (x : Fin n → K) ((1 - e) *ᵥ z) := by
          rw [← psuCKCg1_b_addR, ← hdecomp]
      _ = 0 := by rw [h1, h2, add_zero]
  have hx0 : (x : Fin n → K) = 0 := by
    funext i
    have h := hz ((psuCKCg1_M X)⁻¹ *ᵥ (Pi.single i 1))
    rw [psuCKC_b, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv (psuCKCg1_M X) hG,
      Matrix.one_mulVec] at h
    simp only [dotProduct] at h
    rw [Finset.sum_eq_single i] at h
    · simpa using h
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  exact Subtype.ext hx0

private lemma psuCKCg1_psi_algebraMap {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (c : K) :
    psuPsi h X ((algebraMap K (psuAlg B) c) : Matrix (Fin n) (Fin n) K) =
      ((algebraMap K (psuAlg B) c) : Matrix (Fin n) (Fin n) K) := by
  simp only [Algebra.algebraMap_eq_smul_one, Subalgebra.coe_smul, Subalgebra.coe_one,
    psuPsi_smul, psuPsi_one]

private lemma psuCKCg1_tau {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    {e : Matrix (Fin n) (Fin n) K} (he : e ∈ psuAlg B) (hψ : psuPsi h X e = e)
    {F : Type} [Field F] [Algebra K F]
    (π : psuAlg B →ₐ[K] F) (hπ : Function.Surjective π)
    (hker : ∀ a : psuAlg B, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e = 0) :
    ∃ τ : F ≃+* F, (∀ x, τ (τ x) = x) ∧
      (∀ c : K, τ (algebraMap K F c) = algebraMap K F c) ∧
      ∀ a : psuAlg B, τ (π a) =
        π ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K),
          (psuGraph_star_mem S a a.2).2⟩ := by
  have hpsi0 : psuPsi h X (0 : Matrix (Fin n) (Fin n) K) = 0 := by
    rw [show (0 : Matrix (Fin n) (Fin n) K) = (0 : K) • (1 : Matrix (Fin n) (Fin n) K) by simp,
      psuPsi_smul, psuPsi_one, zero_smul]
  let ρ : psuAlg B →+* F :=
    { toFun := fun a => π ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a a.2).2⟩
      map_one' := by
        have h1 : (⟨psuPsi h X ((1 : psuAlg B) : Matrix (Fin n) (Fin n) K),
            (psuGraph_star_mem S (1 : psuAlg B) (1 : psuAlg B).2).2⟩ : psuAlg B) = 1 :=
          Subtype.ext (psuPsi_one h X)
        rw [h1, map_one]
      map_mul' := by
        intro a b
        have h1 : (⟨psuPsi h X ((a * b : psuAlg B) : Matrix (Fin n) (Fin n) K),
            (psuGraph_star_mem S (a * b) (a * b).2).2⟩ : psuAlg B) =
            ⟨psuPsi h X (b : Matrix (Fin n) (Fin n) K),
              (psuGraph_star_mem S b b.2).2⟩ *
            ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K),
              (psuGraph_star_mem S a a.2).2⟩ :=
          Subtype.ext (psuPsi_mul h X _ _)
        rw [h1, map_mul, mul_comm]
      map_zero' := by
        have h1 : (⟨psuPsi h X ((0 : psuAlg B) : Matrix (Fin n) (Fin n) K),
            (psuGraph_star_mem S (0 : psuAlg B) (0 : psuAlg B).2).2⟩ : psuAlg B) = 0 :=
          Subtype.ext hpsi0
        rw [h1, map_zero]
      map_add' := by
        intro a b
        have h1 : (⟨psuPsi h X ((a + b : psuAlg B) : Matrix (Fin n) (Fin n) K),
            (psuGraph_star_mem S (a + b) (a + b).2).2⟩ : psuAlg B) =
            ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K),
              (psuGraph_star_mem S a a.2).2⟩ +
            ⟨psuPsi h X (b : Matrix (Fin n) (Fin n) K),
              (psuGraph_star_mem S b b.2).2⟩ :=
          Subtype.ext (psuPsi_add h X _ _)
        rw [h1, map_add] }
  have hkerρ : ∀ a : psuAlg B, π.toRingHom a = 0 → ρ a = 0 := by
    intro a h0
    have hae : (a : Matrix (Fin n) (Fin n) K) * e = 0 := (hker a).mp h0
    have h1 : psuPsi h X ((a : Matrix (Fin n) (Fin n) K) * e) = 0 := by
      rw [hae, hpsi0]
    rw [psuPsi_mul, hψ] at h1
    have h2 : psuPsi h X (a : Matrix (Fin n) (Fin n) K) * e = 0 := by
      rw [psuC2dS_comm B (psuPsi h X (a : Matrix (Fin n) (Fin n) K))
        (psuGraph_star_mem S a a.2).2 e he]
      exact h1
    exact (hker ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K),
      (psuGraph_star_mem S a a.2).2⟩).mpr h2
  obtain ⟨φ, hφ⟩ := psuC2dS_factor π.toRingHom hπ ρ hkerρ
  have hφ' : ∀ a : psuAlg B, φ (π a) =
      π ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a a.2).2⟩ := fun a => hφ a
  have hφφa : ∀ a : psuAlg B, φ (φ (π a)) = π a := by
    intro a
    rw [hφ' a, hφ' ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K),
      (psuGraph_star_mem S a a.2).2⟩]
    congr 1
    exact Subtype.ext (psuPsi_psi h X S.X_mem S.X_sq (a : Matrix (Fin n) (Fin n) K))
  have hφφ : ∀ x : F, φ (φ x) = x := by
    intro x
    obtain ⟨a, rfl⟩ := hπ x
    exact hφφa a
  refine ⟨RingEquiv.ofBijective φ (Function.Involutive.bijective hφφ), ?_, ?_, ?_⟩
  · intro x
    simpa only [RingEquiv.ofBijective_apply] using hφφ x
  · intro c
    rw [RingEquiv.ofBijective_apply, ← AlgHom.commutes π c, hφ' (algebraMap K (psuAlg B) c)]
    rw [show (⟨psuPsi h X ((algebraMap K (psuAlg B) c) : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S (algebraMap K (psuAlg B) c)
          (algebraMap K (psuAlg B) c).2).2⟩ : psuAlg B) =
        algebraMap K (psuAlg B) c from Subtype.ext (psuCKCg1_psi_algebraMap c)]
  · intro a
    rw [RingEquiv.ofBijective_apply]
    exact hφ' a

private lemma psuCKCg1_trace_form {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    {e : Matrix (Fin n) (Fin n) K} (hee : e * e = e) (hψ : psuPsi h X e = e)
    {F : Type} [Field F] [Algebra K F] [Finite F]
    [Module F (LinearMap.range e.mulVecLin)] [IsScalarTower K F (LinearMap.range e.mulVecLin)]
    {π : psuAlg B →ₐ[K] F} (hπ : Function.Surjective π)
    (hact : ∀ (a : psuAlg B) (w : LinearMap.range e.mulVecLin),
      ((π a • w : LinearMap.range e.mulVecLin) : Fin n → K) =
        (a : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K))
    (τ : F ≃+* F) (hττ : ∀ x, τ (τ x) = x)
    (hτσ : ∀ c : K, τ (algebraMap K F c) = algebraMap K F c)
    (hτπ : ∀ a : psuAlg B, τ (π a) =
      π ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a a.2).2⟩) :
    ∃ H : LinearMap.range e.mulVecLin → LinearMap.range e.mulVecLin → F,
      (∀ x y z, H (x + y) z = H x z + H y z) ∧
      (∀ x y z, H x (y + z) = H x y + H x z) ∧
      (∀ (a : F) x y, H (a • x) y = τ a * H x y) ∧
      (∀ (a : F) x y, H x (a • y) = a * H x y) ∧
      (∀ x y, H x y = τ (H y x)) ∧
      (∀ x, (∀ y, H x y = 0) → x = 0) ∧
      (∀ (x y : LinearMap.range e.mulVecLin),
        psuCKC_b X (x : Fin n → K) (y : Fin n → K) = Algebra.trace K F (H x y)) := by
  have hKF : ∀ (a : F) (x y : LinearMap.range e.mulVecLin),
      psuCKC_b X ((a • x : LinearMap.range e.mulVecLin) : Fin n → K) (y : Fin n → K) =
      psuCKC_b X (x : Fin n → K)
        ((τ a • y : LinearMap.range e.mulVecLin) : Fin n → K) := by
    intro a x y
    obtain ⟨a0, rfl⟩ := hπ a
    have hx : ((π a0 • x : LinearMap.range e.mulVecLin) : Fin n → K) =
        (a0 : Matrix (Fin n) (Fin n) K) *ᵥ (x : Fin n → K) := hact a0 x
    have hy : ((τ (π a0) • y : LinearMap.range e.mulVecLin) : Fin n → K) =
        (psuPsi h X (a0 : Matrix (Fin n) (Fin n) K)) *ᵥ (y : Fin n → K) := by
      rw [hτπ a0]
      exact hact ⟨psuPsi h X (a0 : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a0 a0.2).2⟩ y
    rw [hx, hy]
    exact psuCKCg1_b_adj S.X_mem S.X_sq (a0 : Matrix (Fin n) (Fin n) K)
      (x : Fin n → K) (y : Fin n → K)
  exact exists_hermTransfer (σ := RingHom.id K) (τ := τ) (hσσ := fun c => rfl) (hττ := hττ)
    (hτσ := hτσ)
    (hK := fun (x y : LinearMap.range e.mulVecLin) =>
      psuCKC_b X (x : Fin n → K) (y : Fin n → K))
    (hKaddL := fun x y z => psuCKCg1_b_addL X _ _ _)
    (hKaddR := fun x y z => psuCKCg1_b_addR X _ _ _)
    (hKsmulR := fun c x y => psuCKCg1_b_smulR X c _ _)
    (hKherm := fun x y => by
      show psuCKC_b X (x : Fin n → K) (y : Fin n → K) =
        psuCKC_b X (y : Fin n → K) (x : Fin n → K)
      exact psuCKCg1_b_symm X (psuCKCg1_Msymm S.X_mem S.X_sq) _ _)
    (hKnd := fun x hx => psuCKCg1_b_nd S.X_mem S.X_sq hee hψ x hx)
    (hKF := hKF)

private lemma psuCKCg1_trace_ext {K F : Type} [Field K] [Field F] [Algebra K F]
    [FiniteDimensional K F] [Algebra.IsSeparable K F] {z z' : F}
    (h : ∀ c : F, Algebra.trace K F (c * z) = Algebra.trace K F (c * z')) : z = z' := by
  have hzero : ∀ c : F, Algebra.trace K F (c * (z - z')) = 0 := by
    intro c
    rw [mul_sub, map_sub, h c, sub_self]
  have hz : z - z' = 0 := by
    let D : F ≃ₗ[K] Module.Dual K F :=
      (Algebra.traceForm K F).toDual (traceForm_nondegenerate K F)
    have hD : D (z - z') = 0 := by
      ext c
      rw [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply, mul_comm]
      exact hzero c
    exact D.injective (by rw [hD, map_zero])
  exact sub_eq_zero.mp hz

private lemma psuCKCg1_H_preserved {K F V : Type} [Field K] [Field F] [Algebra K F]
    [FiniteDimensional K F] [Algebra.IsSeparable K F] [AddCommGroup V] [Module F V]
    (τ : F ≃+* F) (hK : V → V → K) (H : V → V → F)
    (htrace : ∀ x y, hK x y = Algebra.trace K F (H x y))
    (hHsmulL : ∀ (a : F) x y, H (a • x) y = τ a * H x y)
    (hHsmulR : ∀ (a : F) x y, H x (a • y) = a * H x y)
    (hKF : ∀ (a : F) x y, hK (a • x) y = hK x (τ a • y))
    (g : V ≃ₗ[F] V) (hpres : ∀ x y, hK (g x) (g y) = hK x y) :
    ∀ x y, H (g x) (g y) = H x y := by
  intro x y
  apply psuCKCg1_trace_ext (K := K) (F := F)
  intro c
  obtain ⟨a, rfl⟩ := τ.surjective c
  calc Algebra.trace K F (τ a * H (g x) (g y))
      = Algebra.trace K F (H (a • g x) (g y)) := by rw [hHsmulL]
    _ = hK (a • g x) (g y) := (htrace (a • g x) (g y)).symm
    _ = hK (g (a • x)) (g y) := by rw [map_smul]
    _ = hK (a • x) y := hpres (a • x) y
    _ = hK x (τ a • y) := hKF a x y
    _ = Algebra.trace K F (H x (τ a • y)) := htrace x (τ a • y)
    _ = Algebra.trace K F (τ a * H x y) := by rw [hHsmulR]

private lemma psuCKCg1_isometry {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P)
    (hne : psuDag h e ≠ e)
    {F : Type} [Field F] [Algebra K F] [Finite F]
    [Module F (LinearMap.range e.mulVecLin)] [IsScalarTower K F (LinearMap.range e.mulVecLin)]
    (π : psuAlg B →ₐ[K] F)
    (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K)
    (hbd : PsuBD e π ψ)
    (hk : 2 ≤ Module.finrank F (LinearMap.range e.mulVecLin))
    (τ : F ≃+* F)
    (H : LinearMap.range e.mulVecLin → LinearMap.range e.mulVecLin → F)
    (htrace : ∀ (x y : LinearMap.range e.mulVecLin),
      psuCKC_b X (x : Fin n → K) (y : Fin n → K) = Algebra.trace K F (H x y))
    (hHsmulL : ∀ (a : F) x y, H (a • x) y = τ a * H x y)
    (hHsmulR : ∀ (a : F) x y, H x (a • y) = a * H x y)
    (hKF : ∀ (a : F) (x y : LinearMap.range e.mulVecLin),
      psuCKC_b X ((a • x : LinearMap.range e.mulVecLin) : Fin n → K) (y : Fin n → K) =
      psuCKC_b X (x : Fin n → K)
        ((τ a • y : LinearMap.range e.mulVecLin) : Fin n → K)) :
    ∀ t : LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin,
      LinearMap.det (t : LinearMap.range e.mulVecLin →ₗ[F] LinearMap.range e.mulVecLin) = 1 →
      ∀ x y, H (t x) (t y) = H x y := by
  haveI : Module.Finite K F := Module.Finite.of_finite
  haveI : Algebra.IsSeparable K F := by infer_instance
  intro t htdet
  obtain ⟨y0, hy0mem, hy0act⟩ := psuK_sl_in_commutator S P hP e he hne π ψ hbd hk t htdet
  have hθ : psuTheta h X (((y0 : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (((y0 : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    psuK_theta_fixed_of_commutator S e y0 hy0mem
  have hpsiy : psuPsi h X (((y0 : AutPSU.XJ h n) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *
      (((y0 : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
    psuK_psi_mul_eq_one_of_theta_fixed y0 hθ
  have hpres : ∀ x y : LinearMap.range e.mulVecLin,
      psuCKC_b X ((t x : LinearMap.range e.mulVecLin) : Fin n → K)
        ((t y : LinearMap.range e.mulVecLin) : Fin n → K) =
      psuCKC_b X (x : Fin n → K) (y : Fin n → K) := by
    intro x y
    rw [← hy0act x, ← hy0act y]
    rw [psuCKCg1_b_adj S.X_mem S.X_sq, Matrix.mulVec_mulVec, hpsiy, Matrix.one_mulVec]
  exact fun x y => psuCKCg1_H_preserved τ
    (fun x y : LinearMap.range e.mulVecLin => psuCKC_b X (x : Fin n → K) (y : Fin n → K))
    H htrace hHsmulL hHsmulR hKF t hpres x y

private lemma psuCKC_form_transfer {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P)
    (hne : psuDag h e ≠ e) (hψ : psuPsi h X e = e)
    {F : Type} [Field F] [Algebra K F] [Finite F]
    [Module F (LinearMap.range e.mulVecLin)] [IsScalarTower K F (LinearMap.range e.mulVecLin)]
    (π : psuAlg B →ₐ[K] F)
    (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K)
    (hbd : PsuBD e π ψ)
    (hk : 2 ≤ Module.finrank F (LinearMap.range e.mulVecLin)) :
    ∃ (τ : F ≃+* F) (H : LinearMap.range e.mulVecLin → LinearMap.range e.mulVecLin → F),
      (∀ x, τ (τ x) = x) ∧
      (∀ c : K, τ (algebraMap K F c) = algebraMap K F c) ∧
      (∀ a : psuAlg B, τ (π a) = π ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a a.2).2⟩) ∧
      (∀ x y z, H (x + y) z = H x z + H y z) ∧
      (∀ x y z, H x (y + z) = H x y + H x z) ∧
      (∀ (a : F) x y, H (a • x) y = τ a * H x y) ∧
      (∀ (a : F) x y, H x (a • y) = a * H x y) ∧
      (∀ x y, H x y = τ (H y x)) ∧
      (∀ x, (∀ y, H x y = 0) → x = 0) ∧
      (∀ (x y : LinearMap.range e.mulVecLin),
        psuCKC_b X (x : Fin n → K) (y : Fin n → K) = Algebra.trace K F (H x y)) ∧
      (∀ t : LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin,
        LinearMap.det (t : LinearMap.range e.mulVecLin →ₗ[F] LinearMap.range e.mulVecLin) = 1 →
        ∀ x y, H (t x) (t y) = H x y) := by
  have hee : e * e = e := IsIdempotentElem.eq ((hP.1 e).mp he).2.1
  have heB : e ∈ psuAlg B := ((hP.1 e).mp he).1
  obtain ⟨τ, hττ, hτK, hτπ⟩ := psuCKCg1_tau S heB hψ π hbd.hπ hbd.hker
  have hKF : ∀ (a : F) (x y : LinearMap.range e.mulVecLin),
      psuCKC_b X ((a • x : LinearMap.range e.mulVecLin) : Fin n → K) (y : Fin n → K) =
      psuCKC_b X (x : Fin n → K)
        ((τ a • y : LinearMap.range e.mulVecLin) : Fin n → K) := by
    intro a x y
    obtain ⟨a0, rfl⟩ := hbd.hπ a
    have hx : ((π a0 • x : LinearMap.range e.mulVecLin) : Fin n → K) =
        (a0 : Matrix (Fin n) (Fin n) K) *ᵥ (x : Fin n → K) := hbd.hact a0 x
    have hy : ((τ (π a0) • y : LinearMap.range e.mulVecLin) : Fin n → K) =
        (psuPsi h X (a0 : Matrix (Fin n) (Fin n) K)) *ᵥ (y : Fin n → K) := by
      rw [hτπ a0]
      exact hbd.hact ⟨psuPsi h X (a0 : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a0 a0.2).2⟩ y
    rw [hx, hy]
    exact psuCKCg1_b_adj S.X_mem S.X_sq (a0 : Matrix (Fin n) (Fin n) K)
      (x : Fin n → K) (y : Fin n → K)
  obtain ⟨H, hHaddL, hHaddR, hHsmulL, hHsmulR, hHherm, hHnd, hHtrace⟩ :=
    psuCKCg1_trace_form S hee hψ hbd.hπ hbd.hact τ hττ hτK hτπ
  refine ⟨τ, H, hττ, hτK, hτπ, hHaddL, hHaddR, hHsmulL, hHsmulR, hHherm, hHnd, hHtrace, ?_⟩
  exact psuCKCg1_isometry S P hP e he hne π ψ hbd hk τ H hHtrace hHsmulL hHsmulR hKF

private lemma psuCKCg2_psi_mul_e {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (e : Matrix (Fin n) (Fin n) K) (heA : e ∈ psuAlg B) (hψ : psuPsi h X e = e)
    (a : psuAlg B) :
    psuPsi h X ((a : Matrix (Fin n) (Fin n) K) * e) =
      psuPsi h X (a : Matrix (Fin n) (Fin n) K) * e := by
  rw [psuPsi_mul h X (a : Matrix (Fin n) (Fin n) K) e, hψ]
  exact psuC2dS_comm B e heA (psuPsi h X (a : Matrix (Fin n) (Fin n) K))
    (psuGraph_star_mem S a a.2).2

private lemma psuCKC_tau_ne {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (e : Matrix (Fin n) (Fin n) K) (heA : e ∈ psuAlg B) (hψ : psuPsi h X e = e)
    (hnt : ¬ psuPsiTrivial h X B e)
    {F : Type} [Field F] [Algebra K F]
    [Module F (LinearMap.range e.mulVecLin)] [IsScalarTower K F (LinearMap.range e.mulVecLin)]
    (π : psuAlg B →ₐ[K] F)
    (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K)
    (hbd : PsuBD e π ψ)
    (τ : F ≃+* F)
    (hτπ : ∀ a : psuAlg B, τ (π a) = π ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K),
      (psuGraph_star_mem S a a.2).2⟩) :
    ∃ x, τ x ≠ x := by
  by_contra hcon
  push Not at hcon
  apply hnt
  intro a ha
  let b : psuAlg B := ⟨psuPsi h X a, (psuGraph_star_mem S a ha).2⟩
  let a' : psuAlg B := ⟨a, ha⟩
  have hpe : psuPsi h X (a * e) = psuPsi h X a * e :=
    psuCKCg2_psi_mul_e S e heA hψ a'
  have hπb : π b = π a' :=
    (hτπ a').symm.trans (hcon (π a'))
  have hae : psuPsi h X a * e = a * e := by
    have hsub : (b - a') * e = 0 :=
      (hbd.hker (b - a')).mp (by rw [map_sub, hπb, sub_self])
    have h : (b : Matrix (Fin n) (Fin n) K) * e =
        (a' : Matrix (Fin n) (Fin n) K) * e := by
      simpa [Subalgebra.coe_sub, Matrix.sub_mul, sub_eq_zero] using hsub
    exact h
  rw [hpe, hae]

private lemma psuCKC_tau_eq_id {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (e : Matrix (Fin n) (Fin n) K) (heA : e ∈ psuAlg B) (hψ : psuPsi h X e = e)
    (htriv : psuPsiTrivial h X B e)
    {F : Type} [Field F] [Algebra K F]
    [Module F (LinearMap.range e.mulVecLin)] [IsScalarTower K F (LinearMap.range e.mulVecLin)]
    (π : psuAlg B →ₐ[K] F)
    (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K)
    (hbd : PsuBD e π ψ)
    (τ : F ≃+* F)
    (hτπ : ∀ a : psuAlg B, τ (π a) = π ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K),
      (psuGraph_star_mem S a a.2).2⟩) :
    ∀ x, τ x = x := by
  intro x
  obtain ⟨a, rfl⟩ := hbd.hπ x
  rw [hτπ a]
  let b : psuAlg B :=
    ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a a.2).2⟩
  have hae : (b : Matrix (Fin n) (Fin n) K) * e =
      (a : Matrix (Fin n) (Fin n) K) * e :=
    (psuCKCg2_psi_mul_e S e heA hψ a).symm.trans (htriv a a.2)
  have hsub : (b - a) * e = 0 := by
    have h : (b : Matrix (Fin n) (Fin n) K) * e -
        (a : Matrix (Fin n) (Fin n) K) * e = 0 := by
      rw [hae, sub_self]
    simpa [Subalgebra.coe_sub, Matrix.sub_mul] using h
  have hπ0 : π (b - a) = 0 := (hbd.hker (b - a)).mpr hsub
  rw [map_sub] at hπ0
  exact sub_eq_zero.mp hπ0

private lemma psuCKC_kind3_false {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P)
    (hne : psuDag h e ≠ e) (hψ : psuPsi h X e = e) (hnt : ¬ psuPsiTrivial h X B e)
    {F : Type} [Field F] [Algebra K F] [Finite F] [CharP F 2]
    [Module F (LinearMap.range e.mulVecLin)] [IsScalarTower K F (LinearMap.range e.mulVecLin)]
    (π : psuAlg B →ₐ[K] F)
    (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K)
    (hbd : PsuBD e π ψ)
    (hk1 : Module.finrank F (LinearMap.range e.mulVecLin) ≠ 1) :
    False := by
  have heA : e ∈ psuAlg B := ((hP.1 e).mp he).1
  have hk : 2 ≤ Module.finrank F (LinearMap.range e.mulVecLin) := by
    have hne := hk1
    have hpos := hbd.hpos
    omega
  obtain ⟨τ, H, hττ, hτK, hτπ, hHaddL, hHaddR, hHsmulL, hHsmulR, hHherm, hHnd,
    _hHtrace, hiso⟩ := psuCKC_form_transfer S P hP e he hne hψ π ψ hbd hk
  have hneτ : ∃ x, τ x ≠ x := psuCKC_tau_ne S e heA hψ hnt π ψ hbd τ hτπ
  have hτU : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution τ :=
    psuC2dS_isUnitaryInvolution τ hττ hneτ
  haveI : Module.Finite F (LinearMap.range e.mulVecLin) :=
    Module.Finite.of_restrictScalars_finite K F (LinearMap.range e.mulVecLin)
  haveI : Nontrivial (LinearMap.range e.mulVecLin) :=
    Module.nontrivial_of_finrank_pos (R := F) (by omega)
  obtain ⟨v0, hv0⟩ := exists_anisotropic_of_hermitian τ hτU.exists_ne H hHherm hHaddL hHsmulL
    hHaddR hHsmulR hHnd
  obtain ⟨t, htdet, htnot⟩ := exists_transvection_not_isometry H hk hHaddR hHsmulR ⟨v0, hv0⟩
  exact htnot (hiso t htdet)

private lemma psuCKC_kind2_rank {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P)
    (hne : psuDag h e ≠ e) (hψ : psuPsi h X e = e) (htriv : psuPsiTrivial h X B e)
    {F : Type} [Field F] [Algebra K F] [Finite F] [CharP F 2]
    [Module F (LinearMap.range e.mulVecLin)] [IsScalarTower K F (LinearMap.range e.mulVecLin)]
    (π : psuAlg B →ₐ[K] F)
    (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K)
    (hbd : PsuBD e π ψ)
    (hk1 : Module.finrank F (LinearMap.range e.mulVecLin) ≠ 1) :
    Module.finrank F (LinearMap.range e.mulVecLin) = 2 := by
  have heA : e ∈ psuAlg B := ((hP.1 e).mp he).1
  have hk : 2 ≤ Module.finrank F (LinearMap.range e.mulVecLin) := by
    have hne := hk1
    have hpos := hbd.hpos
    omega
  obtain ⟨τ, H, _hττ, _hτK, hτπ, hHaddL, hHaddR, hHsmulL, hHsmulR, _hHherm, hHnd,
    _hHtrace, hiso⟩ := psuCKC_form_transfer S P hP e he hne hψ π ψ hbd hk
  have hτid : ∀ x, τ x = x := psuCKC_tau_eq_id S e heA hψ htriv π ψ hbd τ hτπ
  haveI : Module.Finite F (LinearMap.range e.mulVecLin) :=
    Module.Finite.of_restrictScalars_finite K F (LinearMap.range e.mulVecLin)
  have hsmulL_id : ∀ (a : F) x y, H (a • x) y = a * H x y :=
    fun a x y => by rw [hHsmulL a x y, hτid a]
  have hle2 : Module.finrank F (LinearMap.range e.mulVecLin) ≤ 2 := by
    by_contra hle
    have h3 : 3 ≤ Module.finrank F (LinearMap.range e.mulVecLin) := by omega
    by_cases haniso : ∃ v, H v v ≠ 0
    · obtain ⟨v0, hv0⟩ := haniso
      obtain ⟨t, htdet, htnot⟩ := exists_transvection_not_isometry H hk hHaddR hHsmulR
        ⟨v0, hv0⟩
      exact htnot (hiso t htdet)
    · have halt : ∀ v, H v v = 0 := fun v => not_not.mp (fun hv => haniso ⟨v, hv⟩)
      obtain ⟨t, htdet, htnot⟩ := exists_transvection_not_isometry_of_alternating H h3 hHaddL
        hHaddR hHsmulR halt hHnd
      exact htnot (hiso t htdet)
  omega

private theorem psuCK_kind_C2_core {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P)
    (hne : psuDag h e ≠ e) (hψ : psuPsi h X e = e) (hnt : ¬ psuPsiTrivial h X B e)
    {F : Type} [Field F] [Algebra K F] [Finite F] [CharP F 2]
    [Module F (LinearMap.range e.mulVecLin)] [IsScalarTower K F (LinearMap.range e.mulVecLin)]
    (π : psuAlg B →ₐ[K] F)
    (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K)
    (hbd : PsuBD e π ψ) :
    Group.IsSolvable ↥(psuBlock h B e) := by
  by_cases hk1 : Module.finrank F (LinearMap.range e.mulVecLin) = 1
  · exact psuK_solvable_of_finrank_one S P hP e he π ψ hbd hk1
  · exact (psuCKC_kind3_false S P hP e he hne hψ hnt π ψ hbd hk1).elim

private theorem psuCK_kind_C1_core {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P)
    (hne : psuDag h e ≠ e) (hψ : psuPsi h X e = e) (htriv : psuPsiTrivial h X B e)
    (hns : ¬ Group.IsSolvable ↥(psuBlock h B e))
    {F : Type} [Field F] [Algebra K F] [Finite F] [CharP F 2]
    [Module F (LinearMap.range e.mulVecLin)] [IsScalarTower K F (LinearMap.range e.mulVecLin)]
    (π : psuAlg B →ₐ[K] F)
    (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K)
    (hbd : PsuBD e π ψ) :
    Module.finrank F (LinearMap.range e.mulVecLin) = 2 := by
  by_cases hk1 : Module.finrank F (LinearMap.range e.mulVecLin) = 1
  · exact absurd (psuK_solvable_of_finrank_one S P hP e he π ψ hbd hk1) hns
  · exact psuCKC_kind2_rank S P hP e he hne hψ htriv π ψ hbd hk1

private lemma psuCKAsg1_isCyclic_ringAut (F : Type) [Field F] [Finite F] :
    IsCyclic (F ≃+* F) := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨p, hpchar, n, hp, _hcard⟩ := FiniteField.card' F
  let : Fact p.Prime := ⟨hp⟩
  let : CharP F p := hpchar
  let : Algebra (ZMod p) F := ZMod.algebra F p
  let e : (F ≃+* F) ≃* (F ≃ₐ[ZMod p] F) := {
    toFun := fun σ =>
      AlgEquiv.ofRingEquiv (f := σ) (by
        intro x
        have h :
            (σ.toRingHom.comp (algebraMap (ZMod p) F) : ZMod p →+* F) =
              algebraMap (ZMod p) F := RingHom.ext_zmod _ _
        exact DFunLike.congr_fun h x)
    invFun := fun σ => σ.toRingEquiv
    left_inv := by intro σ; ext x; rfl
    right_inv := by intro σ; ext x; rfl
    map_mul' := by intro σ τ; ext x; rfl }
  exact e.isCyclic.mpr inferInstance

private lemma psuCKAs_involutions_eq {F : Type} [Field F] [Finite F]
    (α β : F ≃+* F) (hα : ∀ x, α (α x) = x) (hβ : ∀ x, β (β x) = x)
    (hαne : ∃ x, α x ≠ x) (hβne : ∃ x, β x ≠ x) : α = β := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Finite (F ≃+* F) :=
    Finite.of_injective (fun σ : F ≃+* F => (σ : F → F)) DFunLike.coe_injective
  haveI : Fintype (F ≃+* F) := Fintype.ofFinite _
  haveI : IsCyclic (F ≃+* F) := psuCKAsg1_isCyclic_ringAut F
  have hα2 : α ^ 2 = 1 := by
    rw [pow_two]
    ext x
    exact hα x
  have hβ2 : β ^ 2 = 1 := by
    rw [pow_two]
    ext x
    exact hβ x
  have hα1 : α ≠ 1 := by
    rintro h
    obtain ⟨x, hx⟩ := hαne
    exact hx (by rw [h]; rfl)
  have hβ1 : β ≠ 1 := by
    rintro h
    obtain ⟨x, hx⟩ := hβne
    exact hx (by rw [h]; rfl)
  by_contra hne
  have hcard := IsCyclic.card_pow_eq_one_le (α := F ≃+* F) (n := 2) (by norm_num)
  have hsub : ({1, α, β} : Finset (F ≃+* F)) ⊆
      Finset.univ.filter (fun a => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · simp
    · simpa using hα2
    · simpa using hβ2
  have h3 : ({1, α, β} : Finset (F ≃+* F)).card = 3 :=
    Finset.card_eq_three.mpr ⟨1, α, β, hα1.symm, hβ1.symm, hne, rfl⟩
  have := Finset.card_le_card hsub
  omega

private lemma psuCKAs_exists_mu {F : Type} [Field F]
    (τ : F ≃+* F) (hτ : ∀ x, τ (τ x) = x) (hτne : ∃ x, τ x ≠ x) :
    ∃ μ : F, τ μ * μ = 1 ∧ μ ≠ 1 := by
  obtain ⟨x, hx⟩ := hτne
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (map_zero τ)
  have hτx : τ x ≠ 0 := fun h0 => hx0 (τ.injective (h0.trans (map_zero τ).symm))
  refine ⟨x / τ x, ?_, ?_⟩
  · rw [map_div₀, hτ x]
    field_simp
  · intro hμ
    apply hx
    have hmul : x = τ x := by
      have := congrArg (fun y : F => y * τ x) hμ
      rwa [div_mul_cancel₀ _ hτx, one_mul] at this
    exact hmul.symm

private lemma psuCKAsg2_theta_algebraMap {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (c : K) :
    psuTheta h X ((algebraMap K (psuAlg B) c) : Matrix (Fin n) (Fin n) K) =
      (h.bar c) • (1 : Matrix (Fin n) (Fin n) K) := by
  simp only [Algebra.algebraMap_eq_smul_one, Subalgebra.coe_smul, Subalgebra.coe_one,
    psuTheta_smul, psuTheta_one]

private lemma psuCKAsg2_sVmem {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {X : GL (Fin n) K}
    {e : Matrix (Fin n) (Fin n) K} (hθe : psuTheta h X e = e)
    {w : Fin n → K} (hw : w ∈ LinearMap.range e.mulVecLin) :
    (X : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => h.bar (w i)) ∈
      LinearMap.range e.mulVecLin := by
  obtain ⟨v, hv⟩ := hw
  rw [← hv, Matrix.mulVecLin_apply, psuC2dS_bar_mulVec h e v]
  have hXinv : ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (X : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul]; simp
  have hθe' : (X : Matrix (Fin n) (Fin n) K) * e.map h.bar *
      ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = e := by
    simpa only [psuTheta] using hθe
  have hXe : (X : Matrix (Fin n) (Fin n) K) * e.map h.bar =
      e * (X : Matrix (Fin n) (Fin n) K) := by
    calc (X : Matrix (Fin n) (Fin n) K) * e.map h.bar
        = (X : Matrix (Fin n) (Fin n) K) * e.map h.bar * 1 := by rw [Matrix.mul_one]
      _ = (X : Matrix (Fin n) (Fin n) K) * e.map h.bar *
            (((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              (X : Matrix (Fin n) (Fin n) K)) := by rw [hXinv]
      _ = ((X : Matrix (Fin n) (Fin n) K) * e.map h.bar *
            ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
              (X : Matrix (Fin n) (Fin n) K) := by noncomm_ring
      _ = e * (X : Matrix (Fin n) (Fin n) K) := by rw [hθe']
  rw [Matrix.mulVec_mulVec, hXe, ← Matrix.mulVec_mulVec]
  exact ⟨(X : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => h.bar (v i)),
    by rw [Matrix.mulVecLin_apply]⟩

private lemma psuCKAs_theta_mem_alg {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    {a : Matrix (Fin n) (Fin n) K} (ha : a ∈ psuAlg B) :
    psuTheta h X a ∈ psuAlg B := by
  refine Algebra.adjoin_induction (p := fun x _ => psuTheta h X x ∈ psuAlg B)
    ?_ ?_ ?_ ?_ ha
  · rintro x ⟨s, hs, rfl⟩
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    have hB : (B : Matrix (Fin n) (Fin n) K) ∈ psuAlg B :=
      Algebra.subset_adjoin ⟨B, rfl, rfl⟩
    obtain ⟨c, hc⟩ := S.theta_B
    rw [hc]
    exact Subalgebra.smul_mem _ hB c
  · intro r
    rw [Algebra.algebraMap_eq_smul_one, psuTheta_smul, psuTheta_one]
    exact Subalgebra.smul_mem _ (Subalgebra.one_mem _) (h.bar r)
  · intro x y hx hy hpx hpy
    rw [psuTheta_add]
    exact Subalgebra.add_mem _ hpx hpy
  · intro x y hx hy hpx hpy
    rw [psuTheta_mul]
    exact Subalgebra.mul_mem _ hpx hpy

private lemma psuCKAs_thetaBar {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    {e : Matrix (Fin n) (Fin n) K} (hde : psuDag h e = e) (hψ : psuPsi h X e = e)
    {F : Type} [Field F] [Algebra K F] (π : psuAlg B →ₐ[K] F) (hπ : Function.Surjective π)
    (hker : ∀ a : psuAlg B, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e = 0) :
    ∃ θb : F ≃+* F,
      (∀ x, θb (θb x) = x) ∧
      (∀ c : K, θb (algebraMap K F c) = algebraMap K F (h.bar c)) ∧
      (∃ x, θb x ≠ x) ∧
      (∀ a : psuAlg B, θb (π a) = π ⟨psuTheta h X (a : Matrix (Fin n) (Fin n) K),
        psuCKAs_theta_mem_alg (a := (a : Matrix (Fin n) (Fin n) K)) S a.2⟩) := by
  classical
  have hθe : psuTheta h X e = e := by
    have h := hψ
    rw [psuPsi, hde] at h
    exact h
  have hθ0 : psuTheta h X (0 : Matrix (Fin n) (Fin n) K) = 0 := by
    simp [psuTheta]
  let ρ : psuAlg B →+* F :=
    { toFun := fun a => π ⟨psuTheta h X (a : Matrix (Fin n) (Fin n) K),
        psuCKAs_theta_mem_alg (a := (a : Matrix (Fin n) (Fin n) K)) S a.2⟩
      map_one' := by
        have h1 : (⟨psuTheta h X ((1 : psuAlg B) : Matrix (Fin n) (Fin n) K),
            psuCKAs_theta_mem_alg (a := ((1 : psuAlg B) : Matrix (Fin n) (Fin n) K)) S
              (1 : psuAlg B).2⟩ : psuAlg B) = 1 :=
          Subtype.ext (psuTheta_one h X)
        rw [h1, map_one]
      map_mul' := by
        intro a b
        have h1 : (⟨psuTheta h X ((a * b : psuAlg B) : Matrix (Fin n) (Fin n) K),
            psuCKAs_theta_mem_alg (a := ((a * b : psuAlg B) : Matrix (Fin n) (Fin n) K)) S
              (a * b).2⟩ : psuAlg B) =
            ⟨psuTheta h X (a : Matrix (Fin n) (Fin n) K),
              psuCKAs_theta_mem_alg (a := (a : Matrix (Fin n) (Fin n) K)) S a.2⟩ *
            ⟨psuTheta h X (b : Matrix (Fin n) (Fin n) K),
              psuCKAs_theta_mem_alg (a := (b : Matrix (Fin n) (Fin n) K)) S b.2⟩ :=
          Subtype.ext (psuTheta_mul h X (a : Matrix (Fin n) (Fin n) K)
            (b : Matrix (Fin n) (Fin n) K))
        rw [h1, map_mul]
      map_zero' := by
        have h1 : (⟨psuTheta h X ((0 : psuAlg B) : Matrix (Fin n) (Fin n) K),
            psuCKAs_theta_mem_alg (a := ((0 : psuAlg B) : Matrix (Fin n) (Fin n) K)) S
              (0 : psuAlg B).2⟩ : psuAlg B) = 0 :=
          Subtype.ext hθ0
        rw [h1, map_zero]
      map_add' := by
        intro a b
        have h1 : (⟨psuTheta h X ((a + b : psuAlg B) : Matrix (Fin n) (Fin n) K),
            psuCKAs_theta_mem_alg (a := ((a + b : psuAlg B) : Matrix (Fin n) (Fin n) K)) S
              (a + b).2⟩ : psuAlg B) =
            ⟨psuTheta h X (a : Matrix (Fin n) (Fin n) K),
              psuCKAs_theta_mem_alg (a := (a : Matrix (Fin n) (Fin n) K)) S a.2⟩ +
            ⟨psuTheta h X (b : Matrix (Fin n) (Fin n) K),
              psuCKAs_theta_mem_alg (a := (b : Matrix (Fin n) (Fin n) K)) S b.2⟩ :=
          Subtype.ext (psuTheta_add h X (a : Matrix (Fin n) (Fin n) K)
            (b : Matrix (Fin n) (Fin n) K))
        rw [h1, map_add] }
  have hkerρ : ∀ a : psuAlg B, π.toRingHom a = 0 → ρ a = 0 := by
    intro a h0
    have hae : (a : Matrix (Fin n) (Fin n) K) * e = 0 := (hker a).mp h0
    have h1 : psuTheta h X ((a : Matrix (Fin n) (Fin n) K) * e) = 0 := by
      rw [hae, hθ0]
    rw [psuTheta_mul, hθe] at h1
    exact (hker ⟨psuTheta h X (a : Matrix (Fin n) (Fin n) K),
      psuCKAs_theta_mem_alg (a := (a : Matrix (Fin n) (Fin n) K)) S a.2⟩).mpr h1
  obtain ⟨φ, hφ⟩ := psuC2dS_factor π.toRingHom hπ ρ hkerρ
  have hφ' : ∀ a : psuAlg B, φ (π a) =
      π ⟨psuTheta h X (a : Matrix (Fin n) (Fin n) K),
        psuCKAs_theta_mem_alg (a := (a : Matrix (Fin n) (Fin n) K)) S a.2⟩ :=
    fun a => hφ a
  have hφφa : ∀ a : psuAlg B, φ (φ (π a)) = π a := by
    intro a
    rw [hφ' a, hφ' ⟨psuTheta h X (a : Matrix (Fin n) (Fin n) K),
      psuCKAs_theta_mem_alg (a := (a : Matrix (Fin n) (Fin n) K)) S a.2⟩]
    congr 1
    exact Subtype.ext (psuTheta_theta h X S.X_sq (a : Matrix (Fin n) (Fin n) K))
  have hφφ : ∀ x : F, φ (φ x) = x := by
    intro x
    obtain ⟨a, rfl⟩ := hπ x
    exact hφφa a
  have hθbK : ∀ c : K, (RingEquiv.ofBijective φ (Function.Involutive.bijective hφφ))
      (algebraMap K F c) = algebraMap K F (h.bar c) := by
    intro c
    rw [RingEquiv.ofBijective_apply, ← AlgHom.commutes π c,
      hφ' (algebraMap K (psuAlg B) c), ← AlgHom.commutes π (h.bar c)]
    congr 1
    apply Subtype.ext
    change psuTheta h X ((algebraMap K (psuAlg B) c) : Matrix (Fin n) (Fin n) K) =
      ((algebraMap K (psuAlg B) (h.bar c)) : Matrix (Fin n) (Fin n) K)
    rw [psuCKAsg2_theta_algebraMap c, Algebra.algebraMap_eq_smul_one,
      Subalgebra.coe_smul, Subalgebra.coe_one]
  have hθbπ : ∀ a : psuAlg B,
      (RingEquiv.ofBijective φ (Function.Involutive.bijective hφφ)) (π a) =
        π ⟨psuTheta h X (a : Matrix (Fin n) (Fin n) K),
          psuCKAs_theta_mem_alg (a := (a : Matrix (Fin n) (Fin n) K)) S a.2⟩ := by
    intro a
    rw [RingEquiv.ofBijective_apply]
    exact hφ' a
  refine ⟨RingEquiv.ofBijective φ (Function.Involutive.bijective hφφ), ?_, hθbK, ?_, hθbπ⟩
  · intro x
    simpa only [RingEquiv.ofBijective_apply] using hφφ x
  · obtain ⟨c, hc⟩ := h.exists_bar_ne
    refine ⟨algebraMap K F c, fun hh => hc ((algebraMap K F).injective ?_)⟩
    rw [← hθbK c]
    exact hh

private lemma psuCKAs_thetaBar_eq_tau {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    {e : Matrix (Fin n) (Fin n) K} (hde : psuDag h e = e) (hψ : psuPsi h X e = e)
    {F : Type} [Field F] [Finite F] [Algebra K F] (π : psuAlg B →ₐ[K] F)
    (hπ : Function.Surjective π)
    (hker : ∀ a : psuAlg B, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e = 0)
    (τ : F ≃+* F) (hττ : ∀ x, τ (τ x) = x) (hτne : ∃ x, τ x ≠ x) :
    ∀ a : psuAlg B, τ (π a) = π ⟨psuTheta h X (a : Matrix (Fin n) (Fin n) K),
      psuCKAs_theta_mem_alg (a := (a : Matrix (Fin n) (Fin n) K)) S a.2⟩ := by
  obtain ⟨θb, hθb_inv, _hθbK, hθb_ne, hθb_π⟩ :=
    psuCKAs_thetaBar S hde hψ π hπ hker
  have heq : θb = τ := psuCKAs_involutions_eq θb τ hθb_inv hττ hθb_ne hτne
  intro a
  rw [← heq]
  exact hθb_π a

private lemma psuCKAs_sV {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    {e : Matrix (Fin n) (Fin n) K} (hde : psuDag h e = e) (hψ : psuPsi h X e = e)
    {F : Type} [Field F] [Algebra K F]
    [Module F (LinearMap.range e.mulVecLin)] [IsScalarTower K F (LinearMap.range e.mulVecLin)]
    (π : psuAlg B →ₐ[K] F)
    (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K)
    (hbd : PsuBD e π ψ) (τ : F ≃+* F)
    (hθbar : ∀ a : psuAlg B, τ (π a) = π ⟨psuTheta h X (a : Matrix (Fin n) (Fin n) K),
      psuCKAs_theta_mem_alg (a := (a : Matrix (Fin n) (Fin n) K)) S a.2⟩) :
    ∃ sV : LinearMap.range e.mulVecLin → LinearMap.range e.mulVecLin,
      (∀ w, (sV w : Fin n → K) = (X : Matrix (Fin n) (Fin n) K) *ᵥ
        (fun i => h.bar ((w : Fin n → K) i))) ∧
      (∀ x y, sV (x + y) = sV x + sV y) ∧
      (∀ (a : F) (x : LinearMap.range e.mulVecLin), sV (a • x) = τ a • sV x) ∧
      (∀ x, sV (sV x) = x) := by
  classical
  have hθe : psuTheta h X e = e := by
    have h := hψ
    rw [psuPsi, hde] at h
    exact h
  let sV : LinearMap.range e.mulVecLin → LinearMap.range e.mulVecLin :=
    fun w => ⟨(X : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => h.bar ((w : Fin n → K) i)),
      psuCKAsg2_sVmem hθe w.2⟩
  have hsV : ∀ w, ((sV w : LinearMap.range e.mulVecLin) : Fin n → K) =
      (X : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => h.bar ((w : Fin n → K) i)) :=
    fun w => rfl
  refine ⟨sV, hsV, ?_, ?_, ?_⟩
  · intro x y
    apply Subtype.ext
    have hsum : ((sV x + sV y : LinearMap.range e.mulVecLin) : Fin n → K) =
        (sV x : Fin n → K) + (sV y : Fin n → K) := rfl
    have hxy : ((x + y : LinearMap.range e.mulVecLin) : Fin n → K) =
        (x : Fin n → K) + (y : Fin n → K) := rfl
    rw [hsum, hsV, hxy]
    rw [show (fun i => h.bar (((x : Fin n → K) + (y : Fin n → K)) i)) =
        (fun i => h.bar ((x : Fin n → K) i)) +
          (fun i => h.bar ((y : Fin n → K) i)) from by
          funext i; exact map_add h.bar _ _]
    rw [Matrix.mulVec_add]
  · intro a x
    obtain ⟨a', ha'⟩ := hbd.hπ a
    apply Subtype.ext
    have hL : ((a • x : LinearMap.range e.mulVecLin) : Fin n → K) =
        (a' : Matrix (Fin n) (Fin n) K) *ᵥ (x : Fin n → K) := by
      rw [← ha']
      exact hbd.hact a' x
    have hR : ((τ a • sV x : LinearMap.range e.mulVecLin) : Fin n → K) =
        psuTheta h X (a' : Matrix (Fin n) (Fin n) K) *ᵥ
          ((sV x : LinearMap.range e.mulVecLin) : Fin n → K) := by
      rw [← ha', hθbar a']
      exact hbd.hact ⟨psuTheta h X (a' : Matrix (Fin n) (Fin n) K),
        psuCKAs_theta_mem_alg (a := (a' : Matrix (Fin n) (Fin n) K)) S a'.2⟩ (sV x)
    have hXinv : ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (X : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul]; simp
    have hθX : psuTheta h X (a' : Matrix (Fin n) (Fin n) K) *
        (X : Matrix (Fin n) (Fin n) K) =
        (X : Matrix (Fin n) (Fin n) K) * (a' : Matrix (Fin n) (Fin n) K).map h.bar := by
      rw [psuTheta]
      calc (X : Matrix (Fin n) (Fin n) K) * (a' : Matrix (Fin n) (Fin n) K).map h.bar *
            ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (X : Matrix (Fin n) (Fin n) K)
          = (X : Matrix (Fin n) (Fin n) K) * (a' : Matrix (Fin n) (Fin n) K).map h.bar *
              (((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
                (X : Matrix (Fin n) (Fin n) K)) := by noncomm_ring
        _ = (X : Matrix (Fin n) (Fin n) K) *
              (a' : Matrix (Fin n) (Fin n) K).map h.bar := by
              rw [hXinv, Matrix.mul_one]
    rw [hsV, hL, hR, hsV, psuC2dS_bar_mulVec h (a' : Matrix (Fin n) (Fin n) K)
      (x : Fin n → K)]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hθX]
  · intro x
    apply Subtype.ext
    simp only [hsV]
    rw [psuC2dS_bar_mulVec h X (fun i => h.bar ((x : Fin n → K) i))]
    rw [show (fun i => h.bar (h.bar ((x : Fin n → K) i))) = (x : Fin n → K) from
      funext fun i => h.bar_bar ((x : Fin n → K) i)]
    rw [Matrix.mulVec_mulVec, S.X_sq, Matrix.one_mulVec]

private lemma psuCKAsg3_map_mulVec {k : ℕ} {F : Type} [Field F] (τ : F →+* F)
    (M : Matrix (Fin k) (Fin k) F) (y : Fin k → F) :
    (fun i => τ ((M *ᵥ y) i)) = M.map τ *ᵥ (fun i => τ (y i)) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

private lemma psuCKAsg3_perfect_le_commutator {G : Type} [Group G] (H : Subgroup G)
    [Group.IsPerfect ↥H] : H ≤ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ := by
  have htop : commutator ↥H = ⊤ := Group.IsPerfect.commutator_eq_top
  have hmap : Subgroup.map H.subtype (⊤ : Subgroup ↥H) = H := by
    ext x; simp [Subgroup.mem_map]
  calc H = Subgroup.map H.subtype (⊤ : Subgroup ↥H) := hmap.symm
    _ = Subgroup.map H.subtype (commutator ↥H) := by rw [htop]
    _ = ⁅H, H⁆ := Subgroup.map_subtype_commutator H
    _ ≤ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ := Subgroup.commutator_mono le_top le_top

private lemma psuCKAsg3_permMatrix_mem {k : ℕ} {F : Type} [Field F] [CharP F 2]
    (τ : F ≃+* F) (ρ : Equiv.Perm (Fin k)) :
    ∃ A : SUid τ k, ((A : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) = ρ.permMatrix F := by
  classical
  let P : Matrix (Fin k) (Fin k) F := ρ.permMatrix F
  have hPentry : ∀ i j, P i j = if ρ i = j then (1 : F) else 0 := by
    intro i j
    simp [P, Equiv.Perm.permMatrix, Matrix.submatrix_apply, Matrix.one_apply]
  have hmap : P.map τ = P := by
    ext i j
    rw [Matrix.map_apply, hPentry i j]
    by_cases hij : ρ i = j <;> simp [hij, map_one, map_zero]
  have hPdet : P.det = 1 := by
    rw [show P.det = (ρ.permMatrix F).det from rfl, Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign ρ) with h | h
    · rw [h]; simp
    · rw [h]
      simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, CharTwo.neg_eq]
  have hunit : conjTr τ P * P = 1 := by
    rw [conjTr, hmap, Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul ρ ρ⁻¹,
      mul_inv_cancel, Matrix.permMatrix_one]
  have hPd : P.det ≠ 0 := by rw [hPdet]; exact one_ne_zero
  let B : GL (Fin k) F := Matrix.GeneralLinearGroup.mkOfDetNeZero P hPd
  have hBdet : (B : Matrix (Fin k) (Fin k) F).det = 1 := by
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hPdet]
  have hBunit : conjTr τ (B : Matrix (Fin k) (Fin k) F) *
      (B : Matrix (Fin k) (Fin k) F) = 1 := by
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hunit]
  refine ⟨⟨B, mem_SUid.mpr ⟨hBdet, hBunit⟩⟩, ?_⟩
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]

private lemma psuCKAsg3_diag_mem {k : ℕ} {F : Type} [Field F]
    (τ : F ≃+* F) (lam : Fin k → F) (hlam : ∀ i, τ (lam i) * lam i = 1)
    (hprod : ∏ i, lam i = 1) :
    ∃ A : SUid τ k, ((A : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) =
      Matrix.diagonal lam := by
  classical
  let D : Matrix (Fin k) (Fin k) F := Matrix.diagonal lam
  have hDdet : D.det = 1 := by
    rw [show D.det = (Matrix.diagonal lam).det from rfl, Matrix.det_diagonal, hprod]
  have hunit : conjTr τ D * D = 1 := by
    rw [conjTr, Matrix.diagonal_map (map_zero τ), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal,
      show (fun i => τ (lam i) * lam i) = (fun _ => (1 : F)) from funext hlam,
      Matrix.diagonal_one]
  have hDd : D.det ≠ 0 := by rw [hDdet]; exact one_ne_zero
  let B : GL (Fin k) F := Matrix.GeneralLinearGroup.mkOfDetNeZero D hDd
  have hBdet : (B : Matrix (Fin k) (Fin k) F).det = 1 := by
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hDdet]
  have hBunit : conjTr τ (B : Matrix (Fin k) (Fin k) F) *
      (B : Matrix (Fin k) (Fin k) F) = 1 := by
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hunit]
  refine ⟨⟨B, mem_SUid.mpr ⟨hBdet, hBunit⟩⟩, ?_⟩
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]

private lemma psuCKAsg3_map_mulVecEquiv {k : ℕ} {F : Type} [Field F] (τ : F ≃+* F)
    (M : Matrix (Fin k) (Fin k) F) (y : Fin k → F) :
    (fun i => τ ((M *ᵥ y) i)) = M.map τ *ᵥ (fun i => τ (y i)) := by
  simpa using psuCKAsg3_map_mulVec (τ : F →+* F) M y

private lemma psuCKAs_comm_gA {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    {e : Matrix (Fin n) (Fin n) K} (hee : e * e = e) (hde : psuDag h e = e)
    {F : Type} [Field F] [Algebra K F]
    [Module F (LinearMap.range e.mulVecLin)]
    (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K)
    (hψw : ∀ (g : LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin)
      (w : LinearMap.range e.mulVecLin),
      (ψ g : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) =
        ((g w : LinearMap.range e.mulVecLin) : Fin n → K))
    (hψfix : ∀ g, (ψ g : Matrix (Fin n) (Fin n) K) * (1 - e) = 1 - e)
    (hψB : ∀ g, (ψ g : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * (ψ g : Matrix (Fin n) (Fin n) K))
    (τ : F ≃+* F) (H : LinearMap.range e.mulVecLin → LinearMap.range e.mulVecLin → F)
    (hHaddL : ∀ x y z, H (x + y) z = H x z + H y z)
    (hHaddR : ∀ x y z, H x (y + z) = H x y + H x z)
    (hHsmulL : ∀ (a : F) x y, H (a • x) y = τ a * H x y)
    (hHsmulR : ∀ (a : F) x y, H x (a • y) = a * H x y)
    (htr : ∀ x y : LinearMap.range e.mulVecLin,
      psuC2dS_hf h (x : Fin n → K) (y : Fin n → K) = Algebra.trace K F (H x y))
    (k : ℕ) (b : Module.Basis (Fin k) F (LinearMap.range e.mulVecLin))
    (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0)
    (hperf : Group.IsPerfect ↥(SUid τ k))
    (sV : LinearMap.range e.mulVecLin → LinearMap.range e.mulVecLin)
    (hsVcoe : ∀ w, (sV w : Fin n → K) = (X : Matrix (Fin n) (Fin n) K) *ᵥ
      (fun i => h.bar ((w : Fin n → K) i))) :
    ∀ (A : SUid τ k) (w : LinearMap.range e.mulVecLin),
      sV (psuC2dE_gA b (A : GL (Fin k) F) w) = psuC2dE_gA b (A : GL (Fin k) F) (sV w) := by
  intro A w
  haveI : Group.IsPerfect ↥(SUid τ k) := hperf
  let φ : SUid τ k →* ↥(psuBlock h B e) :=
    psuC2dE_phi hee hde ψ hψw hψfix hψB τ H hHaddL hHaddR hHsmulL hHsmulR htr k b hb hperf
  haveI : Group.IsPerfect ↥φ.range := Group.IsPerfect.range φ
  have hle : φ.range ≤ ⁅(⊤ : Subgroup ↥(psuBlock h B e)), ⊤⁆ :=
    psuCKAsg3_perfect_le_commutator φ.range
  have hmemCom : φ A ∈ ⁅(⊤ : Subgroup ↥(psuBlock h B e)), ⊤⁆ := hle ⟨A, rfl⟩
  have hmemXJ : (((φ A : ↥(psuBlock h B e)) : AutPSU.XJ h n)) ∈
      ⁅psuBlock h B e, psuBlock h B e⁆ := by
    have h2 : (psuBlock h B e).subtype (φ A) ∈
        Subgroup.map (psuBlock h B e).subtype (commutator ↥(psuBlock h B e)) :=
      Subgroup.mem_map.mpr ⟨φ A, hmemCom, rfl⟩
    rw [Subgroup.map_subtype_commutator (psuBlock h B e)] at h2
    simpa using h2
  have hfix := psuK_theta_fixed_of_commutator S e
    (((φ A : ↥(psuBlock h B e)) : AutPSU.XJ h n)) hmemXJ
  let g := psuC2dE_gA b (A : GL (Fin k) F)
  have hfixY : psuTheta h X ((ψ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((ψ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have h0 : psuTheta h X (psuC2dE_psiA b ψ A : Matrix (Fin n) (Fin n) K) =
        (psuC2dE_psiA b ψ A : Matrix (Fin n) (Fin n) K) := hfix
    rw [psuC2dE_psiA_apply] at h0
    simpa only [g] using h0
  let Xm : Matrix (Fin n) (Fin n) K := (X : GL (Fin n) K)
  let Xim : Matrix (Fin n) (Fin n) K := ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  let Ym : Matrix (Fin n) (Fin n) K := ((ψ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have hfixYm : psuTheta h X Ym = Ym := hfixY
  have hXinvX : Xim * Xm = 1 := by
    dsimp only [Xim, Xm]
    rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one]
  have hmul : Xm * Ym.map h.bar = Ym * Xm := by
    have hθ := hfixYm
    rw [psuTheta] at hθ
    have h1 : (Xm * Ym.map h.bar * Xim) * Xm = Xm * Ym.map h.bar := by
      simp only [Matrix.mul_assoc, hXinvX, Matrix.mul_one]
    calc Xm * Ym.map h.bar = (Xm * Ym.map h.bar * Xim) * Xm := h1.symm
      _ = Ym * Xm := by rw [hθ]
  have hvec : ∀ z : Fin n → K, Xm *ᵥ (Ym.map h.bar *ᵥ z) = Ym *ᵥ (Xm *ᵥ z) := by
    intro z
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) K => M *ᵥ z) hmul
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at h
    exact h
  apply Subtype.ext
  have hYw : (((g w : LinearMap.range e.mulVecLin)) : Fin n → K) =
      Ym *ᵥ (w : Fin n → K) := (hψw g w).symm
  rw [hsVcoe (g w), hYw, psuCKAsg3_map_mulVec h.bar Ym (w : Fin n → K),
    ← hψw g (sV w), hsVcoe w]
  exact hvec (fun i => h.bar ((w : Fin n → K) i))

private lemma psuCKAs_matrix_data {k : ℕ} {F : Type} [Field F] [CharP F 2]
    {V : Type} [AddCommGroup V] [Module F V]
    (τ : F ≃+* F) (hτ : ∀ x, τ (τ x) = x)
    (b : Module.Basis (Fin k) F V) (sV : V → V)
    (hsVadd : ∀ x y, sV (x + y) = sV x + sV y)
    (hsVsmul : ∀ (a : F) x, sV (a • x) = τ a • sV x)
    (hsVinvol : ∀ x, sV (sV x) = x)
    (hcomm : ∀ (A : SUid τ k) (x : V),
      sV (psuC2dE_gA b (A : GL (Fin k) F) x) = psuC2dE_gA b (A : GL (Fin k) F) (sV x)) :
    ∃ c : Matrix (Fin k) (Fin k) F, c.det ≠ 0 ∧
      (∀ ρ : Equiv.Perm (Fin k), (fun a b => c (ρ a) (ρ b)) = c) ∧
      (∀ lam : Fin k → F, (∀ i, τ (lam i) * lam i = 1) → ∏ i, lam i = 1 →
        c * Matrix.diagonal (fun i => τ (lam i)) = Matrix.diagonal lam * c) := by
  classical
  let c : Matrix (Fin k) (Fin k) F := fun i j => (b.equivFun (sV (b j))) i
  have hcoe : ∀ x : V, b.equivFun (sV x) = c *ᵥ (fun i => τ ((b.equivFun x) i)) := by
    intro x
    let eA : V →+ (Fin k → F) :=
      { toFun := b.equivFun, map_zero' := map_zero b.equivFun, map_add' := map_add b.equivFun }
    let sA : V →+ V :=
      { toFun := sV,
        map_zero' := by
          have h0 := hsVadd 0 0
          rw [add_zero] at h0
          exact add_left_cancel (h0.symm.trans (add_zero _).symm),
        map_add' := hsVadd }
    have hx : x = ∑ j, (b.equivFun x) j • b j := by
      conv_lhs => rw [← LinearEquiv.symm_apply_apply b.equivFun x]
      rw [Module.Basis.equivFun_symm_apply]
    have hsum : sV (∑ j, (b.equivFun x) j • b j) =
        ∑ j, τ ((b.equivFun x) j) • sV (b j) := by
      change sA (∑ j, (b.equivFun x) j • b j) =
        ∑ j, τ ((b.equivFun x) j) • sA (b j)
      rw [map_sum sA]
      exact Finset.sum_congr rfl (fun j _ => hsVsmul _ _)
    have hbj : ∀ j, b.equivFun (sV (b j)) = (fun i => c i j) := by
      intro j; funext i; rfl
    calc b.equivFun (sV x)
        = b.equivFun (sV (∑ j, (b.equivFun x) j • b j)) := by conv_lhs => rw [hx]
      _ = b.equivFun (∑ j, τ ((b.equivFun x) j) • sV (b j)) := by rw [hsum]
      _ = ∑ j, τ ((b.equivFun x) j) • b.equivFun (sV (b j)) := by
            change eA (∑ j, τ ((b.equivFun x) j) • sV (b j)) =
              ∑ j, τ ((b.equivFun x) j) • eA (sV (b j))
            rw [map_sum eA]
            exact Finset.sum_congr rfl (fun j _ => map_smul b.equivFun _ _)
      _ = ∑ j, τ ((b.equivFun x) j) • (fun i => c i j) := by
            exact Finset.sum_congr rfl (fun j _ => by rw [hbj j])
      _ = c *ᵥ (fun i => τ ((b.equivFun x) i)) := by
            ext i
            simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Finset.sum_apply,
              smul_eq_mul]
            exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  have hc_inv : c * c.map τ = 1 := by
    have hy : ∀ y : Fin k → F, (c * c.map τ) *ᵥ y = y := by
      intro y
      let x : V := b.equivFun.symm y
      have hx : b.equivFun x = y := LinearEquiv.apply_symm_apply b.equivFun y
      have h1 : b.equivFun (sV x) = c *ᵥ (fun i => τ (y i)) := by
        rw [hcoe x, hx]
      have h2 : b.equivFun (sV (sV x)) =
          c *ᵥ (fun i => τ ((b.equivFun (sV x)) i)) := hcoe (sV x)
      have h3 : b.equivFun (sV (sV x)) = y := by rw [hsVinvol x, hx]
      rw [h3, h1] at h2
      rw [psuCKAsg3_map_mulVecEquiv τ c (fun i => τ (y i))] at h2
      have hττ : (fun i => τ (τ (y i))) = y := by
        funext i; rw [hτ]
      rw [hττ, Matrix.mulVec_mulVec] at h2
      exact h2.symm
    ext i j
    have h := congrFun (hy (Pi.single j (1 : F))) i
    rw [Matrix.mulVec_single_one] at h
    simpa [Matrix.col_apply, Pi.single_apply, Matrix.one_apply] using h
  have hcdet : c.det ≠ 0 := Matrix.det_ne_zero_of_right_inverse hc_inv
  have hcommMat : ∀ A : SUid τ k,
      c * (((A : GL (Fin k) F) : Matrix (Fin k) (Fin k) F).map τ) =
        ((A : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) * c := by
    intro A
    let M : Matrix (Fin k) (Fin k) F := (A : GL (Fin k) F)
    change c * M.map τ = M * c
    have hstep : ∀ y : Fin k → F,
        (c * M.map τ) *ᵥ (fun i => τ (y i)) = (M * c) *ᵥ (fun i => τ (y i)) := by
      intro y
      let x : V := b.equivFun.symm y
      have hx : b.equivFun x = y := LinearEquiv.apply_symm_apply b.equivFun y
      have h := hcomm A x
      have h' := congrArg b.equivFun h
      rw [hcoe (psuC2dE_gA b (A : GL (Fin k) F) x),
        psuC2dE_gA_equivFun b (A : GL (Fin k) F) x,
        psuC2dE_gA_equivFun b (A : GL (Fin k) F) (sV x), hcoe x, hx] at h'
      rw [psuCKAsg3_map_mulVecEquiv τ M y] at h'
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at h'
      exact h'
    ext i j
    have hsingle : (fun i : Fin k => τ ((Pi.single j (1 : F) : Fin k → F) i)) =
        (Pi.single j (1 : F) : Fin k → F) := by
      funext i
      by_cases hij : i = j
      · subst hij; simp
      · rw [Pi.single_apply, if_neg hij, map_zero]
    have h := hstep (Pi.single j (1 : F))
    rw [hsingle, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
    have h2 := congrFun h i
    simpa [Matrix.col_apply] using h2
  refine ⟨c, hcdet, ?_, ?_⟩
  · intro ρ
    obtain ⟨A, hA⟩ := psuCKAsg3_permMatrix_mem τ ρ
    have h := hcommMat A
    rw [hA] at h
    have hP : ∀ i j, (ρ.permMatrix F) i j = if ρ i = j then (1 : F) else 0 := by
      intro i j
      simp [Equiv.Perm.permMatrix, Matrix.submatrix_apply, Matrix.one_apply]
    have hmapP : (ρ.permMatrix F).map τ = ρ.permMatrix F := by
      ext i j
      rw [Matrix.map_apply, hP i j]
      by_cases hij : ρ i = j <;> simp [hij, map_one, map_zero]
    rw [hmapP] at h
    have hrel : ∀ a b, c (ρ a) (ρ b) = c a b := by
      intro a b
      have h2 := congrFun (congrFun h a) (ρ b)
      rw [Matrix.mul_apply, Matrix.mul_apply] at h2
      simp only [hP] at h2
      have hL : (∑ l, c a l * (if ρ l = ρ b then (1 : F) else 0)) = c a b := by
        rw [Finset.sum_eq_single b]
        · simp
        · intro l _ hl
          have hne : ρ l ≠ ρ b := fun hh => hl (ρ.injective hh)
          simp [hne]
        · intro hb; exact absurd (Finset.mem_univ b) hb
      have hR : (∑ l, (if ρ a = l then (1 : F) else 0) * c l (ρ b)) =
          c (ρ a) (ρ b) := by
        rw [Finset.sum_eq_single (ρ a)]
        · simp
        · intro l _ hl
          have hne : ρ a ≠ l := fun hh => hl hh.symm
          simp [hne]
        · intro hρ; exact absurd (Finset.mem_univ (ρ a)) hρ
      rw [hL, hR] at h2
      exact h2.symm
    ext a b
    exact hrel a b
  · intro lam hlam hprod
    obtain ⟨A, hA⟩ := psuCKAsg3_diag_mem τ lam hlam hprod
    have h := hcommMat A
    rw [hA, Matrix.diagonal_map (map_zero τ)] at h
    exact h

private theorem psuCKA_selfDual_commutation_data {f n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P)
    (hde : psuDag h e = e) (hψ : psuPsi h X e = e)
    {F : Type} [Field F] [Algebra K F] [Finite F] [CharP F 2]
    [Module F (LinearMap.range e.mulVecLin)] [IsScalarTower K F (LinearMap.range e.mulVecLin)]
    (π : psuAlg B →ₐ[K] F)
    (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K)
    (hbd : PsuBD e π ψ)
    (hk : 3 ≤ Module.finrank F (LinearMap.range e.mulVecLin))
    (hex : ¬ ((2 ^ f) ^ blockDegree (psuAlg B) e = 2 ∧
      Module.finrank F (LinearMap.range e.mulVecLin) = 3)) :
    ∃ (k : ℕ) (τ : F ≃+* F) (c : Matrix (Fin k) (Fin k) F) (μ : F),
      Module.finrank F (LinearMap.range e.mulVecLin) = k ∧
      3 ≤ k ∧ (∀ x, τ (τ x) = x) ∧ (∃ x, τ x ≠ x) ∧
      c.det ≠ 0 ∧ τ μ * μ = 1 ∧ μ ≠ 1 ∧
      (∀ ρ : Equiv.Perm (Fin k), (fun a b => c (ρ a) (ρ b)) = c) ∧
      (∀ lam : Fin k → F, (∀ i, τ (lam i) * lam i = 1) → ∏ i, lam i = 1 →
        c * Matrix.diagonal (fun i => τ (lam i)) = Matrix.diagonal lam * c) := by
  classical
  have heA : e ∈ psuAlg B := ((hP.1 e).1 he).1
  have hee : e * e = e := ((hP.1 e).1 he).2.1.eq
  obtain ⟨τ, hττ, hτσ, hτπ⟩ := psuC2dS_tau S heA hde π hbd.hπ hbd.hker
  have hne : ∃ x, τ x ≠ x := by
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    refine ⟨algebraMap K F c, fun hh => hc ?_⟩
    exact (algebraMap K F).injective ((hτσ c).symm.trans hh)
  obtain ⟨hKF, hKnd⟩ := psuC2dS_compat S hee hde π hbd.hπ hbd.hact τ hτπ
  obtain ⟨hKaddL, hKaddR, hKsmulL, hKsmulR, hKherm⟩ := psuC2dS_hf_props (n := n) h
  have hτU := psuC2dS_isUnitaryInvolution τ hττ hne
  obtain ⟨H, hHaddL, hHaddR, hHsmulL, hHsmulR, hHherm, hHnd, htr⟩ :=
    exists_hermTransfer (K := K) (F := F) (V := LinearMap.range e.mulVecLin)
      h.bar τ h.bar_bar hττ hτσ
      (fun x y => psuC2dS_hf h (x : Fin n → K) (y : Fin n → K))
      (fun x y z => hKaddL x y z) (fun x y z => hKaddR x y z)
      (fun c x y => hKsmulR c x y) (fun x y => hKherm x y) hKnd hKF
  haveI : Module.Finite K (LinearMap.range e.mulVecLin) := Module.Finite.of_finite
  haveI : Module.Finite F (LinearMap.range e.mulVecLin) :=
    Module.Finite.of_restrictScalars_finite K F (LinearMap.range e.mulVecLin)
  obtain ⟨b, hb⟩ := exists_hermOrthonormalBasis τ hτU H
    (Module.finrank F (LinearMap.range e.mulVecLin)) rfl hHherm hHaddL hHsmulL hHaddR hHsmulR hHnd
  have hcardF : Nat.card F = ((2 ^ f) ^ blockDegree (psuAlg B) e) ^ 2 := by
    rw [hbd.hcard, h.card]
    ring
  have hk2 : 2 ≤ Module.finrank F (LinearMap.range e.mulVecLin) := by omega
  have hexcl : ¬ ((2 ^ f) ^ blockDegree (psuAlg B) e = 2 ∧
      (Module.finrank F (LinearMap.range e.mulVecLin) = 2 ∨
        Module.finrank F (LinearMap.range e.mulVecLin) = 3)) := by
    rintro ⟨hQ2, h23⟩
    rcases h23 with h2 | h3
    · omega
    · exact hex ⟨hQ2, h3⟩
  have hperf : Group.IsPerfect ↥(SUid τ (Module.finrank F (LinearMap.range e.mulVecLin))) :=
    psuC2dS_SUid_perfect τ hτU hcardF hk2 hexcl
  have hθbar := psuCKAs_thetaBar_eq_tau S hde hψ π hbd.hπ hbd.hker τ hττ hne
  obtain ⟨sV, hsVcoe, hsVadd, hsVsmul, hsVinvol⟩ := psuCKAs_sV S hde hψ π ψ hbd τ hθbar
  have hcomm := psuCKAs_comm_gA S hee hde ψ hbd.hψw hbd.hψfix hbd.hψB τ H hHaddL hHaddR
    hHsmulL hHsmulR htr (Module.finrank F (LinearMap.range e.mulVecLin)) b hb hperf sV hsVcoe
  obtain ⟨c, hcdet, hperm, hdiag⟩ :=
    psuCKAs_matrix_data τ hττ b sV hsVadd hsVsmul hsVinvol hcomm
  obtain ⟨μ, hμ, hμ1⟩ := psuCKAs_exists_mu τ hττ hne
  exact ⟨Module.finrank F (LinearMap.range e.mulVecLin), τ, c, μ, rfl, hk, hττ, hne,
    hcdet, hμ, hμ1, hperm, hdiag⟩

private lemma psuCKAg1_Q2_facts {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P)
    {F : Type} [Field F] [Algebra K F]
    [Module F (LinearMap.range e.mulVecLin)] [IsScalarTower K F (LinearMap.range e.mulVecLin)]
    (π : psuAlg B →ₐ[K] F)
    (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K)
    (hbd : PsuBD e π ψ)
    (hQ : (2 ^ f) ^ blockDegree (psuAlg B) e = 2) :
    f = 1 ∧ blockDegree (psuAlg B) e = 1 ∧ Nat.card K = 4 ∧ Nat.card F = 4 := by
  have hdpos : 0 < blockDegree (psuAlg B) e := psuC2d_blockDegree_pos S P hP e he
  have hf1 : 1 ≤ f := h.one_le
  have hQpow : (2 ^ f) ^ blockDegree (psuAlg B) e =
      2 ^ (f * blockDegree (psuAlg B) e) := by rw [pow_mul]
  have h2 : 2 ^ (f * blockDegree (psuAlg B) e) = 2 := by rw [← hQpow]; exact hQ
  have hfd1 : f * blockDegree (psuAlg B) e = 1 := by
    have hm1 : 1 ≤ f * blockDegree (psuAlg B) e := Nat.mul_le_mul hf1 hdpos
    by_contra hm
    have hm2 : 2 ≤ f * blockDegree (psuAlg B) e := by omega
    have h4 : 4 ≤ 2 ^ (f * blockDegree (psuAlg B) e) := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (f * blockDegree (psuAlg B) e) := Nat.pow_le_pow_right (by norm_num) hm2
    omega
  obtain ⟨hf1', hd1⟩ : f = 1 ∧ blockDegree (psuAlg B) e = 1 :=
    ⟨Nat.dvd_one.mp ⟨blockDegree (psuAlg B) e, hfd1.symm⟩,
      Nat.dvd_one.mp ⟨f, by rw [mul_comm, hfd1]⟩⟩
  refine ⟨hf1', hd1, ?_, ?_⟩
  · rw [h.card, hf1']; norm_num
  · rw [hbd.hcard, h.card, hf1', hd1]; norm_num

private noncomputable def psuCKAg1_hfK {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} (e : Matrix (Fin n) (Fin n) K) :
    psuC2dS_V e →ₛₗ[(CFSG.ComponentClassification.Burgoyne.U.barEq h).toRingHom]
      psuC2dS_V e →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (CFSG.ComponentClassification.Burgoyne.U.barEq h).toRingHom (RingHom.id K)
    (fun u v => psuC2dS_hf h (u : Fin n → K) (v : Fin n → K))
    (fun u₁ u₂ v => by
      simpa only [Submodule.coe_add] using
        psuC2dS_hf_add_left h (u₁ : Fin n → K) (u₂ : Fin n → K) (v : Fin n → K))
    (fun c u v => by
      simp only [Submodule.coe_smul]
      rw [psuC2dS_hf_smul_left]
      congr 1)
    (fun u v₁ v₂ => by
      simpa only [Submodule.coe_add] using
        psuC2dS_hf_add_right h (u : Fin n → K) (v₁ : Fin n → K) (v₂ : Fin n → K))
    (fun c u v => by
      simpa only [Submodule.coe_smul, RingHom.id_apply, smul_eq_mul] using
        psuC2dS_hf_smul_right h c (u : Fin n → K) (v : Fin n → K))

private lemma psuCKAg1_hfK_apply {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} (e : Matrix (Fin n) (Fin n) K) (u v : psuC2dS_V e) :
    (psuCKAg1_hfK (h := h) e) u v = psuC2dS_hf h (u : Fin n → K) (v : Fin n → K) := rfl

private lemma psuCKAg1_hf_eq_gramForm {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (u v : Fin n → K) :
    psuC2dS_hf h u v = CFSG.ClassicalGroups.UnitaryFlag.gramForm h (psuJ n K) u v := rfl

private lemma psuCKAg1_hfK_isSymm {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} (e : Matrix (Fin n) (Fin n) K) :
    (psuCKAg1_hfK (h := h) e).IsSymm := by
  refine ⟨fun u v => ?_⟩
  change (CFSG.ComponentClassification.Burgoyne.U.barEq h)
      (psuC2dS_hf h (u : Fin n → K) (v : Fin n → K)) =
    psuC2dS_hf h (v : Fin n → K) (u : Fin n → K)
  rw [psuC2dS_hf_herm h (u : Fin n → K) (v : Fin n → K),
    CFSG.ComponentClassification.Burgoyne.U.barEq_apply, h.bar_bar]

private lemma psuCKAg1_hfK_nondegenerate {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hde : psuDag h e = e)
    {F : Type} [Field F] [Algebra K F]
    [Module F (LinearMap.range e.mulVecLin)] [IsScalarTower K F (LinearMap.range e.mulVecLin)]
    (π : psuAlg B →ₐ[K] F)
    (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K)
    (hbd : PsuBD e π ψ) :
    (psuCKAg1_hfK (h := h) e).Nondegenerate := by
  have hee : e * e = e := ((hP.1 e).1 he).2.1.eq
  have heA : e ∈ psuAlg B := ((hP.1 e).1 he).1
  obtain ⟨τ, hττ, hτσ, hτπ⟩ := psuC2dS_tau S heA hde π hbd.hπ hbd.hker
  obtain ⟨hKF, hKnd⟩ := psuC2dS_compat S hee hde π hbd.hπ hbd.hact τ hτπ
  refine ⟨?_, ?_⟩
  · intro x hx
    exact hKnd x hx
  · intro x hx
    apply hKnd x
    intro y
    have h1 : psuC2dS_hf h (y : Fin n → K) (x : Fin n → K) = 0 := hx y
    have h2 : psuC2dS_hf h (x : Fin n → K) (y : Fin n → K) =
        h.bar (psuC2dS_hf h (y : Fin n → K) (x : Fin n → K)) :=
      psuC2dS_hf_herm h (x : Fin n → K) (y : Fin n → K)
    rw [h2, h1, map_zero]

private lemma psuCKAg1_comm_alg {n : ℕ} {K : Type} [Field K] {B : GL (Fin n) K}
    (x : GL (Fin n) K)
    (hxB : (x : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K)) :
    ∀ a ∈ psuAlg B, (x : Matrix (Fin n) (Fin n) K) * a =
      a * (x : Matrix (Fin n) (Fin n) K) := by
  intro a ha
  refine Algebra.adjoin_induction (p := fun a _ =>
    (x : Matrix (Fin n) (Fin n) K) * a = a * (x : Matrix (Fin n) (Fin n) K)) ?_ ?_ ?_ ?_ ha
  · rintro y ⟨u, hu, rfl⟩
    rw [Set.mem_singleton_iff] at hu
    subst hu
    exact hxB
  · intro r
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul]
  · intro a b _ _ ha hb
    rw [mul_add, add_mul, ha, hb]
  · intro a b _ _ ha hb
    calc (x : Matrix (Fin n) (Fin n) K) * (a * b)
        = ((x : Matrix (Fin n) (Fin n) K) * a) * b := by rw [mul_assoc]
      _ = (a * (x : Matrix (Fin n) (Fin n) K)) * b := by rw [ha]
      _ = a * ((x : Matrix (Fin n) (Fin n) K) * b) := by rw [mul_assoc]
      _ = a * (b * (x : Matrix (Fin n) (Fin n) K)) := by rw [hb]
      _ = (a * b) * (x : Matrix (Fin n) (Fin n) K) := by rw [mul_assoc]

private noncomputable def psuCKAg1_resLin {n : ℕ} {K : Type} [Field K]
    {e : Matrix (Fin n) (Fin n) K} (x : GL (Fin n) K)
    (hxe : (x : Matrix (Fin n) (Fin n) K) * e = e * (x : Matrix (Fin n) (Fin n) K)) :
    psuC2dS_V e →ₗ[K] psuC2dS_V e where
  toFun w := ⟨(x : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K), by
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp w.2
    rw [Matrix.mulVecLin_apply] at hu
    refine ⟨(x : Matrix (Fin n) (Fin n) K) *ᵥ u, ?_⟩
    show e *ᵥ ((x : Matrix (Fin n) (Fin n) K) *ᵥ u) =
      (x : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K)
    rw [← hu, Matrix.mulVec_mulVec, ← hxe, Matrix.mulVec_mulVec]⟩
  map_add' w₁ w₂ := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Matrix.mulVec_add]
  map_smul' c w := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, Matrix.mulVec_smul, RingHom.id_apply]

private noncomputable def psuCKAg1_res {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} (B : GL (Fin n) K) (e : Matrix (Fin n) (Fin n) K)
    (heA : e ∈ psuAlg B) (hde : psuDag h e = e) (x : ↥(psuBlock h B e)) :
    psuC2dS_V e ≃ₗ[K] psuC2dS_V e := by
  have hxmem : (((x : AutPSU.XJ h n) : GL (Fin n) K)) ∈
      Subgroup.centralizer ({B} : Set (GL (Fin n) K)) ⊓ glFixing (1 - e) := by
    have h := Subgroup.mem_comap.mp x.2
    simpa [psuBlock, glBlockCentralizer, psuOrbitIdem, hde] using h
  have hxB : (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) *
        (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have h := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxmem).1 B
      (Set.mem_singleton B)).symm
    simpa using congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) h
  have hxe : (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * e =
      e * (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    psuCKAg1_comm_alg ((x : AutPSU.XJ h n) : GL (Fin n) K) hxB e heA
  have hxinv : (((x⁻¹ : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul]; simp
  have hxinv' : (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (((x⁻¹ : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul]; simp
  have hxe_inv : (((x⁻¹ : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * e =
      e * (((x⁻¹ : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    let a : Matrix (Fin n) (Fin n) K :=
      (((x⁻¹ : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    let b : Matrix (Fin n) (Fin n) K :=
      (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    have hab1 : a * b = 1 := hxinv
    have hab2 : b * a = 1 := hxinv'
    change a * e = e * a
    calc a * e
        = (a * e) * 1 := (mul_one _).symm
      _ = (a * e) * (b * a) := by rw [hab2]
      _ = ((a * e) * b) * a := (mul_assoc (a * e) b a).symm
      _ = (a * (e * b)) * a := congrArg (fun z => z * a) (mul_assoc a e b)
      _ = (a * (b * e)) * a := congrArg (fun z => (a * z) * a) hxe.symm
      _ = ((a * b) * e) * a := congrArg (fun z => z * a) (mul_assoc a b e).symm
      _ = e * a := by rw [hab1, one_mul]
  have hmem : ∀ u : psuC2dS_V e,
      (((x⁻¹ : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        (u : Fin n → K) ∈ psuC2dS_V e := by
    intro u
    obtain ⟨u₀, hu₀⟩ := LinearMap.mem_range.mp u.2
    rw [Matrix.mulVecLin_apply] at hu₀
    refine ⟨(((x⁻¹ : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u₀, ?_⟩
    show e *ᵥ ((((x⁻¹ : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u₀) =
      (((x⁻¹ : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (u : Fin n → K)
    rw [← hu₀, Matrix.mulVec_mulVec, ← hxe_inv, Matrix.mulVec_mulVec]
  refine LinearEquiv.ofBijective
    (psuCKAg1_resLin (((x : AutPSU.XJ h n) : GL (Fin n) K)) hxe) ⟨?_, ?_⟩
  · intro w₁ w₂ hw
    apply Subtype.ext
    have h' : (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        (w₁ : Fin n → K) =
        (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          (w₂ : Fin n → K) := congrArg (fun w : psuC2dS_V e => (w : Fin n → K)) hw
    have h2 := congrArg (fun v : Fin n → K =>
      (((x⁻¹ : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) h'
    simpa [Matrix.mulVec_mulVec, hxinv, Matrix.one_mulVec] using h2
  · intro u
    refine ⟨⟨(((x⁻¹ : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (u : Fin n → K), hmem u⟩, ?_⟩
    apply Subtype.ext
    show (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        ((((x⁻¹ : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          (u : Fin n → K)) = (u : Fin n → K)
    rw [Matrix.mulVec_mulVec, hxinv', Matrix.one_mulVec]

private lemma psuCKAg1_res_apply {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} (B : GL (Fin n) K) (e : Matrix (Fin n) (Fin n) K)
    (heA : e ∈ psuAlg B) (hde : psuDag h e = e) (x : ↥(psuBlock h B e)) (w : psuC2dS_V e) :
    ((psuCKAg1_res (h := h) B e heA hde x w : psuC2dS_V e) : Fin n → K) =
      (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) :=
  rfl

private noncomputable def psuCKAg1_chi {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} (B : GL (Fin n) K) (e : Matrix (Fin n) (Fin n) K)
    (heA : e ∈ psuAlg B) (hde : psuDag h e = e) :
    ↥(psuBlock h B e) →*
      ↥(CFSG.ComponentClassification.CatalogueBUnitaryIsometry.isometryGroup
        (psuCKAg1_hfK (h := h) e)) :=
  { toFun := fun x => ⟨psuCKAg1_res (h := h) B e heA hde x,
      (CFSG.ComponentClassification.CatalogueBUnitaryIsometry.mem_isometryGroup_iff
        (psuCKAg1_hfK (h := h) e) (psuCKAg1_res (h := h) B e heA hde x)).mpr (by
        have hiso := ((CFSG.ClassicalGroups.UnitaryFlag.mem_gramSU_iff_isometry
          (h := h) (G := psuJ n K)
          (g := (((x : AutPSU.XJ h n) : GL (Fin n) K)))).mp
          (x : AutPSU.XJ h n).2).1
        intro u v
        rw [psuCKAg1_hfK_apply, psuCKAg1_hfK_apply, psuCKAg1_res_apply, psuCKAg1_res_apply]
        exact (psuCKAg1_hf_eq_gramForm h _ _).trans
          ((hiso (u : Fin n → K) (v : Fin n → K)).trans
            (psuCKAg1_hf_eq_gramForm h (u : Fin n → K) (v : Fin n → K)).symm))⟩
    map_one' := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro w
      apply Subtype.ext
      simp only [psuCKAg1_res_apply, Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]
      rfl
    map_mul' := by
      intro x y
      apply Subtype.ext
      apply LinearEquiv.ext
      intro w
      apply Subtype.ext
      simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, psuCKAg1_res_apply, Units.val_mul,
        Matrix.mulVec_mulVec] }

private lemma psuCKAg1_chi_inj {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} (B : GL (Fin n) K) (e : Matrix (Fin n) (Fin n) K)
    (heA : e ∈ psuAlg B) (hde : psuDag h e = e) :
    Function.Injective (psuCKAg1_chi (h := h) B e heA hde) := by
  intro x y hxy
  have hres : psuCKAg1_res (h := h) B e heA hde x = psuCKAg1_res (h := h) B e heA hde y :=
    congrArg Subtype.val hxy
  have hlin : ∀ w : psuC2dS_V e,
      (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) =
      (((y : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) := by
    intro w
    have h := congrArg (fun g : psuC2dS_V e ≃ₗ[K] psuC2dS_V e => (g w : psuC2dS_V e)) hres
    have h' := congrArg (fun v : psuC2dS_V e => (v : Fin n → K)) h
    rw [psuCKAg1_res_apply, psuCKAg1_res_apply] at h'
    exact h'
  have hxfix : (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (1 - e) =
      1 - e := by
    have h := Subgroup.mem_comap.mp x.2
    exact (Subgroup.mem_inf.mp (by
      simpa [psuBlock, glBlockCentralizer, psuOrbitIdem, hde] using h)).2
  have hyfix : (((y : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (1 - e) =
      1 - e := by
    have h := Subgroup.mem_comap.mp y.2
    exact (Subgroup.mem_inf.mp (by
      simpa [psuBlock, glBlockCentralizer, psuOrbitIdem, hde] using h)).2
  have hmate : (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * e =
      (((y : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * e := by
    apply Matrix.ext
    intro i j
    have hw := hlin ⟨e *ᵥ Pi.single j 1, ⟨Pi.single j 1, rfl⟩⟩
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one,
      Matrix.mulVec_single_one] at hw
    exact congrFun hw i
  have hmat : (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (((y : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    calc (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        = (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * 1 :=
          (mul_one _).symm
      _ = (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (e + (1 - e)) := by rw [add_sub_cancel]
      _ = (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * e +
            (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (1 - e) :=
          Matrix.mul_add _ _ _
      _ = (((y : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * e +
            (1 - e) := by rw [hmate, hxfix]
      _ = (((y : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * e +
            (((y : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (1 - e) := by
          rw [hyfix]
      _ = (((y : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (e + (1 - e)) := (Matrix.mul_add _ _ _).symm
      _ = (((y : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * 1 := by
          rw [add_sub_cancel]
      _ = (((y : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := mul_one _
  apply Subtype.ext
  apply Subtype.ext
  exact Units.ext hmat

private lemma psuCKAg1_unitarySU_two_solvable {K : Type} [Field K] (h : UnitaryFieldData 2 1 K) :
    Group.IsSolvable ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 2) := by
  haveI : Finite K := h.finite
  haveI : CharP K 2 := h.charP
  have hc := CFSG.RankThree.PartOne.KFU.card_statedSU_eq h (n := 2) (by norm_num)
  have hcard : Nat.card ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 2) = 6 := by
    have e : Nat.card ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 2) =
        Nat.card (CFSG.Open.StatedSU 2 (2 ^ 1) K) := rfl
    rw [e]
    have h2 : Finset.Icc 2 2 = ({2} : Finset ℕ) := by decide
    rw [h2, Finset.prod_singleton] at hc
    have hc1 : (Nat.card (CFSG.Open.StatedSU 2 (2 ^ 1) K) : ℤ) = 6 := by rw [hc]; norm_num
    exact_mod_cast hc1
  haveI : Fintype ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 2) := Fintype.ofFinite _
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    (a := 1) (b := 1) Nat.prime_two Nat.prime_three (by norm_num)
    (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)

private lemma psuCKAg1_specialIsometry_solvable {f n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hde : psuDag h e = e)
    {F : Type} [Field F] [Algebra K F]
    [Module F (LinearMap.range e.mulVecLin)] [IsScalarTower K F (LinearMap.range e.mulVecLin)]
    (π : psuAlg B →ₐ[K] F)
    (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K)
    (hbd : PsuBD e π ψ) (hf1 : f = 1)
    (hKdim : Module.finrank K (psuC2dS_V e) = 2) :
    Group.IsSolvable
      ↥(CFSG.ComponentClassification.CatalogueBUnitaryIsometry.specialIsometry
        (psuCKAg1_hfK (h := h) e)) := by
  have hsigma : (CFSG.ComponentClassification.Burgoyne.U.barEq h) ^ 2 = 1 := by
    ext x
    simp [pow_two, CFSG.ComponentClassification.Burgoyne.U.barEq_apply, h.bar_bar]
  have hne : CFSG.ComponentClassification.Burgoyne.U.barEq h ≠ 1 := by
    intro hh
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    exact hc (by
      have h1 := congrArg (fun f : K ≃+* K => f c) hh
      simpa [CFSG.ComponentClassification.Burgoyne.U.barEq_apply] using h1)
  obtain ⟨b, hb, -, ⟨eSU⟩⟩ :=
    CFSG.ComponentClassification.CatalogueBUnitaryIsometry.exists_native_isometry_groups
      (psuCKAg1_hfK (h := h) e) (psuCKAg1_hfK_isSymm e)
      (psuCKAg1_hfK_nondegenerate S P hP e he hde π ψ hbd) hsigma hne
  rw [hKdim] at eSU
  have hbar : CFSG.ComponentClassification.Burgoyne.U.barEq h =
      CFSG.LieType.BorelTits.unitaryInvolution K 2 1 := by
    ext x
    show h.bar x = CFSG.LieType.BorelTits.unitaryInvolution K 2 1 x
    rw [h.bar_apply, hf1]
    rfl
  have hSUtype : CFSG.LieType.Universal.Unitary.SUid
      (CFSG.ComponentClassification.Burgoyne.U.barEq h) 2 =
      CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 2 := by
    rw [hbar, CFSG.LieType.Universal.Unitary.SUid_eq_statedSU (p := 2) (f := 1)
      (by rw [h.card, hf1]; norm_num) 2]
  have hK : UnitaryFieldData 2 1 K := by rw [hf1] at h; exact h
  haveI : Group.IsSolvable ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 2) :=
    psuCKAg1_unitarySU_two_solvable hK
  have e' := eSU.trans (MulEquiv.subgroupCongr hSUtype)
  exact Group.isSolvable_of_isSolvable_injective (f := e'.toMonoidHom) e'.injective

private lemma psuCKA_finrank_ne_one {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P)
    (hns : ¬ Group.IsSolvable ↥(psuBlock h B e))
    {F : Type} [Field F] [Algebra K F]
    [Module F (LinearMap.range e.mulVecLin)] [IsScalarTower K F (LinearMap.range e.mulVecLin)]
    (π : psuAlg B →ₐ[K] F)
    (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K)
    (hbd : PsuBD e π ψ) :
    Module.finrank F (LinearMap.range e.mulVecLin) ≠ 1 := by
  intro hk
  exact hns (psuK_solvable_of_finrank_one S P hP e he π ψ hbd hk)

private lemma psuCKAg3_perm_two_points (k : ℕ) {i j i' j' : Fin k}
    (hij : i ≠ j) (hi'j' : i' ≠ j') :
    ∃ ρ : Equiv.Perm (Fin k), ρ i = i' ∧ ρ j = j' := by
  let f : Bool → Fin k := fun b => if b then j else i
  let g : Bool → Fin k := fun b => if b then j' else i'
  have hf : Function.Injective f := by
    intro x y hxy
    cases x <;> cases y
    · rfl
    · exact absurd (by simpa [f] using hxy) hij
    · exact absurd (by simpa [f] using hxy.symm) hij
    · rfl
  have hg : Function.Injective g := by
    intro x y hxy
    cases x <;> cases y
    · rfl
    · exact absurd (by simpa [g] using hxy) hi'j'
    · exact absurd (by simpa [g] using hxy.symm) hi'j'
    · rfl
  obtain ⟨ρ, hρ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  exact ⟨ρ, by simpa [f, g] using hρ false, by simpa [f, g] using hρ true⟩

private lemma psuCKAg3_perm_entry {k : ℕ} {F : Type}
    {c : Matrix (Fin k) (Fin k) F}
    (hperm : ∀ ρ : Equiv.Perm (Fin k), (fun a b => c (ρ a) (ρ b)) = c)
    {i j i' j' : Fin k} (hij : i ≠ j) (hi'j' : i' ≠ j') :
    c i j = c i' j' := by
  obtain ⟨ρ, h1, h2⟩ := psuCKAg3_perm_two_points k hij hi'j'
  have hmat := congr_fun (congr_fun (hperm ρ) i) j
  rw [h1, h2] at hmat
  exact hmat.symm

private lemma psuCKAg3_prod_three {k : ℕ} {F : Type} [Field F]
    {a b l : Fin k} (hab : a ≠ b) (hal : a ≠ l) (hbl : b ≠ l) (x y z : F) :
    (∏ i : Fin k,
      (if i = a then x else if i = b then y else if i = l then z else 1))
      = x * y * z := by
  classical
  let f : Fin k → F := fun i =>
    if i = a then x else if i = b then y else if i = l then z else 1
  have ha : f a = x := by simp [f]
  have hb : f b = y := by simp [f, hab.symm]
  have hl : f l = z := by simp [f, hal.symm, hbl.symm]
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ a)]
  have h1 : (∏ i ∈ (Finset.univ.erase a), f i) = y * z := by
    rw [← Finset.mul_prod_erase (Finset.univ.erase a) f
      (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩)]
    have h2 : (∏ i ∈ ((Finset.univ.erase a).erase b), f i) = z := by
      rw [Finset.prod_eq_single l]
      · exact hl
      · intro c hc hcl
        simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hc
        obtain ⟨hcb, hca⟩ := hc
        simp [f, hca, hcb, hcl]
      · intro hmem
        exact absurd (by
          simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          exact ⟨hbl.symm, hal.symm⟩) hmem
    rw [h2, hb]
  rw [ha, h1]
  ring

private lemma psuCKAg3_diag_apply {k : ℕ} {F : Type} [Field F]
    {τ : F ≃+* F} {c : Matrix (Fin k) (Fin k) F}
    (hdiag : ∀ lam : Fin k → F, (∀ i, τ (lam i) * lam i = 1) →
      ∏ i, lam i = 1 →
      c * Matrix.diagonal (fun i => τ (lam i)) = Matrix.diagonal lam * c)
    {lam : Fin k → F}
    (hlam : ∀ i, τ (lam i) * lam i = 1) (hprod : ∏ i, lam i = 1)
    (i j : Fin k) : c i j * τ (lam j) = lam i * c i j := by
  have h := congr_fun (congr_fun (hdiag lam hlam hprod) i) j
  simpa [Matrix.mul_apply, Matrix.diagonal, Finset.sum_eq_single j] using h

private lemma psuCKAg3_scalar {k : ℕ} {F : Type} [Field F]
    (hk : 3 ≤ k) (τ : F ≃+* F) (hττ : ∀ x, τ (τ x) = x)
    (c : Matrix (Fin k) (Fin k) F) (hc : c.det ≠ 0)
    (μ : F) (hμ : τ μ * μ = 1) (hμ1 : μ ≠ 1)
    (hperm : ∀ ρ : Equiv.Perm (Fin k), (fun a b => c (ρ a) (ρ b)) = c)
    (hdiag : ∀ lam : Fin k → F, (∀ i, τ (lam i) * lam i = 1) → ∏ i, lam i = 1 →
      c * Matrix.diagonal (fun i => τ (lam i)) = Matrix.diagonal lam * c) :
    ∃ β : F, β ≠ 0 ∧ c = Matrix.diagonal (fun _ => β) := by
  let a : Fin k := ⟨0, by omega⟩
  let b : Fin k := ⟨1, by omega⟩
  let l : Fin k := ⟨2, by omega⟩
  have hab : a ≠ b := by
    intro h
    have h' := congrArg Fin.val h
    simp [a, b] at h'
  have hal : a ≠ l := by
    intro h
    have h' := congrArg Fin.val h
    simp [a, l] at h'
  have hbl : b ≠ l := by
    intro h
    have h' := congrArg Fin.val h
    simp [b, l] at h'
  let lam1 : Fin k → F := fun i =>
    if i = a then 1 else if i = b then μ else if i = l then τ μ else 1
  have ha1 : lam1 a = 1 := by simp [lam1]
  have hb1 : lam1 b = μ := by simp [lam1, hab.symm]
  have hl1 : lam1 l = τ μ := by simp [lam1, hal.symm, hbl.symm]
  have hlam1 : ∀ i, τ (lam1 i) * lam1 i = 1 := by
    intro i
    by_cases hia : i = a
    · subst i
      rw [ha1]
      simp
    · by_cases hib : i = b
      · subst i
        rw [hb1]
        exact hμ
      · by_cases hil : i = l
        · subst i
          rw [hl1, hττ]
          simpa [mul_comm] using hμ
        · have hi1 : lam1 i = 1 := by simp [lam1, hia, hib, hil]
          rw [hi1]
          simp
  have hprod1 : ∏ i, lam1 i = 1 := by
    have h := psuCKAg3_prod_three (F := F) hab hal hbl (1 : F) μ (τ μ)
    have hmul : μ * τ μ = 1 := by simpa [mul_comm] using hμ
    simpa [lam1, hmul] using h
  have hentry := psuCKAg3_diag_apply hdiag hlam1 hprod1 a b
  rw [ha1, hb1] at hentry
  have hτμne : τ μ - 1 ≠ 0 := by
    intro h
    apply hμ1
    have hτ : τ μ = 1 := sub_eq_zero.mp h
    rw [hτ, one_mul] at hμ
    exact hμ
  have hoff : c a b = 0 := by
    have hzero : c a b * (τ μ - 1) = 0 := by
      simpa [mul_sub, mul_one, hentry]
    exact (mul_eq_zero.mp hzero).resolve_right hτμne
  have hoffdiag : ∀ i j : Fin k, i ≠ j → c i j = 0 := by
    intro i j hij
    have h := psuCKAg3_perm_entry hperm hij hab
    rw [h, hoff]
  have hdiag_eq : ∀ i : Fin k, c i i = c a a := by
    intro i
    have hmat := congr_fun (congr_fun (hperm (Equiv.swap a i)) a) a
    simpa [Equiv.swap_apply_left] using hmat
  have hceq : c = Matrix.diagonal (fun _ : Fin k => c a a) := by
    ext i j
    by_cases hij : i = j
    · subst j
      rw [hdiag_eq i]
      simp
    · rw [hoffdiag i j hij]
      simp [hij]
  have hdet : c.det = (c a a) ^ k := by
    rw [hceq, Matrix.det_diagonal]
    simp [Finset.prod_const]
  refine ⟨c a a, ?_, hceq⟩
  intro hβ
  apply hc
  rw [hdet, hβ]
  exact zero_pow (by omega : k ≠ 0)

private lemma psuCKAg3_final_contradiction {k : ℕ} {F : Type} [Field F] [CharP F 2]
    (hk : 3 ≤ k) (τ : F ≃+* F) (hττ : ∀ x, τ (τ x) = x)
    (μ : F) (hμ : τ μ * μ = 1) (hμ1 : μ ≠ 1)
    (c : Matrix (Fin k) (Fin k) F) (β : F) (hβ : β ≠ 0)
    (hceq : c = Matrix.diagonal (fun _ => β))
    (hdiag : ∀ lam : Fin k → F, (∀ i, τ (lam i) * lam i = 1) → ∏ i, lam i = 1 →
      c * Matrix.diagonal (fun i => τ (lam i)) = Matrix.diagonal lam * c) :
    False := by
  let a : Fin k := ⟨0, by omega⟩
  let b : Fin k := ⟨1, by omega⟩
  let l : Fin k := ⟨2, by omega⟩
  have hab : a ≠ b := by
    intro h
    have h' := congrArg Fin.val h
    simp [a, b] at h'
  have hal : a ≠ l := by
    intro h
    have h' := congrArg Fin.val h
    simp [a, l] at h'
  have hbl : b ≠ l := by
    intro h
    have h' := congrArg Fin.val h
    simp [b, l] at h'
  let lam2 : Fin k → F := fun i =>
    if i = a then μ else if i = b then τ μ else if i = l then 1 else 1
  have ha2 : lam2 a = μ := by simp [lam2]
  have hb2 : lam2 b = τ μ := by simp [lam2, hab.symm]
  have hl2 : lam2 l = 1 := by simp [lam2, hal.symm, hbl.symm]
  have hlam2 : ∀ i, τ (lam2 i) * lam2 i = 1 := by
    intro i
    by_cases hia : i = a
    · subst i
      rw [ha2]
      exact hμ
    · by_cases hib : i = b
      · subst i
        rw [hb2, hττ]
        simpa [mul_comm] using hμ
      · by_cases hil : i = l
        · subst i
          rw [hl2]
          simp
        · have hi2 : lam2 i = 1 := by simp [lam2, hia, hib, hil]
          rw [hi2]
          simp
  have hprod2 : ∏ i, lam2 i = 1 := by
    have h := psuCKAg3_prod_three (F := F) hab hal hbl μ (τ μ) 1
    have hmul : μ * τ μ = 1 := by simpa [mul_comm] using hμ
    simpa [lam2, hmul] using h
  have hentry := psuCKAg3_diag_apply hdiag hlam2 hprod2 a a
  rw [ha2, hceq] at hentry
  simp at hentry
  have hτμ : τ μ = μ := by
    have hcomm : β * τ μ = β * μ := by
      simpa [mul_comm μ β] using hentry
    exact mul_left_cancel₀ hβ hcomm
  have hμsq : μ * μ = 1 := by
    have h := hμ
    rwa [hτμ] at h
  have hsq : (μ - 1) * (μ - 1) = 0 := by
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    calc
      (μ - 1) * (μ - 1) = μ * μ - (2 : F) * μ + 1 := by ring
      _ = 1 - 0 * μ + 1 := by rw [hμsq, h2]
      _ = (1 : F) + 1 := by ring
      _ = 0 := by
        rw [← two_mul]
        simpa using h2
  have hsub : μ - 1 = 0 := by
    rcases mul_eq_zero.mp hsq with h | h
    · exact h
    · exact h
  exact hμ1 (sub_eq_zero.mp hsub)

private lemma psuCKA_semilinear_no_perfect_su_matrix {F : Type} [Field F] [CharP F 2]
    (k : ℕ) (hk : 3 ≤ k) (τ : F ≃+* F) (hττ : ∀ x, τ (τ x) = x)
    (c : Matrix (Fin k) (Fin k) F) (hc : c.det ≠ 0)
    (μ : F) (hμ : τ μ * μ = 1) (hμ1 : μ ≠ 1)
    (hperm : ∀ ρ : Equiv.Perm (Fin k), (fun a b => c (ρ a) (ρ b)) = c)
    (hdiag : ∀ lam : Fin k → F, (∀ i, τ (lam i) * lam i = 1) → ∏ i, lam i = 1 →
      c * Matrix.diagonal (fun i => τ (lam i)) = Matrix.diagonal lam * c) :
    False := by
  obtain ⟨β, hβ, hcβ⟩ := psuCKAg3_scalar hk τ hττ c hc μ hμ hμ1 hperm hdiag
  exact psuCKAg3_final_contradiction hk τ hττ μ hμ hμ1 c β hβ hcβ hdiag

private lemma psuCKA_k_ge_three_impossible {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P)
    (hde : psuDag h e = e) (hψ : psuPsi h X e = e)
    {F : Type} [Field F] [Algebra K F] [Finite F] [CharP F 2]
    [Module F (LinearMap.range e.mulVecLin)] [IsScalarTower K F (LinearMap.range e.mulVecLin)]
    (π : psuAlg B →ₐ[K] F)
    (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K)
    (hbd : PsuBD e π ψ)
    (hk : 3 ≤ Module.finrank F (LinearMap.range e.mulVecLin))
    (hex : ¬ ((2 ^ f) ^ blockDegree (psuAlg B) e = 2 ∧
      Module.finrank F (LinearMap.range e.mulVecLin) = 3)) :
    False := by
  obtain ⟨k, τ, c, μ, _hkdim, hk3, hττ, _hτne, hcdet, hμ, hμ1, hperm, hdiag⟩ :=
    psuCKA_selfDual_commutation_data S P hP e he hde hψ π ψ hbd hk hex
  exact psuCKA_semilinear_no_perfect_su_matrix k hk3 τ hττ c hcdet μ hμ hμ1 hperm hdiag

private lemma psuCKA_small_k_two_Q_two_solvable {f n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P)
    (hde : psuDag h e = e)
    {F : Type} [Field F] [Algebra K F] [Finite F] [CharP F 2]
    [Module F (LinearMap.range e.mulVecLin)] [IsScalarTower K F (LinearMap.range e.mulVecLin)]
    (π : psuAlg B →ₐ[K] F)
    (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K)
    (hbd : PsuBD e π ψ)
    (hk : Module.finrank F (LinearMap.range e.mulVecLin) = 2)
    (hQ : (2 ^ f) ^ blockDegree (psuAlg B) e = 2) :
    Group.IsSolvable ↥(psuBlock h B e) := by
  obtain ⟨hf1, hd1, hcardK, hcardF⟩ := psuCKAg1_Q2_facts S P hP e he π ψ hbd hQ
  have heA : e ∈ psuAlg B := ((hP.1 e).1 he).1
  have hrank : Module.finrank K (LinearMap.range e.mulVecLin) = 2 := by
    rw [← show Matrix.rank e = Module.finrank K (LinearMap.range e.mulVecLin) from rfl,
      hbd.hrank, hbd.hdim, hd1, one_mul, hk]
  haveI : Group.IsSolvable
      ↥(CFSG.ComponentClassification.CatalogueBUnitaryIsometry.isometryGroup
        (psuCKAg1_hfK (h := h) e)) := by
    haveI : Group.IsSolvable
        ↥(CFSG.ComponentClassification.CatalogueBUnitaryIsometry.specialIsometry
          (psuCKAg1_hfK (h := h) e)) :=
      psuCKAg1_specialIsometry_solvable S P hP e he hde π ψ hbd hf1 hrank
    exact Group.isSolvable_of_subgroup_quotient
      (CFSG.ComponentClassification.CatalogueBUnitaryIsometry.specialIsometry
        (psuCKAg1_hfK (h := h) e))
  exact solvable_of_solvable_injective (f := psuCKAg1_chi (h := h) B e heA hde)
    (psuCKAg1_chi_inj (h := h) B e heA hde)

private lemma psuCKAg2_comm_e {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {B : GL (Fin n) K}
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (x : ↥(psuBlock h B e)) :
    ((x : AutPSU.XJ h n) : GL (Fin n) K) * e =
      e * ((x : AutPSU.XJ h n) : GL (Fin n) K) := by
  have heA : e ∈ psuAlg B := ((hP.1 e).1 he).1
  have hxB : (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) *
        (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have hxmem : ((x : AutPSU.XJ h n) : GL (Fin n) K) ∈
        Subgroup.centralizer ({B} : Set (GL (Fin n) K)) ⊓ glFixing (1 - psuOrbitIdem h e) :=
      Subgroup.mem_comap.mp x.2
    have hxcen : ((x : AutPSU.XJ h n) : GL (Fin n) K) ∈
        Subgroup.centralizer ({B} : Set (GL (Fin n) K)) := (Subgroup.mem_inf.mp hxmem).1
    rw [Subgroup.mem_centralizer_iff] at hxcen
    exact congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K))
      (hxcen B (Set.mem_singleton B)).symm
  let C : Subalgebra K (Matrix (Fin n) (Fin n) K) :=
    { carrier := {a | (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * a =
        a * (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)}
      mul_mem' := by
        intro a b ha hb
        have ha' : (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * a =
            a * (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := ha
        have hb' : (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * b =
            b * (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := hb
        show (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (a * b) =
          (a * b) * (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        calc (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (a * b)
            = ((((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * a) * b := by
              rw [mul_assoc]
          _ = (a * (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * b := by
              rw [ha']
          _ = a * ((((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * b) := by
              rw [mul_assoc]
          _ = a * (b * (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
              rw [hb']
          _ = (a * b) * (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
              rw [← mul_assoc]
      one_mem' := by
        show (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * 1 =
          1 * (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        rw [mul_one, one_mul]
      add_mem' := by
        intro a b ha hb
        have ha' : (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * a =
            a * (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := ha
        have hb' : (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * b =
            b * (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := hb
        show (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (a + b) =
          (a + b) * (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        rw [mul_add, add_mul, ha', hb']
      zero_mem' := by
        show (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * 0 =
          0 * (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        rw [mul_zero, zero_mul]
      algebraMap_mem' := by
        intro c
        show (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            algebraMap K (Matrix (Fin n) (Fin n) K) c =
          algebraMap K (Matrix (Fin n) (Fin n) K) c *
            (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        simp [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc] }
  have hle : psuAlg B ≤ C := by
    rw [psuAlg, Algebra.adjoin_le_iff]
    rintro a ⟨b, hb, rfl⟩
    rw [Set.mem_singleton_iff] at hb
    subst hb
    exact hxB
  exact hle heA

private lemma psuCKAg2_mulVec_mem_Ve_of_comm {n : ℕ} {K : Type} [Field K]
    {e : Matrix (Fin n) (Fin n) K} (hee : e * e = e) {M : GL (Fin n) K}
    (hcomm : (M : Matrix (Fin n) (Fin n) K) * e = e * (M : Matrix (Fin n) (Fin n) K))
    {w : Fin n → K} (hw : w ∈ psuC2dS_V e) :
    (M : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ psuC2dS_V e := by
  refine ⟨(M : Matrix (Fin n) (Fin n) K) *ᵥ w, ?_⟩
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hcomm.symm, ← Matrix.mulVec_mulVec,
    psuC2dS_mulVec_eq_of_mem hee hw]

private lemma psuCKAg2_mulVec_mem_Ve {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {B : GL (Fin n) K}
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (x : ↥(psuBlock h B e))
    {w : Fin n → K} (hw : w ∈ psuC2dS_V e) :
    ((x : AutPSU.XJ h n) : GL (Fin n) K) *ᵥ w ∈ psuC2dS_V e := by
  have hee : e * e = e := ((hP.1 e).1 he).2.1.eq
  exact psuCKAg2_mulVec_mem_Ve_of_comm hee (psuCKAg2_comm_e P hP e he x) hw

private lemma psuCKAg2_inv_comm {n : ℕ} {K : Type} [Field K]
    {e : Matrix (Fin n) (Fin n) K} {M : GL (Fin n) K}
    (hcomm : (M : Matrix (Fin n) (Fin n) K) * e = e * (M : Matrix (Fin n) (Fin n) K)) :
    (((M⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) * e =
      e * (((M⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) := by
  have h := congrArg (fun t : Matrix (Fin n) (Fin n) K =>
    (((M⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) * t *
      (((M⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)) hcomm
  have hL : (((M⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *
      ((M : Matrix (Fin n) (Fin n) K) * e) *
        (((M⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) =
      e * (((M⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) := by
    calc (((M⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *
          ((M : Matrix (Fin n) (Fin n) K) * e) *
            (((M⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)
        = ((((M⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *
            (M : Matrix (Fin n) (Fin n) K)) * e *
              (((M⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) := by
            rw [← Matrix.mul_assoc]
      _ = ((1 : Matrix (Fin n) (Fin n) K) * e) *
              (((M⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      _ = e * (((M⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) := by
            rw [Matrix.one_mul]
  have hR : (((M⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *
      (e * (M : Matrix (Fin n) (Fin n) K)) *
        (((M⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) =
      (((M⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) * e := by
    calc (((M⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *
          (e * (M : Matrix (Fin n) (Fin n) K)) *
            (((M⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)
        = (((M⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *
            ((e * (M : Matrix (Fin n) (Fin n) K)) *
              (((M⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)) := by
            rw [Matrix.mul_assoc]
      _ = (((M⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *
            (e * ((M : Matrix (Fin n) (Fin n) K) *
              (((M⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K))) := by
            rw [Matrix.mul_assoc]
      _ = (((M⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) * (e * 1) := by
            rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      _ = (((M⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) * e := by
            rw [mul_one]
  rw [hL, hR] at h
  exact h.symm

private noncomputable def psuCKAg2_restrictGL {f n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {h : UnitaryFieldData 2 f K} {B : GL (Fin n) K}
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) :
    ↥(psuBlock h B e) →* LinearMap.GeneralLinearGroup K (psuC2dS_V e) where
  toFun x :=
    { val := LinearMap.restrict (Matrix.mulVecLin
          ((((x : AutPSU.XJ h n) : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K))
        (fun w hw => psuCKAg2_mulVec_mem_Ve P hP e he x hw)
      inv := LinearMap.restrict (Matrix.mulVecLin
          (((((x : AutPSU.XJ h n) : GL (Fin n) K))⁻¹ : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K))
        (fun w hw => psuCKAg2_mulVec_mem_Ve_of_comm (((hP.1 e).1 he).2.1.eq)
          (psuCKAg2_inv_comm (psuCKAg2_comm_e P hP e he x)) hw)
      val_inv := by
        apply LinearMap.ext
        intro w
        apply Subtype.ext
        change ((((x : AutPSU.XJ h n) : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *ᵥ
          (((((x : AutPSU.XJ h n) : GL (Fin n) K)⁻¹ : GL (Fin n) K)) :
            Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) = (w : Fin n → K)
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec]
      inv_val := by
        apply LinearMap.ext
        intro w
        apply Subtype.ext
        change ((((x : AutPSU.XJ h n) : GL (Fin n) K)⁻¹ : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K) *ᵥ
          (((((x : AutPSU.XJ h n) : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *ᵥ
            (w : Fin n → K)) = (w : Fin n → K)
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec] }
  map_one' := by
    apply Units.ext
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change (((1 : ↥(psuBlock h B e)) : AutPSU.XJ h n) : GL (Fin n) K) *ᵥ (w : Fin n → K) =
      (w : Fin n → K)
    rw [Subgroup.coe_one, Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]
  map_mul' := by
    intro x y
    apply Units.ext
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change ((((x * y : ↥(psuBlock h B e)) : AutPSU.XJ h n) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) =
      ((((x : ↥(psuBlock h B e)) : AutPSU.XJ h n) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) *ᵥ
        (((((y : ↥(psuBlock h B e)) : AutPSU.XJ h n) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K))
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec]

private lemma psuCKAg2_restrictGL_apply {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {B : GL (Fin n) K}
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (x : ↥(psuBlock h B e))
    (w : psuC2dS_V e) :
    ((psuCKAg2_restrictGL P hP e he x : psuC2dS_V e →ₗ[K] psuC2dS_V e) w : Fin n → K) =
      ((x : AutPSU.XJ h n) : GL (Fin n) K) *ᵥ (w : Fin n → K) :=
  rfl

private noncomputable def psuCKAg2_form {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (e : Matrix (Fin n) (Fin n) K) :
    psuC2dS_V e →ₛₗ[h.bar] psuC2dS_V e →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ h.bar (RingHom.id K)
    (fun u v => psuC2dS_hf h (u : Fin n → K) (v : Fin n → K))
    (fun u u' v => psuC2dS_hf_add_left h (u : Fin n → K) (u' : Fin n → K) (v : Fin n → K))
    (fun c u v => psuC2dS_hf_smul_left h c (u : Fin n → K) (v : Fin n → K))
    (fun u v v' => psuC2dS_hf_add_right h (u : Fin n → K) (v : Fin n → K) (v' : Fin n → K))
    (fun c u v => psuC2dS_hf_smul_right h c (u : Fin n → K) (v : Fin n → K))

private lemma psuCKAg2_form_apply {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (e : Matrix (Fin n) (Fin n) K) (u v : psuC2dS_V e) :
    psuCKAg2_form h e u v = psuC2dS_hf h (u : Fin n → K) (v : Fin n → K) :=
  rfl

private lemma psuCKAg2_form_isSymm {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (e : Matrix (Fin n) (Fin n) K) :
    (psuCKAg2_form h e).IsSymm :=
  ⟨fun u v => by
    rw [psuCKAg2_form_apply, psuCKAg2_form_apply]
    exact (psuC2dS_hf_herm h (v : Fin n → K) (u : Fin n → K)).symm⟩

private lemma psuCKAg2_form_sep {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (e : Matrix (Fin n) (Fin n) K)
    (hee : e * e = e) (hde : psuDag h e = e) :
    (psuCKAg2_form h e).SeparatingLeft := by
  intro u hu
  apply Subtype.ext
  apply psuC2dS_eq_zero_of_forall_hf h (u : Fin n → K)
  intro v
  have h1 : psuC2dS_hf h (u : Fin n → K) (e *ᵥ v) = 0 := by
    have h := hu ⟨e *ᵥ v, ⟨v, Matrix.mulVecLin_apply e v⟩⟩
    rwa [psuCKAg2_form_apply] at h
  have h2 : psuC2dS_hf h (u : Fin n → K) ((1 - e) *ᵥ v) = 0 := by
    have humem : e *ᵥ (u : Fin n → K) = (u : Fin n → K) :=
      psuC2dS_mulVec_eq_of_mem hee u.2
    calc psuC2dS_hf h (u : Fin n → K) ((1 - e) *ᵥ v)
        = psuC2dS_hf h (e *ᵥ (u : Fin n → K)) ((1 - e) *ᵥ v) := by rw [humem]
      _ = psuC2dS_hf h (u : Fin n → K) (psuDag h e *ᵥ ((1 - e) *ᵥ v)) :=
            psuC2dS_hf_dag h e (u : Fin n → K) ((1 - e) *ᵥ v)
      _ = psuC2dS_hf h (u : Fin n → K) (e *ᵥ ((1 - e) *ᵥ v)) := by rw [hde]
      _ = psuC2dS_hf h (u : Fin n → K) 0 := by rw [psuC2dS_e_mul_one_sub hee v]
      _ = 0 := psuC2dS_hf_zero_right h (u : Fin n → K)
  calc psuC2dS_hf h (u : Fin n → K) v
      = psuC2dS_hf h (u : Fin n → K) (e *ᵥ v + (1 - e) *ᵥ v) := by
          rw [psuC2dS_add_one_sub]
    _ = psuC2dS_hf h (u : Fin n → K) (e *ᵥ v) +
          psuC2dS_hf h (u : Fin n → K) ((1 - e) *ᵥ v) :=
          psuC2dS_hf_add_right h _ _ _
    _ = 0 := by rw [h1, h2, add_zero]

private lemma psuCKAg2_fixes {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {B : GL (Fin n) K}
    (e : Matrix (Fin n) (Fin n) K) (hde : psuDag h e = e)
    (x : ↥(psuBlock h B e)) :
    (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (1 - e) = 1 - e := by
  have hxmem : ((x : AutPSU.XJ h n) : GL (Fin n) K) ∈
      Subgroup.centralizer ({B} : Set (GL (Fin n) K)) ⊓ glFixing (1 - psuOrbitIdem h e) :=
    Subgroup.mem_comap.mp x.2
  have h := (Subgroup.mem_inf.mp hxmem).2
  rwa [psuOrbitIdem, if_pos hde] at h

private lemma psuCKAg2_restrict_mem {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {B : GL (Fin n) K}
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (x : ↥(psuBlock h B e)) :
    psuCKAg2_restrictGL P hP e he x ∈ sesqUnitaryGroup (psuCKAg2_form h e) := by
  rw [mem_sesqUnitaryGroup]
  intro u v
  have hu := psuCKAg2_restrictGL_apply P hP e he x u
  have hv := psuCKAg2_restrictGL_apply P hP e he x v
  have hiso := (CFSG.ClassicalGroups.UnitaryFlag.mem_gramSU_iff_isometry.mp
    (x : AutPSU.XJ h n).2).1 (u : Fin n → K) (v : Fin n → K)
  rw [psuCKAg2_form_apply, psuCKAg2_form_apply, hu, hv]
  exact hiso

private noncomputable def psuCKAg2_embed {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (h : UnitaryFieldData 2 f K) {B : GL (Fin n) K}
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) :
    ↥(psuBlock h B e) →* ↥(sesqUnitaryGroup (psuCKAg2_form h e)) :=
  (psuCKAg2_restrictGL P hP e he).codRestrict _ (fun x => psuCKAg2_restrict_mem P hP e he x)

private lemma psuCKAg2_embed_injective {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (h : UnitaryFieldData 2 f K) {B : GL (Fin n) K}
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hde : psuDag h e = e) :
    Function.Injective (psuCKAg2_embed h P hP e he) := by
  intro x y hxy
  have hρ : psuCKAg2_restrictGL P hP e he x = psuCKAg2_restrictGL P hP e he y :=
    Subtype.ext_iff.mp hxy
  have hρlin : (psuCKAg2_restrictGL P hP e he x : psuC2dS_V e →ₗ[K] psuC2dS_V e) =
      (psuCKAg2_restrictGL P hP e he y : psuC2dS_V e →ₗ[K] psuC2dS_V e) :=
    congrArg (fun u : LinearMap.GeneralLinearGroup K (psuC2dS_V e) =>
      (u : psuC2dS_V e →ₗ[K] psuC2dS_V e)) hρ
  have hxv : ∀ w : psuC2dS_V e,
      (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) =
      (((y : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) := by
    intro w
    rw [← psuCKAg2_restrictGL_apply P hP e he x w,
      ← psuCKAg2_restrictGL_apply P hP e he y w, hρlin]
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  rw [← psuC2dS_add_one_sub e v, Matrix.mulVec_add, Matrix.mulVec_add]
  congr 1
  · exact hxv ⟨e *ᵥ v, ⟨v, Matrix.mulVecLin_apply e v⟩⟩
  · rw [Matrix.mulVec_mulVec, psuCKAg2_fixes e hde x,
      Matrix.mulVec_mulVec, psuCKAg2_fixes e hde y]

private theorem psuCKAg2_card_primeFactors_two_three (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (2 ^ a * 3 ^ b).primeFactors.card ≤ 2 := by
  rw [Nat.primeFactors_mul (by positivity) (by positivity),
    Nat.primeFactors_prime_pow ha Nat.prime_two, Nat.primeFactors_prime_pow hb Nat.prime_three]
  exact (Finset.card_union_le _ _).trans (by simp)

private theorem psuCKAg2_isSolvable_of_card_two_three {G : Type*} [Group G] [Finite G] {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (h : Nat.card G = 2 ^ a * 3 ^ b) : Group.IsSolvable G :=
  isSolvable_of_card_primeFactors_le_two
    (h ▸ psuCKAg2_card_primeFactors_two_three a b ha hb)

private lemma psuCKAg2_card {n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 1 K} (e : Matrix (Fin n) (Fin n) K)
    (hee : e * e = e) (hde : psuDag h e = e)
    (hdim : Module.finrank K (psuC2dS_V e) = 3) :
    Nat.card ↥(sesqUnitaryGroup (psuCKAg2_form h e)) = 648 := by
  obtain ⟨hcard, _⟩ := CFSG.LinearGroups.unitary_full_group_order h
    (psuCKAg2_form_isSymm h e) (psuCKAg2_form_sep h e hee hde) (n := 3) hdim (by norm_num)
  have hcard' : (Nat.card ↥(sesqUnitaryGroup (psuCKAg2_form h e)) : ℤ) = 648 := by
    rw [hcard]
    norm_num [Finset.prod_Icc_succ_top]
  exact_mod_cast hcard'

private lemma psuCKA_small_k_three_Q_two_solvable {f n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P)
    (hde : psuDag h e = e) (hψ : psuPsi h X e = e)
    {F : Type} [Field F] [Algebra K F] [Finite F]
    [Module F (LinearMap.range e.mulVecLin)] [IsScalarTower K F (LinearMap.range e.mulVecLin)]
    (π : psuAlg B →ₐ[K] F)
    (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K)
    (hbd : PsuBD e π ψ)
    (hk : Module.finrank F (LinearMap.range e.mulVecLin) = 3)
    (hQ : (2 ^ f) ^ blockDegree (psuAlg B) e = 2) :
    Group.IsSolvable ↥(psuBlock h B e) := by
  have hdpos : 0 < blockDegree (psuAlg B) e := psuC2d_blockDegree_pos S P hP e he
  have hQ' : 2 ^ (f * blockDegree (psuAlg B) e) = 2 := by
    rw [pow_mul]; exact hQ
  have hle : f * blockDegree (psuAlg B) e ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ f * blockDegree (psuAlg B) e := by omega
    have h4 : 4 ≤ 2 ^ (f * blockDegree (psuAlg B) e) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (f * blockDegree (psuAlg B) e) := Nat.pow_le_pow_right (by norm_num) h2
    rw [hQ'] at h4
    omega
  have hfd : f * blockDegree (psuAlg B) e = 1 := by
    have hpos : 0 < f * blockDegree (psuAlg B) e :=
      Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one h.one_le) hdpos
    exact le_antisymm hle (Nat.succ_le_of_lt hpos)
  have hf1 : f = 1 := Nat.dvd_one.mp ⟨blockDegree (psuAlg B) e, hfd.symm⟩
  have hd1 : blockDegree (psuAlg B) e = 1 :=
    Nat.dvd_one.mp ⟨f, by rw [mul_comm]; exact hfd.symm⟩
  subst f
  have hee : e * e = e := ((hP.1 e).1 he).2.1.eq
  have hdimKF : Module.finrank K F = 1 := by rw [hbd.hdim, hd1]
  have hdim : Module.finrank K (psuC2dS_V e) = 3 := by
    have h := Module.finrank_mul_finrank K F (psuC2dS_V e)
    rw [hdimKF, hk, one_mul] at h
    omega
  haveI : Group.IsSolvable ↥(sesqUnitaryGroup (psuCKAg2_form h e)) :=
    psuCKAg2_isSolvable_of_card_two_three (a := 3) (b := 4) (by norm_num) (by norm_num)
      (by rw [psuCKAg2_card e hee hde hdim]; norm_num)
  exact solvable_of_solvable_injective (f := psuCKAg2_embed h P hP e he)
    (psuCKAg2_embed_injective h P hP e he hde)

private lemma psuCKA_Q_eq_two_of_not_four_le {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {B : GL (Fin n) K}
    (e : Matrix (Fin n) (Fin n) K)
    {F : Type} [Field F] [Algebra K F] [Finite F]
    [Module F (LinearMap.range e.mulVecLin)] [IsScalarTower K F (LinearMap.range e.mulVecLin)]
    (π : psuAlg B →ₐ[K] F)
    (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K)
    (hbd : PsuBD e π ψ)
    (h4 : ¬ 4 ≤ (2 ^ f) ^ blockDegree (psuAlg B) e) :
    (2 ^ f) ^ blockDegree (psuAlg B) e = 2 := by
  have hf : 1 ≤ f := h.one_le
  have hF2 : 2 ≤ Nat.card F := by
    haveI : Fintype F := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hd : 1 ≤ blockDegree (psuAlg B) e := by
    by_contra h0
    have h0' : blockDegree (psuAlg B) e = 0 := by omega
    have h1 : Nat.card F = 1 := by rw [hbd.hcard, h0', pow_zero]
    omega
  have hpow : (2 ^ f) ^ blockDegree (psuAlg B) e =
      2 ^ (f * blockDegree (psuAlg B) e) := by rw [pow_mul]
  have hlt : 2 ^ (f * blockDegree (psuAlg B) e) < 4 := by
    rw [← hpow]
    exact Nat.lt_of_not_le h4
  have hfdlt : f * blockDegree (psuAlg B) e < 2 := by
    by_contra hh
    have h2 : 2 ≤ f * blockDegree (psuAlg B) e := by omega
    have h4' : 4 ≤ 2 ^ (f * blockDegree (psuAlg B) e) := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (f * blockDegree (psuAlg B) e) := Nat.pow_le_pow_right (by norm_num) h2
    omega
  have hmul1 : 1 ≤ f * blockDegree (psuAlg B) e := Nat.mul_le_mul hf hd
  have hfd1 : f * blockDegree (psuAlg B) e = 1 := by omega
  rw [hpow, hfd1, pow_one]

private theorem psuCK_kind_A_core {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P)
    (hde : psuDag h e = e) (hψ : psuPsi h X e = e)
    (hns : ¬ Group.IsSolvable ↥(psuBlock h B e))
    {F : Type} [Field F] [Algebra K F] [Finite F] [CharP F 2]
    [Module F (LinearMap.range e.mulVecLin)] [IsScalarTower K F (LinearMap.range e.mulVecLin)]
    (π : psuAlg B →ₐ[K] F)
    (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K)
    (hbd : PsuBD e π ψ) :
    Module.finrank F (LinearMap.range e.mulVecLin) = 2 ∧
      4 ≤ (2 ^ f) ^ blockDegree (psuAlg B) e := by
  have hk_ne_one : Module.finrank F (LinearMap.range e.mulVecLin) ≠ 1 :=
    psuCKA_finrank_ne_one S P hP e he hns π ψ hbd
  have hk_pos : 0 < Module.finrank F (LinearMap.range e.mulVecLin) := hbd.hpos
  have hk_two : 2 ≤ Module.finrank F (LinearMap.range e.mulVecLin) := by omega
  have hk_eq : Module.finrank F (LinearMap.range e.mulVecLin) = 2 := by
    by_contra hne
    have hk_three : 3 ≤ Module.finrank F (LinearMap.range e.mulVecLin) := by omega
    by_cases hQ : (2 ^ f) ^ blockDegree (psuAlg B) e = 2
    · by_cases hk3 : Module.finrank F (LinearMap.range e.mulVecLin) = 3
      · exact absurd
          (psuCKA_small_k_three_Q_two_solvable S P hP e he hde hψ π ψ hbd hk3 hQ) hns
      · exact psuCKA_k_ge_three_impossible S P hP e he hde hψ π ψ hbd hk_three
          (fun h => hk3 h.2)
    · exact psuCKA_k_ge_three_impossible S P hP e he hde hψ π ψ hbd hk_three
        (fun h => hQ h.1)
  refine ⟨hk_eq, ?_⟩
  by_contra h4
  have hQ2 : (2 ^ f) ^ blockDegree (psuAlg B) e = 2 :=
    psuCKA_Q_eq_two_of_not_four_le h e π ψ hbd h4
  exact hns (psuCKA_small_k_two_Q_two_solvable S P hP e he hde π ψ hbd hk_eq hQ2)

private lemma psuCT_kind_four_facts {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (e : Matrix (Fin n) (Fin n) K) (hk : psuKind h X B e = 4) :
    psuTheta h X e = e ∧ psuDag h e ≠ e := by
  have hde : psuDag h e ≠ e := by
    intro hde
    unfold psuKind at hk
    rw [if_pos hde] at hk
    split_ifs at hk <;> omega
  have hψdag' : psuPsi h X e = psuDag h e := by
    by_contra hψdag
    unfold psuKind at hk
    rw [if_neg hde] at hk
    by_cases hψ : psuPsi h X e = e
    · rw [if_pos hψ] at hk
      split_ifs at hk <;> omega
    · rw [if_neg hψ, if_neg hψdag] at hk
      omega
  refine ⟨?_, hde⟩
  have h1 : psuTheta h X (psuDag h e) = psuDag h e := hψdag'
  have h2 := congrArg (psuDag h) h1
  rw [← psuTheta_dag h X S.X_mem S.X_sq (psuDag h e), psuDag_dag] at h2
  exact h2

private lemma psuCT_kind_three_facts {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (e : Matrix (Fin n) (Fin n) K) (hk : psuKind h X B e = 3) :
    psuDag h e ≠ e ∧ psuPsi h X e = e ∧ ¬ psuPsiTrivial h X B e := by
  have hde : psuDag h e ≠ e := by
    intro hde
    unfold psuKind at hk
    rw [if_pos hde] at hk
    split_ifs at hk <;> omega
  have hψ : psuPsi h X e = e := by
    by_contra hψ
    unfold psuKind at hk
    rw [if_neg hde, if_neg hψ] at hk
    split_ifs at hk <;> omega
  have hnt : ¬ psuPsiTrivial h X B e := by
    intro htr
    unfold psuKind at hk
    rw [if_neg hde, if_pos hψ, if_pos htr] at hk
    omega
  exact ⟨hde, hψ, hnt⟩

private lemma psuCT_kind_two_facts {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (e : Matrix (Fin n) (Fin n) K) (hk : psuKind h X B e = 2) :
    psuDag h e ≠ e ∧ psuPsi h X e = e ∧ psuPsiTrivial h X B e := by
  have hde : psuDag h e ≠ e := by
    intro hde
    unfold psuKind at hk
    rw [if_pos hde] at hk
    split_ifs at hk <;> omega
  have hψ : psuPsi h X e = e := by
    by_contra hψ
    unfold psuKind at hk
    rw [if_neg hde, if_neg hψ] at hk
    split_ifs at hk <;> omega
  have htr : psuPsiTrivial h X B e := by
    by_contra htr
    unfold psuKind at hk
    rw [if_neg hde, if_pos hψ, if_neg htr] at hk
    omega
  exact ⟨hde, hψ, htr⟩

private lemma psuCT_kind_zero_facts {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (e : Matrix (Fin n) (Fin n) K) (hk : psuKind h X B e = 0) :
    psuDag h e = e ∧ psuPsi h X e = e := by
  have hde : psuDag h e = e := by
    by_contra hde
    unfold psuKind at hk
    rw [if_neg hde] at hk
    split_ifs at hk <;> omega
  have hψ : psuPsi h X e = e := by
    by_contra hψ
    unfold psuKind at hk
    rw [if_pos hde, if_neg hψ] at hk
    omega
  exact ⟨hde, hψ⟩

theorem psuGraph_kind_unstable {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P)
    (hk : psuKind h X B e = 1 ∨ psuKind h X B e = 5) :
    Group.IsSolvable ↥(psuBlock h B e) := by
  exact psuCK_kind_unstable_core S P hP e he hk

theorem psuGraph_kind_D {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hk : psuKind h X B e = 4) :
    Group.IsSolvable ↥(psuBlock h B e) := by
  obtain ⟨F, hFld, hAlg, hFin, hChar, π, hM, hT, ψ, hπ, hker, hdim, hcard, hact, hrank, hpos,
    hψinj, hψw, hψfix, hψe, hψB⟩ := exists_blockEmbed S.odd rfl ((hP.1 e).1 he)
  letI : Field F := hFld
  letI : Algebra K F := hAlg
  letI : Finite F := hFin
  letI : CharP F 2 := hChar
  letI : Module F (LinearMap.range e.mulVecLin) := hM
  letI : IsScalarTower K F (LinearMap.range e.mulVecLin) := hT
  obtain ⟨hθe, hne⟩ := psuCT_kind_four_facts S e hk
  exact psuCK_kind_D_core S P hP e he hθe hne π ψ
    ⟨hπ, hker, hdim, hcard, hact, hrank, hpos, hψinj, hψw, hψfix, hψe, hψB⟩

theorem psuGraph_kind_C2 {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hk : psuKind h X B e = 3) :
    Group.IsSolvable ↥(psuBlock h B e) := by
  obtain ⟨F, hFld, hAlg, hFin, hChar, π, hM, hT, ψ, hπ, hker, hdim, hcard, hact, hrank, hpos,
    hψinj, hψw, hψfix, hψe, hψB⟩ := exists_blockEmbed S.odd rfl ((hP.1 e).1 he)
  letI : Field F := hFld
  letI : Algebra K F := hAlg
  letI : Finite F := hFin
  letI : CharP F 2 := hChar
  letI : Module F (LinearMap.range e.mulVecLin) := hM
  letI : IsScalarTower K F (LinearMap.range e.mulVecLin) := hT
  obtain ⟨hne, hψ, hnt⟩ := psuCT_kind_three_facts e hk
  exact psuCK_kind_C2_core S P hP e he hne hψ hnt π ψ
    ⟨hπ, hker, hdim, hcard, hact, hrank, hpos, hψinj, hψw, hψfix, hψe, hψB⟩

theorem psuGraph_kind_C1 {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hk : psuKind h X B e = 2)
    (hns : ¬ Group.IsSolvable ↥(psuBlock h B e)) :
    Matrix.rank e = 2 * blockDegree (psuAlg B) e := by
  obtain ⟨F, hFld, hAlg, hFin, hChar, π, hM, hT, ψ, hπ, hker, hdim, hcard, hact, hrank, hpos,
    hψinj, hψw, hψfix, hψe, hψB⟩ := exists_blockEmbed S.odd rfl ((hP.1 e).1 he)
  letI : Field F := hFld
  letI : Algebra K F := hAlg
  letI : Finite F := hFin
  letI : CharP F 2 := hChar
  letI : Module F (LinearMap.range e.mulVecLin) := hM
  letI : IsScalarTower K F (LinearMap.range e.mulVecLin) := hT
  obtain ⟨hne, hψ, htriv⟩ := psuCT_kind_two_facts e hk
  have hk2 := psuCK_kind_C1_core S P hP e he hne hψ htriv hns π ψ
    ⟨hπ, hker, hdim, hcard, hact, hrank, hpos, hψinj, hψw, hψfix, hψe, hψB⟩
  rw [hrank, hdim, hk2]
  exact Nat.mul_comm (blockDegree (psuAlg B) e) 2

theorem psuGraph_kind_A {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hk : psuKind h X B e = 0)
    (hns : ¬ Group.IsSolvable ↥(psuBlock h B e)) :
    Matrix.rank e = 2 * blockDegree (psuAlg B) e ∧ 4 ≤ (2 ^ f) ^ blockDegree (psuAlg B) e := by
  obtain ⟨F, hFld, hAlg, hFin, hChar, π, hM, hT, ψ, hπ, hker, hdim, hcard, hact, hrank, hpos,
    hψinj, hψw, hψfix, hψe, hψB⟩ := exists_blockEmbed S.odd rfl ((hP.1 e).1 he)
  letI : Field F := hFld
  letI : Algebra K F := hAlg
  letI : Finite F := hFin
  letI : CharP F 2 := hChar
  letI : Module F (LinearMap.range e.mulVecLin) := hM
  letI : IsScalarTower K F (LinearMap.range e.mulVecLin) := hT
  obtain ⟨hde, hψ⟩ := psuCT_kind_zero_facts e hk
  have hc := psuCK_kind_A_core S P hP e he hde hψ hns π ψ
    ⟨hπ, hker, hdim, hcard, hact, hrank, hpos, hψinj, hψw, hψfix, hψe, hψB⟩
  refine ⟨?_, hc.2⟩
  rw [hrank, hdim, hc.1]
  exact Nat.mul_comm (blockDegree (psuAlg B) e) 2

end CFSG.StandardType
