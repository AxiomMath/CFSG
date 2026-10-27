module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKU43Cent5
import CFSG.RankThree.PartTwo.Sec4.Item426A6U43
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKU43

open Matrix CFSG.Blueprint

section Linear

variable {L : Type*} [Field L] [CharP L 3]

theorem exists_eig_of_unitary {B : Matrix (Fin 4) (Fin 4) L}
    (hu : (B.map (frobenius L 3))ᵀ * B = 1) {μ β : L} {v : Fin 4 → L}
    (hv : v ≠ 0) (hBv : B *ᵥ v = μ • v) (hμβ : μ ^ 3 * β = 1) :
    ∃ w, w ≠ 0 ∧ B *ᵥ w = β • w := by
  set w : Fin 4 → L := fun i => (v i) ^ 3 with hw
  have hw0 : w ≠ 0 := by
    intro h0
    apply hv
    funext i
    have := congrFun h0 i
    simp only [hw, Pi.zero_apply] at this
    exact (pow_eq_zero_iff (by norm_num)).mp this
  have h1 : B.map (frobenius L 3) *ᵥ w = μ ^ 3 • w := by
    funext i
    have := RingHom.map_mulVec (frobenius L 3) B v i
    rw [hBv] at this
    simpa [frobenius_def, mul_pow, hw, Function.comp_def] using this.symm
  have h2 : w ᵥ* B = β • w := by
    have h3 : w ᵥ* ((B.map (frobenius L 3))ᵀ * B) = w := by rw [hu, vecMul_one]
    rw [← vecMul_vecMul, vecMul_transpose, h1, smul_vecMul] at h3
    calc w ᵥ* B = (β * μ ^ 3) • (w ᵥ* B) := by rw [mul_comm, hμβ, one_smul]
      _ = β • w := by rw [mul_smul, h3]
  have hdet : (B - Matrix.scalar (Fin 4) β).det = 0 := by
    rw [← exists_vecMul_eq_zero_iff]
    refine ⟨w, hw0, ?_⟩
    rw [vecMul_sub, h2, scalar_apply]
    funext i
    simp [mul_comm]
  obtain ⟨w', hw', h⟩ := exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨w', hw', ?_⟩
  rw [sub_mulVec, sub_eq_zero, scalar_apply] at h
  rw [h]
  funext i
  simp [mulVec_diagonal]

theorem core_seven [IsAlgClosed L] {B : Matrix (Fin 4) (Fin 4) L}
    (hu : (B.map (frobenius L 3))ᵀ * B = 1) (h7 : B ^ 7 = 1) (hB1 : B ≠ 1) (hdetB : B.det = 1) :
    ∃ v : Fin 4 → L, v ≠ 0 ∧
      (∀ A : Matrix (Fin 4) (Fin 4) L, A * B = B * A →
        (A.map (frobenius L 3))ᵀ * A = 1 → A.det = 1 →
        ∃ c : L, A *ᵥ v = c • v ∧ c ^ 28 = 1 ∧ (c ^ 4 = 1 → A = Matrix.scalar (Fin 4) c)) ∧
      (∀ Y : Matrix (Fin 4) (Fin 4) L, Y * B = B ^ 6 * Y → Y *ᵥ v = 0) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h7L : (7 : L) ≠ 0 := by
    intro h
    have h' : ((7 : ℕ) : L) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff L 3] at h'
    norm_num at h'
  obtain ⟨μ, v, hv, hBv, hμ1⟩ : ∃ μ : L, ∃ v : Fin 4 → L, v ≠ 0 ∧ B *ᵥ v = μ • v ∧ μ ≠ 1 := by
    set Q := B ^ 6 + B ^ 5 + B ^ 4 + B ^ 3 + B ^ 2 + B + 1 with hQ
    have hQB : Q * (B - 1) = B ^ 7 - 1 := by rw [hQ]; noncomm_ring
    have hcomm : B * Q = Q * B := by rw [hQ]; noncomm_ring
    obtain ⟨u, hu'⟩ : ∃ u, (B - 1) *ᵥ u ≠ 0 := by
      by_contra hcon
      apply hB1
      have h0 : B - 1 = 0 := Matrix.mulVec_injective (funext fun u => by
        by_contra hne
        exact hcon ⟨u, by simpa using hne⟩)
      exact sub_eq_zero.mp h0
    set W := LinearMap.ker (Matrix.toLin' Q) with hW
    have hinv : ∀ y ∈ W, Matrix.toLin' B y ∈ W := by
      intro y hy
      rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hy ⊢
      rw [Matrix.toLin'_apply, mulVec_mulVec, ← hcomm, ← mulVec_mulVec, hy, mulVec_zero]
    have hmem : (B - 1) *ᵥ u ∈ W := by
      rw [LinearMap.mem_ker, Matrix.toLin'_apply, mulVec_mulVec, hQB, h7, sub_self, zero_mulVec]
    have hne : W ≠ ⊥ := fun h => hu' (by rw [h] at hmem; exact (Submodule.mem_bot L).mp hmem)
    have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hne
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue ((Matrix.toLin' B).restrict hinv)
    obtain ⟨y, hy⟩ := hμ.exists_hasEigenvector
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hy
    have hBy : B *ᵥ (y : Fin 4 → L) = μ • (y : Fin 4 → L) := by
      have := congrArg Subtype.val hy.1
      simpa [LinearMap.restrict_apply, Matrix.toLin'_apply] using this
    have hy0 : (y : Fin 4 → L) ≠ 0 := fun h => hy.2 (Subtype.ext h)
    refine ⟨μ, y, hy0, hBy, ?_⟩
    rintro rfl
    have hpow : ∀ k : ℕ, B ^ k *ᵥ (y : Fin 4 → L) = (y : Fin 4 → L) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ← mulVec_mulVec, hBy, one_smul, ih]
    have hQy : Q *ᵥ (y : Fin 4 → L) = (7 : L) • (y : Fin 4 → L) := by
      have h1 := hpow 1
      rw [pow_one] at h1
      rw [hQ, add_mulVec, add_mulVec, add_mulVec, add_mulVec, add_mulVec, add_mulVec, hpow, hpow,
        hpow, hpow, hpow, h1, one_mulVec,
        show (7 : L) = 1 + 1 + 1 + 1 + 1 + 1 + 1 by norm_num, add_smul, add_smul, add_smul,
        add_smul, add_smul, add_smul, one_smul]
    have hy' := y.2
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, hQy] at hy'
    exact hy0 ((smul_eq_zero.mp hy').resolve_left h7L)
  have hpowv : ∀ k : ℕ, B ^ k *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← mulVec_mulVec, hBv, mulVec_smul, ih, smul_smul, pow_succ']
  have hμ7 : μ ^ 7 = 1 := by
    have h := hpowv 7
    rw [h7, one_mulVec] at h
    by_contra hne
    apply hv
    have h' : (μ ^ 7 - 1) • v = 0 := by rw [sub_smul, ← h, one_smul, sub_self]
    exact (smul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hne)
  have hμ0 : μ ≠ 0 := by rintro rfl; norm_num at hμ7
  have hprim : IsPrimitiveRoot μ 7 := (orderOf_eq_prime hμ7 hμ1) ▸ IsPrimitiveRoot.orderOf μ
  have h14 : μ ^ 14 = 1 := by rw [show 14 = 7 * 2 by norm_num, pow_mul, hμ7, one_pow]
  obtain ⟨v₄, hv₄, hBv₄⟩ := exists_eig_of_unitary hu hv hBv (β := μ ^ 4)
    (by rw [← pow_add]; exact hμ7)
  obtain ⟨v₂, hv₂, hBv₂⟩ := exists_eig_of_unitary hu hv₄ hBv₄ (β := μ ^ 2)
    (by rw [← pow_mul, ← pow_add]; exact h14)
  set e : Fin 4 → ℕ := ![0, 1, 2, 4] with he
  have he7 : ∀ i, e i < 7 := by intro i; fin_cases i <;> simp [he]
  have he_inj : ∀ i j, μ ^ e i = μ ^ e j → i = j := by
    intro i j h
    have := hprim.pow_inj (he7 i) (he7 j) h
    fin_cases i <;> fin_cases j <;> simp [he] at this ⊢
  set v3 : Fin 3 → (Fin 4 → L) := ![v, v₂, v₄] with hv3
  have hli3 : LinearIndependent L v3 := by
    refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' B)
      (fun i : Fin 3 => μ ^ e i.succ) (fun i j h => Fin.succ_injective _ (he_inj _ _ h)) v3
      fun i => ?_
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    fin_cases i
    · exact ⟨by simpa [hv3, he] using hBv, by simpa [hv3] using hv⟩
    · exact ⟨by simpa [hv3, he] using hBv₂, by simpa [hv3] using hv₂⟩
    · exact ⟨by simpa [hv3, he] using hBv₄, by simpa [hv3] using hv₄⟩
  set f := Matrix.toLinAlgEquiv' B with hf
  have hf7 : f ^ 7 = 1 := by rw [hf, ← map_pow, h7, map_one]
  have hsemi : Module.End.IsSemisimple (f : Module.End L (Fin 4 → L)) := by
    refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := Polynomial.X ^ 7 - 1) ?_ ?_
    · simpa using (Polynomial.separable_X_pow_sub_C (1 : L) h7L one_ne_zero).squarefree
    · simp [hf7]
  obtain ⟨ν, u, hBu, hnotin⟩ : ∃ ν : L, ∃ u : Fin 4 → L, B *ᵥ u = ν • u ∧
      u ∉ Submodule.span L (Set.range v3) := by
    by_contra hcon
    push Not at hcon
    have hle : ⨆ β : L, Module.End.eigenspace (f : Module.End L (Fin 4 → L)) β ≤
        Submodule.span L (Set.range v3) := by
      refine iSup_le fun β x hx => hcon β x ?_
      rw [Module.End.mem_eigenspace_iff] at hx
      simpa [hf, Matrix.toLinAlgEquiv'_apply] using hx
    rw [hsemi.iSup_eigenspace_eq_top] at hle
    have h1 := Submodule.finrank_mono hle
    rw [finrank_top, Module.finrank_fin_fun] at h1
    have h2 := finrank_range_le_card (R := L) v3
    simp only [Fintype.card_fin] at h2
    have := h1.trans h2
    omega
  set vec : Fin 4 → (Fin 4 → L) := ![u, v, v₂, v₄] with hvec_def
  have hli : LinearIndependent L vec := by
    have := linearIndependent_fin_cons.mpr ⟨hli3, hnotin⟩
    exact this
  have hcard : Fintype.card (Fin 4) = Module.finrank L (Fin 4 → L) := by simp
  set bs := basisOfLinearIndependentOfCardEqFinrank hli hcard with hbs_def
  have hbs : ∀ i, bs i = vec i := fun i => by simp [hbs_def]
  have hdiag : ∀ (M : Matrix (Fin 4) (Fin 4) L) (d : Fin 4 → L),
      (∀ k, M *ᵥ vec k = d k • vec k) → M.det = ∏ k, d k := by
    intro M d hMd
    have hmat : LinearMap.toMatrix bs bs (Matrix.toLin' M) = Matrix.diagonal d := by
      ext i j
      rw [LinearMap.toMatrix_apply, Matrix.toLin'_apply, hbs, hMd j, ← hbs, map_smul,
        bs.repr_self, Matrix.diagonal_apply, Finsupp.smul_apply, Finsupp.single_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Ne.symm hij]
    rw [← LinearMap.det_toLin' M, ← LinearMap.det_toMatrix bs, hmat, Matrix.det_diagonal]
  have hν : ν = 1 := by
    have h := hdiag B ![ν, μ, μ ^ 2, μ ^ 4] (by
      intro k
      fin_cases k
      · simpa [hvec_def] using hBu
      · simpa [hvec_def] using hBv
      · simpa [hvec_def] using hBv₂
      · simpa [hvec_def] using hBv₄)
    rw [hdetB, Fin.prod_univ_four] at h
    have h' : 1 = ν * μ * μ ^ 2 * μ ^ 4 := h
    have : ν * μ ^ 7 = 1 := by linear_combination -h'
    rwa [hμ7, mul_one] at this
  subst hν
  set lam : Fin 4 → L := fun i => μ ^ e i with hlam_def
  have hvec : ∀ i, B *ᵥ vec i = lam i • vec i := by
    intro i
    fin_cases i
    · simpa [hvec_def, hlam_def, he] using hBu
    · simpa [hvec_def, hlam_def, he] using hBv
    · simpa [hvec_def, hlam_def, he] using hBv₂
    · simpa [hvec_def, hlam_def, he] using hBv₄
  have hvec0 : ∀ i, vec i ≠ 0 := fun i => hli.ne_zero i
  have hlam : Function.Injective lam := fun i j h => he_inj i j h
  have heig : ∀ (β : L) (x : Fin 4 → L), B *ᵥ x = β • x → ∀ j, lam j ≠ β → bs.repr x j = 0 := by
    intro β x hBx j hj
    set c := bs.repr x with hc
    have hxsum : x = ∑ j, c j • vec j := by
      conv_lhs => rw [← bs.sum_repr x]
      simp only [hbs]
      rfl
    have h1 : B *ᵥ x = ∑ j, (lam j * c j) • bs j := by
      rw [hxsum, mulVec_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mulVec_smul, hvec i, smul_smul, hbs, mul_comm]
    have h2 : β • x = ∑ j, (β * c j) • bs j := by
      rw [hxsum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, hbs]
    have h3 := congrArg (fun y => bs.repr y j) (h1.symm.trans (hBx.trans h2))
    simp only [bs.repr_sum_self] at h3
    have h4 : (lam j - β) * c j = 0 := by rw [sub_mul, h3, sub_self]
    exact (mul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr hj)
  set σ : Fin 4 → Fin 4 := ![0, 3, 1, 2] with hσ
  have hlamσ : ∀ k, lam k ^ 3 * lam (σ k) = 1 := by
    intro k
    fin_cases k <;> simp [hlam_def, hσ, he, ← pow_mul, ← pow_add, hμ7, h14] <;>
      first | done | (rw [← pow_succ]; exact hμ7)
  have hlam0 : ∀ k, lam k ≠ 0 := fun k => pow_ne_zero _ hμ0
  have hσ_unique : ∀ k j, lam k ^ 3 * lam j = 1 → j = σ k := by
    intro k j h
    apply hlam
    exact mul_left_cancel₀ (pow_ne_zero 3 (hlam0 k)) (h.trans (hlamσ k).symm)
  have hpair : ∀ k, (fun i => vec k i ^ 3) ⬝ᵥ vec (σ k) ≠ 0 := by
    intro k h0
    have hall : ∀ j, (fun i => vec k i ^ 3) ⬝ᵥ vec j = 0 := by
      intro j
      by_cases hj : j = σ k
      · rw [hj]; exact h0
      · have h := pair_eig hu (hvec k) (hvec j)
        have h' : (lam k ^ 3 * lam j - 1) * ((fun i => vec k i ^ 3) ⬝ᵥ vec j) = 0 := by
          rw [sub_mul, h, one_mul, sub_self]
        exact (mul_eq_zero.mp h').resolve_left
          (sub_ne_zero.mpr fun h1 => hj (hσ_unique k j h1))
    have hzero : ∀ w : Fin 4 → L, (fun i => vec k i ^ 3) ⬝ᵥ w = 0 := by
      intro w
      rw [← bs.sum_repr w, dotProduct_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [dotProduct_smul, hbs, hall j, smul_zero]
    apply hvec0 k
    funext i
    have := hzero (Pi.single i 1)
    rw [dotProduct_single, mul_one] at this
    exact (pow_eq_zero_iff (by norm_num)).mp this
  refine ⟨v, hv, ?_, ?_⟩
  · intro A hAB hAu hdet
    have hAvec : ∀ k, ∃ c : L, A *ᵥ vec k = c • vec k := by
      intro k
      set x := A *ᵥ vec k with hx
      have hBx : B *ᵥ x = lam k • x := by
        rw [hx, mulVec_mulVec, ← hAB, ← mulVec_mulVec, hvec k, mulVec_smul]
      refine ⟨bs.repr x k, ?_⟩
      conv_lhs => rw [← bs.sum_repr x]
      rw [Finset.sum_eq_single k (fun j _ hjk => by
        rw [heig _ x hBx j (hlam.ne hjk), zero_smul]) (by simp), hbs]
    choose cf hcf using hAvec
    have hrel : ∀ k, cf k ^ 3 * cf (σ k) = 1 := by
      intro k
      have h := pair_eig hAu (hcf k) (hcf (σ k))
      have h' : (cf k ^ 3 * cf (σ k) - 1) * ((fun i => vec k i ^ 3) ⬝ᵥ vec (σ k)) = 0 := by
        rw [sub_mul, h, one_mul, sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right (hpair k))
    have hdetc := hdiag A cf hcf
    have hr1 : cf 1 ^ 3 * cf 3 = 1 := hrel 1
    have hr2 : cf 2 ^ 3 * cf 1 = 1 := hrel 2
    have hr3 : cf 3 ^ 3 * cf 2 = 1 := hrel 3
    rw [hdet, Fin.prod_univ_four] at hdetc
    set c := cf 1 with hc
    have hc0 : c ≠ 0 := by rintro h; rw [h] at hr1; simp at hr1
    have e3 : cf 3 = (c ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right hr1
    have e2 : cf 2 = c ^ 9 := by
      rw [e3, inv_pow, ← pow_mul] at hr3
      rw [← mul_inv_cancel_left₀ (pow_ne_zero (3 * 3) hc0) (cf 2), hr3, mul_one]
    have h28 : c ^ 28 = 1 := by
      rw [e2, ← pow_mul, ← pow_succ] at hr2
      exact hr2
    refine ⟨c, by rw [show v = vec 1 from rfl]; exact hcf 1, h28, fun h4 => ?_⟩
    have hc3 : (c ^ 3)⁻¹ = c := by
      rw [inv_eq_iff_eq_inv, ← mul_eq_one_iff_eq_inv₀ hc0, ← pow_succ, h4]
    have hc9 : c ^ 9 = c := by
      rw [show 9 = 4 * 2 + 1 by norm_num, pow_succ, pow_mul, h4, one_pow, one_mul]
    have e0 : cf 0 = c := by
      rw [e2, e3, hc9, hc3] at hdetc
      have h1 : cf 0 * c ^ 3 = 1 := by rw [hdetc]; ring
      rw [eq_inv_of_mul_eq_one_left h1, hc3]
    have hall : ∀ k, cf k = c := by
      intro k
      fin_cases k
      · exact e0
      · rfl
      · exact e2.trans hc9
      · exact e3.trans hc3
    have hlin : Matrix.toLin' A = Matrix.toLin' (Matrix.scalar (Fin 4) c) := by
      apply bs.ext
      intro i
      rw [hbs, Matrix.toLin'_apply, Matrix.toLin'_apply, hcf, hall, scalar_apply]
      funext j
      rw [mulVec_diagonal]
      simp [mul_comm]
    exact Matrix.toLin'.injective hlin
  · intro Y hY
    set w := Y *ᵥ v with hw
    have hB6 : B ^ 6 *ᵥ w = μ • w := by
      rw [hw, mulVec_mulVec, ← hY, ← mulVec_mulVec, hBv, mulVec_smul]
    have hBw : B *ᵥ w = μ ^ 6 • w := by
      have h1 : B *ᵥ (B ^ 6 *ᵥ w) = w := by rw [mulVec_mulVec, ← pow_succ', h7, one_mulVec]
      rw [hB6, mulVec_smul] at h1
      calc B *ᵥ w = (μ ^ 6 * μ) • (B *ᵥ w) := by rw [← pow_succ, hμ7, one_smul]
        _ = μ ^ 6 • w := by rw [mul_smul, h1]
    have hrepr : ∀ j, bs.repr w j = 0 := by
      intro j
      refine heig _ w hBw j fun h => ?_
      have h6 : e j = 6 := hprim.pow_inj (he7 j) (by norm_num) h
      fin_cases j <;> simp [he] at h6
    rw [← bs.sum_repr w]
    exact Finset.sum_eq_zero fun j _ => by rw [hrepr j, zero_smul]

end Linear

section U43

open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.A318P (projSU_of_statedClassicalModel_gen)
open CFSG.RankThree.PartTwo.Sec4.Item426 (pow_mul_four_eq_one)

theorem seven_facts_projSU (x : projSU 4 3 1) (hx : orderOf x = 7) :
    Nat.card (Subgroup.centralizer ({x} : Set (projSU 4 3 1))) ≤ 7 ∧
      ∀ t : projSU 4 3 1, t * x * t⁻¹ ≠ x⁻¹ := by
  classical
  set K := GaloisField 3 (2 * 1) with hKdef
  have hU : UnitaryFieldData 3 1 K :=
    ⟨Nat.prime_three, le_rfl, GaloisField.card 3 (2 * 1) (by norm_num)⟩
  have : CharP K 3 := hU.charP
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hlift : ∀ z : projSU 4 3 1, ∃ Z : GL (Fin 4) K, Z ∈ unitarySU 3 1 K 4 ∧
      ProjGenLinGroup.mk Z = (z : ProjGenLinGroup (Fin 4) K) := fun z =>
    Subgroup.mem_map.mp
      ((SetLike.ext_iff.mp (CFSG.RankThree.PartTwo.Sec4.projSU_eq_map_statedSU 4 3 1) _).mp z.2)
  choose Lf hLfmem hLf using hlift
  have hbar : (⇑hU.bar : K → K) = ⇑(frobenius K 3) :=
    funext fun c => by rw [hU.bar_apply, frobenius_def, pow_one]
  have hdet1 : ∀ Z ∈ unitarySU 3 1 K 4, Matrix.GeneralLinearGroup.det Z = 1 := fun Z hZ =>
    Units.ext (by simpa using ((mem_unitarySU_iff hU).mp hZ).1)
  have hunit : ∀ Z ∈ unitarySU 3 1 K 4,
      ((Z : Matrix (Fin 4) (Fin 4) K).map (frobenius K 3))ᵀ * Z = 1 := fun Z hZ => by
    have h := ((mem_unitarySU_iff hU).mp hZ).2
    rwa [hbar] at h
  set X := Lf x with hXdef
  have hx7 : (x : ProjGenLinGroup (Fin 4) K) ^ 7 = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx] at h
    rw [← Subgroup.coe_pow, h, OneMemClass.coe_one]
  have hx1 : (x : ProjGenLinGroup (Fin 4) K) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    norm_num at hx
  set B := X ^ 8 with hB
  have hBmem : B ∈ unitarySU 3 1 K 4 := pow_mem (hLfmem x) 8
  have hB7 : B ^ 7 = 1 := by
    rw [hB, ← pow_mul, show 8 * 7 = 7 * 4 * 2 by norm_num, pow_mul,
      pow_mul_four_eq_one ((mem_unitarySU_iff hU).mp (hLfmem x)).1 (by rw [hLf, hx7]), one_pow]
  have hBx : ProjGenLinGroup.mk B = (x : ProjGenLinGroup (Fin 4) K) := by
    rw [hB, map_pow, hLf, show 8 = 7 + 1 by norm_num, pow_succ, hx7, one_mul]
  have hB1 : B ≠ 1 := fun h => hx1 (by rw [← hBx, h, map_one])
  have hconj7 : ∀ T : GL (Fin 4) K, (T * B * T⁻¹) ^ 7 = 1 := fun T => by
    rw [show T * B * T⁻¹ = MulAut.conj T B by simp, ← map_pow, hB7, map_one]
  have hconjdet : ∀ T : GL (Fin 4) K,
      Matrix.GeneralLinearGroup.det (T * B * T⁻¹) = Matrix.GeneralLinearGroup.det B := fun T => by
    simp [map_mul, map_inv, mul_comm]
  set L := AlgebraicClosure K
  set ι := (algebraMap K L).mapMatrix (m := Fin 4) with hι
  have hιunit : ∀ Z ∈ unitarySU 3 1 K 4,
      ((ι (Z : Matrix (Fin 4) (Fin 4) K)).map (frobenius L 3))ᵀ * ι Z = 1 := fun Z hZ =>
    unitary_mapMatrix (hunit Z hZ)
  have hιdet : ∀ Z ∈ unitarySU 3 1 K 4, (ι (Z : Matrix (Fin 4) (Fin 4) K)).det = 1 := by
    intro Z hZ
    rw [hι, ← RingHom.map_det, ((mem_unitarySU_iff hU).mp hZ).1, map_one]
  have hιinj : Function.Injective ι := Matrix.map_injective (algebraMap K L).injective
  obtain ⟨v, hv, hcore, hreal⟩ := core_seven (B := ι B) (hιunit B hBmem)
    (by rw [← map_pow, ← Units.val_pow_eq_pow_val, hB7, Units.val_one, map_one])
    (fun h => hB1 (Units.ext (hιinj (by rw [h, Units.val_one, map_one]))))
    (hιdet B hBmem)
  have hιcomm : ∀ Z : GL (Fin 4) K, Z * B = B * Z →
      ι (Z : Matrix (Fin 4) (Fin 4) K) * ι B = ι B * ι Z := fun Z h => by
    rw [← map_mul, ← map_mul, ← Units.val_mul, ← Units.val_mul, h]
  refine ⟨?_, ?_⟩
  ·
    have hcomm : ∀ y : Subgroup.centralizer ({x} : Set (projSU 4 3 1)),
        Lf y * B = B * Lf y := by
      intro y
      have hyx : (y : projSU 4 3 1) * x = x * y :=
        (Subgroup.mem_centralizer_iff.mp y.2 x (Set.mem_singleton x)).symm
      have h := eq_of_mk_eq (n := 7) (A := Lf y * B * (Lf y)⁻¹) (C := B) (by norm_num)
        (hconj7 _) hB7 (hconjdet _)
        (by
          rw [map_mul, map_mul, map_inv, hLf, hBx, mul_inv_eq_iff_eq_mul]
          exact_mod_cast hyx)
      rwa [mul_inv_eq_iff_eq_mul] at h
    have hc : ∀ y : Subgroup.centralizer ({x} : Set (projSU 4 3 1)),
        ∃ c : L, ι (Lf y : Matrix (Fin 4) (Fin 4) K) *ᵥ v = c • v ∧ c ^ 28 = 1 := fun y => by
      obtain ⟨c, h1, h2, -⟩ := hcore _ (hιcomm _ (hcomm y)) (hιunit _ (hLfmem y))
        (hιdet _ (hLfmem y))
      exact ⟨c, h1, h2⟩
    choose cf hcfv hcf28 using hc
    set R := (Polynomial.nthRoots 7 (1 : L)).toFinset with hR
    have hmemR : ∀ y, cf y ^ 4 ∈ R := fun y => by
      rw [hR, Multiset.mem_toFinset, Polynomial.mem_nthRoots (by norm_num), ← pow_mul]
      exact hcf28 y
    have hinj : Function.Injective (fun y => (⟨cf y ^ 4, hmemR y⟩ : R)) := by
      intro y y' hyy
      have h4 : cf y ^ 4 = cf y' ^ 4 := congrArg Subtype.val hyy
      set Z := Lf y' * (Lf y)⁻¹ with hZ
      have hZmem : Z ∈ unitarySU 3 1 K 4 := mul_mem (hLfmem y') (inv_mem (hLfmem y))
      have hZcomm : Z * B = B * Z := by
        have hinvc : (Lf y)⁻¹ * B = B * (Lf y)⁻¹ := by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hcomm y, mul_inv_cancel_right]
        rw [hZ, mul_assoc, hinvc, ← mul_assoc, hcomm y', mul_assoc]
      have hcy0 : cf y ≠ 0 := by
        intro h0
        have := hcf28 y
        rw [h0] at this
        norm_num at this
      have hinvv : ι ((Lf y)⁻¹ : GL (Fin 4) K) *ᵥ v = (cf y)⁻¹ • v := by
        have h1 : ι ((Lf y)⁻¹ : GL (Fin 4) K) *ᵥ (ι (Lf y : Matrix (Fin 4) (Fin 4) K) *ᵥ v) =
            v := by
          rw [mulVec_mulVec, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one,
            one_mulVec]
        rw [hcfv, mulVec_smul] at h1
        calc ι ((Lf y)⁻¹ : GL (Fin 4) K) *ᵥ v
            = (cf y)⁻¹ • (cf y • (ι ((Lf y)⁻¹ : GL (Fin 4) K) *ᵥ v)) := by
              rw [smul_smul, inv_mul_cancel₀ hcy0, one_smul]
          _ = (cf y)⁻¹ • v := by rw [h1]
      have hZv : ι (Z : Matrix (Fin 4) (Fin 4) K) *ᵥ v = (cf y' * (cf y)⁻¹) • v := by
        rw [hZ, Units.val_mul, map_mul, ← mulVec_mulVec, hinvv, mulVec_smul, hcfv, smul_smul,
          mul_comm (cf y)⁻¹]
      obtain ⟨d, hd1, -, hd3⟩ := hcore _ (hιcomm _ hZcomm) (hιunit _ hZmem) (hιdet _ hZmem)
      have hdd : d = cf y' * (cf y)⁻¹ := by
        rw [hZv] at hd1
        by_contra hne
        have h' : (cf y' * (cf y)⁻¹ - d) • v = 0 := by rw [sub_smul, hd1, sub_self]
        exact hv ((smul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr (Ne.symm hne)))
      have hd4 : d ^ 4 = 1 := by
        rw [hdd, mul_pow, inv_pow, ← h4, mul_inv_cancel₀ (pow_ne_zero 4 hcy0)]
      have hZs := eq_scalar_of_mapMatrix (hd3 hd4)
      have hZ00 : (Z : Matrix (Fin 4) (Fin 4) K) 0 0 ≠ 0 := by
        intro h0
        rw [h0, map_zero] at hZs
        have := (Matrix.GeneralLinearGroup.det Z).ne_zero
        rw [Matrix.GeneralLinearGroup.val_det_apply, hZs, Matrix.det_zero] at this
        exact this rfl
      have hmkZ : ProjGenLinGroup.mk Z = 1 := by
        rw [ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar]
        refine ⟨Units.mk0 _ hZ00, Units.ext ?_⟩
        conv_rhs => rw [hZs]
        rfl
      have hyy' : ((y' : projSU 4 3 1) : ProjGenLinGroup (Fin 4) K) = (y : projSU 4 3 1) := by
        rw [← hLf, ← hLf, ← mul_inv_eq_one, ← map_inv, ← map_mul, ← hZ, hmkZ]
      exact (Subtype.ext (Subtype.ext hyy')).symm
    calc Nat.card (Subgroup.centralizer ({x} : Set (projSU 4 3 1)))
        ≤ Nat.card R := Nat.card_le_card_of_injective _ hinj
      _ = R.card := Nat.card_eq_finsetCard R
      _ ≤ Multiset.card (Polynomial.nthRoots 7 (1 : L)) := Multiset.toFinset_card_le _
      _ ≤ 7 := Polynomial.card_nthRoots 7 1
  ·
    intro t ht
    set T := Lf t with hT
    have h := eq_of_mk_eq (n := 7) (A := T * B * T⁻¹) (C := B ^ 6) (by norm_num) (hconj7 _)
      (by rw [← pow_mul, show 6 * 7 = 7 * 6 by norm_num, pow_mul, hB7, one_pow])
      (by rw [hconjdet, show Matrix.GeneralLinearGroup.det (B ^ 6) =
        Matrix.GeneralLinearGroup.det B ^ 6 from map_pow _ _ _, hdet1 B hBmem, one_pow])
      (by
        rw [map_mul, map_mul, map_inv, hT, hLf, hBx, map_pow, hBx]
        have h6 : (x : ProjGenLinGroup (Fin 4) K) ^ 6 = (x : ProjGenLinGroup (Fin 4) K)⁻¹ :=
          eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hx7])
        rw [h6]
        exact_mod_cast ht)
    have hTB : T * B = B ^ 6 * T := by rwa [mul_inv_eq_iff_eq_mul] at h
    have hm : ι (T : Matrix (Fin 4) (Fin 4) K) * ι B = ι B ^ 6 * ι T := by
      rw [← map_mul, ← map_pow, ← map_mul, ← Units.val_pow_eq_pow_val, ← Units.val_mul,
        ← Units.val_mul, hTB]
    have h0 := hreal _ hm
    have h1 : ι ((T⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ
        (ι (T : Matrix (Fin 4) (Fin 4) K) *ᵥ v) = v := by
      rw [mulVec_mulVec, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one,
        one_mulVec]
    rw [h0, mulVec_zero] at h1
    exact hv h1.symm

end U43

section Normalizer

theorem zmod7_mul_self_eq_one : ∀ b : ZMod 7, b * b = 1 → b = 1 ∨ b = -1 := by decide

variable {G : Type*} [Group G] [Finite G]

theorem card_normalizer_dvd_twentyOne (P : Subgroup G) (hP : Nat.card P = 7)
    (hC : ∀ x : G, orderOf x = 7 → Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ 7)
    (hR : ∀ x : G, orderOf x = 7 → ∀ t : G, t * x * t⁻¹ ≠ x⁻¹) :
    Nat.card (Subgroup.normalizer (P : Set G)) ∣ 21 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := isCyclic_of_prime_card hP
  obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := P)
  rw [hP] at ha
  set x : G := (a : G) with hxa
  have hx : orderOf x = 7 := by rw [hxa, Subgroup.orderOf_coe, ha]
  have hzP : Subgroup.zpowers x = P := by
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr a.2) ?_
    rw [Nat.card_zpowers, hx, hP]
  have h42 : Nat.card (Subgroup.normalizer (P : Set G)) ∣ 42 := by
    have h1 := card_normalizer_zpowers_dvd x
    rw [hzP, hx, Nat.totient_prime (Fact.out : Nat.Prime 7)] at h1
    exact h1.trans (Nat.mul_dvd_mul_right (hC x hx) 6)
  have hodd : ¬ 2 ∣ Nat.card (Subgroup.normalizer (P : Set G)) := by
    intro h2
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have ht2 : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe, ht]
    have htt : (t : G) * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
    have hmem : (t : G) * x * (t : G)⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp t.2 x).mp (hzP ▸ Subgroup.mem_zpowers x)
    have hmem' : (t : G) * x * (t : G)⁻¹ ∈ Subgroup.zpowers x := by rw [hzP]; exact hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem'
    have hkk : x ^ (k * k) = x ^ (1 : ℤ) := by
      have h1 : ((t : G) * x * (t : G)⁻¹) ^ k = (t : G) * x ^ k * (t : G)⁻¹ := conj_zpow
      rw [← hk, ← _root_.zpow_mul, hk] at h1
      rw [h1, zpow_one]
      have hti : (t : G)⁻¹ = t := inv_eq_of_mul_eq_one_right htt
      calc (t : G) * ((t : G) * x * (t : G)⁻¹) * (t : G)⁻¹
          = ((t : G) * t) * x * ((t : G)⁻¹ * (t : G)⁻¹) := by group
        _ = x := by rw [htt, hti, htt, one_mul, mul_one]
    rw [zpow_eq_zpow_iff_modEq, hx] at hkk
    have hz : ((k : ℤ) : ZMod 7) * (k : ZMod 7) = 1 := by
      have := (ZMod.intCast_eq_intCast_iff (k * k) 1 7).mpr hkk
      push_cast at this
      exact this
    rcases zmod7_mul_self_eq_one _ hz with h1 | h1
    ·
      have hk1 : k ≡ 1 [ZMOD 7] := by
        have : ((k : ℤ) : ZMod 7) = ((1 : ℤ) : ZMod 7) := by rw [h1]; push_cast; rfl
        exact (ZMod.intCast_eq_intCast_iff k 1 7).mp this
      have hxk : x ^ k = x := by
        rw [← zpow_one x, ← _root_.zpow_mul, one_mul, zpow_eq_zpow_iff_modEq, hx]
        exact hk1
      have htC : (t : G) ∈ Subgroup.centralizer ({x} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        rw [hxk] at hk
        rw [eq_mul_inv_iff_mul_eq] at hk
        first | exact hk | exact hk.symm
      have := (Subgroup.orderOf_dvd_natCard _ htC).trans (hC x hx)
      rw [ht2] at this
      norm_num at this
    ·
      have hk1 : k ≡ -1 [ZMOD 7] := by
        have : ((k : ℤ) : ZMod 7) = ((-1 : ℤ) : ZMod 7) := by rw [h1]; push_cast; rfl
        exact (ZMod.intCast_eq_intCast_iff k (-1) 7).mp this
      have hxk : x ^ k = x⁻¹ := by
        rw [← zpow_neg_one x, zpow_eq_zpow_iff_modEq, hx]
        exact hk1
      exact hR x hx t (by rw [← hk, hxk])
  have hcop : Nat.Coprime (Nat.card (Subgroup.normalizer (P : Set G))) 2 :=
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd))
  exact hcop.dvd_of_dvd_mul_left (by simpa [show (42 : ℕ) = 21 * 2 by norm_num] using h42)

end Normalizer

theorem u43Norm7 : U43Norm7Statement := by
  unfold U43Norm7Statement
  intro S _ _ hS P hP
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := CFSG.Quasithin.A318P.projSU_of_statedClassicalModel_gen
    (hS.statedClassicalModel (by decide))
  refine card_normalizer_dvd_twentyOne P hP ?_ ?_
  · intro x hx
    have hex : orderOf (e x) = 7 := by rw [MulEquiv.orderOf_eq]; exact hx
    have hle : Nat.card (Subgroup.centralizer ({x} : Set S)) ≤ 7 := by
      refine le_trans ?_ (seven_facts_projSU (e x) hex).1
      refine Nat.card_le_card_of_injective
        (fun y => ⟨e y, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩) ?_
      · rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp y.2]
      · intro a b h
        exact Subtype.ext (e.injective (congrArg Subtype.val h))
    have hdvd : 7 ∣ Nat.card (Subgroup.centralizer ({x} : Set S)) := by
      have hxmem : x ∈ Subgroup.centralizer ({x} : Set S) :=
        Subgroup.mem_centralizer_singleton_iff.mpr rfl
      have := Subgroup.orderOf_dvd_natCard _ hxmem
      rwa [hx] at this
    have hpos : 0 < Nat.card (Subgroup.centralizer ({x} : Set S)) := Nat.card_pos
    obtain ⟨k, hk⟩ := hdvd
    rw [hk] at hle hpos ⊢
    have : k = 1 := by omega
    rw [this]
  · intro x hx t ht
    have hex : orderOf (e x) = 7 := by rw [MulEquiv.orderOf_eq]; exact hx
    exact (seven_facts_projSU (e x) hex).2 (e t) (by rw [← map_inv, ← map_mul, ← map_mul, ht,
      map_inv])

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKU43

