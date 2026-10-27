module

public import CFSG.RankThree.PartOne.CTP.SuTransfer
public import CFSG.RankThree.PartOne.CTP.UnitaryNode
public import CFSG.RankThree.PartOne.CTP.SpEdge

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.Universal.Unitary (SUid conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open scoped MatrixGroups

section Spectrum

variable {K : Type} [Field K]

theorem isRoot_charpoly_inv_of_conjTr {n : ℕ} (σ : K ≃+* K) (hσ : ∀ c, σ (σ c) = c)
    {M : Matrix (Fin n) (Fin n) K} (hM : conjTr σ M * M = 1) {a : K}
    (ha : M.charpoly.IsRoot a) : M.charpoly.IsRoot (σ a)⁻¹ := by
  classical
  have hM' : M * conjTr σ M = 1 := mul_eq_one_comm.mpr hM
  let u : (Matrix (Fin n) (Fin n) K)ˣ := ⟨M, conjTr σ M, hM', hM⟩
  have hspec : a ∈ spectrum K (u : Matrix (Fin n) (Fin n) K) :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.mpr ha
  have ha0 : a ≠ 0 := spectrum.ne_zero_of_mem_of_unit hspec
  have hspec' : a⁻¹ ∈ spectrum K ((u⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) :
      Matrix (Fin n) (Fin n) K) := by
    have := (spectrum.inv_mem_iff (R := K) (r := Units.mk0 a ha0) (a := u)).mp hspec
    simpa using this
  have hcp : (conjTr σ M).charpoly = M.charpoly.map (σ : K →+* K) := by
    unfold conjTr
    rw [Matrix.charpoly_transpose]
    exact Matrix.charpoly_map M (σ : K →+* K)
  have hroot : (conjTr σ M).charpoly.IsRoot a⁻¹ :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.mp (by simpa [u] using hspec')
  rw [hcp] at hroot
  have h1 : (M.charpoly.map (σ : K →+* K)).eval (σ (σ a⁻¹)) = 0 := by
    rw [hσ]
    exact hroot
  rw [Polynomial.eval_map] at h1
  have h3 : (σ : K →+* K) (M.charpoly.eval (σ a⁻¹)) = 0 := by
    rw [← Polynomial.eval₂_at_apply]
    exact h1
  have h4 : M.charpoly.eval (σ a⁻¹) = 0 := (map_eq_zero σ).mp h3
  rw [map_inv₀] at h4
  exact h4

end Spectrum

section Scalar

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)

theorem unitary_conjTr_mul_four
    (A : primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :
    conjTr (unitaryInvolution K 2 f) ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
  have hσ : (⇑(unitaryInvolution K 2 f) : K → K) = ⇑h.bar :=
    funext fun c => by rw [unitaryInvolution_apply, h.bar_apply]
  have e : (((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ * 1 *
      ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := mem_primeFormUnitary.mp A.2
  rw [Matrix.mul_one] at e
  have e2 : conjTr (unitaryInvolution K 2 f) ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ := by
    simp only [conjTr, hσ]
  rw [e2]
  exact e

omit [Finite K] [CharP K 2] in
theorem coe_scalar_mul_four (u : Kˣ) (A : GL (Fin 4) K) :
    ((GeneralLinearGroup.scalar (Fin 4) u * A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (u : K) • (A : Matrix (Fin 4) (Fin 4) K) := by
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul]

include h in
theorem exists_mem_suid_conj_eq (hq : 4 ≤ 2 ^ f) (A : GL (Fin 4) K)
    (hA : A ∈ primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :
    ∃ g : SUid (unitaryInvolution K 2 f) 4, ∀ s : GL (Fin 4) K,
      (g : GL (Fin 4) K) * s * (g : GL (Fin 4) K)⁻¹ = A * s * A⁻¹ := by
  classical
  set σ := unitaryInvolution K 2 f with hσdef
  have hAu : conjTr σ (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1 :=
    unitary_conjTr_mul_four h ⟨A, hA⟩
  set d : K := (A : Matrix (Fin 4) (Fin 4) K).det with hddef
  have hd : σ d * d = 1 := by
    have := congrArg Matrix.det hAu
    rw [Matrix.det_mul, Matrix.det_one] at this
    have e : (conjTr σ (A : Matrix (Fin 4) (Fin 4) K)).det = σ d := by
      unfold conjTr
      rw [Matrix.det_transpose]
      exact (RingHom.map_det (σ : K →+* K) _).symm
    rwa [e] at this
  have hd0 : d ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero
  have hdq : d ^ (2 ^ f + 1) = 1 := by
    rw [unitaryInvolution_apply] at hd
    rw [pow_succ]
    exact hd
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime (gcd_four_two_pow_add_one hq)
    (by omega : 1 < 2 ^ f + 1)
  set c : K := d ^ k with hcdef
  have hc4 : c ^ 4 = d := by
    rw [hcdef, ← pow_mul, mul_comm k 4]
    have h1 : 4 * k = 4 * k % (2 ^ f + 1) + (2 ^ f + 1) * (4 * k / (2 ^ f + 1)) :=
      (Nat.mod_add_div _ _).symm
    rw [h1, pow_add, hk, pow_mul, hdq, one_pow, mul_one, pow_one]
  have hcσ : σ c * c = 1 := by
    rw [unitaryInvolution_apply, ← pow_succ, hcdef, ← pow_mul, mul_comm, pow_mul, hdq, one_pow]
  have hc0 : c ≠ 0 := by
    intro hc
    rw [hc] at hc4
    exact hd0 (by rw [← hc4]; norm_num)
  set u : Kˣ := Units.mk0 c hc0 with hudef
  set z : GL (Fin 4) K := GeneralLinearGroup.scalar (Fin 4) u⁻¹ with hzdef
  have hzcoe : ((z * A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      c⁻¹ • (A : Matrix (Fin 4) (Fin 4) K) := by
    rw [hzdef, coe_scalar_mul_four, Units.val_inv_eq_inv_val, hudef, Units.val_mk0]
  have hmem : z * A ∈ SUid σ 4 := by
    refine ⟨?_, ?_⟩
    · rw [hzcoe, Matrix.det_smul, Fintype.card_fin, ← hddef, inv_pow, hc4, inv_mul_cancel₀ hd0]
    · rw [hzcoe]
      have e : conjTr σ (c⁻¹ • (A : Matrix (Fin 4) (Fin 4) K)) =
          σ c⁻¹ • conjTr σ (A : Matrix (Fin 4) (Fin 4) K) := by
        ext i j
        simp [conjTr, map_mul]
      rw [e, Matrix.smul_mul, Matrix.mul_smul, hAu, smul_smul, map_inv₀, ← mul_inv, hcσ,
        inv_one, one_smul]
  refine ⟨⟨z * A, hmem⟩, fun s => ?_⟩
  have hz : ∀ y : GL (Fin 4) K, z * y = y * z := fun y => (commute_scalar u⁻¹ y).eq.symm
  change z * A * s * (z * A)⁻¹ = A * s * A⁻¹
  calc z * A * s * (z * A)⁻¹ = z * (A * s * A⁻¹) * z⁻¹ := by group
    _ = (A * s * A⁻¹) * z * z⁻¹ := by rw [hz]
    _ = A * s * A⁻¹ := by group

end Scalar

section Aut

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)

include h in
theorem su_aut_odd (hq : 4 ≤ 2 ^ f) {p : ℕ} (hp : Odd p)
    {ε : MulAut (SUid (unitaryInvolution K 2 f) 4)} (hε : ε ^ p = 1)
    {x : SUid (unitaryInvolution K 2 f) 4} (hx : orderOf x = 2 ^ f - 1) (hεx : ε x = x) :
    ∃ g : SUid (unitaryInvolution K 2 f) 4, ∀ s, ε s = g * s * g⁻¹ := by
  classical
  have hC : IsPrimeFormGram (1 : GL (Fin 4) K) := isPrimeFormGram_one
  have hnq : ¬ (4 = 3 ∧ 2 ^ f = 2) := by rintro ⟨h4, -⟩; omega
  let e : SUid (unitaryInvolution K 2 f) 4 ≃*
      primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
    MulEquiv.ofBijective (suProjFour h) (suProjFour_bijective h hq)
  set α : MulAut (primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :=
    MulAut.congr e ε with hαdef
  have hα : ∀ s, α (suProjFour h s) = suProjFour h (ε s) := by
    intro s
    change e (ε (e.symm (e s))) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hαp : α ^ p = 1 := by rw [hαdef, ← map_pow, hε, map_one]
  obtain ⟨⟨A, τ⟩, hx'⟩ := primeFormPsi_surjective h hC (by norm_num) hnq α
  rw [primeFormPsi_apply] at hx'
  have hτr : τ ^ p = 1 := by
    have := congrArg (primeFormFieldFactor h hC (by norm_num) hnq) hαp
    rw [map_pow, ← hx', primeFormFieldFactor_apply, map_one] at this
    exact this
  have hτodd : Odd (orderOf τ) := Odd.of_dvd_nat hp (orderOf_dvd_of_pow_eq_one hτr)
  have hα_mk : ∀ g : gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K),
      α (QuotientGroup.mk g) =
        QuotientGroup.mk (primeFormConjSU h _ A (primeFormFieldSU h hC τ g)) := by
    intro g
    rw [← hx', MulAut.mul_apply]
    change primeFormConjAut h _ A (primeFormFieldAut h hC τ (QuotientGroup.mk g)) = _
    rw [primeFormFieldAut_mk, primeFormConjAut_mk]
  have hconjA : ∀ s : SUid (unitaryInvolution K 2 f) 4,
      ((ε s : SUid (unitaryInvolution K 2 f) 4) : GL (Fin 4) K) =
        (A : GL (Fin 4) K) * glAut τ (s : GL (Fin 4) K) * (A : GL (Fin 4) K)⁻¹ := by
    intro s
    have h1 : (QuotientGroup.mk (primeFormConjSU h _ A
        (primeFormFieldSU h hC τ (suEquivFour h s))) : primeFormP h _) =
        QuotientGroup.mk (suEquivFour h (ε s)) :=
      (hα_mk (suEquivFour h s)).symm.trans (hα s)
    have h2 := QuotientGroup.eq.mp h1
    rw [normOneScalars_four_eq_bot h hq, Subgroup.mem_bot, inv_mul_eq_one] at h2
    exact (congrArg Subtype.val h2).symm
  have hAx : (A : GL (Fin 4) K) * glAut τ (x : GL (Fin 4) K) = (x : GL (Fin 4) K) *
      (A : GL (Fin 4) K) := by
    have h1 := hconjA x
    rw [hεx] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1.symm
  set xm : Matrix (Fin 4) (Fin 4) K := ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hxm
  have hconj : ∃ M : Matrix (Fin 4) (Fin 4) K, IsUnit M ∧ M * xm.map τ = xm * M := by
    refine ⟨((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K), (A : GL (Fin 4) K).isUnit, ?_⟩
    have h2 := congrArg (fun u : GL (Fin 4) K => (u : Matrix (Fin 4) (Fin 4) K)) hAx
    simpa only [Units.val_mul, coe_glAut] using h2
  let matHom : SUid (unitaryInvolution K 2 f) 4 →* Matrix (Fin 4) (Fin 4) K :=
    (Units.coeHom (Matrix (Fin 4) (Fin 4) K)).comp (SUid (unitaryInvolution K 2 f) 4).subtype
  have hmatinj : Function.Injective matHom := fun a b hab => Subtype.ext (Units.ext hab)
  have hord : orderOf xm = 2 ^ f - 1 := by
    have := orderOf_injective matHom hmatinj x
    exact this.trans hx
  have hxpow : xm ^ (2 ^ f - 1) = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one xm
  have hmK : 2 ^ f - 1 ∣ Nat.card K - 1 := by
    rw [h.card_eq_sq]
    have e2 : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      zify [show 1 ≤ 2 ^ f by omega, show 1 ≤ (2 ^ f) ^ 2 by nlinarith]
      ring
    rw [e2]
    exact Dvd.intro_left _ rfl
  have hodd : Odd (2 ^ f - 1) := by
    have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by rintro rfl; omega)
    obtain ⟨k, hk⟩ := h2
    exact ⟨k - 1, by omega⟩
  have hxu : conjTr (unitaryInvolution K 2 f) xm * xm = 1 := x.2.2
  have hrec : ∀ r : K, xm.charpoly.IsRoot r → xm.charpoly.IsRoot r⁻¹ := by
    intro r hr
    have hr1 : r ^ (2 ^ f - 1) = 1 :=
      (pow_eq_one_iff_forall_isRoot_charpoly hmK hxpow (2 ^ f - 1)).mp hxpow r hr
    have hσr : unitaryInvolution K 2 f r = r := by
      rw [unitaryInvolution_apply]
      calc r ^ 2 ^ f = r ^ (2 ^ f - 1) * r := by
            rw [← pow_succ]
            congr 1
            omega
        _ = r := by rw [hr1, one_mul]
    have := isRoot_charpoly_inv_of_conjTr (unitaryInvolution K 2 f)
      (CFSG.LieType.BorelTits.unitaryInvolution_involutive h.card_eq_sq) hxu hr
    rwa [hσr] at this
  have hfix := fixes_rootsOfUnity_of_conj (by simp) τ hp hτr hodd hmK hord hrec hconj
  obtain ⟨μ, hμ⟩ := exists_primitiveRoot_q_sub_one h.card_eq_sq (by omega : 2 ≤ 2 ^ f)
  have hτ1 : τ = 1 := ringEquiv_eq_one_of_fix_unitary h.card_eq_sq (by omega) hτodd hμ
    (hfix μ hμ.pow_eq_one)
  subst hτ1
  obtain ⟨g, hg⟩ := exists_mem_suid_conj_eq h hq (A : GL (Fin 4) K) A.2
  refine ⟨g, fun s => ?_⟩
  apply Subtype.ext
  rw [hconjA s]
  have hs1 : glAut (1 : K ≃+* K) (s : GL (Fin 4) K) = s := by
    rw [map_one]
    rfl
  rw [hs1]
  exact (hg s).symm

end Aut

section Normalizer

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)

include h in
theorem exists_su_of_normalizes (hq : 4 ≤ 2 ^ f) {G : Type} [Group G]
    (θ : SUid (unitaryInvolution K 2 f) 4 →* G) (hθ : Function.Injective θ) {e : G}
    (he : e ∈ Subgroup.normalizer (θ.range : Set G)) {p : ℕ} (hp : Odd p) (hep : e ^ p = 1)
    {x : SUid (unitaryInvolution K 2 f) 4} (hx : orderOf x = 2 ^ f - 1)
    (hex : e * θ x = θ x * e) :
    ∃ g : SUid (unitaryInvolution K 2 f) 4, g ^ p = 1 ∧
      ∀ s : SUid (unitaryInvolution K 2 f) 4, θ (g * s * g⁻¹) = e * θ s * e⁻¹ := by
  obtain ⟨ε, hε⟩ := exists_aut_of_normalizes θ hθ he
  have hεpow : ∀ k : ℕ, ∀ s, θ ((ε ^ k) s) = e ^ k * θ s * (e ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro s; simp
    | succ k ih =>
      intro s
      rw [pow_succ, pow_succ, MulAut.mul_apply, ih, hε]
      group
  have hεp : ε ^ p = 1 := by
    refine MulEquiv.ext fun s => hθ ?_
    rw [hεpow, hep]
    simp
  have hεx : ε x = x := by
    apply hθ
    rw [hε, hex]
    group
  obtain ⟨g, hg⟩ := su_aut_odd h hq hp hεp hx hεx
  have hεk : ∀ k : ℕ, ∀ s, (ε ^ k) s = g ^ k * s * (g ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro s; simp
    | succ k ih =>
      intro s
      rw [pow_succ, MulAut.mul_apply, hg, ih]
      group
  refine ⟨g, ?_, fun s => by rw [← hg, hε]⟩
  have hcen : g ^ p ∈ Subgroup.center (SUid (unitaryInvolution K 2 f) 4) :=
    Subgroup.mem_center_iff.mpr fun s => by
      have h1 : g ^ p * s * (g ^ p)⁻¹ = s := by
        rw [← hεk, hεp, MulAut.one_apply]
      rw [mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
  rw [center_suid_four_eq_bot h hq] at hcen
  exact hcen

end Normalizer

end CFSG.RankThree.PartOne.CTP
