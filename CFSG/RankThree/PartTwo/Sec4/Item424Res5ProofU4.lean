module

public import CFSG.RankThree.PartTwo.Sec4.Item424Res5ProofTools
public import CFSG.RankThree.PartTwo.Sec21.Item228Census3ProofU4Syl

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.RankThree.PartTwo.Sec21.Item228Census3Proof (exists_conj_into_d8Tor_su_prime)
open Matrix

namespace Item424Res5

theorem weyl_of_conj_into {Y : Type*} [Group Y] [Finite Y] {T : Subgroup Y} (hT9 : Nat.card T ≤ 9)
    {M : Y}
    (hMT : ∀ t ∈ T, M * t * M⁻¹ ∈ T) (hM2 : ∀ t ∈ T, M ^ 2 * t * (M ^ 2)⁻¹ = t⁻¹)
    (hconj : ∀ E : Subgroup Y, (∀ x ∈ E, x ^ 3 = 1) → ∃ g : Y, ∀ x ∈ E, g * x * g⁻¹ ∈ T)
    (E : Subgroup Y) (hexp : ∀ x ∈ E, x ^ 3 = 1) (hcard : Nat.card E = 9) :
    ∃ h : Y, (∀ x ∈ E, h * x * h⁻¹ ∈ E) ∧ ∀ x ∈ E, h ^ 2 * x * (h ^ 2)⁻¹ = x⁻¹ := by
  obtain ⟨g, hg⟩ := hconj E hexp
  set E' := E.map (MulAut.conj g).toMonoidHom with hE'
  have hle : E' ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact hg x hx
  have hcard' : Nat.card E' = 9 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]
  have hET : E' = T := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard']; exact hT9)
  have hsurj : ∀ t ∈ T, ∃ x ∈ E, g * x * g⁻¹ = t := by
    intro t ht
    rw [← hET] at ht
    obtain ⟨x, hx, rfl⟩ := ht
    exact ⟨x, hx, rfl⟩
  refine ⟨g⁻¹ * M * g, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨x', hx', hx'e⟩ := hsurj _ (hMT _ (hg x hx))
    have e : g⁻¹ * M * g * x * (g⁻¹ * M * g)⁻¹ = g⁻¹ * (M * (g * x * g⁻¹) * M⁻¹) * g := by group
    rw [e, ← hx'e]
    have e2 : g⁻¹ * (g * x' * g⁻¹) * g = x' := by group
    rw [e2]
    exact hx'
  · have e : (g⁻¹ * M * g) ^ 2 = g⁻¹ * M ^ 2 * g := by
      rw [pow_two, pow_two]
      group
    rw [e]
    have e2 : g⁻¹ * M ^ 2 * g * x * (g⁻¹ * M ^ 2 * g)⁻¹ =
        g⁻¹ * (M ^ 2 * (g * x * g⁻¹) * (M ^ 2)⁻¹) * g := by group
    rw [e2, hM2 _ (hg x hx)]
    group

@[expose] def rotFour : Equiv.Perm (Fin 4) :=
  ⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩

theorem rotFour_rev : ∀ i, rotFour (Fin.rev i) = Fin.rev (rotFour i) := by decide

theorem sign_rotFour : Equiv.Perm.sign rotFour = -1 := by decide

variable {F : Type} [Field F]

@[expose] def epsFour (y : Fˣ) : Fin 4 → Fˣ := ![y, 1, 1, -y⁻¹]

@[expose] noncomputable def weylMono (y : Fˣ) : GL (Fin 4) F := permGL rotFour * diagU (epsFour y)

theorem weylMono_mem (σ : F ≃+* F) {y : Fˣ} (hy : σ (y : F) = -y) :
    weylMono y ∈ SU σ 4 := by
  refine mem_SU.mpr ⟨?_, ?_⟩
  · rw [weylMono, Units.val_mul, Matrix.det_mul, det_diagU, coe_permGL, Matrix.det_permutation,
      Equiv.Perm.sign_inv, sign_rotFour]
    simp [epsFour, Fin.prod_univ_four]
  · rw [weylMono, Units.val_mul, conjTr_mul]
    have hP := permGL_gram (K := F) σ rotFour rotFour_rev
    have hD := diagU_gram σ (d := epsFour y) (fun i => by
      fin_cases i
      · simp [epsFour, hy]
      · simp [epsFour]
      · simp [epsFour]
      · simp only [epsFour, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
        have : (Fin.rev (3 : Fin 4)) = 0 := rfl
        rw [this]
        simp only [Matrix.cons_val_zero, Units.val_neg, map_neg, Units.val_inv_eq_inv_val,
          map_inv₀, hy]
        have hy0 : (y : F) ≠ 0 := y.ne_zero
        field_simp)
    calc conjTr σ ((diagU (epsFour y) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          conjTr σ ((permGL rotFour : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * antidiag 4 *
          (((permGL rotFour : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
            ((diagU (epsFour y) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) =
        conjTr σ ((diagU (epsFour y) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          (conjTr σ ((permGL rotFour : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * antidiag 4 *
            ((permGL rotFour : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) *
          ((diagU (epsFour y) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
          simp only [Matrix.mul_assoc]
      _ = antidiag 4 := by rw [hP, hD]

theorem weylMono_conj (y : Fˣ) (v : D8Mod 3 F) :
    weylMono y * diagU (d8Vec 4 v) * (weylMono y)⁻¹ = diagU (d8Vec 4 (v.2⁻¹, v.1)) := by
  have hDX : (diagU (epsFour y) : GL (Fin 4) F) * diagU (d8Vec 4 v) * (diagU (epsFour y))⁻¹ =
      diagU (d8Vec 4 v) := by
    rw [diagU_mul, mul_comm (epsFour y) (d8Vec 4 v), ← diagU_mul, mul_inv_cancel_right]
  calc weylMono y * diagU (d8Vec 4 v) * (weylMono y)⁻¹ =
        permGL rotFour * ((diagU (epsFour y) : GL (Fin 4) F) * diagU (d8Vec 4 v) *
          (diagU (epsFour y))⁻¹) * (permGL rotFour)⁻¹ := by
        rw [weylMono]
        group
    _ = diagU (d8Vec 4 v ∘ rotFour.symm) := by rw [hDX, permGL_conj_diagU]
    _ = diagU (d8Vec 4 (v.2⁻¹, v.1)) := by
        congr 1
        funext i
        rw [d8Vec_four, d8Vec_four]
        fin_cases i <;> simp [rotFour, dvec4]

theorem weylMono_sq_conj (y : Fˣ) (v : D8Mod 3 F) :
    weylMono y ^ 2 * diagU (d8Vec 4 v) * (weylMono y ^ 2)⁻¹ = (diagU (d8Vec 4 v))⁻¹ := by
  have e : weylMono y ^ 2 * diagU (d8Vec 4 v) * (weylMono y ^ 2)⁻¹ =
      weylMono y * (weylMono y * diagU (d8Vec 4 v) * (weylMono y)⁻¹) * (weylMono y)⁻¹ := by
    rw [pow_two]
    group
  rw [e, weylMono_conj, weylMono_conj]
  have hv : ((v.2⁻¹, v.1) : D8Mod 3 F).2⁻¹ = v.1⁻¹ := rfl
  rw [hv]
  have h1 : ((v.1⁻¹, v.2⁻¹) : D8Mod 3 F) = v⁻¹ := rfl
  rw [show (((v.2⁻¹, v.1) : D8Mod 3 F).1) = v.2⁻¹ from rfl, h1]
  have := (diagUHom.comp (d8VecHom (p := 3) (K := F) 4)).map_inv v
  exact this

theorem exists_unit_unitaryInvolution_eq_neg [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hf : 1 ≤ f) :
    ∃ y : Fˣ, unitaryInvolution F p f (y : F) = -y := by
  have := Fintype.ofFinite F
  have hq : 1 < p ^ f := Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt
  obtain ⟨c, hc⟩ : ∃ c : F, unitaryInvolution F p f c ≠ c := by
    by_contra h
    push Not at h
    have hroots : (Finset.univ : Finset F).val ⊆
        (Polynomial.X ^ (p ^ f) - Polynomial.X : Polynomial F).roots := by
      intro a _
      rw [Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero F hq), Polynomial.IsRoot,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, ← unitaryInvolution_apply,
        h a, sub_self]
    have hle := Polynomial.card_le_degree_of_subset_roots hroots
    rw [FiniteField.X_pow_card_sub_X_natDegree_eq F hq, Finset.card_univ,
      ← Nat.card_eq_fintype_card, hF] at hle
    nlinarith
  have hy0 : c - unitaryInvolution F p f c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  refine ⟨Units.mk0 _ hy0, ?_⟩
  simp only [Units.val_mk0, map_sub, unitaryInvolution_involutive hF]
  ring

theorem exists_weyl_su4 [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hf : 1 ≤ f) (h3 : 3 ∣ p ^ f - 1)
    (E : Subgroup (SU (unitaryInvolution F p f) 4)) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 9) :
    ∃ h : SU (unitaryInvolution F p f) 4, (∀ x ∈ E, h * x * h⁻¹ ∈ E) ∧
      ∀ x ∈ E, h ^ 2 * x * (h ^ 2)⁻¹ = x⁻¹ := by
  obtain ⟨y, hy⟩ := exists_unit_unitaryInvolution_eq_neg hF hf
  let M : SU (unitaryInvolution F p f) 4 := ⟨weylMono y, weylMono_mem _ hy⟩
  let T : Subgroup (SU (unitaryInvolution F p f) 4) :=
    (d8Tor 3 F 4).subgroupOf (SU (unitaryInvolution F p f) 4)
  have hT9 : Nat.card T ≤ 9 := by
    have h1 : Nat.card T ≤ Nat.card (d8Tor 3 F 4) := by
      refine Nat.card_le_card_of_injective
        (fun t : T => (⟨((t : SU (unitaryInvolution F p f) 4) : GL (Fin 4) F), t.2⟩ :
          d8Tor 3 F 4)) ?_
      intro s t hst
      have h := congrArg (fun z : d8Tor 3 F 4 => (z : GL (Fin 4) F)) hst
      exact Subtype.ext (Subtype.ext h)
    have h2 : Nat.card (d8Tor 3 F 4) ≤ Nat.card (D8Mod 3 F) :=
      Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
    have h3' : Nat.card (D8Mod 3 F) ≤ 9 := by
      rw [Nat.card_prod]
      have := card_rootsOfUnity F 3
      nlinarith
    omega
  have hmemT : ∀ t ∈ T, ∃ v : D8Mod 3 F,
      diagU (d8Vec 4 v) = ((t : SU (unitaryInvolution F p f) 4) : GL (Fin 4) F) :=
    fun t ht => mem_d8Tor_iff.mp (Subgroup.mem_subgroupOf.mp ht)
  have hMT : ∀ t ∈ T, M * t * M⁻¹ ∈ T := by
    intro t ht
    obtain ⟨v, hv⟩ := hmemT t ht
    rw [Subgroup.mem_subgroupOf, mem_d8Tor_iff]
    refine ⟨(v.2⁻¹, v.1), ?_⟩
    rw [← weylMono_conj y v, hv]
    rfl
  have hM2 : ∀ t ∈ T, M ^ 2 * t * (M ^ 2)⁻¹ = t⁻¹ := by
    intro t ht
    obtain ⟨v, hv⟩ := hmemT t ht
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_pow]
    rw [← hv]
    exact weylMono_sq_conj y v
  refine weyl_of_conj_into hT9 hMT hM2 (fun E' hE' => ?_) E hexp hcard
  exact exists_conj_into_d8Tor_su_prime (n := 4) (Or.inl rfl) d8Comb_four hF Nat.prime_three
    (by norm_num) h3 E' hE'

theorem projSU_eq_map (n p f : ℕ) [Fact p.Prime] :
    projSU n p f = (StatedSU n (p ^ f) (GaloisField p (2 * f))).map
      (ProjGenLinGroup.mk : GL (Fin n) _ →* _) := by
  rw [projSU, StatedSU]
  congr 2
  ext A
  simp [Units.ext_iff]

theorem census424_of_projSU_four {X : Type} [Group X] [Finite X] {p f : ℕ} [Fact p.Prime]
    (hf : 1 ≤ f) (h3 : 3 ∣ p ^ f - 1) (eX : X ≃* projSU 4 p f) : Census424 X := by
  set F := GaloisField p (2 * f) with hFdef
  have hF : Nat.card F = (p ^ f) ^ 2 := by
    rw [GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
  let π₀ : StatedSU 4 (p ^ f) F →* projSU 4 p f :=
    ((ProjGenLinGroup.mk : GL (Fin 4) F →* _).comp (StatedSU 4 (p ^ f) F).subtype).codRestrict
      (projSU 4 p f) (fun x => by rw [projSU_eq_map]; exact ⟨x, x.2, rfl⟩)
  have hπ₀ : Function.Surjective π₀ := by
    rintro ⟨y, hy⟩
    rw [projSU_eq_map, Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  let e := equivStatedSU hF 4
  have hπ : Function.Surjective ((eX.symm.toMonoidHom.comp π₀).comp e.toMonoidHom) :=
    (eX.symm.surjective.comp hπ₀).comp e.surjective
  refine census424_of_cover _ hπ (fun z hz => ?_) (fun E hc hexp hcard =>
    exists_weyl_su4 hF hf h3 E hexp hcard)
  have h1 : π₀ (e z) = 1 := by
    apply eX.symm.injective
    rw [map_one]
    exact hz
  have h2 : ProjGenLinGroup.mk ((e z : StatedSU 4 (p ^ f) F) : GL (Fin 4) F) = 1 :=
    congrArg Subtype.val h1
  rw [ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at h2
  obtain ⟨c, hc⟩ := h2
  have hdet := det_eq_one_of_mem_statedSU (e z).2
  rw [← hc] at hdet
  have hc4 : (c : F) ^ 4 = 1 := by
    simpa [Matrix.GeneralLinearGroup.scalar] using hdet
  have hcu : c ^ 4 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hc4, Units.val_one])
  have h4 : e z ^ 4 = 1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, ← hc, ← map_pow, hcu, map_one]
    rfl
  apply e.injective
  rw [map_pow, h4, map_one]

end Item424Res5

end CFSG.RankThree.PartTwo.Sec4
