module

public import CFSG.RankThree.PartOne.TCX.E.Claims

public section

namespace CFSG.RankThree.PartOne.TCX.E

open Subgroup Matrix CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.KLCE
open scoped commutatorElement

section Abstract

theorem exists_hom_of_push' {G G' D : Type} [Group G] [Group G'] [Group D] (ψ : G →* G')
    (hψ : Function.Injective ψ) (ρ : D →* G') (hrange : ρ.range ≤ ψ.range) :
    ∃ φ : D →* G, (∀ d, ψ (φ d) = ρ d) ∧ φ.range = (ρ.range).comap ψ ∧
      ∀ d, φ d = 1 ↔ ρ d = 1 := by
  classical
  have hex : ∀ d, ∃ g, ψ g = ρ d := fun d => hrange ⟨d, rfl⟩
  choose f hf using hex
  have hmul : ∀ a b, f (a * b) = f a * f b := fun a b => by
    apply hψ
    rw [map_mul, hf, hf, hf, map_mul]
  have hone : f 1 = 1 := by
    apply hψ
    rw [hf, map_one, map_one]
  refine ⟨⟨⟨f, hone⟩, hmul⟩, hf, ?_, fun d => ?_⟩
  · ext g
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨d, (hf d).symm⟩
    · rintro ⟨d, hd⟩
      refine ⟨d, ?_⟩
      apply hψ
      exact (hf d).trans hd
  · constructor
    · intro h
      have h1 := hf d
      rw [show f d = 1 from h, map_one] at h1
      exact h1.symm
    · intro h
      apply hψ
      show ψ (f d) = ψ 1
      rw [hf, h, map_one]

theorem eq_one_of_central_hom {D : Type} [Group D] (hperf : commutator D = ⊤) (ζ : D →* D)
    (hζ : ∀ d, ζ d ∈ Subgroup.center D) : ∀ d, ζ d = 1 := by
  have hle : commutator D ≤ ζ.ker := by
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, commutatorElement_def]
    simp only [map_mul, map_inv]
    have h1 := Subgroup.mem_center_iff.1 (hζ a) (ζ b)
    rw [← h1]
    group
  intro d
  have hd : d ∈ commutator D := by rw [hperf]; exact Subgroup.mem_top d
  exact hle hd

theorem not_inner_of_class_central {G D R : Type} [Group G] [Group D] (φ : D →* G)
    (hker : ∀ d, φ d = 1 → d ∈ Subgroup.center D) (hperf : commutator D = ⊤)
    (α : MulAut G) (τ : D →* D) (hαφ : ∀ d, α (φ d) = φ (τ d))
    (χ : D → R) (hχ : ∀ E d : D, χ (E * d * E⁻¹) = χ d) (d : D) (hd : χ (τ d) ≠ χ d) :
    ∀ e ∈ φ.range, ¬ ∀ g ∈ φ.range, α g = e * g * e⁻¹ := by
  rintro _ ⟨E, rfl⟩ hall
  have hz : ∀ x, τ x * (E * x * E⁻¹)⁻¹ ∈ Subgroup.center D := fun x => by
    apply hker
    have h := hall (φ x) ⟨x, rfl⟩
    rw [hαφ, ← map_inv, ← map_mul, ← map_mul] at h
    rw [map_mul, map_inv, h, mul_inv_cancel]
  let ζ : D →* D :=
    { toFun := fun x => τ x * (E * x * E⁻¹)⁻¹
      map_one' := by simp
      map_mul' := fun x y => by
        have hcy := Subgroup.mem_center_iff.1 (hz y) ((E * x * E⁻¹)⁻¹)
        have e2 : (E * (x * y) * E⁻¹)⁻¹ = (E * y * E⁻¹)⁻¹ * (E * x * E⁻¹)⁻¹ := by group
        show τ (x * y) * (E * (x * y) * E⁻¹)⁻¹ =
          τ x * (E * x * E⁻¹)⁻¹ * (τ y * (E * y * E⁻¹)⁻¹)
        rw [map_mul, e2]
        calc τ x * τ y * ((E * y * E⁻¹)⁻¹ * (E * x * E⁻¹)⁻¹)
            = τ x * ((τ y * (E * y * E⁻¹)⁻¹) * (E * x * E⁻¹)⁻¹) := by group
          _ = τ x * ((E * x * E⁻¹)⁻¹ * (τ y * (E * y * E⁻¹)⁻¹)) := by rw [← hcy]
          _ = τ x * (E * x * E⁻¹)⁻¹ * (τ y * (E * y * E⁻¹)⁻¹) := by group }
  have h1 := eq_one_of_central_hom hperf ζ hz d
  have h2 : τ d = E * d * E⁻¹ := by
    have : τ d * (E * d * E⁻¹)⁻¹ = 1 := h1
    exact mul_inv_eq_one.1 this
  exact hd (by rw [h2, hχ])

theorem quotient_center_equiv {G D : Type} [Group G] [Group D] (φ : D →* G)
    (hker : ∀ d, φ d = 1 → d ∈ Subgroup.center D) (hperf : commutator D = ⊤) :
    Nonempty ((D ⧸ Subgroup.center D) ≃* (↥φ.range ⧸ Subgroup.center ↥φ.range)) := by
  let ψ : D →* (↥φ.range ⧸ Subgroup.center ↥φ.range) :=
    (QuotientGroup.mk' _).comp φ.rangeRestrict
  have hψs : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective _).comp (MonoidHom.rangeRestrict_surjective φ)
  have hψk : ψ.ker = Subgroup.center D := by
    ext d
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have hc : φ.rangeRestrict d ∈ Subgroup.center ↥φ.range := (QuotientGroup.eq_one_iff _).1 h
      have hcomm : ∀ x, d * x * d⁻¹ * x⁻¹ ∈ Subgroup.center D := fun x => by
        apply hker
        have h1 := Subgroup.mem_center_iff.1 hc ⟨φ x, x, rfl⟩
        have h2 : φ x * φ d = φ d * φ x := congrArg Subtype.val h1
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h2]
        group
      let ζ : D →* D :=
        { toFun := fun x => d * x * d⁻¹ * x⁻¹
          map_one' := by simp
          map_mul' := fun x y => by
            have hcy := Subgroup.mem_center_iff.1 (hcomm y) x⁻¹
            show d * (x * y) * d⁻¹ * (x * y)⁻¹ = d * x * d⁻¹ * x⁻¹ * (d * y * d⁻¹ * y⁻¹)
            calc d * (x * y) * d⁻¹ * (x * y)⁻¹
                = (d * x * d⁻¹) * ((d * y * d⁻¹ * y⁻¹) * x⁻¹) := by group
              _ = (d * x * d⁻¹) * (x⁻¹ * (d * y * d⁻¹ * y⁻¹)) := by rw [← hcy]
              _ = d * x * d⁻¹ * x⁻¹ * (d * y * d⁻¹ * y⁻¹) := by group }
      have := eq_one_of_central_hom hperf ζ hcomm
      rw [Subgroup.mem_center_iff]
      intro x
      have hx : d * x * d⁻¹ * x⁻¹ = 1 := this x
      calc x * d = (d * x * d⁻¹ * x⁻¹)⁻¹ * (d * x) := by group
        _ = d * x := by rw [hx, inv_one, one_mul]
    · intro hd
      refine (QuotientGroup.eq_one_iff _).2 ?_
      rw [Subgroup.mem_center_iff]
      rintro ⟨_, x, rfl⟩
      apply Subtype.ext
      show φ x * φ d = φ d * φ x
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hd x]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)⟩

theorem layerDatum2_of_model' {p : ℕ} {M : Type} [Group M] (F₀ : M → M) {D : Type} [Group D]
    (ρ' : D →* M) (τ'' : D → D) (hker : ∀ d, ρ' d = 1 → d ∈ Subgroup.center D)
    (hcompat : ∀ d, F₀ (ρ' d) = ρ' (τ'' d))
    (hclaims : ∀ {G : Type} [Group G] (α : MulAut G) (φ : D →* G),
      (∀ d, φ d = 1 → d ∈ Subgroup.center D) → (∀ d, α (φ d) = φ (τ'' d)) →
      ∀ Q : Subgroup G, φ.range = Q → LayerClaims2 p α Q) :
    LayerDatum2 p F₀ ρ'.range := by
  intro G _ _ ψ hψ hPψ α _ hψα _
  obtain ⟨φ, hψφ, hφrange, hφker⟩ := exists_hom_of_push' ψ hψ ρ' hPψ
  have hαφ : ∀ d, α (φ d) = φ (τ'' d) := fun d => by
    apply hψ
    rw [hψα, hψφ, hcompat, hψφ]
  obtain ⟨-, hout, hmodel, hfix⟩ :=
    hclaims α φ (fun d hd => hker d ((hφker d).1 hd)) hαφ _ hφrange
  exact ⟨hout, hmodel, hfix⟩

theorem braid_not_central {D : Type} [Group D] (x y : D) (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x ≠ y) (h3 : (x * y) ^ 3 = 1) : ⁅x, y⁆ ∉ Subgroup.center D := by
  intro hz
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hz' := Subgroup.mem_center_iff.1 hz x
  rw [commutatorElement_def, hxi, hyi] at hz'
  have h3' : x * y * x * y * x * y = 1 := by
    have : (x * y) ^ 3 = x * y * x * y * x * y := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [← this]
    exact h3
  have e1 : x * y * x * y * x = y := by
    have := eq_inv_of_mul_eq_one_left h3'
    rw [this, hyi]
  have e2 : x * (x * y * x * y) = y * x * y := by
    simp only [← mul_assoc]
    rw [hx, one_mul]
  have e3 : y * x * y = y := by rw [← e2, hz', e1]
  have e4 : x * y = 1 := by
    have : y * (x * y) = y * 1 := by rw [← mul_assoc, e3, mul_one]
    exact mul_left_cancel this
  have e5 : x = y := by
    have := eq_inv_of_mul_eq_one_left e4
    rw [this, hyi]
  exact hxy e5

end Abstract

section SL

variable {m : ℕ} {K' : Type} [Field K']

theorem transvection_noncomm_central [CharP K' 2]
    (z : SpecialLinearGroup (Fin (m + 2)) K')
    (hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin (m + 2)) K')) :
    SpecialLinearGroup.transvection (show (0 : Fin (m + 2)) ≠ 1 by simp) (1 : K') *
      SpecialLinearGroup.transvection (show (1 : Fin (m + 2)) ≠ 0 by simp) (1 : K') ≠
    z * (SpecialLinearGroup.transvection (show (1 : Fin (m + 2)) ≠ 0 by simp) (1 : K') *
      SpecialLinearGroup.transvection (show (0 : Fin (m + 2)) ≠ 1 by simp) (1 : K')) := by
  intro h
  obtain ⟨r, -, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  have h2 : (1 : K') + 1 = 0 := by
    have := CharP.cast_eq_zero K' 2
    simpa [one_add_one_eq_two] using this
  have hM := congrArg (fun C : SpecialLinearGroup (Fin (m + 2)) K' =>
    (C : Matrix (Fin (m + 2)) (Fin (m + 2)) K')) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, ← hrz, SpecialLinearGroup.transvection_coe,
    Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.single_mul_single_same, Matrix.scalar_apply] at hM
  have a0 := congrFun (congrFun hM 0) 0
  have a1 := congrFun (congrFun hM 1) 1
  simp at a0 a1
  have hr0 : r = 0 := by rw [← a0, h2]
  rw [hr0, add_zero] at a1
  exact one_ne_zero a1

theorem transvection_noncomm_phi [CharP K' 2] {G : Type} [Group G]
    (φ : SpecialLinearGroup (Fin (m + 2)) K' →* G)
    (hker : ∀ d, φ d = 1 → d ∈ Subgroup.center (SpecialLinearGroup (Fin (m + 2)) K')) :
    φ (SpecialLinearGroup.transvection (show (0 : Fin (m + 2)) ≠ 1 by simp) (1 : K')) *
      φ (SpecialLinearGroup.transvection (show (1 : Fin (m + 2)) ≠ 0 by simp) (1 : K')) ≠
    φ (SpecialLinearGroup.transvection (show (1 : Fin (m + 2)) ≠ 0 by simp) (1 : K')) *
      φ (SpecialLinearGroup.transvection (show (0 : Fin (m + 2)) ≠ 1 by simp) (1 : K')) := by
  intro h
  have hz : SpecialLinearGroup.transvection (show (0 : Fin (m + 2)) ≠ 1 by simp) (1 : K') *
      SpecialLinearGroup.transvection (show (1 : Fin (m + 2)) ≠ 0 by simp) (1 : K') *
      (SpecialLinearGroup.transvection (show (1 : Fin (m + 2)) ≠ 0 by simp) (1 : K') *
        SpecialLinearGroup.transvection (show (0 : Fin (m + 2)) ≠ 1 by simp) (1 : K'))⁻¹ ∈
      Subgroup.center (SpecialLinearGroup (Fin (m + 2)) K') := by
    apply hker
    simp only [map_mul, map_inv, h, mul_inv_cancel]
  exact transvection_noncomm_central _ hz (by group)

theorem sl_commutator_top {p f' : ℕ} (hp5 : 5 ≤ p) (hf' : 1 ≤ f') [Finite K']
    (hK' : Nat.card K' = 2 ^ (p * f')) :
    commutator (SpecialLinearGroup (Fin (m + 2)) K') = ⊤ := by
  have hpf : 5 ≤ p * f' := by nlinarith
  have hbig : 8 ≤ 2 ^ (p * f') := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (p * f') := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : ∃ s : Finset K', s.card = 4 := by
    have : Fintype K' := Fintype.ofFinite K'
    have hc : 4 ≤ (Finset.univ : Finset K').card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK']
      omega
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hc
    exact ⟨s, hs⟩
  have := CFSG.LinearGroups.special_linear_isPerfect (K := K') (n := m + 2) (by omega) (Or.inr h4)
  exact Group.IsPerfect.commutator_eq_top

theorem lieModel_psl_of_central {p f' : ℕ} (hp5 : 5 ≤ p) (hf' : 1 ≤ f') [Finite K']
    (hK' : Nat.card K' = 2 ^ (p * f')) {G : Type} [Group G]
    (φ : SpecialLinearGroup (Fin (m + 2)) K' →* G)
    (hker : ∀ d, φ d = 1 → d ∈ Subgroup.center (SpecialLinearGroup (Fin (m + 2)) K')) :
    LieModel (↥φ.range ⧸ Subgroup.center ↥φ.range) .PSL (m + 2) 2 (p * f') := by
  obtain ⟨e⟩ := quotient_center_equiv φ hker (sl_commutator_top hp5 hf' hK')
  let e' : ProjectiveSpecialLinearGroup (Fin (m + 2)) K' ≃*
      ↥φ.range ⧸ Subgroup.center ↥φ.range := e
  have hpf : 5 ≤ p * f' := by nlinarith
  have hbig : 8 ≤ 2 ^ (p * f') := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (p * f') := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hadm : StatedLieAdmissible .PSL (m + 2) 2 (p * f') := by
    refine ⟨Nat.prime_two, by omega, by omega, ?_, ?_⟩
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
  refine Or.inl ⟨by decide, ?_⟩
  refine CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv e' ?_
  exact ⟨hadm, K', inferInstance, inferInstance, hK',
    ⟨projectiveSpecialLinearGroupEquivStatedProj (m + 2) K'⟩⟩

theorem sl_claims2' {p f' : ℕ} (hp5 : 5 ≤ p) (hf' : 1 ≤ f') [Finite K'] [CharP K' 2]
    (hK' : Nat.card K' = 2 ^ (p * f')) {σ' : K' ≃+* K'} (hσ' : σ' ≠ 1) {G : Type} [Group G]
    (α : MulAut G) (φ : SpecialLinearGroup (Fin (m + 2)) K' →* G)
    (hker : ∀ d, φ d = 1 → d ∈ Subgroup.center (SpecialLinearGroup (Fin (m + 2)) K'))
    (hαφ : ∀ B, α (φ B) = φ (SpecialLinearGroup.map σ'.toRingHom B)) (Q : Subgroup G)
    (hQ : φ.range = Q) : LayerClaims2 p α Q := by
  subst hQ
  have hperf := sl_commutator_top (m := m) hp5 hf' hK'
  have h01 : (0 : Fin (m + 2)) ≠ 1 := by simp
  have h10 : (1 : Fin (m + 2)) ≠ 0 := by simp
  refine ⟨?_, ?_, ⟨.PSL, m + 2, f', hf', lieModel_psl_of_central hp5 hf' hK' φ hker⟩, ?_⟩
  · rintro _ ⟨B, rfl⟩
    exact ⟨_, (hαφ B).symm⟩
  · obtain ⟨a, ha⟩ : ∃ a, σ' a ≠ a := by
      by_contra h
      exact hσ' (RingEquiv.ext fun a => by_contra fun hne => h ⟨a, hne⟩)
    refine not_inner_of_class_central φ hker hperf α (SpecialLinearGroup.map σ'.toRingHom) hαφ
      (fun d => Matrix.trace (d : Matrix (Fin (m + 2)) (Fin (m + 2)) K')) (fun E d => ?_)
      (SpecialLinearGroup.transvection h01 a * SpecialLinearGroup.transvection h10 1) ?_
    · show Matrix.trace ((E * d * E⁻¹ : SpecialLinearGroup (Fin (m + 2)) K') :
        Matrix (Fin (m + 2)) (Fin (m + 2)) K') =
        Matrix.trace (d : Matrix (Fin (m + 2)) (Fin (m + 2)) K')
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
        inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
    · simp only [map_mul, map_transvection]
      rw [trace_transvection_pair h01, trace_transvection_pair h01]
      simp only [map_one, mul_one]
      intro h
      exact ha (add_left_cancel h)
  · have hc : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hone : σ'.toRingHom (1 : K') = 1 := map_one _
    have ho : ∀ (i j : Fin (m + 2)) (hij : i ≠ j),
        ∃ k : ℕ, orderOf (φ (SpecialLinearGroup.transvection hij (1 : K'))) = 2 ^ k := by
      intro i j hij
      have hd := orderOf_map_dvd φ (SpecialLinearGroup.transvection hij (1 : K'))
      rw [orderOf_transvection_one hij] at hd
      rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
    refine ⟨φ (SpecialLinearGroup.transvection h01 1), ⟨_, rfl⟩, ?_,
      φ (SpecialLinearGroup.transvection h10 1), ⟨_, rfl⟩, ?_, ho _ _ h01, ho _ _ h10, ?_⟩
    · rw [hαφ, map_transvection, hone]
    · rw [hαφ, map_transvection, hone]
    · exact transvection_noncomm_phi φ hker

end SL

section SU

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem lieModel_psu_of_central {p f' : ℕ} (hp5 : 5 ≤ p) (hf' : 1 ≤ f')
    (hK : Nat.card K = (2 ^ (p * f')) ^ 2) {G : Type} [Group G]
    (φ : ↥(StatedSU (m + 3) (2 ^ (p * f')) K) →* G)
    (hker : ∀ d, φ d = 1 → d ∈ Subgroup.center ↥(StatedSU (m + 3) (2 ^ (p * f')) K)) :
    LieModel (↥φ.range ⧸ Subgroup.center ↥φ.range) .PSU (m + 3) 2 (p * f') := by
  have hg : 1 ≤ p * f' := by nlinarith
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbig : 2 ^ 5 ≤ 2 ^ (p * f') := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hnq : (m + 3, 2 ^ (p * f')) ≠ (3, 2) := by
    intro h
    simp only [Prod.mk.injEq] at h
    omega
  have hq := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) (f := p * f')
    hK (by omega) hnq
  have hP : Group.IsPerfect ↥(StatedSU (m + 3) (2 ^ (p * f')) K) := hq.1.1
  obtain ⟨e'⟩ := quotient_center_equiv φ hker Group.IsPerfect.commutator_eq_top
  let e'' : ↥(StatedSU (m + 3) (2 ^ (p * f')) K) ⧸
      Subgroup.center ↥(StatedSU (m + 3) (2 ^ (p * f')) K) ≃*
      StatedProj (StatedSU (m + 3) (2 ^ (p * f')) K) :=
    QuotientGroup.quotientMulEquivOfEq hq.2
  have hadm : StatedLieAdmissible .PSU (m + 3) 2 (p * f') := ⟨Nat.prime_two, hg, by omega, hnq⟩
  refine Or.inl ⟨by decide, ?_⟩
  exact ⟨hadm, K, inferInstance, inferInstance, hK, ⟨e'.symm.trans e''⟩⟩

@[expose] noncomputable def permSU {g : ℕ} (hK : Nat.card K = (2 ^ g) ^ 2) (σ : Equiv.Perm (Fin (m + 3))) :
    ↥(StatedSU (m + 3) (2 ^ g) K) :=
  ⟨permGLn σ, permGLn_mem (by omega) hK σ⟩

theorem permSU_mul {g : ℕ} (hK : Nat.card K = (2 ^ g) ^ 2) (σ τ : Equiv.Perm (Fin (m + 3))) :
    permSU hK (σ * τ) = permSU hK τ * permSU hK σ := by
  apply Subtype.ext
  apply Units.ext
  change (σ * τ).permMatrix K = τ.permMatrix K * σ.permMatrix K
  rw [Matrix.permMatrix_mul]

theorem permSU_one {g : ℕ} (hK : Nat.card K = (2 ^ g) ^ 2) :
    permSU (m := m) hK 1 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change (1 : Equiv.Perm (Fin (m + 3))).permMatrix K = 1
  exact Matrix.permMatrix_one

theorem permSU_injective {g : ℕ} (hK : Nat.card K = (2 ^ g) ^ 2) :
    Function.Injective (permSU (m := m) hK) := fun σ τ h => by
  have h1 := congrArg (fun u : ↥(StatedSU (m + 3) (2 ^ g) K) =>
    ((u : GL (Fin (m + 3)) K) : Matrix (Fin (m + 3)) (Fin (m + 3)) K)) h
  exact permMatrix_injective_n h1

theorem permSU_braid {g : ℕ} (hK : Nat.card K = (2 ^ g) ^ 2) :
    ∃ x y : ↥(StatedSU (m + 3) (2 ^ g) K), x * x = 1 ∧ y * y = 1 ∧
      (∃ σ₁ : Equiv.Perm (Fin (m + 3)), x = permSU hK σ₁) ∧
      (∃ σ₂ : Equiv.Perm (Fin (m + 3)), y = permSU hK σ₂) ∧
      ⁅x, y⁆ ∉ Subgroup.center ↥(StatedSU (m + 3) (2 ^ g) K) := by
  set i₀ : Fin (m + 3) := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin (m + 3) := ⟨1, by omega⟩ with hi₁
  set i₂ : Fin (m + 3) := ⟨2, by omega⟩ with hi₂
  have h01 : i₀ ≠ i₁ := fun h => by simp [hi₀, hi₁] at h
  have h12 : i₁ ≠ i₂ := fun h => by simp [hi₁, hi₂, Fin.ext_iff] at h
  have h02 : i₀ ≠ i₂ := fun h => by simp [hi₀, hi₂, Fin.ext_iff] at h
  set σ₁ : Equiv.Perm (Fin (m + 3)) := Equiv.swap i₀ i₁ with hσ₁
  set σ₂ : Equiv.Perm (Fin (m + 3)) := Equiv.swap i₁ i₂ with hσ₂
  have hbraid : (σ₂ * σ₁) * (σ₂ * σ₁) * (σ₂ * σ₁) = 1 := by
    have e1 : Equiv.swap i₁ i₂ * Equiv.swap i₀ i₁ * Equiv.swap i₁ i₂ = Equiv.swap i₂ i₀ :=
      Equiv.swap_mul_swap_mul_swap h01 h02
    have e2 : Equiv.swap i₀ i₁ * Equiv.swap i₁ i₂ * Equiv.swap i₀ i₁ = Equiv.swap i₂ i₀ := by
      have := Equiv.swap_mul_swap_mul_swap (x := i₂) (y := i₁) (z := i₀) h12.symm h02.symm
      rw [Equiv.swap_comm i₁ i₀, Equiv.swap_comm i₂ i₁] at this
      rw [this, Equiv.swap_comm i₀ i₂]
    calc (σ₂ * σ₁) * (σ₂ * σ₁) * (σ₂ * σ₁)
        = (σ₂ * σ₁ * σ₂) * (σ₁ * σ₂ * σ₁) := by group
      _ = 1 := by rw [hσ₁, hσ₂, e1, e2, Equiv.swap_mul_self]
  have hx : permSU hK σ₁ * permSU hK σ₁ = 1 := by
    rw [← permSU_mul, hσ₁, Equiv.swap_mul_self, permSU_one]
  have hy : permSU hK σ₂ * permSU hK σ₂ = 1 := by
    rw [← permSU_mul, hσ₂, Equiv.swap_mul_self, permSU_one]
  have hxy : permSU hK σ₁ ≠ permSU hK σ₂ := by
    intro h
    have := congrArg (fun f : Equiv.Perm (Fin (m + 3)) => f i₀) (permSU_injective hK h)
    simp only [hσ₁, hσ₂, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne h01 h02] at this
    exact h01 this.symm
  have h3 : (permSU hK σ₁ * permSU hK σ₂) ^ 3 = 1 := by
    have e : permSU hK σ₁ * permSU hK σ₂ = permSU hK (σ₂ * σ₁) := (permSU_mul hK σ₂ σ₁).symm
    calc (permSU hK σ₁ * permSU hK σ₂) ^ 3 = (permSU hK (σ₂ * σ₁)) ^ 3 := by rw [e]
      _ = permSU hK (σ₂ * σ₁) * permSU hK (σ₂ * σ₁) * permSU hK (σ₂ * σ₁) := pow_three' _
      _ = permSU hK ((σ₂ * σ₁) * ((σ₂ * σ₁) * (σ₂ * σ₁))) := by
        rw [← permSU_mul hK (σ₂ * σ₁) (σ₂ * σ₁),
          ← permSU_mul hK (σ₂ * σ₁) ((σ₂ * σ₁) * (σ₂ * σ₁))]
      _ = 1 := by rw [← mul_assoc, hbraid, permSU_one]
  exact ⟨_, _, hx, hy, ⟨σ₁, rfl⟩, ⟨σ₂, rfl⟩, braid_not_central _ _ hx hy hxy h3⟩

theorem su_claims2' {p f' : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hf' : 1 ≤ f')
    (hK : Nat.card K = (2 ^ (p * f')) ^ 2) {σ : K ≃+* K} (hσ : orderOf σ = p) {G : Type}
    [Group G] (α : MulAut G) (φ : ↥(StatedSU (m + 3) (2 ^ (p * f')) K) →* G)
    (hker : ∀ d, φ d = 1 → d ∈ Subgroup.center ↥(StatedSU (m + 3) (2 ^ (p * f')) K))
    (τ : ↥(StatedSU (m + 3) (2 ^ (p * f')) K) →* ↥(StatedSU (m + 3) (2 ^ (p * f')) K))
    (hτ : ∀ A, (((τ A : ↥(StatedSU (m + 3) (2 ^ (p * f')) K)) : GL (Fin (m + 3)) K) :
        Matrix (Fin (m + 3)) (Fin (m + 3)) K) =
      (((A : ↥(StatedSU (m + 3) (2 ^ (p * f')) K)) : GL (Fin (m + 3)) K) :
        Matrix (Fin (m + 3)) (Fin (m + 3)) K).map σ)
    (hαφ : ∀ A, α (φ A) = φ (τ A)) (Q : Subgroup G) (hQ : φ.range = Q) :
    LayerClaims2 p α Q := by
  have hg : 1 ≤ p * f' := by nlinarith
  have hn : 1 ≤ m + 3 := by omega
  have hc : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hσp : σ ^ p = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hbig : 2 ^ 5 ≤ 2 ^ (p * f') := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hnq : (m + 3, 2 ^ (p * f')) ≠ (3, 2) := by
    intro h
    simp only [Prod.mk.injEq] at h
    omega
  have hq := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) (f := p * f')
    hK (by omega) hnq
  have hP : Group.IsPerfect ↥(StatedSU (m + 3) (2 ^ (p * f')) K) := hq.1.1
  have hperf : commutator ↥(StatedSU (m + 3) (2 ^ (p * f')) K) = ⊤ :=
    Group.IsPerfect.commutator_eq_top
  have hτs : ∀ π : Equiv.Perm (Fin (m + 3)), τ (permSU hK π) = permSU hK π := fun π => by
    apply Subtype.ext
    apply Units.ext
    rw [hτ]
    change (π.permMatrix K).map σ = π.permMatrix K
    ext i j
    simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply]
    split_ifs <;> simp
  subst hQ
  refine ⟨?_, ?_, ⟨.PSU, m + 3, f', hf', lieModel_psu_of_central hp5 hf' hK φ hker⟩, ?_⟩
  · rintro _ ⟨A, rfl⟩
    exact ⟨τ A, (hαφ A).symm⟩
  ·
    obtain ⟨l, hl, hmove⟩ := exists_normOne_ne_fixed hp hp5 hf' hK hσ
    set A₀ : ↥(StatedSU (m + 3) (2 ^ (p * f')) K) := ⟨diagSU l, diagSU_mem hK l hl⟩ with hA₀
    refine not_inner_of_class_central φ hker hperf α τ hαφ
      (fun d => Matrix.trace (((d : ↥(StatedSU (m + 3) (2 ^ (p * f')) K)) : GL (Fin (m + 3)) K) :
        Matrix (Fin (m + 3)) (Fin (m + 3)) K)) (fun E d => ?_) A₀ ?_
    · show Matrix.trace ((((E * d * E⁻¹ : ↥(StatedSU (m + 3) (2 ^ (p * f')) K)) :
        GL (Fin (m + 3)) K)) : Matrix (Fin (m + 3)) (Fin (m + 3)) K) = _
      have := trace_conj_units (E : GL (Fin (m + 3)) K)
        (((d : ↥(StatedSU (m + 3) (2 ^ (p * f')) K)) : GL (Fin (m + 3)) K) :
          Matrix (Fin (m + 3)) (Fin (m + 3)) K)
      rw [← this]
      rfl
    · show Matrix.trace (((τ A₀ : ↥(StatedSU (m + 3) (2 ^ (p * f')) K)) : GL (Fin (m + 3)) K) :
        Matrix (Fin (m + 3)) (Fin (m + 3)) K) ≠ Matrix.trace
          (((A₀ : ↥(StatedSU (m + 3) (2 ^ (p * f')) K)) : GL (Fin (m + 3)) K) :
            Matrix (Fin (m + 3)) (Fin (m + 3)) K)
      rw [hτ, hA₀]
      simp only [coe_diagSU]
      rw [Matrix.diagonal_map (map_zero σ), Matrix.trace_diagonal, Matrix.trace_diagonal]
      have e1 : ∑ i : Fin (m + 3), σ (dvec (l : K) i) =
          σ (l : K) + (σ (l : K))⁻¹ + ((m + 1 : ℕ) : K) := by
        have := congrArg σ (sum_dvec (m := m) (l : K))
        simp only [map_sum] at this
        rw [this]
        simp
      show ∑ i : Fin (m + 3), σ (dvec (l : K) i) ≠ ∑ i : Fin (m + 3), dvec (l : K) i
      rw [e1, sum_dvec]
      intro h
      have h1 : σ (l : K) + (σ (l : K))⁻¹ = (l : K) + (l : K)⁻¹ := add_right_cancel h
      have hl0 : (l : K) ≠ 0 := l.ne_zero
      have hx0 : σ (l : K) ≠ 0 := fun h0 => hl0 (σ.injective (by rw [h0, map_zero]))
      have h2 : (σ (l : K) - l) * (σ (l : K) * l - 1) = 0 := by
        field_simp at h1
        linear_combination h1
      rcases mul_eq_zero.1 h2 with h3 | h3
      · exact hmove (sub_eq_zero.1 h3)
      ·
        have h4 : σ (l : K) = (l : K)⁻¹ := eq_inv_of_mul_eq_one_left (sub_eq_zero.1 h3)
        have h5 : σ^[2] (l : K) = l := by
          change σ (σ (l : K)) = l
          rw [h4, map_inv₀, h4, inv_inv]
        have h6 : ∀ k : ℕ, σ^[2 * k] (l : K) = l := by
          intro k
          induction k with
          | zero => rfl
          | succ k ih =>
            rw [show 2 * (k + 1) = 2 * k + 2 by ring, Function.iterate_add_apply, h5, ih]
        obtain ⟨k, hk⟩ := hpodd
        have h7 : σ^[p] (l : K) = l := by
          rw [← RingAut.coe_pow, hσp]
          rfl
        have h10 : σ (l : K) = l := by
          have h8 := Function.iterate_succ_apply' (⇑σ) (2 * k) (l : K)
          rw [h6 k] at h8
          rw [hk] at h7
          exact h8.symm.trans h7
        exact hmove h10
  · obtain ⟨x, y, hx, hy, ⟨σ₁, rfl⟩, ⟨σ₂, rfl⟩, hnc⟩ := permSU_braid (m := m) hK
    have ho : ∀ w : ↥(StatedSU (m + 3) (2 ^ (p * f')) K), w * w = 1 →
        ∃ k : ℕ, orderOf (φ w) = 2 ^ k := by
      intro w hw
      have h2 : orderOf (φ w) ∣ 2 := orderOf_dvd_of_pow_eq_one (by
        rw [pow_two, ← map_mul, hw, map_one])
      rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
    refine ⟨φ (permSU hK σ₁), ⟨_, rfl⟩, ?_, φ (permSU hK σ₂), ⟨_, rfl⟩, ?_, ho _ hx, ho _ hy, ?_⟩
    · rw [hαφ, hτs]
    · rw [hαφ, hτs]
    · intro h
      apply hnc
      apply hker
      rw [commutatorElement_def]
      simp only [map_mul, map_inv]
      rw [h]
      group

end SU

end CFSG.RankThree.PartOne.TCX.E
