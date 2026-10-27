module

public import CFSG.Quasithin.Background.G25Setup
public import CFSG.Quasithin.Background.G1Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.SL2Model
  CFSG.Quasithin.SL3Model
open scoped MatrixGroups Pointwise commutatorElement

section SL3

variable {F : Type*} [Field F]

theorem Qv_vE_decompose {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {q : SL(3, F)} (hq : q ∈ Qv (vE F a)) :
    ∃ β γ : F, q = Matrix.SpecialLinearGroup.transvection hab β *
      Matrix.SpecialLinearGroup.transvection hac γ := by
  obtain ⟨hq1, hq2⟩ := hq
  obtain ⟨β, hβ⟩ := hq2 (vE F b)
  obtain ⟨γ, hγ⟩ := hq2 (vE F c)
  refine ⟨β, γ, ?_⟩
  apply CFSG.Quasithin.G1.SL_ext_basis
  intro j
  rw [mul_smul, transvection_smul hac, transvection_smul hab]
  rcases TripleGrp.fin_three_cases a b c j hab hac hbc with rfl | rfl | rfl
  · rw [show (Pi.single j 1 : Fin 3 → F) = vE F j from rfl, hq1]
    simp [vE, hab.symm, hac.symm]
  · rw [show (Pi.single j 1 : Fin 3 → F) = vE F j from rfl, hβ]
    simp [vE, hbc.symm]
  · rw [show (Pi.single j 1 : Fin 3 → F) = vE F j from rfl, hγ]
    simp [vE, hbc, hab.symm]

theorem Qv_decompose (Q : SL(3, F)) {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {q : SL(3, F)} (hq : q ∈ Qv (Q • vE F a)) :
    ∃ q₁ q₂ : SL(3, F), q₁ ∈ Qv (Q • vE F a) ∧ q₂ ∈ Qv (Q • vE F a) ∧ q = q₁ * q₂ ∧
      q₁ • (Q • vE F c) = Q • vE F c ∧ q₂ • (Q • vE F b) = Q • vE F b := by
  have h0 : Q⁻¹ * q * Q⁻¹⁻¹ ∈ Qv (vE F a) := by
    have := (mem_Qv_conj Q⁻¹ q).2 hq
    rwa [inv_smul_smul] at this
  obtain ⟨β, γ, hβγ⟩ := Qv_vE_decompose hab hac hbc h0
  refine ⟨Q * Matrix.SpecialLinearGroup.transvection hab β * Q⁻¹,
    Q * Matrix.SpecialLinearGroup.transvection hac γ * Q⁻¹,
    (mem_Qv_conj Q _).2 (transvection_mem_Qv hab β),
    (mem_Qv_conj Q _).2 (transvection_mem_Qv hac γ), ?_, ?_, ?_⟩
  · have e : q = Q * (Q⁻¹ * q * Q⁻¹⁻¹) * Q⁻¹ := by group
    rw [e, hβγ]
    group
  · simp only [mul_smul, inv_smul_smul]
    rw [transvection_smul hab]
    simp [vE, hbc]
  · simp only [mul_smul, inv_smul_smul]
    rw [transvection_smul hac]
    simp [vE, hbc.symm]

end SL3

variable {G : Type*} [Group G]

namespace L3Setting

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (St : L3Setting n V V₁ L T H)
  {g h : G} (hg : g ∈ L) (hh : h ∈ L)

omit [Finite G] in
theorem exists_basis_Q (hV : V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h) :
    ∃ (Q : SL(3, GaloisField 2 n)) (lam : Fin 3 → GaloisField 2 n), (∀ k, lam k ≠ 0) ∧
      ∀ k, Q • vE (GaloisField 2 n) k = lam k • St.pvec (tripleConj_mem hg hh k) := by
  obtain ⟨Q, r, hr, h0, h1, h2⟩ := exists_basis_matrix (St.span_of_sum hg hh hV)
  refine ⟨Q, ![1, 1, r], ?_, ?_⟩
  · intro k
    fin_cases k <;> simp [hr]
  · intro k
    fin_cases k
    · have e : (⟨tripleConj g h 0, tripleConj_mem hg hh 0⟩ : ↥L) = 1 :=
        Subtype.ext (by simp [tripleConj])
      simp only [Fin.zero_eta, pvec, e, inv_one, map_one, one_smul, Matrix.cons_val_zero]
      simpa using h0
    · have e : (⟨tripleConj g h 1, tripleConj_mem hg hh 1⟩ : ↥L) = ⟨g, hg⟩ :=
        Subtype.ext (by simp [tripleConj])
      simp only [Fin.mk_one, pvec, e, Matrix.cons_val_one]
      simpa using h1
    · have e : (⟨tripleConj g h 2, tripleConj_mem hg hh 2⟩ : ↥L) = ⟨h, hh⟩ :=
        Subtype.ext (by simp [tripleConj])
      simp only [Fin.reduceFinMk, pvec, e]
      simpa using h2

theorem mem_normalizer_W_of_fix {k : Fin 3} (x : ↥(L ⊔ conjClosure V H))
    (hx : St.Phi x • St.pvec (tripleConj_mem hg hh k) = St.pvec (tripleConj_mem hg hh k)) :
    (x : G) ∈ Subgroup.normalizer
      ((TripleGrp.W (pCoreOf 2 (L ⊔ conjClosure V H)) (tripleU (conjClosure V H) g h) k :
        Subgroup G) : Set G) := by
  obtain ⟨-, -, -, hINorm, -⟩ := St.sxFacts
  have hfwd : ∀ z : ↥(L ⊔ conjClosure V H),
      St.Phi z • St.pvec (tripleConj_mem hg hh k) = St.pvec (tripleConj_mem hg hh k) →
      ∀ y ∈ TripleGrp.W (pCoreOf 2 (L ⊔ conjClosure V H)) (tripleU (conjClosure V H) g h) k,
        (z : G) * y * (z : G)⁻¹ ∈
          TripleGrp.W (pCoreOf 2 (L ⊔ conjClosure V H)) (tripleU (conjClosure V H) g h) k := by
    intro z hz y hy
    refine ⟨?_, hINorm _ z.2 y hy.2⟩
    exact St.conj_rconj_mem (tripleConj_mem hg hh k) (tripleConj_mem hg hh k) z
      ⟨1, by rw [hz, one_smul]⟩ hy.1
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨hfwd x hx y, fun hy => ?_⟩
  have hx' : St.Phi x⁻¹ • St.pvec (tripleConj_mem hg hh k) = St.pvec (tripleConj_mem hg hh k) := by
    rw [map_inv, inv_smul_eq_iff]
    exact hx.symm
  have := hfwd x⁻¹ hx' _ hy
  simpa [mul_assoc] using this

include St hg hh in
theorem tripleGrp_dec (hV : V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h) :
    ∀ (i j k : Fin 3), i ≠ j → i ≠ k → j ≠ k →
      ∀ u ∈ tripleU (conjClosure V H) g h i,
        ∃ u₁ ∈ tripleU (conjClosure V H) g h i ⊓ Subgroup.normalizer
            ((TripleGrp.W (pCoreOf 2 (L ⊔ conjClosure V H)) (tripleU (conjClosure V H) g h) k :
              Subgroup G) : Set G),
          ∃ u₂ ∈ tripleU (conjClosure V H) g h i ⊓ Subgroup.normalizer
            ((TripleGrp.W (pCoreOf 2 (L ⊔ conjClosure V H)) (tripleU (conjClosure V H) g h) j :
              Subgroup G) : Set G),
            ∃ s ∈ TripleGrp.W (pCoreOf 2 (L ⊔ conjClosure V H)) (tripleU (conjClosure V H) g h) i,
              u = u₁ * u₂ * s := by
  intro i j k hij hik hjk u hu
  obtain ⟨Q, lam, hlam, hQ⟩ := St.exists_basis_Q hg hh hV
  have hcm := tripleConj_mem hg hh
  have hT := St.tripleGrp hg hh hV
  have huI : u ∈ L ⊔ conjClosure V H := hT.Uk_le_I i hu
  have hQv : ∀ m, Qv (Q • vE (GaloisField 2 n) m) = Qv (St.pvec (hcm m)) := fun m => by
    rw [hQ m, Qv_smul (hlam m)]
  have h1 : St.Phi ⟨u, huI⟩ ∈ Qv (Q • vE (GaloisField 2 n) i) := by
    rw [hQv i]
    exact St.Phi_mem_Qv_of_mem_rconj (hcm i) ⟨u, huI⟩ hu
  obtain ⟨q₁, q₂, hq₁, hq₂, hq, hf₁, hf₂⟩ := Qv_decompose Q hij hik hjk h1
  have hfix : ∀ (m : Fin 3) (q : SL(3, GaloisField 2 n)),
      q • (Q • vE (GaloisField 2 n) m) = Q • vE (GaloisField 2 n) m →
        q • St.pvec (hcm m) = St.pvec (hcm m) := by
    intro m q hqm
    rw [hQ m, smul_comm] at hqm
    exact smul_right_injective _ (hlam m) hqm
  rw [hQv i] at hq₁ hq₂
  obtain ⟨x₁, hx₁U, hx₁⟩ := St.exists_lift (hcm i) hq₁
  obtain ⟨x₂, hx₂U, hx₂⟩ := St.exists_lift (hcm i) hq₂
  refine ⟨(x₁ : G), ⟨hx₁U, St.mem_normalizer_W_of_fix hg hh x₁ (by rw [hx₁]; exact hfix k q₁ hf₁)⟩,
    (x₂ : G), ⟨hx₂U, St.mem_normalizer_W_of_fix hg hh x₂ (by rw [hx₂]; exact hfix j q₂ hf₂)⟩,
    (((x₁ : G) * x₂)⁻¹ * u), ⟨?_, ?_⟩, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ hx₁U hx₂U)) hu
  · have hmem : (((x₁ * x₂)⁻¹ * ⟨u, huI⟩ : ↥(L ⊔ conjClosure V H)) : G) =
        ((x₁ : G) * x₂)⁻¹ * u := by simp
    rw [← hmem]
    refine (St.Phi_eq_one_iff_mem_S _).1 ?_
    rw [map_mul, map_inv, map_mul, hx₁, hx₂, hq]
    simp
  · group

include St hg hh in
theorem G25_four_inv (hV : V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h) :
    L ⊔ conjClosure V H ≤ Subgroup.normalizer
      ((TripleGrp.S₃ (pCoreOf 2 (L ⊔ conjClosure V H)) (tripleU (conjClosure V H) g h) :
        Subgroup G) : Set G) :=
  (St.tripleGrp hg hh hV).I_le_normalizer_S₃ (St.tripleGrp_dec hg hh hV)

end L3Setting

end CFSG.Quasithin
