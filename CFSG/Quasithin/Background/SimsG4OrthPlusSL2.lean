module

public import CFSG.Quasithin.Background.SimsG4Core
import CFSG.Quasithin.Background.SimsG4OrthURefl
import CFSG.GH74.Uniqueness.Bender.Dickson
import CFSG.Timmesfeld.RankOne.SL2

public section

open Matrix

namespace CFSG.Quasithin.SimsG4.OrthPlus

section General

variable {G : Type*} [Group G]

theorem exists_two_subgroup_of_comm {L : Subgroup G}
    (hcomm : ∀ x ∈ L, ∀ y ∈ L, x * x = 1 → y * y = 1 → x * y = y * x)
    {u : G} (huL : u ∈ L) (hu : u * u = 1) (hu1 : u ≠ 1) :
    ∃ P : Subgroup G, IsPGroup 2 P ∧ P ≠ ⊥ ∧ ∀ x ∈ L, ∀ p ∈ P, x * p * x⁻¹ ∈ P := by
  let P : Subgroup G :=
    { carrier := {x | x ∈ L ∧ x * x = 1}
      mul_mem' := by
        rintro a b ⟨haL, ha⟩ ⟨hbL, hb⟩
        refine ⟨L.mul_mem haL hbL, ?_⟩
        have hab := hcomm a haL b hbL ha hb
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [← hab]
          _ = (a * a) * (b * b) := by group
          _ = 1 := by rw [ha, hb, one_mul]
      one_mem' := ⟨L.one_mem, mul_one 1⟩
      inv_mem' := by
        rintro a ⟨haL, ha⟩
        exact ⟨L.inv_mem haL, by rw [← _root_.mul_inv_rev, ha, inv_one]⟩ }
  refine ⟨P, fun x => ⟨1, Subtype.ext ?_⟩, ?_, ?_⟩
  · rw [SubgroupClass.coe_pow, OneMemClass.coe_one, pow_one, sq]
    exact x.2.2
  · intro hP
    have h : u ∈ P := ⟨huL, hu⟩
    rw [hP, Subgroup.mem_bot] at h
    exact hu1 h
  · rintro x hx p ⟨hpL, hp⟩
    refine ⟨L.mul_mem (L.mul_mem hx hpL) (L.inv_mem hx), ?_⟩
    calc x * p * x⁻¹ * (x * p * x⁻¹) = x * (p * p) * x⁻¹ := by group
      _ = 1 := by rw [hp, mul_one, mul_inv_cancel]

theorem odd_data_of_comm [Finite G] {L : Subgroup G} (hcomm : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a)
    (hodd : Odd (Nat.card L)) :
    (∀ a ∈ L, ∀ b ∈ L, a * b = b * a) ∧ (∃ m, Odd m ∧ ∀ t ∈ L, t ^ m = 1) ∧
      (∀ x ∈ L, ∀ t ∈ L, x * t * x⁻¹ ∈ L) ∧ ∀ x ∈ L, x * x ∈ L :=
  ⟨hcomm, ⟨Nat.card L, hodd, fun t ht => by
      have h : (⟨t, ht⟩ : L) ^ Nat.card L = 1 := pow_card_eq_one'
      exact congrArg Subtype.val h⟩,
    fun x hx t ht => L.mul_mem (L.mul_mem hx ht) (L.inv_mem hx), fun x hx => L.mul_mem hx hx⟩

end General

section Dihedral

@[expose] def rotations (z : ℕ) : Subgroup (DihedralGroup z) where
  carrier := {g | ∃ i, g = DihedralGroup.r i}
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨i + j, DihedralGroup.r_mul_r i j⟩
  one_mem' := ⟨0, DihedralGroup.one_def⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨-i, DihedralGroup.inv_r i⟩

theorem rotations_comm {z : ℕ} {a b : DihedralGroup z} (ha : a ∈ rotations z)
    (hb : b ∈ rotations z) : a * b = b * a := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  rw [DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]

theorem rotations_pow {z : ℕ} {a : DihedralGroup z} (ha : a ∈ rotations z) : a ^ z = 1 := by
  obtain ⟨i, rfl⟩ := ha
  rw [DihedralGroup.r_pow, ZMod.natCast_self, mul_zero, DihedralGroup.r_zero]

theorem rotations_conj {z : ℕ} (g : DihedralGroup z) {a : DihedralGroup z}
    (ha : a ∈ rotations z) : g * a * g⁻¹ ∈ rotations z := by
  obtain ⟨i, rfl⟩ := ha
  rcases g with j | j
  · exact ⟨i, by simp⟩
  · exact ⟨-i, by simp⟩

theorem mul_self_mem_rotations {z : ℕ} (g : DihedralGroup z) : g * g ∈ rotations z := by
  rcases g with j | j
  · exact ⟨j + j, DihedralGroup.r_mul_r j j⟩
  · exact ⟨0, by rw [DihedralGroup.sr_mul_self, DihedralGroup.one_def]⟩

end Dihedral

section SL2

variable {K : Type} [Field K]

theorem not_isIrredOnV_bot : ¬ IsIrredOnV (⊥ : Subgroup ((Fin 2 → K) ≃ₗ[K] (Fin 2 → K))) := by
  intro h
  rcases h (K ∙ (Pi.single 0 1 : Fin 2 → K)) (fun g hg w hw => by
      rw [Subgroup.mem_bot] at hg
      rw [hg]
      exact hw) with h0 | h1
  · have h := Submodule.mem_span_singleton_self (R := K) (Pi.single 0 1 : Fin 2 → K)
    rw [h0, Submodule.mem_bot] at h
    have := congrFun h 0
    simp at this
  · have h : (Pi.single 1 1 : Fin 2 → K) ∈ K ∙ (Pi.single 0 1 : Fin 2 → K) := by
      rw [h1]
      exact Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    have := congrFun hc 1
    simp at this

theorem trace_pow_two (X : Matrix (Fin 2) (Fin 2) K) :
    (X ^ 2).trace = X.trace ^ 2 - 2 * X.det := by
  simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.trace_fin_two, Matrix.det_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem trace_pow_three (X : Matrix (Fin 2) (Fin 2) K) :
    (X ^ 3).trace = X.trace ^ 3 - 3 * X.trace * X.det := by
  simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.trace_fin_two, Matrix.det_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem trace_pow_five (X : Matrix (Fin 2) (Fin 2) K) :
    (X ^ 5).trace = X.trace ^ 5 - 5 * X.trace ^ 3 * X.det + 5 * X.trace * X.det ^ 2 := by
  simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.trace_fin_two, Matrix.det_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring

variable [CharP K 2]

theorem trace_pow_four_eq (x : Matrix.SpecialLinearGroup (Fin 2) K)
    (hx : x = 1 ∨ x ^ 2 = 1 ∨ x ^ 3 = 1 ∨ x ^ 5 = 1) :
    (x : Matrix (Fin 2) (Fin 2) K).trace ^ 4 = (x : Matrix (Fin 2) (Fin 2) K).trace := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hd : (x : Matrix (Fin 2) (Fin 2) K).det = 1 := Matrix.SpecialLinearGroup.det_coe x
  have htr1 : (1 : Matrix (Fin 2) (Fin 2) K).trace = 0 := by
    rw [Matrix.trace_one, Fintype.card_fin]
    exact_mod_cast h2
  have hpow : ∀ k : ℕ, x ^ k = 1 → ((x : Matrix (Fin 2) (Fin 2) K) ^ k).trace = 0 := by
    intro k hk
    rw [← Matrix.SpecialLinearGroup.coe_pow, hk, Matrix.SpecialLinearGroup.coe_one, htr1]
  rcases hx with h | h | h | h
  · rw [h, Matrix.SpecialLinearGroup.coe_one, htr1]
    ring
  · have h' := hpow 2 h
    rw [trace_pow_two, hd] at h'
    generalize (x : Matrix (Fin 2) (Fin 2) K).trace = t at h' ⊢
    have ht0 : t ^ 2 = 0 := by linear_combination h' + h2
    rw [pow_eq_zero_iff two_ne_zero] at ht0
    rw [ht0]
    ring
  · have h' := hpow 3 h
    rw [trace_pow_three, hd] at h'
    generalize (x : Matrix (Fin 2) (Fin 2) K).trace = t at h' ⊢
    have hsq : (t * (t + 1)) ^ 2 = 0 := by
      linear_combination t * h' + (t ^ 3 + 2 * t ^ 2) * h2
    rw [pow_eq_zero_iff two_ne_zero] at hsq
    linear_combination (t ^ 2 - t + 1) * hsq - t * h2
  · have h' := hpow 5 h
    rw [trace_pow_five, hd] at h'
    generalize (x : Matrix (Fin 2) (Fin 2) K).trace = t at h' ⊢
    have hsq : (t * (t ^ 2 + t + 1)) ^ 2 = 0 := by
      linear_combination t * h' + (t ^ 5 + 4 * t ^ 4 + t ^ 3 - 2 * t ^ 2) * h2
    rw [pow_eq_zero_iff two_ne_zero] at hsq
    linear_combination (t - 1) * hsq

variable [Finite K]

theorem even_card_vec : Even (Nat.card (Fin 2 → K)) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := K), hn, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  exact (Nat.even_pow.mpr ⟨even_two, n.ne_zero⟩).pow_of_ne_zero (by norm_num)

theorem eq_bot_of_isPGroup {L P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)}
    (hirr : IsIrredOnV (L.map Matrix.SpecialLinearGroup.toLin')) (hP : IsPGroup 2 P)
    (hPL : ∀ x ∈ L, ∀ p ∈ P, x * p * x⁻¹ ∈ P) : P = ⊥ := by
  have h := core_trivial (L.map Matrix.SpecialLinearGroup.toLin') hirr even_card_vec
    (P.map Matrix.SpecialLinearGroup.toLin') (hP.map _) (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨p, hp, rfl⟩
      exact ⟨x * p * x⁻¹, hPL x hx p hp, by simp only [map_mul, map_inv]⟩)
  exact (Subgroup.map_eq_bot_iff_of_injective _ Matrix.SpecialLinearGroup.toLin'_injective).mp h

theorem card_SL2 :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  have : Fintype K := Fintype.ofFinite K
  rw [Matrix.card_SL_field, Nat.card_eq_fintype_card (α := K)]
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card K = k + 2 := ⟨Fintype.card K - 2, by omega⟩
  rw [Fin.prod_univ_two, hk]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  have e1 : (k + 2) ^ 2 - (k + 2) = (k + 2) * (k + 1) := Nat.sub_eq_of_eq_add (by ring)
  rw [e1, show k + 2 - 1 = k + 1 by omega, ← mul_assoc, Nat.mul_div_cancel _ (by omega), mul_comm]

theorem odd_data_of_card_two (hK : Nat.card K = 2)
    (L : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) :
    ∃ T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K), (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) ∧
      (∃ m, Odd m ∧ ∀ t ∈ T, t ^ m = 1) ∧ (∀ x ∈ L, ∀ t ∈ T, x * t * x⁻¹ ∈ T) ∧
        ∀ x ∈ L, x * x ∈ T := by
  have h6 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 6 := by
    rw [card_SL2, hK]
    norm_num
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Matrix.SpecialLinearGroup (Fin 2) K) 3
    (by rw [h6]; norm_num)
  set T₀ := Subgroup.zpowers g
  have hT₀ : Nat.card T₀ = 3 := by rw [Nat.card_zpowers, hg]
  have hidx : T₀.index = 2 := by
    have h := T₀.card_mul_index
    rw [hT₀, h6] at h
    omega
  have hN : T₀.Normal := Subgroup.normal_of_index_eq_two hidx
  refine ⟨T₀ ⊓ L, ?_, ⟨3, by norm_num, fun t ht => ?_⟩, ?_, ?_⟩
  · rintro a ⟨ha, -⟩ b ⟨hb, -⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact zpow_mul_comm g i j
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht.1
    have hg3 : g ^ 3 = 1 := by
      rw [← hg]
      exact pow_orderOf_eq_one g
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hg3,
      _root_.one_zpow]
  · rintro x hx t ⟨htT, htL⟩
    exact ⟨hN.conj_mem t htT x, L.mul_mem (L.mul_mem hx htL) (L.inv_mem hx)⟩
  · intro x hx
    refine ⟨?_, L.mul_mem hx hx⟩
    have := Subgroup.sq_mem_of_index_two hidx x
    rwa [sq] at this

theorem card_le_four (h : ∀ y : K, y ^ 4 = y) : Nat.card K ≤ 4 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hne := FiniteField.X_pow_card_sub_X_ne_zero K (p := 4) (by norm_num)
  have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq K (p := 4) (by norm_num)
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ, ← hdeg]
  refine Polynomial.card_le_degree_of_subset_roots fun y _ => ?_
  rw [Polynomial.mem_roots hne, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, h y, sub_self]

open CFSG.Glauberman.Dickson in
private theorem trace_mem_of_witness {m : ℕ}
    {M : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)}
    (W : SubfieldConjugacyWitness 2 m M) (x : Matrix.SpecialLinearGroup (Fin 2) K)
    (hx : QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) x ∈ M) :
    (x : Matrix (Fin 2) (Fin 2) K).trace ∈ W.K := by
  obtain ⟨A0, hA0⟩ := Matrix.ProjGenLinGroup.mk_surjective (W.phi ⟨_, hx⟩)
  obtain ⟨C, hC⟩ := Matrix.ProjGenLinGroup.mk_surjective W.conjugator
  have hproj : Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map W.K.subtype A0) =
      Matrix.ProjGenLinGroup.mk (C * Matrix.SpecialLinearGroup.toGL x * C⁻¹) := by
    have h := W.map_phi ⟨_, hx⟩
    rw [← hA0, h826_pglMap_mk, ← hC] at h
    rw [h, h826_pslToPGL_mk]
    simp only [map_mul, map_inv]
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hproj
  set B : Matrix (Fin 2) (Fin 2) K :=
    ((Matrix.GeneralLinearGroup.map W.K.subtype A0 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  have hB : ∀ i j, B i j ∈ W.K := fun i j => by
    change W.K.subtype (A0 i j) ∈ W.K
    exact (A0 i j).2
  have hmat : B * Matrix.scalar (Fin 2) (u : K) =
      (C : Matrix (Fin 2) (Fin 2) K) * (x : Matrix (Fin 2) (Fin 2) K) *
        ((C⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    have h := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) hu
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] at h
    exact h
  have htr : B.trace * u = (x : Matrix (Fin 2) (Fin 2) K).trace := by
    have h := congrArg Matrix.trace hmat
    rw [Matrix.trace_units_conj] at h
    rw [← h, Matrix.scalar_apply, Matrix.trace_fin_two, Matrix.trace_fin_two]
    simp [Matrix.mul_diagonal]
    ring
  have h1 : (B * Matrix.scalar (Fin 2) (u : K)).det = B.det * (u : K) ^ 2 := by
    rw [Matrix.det_mul, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two]
    ring
  have h2 : ((C : Matrix (Fin 2) (Fin 2) K) * (x : Matrix (Fin 2) (Fin 2) K) *
      ((C⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one,
      ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hdet : B.det * (u : K) ^ 2 = 1 := by rw [← h1, hmat, h2]
  have hBdet : B.det ∈ W.K := by
    rw [Matrix.det_fin_two]
    exact W.K.sub_mem (W.K.mul_mem (hB 0 0) (hB 1 1)) (W.K.mul_mem (hB 0 1) (hB 1 0))
  have hu2 : (u : K) ^ 2 ∈ W.K := by
    have : (u : K) ^ 2 = B.det⁻¹ := eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hdet)
    rw [this]
    exact W.K.inv_mem hBdet
  have huK := mem_of_sq_mem_subfield W.K hu2
  rw [← htr, Matrix.trace_fin_two]
  exact W.K.mul_mem (W.K.add_mem (hB 0 0) (hB 1 1)) huK

private theorem alternating_five_pow_cases : ∀ σ : alternatingGroup (Fin 5),
    σ = 1 ∨ σ ^ 2 = 1 ∨ σ ^ 3 = 1 ∨ σ ^ 5 = 1 := by
  decide +kernel

end SL2

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private noncomputable def toPSL :
    Matrix.SpecialLinearGroup (Fin 2) K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
  MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)))
    ⟨fun x y hxy => by
      have h : x⁻¹ * y ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) :=
        QuotientGroup.eq.mp hxy
      rw [CFSG.Timmesfeld.RankOne.center_SL2_eq_bot K, Subgroup.mem_bot] at h
      exact inv_mul_eq_one.mp h, QuotientGroup.mk'_surjective _⟩

private theorem toPSL_apply (x : Matrix.SpecialLinearGroup (Fin 2) K) :
    toPSL x = QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) x := rfl

theorem sl2_trace_field_cases
    (L : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K))
    (hirr : IsIrredOnV (L.map Matrix.SpecialLinearGroup.toLin'))
    (htr : ∀ K₁ : Subfield K, (∀ x ∈ L, (x : Matrix (Fin 2) (Fin 2) K).trace ∈ K₁) → K₁ = ⊤) :
    (L = ⊤ ∧ 4 ≤ Nat.card K) ∨
      ∃ T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K), (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) ∧
        (∃ m, Odd m ∧ ∀ t ∈ T, t ^ m = 1) ∧ (∀ x ∈ L, ∀ t ∈ T, x * t * x⁻¹ ∈ T) ∧
          ∀ x ∈ L, x * x ∈ T := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hcard : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hn1 : 1 ≤ (n : ℕ) := n.pos
  by_cases hn2 : (n : ℕ) = 1
  · exact Or.inr (odd_data_of_card_two (by rw [hcard, hn2]; norm_num) L)
  have h4 : 4 ≤ Nat.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) (by omega)
  set M := L.map (toPSL (K := K)).toMonoidHom
  let eLM : L ≃* M := L.equivMapOfInjective (toPSL (K := K)).toMonoidHom toPSL.injective
  have hcardLM : Nat.card L = Nat.card M := Nat.card_congr eLM.toEquiv
  let f : M →* Matrix.SpecialLinearGroup (Fin 2) K :=
    (toPSL (K := K)).symm.toMonoidHom.comp M.subtype
  have hfinj : Function.Injective f := toPSL.symm.injective.comp Subtype.val_injective
  have hLf : ∀ x (hx : x ∈ L), f (eLM ⟨x, hx⟩) = x := fun x _ => toPSL.symm_apply_apply x
  have hcommL : (∀ a b : M, a * b = b * a) → ∀ a ∈ L, ∀ b ∈ L, a * b = b * a := by
    intro h a ha b hb
    have h1 : eLM (⟨a, ha⟩ * ⟨b, hb⟩) = eLM (⟨b, hb⟩ * ⟨a, ha⟩) := by
      rw [map_mul, map_mul, h]
    exact congrArg Subtype.val (eLM.injective h1)
  have hnorm : ∀ N : Subgroup M, N.Normal → ∀ x ∈ L, ∀ p ∈ N.map f, x * p * x⁻¹ ∈ N.map f := by
    rintro N hN x hx _ ⟨q, hq, rfl⟩
    refine ⟨eLM ⟨x, hx⟩ * q * (eLM ⟨x, hx⟩)⁻¹, hN.conj_mem q hq _, ?_⟩
    rw [map_mul, map_mul, map_inv, hLf x hx]
  have hpowL : ∀ {X : Type} [Group X] (e : L ≃* X) (x : Matrix.SpecialLinearGroup (Fin 2) K)
      (hx : x ∈ L) (k : ℕ), e ⟨x, hx⟩ ^ k = 1 → x ^ k = 1 := by
    intro X _ e x hx k h
    have h1 : e (⟨x, hx⟩ ^ k) = e 1 := by rw [map_pow, h, map_one]
    exact congrArg Subtype.val (e.injective h1)
  have htop : ∀ {m : ℕ} (W : CFSG.Glauberman.Dickson.SubfieldConjugacyWitness 2 m M), m = n := by
    intro m W
    have hW : W.K = ⊤ := htr W.K fun x hx =>
      trace_mem_of_witness W x (by rw [← toPSL_apply]; exact Subgroup.mem_map_of_mem _ hx)
    have h1 : Nat.card W.K = Nat.card K := by
      rw [hW]
      exact Nat.card_congr Subfield.topEquiv.toEquiv
    rw [W.card_eq, hcard] at h1
    exact Nat.pow_right_injective le_rfl h1
  have hodd1 := CFSG.GH74.Uniqueness.Bender.odd_two_pow_sub_one n hn1
  have hodd2 := CFSG.GH74.Uniqueness.Bender.odd_two_pow_add_one n hn1
  have hg : Nat.gcd (2 ^ (n : ℕ) - 1) 2 = 1 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd1.not_two_dvd_nat)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification_with_subfield
      (p := 2) (f := n) hcard M with
    hEl | ⟨z, hz, hzc, hcyc⟩ | ⟨z, hz, -, ⟨eD⟩⟩ | ⟨-, ⟨eA4⟩⟩ | ⟨h16, -⟩ | ⟨-, ⟨eA5⟩⟩ |
      ⟨m, t, -, ht, N, C, hN, hNel, -, hCcyc, hCcard, -, hsup⟩ | ⟨m, hm0, -, ⟨eP⟩, ⟨W⟩⟩ |
      ⟨m, hm0, hmn, -, ⟨W⟩⟩
  ·
    exfalso
    have hP : IsPGroup 2 L := (@CFSG.IsElementaryAbelian.isPGroup 2 M _ hEl).of_equiv eLM.symm
    have hbot := eq_bot_of_isPGroup hirr hP fun x hx p hp =>
      L.mul_mem (L.mul_mem hx hp) (L.inv_mem hx)
    rw [hbot, Subgroup.map_bot] at hirr
    exact not_isIrredOnV_bot hirr
  ·
    right
    rw [hcard, hg, Nat.div_one, Nat.div_one] at hz
    refine ⟨L, odd_data_of_comm (hcommL fun a b => ?_) ?_⟩
    · haveI := hcyc
      exact IsCyclic.isMulCommutative.is_comm.comm a b
    · rw [hcardLM, hzc]
      exact hz.elim (Odd.of_dvd_nat hodd1) (Odd.of_dvd_nat hodd2)
  ·
    right
    rw [hcard, hg, Nat.div_one, Nat.div_one] at hz
    have hzodd : Odd z := hz.elim (Odd.of_dvd_nat hodd1) (Odd.of_dvd_nat hodd2)
    let g : DihedralGroup z →* Matrix.SpecialLinearGroup (Fin 2) K := f.comp eD.symm.toMonoidHom
    have hgx : ∀ x (hx : x ∈ L), g (eD (eLM ⟨x, hx⟩)) = x := fun x hx => by
      change f (eD.symm (eD (eLM ⟨x, hx⟩))) = x
      rw [MulEquiv.symm_apply_apply, hLf x hx]
    refine ⟨(rotations z).map g, ?_, ⟨z, hzodd, ?_⟩, ?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, rotations_comm ha hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, rotations_pow ha, map_one]
    · rintro x hx _ ⟨a, ha, rfl⟩
      refine ⟨_, rotations_conj (eD (eLM ⟨x, hx⟩)) ha, ?_⟩
      rw [map_mul, map_mul, map_inv, hgx x hx]
    · intro x hx
      refine ⟨_, mul_self_mem_rotations (eD (eLM ⟨x, hx⟩)), ?_⟩
      rw [map_mul, hgx x hx]
  ·
    exfalso
    let e := eLM.trans eA4
    have hcomm : ∀ x ∈ L, ∀ y ∈ L, x * x = 1 → y * y = 1 → x * y = y * x := by
      intro x hx y hy hx2 hy2
      have h1 : e ⟨x, hx⟩ * e ⟨x, hx⟩ = 1 := by
        rw [← map_mul, show (⟨x, hx⟩ : L) * ⟨x, hx⟩ = 1 from Subtype.ext hx2, map_one]
      have h2 : e ⟨y, hy⟩ * e ⟨y, hy⟩ = 1 := by
        rw [← map_mul, show (⟨y, hy⟩ : L) * ⟨y, hy⟩ = 1 from Subtype.ext hy2, map_one]
      have h3 := CFSG.GH74.Uniqueness.Bender.A4_involutions_commute _ _ h1 h2
      have h4 : e (⟨x, hx⟩ * ⟨y, hy⟩) = e (⟨y, hy⟩ * ⟨x, hx⟩) := by rw [map_mul, map_mul, h3]
      exact congrArg Subtype.val (e.injective h4)
    obtain ⟨a, ha, ha1⟩ := CFSG.GH74.Uniqueness.Bender.A4_exists_involution
    have hu : ((e.symm a : L) : Matrix.SpecialLinearGroup (Fin 2) K) *
        (e.symm a : L) = 1 := by
      rw [← Subgroup.coe_mul, ← map_mul, ha, map_one, Subgroup.coe_one]
    have hu1 : ((e.symm a : L) : Matrix.SpecialLinearGroup (Fin 2) K) ≠ 1 := by
      intro h
      apply ha1
      have : e.symm a = 1 := Subtype.ext h
      rw [← e.apply_symm_apply a, this, map_one]
    obtain ⟨P, hP2, hPne, hPL⟩ := exists_two_subgroup_of_comm hcomm (e.symm a).2 hu hu1
    exact hPne (eq_bot_of_isPGroup hirr hP2 hPL)
  ·
    exact absurd h16 (CFSG.GH74.Uniqueness.Bender.not_sixteen_dvd n hn1)
  ·
    left
    let e := eLM.trans eA5
    have horder : ∀ x ∈ L, x = 1 ∨ x ^ 2 = 1 ∨ x ^ 3 = 1 ∨ x ^ 5 = 1 := by
      intro x hx
      rcases alternating_five_pow_cases (e ⟨x, hx⟩) with h | h | h | h
      · left
        have h1 : e ⟨x, hx⟩ = e 1 := by rw [h, map_one]
        exact congrArg Subtype.val (e.injective h1)
      · exact Or.inr (Or.inl (hpowL e x hx 2 h))
      · exact Or.inr (Or.inr (Or.inl (hpowL e x hx 3 h)))
      · exact Or.inr (Or.inr (Or.inr (hpowL e x hx 5 h)))
    have hK₁ := htr (RingHom.eqLocusField (iterateFrobenius K 2 2) (RingHom.id K)) fun x hx => by
      rw [RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply]
      exact trace_pow_four_eq x (horder x hx)
    have hall : ∀ y : K, y ^ 4 = y := fun y => by
      have hy : y ∈ RingHom.eqLocusField (iterateFrobenius K 2 2) (RingHom.id K) := by
        rw [hK₁]
        exact Subfield.mem_top y
      rw [RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply] at hy
      exact hy
    have hK4 : Nat.card K = 4 := le_antisymm (card_le_four hall) h4
    refine ⟨Subgroup.eq_top_of_card_eq L ?_, h4⟩
    rw [hcardLM, Nat.card_congr eA5.toEquiv, nat_card_alternatingGroup, card_SL2, hK4]
    simp [Nat.factorial]
  ·
    rw [hg, Nat.div_one] at ht
    by_cases hNb : N = ⊥
    · right
      have hC : C = ⊤ := by rw [hNb, bot_sup_eq] at hsup; exact hsup
      refine ⟨L, odd_data_of_comm (hcommL fun a b => ?_) ?_⟩
      · haveI := hCcyc
        have h := IsCyclic.isMulCommutative.is_comm.comm
          (⟨a, hC ▸ Subgroup.mem_top a⟩ : C) ⟨b, hC ▸ Subgroup.mem_top b⟩
        exact congrArg Subtype.val h
      · rw [hcardLM, ← Subgroup.card_top (G := M), ← hC, hCcard]
        exact Odd.of_dvd_nat hodd1 ht
    · exfalso
      have hP2 : IsPGroup 2 (N.map f) := (@CFSG.IsElementaryAbelian.isPGroup 2 N _ hNel).map f
      have hPne : N.map f ≠ ⊥ := fun h =>
        hNb ((Subgroup.map_eq_bot_iff_of_injective N hfinj).mp h)
      exact hPne (eq_bot_of_isPGroup hirr hP2 (hnorm N hN))
  ·
    left
    have hmn := htop W
    subst hmn
    refine ⟨Subgroup.eq_top_of_card_eq L ?_, h4⟩
    rw [hcardLM, Nat.card_congr eP.toEquiv, CFSG.GH74.Uniqueness.Bender.card_psl2_even _ hn1,
      card_SL2, hcard]
  ·
    exfalso
    have hmn' := htop W
    subst hmn'
    have := Nat.le_of_dvd (by omega) hmn
    omega

end Main

end CFSG.Quasithin.SimsG4.OrthPlus
