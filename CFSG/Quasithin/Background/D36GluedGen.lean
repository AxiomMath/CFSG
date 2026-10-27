module

public import CFSG.Quasithin.Background.A3StructureDefs
import CFSG.Quasithin.Background.F918Z4c2Real

public section

namespace CFSG.Quasithin

open Matrix.SpecialLinearGroup Matrix

section SL2

variable {K : Type} [Field K]

@[expose] noncomputable def sl2RootGroup {i j : Fin 2} (hij : i ≠ j) :
    Subgroup (SpecialLinearGroup (Fin 2) K) :=
  (transvectionHom (A := K) hij).range

theorem card_sl2RootGroup {i j : Fin 2} (hij : i ≠ j) :
    Nat.card (sl2RootGroup (K := K) hij) = Nat.card K := by
  have hinj : Function.Injective (transvectionHom (A := K) (n := Fin 2) hij) := fun c d h =>
    Multiplicative.toAdd.injective (transvection_injective hij (by simpa using h))
  rw [sl2RootGroup, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
  exact Nat.card_congr Multiplicative.toAdd

@[expose] def sl2WeylElt : SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩

theorem sl2Weyl_conj (c : K) :
    (sl2WeylElt : SpecialLinearGroup (Fin 2) K) * transvection (show (0 : Fin 2) ≠ 1 by decide) c *
      (sl2WeylElt : SpecialLinearGroup (Fin 2) K)⁻¹ =
      transvection (show (1 : Fin 2) ≠ 0 by decide) (-c) := by
  apply Subtype.ext
  rw [coe_mul, coe_mul, coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2WeylElt, transvection_coe, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.one_apply, Matrix.single_apply, Matrix.vecMul, dotProduct,
      Matrix.add_apply]

theorem sl2RootGroup_sup_eq_top :
    sl2RootGroup (K := K) (show (0 : Fin 2) ≠ 1 by decide) ⊔
      sl2RootGroup (K := K) (show (1 : Fin 2) ≠ 0 by decide) = ⊤ := by
  have h := closure_range_toSpecialLinearGroup_eq_top_of_field (ι := Fin 2) (K := K)
  rw [eq_top_iff, ← h, Subgroup.closure_le]
  rintro _ ⟨t, rfl⟩
  obtain ⟨i, j, hij, c⟩ := t
  rw [TransvectionStruct.toSpecialLinearGroup_mk]
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact Subgroup.mem_sup_left ⟨Multiplicative.ofAdd c, by simp⟩
  · exact Subgroup.mem_sup_right ⟨Multiplicative.ofAdd c, by simp⟩
  · exact absurd rfl hij

theorem d36_factorization_card_sl2 [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    (Nat.card (SpecialLinearGroup (Fin 2) K)).factorization 2 = n := by
  rw [Z4c2.card_specialLinearGroup_two, hK]
  have h2n : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hne : (2 ^ n) ^ 2 - 1 ≠ 0 := by
    have : 4 ≤ (2 ^ n) ^ 2 := by nlinarith
    omega
  have hodd : ¬ 2 ∣ (2 ^ n) ^ 2 - 1 := by
    obtain ⟨m, hm⟩ : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have h4 : (2 ^ n) ^ 2 = 2 * (2 * m * m) := by rw [hm]; ring
    omega
  rw [Nat.factorization_mul (by positivity) hne, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hodd]
  simp [Nat.factorization_pow, Nat.Prime.factorization_self Nat.prime_two]

theorem map_conj_sl2RootGroup :
    (sl2RootGroup (K := K) (show (0 : Fin 2) ≠ 1 by decide)).map
        (MulAut.conj (sl2WeylElt : SpecialLinearGroup (Fin 2) K)).toMonoidHom =
      sl2RootGroup (K := K) (show (1 : Fin 2) ≠ 0 by decide) := by
  ext x
  constructor
  · rintro ⟨y, ⟨c, rfl⟩, rfl⟩
    refine ⟨Multiplicative.ofAdd (-Multiplicative.toAdd c), ?_⟩
    simp only [transvectionHom_apply, toAdd_ofAdd, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (sl2Weyl_conj (Multiplicative.toAdd c)).symm
  · rintro ⟨c, rfl⟩
    refine ⟨transvection (show (0 : Fin 2) ≠ 1 by decide) (-Multiplicative.toAdd c),
      ⟨Multiplicative.ofAdd (-Multiplicative.toAdd c), by simp⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, transvectionHom_apply]
    rw [sl2Weyl_conj, neg_neg]

theorem sl2Weyl_t_conj (t s : K) (ht : t ≠ 0) :
    (transvection (show (0 : Fin 2) ≠ 1 by decide) t *
        transvection (show (1 : Fin 2) ≠ 0 by decide) (-t⁻¹) *
        transvection (show (0 : Fin 2) ≠ 1 by decide) t) *
      transvection (show (1 : Fin 2) ≠ 0 by decide) s *
      (transvection (show (0 : Fin 2) ≠ 1 by decide) t *
        transvection (show (1 : Fin 2) ≠ 0 by decide) (-t⁻¹) *
        transvection (show (0 : Fin 2) ≠ 1 by decide) t)⁻¹ =
      transvection (show (0 : Fin 2) ≠ 1 by decide) (-(t ^ 2 * s)) := by
  apply Subtype.ext
  rw [coe_mul, coe_mul, coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transvection_coe, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.one_apply, Matrix.single_apply, Matrix.vecMul, dotProduct,
      Matrix.add_apply, coe_mul] <;> field_simp <;> ring

theorem zpowers_sup_lower_eq_top {t : K} (ht : t ≠ 0) :
    Subgroup.zpowers (transvection (show (0 : Fin 2) ≠ 1 by decide) t) ⊔
      sl2RootGroup (K := K) (show (1 : Fin 2) ≠ 0 by decide) = ⊤ := by
  set H := Subgroup.zpowers (transvection (show (0 : Fin 2) ≠ 1 by decide) t) ⊔
    sl2RootGroup (K := K) (show (1 : Fin 2) ≠ 0 by decide) with hH
  have hT : transvection (show (0 : Fin 2) ≠ 1 by decide) t ∈ H :=
    (le_sup_left : Subgroup.zpowers (transvection (show (0 : Fin 2) ≠ 1 by decide) t) ≤ H)
      (Subgroup.mem_zpowers _)
  have hT' : ∀ s : K, transvection (show (1 : Fin 2) ≠ 0 by decide) s ∈ H := fun s =>
    (le_sup_right : sl2RootGroup (K := K) (show (1 : Fin 2) ≠ 0 by decide) ≤ H)
      ⟨Multiplicative.ofAdd s, by simp⟩
  have hup : sl2RootGroup (K := K) (show (0 : Fin 2) ≠ 1 by decide) ≤ H := by
    rintro _ ⟨c, rfl⟩
    have hw : transvection (show (0 : Fin 2) ≠ 1 by decide) t *
        transvection (show (1 : Fin 2) ≠ 0 by decide) (-t⁻¹) *
        transvection (show (0 : Fin 2) ≠ 1 by decide) t ∈ H :=
      H.mul_mem (H.mul_mem hT (hT' _)) hT
    have h1 := H.mul_mem (H.mul_mem hw (hT' (-(Multiplicative.toAdd c / t ^ 2)))) (H.inv_mem hw)
    rw [sl2Weyl_t_conj t _ ht] at h1
    have e : -(t ^ 2 * -(Multiplicative.toAdd c / t ^ 2)) = Multiplicative.toAdd c := by
      field_simp
    rw [e] at h1
    simpa using h1
  rw [eq_top_iff, ← sl2RootGroup_sup_eq_top]
  exact sup_le hup le_sup_right

end SL2

theorem exists_gen_pair_strong {G : Type} [Group G] [Finite G] {n : ℕ} (hG : IsPSL 2 2 n G)
    {R : Subgroup G} (hRcard : Nat.card R = 2 ^ n) :
    ∃ g : G, R ⊔ R.map (MulAut.conj g).toMonoidHom = ⊤ ∧
      ∀ r ∈ R, r ≠ 1 → Subgroup.zpowers r ⊔ R.map (MulAut.conj g).toMonoidHom = ⊤ := by
  obtain ⟨K, hKf, hKfin, hKc, hKcard, hn2, ⟨e⟩⟩ := Z4c2.exists_equiv_sl hG
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (SpecialLinearGroup (Fin 2) K) := Finite.of_equiv G e.toEquiv
  have hfac := d36_factorization_card_sl2 (K := K) (by omega) hKcard
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  let P : Sylow 2 (SpecialLinearGroup (Fin 2) K) :=
    Sylow.ofCard (sl2RootGroup (K := K) h01) (by rw [card_sl2RootGroup, hKcard, hfac])
  let Q : Sylow 2 (SpecialLinearGroup (Fin 2) K) :=
    Sylow.ofCard (R.map e.toMonoidHom) (by
      rw [Subgroup.card_map_of_injective e.injective, hRcard, hfac])
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 2) K) P Q
  have hPQ : (sl2RootGroup (K := K) h01).map (MulAut.conj h).toMonoidHom = R.map e.toMonoidHom :=
    congrArg Sylow.toSubgroup hh
  have hc : (R.map (MulAut.conj (e.symm (h * sl2WeylElt * h⁻¹))).toMonoidHom).map e.toMonoidHom =
      (R.map e.toMonoidHom).map (MulAut.conj (h * sl2WeylElt * h⁻¹)).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp
  have e1 : (MulAut.conj (h * sl2WeylElt * h⁻¹)).toMonoidHom.comp (MulAut.conj h).toMonoidHom =
      (MulAut.conj h).toMonoidHom.comp
        (MulAut.conj (sl2WeylElt : SpecialLinearGroup (Fin 2) K)).toMonoidHom := by
    ext x
    simp [mul_assoc]
  have hlow : (R.map (MulAut.conj (e.symm (h * sl2WeylElt * h⁻¹))).toMonoidHom).map
      e.toMonoidHom = (sl2RootGroup (K := K) h10).map (MulAut.conj h).toMonoidHom := by
    rw [hc, ← hPQ, Subgroup.map_map, e1, ← Subgroup.map_map, map_conj_sl2RootGroup]
  refine ⟨e.symm (h * sl2WeylElt * h⁻¹), ?_, ?_⟩
  · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ e.surjective, hlow, ← hPQ,
      ← Subgroup.map_sup, sl2RootGroup_sup_eq_top]
    exact Subgroup.map_top_of_surjective _ (MulAut.conj h).surjective
  · intro r hr hr1
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    have her : e r ∈ R.map e.toMonoidHom := ⟨r, hr, rfl⟩
    rw [← hPQ] at her
    obtain ⟨y, ⟨c, rfl⟩, hyr⟩ := her
    have hc0 : Multiplicative.toAdd c ≠ 0 := by
      intro h0
      apply hr1
      apply e.injective
      have : c = 1 := Multiplicative.toAdd.injective h0
      rw [← hyr, this, map_one, map_one, map_one]
    have hz : (Subgroup.zpowers r).map e.toMonoidHom =
        (Subgroup.zpowers (transvection h01 (Multiplicative.toAdd c))).map
          (MulAut.conj h).toMonoidHom := by
      rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      have : (MulAut.conj h).toMonoidHom (transvection h01 (Multiplicative.toAdd c)) =
          e.toMonoidHom r := by
        have h' := hyr
        simpa using h'
      rw [this]
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ e.surjective, hz, hlow,
      ← Subgroup.map_sup, zpowers_sup_lower_eq_top hc0]
    exact Subgroup.map_top_of_surjective _ (MulAut.conj h).surjective

theorem exists_gen_pair_of_psl2_two {G : Type} [Group G] [Finite G] {n : ℕ} (hG : IsPSL 2 2 n G)
    {R : Subgroup G} (hRcard : Nat.card R = 2 ^ n) :
    ∃ g : G, R ⊔ R.map (MulAut.conj g).toMonoidHom = ⊤ :=
  (exists_gen_pair_strong hG hRcard).imp fun _ h => h.1

end CFSG.Quasithin
