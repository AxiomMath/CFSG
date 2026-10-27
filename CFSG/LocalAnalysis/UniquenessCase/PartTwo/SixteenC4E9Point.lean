module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16UTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.RankThreeUC Matrix
open CFSG.LieType.Universal.Unitary (SUid)

variable {G : Type} [Group G] [Finite G]

namespace UFrame

variable {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {L : Subgroup G}
  (F : UFrame V₀ V hV L)

private def dunit {K : Type} [Field K] (a b : Kˣ) : Fin 4 → Kˣ :=
  ![a, a, b, (a * a * b)⁻¹]

private def dvec {K : Type} [Field K] (a b : Kˣ) : Fin 4 → K :=
  fun i => (dunit a b i : K)

private theorem dunit_mul {K : Type} [Field K] (a a' b b' : Kˣ) :
    dunit (a * a') (b * b') = dunit a b * dunit a' b' := by
  funext i
  fin_cases i
  · simp [dunit]
  · simp [dunit]
  · simp [dunit]
  · have h : ((a * a') * (a * a') * (b * b') : Kˣ) = (a * a * b) * (a' * a' * b') := by
      ac_rfl
    simp [dunit, h, mul_inv]
    ac_rfl

private theorem dvec_mul {K : Type} [Field K] (a a' b b' : Kˣ) (i : Fin 4) :
    dvec (a * a') (b * b') i = dvec a b i * dvec a' b' i := by
  simp only [dvec]
  rw [dunit_mul, Pi.mul_apply, Units.val_mul]

private theorem dvec_norm {K : Type} [Field K] {σ : K ≃+* K} {Z : Subgroup Kˣ}
    (hZ : ∀ a ∈ Z, σ (a : K) * a = 1) {a b : Kˣ} (ha : a ∈ Z) (hb : b ∈ Z) (i : Fin 4) :
    σ (dvec a b i) * dvec a b i = 1 := by
  fin_cases i
  · simpa [dvec, dunit] using hZ a ha
  · simpa [dvec, dunit] using hZ a ha
  · simpa [dvec, dunit] using hZ b hb
  · simpa [dvec, dunit] using hZ _ (Z.inv_mem (Z.mul_mem (Z.mul_mem ha ha) hb))

private theorem dvec_det {K : Type} [Field K] (a b : Kˣ) : ∏ i, dvec a b i = 1 := by
  rw [Fin.prod_univ_four]
  have h : ((a * a * b * (a * a * b)⁻¹ : Kˣ) : K) = 1 := by simp
  simpa [dvec, dunit, mul_assoc] using h

private noncomputable def s16_C4E9Point_torus {K : Type} [Field K] {σ : K ≃+* K}
    (Z : Subgroup Kˣ) (hZ : ∀ a ∈ Z, σ (a : K) * a = 1) : ↥Z × ↥Z →* ↥(SUid σ 4) where
  toFun x := diagSU σ (dvec (x.1 : Kˣ) (x.2 : Kˣ)) (dvec_norm hZ x.1.2 x.2.2) (dvec_det _ _)
  map_one' := by
    apply ext_smul
    intro v
    rw [diagSU_smul, one_smul]
    funext i
    fin_cases i <;> simp [dvec, dunit]
  map_mul' x y := by
    apply ext_smul
    intro v
    rw [mul_smul, diagSU_smul, diagSU_smul, diagSU_smul]
    funext i
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
    rw [dvec_mul, mul_assoc]

private theorem s16_C4E9Point_torus_smul {K : Type} [Field K] {σ : K ≃+* K}
    (Z : Subgroup Kˣ) (hZ : ∀ a ∈ Z, σ (a : K) * a = 1) (x : ↥Z × ↥Z) (v : Fin 4 → K) :
    s16_C4E9Point_torus Z hZ x • v = fun i => dvec (x.1 : Kˣ) (x.2 : Kˣ) i * v i :=
  diagSU_smul σ _ (dvec_norm hZ x.1.2 x.2.2) (dvec_det _ _) v

private theorem s16_C4E9Point_torus_injective {K : Type} [Field K] {σ : K ≃+* K}
    (Z : Subgroup Kˣ) (hZ : ∀ a ∈ Z, σ (a : K) * a = 1) :
    Function.Injective (s16_C4E9Point_torus Z hZ) := by
  intro x y h
  have h1 := congrArg (fun g => g • (Pi.single 0 1 : Fin 4 → K)) h
  have h2 := congrArg (fun g => g • (Pi.single 2 1 : Fin 4 → K)) h
  simp only [s16_C4E9Point_torus_smul] at h1 h2
  have e1 := congrFun h1 0
  have e2 := congrFun h2 2
  simp [dvec, dunit] at e1 e2
  exact Prod.ext (Subtype.ext (Units.ext e1)) (Subtype.ext (Units.ext e2))

theorem exists_E9_stab_point {x : Fin 4 → F.K} (hx0 : x ≠ 0) (hx : herm F.σ x x = 0) :
    ∃ E : Subgroup (GL (Fin 4) F.K), E ≤ SUid F.σ 4 ∧ IsPGroup 3 E ∧ ¬ IsCyclic E ∧
      ∀ g ∈ E, ∀ y ∈ Submodule.span F.K {x},
        ((g : GL (Fin 4) F.K) : Matrix (Fin 4) (Fin 4) F.K) *ᵥ y ∈ Submodule.span F.K {x} := by
  have hK : Nat.card F.K = (2 ^ 1) ^ 2 := by rw [F.card_K]; norm_num
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F.K 2 := charP_of_card_sq (p := 2) (f := 1) hK
  have hσ : ∀ c : F.K, F.σ c * c = c ^ (2 ^ 1 + 1) := by
    intro c
    rw [F.norm_eq c]
    norm_num
  obtain ⟨Z, hZp, hZcard, hZ⟩ :=
    exists_torus_data (p := 3) (n := 1) Nat.prime_three (by norm_num) hK hσ
  set x0 : Fin 4 → F.K := ![1, 1, 0, 0] with hx0def
  have h11 : (1 : F.K) + 1 = 0 := by
    rw [← two_mul, mul_one]
    exact F.two_eq_zero
  have hx0_ne : x0 ≠ 0 := by
    intro h
    have h0 : (1 : F.K) = 0 := by simpa [hx0def] using congrFun h 0
    exact one_ne_zero h0
  have hx0_sing : herm F.σ x0 x0 = 0 := by
    simp only [herm, hx0def, Fin.sum_univ_four]
    show F.σ 1 * 1 + F.σ 1 * 1 + F.σ 0 * 0 + F.σ 0 * 0 = 0
    simp only [map_one, map_zero, one_mul, zero_mul, add_zero]
    exact h11
  have htheta : ∀ (a b : ↥Z),
      s16_C4E9Point_torus Z hZ (a, b) • x0 = ((a : F.Kˣ) : F.K) • x0 := by
    intro a b
    rw [s16_C4E9Point_torus_smul Z hZ (a, b) x0]
    funext i
    fin_cases i <;> simp [dvec, dunit, hx0def]
  have htrans : MulAction.IsPretransitive (↥(SUid F.σ 4)) (isoPts F.σ 4) :=
    isPretransitive_isoPts F.isUnitary (by norm_num : 3 ≤ 4)
  obtain ⟨t, ht⟩ := htrans.exists_smul_eq (pt x0 hx0_ne hx0_sing) (pt x hx0 hx)
  have ht_ne : t • x0 ≠ 0 := (smul_ne_zero_iff_ne t).mpr hx0_ne
  have ht_sing : herm F.σ (t • x0) (t • x0) = 0 := by
    rw [herm_smul_smul]
    exact hx0_sing
  have hpt : pt (t • x0) ht_ne ht_sing = pt x hx0 hx := by
    change t • pt x0 hx0_ne hx0_sing = pt x hx0 hx
    exact ht
  obtain ⟨c, hc⟩ :=
    (pt_eq_pt_iff (v := t • x0) (w := x) ht_ne hx0 ht_sing hx).mp hpt
  have hc0 : c ≠ 0 := by
    intro hc0eq
    exact ht_ne (by rw [← hc, hc0eq, zero_smul])
  have htinv : t⁻¹ • x = c⁻¹ • x0 := by
    have h1 : c • (t⁻¹ • x) = x0 := by
      have h2 : t⁻¹ • (c • x) = t⁻¹ • (t • x0) := by rw [hc]
      rwa [smul_comm t⁻¹ c x, inv_smul_smul] at h2
    calc t⁻¹ • x = c⁻¹ • (c • (t⁻¹ • x)) := by
          rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • x0 := by rw [h1]
  have hscale : ∀ (ab : ↥Z × ↥Z) (d : F.K),
      (t * s16_C4E9Point_torus Z hZ ab * t⁻¹ : ↥(SUid F.σ 4)) • (d • x)
        = (d * ((ab.1 : F.Kˣ) : F.K)) • x := by
    rintro ⟨a, b⟩ d
    rw [mul_smul, mul_smul]
    rw [smul_comm t⁻¹ d x]
    rw [htinv]
    rw [smul_smul d c⁻¹ x0]
    rw [smul_comm (s16_C4E9Point_torus Z hZ (a, b)) (d * c⁻¹) x0]
    rw [htheta a b]
    rw [smul_smul (d * c⁻¹) ((a : F.Kˣ) : F.K) x0]
    rw [smul_comm t (((d * c⁻¹) * ((a : F.Kˣ) : F.K))) x0]
    rw [← hc]
    rw [smul_smul (((d * c⁻¹) * ((a : F.Kˣ) : F.K))) c x]
    have hcoef : ((d * c⁻¹) * ((a : F.Kˣ) : F.K)) * c = d * ((a : F.Kˣ) : F.K) := by
      calc ((d * c⁻¹) * ((a : F.Kˣ) : F.K)) * c
          = d * ((a : F.Kˣ) : F.K) * (c⁻¹ * c) := by ring
        _ = d * ((a : F.Kˣ) : F.K) * 1 := by rw [inv_mul_cancel₀ hc0]
        _ = d * ((a : F.Kˣ) : F.K) := by rw [mul_one]
    rw [hcoef]
  set Ψ : ↥Z × ↥Z →* GL (Fin 4) F.K :=
    (SUid F.σ 4).subtype.comp ((MulAut.conj t).toMonoidHom.comp (s16_C4E9Point_torus Z hZ))
    with hΨ
  have hΨa : ∀ a, Ψ a = ((t * s16_C4E9Point_torus Z hZ a * t⁻¹ : ↥(SUid F.σ 4)) :
      GL (Fin 4) F.K) := fun a => rfl
  have hinj : Function.Injective Ψ := by
    rw [hΨ]
    exact (SUid F.σ 4).subtype_injective.comp
      ((MulAut.conj t).injective.comp (s16_C4E9Point_torus_injective Z hZ))
  have hEspan : Ψ.range ≤ SUid F.σ 4 := by
    rintro _ ⟨a, rfl⟩
    rw [hΨa a]
    exact (t * s16_C4E9Point_torus Z hZ a * t⁻¹).2
  have hcardE : Nat.card Ψ.range = 3 ^ 2 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, hZcard]
    norm_num
  have hA : ∀ a : ↥Z × ↥Z, a ^ 3 = 1 := fun a => by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · simpa using hZp a.1 a.1.2
    · simpa using hZp a.2 a.2.2
  have hEab : IsElemAbelian 3 Ψ.range := isElemAbelian_range Ψ hA
  have hPGroup : IsPGroup 3 Ψ.range :=
    fun g => ⟨1, Subtype.ext (by simpa using hEab.2 (g : GL (Fin 4) F.K) g.2)⟩
  have hNotCyc : ¬ IsCyclic Ψ.range := by
    intro hcyc
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have h1 : orderOf g = 3 ^ 2 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcardE]
    have h3 : (g : GL (Fin 4) F.K) ^ 3 = 1 := hEab.2 g g.2
    have h4 : g ^ 3 = 1 := Subtype.ext h3
    have hdvd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one h4
    rw [h1] at hdvd
    have hle : 3 ^ 2 ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    exact absurd hle (by norm_num)
  refine ⟨Ψ.range, hEspan, hPGroup, hNotCyc, ?_⟩
  rintro g ⟨ab, rfl⟩ y hy
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hy
  rw [hΨa ab]
  rw [← CFSG.ClassicalGroups.Unitary.smul_def F.σ
    (t * s16_C4E9Point_torus Z hZ ab * t⁻¹) (d • x)]
  rw [hscale ab d]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

end UFrame

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
