module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResU3ThreeSub
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GUniGeom
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylRest13Known
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNinePGL
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneUnitaryLabel
public import CFSG.HardMathSupport.Lang.Proving.CubeNormOne

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.FQ
open CFSG.LocalAnalysis.GLTheoremA.T156.Uni (Induced exists_induced orderOf_eq_of_induced
  fixF_data fixF_pow charP_fixF subfieldHom subfieldInclusion coe_subfieldInclusion subfieldEquiv
  coe_subfieldEquiv_mk range_subfieldHom ggFixGeom_unitary simple_noncomm_proj
  eq_one_of_fixes_subfield)

namespace ResU3Three

theorem three_dvd_two_pow_div_add_one_U3Three {n : ℕ} (h3 : 3 ∣ 2 ^ n + 1) (h3n : 3 ∣ n) :
    3 ∣ 2 ^ (n / 3) + 1 := by
  obtain ⟨t, rfl⟩ := h3n
  rw [Nat.mul_div_cancel_left t (by norm_num)]
  rw [mul_comm, pow_mul] at h3
  set q := 2 ^ t
  have hmod : q ^ 3 % 3 = q % 3 := by
    rcases (by omega : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2) with h | h | h <;>
      simp [Nat.pow_mod, h]
  have h1 := Nat.mod_eq_zero_of_dvd h3
  have h2 : (q + 1) % 3 = 0 := by
    rw [Nat.add_mod] at h1 ⊢
    rw [hmod] at h1
    exact h1
  exact Nat.dvd_of_mod_eq_zero h2

theorem two_le_div_three_U3Three {n : ℕ} (hn : 1 ≤ n) (h3n : 3 ∣ n) (hn3 : n ≠ 3) :
    2 ≤ n / 3 := by
  obtain ⟨t, rfl⟩ := h3n
  rw [Nat.mul_div_cancel_left t (by norm_num)]
  omega

theorem exists_cube_root_U3Three {k K : Type} [Field k] [Finite k] [Field K] [Finite K]
    (j : k →+* K) {Q : ℕ} (hk : Nat.card k = Q) (hK : Nat.card K = Q ^ 3) (hQ : Q % 3 = 1)
    (c : k) : ∃ e : K, e ^ 3 = j c := by
  by_cases hc : c = 0
  · exact ⟨0, by rw [hc, map_zero]; ring⟩
  obtain ⟨a, rfl⟩ : ∃ a, Q = 3 * a + 1 := ⟨Q / 3, by omega⟩
  have hl : j c ≠ 0 := (map_ne_zero j).mpr hc
  have e1 : (3 * a + 1) ^ 3 - 1 = 3 * (3 * a * (3 * a ^ 2 + 3 * a + 1)) := by
    have h1 : (3 * a + 1) ^ 3 = 3 * (3 * a * (3 * a ^ 2 + 3 * a + 1)) + 1 := by ring
    rw [h1, Nat.add_sub_cancel]
  have h3 : 3 ∣ (3 * a + 1) ^ 3 - 1 := ⟨_, e1⟩
  rw [CFSG.HardMathSupport.Lang.Proving.cube_units_iff hK h3 hl, e1,
    Nat.mul_div_cancel_left _ (by norm_num), pow_mul, ← map_pow]
  have hck : c ^ (3 * a) = 1 := by
    have := Fintype.ofFinite k
    have h1 := FiniteField.pow_card_sub_one_eq_one c hc
    rwa [← Nat.card_eq_fintype_card, hk, Nat.add_sub_cancel] at h1
  rw [hck, map_one, one_pow]

theorem map_mem_guSet_U3Three {k K : Type} [Field k] [Field K] (ι : k →+* K) {q q₀ : ℕ}
    (hpow : ∀ b : k, ι b ^ q = ι (b ^ q₀)) {B : GL (Fin 3) k}
    (hB : B ∈ LargeEvenGUSet (Fin 3) k q₀) :
    Matrix.GeneralLinearGroup.map ι B ∈ LargeEvenGUSet (Fin 3) K q := by
  obtain ⟨μ, hμ0, hμq, hμ⟩ := hB
  refine ⟨ι μ, (map_ne_zero ι).mpr hμ0, by rw [hpow, hμq], ?_⟩
  have h1 : ((Matrix.GeneralLinearGroup.map ι B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (B : Matrix (Fin 3) (Fin 3) k).map ι := rfl
  have h2 : ((B : Matrix (Fin 3) (Fin 3) k).map ι).map (· ^ q) =
      ((B : Matrix (Fin 3) (Fin 3) k).map (· ^ q₀)).map ι := by
    ext a b
    simp [hpow]
  rw [h1, h2, ← Matrix.transpose_map, ← Matrix.map_mul, hμ]
  ext a b
  by_cases hab : a = b
  · subst hab
    simp
  · simp [Matrix.one_apply_ne hab]

variable {K : Type} [Field K] [Finite K]

theorem ggCenterKp_u3Three
    {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 2 ≤ n) :
    GGCenterKp (fun k => k ∣ 3) (LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n))) := by
  intro L' _ _ ψ hψ hker hperf
  have h₀ := TableBU.unitaryFieldData_of_card hK (by omega)
  haveI : CharP K 2 := h₀.charP
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (LargeEvenSUGroup (Fin 3) K (2 ^ n)) := Finite.of_injective
    (fun x : LargeEvenSUGroup (Fin 3) K (2 ^ n) => ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (fun x y hxy => Subtype.ext (Units.ext hxy))
  obtain ⟨φ, hφs, hφ⟩ := exists_cover_of_sections
    (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ n))) (QuotientGroup.mk'_surjective _)
    (fun E _ _ π hπ hcen =>
      CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central
        (F := K) (p := 2) (f := n) hK (by omega) le_rfl (by decide) (dq_ne_U3Three hn) hπ hcen)
    ψ hψ hker hperf
  have hkerMap : ψ.ker ≤ ((LargeEvenScalars (Fin 3) K).subgroupOf
      (LargeEvenSUGroup (Fin 3) K (2 ^ n))).map φ := by
    intro l hl
    obtain ⟨g, rfl⟩ := hφs l
    rw [MonoidHom.mem_ker, hφ g] at hl
    exact Subgroup.mem_map.mpr ⟨g, (QuotientGroup.eq_one_iff g).mp hl, rfl⟩
  have hcardZ : Nat.card ((CFSG.Open.StatedScalars (Fin 3) K).subgroupOf
      (CFSG.Open.StatedSU 3 (2 ^ n) K)) ∣ 3 := by
    rw [(CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (by norm_num : 1 ≤ 3)).2.2]
    exact Nat.gcd_dvd_left _ _
  exact (Subgroup.card_dvd_of_le hkerMap).trans ((Subgroup.card_map_dvd _ _).trans hcardZ)

theorem ggFixNoCompOn_u3Three [CharP K 2] {n : ℕ} (hn1 : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {σ : K ≃+* K} (hσ : Odd (orderOf σ)) (hdq : ((3 : ℕ), 2 ^ (n / orderOf σ)) ≠ (3, 2))
    {f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n)))} (hf : Induced (2 ^ n) σ f) :
    GGFixNoCompOn (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ n)))
        (LargeEvenGUSet (Fin 3) K (2 ^ n))) f
      (subfieldEquiv le_rfl hn1 hK hσ hdq hf).symm
      (regSetU3Three (fixF σ).subtype (2 ^ (n / orderOf σ))) := by
  intro φ hφI _ φ₀ hφ₀ hres J hJ
  obtain ⟨B, hBN, hBgu, hBreg, rfl⟩ := hφ₀
  have h := TableBU.unitaryFieldData_of_card hK hn1
  have hNK := TableBUE.gu_subset_normalizer (d := 3) h
  set ιB : GL (Fin 3) K := Matrix.GeneralLinearGroup.map (fixF σ).subtype B with hιB
  have hιBgu : ιB ∈ LargeEvenGUSet (Fin 3) K (2 ^ n) :=
    map_mem_guSet_U3Three (fixF σ).subtype
      (fun b => by rw [map_pow]; exact fixF_pow hn1 hK σ hσ b) hBgu
  have hagree : ∀ x : LargeEvenSUGroup (Fin 3) (fixF σ) (2 ^ (n / orderOf σ)),
      φ (subfieldHom hn1 hK σ hσ x) =
        TableB.projConj _ ⟨ιB, hNK hιBgu⟩ (subfieldHom hn1 hK σ hσ x) := by
    intro x
    have hx : subfieldHom hn1 hK σ hσ x ∈ ggFixDer f := by
      rw [← range_subfieldHom le_rfl hn1 hK hσ hdq hf]
      exact ⟨x, rfl⟩
    have h1 := hres _ hx
    have h2 : (subfieldEquiv le_rfl hn1 hK hσ hdq hf).symm ⟨subfieldHom hn1 hK σ hσ x, hx⟩ =
        QuotientGroup.mk x := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext (coe_subfieldEquiv_mk le_rfl hn1 hK hσ hdq hf x).symm
    rw [h2, TableB.projConj_mk, MulEquiv.symm_apply_eq] at h1
    have h3 := congrArg Subtype.val h1
    rw [coe_subfieldEquiv_mk] at h3
    change φ (subfieldHom hn1 hK σ hσ x) = _ at h3
    rw [h3]
    change LargeEvenProjMk _ (subfieldInclusion hn1 hK σ hσ _) =
      TableB.projConj _ ⟨ιB, hNK hιBgu⟩ (LargeEvenProjMk _ (subfieldInclusion hn1 hK σ hσ x))
    rw [show LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ n)) (subfieldInclusion hn1 hK σ hσ x)
      = ((subfieldInclusion hn1 hK σ hσ x : LargeEvenSUGroup (Fin 3) K (2 ^ n)) :
        LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n))) from rfl, TableB.projConj_mk]
    congr 1
  have hcI : TableB.projConj _ ⟨ιB, hNK hιBgu⟩ ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ n)))
        (LargeEvenGUSet (Fin 3) K (2 ^ n)) :=
    ⟨ιB, hιBgu, fun g g' hg => by
      rw [show LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ n)) g =
        ((g : LargeEvenSUGroup (Fin 3) K (2 ^ n)) : LargeEvenProj _) from rfl,
        TableB.projConj_mk]
      congr 1
      exact Subtype.ext hg.symm⟩
  have hI := RecipeFieldSU.coe_recIU (d := 3) h hK (by norm_num)
  have hmem : (TableB.projConj _ ⟨ιB, hNK hιBgu⟩)⁻¹ * φ ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ n)))
        (LargeEvenGUSet (Fin 3) K (2 ^ n)) := by
    rw [← hI] at hcI hφI ⊢
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hcI) hφI
  have h1 := eq_one_of_fixes_subfield le_rfl hn1 hK σ hσ hdq hmem fun g => by
    rw [MulAut.mul_apply, hagree, MulAut.inv_apply_self]
  have hφeq : φ = TableB.projConj _ ⟨ιB, hNK hιBgu⟩ := (inv_mul_eq_one.mp h1).symm
  rw [hφeq] at hJ
  exact not_isComponentOf_of_isSolvable (isSolvable_ggFix_projConj_of_reg _ hBreg) hJ

theorem ggFixDataKX_u3Three
    {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 2 ≤ n)
    (h3 : 3 ∣ 2 ^ n + 1) (h3n : 3 ∣ n) (hn3 : n ≠ 3)
    {f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n)))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ n))))
    (hord : orderOf f = 3) :
    GGFixDataKX 3 (fun k => k ∣ 3)
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ n)))
        (LargeEvenGUSet (Fin 3) K (2 ^ n))) f := by
  have hn1 : 1 ≤ n := by omega
  have h := TableBU.unitaryFieldData_of_card hK hn1
  haveI : CharP K 2 := h.charP
  obtain ⟨σ, hσf⟩ := exists_induced hf
  have hσord : orderOf σ = 3 :=
    (orderOf_eq_of_induced (d := 3) (by norm_num) hn1 hK hσf).trans hord
  have hσ : Odd (orderOf σ) := by rw [hσord]; decide
  have hm : 2 ≤ n / orderOf σ := by
    rw [hσord]
    exact two_le_div_three_U3Three hn1 h3n hn3
  have hdq : ((3 : ℕ), 2 ^ (n / orderOf σ)) ≠ (3, 2) := dq_ne_U3Three hm
  obtain ⟨-, -, hk⟩ := fixF_data hn1 hK σ hσ
  haveI : CharP (fixF σ) 2 := charP_fixF hn1 hK σ hσ
  have h3' : 3 ∣ 2 ^ (n / orderOf σ) + 1 := by
    rw [hσord]
    exact three_dvd_two_pow_div_add_one_U3Three h3 h3n
  have hS := simple_noncomm_proj hk le_rfl hdq
  have hKQ : Nat.card K = ((2 ^ (n / orderOf σ)) ^ 2) ^ 3 := by
    rw [hK, hσord]
    obtain ⟨t, rfl⟩ := h3n
    rw [Nat.mul_div_cancel_left t (by norm_num)]
    ring
  have hQ : (2 ^ (n / orderOf σ)) ^ 2 % 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, Nat.pow_mod]
    norm_num
  have hcube : ∀ c : fixF σ, ∃ e : K, e ^ 3 = (fixF σ).subtype c :=
    exists_cube_root_U3Three (fixF σ).subtype hk hKQ hQ
  refine ⟨LargeEvenProj (LargeEvenSUGroup (Fin 3) (fixF σ) (2 ^ (n / orderOf σ))), inferInstance,
    LargeEvenMatConjImage (LargeEvenProjMk _)
      (LargeEvenGUSet (Fin 3) (fixF σ) (2 ^ (n / orderOf σ))),
    regSetU3Three (fixF σ).subtype (2 ^ (n / orderOf σ)),
    (subfieldEquiv le_rfl hn1 hK hσ hdq hσf).symm, hS.1, hS.2,
    ggFixGeom_unitary le_rfl hn1 hK hσ hdq hσf, ?_, ?_, ggFixNoCompOn_u3Three hn1 hK hσ hdq hσf⟩
  · exact TypeA.ggTorusLift_zero (two_dvd_card_statedProj_statedSU (d := 3)
      (f := n / orderOf σ) (K := fixF σ) (by norm_num))
  · exact ggTorusNoLineTwoKX_u3Three (fixF σ).subtype hk hm h3' hcube _

end ResU3Three

theorem largeEvenLabelAll_rowKX_u3Three
    {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .twA ∧ lab.rank = 2 ∧ 3 ∣ 2 ^ lab.n + 1 ∧ 3 ∣ lab.n ∧ lab.n ≠ 3) :
    LargeEvenLabelAll lab fun R _ I _ => (∀ g : R, MulAut.conj g ∈ I) ∧ GGTorusLift 3 0 R ∧
      (IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
        GGTorusNoLineComp 3 0 R I ∧ GGCenterKp (fun k => k ∣ 3) R) := by
  obtain ⟨ht, hl, -, -, -⟩ := h
  have hinn := largeEvenLabelAll_inn_twA hlab ht
  have hcard := largeEvenLabelAll_lift_card_lt_unitaryThree_all Nat.prime_three (by norm_num)
    hlab ht hl
  have hrest : LargeEvenLabelAll lab fun R _ I _ =>
      GGTorusLift 3 0 R ∧ GGCenterKp (fun k => k ∣ 3) R := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht hl
    subst ht hl
    have hn : 2 ≤ n := hlab.2.2 rfl
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := (TableBU.unitaryFieldData_of_card hK (by omega)).charP
    exact ⟨K, inferInstance, inferInstance, hK, hQ',
      TypeA.ggTorusLift_zero
        (two_dvd_card_statedProj_statedSU (d := 3) (f := n) (K := K) (by norm_num)),
      ResU3Three.ggCenterKp_u3Three hK hn⟩
  refine (largeEvenLabelAll_and hinn (largeEvenLabelAll_and hcard hrest)).mono ?_
  rintro R _ I F ⟨hi, hc, hl0, hKp⟩
  refine ⟨hi, hl0, fun _ _ => ⟨?_, hKp⟩⟩
  intro L' _ _ ψ hψ hker hperf A hA hAI _ h27 _
  exact absurd h27 (not_le.mpr (hc L' ψ hψ hker hperf A hA hAI))

theorem largeEvenLabelAll_fixKX_u3Three
    {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .twA ∧ lab.rank = 2 ∧ 3 ∣ 2 ^ lab.n + 1 ∧ 3 ∣ lab.n ∧ lab.n ≠ 3) :
    LargeEvenLabelAll lab (GGRawFieldFixKX 3 (fun k => k ∣ 3)) := by
  obtain ⟨ht, hl, h3, h3n, hn3⟩ := h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hl h3 h3n hn3
  subst ht hl
  have hn : 2 ≤ n := hlab.2.2 rfl
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  exact ⟨K, inferInstance, inferInstance, hK, hQ', fun _ _ f hf hord =>
    ResU3Three.ggFixDataKX_u3Three hK hn h3 h3n hn3 hf hord⟩

end CFSG.StandardType

end
