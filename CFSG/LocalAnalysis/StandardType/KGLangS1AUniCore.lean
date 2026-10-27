module

public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagUnitary
import CFSG.LocalAnalysis.StandardType.KGLangTorAFields
import CFSG.LocalAnalysis.StandardType.GGL45TGSU

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial

private theorem kgLangS1AUniCoreAux_prod_zpow_eq_zpow_sum {ι G : Type*} [CommGroup G]
    (s : Finset ι) (y : G) (e : ι → ℤ) :
    s.prod (fun i => y ^ e i) = y ^ s.sum e := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ← zpow_add]

private theorem kgLangS1AUniCoreAux_zpow_pow_eq_one {G : Type*} [Group G] (u : G) {p : ℕ}
    (hp : u ^ p = 1) (n : ℤ) : (u ^ n) ^ p = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hp, one_zpow]

private theorem kgLangS1AUniCoreAux_dvd_add_one {p x : ℕ} (hp : p.Prime)
    (h : p ∣ x ^ p + 1) : p ∣ x + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : ((x ^ p + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  rw [Nat.cast_add, Nat.cast_pow, ZMod.pow_card, Nat.cast_one] at h1
  rw [← ZMod.natCast_eq_zero_iff]
  simpa using h1

private theorem kgLangS1AUniCoreAux_blockScalar_commute {d : ℕ} {F : Type} [Field F]
    {a : Fin d → ℤ} {w : Fin d → F} {D E : GL (Fin d) F}
    (hD : ∀ i j, a i ≠ a j → (D : Matrix (Fin d) (Fin d) F) i j = 0)
    (hE : (E : Matrix (Fin d) (Fin d) F) = Matrix.diagonal w)
    (hw : ∀ i j, a i = a j → w i = w j) :
    D * E = E * D := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hE]
  ext i j
  have h1 : ((D : Matrix (Fin d) (Fin d) F) * Matrix.diagonal w) i j =
      (D : Matrix (Fin d) (Fin d) F) i j * w j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [Matrix.diagonal_apply_eq]
    · intro k _ hk; rw [Matrix.diagonal_apply_ne _ hk, mul_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  have h2 : (Matrix.diagonal w * (D : Matrix (Fin d) (Fin d) F)) i j =
      w i * (D : Matrix (Fin d) (Fin d) F) i j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [Matrix.diagonal_apply_eq]
    · intro k _ hk; rw [Matrix.diagonal_apply_ne _ (Ne.symm hk), zero_mul]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [h1, h2]
  by_cases hij : a i = a j
  · rw [hw i j hij, mul_comm]
  · rw [hD i j hij, zero_mul, mul_zero]

private theorem kgLangS1AUniCoreAux_map_diagHom {d : ℕ} {F : Type} [Field F]
    (σ : F →+* F) (w : Fin d → Fˣ) :
    Matrix.GeneralLinearGroup.map σ (CFSG.SectionRank.OddCover.diagHom d w) =
      CFSG.SectionRank.OddCover.diagHom d (fun i => Units.map σ (w i)) := by
  apply Units.ext
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, CFSG.SectionRank.OddCover.coe_diagHom,
    CFSG.SectionRank.OddCover.coe_diagHom]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    rfl
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij, map_zero]

private theorem kgLangS1AUniCoreAux_map_diagHom_mul {d : ℕ} {F : Type} [Field F]
    (σ : F →+* F) (w v : Fin d → Fˣ)
    (hrel : ∀ i, Units.map σ (w i) = v i * w i) :
    Matrix.GeneralLinearGroup.map σ (CFSG.SectionRank.OddCover.diagHom d w) =
      CFSG.SectionRank.OddCover.diagHom d w * CFSG.SectionRank.OddCover.diagHom d v := by
  apply Units.ext
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, Units.val_mul]
  simp only [CFSG.SectionRank.OddCover.coe_diagHom]
  rw [Matrix.diagonal_mul_diagonal]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, mul_comm]
    simpa using congrArg Units.val (hrel i)
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij, map_zero]

theorem kgLangS1A_uni_core {d n p : ℕ} {F : Type} [Field F] [Finite F]
    (h : UnitaryFieldData 2 n F) (hp : p.Prime) (hp2 : p ≠ 2) {σ : F ≃+* F}
    (hσ : orderOf σ = p) (hsplit : p ∣ 2 ^ n + 1) {U : GL (Fin d) F}
    (hUσ : Matrix.GeneralLinearGroup.map (σ : F →+* F) U = U)
    (hU : U ∈ TableB.unitGroup (ι := Fin d) h.bar) {a : Fin d → ℤ} (hsum : ∑ i, a i = 0)
    (hne : ∃ i j, ¬ (p : ℤ) ∣ a i - a j) :
    ∃ e s : GL (Fin d) F, e ∈ LargeEvenSUGroup (Fin d) F (2 ^ n) ∧
      s ∈ LargeEvenSUGroup (Fin d) F (2 ^ n) ∧
      Matrix.GeneralLinearGroup.map (σ : F →+* F) e = e ∧ e ^ p = 1 ∧
      e ∉ LargeEvenScalars (Fin d) F ∧
      Matrix.GeneralLinearGroup.map (σ : F →+* F) s = s * e ∧
      ∀ B : GL (Fin d) F, (∀ i j, a i ≠ a j →
          ((U⁻¹ * B * U : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i j = 0) →
        B * e = e * B ∧ B * s = s * B := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hn : 1 ≤ n := h.one_le
  haveI : CharP F 2 := h.charP
  haveI : Fintype F := Fintype.ofFinite F
  have hF : Nat.card F = (2 ^ n) ^ 2 := by
    rw [h.card, ← pow_mul]
    congr 1
    omega
  obtain ⟨hpn, hcard0⟩ := kgLangTorA_card_fixed_unitary hn hp hp2 hF hσ
  set q₀ : ℕ := 2 ^ (n / p) with hq₀
  have hnpad : 1 ≤ n / p := by
    obtain ⟨k, hk⟩ := hpn
    have hk1 : 1 ≤ k := by
      by_contra hk0
      have hk0' : k = 0 := by omega
      rw [hk0'] at hk
      omega
    rw [hk, Nat.mul_div_right k hp.pos]
    exact hk1
  have h2np : 2 ^ n = q₀ ^ p := by
    obtain ⟨k, hk⟩ := hpn
    have hk' : n / p = k := by rw [hk, Nat.mul_div_right k hp.pos]
    rw [hk, hq₀, hk', ← pow_mul, mul_comm]
  have hpq₀ : p ∣ q₀ + 1 := by
    have h' : p ∣ q₀ ^ p + 1 := by rwa [← h2np]
    exact kgLangS1AUniCoreAux_dvd_add_one hp h'
  have hcard0' : Nat.card
      (CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ) = q₀ ^ 2 := by
    rw [hcard0, hq₀]
  let h₀ : UnitaryFieldData 2 (n / p)
      (CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ) :=
    unitaryFieldData_of_card hnpad hcard0'
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot h₀ hp hpq₀
  let ω₀ : (CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ)ˣ :=
    Units.mk0 ζ (hζ.ne_zero hp.ne_zero)
  have hω₀p : ω₀ ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact hζ.pow_eq_one
  have hω₀1 : ω₀ ≠ 1 := by
    intro hh
    exact hζ.ne_one hp.one_lt (Units.ext_iff.mp hh)
  let ωF : Fˣ := Units.map (CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ).subtype ω₀
  have hωFp : ωF ^ p = 1 := by
    rw [← map_pow, hω₀p, map_one]
  have hωF1 : ωF ≠ 1 := by
    intro hh
    exact hω₀1 (Units.map_injective
      (CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ).subtype_injective hh)
  have hωFpF : (ωF : F) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hωFp, Units.val_one]
  have hωFq : (ωF : F) ^ (2 ^ n + 1) = 1 := by
    obtain ⟨k, hk⟩ := hsplit
    rw [hk, pow_mul, hωFpF, one_pow]
  have hωFσ : σ (ωF : F) = (ωF : F) := by
    have hfix := RingHom.mem_eqLocusField.mp
      (ω₀ : CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ).2
    simpa [ωF] using hfix
  have hωForder : orderOf ωF = p := orderOf_eq_prime hωFp hωF1
  obtain ⟨c, hcq, hcσ⟩ :=
    kgLangTorA_hilbert90_unitary hn hF hp hσ hωFpF hωFq
  have hc0 : c ≠ 0 := by
    intro hc0'
    rw [hc0'] at hcq
    rw [zero_pow (by omega : 2 ^ n + 1 ≠ 0)] at hcq
    exact zero_ne_one hcq
  let cF : Fˣ := Units.mk0 c hc0
  have hcFq : (cF : F) ^ (2 ^ n + 1) = 1 := hcq
  have hcFσ : σ (cF : F) = (ωF : F) * (cF : F) := hcσ
  have hcFqU : cF ^ (2 ^ n + 1) = 1 := Units.ext hcFq
  have hωFqU : ωF ^ (2 ^ n + 1) = 1 := Units.ext hωFq
  let we : Fin d → Fˣ := fun i => ωF ^ (a i)
  let ws : Fin d → Fˣ := fun i => cF ^ (a i)
  have hwe : ∏ i, we i = 1 := by
    change Finset.univ.prod (fun i => ωF ^ (a i)) = 1
    rw [kgLangS1AUniCoreAux_prod_zpow_eq_zpow_sum Finset.univ ωF a, hsum, zpow_zero]
  have hws : ∏ i, ws i = 1 := by
    change Finset.univ.prod (fun i => cF ^ (a i)) = 1
    rw [kgLangS1AUniCoreAux_prod_zpow_eq_zpow_sum Finset.univ cF a, hsum, zpow_zero]
  have hwe_pow : ∀ i, we i ^ p = 1 :=
    fun i => kgLangS1AUniCoreAux_zpow_pow_eq_one ωF hωFp (a i)
  have hwe_norm : ∀ i, (we i : F) ^ (2 ^ n + 1) = 1 := by
    intro i
    have h1 : we i ^ (2 ^ n + 1) = 1 :=
      kgLangS1AUniCoreAux_zpow_pow_eq_one ωF hωFqU (a i)
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  have hws_norm : ∀ i, (ws i : F) ^ (2 ^ n + 1) = 1 := by
    intro i
    have h1 : ws i ^ (2 ^ n + 1) = 1 :=
      kgLangS1AUniCoreAux_zpow_pow_eq_one cF hcFqU (a i)
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  have hwe_fixed : ∀ i, σ (we i : F) = (we i : F) := by
    intro i
    have h1 : Units.map (σ : F →* F) (we i) = we i := by
      change Units.map (σ : F →* F) (ωF ^ (a i)) = ωF ^ (a i)
      rw [map_zpow, show Units.map (σ : F →* F) ωF = ωF from Units.ext hωFσ]
    simpa using congrArg Units.val h1
  have hrel : ∀ i, Units.map (σ : F →* F) (ws i) = we i * ws i := by
    intro i
    change Units.map (σ : F →* F) (cF ^ (a i)) = ωF ^ (a i) * cF ^ (a i)
    rw [map_zpow, show Units.map (σ : F →* F) cF = ωF * cF from Units.ext hcFσ, mul_zpow]
  let Dwe : GL (Fin d) F := CFSG.SectionRank.OddCover.diagHom d we
  let Dws : GL (Fin d) F := CFSG.SectionRank.OddCover.diagHom d ws
  let e : GL (Fin d) F := U * Dwe * U⁻¹
  let s : GL (Fin d) F := U * Dws * U⁻¹
  have hDwe_fixed : Matrix.GeneralLinearGroup.map (σ : F →+* F) Dwe = Dwe := by
    show Matrix.GeneralLinearGroup.map (σ : F →+* F)
        (CFSG.SectionRank.OddCover.diagHom d we) = CFSG.SectionRank.OddCover.diagHom d we
    rw [kgLangS1AUniCoreAux_map_diagHom (σ : F →+* F) we]
    congr 1
    funext i
    exact Units.ext (hwe_fixed i)
  have hσDws : Matrix.GeneralLinearGroup.map (σ : F →+* F) Dws = Dws * Dwe := by
    show Matrix.GeneralLinearGroup.map (σ : F →+* F)
        (CFSG.SectionRank.OddCover.diagHom d ws) =
      CFSG.SectionRank.OddCover.diagHom d ws * CFSG.SectionRank.OddCover.diagHom d we
    exact kgLangS1AUniCoreAux_map_diagHom_mul (σ : F →+* F) ws we hrel
  have hDwe_pow : Dwe ^ p = 1 := by
    show (CFSG.SectionRank.OddCover.diagHom d we) ^ p = 1
    rw [← map_pow (CFSG.SectionRank.OddCover.diagHom d) we p]
    rw [show (we ^ p) = 1 from funext (fun i => hwe_pow i), map_one]
  have hUmat : ((U : Matrix (Fin d) (Fin d) F).map (h.bar : F →+* F)).transpose *
      (U : Matrix (Fin d) (Fin d) F) = 1 := TableB.mem_unitGroup.mp hU
  have hUcu : U ∈ GGL45TG.SU.CU h d := ⟨1, by rw [hUmat, one_smul]⟩
  have hDwe_su : Dwe ∈ LargeEvenSUGroup (Fin d) F (2 ^ n) := by
    show CFSG.SectionRank.OddCover.diagHom d we ∈ LargeEvenSUGroup (Fin d) F (2 ^ n)
    rw [GGL45TG.SU.mem_su_iff h]
    refine ⟨?_, ?_⟩
    · rw [CFSG.SectionRank.OddCover.coe_diagHom,
        Matrix.diagonal_map (f := ⇑h.bar) (map_zero h.bar),
        Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      rw [show h.bar (we i) = (we i : F) ^ 2 ^ n from h.bar_apply (we i),
        ← pow_succ, hwe_norm i]
    · rw [CFSG.SectionRank.OddCover.det_diagHom, ← Units.coe_prod, hwe, Units.val_one]
  have hDws_su : Dws ∈ LargeEvenSUGroup (Fin d) F (2 ^ n) := by
    show CFSG.SectionRank.OddCover.diagHom d ws ∈ LargeEvenSUGroup (Fin d) F (2 ^ n)
    rw [GGL45TG.SU.mem_su_iff h]
    refine ⟨?_, ?_⟩
    · rw [CFSG.SectionRank.OddCover.coe_diagHom,
        Matrix.diagonal_map (f := ⇑h.bar) (map_zero h.bar),
        Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      rw [show h.bar (ws i) = (ws i : F) ^ 2 ^ n from h.bar_apply (ws i),
        ← pow_succ, hws_norm i]
    · rw [CFSG.SectionRank.OddCover.det_diagHom, ← Units.coe_prod, hws, Units.val_one]
  have he_su : e ∈ LargeEvenSUGroup (Fin d) F (2 ^ n) :=
    GGL45TG.SU.conj_mem_su h hUcu hDwe_su
  have hs_su : s ∈ LargeEvenSUGroup (Fin d) F (2 ^ n) :=
    GGL45TG.SU.conj_mem_su h hUcu hDws_su
  have he_fixed : Matrix.GeneralLinearGroup.map (σ : F →+* F) e = e := by
    show Matrix.GeneralLinearGroup.map (σ : F →+* F) (U * Dwe * U⁻¹) = U * Dwe * U⁻¹
    rw [map_mul, map_mul, map_inv, hUσ, hDwe_fixed]
  have hep_e : e ^ p = 1 := by
    show (U * Dwe * U⁻¹) ^ p = 1
    rw [conj_pow, hDwe_pow, mul_one, mul_inv_cancel]
  have hDwe_notscalar : Dwe ∉ LargeEvenScalars (Fin d) F := by
    show CFSG.SectionRank.OddCover.diagHom d we ∉ LargeEvenScalars (Fin d) F
    intro hsc
    rw [largeEvenScalars_def] at hsc
    obtain ⟨μ, hμ⟩ := hsc
    obtain ⟨i, j, hij⟩ := hne
    have hμ' : (CFSG.SectionRank.OddCover.diagHom d we :
        Matrix (Fin d) (Fin d) F) = Matrix.scalar (Fin d) (μ : F) := by
      rw [← hμ, Matrix.GeneralLinearGroup.coe_scalar]
    have hdiag_i : (CFSG.SectionRank.OddCover.diagHom d we :
        Matrix (Fin d) (Fin d) F) i i = (we i : F) := by
      rw [CFSG.SectionRank.OddCover.coe_diagHom, Matrix.diagonal_apply_eq]
    have hdiag_j : (CFSG.SectionRank.OddCover.diagHom d we :
        Matrix (Fin d) (Fin d) F) j j = (we j : F) := by
      rw [CFSG.SectionRank.OddCover.coe_diagHom, Matrix.diagonal_apply_eq]
    have hsc_i : (CFSG.SectionRank.OddCover.diagHom d we :
        Matrix (Fin d) (Fin d) F) i i = (μ : F) := by
      rw [hμ']; simp [Matrix.scalar_apply]
    have hsc_j : (CFSG.SectionRank.OddCover.diagHom d we :
        Matrix (Fin d) (Fin d) F) j j = (μ : F) := by
      rw [hμ']; simp [Matrix.scalar_apply]
    have hweij : (we i : F) = (we j : F) :=
      hdiag_i.symm.trans (hsc_i.trans (hsc_j.symm.trans hdiag_j))
    have hdiff : we i ≠ we j := by
      intro hh
      have h3 : ωF ^ (a i) = ωF ^ (a j) := by simpa [we] using hh
      have hmod : a i ≡ a j [ZMOD (p : ℤ)] := by
        have h4 := zpow_eq_zpow_iff_modEq.mp h3
        rwa [hωForder] at h4
      exact hij (by
        have h6 := Int.modEq_iff_dvd.mp hmod
        have h7 := dvd_neg.mpr h6
        simpa only [neg_sub] using h7)
    exact hdiff (Units.ext hweij)
  have he_notscalar : e ∉ LargeEvenScalars (Fin d) F := by
    intro hsc
    apply hDwe_notscalar
    have hcen : e ∈ Subgroup.center (GL (Fin d) F) := TableB.scalars_le_center hsc
    have h1 : U⁻¹ * e * U = e := by
      rw [Subgroup.mem_center_iff.mp hcen U⁻¹]
      group
    have hDwe_eq : Dwe = e := by
      rw [show Dwe = U⁻¹ * (U * Dwe * U⁻¹) * U from by group,
        show U * Dwe * U⁻¹ = e from rfl, h1]
    rwa [hDwe_eq]
  have hsσ' : Matrix.GeneralLinearGroup.map (σ : F →+* F) s = s * e := by
    show Matrix.GeneralLinearGroup.map (σ : F →+* F) (U * Dws * U⁻¹) =
      (U * Dws * U⁻¹) * (U * Dwe * U⁻¹)
    rw [map_mul, map_mul, map_inv, hUσ, hσDws]
    group
  refine ⟨e, s, he_su, hs_su, he_fixed, hep_e, he_notscalar, hsσ', ?_⟩
  intro B hB
  have hB_eq : B = U * (U⁻¹ * B * U) * U⁻¹ := by group
  have hcommDe : (U⁻¹ * B * U) * Dwe = Dwe * (U⁻¹ * B * U) :=
    kgLangS1AUniCoreAux_blockScalar_commute hB
      (CFSG.SectionRank.OddCover.coe_diagHom we)
      (fun i j hij => by dsimp only [we]; rw [hij])
  have hcommDs : (U⁻¹ * B * U) * Dws = Dws * (U⁻¹ * B * U) :=
    kgLangS1AUniCoreAux_blockScalar_commute hB
      (CFSG.SectionRank.OddCover.coe_diagHom ws)
      (fun i j hij => by dsimp only [ws]; rw [hij])
  constructor
  · rw [hB_eq]
    show (U * (U⁻¹ * B * U) * U⁻¹) * (U * Dwe * U⁻¹) =
      (U * Dwe * U⁻¹) * (U * (U⁻¹ * B * U) * U⁻¹)
    rw [show (U * (U⁻¹ * B * U) * U⁻¹) * (U * Dwe * U⁻¹) =
          U * ((U⁻¹ * B * U) * Dwe) * U⁻¹ from by group,
      show (U * Dwe * U⁻¹) * (U * (U⁻¹ * B * U) * U⁻¹) =
          U * (Dwe * (U⁻¹ * B * U)) * U⁻¹ from by group,
      hcommDe]
  · rw [hB_eq]
    show (U * (U⁻¹ * B * U) * U⁻¹) * (U * Dws * U⁻¹) =
      (U * Dws * U⁻¹) * (U * (U⁻¹ * B * U) * U⁻¹)
    rw [show (U * (U⁻¹ * B * U) * U⁻¹) * (U * Dws * U⁻¹) =
          U * ((U⁻¹ * B * U) * Dws) * U⁻¹ from by group,
      show (U * Dws * U⁻¹) * (U * (U⁻¹ * B * U) * U⁻¹) =
          U * (Dws * (U⁻¹ * B * U)) * U⁻¹ from by group,
      hcommDs]

end CFSG.StandardType
