module

public import CFSG.RankThree.PartTwo.Sec16.Item166Res6ProofE9U
public import CFSG.LieType.SeitzGeneration.OuterCirc
public import CFSG.LieType.SeitzGeneration.HeisTorusUDefs
public import CFSG.RankThree.PartTwo.Sec15.KSL3TwoProofDiag
import CFSG.LieType.SeitzGeneration.HeisTorusU83
import CFSG.LieType.SeitzGeneration.HeisTorusU84
import CFSG.LocalAnalysis.UniquenessCase.UC1K326SL3GenMatrix
import CFSG.LocalAnalysis.UniquenessCase.UCInspL3UNorm
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3.Invariant
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm
import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.Sec16.Proof166Res6 (permSU permGL coe_permGL)

namespace U3Gen

open CFSG.LieType.SeitzGeneration
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartTwo.Sec15.KSL3Two (IsMonomialWith)

theorem five_le_div_gcd_of_mod {p f : ℕ} (hq : p ^ f % 3 = 1) (hq7 : 7 < p ^ f) :
    5 ≤ (p ^ f + 1) / Nat.gcd 2 (p ^ f + 1) := by
  have hq10 : 10 ≤ p ^ f := by omega
  by_cases h2 : 2 ∣ p ^ f
  · have hodd : Odd (p ^ f + 1) := by
      obtain ⟨k, hk⟩ := h2
      exact ⟨k, by omega⟩
    have hgcd : Nat.gcd 2 (p ^ f + 1) = 1 := by
      have hle : Nat.gcd 2 (p ^ f + 1) ≤ 2 :=
        Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 2 (p ^ f + 1))
      have hpos : 0 < Nat.gcd 2 (p ^ f + 1) :=
        Nat.gcd_pos_of_pos_left _ (by norm_num)
      have hne : Nat.gcd 2 (p ^ f + 1) ≠ 2 := by
        obtain ⟨k, hk⟩ := h2
        intro hg
        obtain ⟨m, hm⟩ := hg ▸ Nat.gcd_dvd_right 2 (p ^ f + 1)
        omega
      omega
    rw [hgcd, Nat.div_one]
    omega
  · have hmod : p ^ f % 2 = 1 := by
      have h := Nat.mod_two_eq_zero_or_one (p ^ f)
      have h0 : p ^ f % 2 ≠ 0 := fun h0 => h2 ((Nat.dvd_iff_mod_eq_zero).mpr h0)
      omega
    have heven : 2 ∣ p ^ f + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    have hgcd : Nat.gcd 2 (p ^ f + 1) = 2 := by
      have hle : Nat.gcd 2 (p ^ f + 1) ≤ 2 :=
        Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 2 (p ^ f + 1))
      have hdvd : 2 ∣ Nat.gcd 2 (p ^ f + 1) := Nat.dvd_gcd dvd_rfl heven
      have hpos : 0 < Nat.gcd 2 (p ^ f + 1) :=
        Nat.gcd_pos_of_pos_left _ (by norm_num)
      omega
    rw [hgcd]
    omega

theorem exists_normOne_unit_ne_one {p f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData p f F) (hq : p ^ f % 3 = 1) :
    ∃ lam : Fˣ, h.norm (lam : F) = 1 ∧ lam ≠ 1 ∧ (lam : F) ^ 3 ≠ 1 := by
  have hfinite : Finite F := h.finite
  have hcard := h.card_ker_normUnits_and_surjective.1
  have hFintype : Fintype (Units.map h.normHom).ker := Fintype.ofFinite _
  have h2 : 1 < Fintype.card (Units.map h.normHom).ker := by
    rw [← Nat.card_eq_fintype_card, hcard]
    omega
  obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card h2 (1 : (Units.map h.normHom).ker)
  have hnorm : h.norm ((b : Fˣ) : F) = 1 := (h.mem_ker_normUnits).mp b.2
  have hq1 : (b : Fˣ) ^ (p ^ f + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, ← h.norm_eq_pow]
    exact hnorm
  have h3 : (b : Fˣ) ^ 3 ≠ 1 := by
    intro hb3
    have hb1 : (b : Fˣ) ^ 1 = 1 := by
      have := pow_gcd_eq_one.2 ⟨hb3, hq1⟩
      rwa [CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3.coprime_three hq] at this
    exact hb (by simpa using hb1)
  refine ⟨b, hnorm, ?_, ?_⟩
  · intro hb1
    exact hb (Subtype.ext hb1)
  · intro h3f
    exact h3 (Units.ext (by simpa using h3f))

def circOff {F : Type} [Field F] (lam : F) : F := ((lam ^ 2)⁻¹ - lam) / 3

def circElem {F : Type} [Field F] (lam : F) : Matrix (Fin 3) (Fin 3) F :=
  circMat 1 (lam + circOff lam) (circOff lam) (circOff lam)

theorem bar_eq_inv_of_norm_one {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F)
    {lam : F} (hlam : h.norm lam = 1) : h.bar lam = lam⁻¹ :=
  eq_inv_of_mul_eq_one_right hlam

theorem bar_circOff {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F)
    {lam : F} (hlam : h.norm lam = 1) :
    h.bar (circOff lam) = (lam ^ 2 - lam⁻¹) / 3 := by
  have hbar_lam : h.bar lam = lam⁻¹ := bar_eq_inv_of_norm_one h hlam
  unfold circOff
  rw [map_div₀, map_sub, map_inv₀, map_pow, hbar_lam]
  simp only [map_ofNat]
  rw [← inv_pow, inv_inv]

theorem circOff_ne_zero {F : Type} [Field F] (h3 : (3 : F) ≠ 0) {lam : F}
    (hlam0 : lam ≠ 0) (hlam3 : lam ^ 3 ≠ 1) : circOff lam ≠ 0 := by
  intro h0
  apply hlam3
  have hnum : (lam ^ 2)⁻¹ - lam = 0 := by
    exact (div_eq_zero_iff).mp h0 |>.resolve_right h3
  have hEq : (lam ^ 2)⁻¹ = lam := sub_eq_zero.mp hnum
  have hmul : (lam ^ 2)⁻¹ * lam ^ 2 = lam * lam ^ 2 := by rw [hEq]
  rw [inv_mul_cancel₀ (pow_ne_zero 2 hlam0)] at hmul
  calc lam ^ 3 = lam * lam ^ 2 := by ring
    _ = 1 := hmul.symm

theorem circElem_det {F : Type} [Field F] (h3 : (3 : F) ≠ 0) {lam : F}
    (hlam0 : lam ≠ 0) : (circElem lam).det = 1 := by
  rw [circElem, det_circMat]
  unfold circOff
  field_simp [h3, hlam0]
  ring

theorem circElem_unitary {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F)
    {lam : F} (hlam : h.norm lam = 1) (h3 : (3 : F) ≠ 0) :
    ((circElem lam).map h.bar)ᵀ * circElem lam = 1 := by
  have hbar_lam : h.bar lam = lam⁻¹ := bar_eq_inv_of_norm_one h hlam
  have hbar_mu := bar_circOff h hlam
  have hlam0 : lam ≠ 0 := by
    intro h0
    have h1 : (0 : F) = 1 := by
      have h2 := h0 ▸ hlam
      simp [UnitaryFieldData.norm] at h2
    exact zero_ne_one h1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [circElem, circMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.map_apply,
      Matrix.transpose_apply, hbar_lam, hbar_mu] <;>
    unfold circOff <;> field_simp [hlam0, h3] <;> ring

theorem circElem_comm_permSU {F : Type} [Field F] :
    ∀ lam : F, circElem lam * ((permGL : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((permGL : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * circElem lam := by
  intro lam
  have h := circMat_comm (1 : F) (lam + circOff lam) (circOff lam) (circOff lam)
  have hC : heisC (1 : F) = ((permGL : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [coe_permGL]
    rfl
  rw [hC] at h
  exact h

def cyclePerm3 : Fin 3 → Fin 3 := ![1, 2, 0]

theorem permSU_isMonomialWith {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F) :
    IsMonomialWith ((permSU h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) cyclePerm3 := by
  intro i j
  have hmat : ((permSU h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = !![0, 0, 1; 1, 0, 0;
      0, 1, 0] := coe_permGL
  rw [hmat]
  fin_cases i <;> fin_cases j <;> simp [cyclePerm3]

theorem cyclePerm3_cube : cyclePerm3 ∘ cyclePerm3 ∘ cyclePerm3 = id := by
  decide

theorem cyclePerm3_ne_id : cyclePerm3 ≠ id := by
  decide

noncomputable def normOneScalarGL {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F) :
    Subgroup (GL (Fin 3) F) :=
  (Units.map h.normHom).ker.map (GeneralLinearGroup.scalar (Fin 3))

theorem mem_normOneScalarGL {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F)
    {g : GL (Fin 3) F} :
    g ∈ normOneScalarGL h ↔ ∃ c : Fˣ, h.norm (c : F) = 1 ∧
      g = GeneralLinearGroup.scalar (Fin 3) c := by
  rw [normOneScalarGL, Subgroup.mem_map]
  constructor
  · rintro ⟨c, hc, hgc⟩
    exact ⟨c, (h.mem_ker_normUnits).mp hc, hgc.symm⟩
  · rintro ⟨c, hc, hgc⟩
    exact ⟨c, (h.mem_ker_normUnits).mpr hc, hgc.symm⟩

theorem normOneScalarGL_normal {p f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData p f F) : (normOneScalarGL h).Normal := by
  refine ⟨fun z hz g => ?_⟩
  obtain ⟨c, hc, hg⟩ := (mem_normOneScalarGL h).mp hz
  have hcomm : Commute g (GeneralLinearGroup.scalar (Fin 3) c) := commute_scalar c g
  rw [hg, hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
  exact (mem_normOneScalarGL h).mpr ⟨c, hc, rfl⟩


theorem exists_normOne_cube_of_diag_entries {p f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData p f F) (hq : p ^ f % 3 = 1) {t : Fin 3 → F}
    (hnorm : ∀ i, h.bar (t i) * t i = 1) :
    ∃ s : Fˣ, h.norm (s : F) = 1 ∧ (s : F) ^ 3 = t 0 * t 1 * t 2 := by
  have ht0 : ∀ i, t i ≠ 0 := by
    intro i h0
    have h := hnorm i
    rw [h0, map_zero, zero_mul] at h
    exact zero_ne_one h
  let c : Fin 3 → Fˣ := fun i => Units.mk0 (t i) (ht0 i)
  have hc_norm : ∀ i, h.norm ((c i : Fˣ) : F) = 1 := by
    intro i
    rw [UnitaryFieldData.norm]
    change t i * h.bar (t i) = 1
    rw [mul_comm]
    exact hnorm i
  let z : Fˣ := c 0 * c 1 * c 2
  have hz_norm : h.norm (z : F) = 1 := by
    have h0 := hc_norm 0
    have h1 := hc_norm 1
    have h2 := hc_norm 2
    simp only [z, Units.val_mul] at h0 h1 h2 ⊢
    rw [norm_mul_eq, norm_mul_eq, h0, h1, h2, one_mul]
    norm_num
  have hzroot : z ∈ rootsOfUnity (p ^ f + 1) F := by
    rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one,
      ← h.norm_eq_pow]
    exact hz_norm
  obtain ⟨s, hsroot, hs3⟩ :=
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3.exists_cube hq hzroot
  have hs3f : (s : F) ^ 3 = t 0 * t 1 * t 2 := by
    have h := congrArg Units.val hs3
    rw [Units.val_pow_eq_pow_val] at h
    rw [h]
    simp [z, c]
  have hsnorm : h.norm (s : F) = 1 := by
    rw [h.norm_eq_pow]
    simpa using congrArg Units.val ((mem_rootsOfUnity (p ^ f + 1) s).mp hsroot)
  exact ⟨s, hsnorm, hs3f⟩

theorem diag_mem_sup_normOneScalar {p f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData p f F) (hq : p ^ f % 3 = 1)
    {H : Subgroup (unitarySU p f F 3)}
    (hdiag : ∀ x : unitarySU p f F 3,
      ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag → x ∈ H)
    {g : GL (Fin 3) F} (hgU : g ∈ primeFormUnitary h (1 : Matrix (Fin 3) (Fin 3) F))
    {t : Fin 3 → F} (hgt : (g : Matrix (Fin 3) (Fin 3) F) = diagonal t) :
    g ∈ H.map (unitarySU p f F 3).subtype ⊔ normOneScalarGL h := by
  have hbar : ((g : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * g = 1 := by
    have h1 := (mem_primeFormUnitary (h := h) (C := (1 : Matrix (Fin 3) (Fin 3) F))
      (g := g)).mp hgU
    simpa using h1
  rw [hgt, Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one] at hbar
  have hnorm_i : ∀ i, h.bar (t i) * t i = 1 := by
    intro i
    have := congrFun (congrFun hbar i) i
    simpa using this
  obtain ⟨s, hsnorm, hs3f⟩ := exists_normOne_cube_of_diag_entries h hq hnorm_i
  have hs0 : (s : F) ≠ 0 := by
    have := s.ne_zero
    exact_mod_cast this
  let u : Matrix (Fin 3) (Fin 3) F := diagonal (fun i => (s : F)⁻¹ * t i)
  have hu_det : u.det = 1 := by
    rw [show u = diagonal (fun i => (s : F)⁻¹ * t i) from rfl, Matrix.det_diagonal,
      Fin.prod_univ_three]
    calc ((s : F)⁻¹ * t 0) * ((s : F)⁻¹ * t 1) * ((s : F)⁻¹ * t 2)
        = ((s : F)⁻¹) ^ 3 * (t 0 * t 1 * t 2) := by ring
      _ = ((s : F)⁻¹) ^ 3 * (s : F) ^ 3 := by rw [hs3f]
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hs0, one_pow]
  have hu_bar : ∀ i, h.bar ((s : F)⁻¹ * t i) * ((s : F)⁻¹ * t i) = 1 := by
    intro i
    have hti_norm : h.norm (t i) = 1 := by
      rw [UnitaryFieldData.norm, mul_comm]
      exact hnorm_i i
    have h1 : h.norm ((s : F)⁻¹ * t i) = 1 := by
      rw [norm_mul_eq, norm_inv_eq, hsnorm, hti_norm, inv_one, one_mul]
    rw [UnitaryFieldData.norm] at h1
    simpa [mul_comm] using h1
  let uGL : GL (Fin 3) F := GeneralLinearGroup.mkOfDetNeZero u (by rw [hu_det]; exact one_ne_zero)
  have huGL_coe : (uGL : Matrix (Fin 3) (Fin 3) F) = u := by
    simp [uGL]
  have hu_mem : uGL ∈ unitarySU p f F 3 := by
    rw [mem_unitarySU_iff h]
    refine ⟨?_, ?_⟩
    · rw [huGL_coe]
      exact hu_det
    · rw [huGL_coe, Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact hu_bar i
  let uSU : unitarySU p f F 3 := ⟨uGL, hu_mem⟩
  have huSU_diag : ((uSU : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag := by
    change u.IsDiag
    exact Matrix.isDiag_diagonal _
  have huH : uSU ∈ H := hdiag uSU huSU_diag
  have hdecomp : GeneralLinearGroup.scalar (Fin 3) s * uGL = g := by
    apply Units.ext
    change (GeneralLinearGroup.scalar (Fin 3) s : Matrix (Fin 3) (Fin 3) F) *
      (uGL : Matrix (Fin 3) (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F)
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, huGL_coe, hgt]
    simp only [u]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_inv_cancel_left₀ hs0 (t i)
  have hNormal : (normOneScalarGL h).Normal := normOneScalarGL_normal h
  rw [← hdecomp]
  exact (H.map (unitarySU p f F 3).subtype ⊔ normOneScalarGL h).mul_mem
    (Subgroup.mem_sup_right ((mem_normOneScalarGL h).mpr ⟨s, hsnorm, rfl⟩))
    (Subgroup.mem_sup_left (Subgroup.mem_map.mpr ⟨uSU, huH, rfl⟩))

theorem mem_of_mem_sup_normOneScalar {p f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData p f F) (hq : p ^ f % 3 = 1)
    {H : Subgroup (unitarySU p f F 3)} {g : unitarySU p f F 3}
    (hg : (g : GL (Fin 3) F) ∈
      H.map (unitarySU p f F 3).subtype ⊔ normOneScalarGL h) : g ∈ H := by
  have hNormal : (normOneScalarGL h).Normal := normOneScalarGL_normal h
  rw [Subgroup.mem_sup_of_normal_right] at hg
  obtain ⟨y, hy, z, hz, hyz⟩ := hg
  obtain ⟨ySU, hyH, hyeq⟩ := Subgroup.mem_map.mp hy
  obtain ⟨cc, hcc, hzc⟩ := (mem_normOneScalarGL h).mp hz
  have hySU : y ∈ unitarySU p f F 3 := by
    rw [← hyeq]
    exact ySU.2
  have hzSU : z ∈ unitarySU p f F 3 := by
    have hzEq : z = y⁻¹ * (g : GL (Fin 3) F) := by
      rw [← hyz]
      group
    rw [hzEq]
    exact Subgroup.mul_mem (H := unitarySU p f F 3) ((unitarySU p f F 3).inv_mem hySU) g.2
  have hz_det : ((z : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 :=
    ((mem_unitarySU_iff h).mp hzSU).1
  have h1 : ((GeneralLinearGroup.scalar (Fin 3) cc : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [← hzc]
    exact hz_det
  have hcc3 : cc ^ 3 = 1 := by
    have h2 : (GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) cc) : F) = 1 := by
      rw [GeneralLinearGroup.val_det_apply]
      exact h1
    rw [GeneralLinearGroup.det_scalar] at h2
    apply Units.ext
    simpa using h2
  have hccq : cc ^ (p ^ f + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, ← h.norm_eq_pow]
    exact hcc
  have hcc1 : cc = 1 := by
    have := pow_gcd_eq_one.2 ⟨hcc3, hccq⟩
    rw [CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3.coprime_three hq] at this
    simpa using this
  have hz1 : z = 1 := by
    rw [hzc, hcc1, map_one]
  have hgy : (g : GL (Fin 3) F) = y := by
    rw [← hyz, hz1, mul_one]
  have hgmap : (g : GL (Fin 3) F) ∈ H.map (unitarySU p f F 3).subtype := by
    rw [hgy]
    exact hy
  obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp hgmap
  have hxg' : x = g := Subtype.ext hxg
  rwa [hxg'] at hx

theorem exists_circElem_mem_unitarySU {p f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData p f F) {lam : F} (hlam : h.norm lam = 1) (h3 : (3 : F) ≠ 0) :
    ∃ c : unitarySU p f F 3,
      ((c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = circElem lam := by
  have hlam0 : lam ≠ 0 := by
    intro h0
    have h1 : (0 : F) = 1 := by
      have h2 := h0 ▸ hlam
      simp [UnitaryFieldData.norm] at h2
    exact zero_ne_one h1
  have hdet : (circElem lam).det = 1 := circElem_det h3 hlam0
  let cGL : GL (Fin 3) F :=
    GeneralLinearGroup.mkOfDetNeZero (circElem lam) (by rw [hdet]; exact one_ne_zero)
  have hcoe : (cGL : Matrix (Fin 3) (Fin 3) F) = circElem lam := by simp [cGL]
  have hmem : cGL ∈ unitarySU p f F 3 := by
    rw [mem_unitarySU_iff h]
    refine ⟨?_, ?_⟩
    · rw [hcoe]
      exact hdet
    · rw [hcoe]
      exact circElem_unitary h hlam h3
  exact ⟨⟨cGL, hmem⟩, hcoe⟩

theorem circElem_not_monomial {F : Type} [Field F] {lam : F} (hmu : circOff lam ≠ 0) :
    ¬ IsMonomialMat (circElem lam) := by
  intro hmono
  have h10 : (circElem lam) 1 0 ≠ 0 := by
    simpa [circElem, circMat] using hmu
  have h20 : (circElem lam) 2 0 ≠ 0 := by
    simpa [circElem, circMat] using hmu
  have h12 : (1 : Fin 3) = 2 := hmono 0 1 2 h10 h20
  exact absurd h12 (by decide)

theorem exists_nonmonomial_mem_sup {p f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData p f F) (hq : p ^ f % 3 = 1)
    {H : Subgroup (unitarySU p f F 3)}
    (hcen : centralizer ({permSU h} : Set (unitarySU p f F 3)) ≤ H) :
    ∃ x ∈ H.map (unitarySU p f F 3).subtype ⊔ normOneScalarGL h,
      ¬ IsMonomialMat (x : Matrix (Fin 3) (Fin 3) F) := by
  have hFinite : Finite F := h.finite
  have hFact : Fact p.Prime := ⟨h.prime⟩
  have hChar : CharP F p := h.charP
  have h3 : (3 : F) ≠ 0 :=
    CFSG.LocalAnalysis.UniquenessCase.UCK.Insp.three_ne_zero_of_pow_mod_one h.one_le hq
  obtain ⟨lam, hlam, -, hlam3⟩ := exists_normOne_unit_ne_one h hq
  have hlam0 : (lam : F) ≠ 0 := lam.ne_zero
  have hmu : circOff (lam : F) ≠ 0 := circOff_ne_zero h3 hlam0 hlam3
  obtain ⟨cSU, hc_coe⟩ := exists_circElem_mem_unitarySU h hlam h3
  have hc_cent : cSU ∈ centralizer ({permSU h} : Set (unitarySU p f F 3)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    apply Units.ext
    change ((cSU : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((permSU h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((permSU h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((cSU : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
    rw [hc_coe]
    have hp : ((permSU h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((permGL : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := rfl
    rw [hp]
    exact circElem_comm_permSU (lam : F)
  have hcH : cSU ∈ H := hcen hc_cent
  refine ⟨(cSU : GL (Fin 3) F), ?_, ?_⟩
  · exact Subgroup.mem_sup_left (Subgroup.mem_map.mpr ⟨cSU, hcH, rfl⟩)
  · rw [hc_coe]
    exact circElem_not_monomial hmu

theorem exists_plane_blocks_of_diag {p f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData p f F) (hq : p ^ f % 3 = 1) (hq7 : 7 < p ^ f)
    {H : Subgroup (unitarySU p f F 3)}
    (hdiag : ∀ x : unitarySU p f F 3,
      ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag → x ∈ H)
    (hcen : centralizer ({permSU h} : Set (unitarySU p f F 3)) ≤ H) :
    ∃ a b : Fin 3, a ≠ b ∧ ∀ g : unitarySU p f F 3,
      IsCoordBlockOn a b ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) → g ∈ H := by
  have hq4 : 4 ≤ p ^ f := by omega
  have he : 5 ≤ (p ^ f + 1) / Nat.gcd 2 (p ^ f + 1) := five_le_div_gcd_of_mod hq hq7
  let Z : Subgroup (GL (Fin 3) F) := normOneScalarGL h
  let X : Subgroup (GL (Fin 3) F) := H.map (unitarySU p f F 3).subtype ⊔ Z
  have hXU : X ≤ primeFormUnitary h (1 : Matrix (Fin 3) (Fin 3) F) := by
    refine sup_le ?_ ?_
    · rintro x ⟨y, hy, rfl⟩
      rw [mem_primeFormUnitary]
      have hy' := ((mem_unitarySU_iff h).mp y.2).2
      simpa using hy'
    · rintro z hz
      obtain ⟨c, hc, hzc⟩ := (mem_normOneScalarGL h).mp hz
      rw [hzc]
      have := scalar_mem_primeFormUnitary_one h (n := 3) hc
      simpa using this
  have hD : ∀ g ∈ primeFormUnitary h (1 : Matrix (Fin 3) (Fin 3) F),
      (∃ t, (g : Matrix (Fin 3) (Fin 3) F) = diagonal t) → g ∈ X := by
    intro g hgU hgt
    obtain ⟨t, ht⟩ := hgt
    exact diag_mem_sup_normOneScalar h hq hdiag hgU ht
  have hx : ∃ x ∈ X, ¬ IsMonomialMat (x : Matrix (Fin 3) (Fin 3) F) := by
    obtain ⟨x, hxX, hxm⟩ := exists_nonmonomial_mem_sup h hq hcen
    exact ⟨x, by simpa [X, Z] using hxX, hxm⟩
  obtain ⟨a, b, hab, hplaneX⟩ :=
    CFSG.LieType.SeitzGeneration.exists_block_su_of_diag h hq4 he (n := 3)
      (by norm_num) X hXU hD hx
  refine ⟨a, b, hab, ?_⟩
  intro g hg
  exact mem_of_mem_sup_normOneScalar h hq (by simpa [X, Z] using hplaneX (g : GL (Fin 3) F) g.2 hg)

end U3Gen

open U3Gen
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LieType.SeitzGeneration

theorem su3_eq_top_of_diag_mem_of_centralizer_le {p f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData p f F) (hq : p ^ f % 3 = 1) (hq7 : 7 < p ^ f)
    {H : Subgroup (unitarySU p f F 3)}
    (hdiag : ∀ x : unitarySU p f F 3,
      ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag → x ∈ H)
    (hcen : centralizer ({permSU h} : Set (unitarySU p f F 3)) ≤ H) : H = ⊤ := by
  obtain ⟨a, b, hab, hplaneH⟩ := exists_plane_blocks_of_diag h hq hq7 hdiag hcen
  have htH : permSU h ∈ H :=
    hcen (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hblocks :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.SL3G.planes_of_cycle
      (unitarySU p f F 3).subtype H htH (permSU_isMonomialWith h) cyclePerm3_cube
      cyclePerm3_ne_id hab hplaneH
  refine eq_top_iff.mpr fun x hx => ?_
  have hle : unitarySU p f F 3 ≤ H.map (unitarySU p f F 3).subtype := by
    refine CFSG.LieType.SeitzGeneration.unitarySU_le_of_blocks h (by omega) (n := 3)
      (by norm_num) (H.map (unitarySU p f F 3).subtype) ?_
    intro c d hcd g hgSU hblock
    exact Subgroup.mem_map.mpr ⟨⟨g, hgSU⟩, hblocks c d hcd ⟨g, hgSU⟩ hblock, rfl⟩
  have hx' : (x : GL (Fin 3) F) ∈ H.map (unitarySU p f F 3).subtype := hle x.2
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
  have hxy : y = x := Subtype.ext hyx
  rwa [hxy] at hy

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen
