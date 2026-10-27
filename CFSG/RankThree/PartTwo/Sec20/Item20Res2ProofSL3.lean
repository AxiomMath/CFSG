module

public import CFSG.CGT.T75N.L29Rad
public import CFSG.CGT.T75N.L29Stab
public import CFSG.RankThree.PartTwo.Sec20.Item20ResProofXActs
public import CFSG.CGT.PushingUpLit.A78.BenderTI
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.Sec20.OneStepsProofV

public section

namespace CFSG.RankThree.PartTwo.Sec20.Res2

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.CGT.T75N

variable {F : Type} [Field F]

theorem slCoeMul (g h : SpecialLinearGroup (Fin 3) F) :
    ((g * h : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (g : Matrix (Fin 3) (Fin 3) F) * (h : Matrix (Fin 3) (Fin 3) F) := rfl

theorem slCoeOne : ((1 : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := rfl

theorem slCoeInvMul (g : SpecialLinearGroup (Fin 3) F) :
    ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (g : Matrix (Fin 3) (Fin 3) F) = 1 :=
  congrArg Subtype.val (inv_mul_cancel g)

theorem slCoeMulInv (g : SpecialLinearGroup (Fin 3) F) :
    (g : Matrix (Fin 3) (Fin 3) F) *
      ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 :=
  congrArg Subtype.val (mul_inv_cancel g)

variable (F) in
abbrev vstab : Subgroup (SpecialLinearGroup (Fin 3) F) := vecStab 3 (Pi.single 0 1)

variable (F) in
@[expose] def lstab : Subgroup (SpecialLinearGroup (Fin 3) F) where
  carrier := {g : SpecialLinearGroup (Fin 3) F | ∃ a : F,
    (g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 = a • Pi.single 0 1}
  one_mem' := ⟨1, by
    show ((1 : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ _ = _
    rw [slCoeOne, one_mulVec, one_smul]⟩
  mul_mem' := by
    rintro g h ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨b * a, ?_⟩
    show ((g * h : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ _ = _
    rw [slCoeMul, ← mulVec_mulVec, hb, mulVec_smul, ha, smul_smul]
  inv_mem' := by
    rintro g ⟨a, ha⟩
    have he : (Pi.single 0 1 : Fin 3 → F) = a • (((g⁻¹ : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1) := by
      rw [← mulVec_smul, ← ha, mulVec_mulVec, slCoeInvMul, one_mulVec]
    have ha0 : a ≠ 0 := by
      rintro rfl
      have := congrFun he 0
      simp at this
    refine ⟨a⁻¹, ?_⟩
    show ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ _ = _
    calc ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1
        = a⁻¹ • (a • (((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
          Pi.single 0 1)) := by rw [smul_smul, inv_mul_cancel₀ ha0, one_smul]
      _ = a⁻¹ • Pi.single 0 1 := by rw [← he]

variable (F) in
abbrev urad : Subgroup (SpecialLinearGroup (Fin 3) F) := radRow 3 F 0

theorem eq_smul_e0 {v : Fin 3 → F} (h1 : v 1 = 0) (h2 : v 2 = 0) :
    v = v 0 • (Pi.single 0 1 : Fin 3 → F) := by
  ext i
  fin_cases i <;> simp [h1, h2]

theorem mem_lstab_iff {g : SpecialLinearGroup (Fin 3) F} :
    g ∈ lstab F ↔ ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1) 1 = 0 ∧
      ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1) 2 = 0 := by
  constructor
  · rintro ⟨a, ha⟩
    rw [ha]
    simp
  · rintro ⟨h1, h2⟩
    exact ⟨((g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1) 0, eq_smul_e0 h1 h2⟩

theorem vstab_le_lstab : vstab F ≤ lstab F := fun g hg => by
  refine ⟨1, ?_⟩
  rw [one_smul]
  exact hg

theorem mulVec_e0_ne_zero (g : SpecialLinearGroup (Fin 3) F) :
    (g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 ≠ 0 := by
  intro h
  have h1 : ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1) = Pi.single 0 1 := by
    rw [mulVec_mulVec, slCoeInvMul, one_mulVec]
  rw [h, mulVec_zero] at h1
  have := congrFun h1 0
  simp at this

theorem mem_vstab_of_mem_lstab_of_pow_three [Finite F] (hq : Nat.card F % 3 = 2)
    {g : SpecialLinearGroup (Fin 3) F} (hg : g ∈ lstab F) (hg3 : g ^ 3 = 1) : g ∈ vstab F := by
  obtain ⟨a, ha⟩ := hg
  have h3 : ((g ^ 3 : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      Pi.single 0 1 = a ^ 3 • (Pi.single 0 1 : Fin 3 → F) := by
    rw [pow_succ, pow_succ, pow_one, slCoeMul, slCoeMul, ← mulVec_mulVec, ← mulVec_mulVec]
    simp only [ha, mulVec_smul, smul_smul]
    congr 1
    ring
  rw [hg3, slCoeOne, one_mulVec] at h3
  have h0 := congrFun h3 0
  simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, mul_one] at h0
  have ha1 : a = 1 := eq_one_of_pow_three_eq_one_of_card hq h0.symm
  show (g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 = Pi.single 0 1
  rw [ha, ha1, one_smul]

theorem exists_mem_vstab_mulVec_e1 {u : Fin 3 → F} (hu : u 1 ≠ 0 ∨ u 2 ≠ 0) :
    ∃ k ∈ vstab F, (k : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 1 1 = u := by
  rcases hu with h1 | h2
  · refine ⟨⟨!![1, u 0, 0; 0, u 1, 0; 0, u 2, (u 1)⁻¹], by simp [Matrix.det_fin_three, h1]⟩, ?_, ?_⟩
    · show !![1, u 0, 0; 0, u 1, 0; 0, u 2, (u 1)⁻¹] *ᵥ Pi.single 0 1 = Pi.single 0 1
      ext i
      fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three]
    · show !![1, u 0, 0; 0, u 1, 0; 0, u 2, (u 1)⁻¹] *ᵥ Pi.single 1 1 = u
      ext i
      fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three]
  · by_cases h1 : u 1 = 0
    · refine ⟨⟨!![1, u 0, 0; 0, u 1, -(u 2)⁻¹; 0, u 2, 0], by simp [Matrix.det_fin_three, h1, h2]⟩,
        ?_, ?_⟩
      · show !![1, u 0, 0; 0, u 1, -(u 2)⁻¹; 0, u 2, 0] *ᵥ Pi.single 0 1 = Pi.single 0 1
        ext i
        fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three]
      · show !![1, u 0, 0; 0, u 1, -(u 2)⁻¹; 0, u 2, 0] *ᵥ Pi.single 1 1 = u
        ext i
        fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three]
    · refine ⟨⟨!![1, u 0, 0; 0, u 1, 0; 0, u 2, (u 1)⁻¹], by simp [Matrix.det_fin_three, h1]⟩,
        ?_, ?_⟩
      · show !![1, u 0, 0; 0, u 1, 0; 0, u 2, (u 1)⁻¹] *ᵥ Pi.single 0 1 = Pi.single 0 1
        ext i
        fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three]
      · show !![1, u 0, 0; 0, u 1, 0; 0, u 2, (u 1)⁻¹] *ᵥ Pi.single 1 1 = u
        ext i
        fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three]

theorem inv_mulVec_mulVec (g : SpecialLinearGroup (Fin 3) F) (v : Fin 3 → F) :
    ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = v := by
  rw [mulVec_mulVec, slCoeInvMul, one_mulVec]

theorem mulVec_inv_mulVec (g : SpecialLinearGroup (Fin 3) F) (v : Fin 3 → F) :
    (g : Matrix (Fin 3) (Fin 3) F) *ᵥ
      (((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = v := by
  rw [mulVec_mulVec, slCoeMulInv, one_mulVec]

theorem mulVec_mul_mul (a b c : SpecialLinearGroup (Fin 3) F) (v : Fin 3 → F) :
    ((a * b * c : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
      (a : Matrix (Fin 3) (Fin 3) F) *ᵥ ((b : Matrix (Fin 3) (Fin 3) F) *ᵥ
        ((c : Matrix (Fin 3) (Fin 3) F) *ᵥ v)) := by
  rw [slCoeMul, slCoeMul, ← mulVec_mulVec, ← mulVec_mulVec]

theorem conj_mulVec_eq_iff (g r : SpecialLinearGroup (Fin 3) F) (v w : Fin 3 → F) :
    ((g⁻¹ * r * g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = w ↔
      (r : Matrix (Fin 3) (Fin 3) F) *ᵥ ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
        (g : Matrix (Fin 3) (Fin 3) F) *ᵥ w := by
  rw [mulVec_mul_mul]
  constructor
  · intro h
    rw [← h, mulVec_inv_mulVec]
  · intro h
    rw [h, inv_mulVec_mulVec]

theorem eq_top_of_vstab_le {H : Subgroup (SpecialLinearGroup (Fin 3) F)} (hH : vstab F ≤ H)
    (hnot : ¬ H ≤ lstab F) : H = ⊤ := by
  obtain ⟨h, hhH, hhP⟩ := Set.not_subset.mp hnot
  have hh' : ((h : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1) 1 ≠ 0 ∨
      ((h : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1) 2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hhP (mem_lstab_iff.mpr hcon)
  have key : ∀ w : Fin 3 → F, (w 1 ≠ 0 ∨ w 2 ≠ 0) →
      ∃ k ∈ H, (k : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 = w := by
    intro w hw
    obtain ⟨k₁, hk₁, hk₁e⟩ := exists_mem_vstab_mulVec_e1 hh'
    obtain ⟨k₂, hk₂, hk₂e⟩ := exists_mem_vstab_mulVec_e1 hw
    refine ⟨k₂ * k₁⁻¹ * h, H.mul_mem (H.mul_mem (hH hk₂) (H.inv_mem (hH hk₁))) hhH, ?_⟩
    rw [slCoeMul, slCoeMul, ← mulVec_mulVec,
      ← mulVec_mulVec, ← hk₁e, inv_mulVec_mulVec, hk₂e]
  rw [eq_top_iff]
  intro A _
  set w := (A : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 with hw
  obtain ⟨k, hkH, hk⟩ : ∃ k ∈ H, (k : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 = w := by
    by_cases hw' : w 1 ≠ 0 ∨ w 2 ≠ 0
    · exact key w hw'
    · push Not at hw'
      have hw0 : w 0 ≠ 0 := by
        intro h0
        apply mulVec_e0_ne_zero A
        rw [← hw]
        ext i
        fin_cases i <;> simp [h0, hw'.1, hw'.2]
      obtain ⟨k₁, hk₁H, hk₁⟩ := key (Pi.single 1 1) (Or.inl (by simp))
      obtain ⟨k₂, hk₂H, hk₂⟩ := key (w 0 • Pi.single 1 1) (Or.inl (by simp [hw0]))
      refine ⟨k₁⁻¹ * k₂, H.mul_mem (H.inv_mem hk₁H) hk₂H, ?_⟩
      rw [slCoeMul, ← mulVec_mulVec, hk₂, mulVec_smul, ← hk₁,
        inv_mulVec_mulVec]
      exact (eq_smul_e0 hw'.1 hw'.2).symm
  have hq : k⁻¹ * A ∈ vstab F := by
    show ((k⁻¹ * A : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 =
      Pi.single 0 1
    rw [slCoeMul, ← mulVec_mulVec, ← hw, ← hk, inv_mulVec_mulVec]
  have := H.mul_mem hkH (hH hq)
  rwa [mul_inv_cancel_left] at this

theorem rowMat_zero_mulVec (a v : Fin 3 → F) :
    rowMat 0 a *ᵥ v = v + (a ⬝ᵥ v) • (Pi.single 0 1 : Fin 3 → F) := by
  rw [rowMat, add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul]

theorem mem_urad_iff {g : SpecialLinearGroup (Fin 3) F} :
    g ∈ urad F ↔ (g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧
      ∀ v : Fin 3 → F, ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 1 = v 1 ∧
        ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 2 = v 2 := by
  constructor
  · rintro ⟨a, ha, hg⟩
    have ha0 : a 0 = 0 := ha 0 le_rfl
    rw [hg]
    refine ⟨?_, fun v => ?_⟩
    · rw [rowMat_zero_mulVec]
      simp [ha0]
    · rw [rowMat_zero_mulVec]
      simp
  · rintro ⟨h0, h12⟩
    refine ⟨fun j => if j = 0 then 0 else (g : Matrix (Fin 3) (Fin 3) F) 0 j, ?_, ?_⟩
    · intro i hi
      have : i = 0 := Fin.le_zero_iff.mp hi
      simp [this]
    · have hcol : ∀ j : Fin 3, ∀ i : Fin 3, i ≠ 0 →
          (g : Matrix (Fin 3) (Fin 3) F) i j = if i = j then 1 else 0 := by
        intro j i hi
        have h := h12 (Pi.single j 1)
        rw [mulVec_single_one] at h
        have hi' : i = 1 ∨ i = 2 := by fin_cases i <;> simp_all
        rcases hi' with rfl | rfl
        · have h1 := h.1
          rw [col_apply] at h1
          rw [h1]
          simp [Pi.single_apply, eq_comm]
        · have h2 := h.2
          rw [col_apply] at h2
          rw [h2]
          simp [Pi.single_apply, eq_comm]
      have h00 : (g : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 := by
        have := congrFun h0 0
        rwa [mulVec_single_one, col_apply, Pi.single_eq_same] at this
      ext i j
      by_cases hi : i = 0
      · subst hi
        by_cases hj : j = 0
        · subst hj
          simp [rowMat, vecMulVec_apply, h00]
        · simp [rowMat, vecMulVec_apply, hj, Ne.symm hj]
      · rw [hcol j i hi]
        simp [rowMat, vecMulVec_apply, hi, Matrix.one_apply]

theorem urad_le_vstab : urad F ≤ vstab F := fun _ hg => (mem_urad_iff.mp hg).1

theorem conj_mem_urad {k : SpecialLinearGroup (Fin 3) F} (hk : k ∈ lstab F)
    {u : SpecialLinearGroup (Fin 3) F} (hu : u ∈ urad F) : k * u * k⁻¹ ∈ urad F := by
  obtain ⟨hu0, hu12⟩ := mem_urad_iff.mp hu
  obtain ⟨a, ha⟩ := hk
  have hkinv : k⁻¹ ∈ lstab F := (lstab F).inv_mem ⟨a, ha⟩
  obtain ⟨b, hb⟩ := hkinv
  rw [mem_urad_iff]
  refine ⟨?_, fun v => ?_⟩
  · rw [slCoeMul, slCoeMul, ← mulVec_mulVec, ← mulVec_mulVec,
      hb, mulVec_smul, hu0, ← hb, mulVec_mulVec, slCoeMulInv, one_mulVec]
  · set w := ((k⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v with hw
    have hdiff : (u : Matrix (Fin 3) (Fin 3) F) *ᵥ w =
        w + ((u : Matrix (Fin 3) (Fin 3) F) *ᵥ w - w) 0 • (Pi.single 0 1 : Fin 3 → F) := by
      have h := eq_smul_e0 (v := (u : Matrix (Fin 3) (Fin 3) F) *ᵥ w - w)
        (by simp [(hu12 w).1]) (by simp [(hu12 w).2])
      rw [← h]
      abel
    rw [slCoeMul, slCoeMul, ← mulVec_mulVec, ← mulVec_mulVec,
      ← hw, hdiff, mulVec_add, mulVec_smul, ha, hw, mulVec_mulVec, slCoeMulInv, one_mulVec]
    simp

theorem card_urad [Finite F] : Nat.card (urad F) = Nat.card F ^ 2 :=
  card_radRow (n := 3) 0

theorem unitriangular_mulVec_e0 {u : SpecialLinearGroup (Fin 3) F}
    (hu : u ∈ LinearFlag.unitriangular 3 F) :
    (u : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  obtain ⟨hlow, hdiag⟩ := LinearFlag.mem_unitriangular.mp hu
  ext i
  rw [mulVec_single_one, col_apply]
  fin_cases i
  · simpa using hdiag 0
  · simpa using hlow 1 0 (by decide)
  · simpa using hlow 2 0 (by decide)

theorem unitriangular_mulVec_e1 {u : SpecialLinearGroup (Fin 3) F}
    (hu : u ∈ LinearFlag.unitriangular 3 F) :
    (u : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 1 1 =
      Pi.single 1 1 + (u : Matrix (Fin 3) (Fin 3) F) 0 1 • (Pi.single 0 1 : Fin 3 → F) := by
  obtain ⟨hlow, hdiag⟩ := LinearFlag.mem_unitriangular.mp hu
  ext i
  rw [mulVec_single_one, col_apply]
  fin_cases i
  · simp
  · simpa using hdiag 1
  · simpa using hlow 2 1 (by decide)

theorem eq_one_of_forall_mulVec_eq {g : SpecialLinearGroup (Fin 3) F}
    (h : ∀ v : Fin 3 → F, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v) : g = 1 := by
  apply Subtype.ext
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  rw [mulVec_single_one, col_apply] at this
  rw [this]
  simp [Pi.single_apply, Matrix.one_apply]

theorem exists_conj_unitriangular_of_isPGroup [Finite F] [CharP F 2]
    {R : Subgroup (SpecialLinearGroup (Fin 3) F)} (hR : IsPGroup 2 R) :
    ∃ g : SpecialLinearGroup (Fin 3) F, ∀ r ∈ R, g⁻¹ * r * g ∈ LinearFlag.unitriangular 3 F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hRQ⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_conj_unitriangular_le_sylow Q
  obtain ⟨P, hP⟩ := LinearFlag.exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
  set U := LinearFlag.unitriangular 3 F with hU
  have hle : U.map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup (SpecialLinearGroup (Fin 3) F)) := by
    rintro _ ⟨u, hu, rfl⟩
    exact hg u hu
  have hcard : Nat.card (Q : Subgroup (SpecialLinearGroup (Fin 3) F)) ≤
      Nat.card (U.map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, ← hP, Sylow.card_eq_multiplicity,
      Sylow.card_eq_multiplicity]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  refine ⟨g, fun r hr => ?_⟩
  have hrQ : r ∈ (Q : Subgroup (SpecialLinearGroup (Fin 3) F)) := hRQ hr
  rw [← heq] at hrQ
  obtain ⟨u, hu, rfl⟩ := hrQ
  simpa [MulAut.conj_apply, mul_assoc] using hu

variable (F) in
@[expose] def IrredModE0 (Y : Subgroup (SpecialLinearGroup (Fin 3) F)) : Prop :=
  ∀ S : AddSubgroup (Fin 3 → F), (∀ k ∈ Y, ∀ w ∈ S, (k : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ S) →
    ∀ u ∈ S, (u 1 ≠ 0 ∨ u 2 ≠ 0) → S = ⊤

theorem irredModE0_vstab : IrredModE0 F (vstab F) := fun S hS _ hu hu' =>
  addSubgroup_eq_top_of_vectorStabilizer_invariant S (fun h hh y hy => hS h hh y hy) hu hu'

theorem le_urad_of_isPGroup [Finite F] [CharP F 2] {Y R : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hYv : Y ≤ vstab F) (hY : IrredModE0 F Y) (hR : IsPGroup 2 R)
    (hYR : Y ≤ Subgroup.normalizer (R : Set (SpecialLinearGroup (Fin 3) F))) : R ≤ urad F := by
  obtain ⟨g, hg⟩ := exists_conj_unitriangular_of_isPGroup hR
  have hconj : ∀ k ∈ Y, ∀ r ∈ R, k⁻¹ * r * k ∈ R := by
    intro k hk r hr
    have := (Subgroup.mem_normalizer_iff.mp (hYR (Y.inv_mem hk)) r).mp hr
    simpa using this
  have hrg : ∀ r ∈ R, (r : Matrix (Fin 3) (Fin 3) F) *ᵥ
      ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1) =
        (g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 :=
    fun r hr => (conj_mulVec_eq_iff g r _ _).mp (unitriangular_mulVec_e0 (hg r hr))
  let Fix : AddSubgroup (Fin 3 → F) :=
    { carrier := {w | ∀ r ∈ R, (r : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w}
      zero_mem' := fun r _ => mulVec_zero _
      add_mem' := fun ha hb r hr => by rw [mulVec_add, ha r hr, hb r hr]
      neg_mem' := fun ha r hr => by rw [mulVec_neg, ha r hr] }
  have hFix : ∀ k ∈ Y, ∀ w ∈ Fix, (k : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ Fix :=
    fun k hk w hw r hr => (conj_mulVec_eq_iff k r w w).mp (hw _ (hconj k hk r hr))
  have hge0 : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 ∈ Fix := hrg
  by_cases hoff : ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1) 1 ≠ 0 ∨
      ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1) 2 ≠ 0
  ·
    have htop := hY Fix hFix _ hge0 hoff
    intro r hr
    have : r = 1 := eq_one_of_forall_mulVec_eq fun v => by
      have hv : v ∈ Fix := htop ▸ AddSubgroup.mem_top v
      exact hv r hr
    rw [this]
    exact (urad F).one_mem
  push Not at hoff
  set lam := ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1) 0 with hlam
  have hge : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 = lam • Pi.single 0 1 :=
    eq_smul_e0 hoff.1 hoff.2
  have hlam0 : lam ≠ 0 := by
    intro h0
    apply mulVec_e0_ne_zero g
    rw [hge, h0, zero_smul]
  have hRe0 : ∀ r ∈ R, (r : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    intro r hr
    have h := hrg r hr
    rw [hge, mulVec_smul] at h
    exact smul_right_injective _ hlam0 h
  let Fix' : AddSubgroup (Fin 3 → F) :=
    { carrier := {w | ∀ r ∈ R, ((r : Matrix (Fin 3) (Fin 3) F) *ᵥ w - w) 1 = 0 ∧
        ((r : Matrix (Fin 3) (Fin 3) F) *ᵥ w - w) 2 = 0}
      zero_mem' := fun r _ => by simp
      add_mem' := fun ha hb r hr => by
        refine ⟨?_, ?_⟩
        · have h1 := (ha r hr).1
          have h2 := (hb r hr).1
          simp only [Pi.sub_apply, mulVec_add, Pi.add_apply] at h1 h2 ⊢
          linear_combination h1 + h2
        · have h1 := (ha r hr).2
          have h2 := (hb r hr).2
          simp only [Pi.sub_apply, mulVec_add, Pi.add_apply] at h1 h2 ⊢
          linear_combination h1 + h2
      neg_mem' := fun ha r hr => by
        refine ⟨?_, ?_⟩
        · have h1 := (ha r hr).1
          simp only [Pi.sub_apply, mulVec_neg, Pi.neg_apply] at h1 ⊢
          linear_combination -h1
        · have h1 := (ha r hr).2
          simp only [Pi.sub_apply, mulVec_neg, Pi.neg_apply] at h1 ⊢
          linear_combination -h1 }
  have hFix' : ∀ k ∈ Y, ∀ w ∈ Fix', (k : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ Fix' := by
    intro k hk w hw r hr
    obtain ⟨h1, h2⟩ := hw _ (hconj k hk r hr)
    set x := ((k⁻¹ * r * k : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w - w
      with hx
    have hxe : x = x 0 • (Pi.single 0 1 : Fin 3 → F) := eq_smul_e0 h1 h2
    have hkx : (k : Matrix (Fin 3) (Fin 3) F) *ᵥ x =
        (r : Matrix (Fin 3) (Fin 3) F) *ᵥ ((k : Matrix (Fin 3) (Fin 3) F) *ᵥ w) -
          (k : Matrix (Fin 3) (Fin 3) F) *ᵥ w := by
      rw [hx, mulVec_sub, mulVec_mul_mul, mulVec_inv_mulVec]
    have hk0 : (k : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 = Pi.single 0 1 := hYv hk
    rw [← hkx, hxe, mulVec_smul, hk0]
    simp
  have hge1 : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 1 1 ∈ Fix' := by
    intro r hr
    have hu := unitriangular_mulVec_e1 (hg r hr)
    have h : (r : Matrix (Fin 3) (Fin 3) F) *ᵥ ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 1 1) =
        (g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 1 1 +
          ((g⁻¹ * r * g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1 •
            (lam • (Pi.single 0 1 : Fin 3 → F)) := by
      rw [(conj_mulVec_eq_iff g r _ _).mp hu, mulVec_add, mulVec_smul, hge]
    rw [h]
    simp
  have hoff1 : ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 1 1) 1 ≠ 0 ∨
      ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 1 1) 2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h1 := eq_smul_e0 hcon.1 hcon.2
    have h2 : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ (Pi.single 1 1 -
        (((g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 1 1) 0 * lam⁻¹) • Pi.single 0 1) = 0 := by
      rw [mulVec_sub, mulVec_smul, hge, smul_smul, mul_assoc, inv_mul_cancel₀ hlam0, mul_one,
        ← h1, sub_self]
    have h3 := congrArg (fun x => ((g⁻¹ : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) *ᵥ x) h2
    simp only [inv_mulVec_mulVec, mulVec_zero] at h3
    have := congrFun h3 1
    simp at this
  have htop := hY Fix' hFix' _ hge1 hoff1
  intro r hr
  rw [mem_urad_iff]
  refine ⟨hRe0 r hr, fun v => ?_⟩
  have hv : v ∈ Fix' := htop ▸ AddSubgroup.mem_top v
  obtain ⟨h1, h2⟩ := hv r hr
  simp only [Pi.sub_apply, sub_eq_zero] at h1 h2
  exact ⟨h1, h2⟩

abbrev uelt (a : Fin 3 → F) (ha : a 0 = 0) : SpecialLinearGroup (Fin 3) F := rowSL 0 a ha

theorem uelt_mem (a : Fin 3 → F) (ha : a 0 = 0) : uelt a ha ∈ urad F :=
  ⟨a, fun i hi => by rw [Fin.le_zero_iff.mp hi]; exact ha, rfl⟩

theorem exists_eq_uelt {u : SpecialLinearGroup (Fin 3) F} (hu : u ∈ urad F) :
    ∃ (a : Fin 3 → F) (ha : a 0 = 0), u = uelt a ha := by
  obtain ⟨a, ha, hu⟩ := hu
  exact ⟨a, ha 0 le_rfl, Subtype.ext hu⟩

theorem uelt_mul (a b : Fin 3 → F) (ha : a 0 = 0) (hb : b 0 = 0) :
    uelt a ha * uelt b hb = uelt (a + b) (by simp [ha, hb]) :=
  Subtype.ext (rowMat_mul 0 ha b)

theorem uelt_zero : uelt (0 : Fin 3 → F) rfl = 1 := Subtype.ext (rowMat_zero 0)

theorem uelt_eq_one {a : Fin 3 → F} (ha : a 0 = 0) (h : a = 0) : uelt a ha = 1 := by
  subst h
  exact uelt_zero

theorem conj_uelt {k : SpecialLinearGroup (Fin 3) F} (hk : k ∈ vstab F) (a : Fin 3 → F)
    (ha : a 0 = 0) :
    k * uelt a ha * k⁻¹ = uelt (a ᵥ* ((k⁻¹ : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F)) (by
        rw [vecMul_apply_eq, show ((k⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
          *ᵥ Pi.single 0 1 = Pi.single 0 1 from (vstab F).inv_mem hk, dotProduct_single, ha,
          mul_one]) := by
  apply Subtype.ext
  show (k : Matrix (Fin 3) (Fin 3) F) * rowMat 0 a *
    ((k⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = rowMat 0 _
  have hk0 : (k : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 = Pi.single 0 1 := hk
  rw [rowMat, conj_one_add_vecMulVec _ _ (slCoeMulInv k), hk0, rowMat]

theorem vecMul_transvection' (b : Fin 3 → F) (i j : Fin 3) (d : F) :
    b ᵥ* transvection i j d = b + Pi.single j (b i * d) := by
  rw [transvection, Matrix.vecMul_add, Matrix.vecMul_one]
  congr 1
  ext l
  simp only [vecMul, dotProduct, Matrix.single_apply, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · by_cases h : j = l
    · subst h
      simp
    · simp [h, Ne.symm h]
  · intro m _ hm
    simp [Ne.symm hm]
  · simp

theorem transvection_mem_vstab {i j : Fin 3} (hij : i ≠ j) (hj : j ≠ 0) (d : F) :
    SpecialLinearGroup.transvection hij d ∈ vstab F := by
  show ((SpecialLinearGroup.transvection hij d : SpecialLinearGroup (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 = Pi.single 0 1
  rw [SpecialLinearGroup.transvection_coe, ← transvection, LinearFlag.transvection_mulVec,
    Pi.single_apply, ite_eq_right_iff.mpr (fun h => absurd h hj), mul_zero, Pi.single_zero,
    add_zero]

theorem eq_urad_of_le {R : Subgroup (SpecialLinearGroup (Fin 3) F)} (hRu : R ≤ urad F)
    (hR : vstab F ≤ Subgroup.normalizer (R : Set (SpecialLinearGroup (Fin 3) F))) (hne : R ≠ ⊥) :
    R = urad F := by
  classical
  let P : (Fin 3 → F) → Prop := fun b => ∃ hb : b 0 = 0, uelt b hb ∈ R
  have hPadd : ∀ b c, P b → P c → P (b + c) := by
    rintro b c ⟨hb, hbR⟩ ⟨hc, hcR⟩
    refine ⟨by simp [hb, hc], ?_⟩
    rw [← uelt_mul b c hb hc]
    exact R.mul_mem hbR hcR
  have hPinv : ∀ b (k : SpecialLinearGroup (Fin 3) F), k ∈ vstab F → P b →
      P (b ᵥ* ((k⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
    rintro b k hk ⟨hb, hbR⟩
    have h := (Subgroup.mem_normalizer_iff.mp (hR hk) _).mp hbR
    rw [conj_uelt hk b hb] at h
    exact ⟨_, h⟩
  have hT : ∀ (i j : Fin 3) (hij : i ≠ j), j ≠ 0 → ∀ (d : F) b, P b →
      P (b + Pi.single j (b i * d)) := by
    intro i j hij hj d b hb
    have hk := (vstab F).inv_mem (transvection_mem_vstab (F := F) hij hj d)
    have := hPinv b _ hk hb
    rw [inv_inv, SpecialLinearGroup.transvection_coe, ← transvection,
      vecMul_transvection'] at this
    exact this
  have hsub : ∀ (i j : Fin 3) (hij : i ≠ j), j ≠ 0 → ∀ (d : F) b, P b →
      P (Pi.single j (b i * d)) := by
    intro i j hij hj d b hb
    obtain ⟨hb0, hbR⟩ := hb
    obtain ⟨h1, h1R⟩ := hT i j hij hj d b ⟨hb0, hbR⟩
    have hneg : P (-b) := ⟨by simp [hb0], by
      have : uelt (-b) (by simp [hb0]) = (uelt b hb0)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, uelt_mul]
        exact uelt_eq_one _ (neg_add_cancel b)
      rw [this]
      exact R.inv_mem hbR⟩
    have := hPadd _ _ ⟨h1, h1R⟩ hneg
    simpa using this
  obtain ⟨⟨u, huR⟩, hu1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hu1 : u ≠ 1 := fun h => hu1' (Subtype.ext h)
  obtain ⟨a, ha0, hau⟩ := exists_eq_uelt (hRu huR)
  have hPa : P a := ⟨ha0, hau ▸ huR⟩
  have ha12 : a 1 ≠ 0 ∨ a 2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hu1
    have : a = 0 := by
      ext i
      fin_cases i <;> simp [ha0, hcon.1, hcon.2]
    rw [hau]
    exact uelt_eq_one ha0 this
  have hall : ∀ x : F, P (Pi.single 1 x) ∧ P (Pi.single 2 x) := by
    rcases ha12 with h1 | h2
    · have hs2 : ∀ x : F, P (Pi.single 2 x) := fun x => by
        have := hsub 1 2 (by decide) (by decide) (x / a 1) a hPa
        rwa [mul_div_cancel₀ x h1] at this
      have hs1 : ∀ x : F, P (Pi.single 1 x) := fun x => by
        have := hsub 2 1 (by decide) (by decide) x _ (hs2 1)
        simpa using this
      exact fun x => ⟨hs1 x, hs2 x⟩
    · have hs1 : ∀ x : F, P (Pi.single 1 x) := fun x => by
        have := hsub 2 1 (by decide) (by decide) (x / a 2) a hPa
        rwa [mul_div_cancel₀ x h2] at this
      have hs2 : ∀ x : F, P (Pi.single 2 x) := fun x => by
        have := hsub 1 2 (by decide) (by decide) x _ (hs1 1)
        simpa using this
      exact fun x => ⟨hs1 x, hs2 x⟩
  refine le_antisymm hRu fun w hw => ?_
  obtain ⟨b, hb0, rfl⟩ := exists_eq_uelt hw
  have hbsum : b = Pi.single 1 (b 1) + Pi.single 2 (b 2) := by
    ext i
    fin_cases i <;> simp [hb0]
  obtain ⟨_, hR'⟩ := hPadd _ _ (hall (b 1)).1 (hall (b 2)).2
  convert hR' using 2

@[expose] def blkMat (k : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 2) (Fin 2) F :=
  !![k 1 1, k 1 2; k 2 1, k 2 2]

theorem col_zero_of_mem_vstab {k : SpecialLinearGroup (Fin 3) F} (hk : k ∈ vstab F) :
    (k : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 ∧ (k : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧
      (k : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := by
  have h : (k : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 = Pi.single 0 1 := hk
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  rw [mulVec_single_one, col_apply] at h0 h1 h2
  simp only [Pi.single_eq_same] at h0
  exact ⟨h0, by simpa using h1, by simpa using h2⟩

theorem blkMat_mul {k k' : Matrix (Fin 3) (Fin 3) F} (h1 : k 1 0 = 0) (h2 : k 2 0 = 0) :
    blkMat (k * k') = blkMat k * blkMat k' := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkMat, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, h1, h2]

theorem det_blkMat {k : SpecialLinearGroup (Fin 3) F} (hk : k ∈ vstab F) :
    (blkMat (k : Matrix (Fin 3) (Fin 3) F)).det = 1 := by
  obtain ⟨h00, h10, h20⟩ := col_zero_of_mem_vstab hk
  have hdet : (k : Matrix (Fin 3) (Fin 3) F).det = 1 := k.2
  rw [det_fin_three, h00, h10, h20] at hdet
  rw [det_fin_two]
  simp only [blkMat, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one]
  linear_combination hdet

@[expose] def blkSL {k : SpecialLinearGroup (Fin 3) F} (hk : k ∈ vstab F) :
    SpecialLinearGroup (Fin 2) F :=
  ⟨blkMat (k : Matrix (Fin 3) (Fin 3) F), det_blkMat hk⟩

theorem mulVec_one_two_of_mem_vstab {k : SpecialLinearGroup (Fin 3) F} (hk : k ∈ vstab F)
    (v : Fin 3 → F) :
    ((k : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 1 =
        (k : Matrix (Fin 3) (Fin 3) F) 1 1 * v 1 + (k : Matrix (Fin 3) (Fin 3) F) 1 2 * v 2 ∧
      ((k : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 2 =
        (k : Matrix (Fin 3) (Fin 3) F) 2 1 * v 1 + (k : Matrix (Fin 3) (Fin 3) F) 2 2 * v 2 := by
  obtain ⟨-, h10, h20⟩ := col_zero_of_mem_vstab hk
  simp [mulVec, dotProduct, Fin.sum_univ_three, h10, h20]

theorem coe_epsHom_one (B : SpecialLinearGroup (Fin 2) F) :
    ((epsHom 1 F B : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0; 0, (B : Matrix (Fin 2) (Fin 2) F) 0 0, (B : Matrix (Fin 2) (Fin 2) F) 0 1;
        0, (B : Matrix (Fin 2) (Fin 2) F) 1 0, (B : Matrix (Fin 2) (Fin 2) F) 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem epsHom_mem_vstab (B : SpecialLinearGroup (Fin 2) F) : epsHom 1 F B ∈ vstab F := by
  show ((epsHom 1 F B : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
    Pi.single 0 1 = Pi.single 0 1
  rw [coe_epsHom_one]
  ext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three]

theorem mul_epsHom_inv_mem_urad {k : SpecialLinearGroup (Fin 3) F} (hk : k ∈ vstab F) :
    k * (epsHom 1 F (blkSL hk))⁻¹ ∈ urad F := by
  set ε := epsHom 1 F (blkSL hk) with hε
  have hεv : ε ∈ vstab F := epsHom_mem_vstab _
  rw [mem_urad_iff]
  refine ⟨(vstab F).mul_mem hk ((vstab F).inv_mem hεv), fun v => ?_⟩
  set w := ((ε⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v with hw
  have hv : v = (ε : Matrix (Fin 3) (Fin 3) F) *ᵥ w := by rw [hw, mulVec_inv_mulVec]
  rw [slCoeMul, ← mulVec_mulVec, ← hw]
  obtain ⟨hk1, hk2⟩ := mulVec_one_two_of_mem_vstab hk w
  obtain ⟨hε1, hε2⟩ := mulVec_one_two_of_mem_vstab hεv w
  have hεe : (ε : Matrix (Fin 3) (Fin 3) F) 1 1 = (k : Matrix (Fin 3) (Fin 3) F) 1 1 ∧
      (ε : Matrix (Fin 3) (Fin 3) F) 1 2 = (k : Matrix (Fin 3) (Fin 3) F) 1 2 ∧
      (ε : Matrix (Fin 3) (Fin 3) F) 2 1 = (k : Matrix (Fin 3) (Fin 3) F) 2 1 ∧
      (ε : Matrix (Fin 3) (Fin 3) F) 2 2 = (k : Matrix (Fin 3) (Fin 3) F) 2 2 := by
    rw [hε, coe_epsHom_one]
    exact ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [hk1]
    conv_rhs => rw [hv]
    rw [hε1, hεe.1, hεe.2.1]
  · rw [hk2]
    conv_rhs => rw [hv]
    rw [hε2, hεe.2.2.1, hεe.2.2.2]

theorem sq_eq_one_of_mem_urad [CharP F 2] {u : SpecialLinearGroup (Fin 3) F} (hu : u ∈ urad F) :
    u ^ 2 = 1 := by
  obtain ⟨a, ha, rfl⟩ := exists_eq_uelt hu
  rw [pow_two, uelt_mul]
  exact uelt_eq_one _ (by rw [← two_smul ℕ a]; ext i; simp [CharTwo.two_eq_zero])

theorem not_mem_urad_of_pow_three [CharP F 2] {c : SpecialLinearGroup (Fin 3) F} (hc3 : c ^ 3 = 1)
    (hc1 : c ≠ 1) : c ∉ urad F := by
  intro hc
  apply hc1
  have h2 := sq_eq_one_of_mem_urad hc
  calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
    _ = 1 := by rw [hc3, h2, inv_one, one_mul]

theorem blkSL_ne_one_of_not_mem_urad {c : SpecialLinearGroup (Fin 3) F} (hc : c ∈ vstab F)
    (hcu : c ∉ urad F) : blkSL hc ≠ 1 := by
  intro h
  apply hcu
  have := mul_epsHom_inv_mem_urad hc
  rwa [h, map_one, inv_one, mul_one] at this

theorem uelt_injective {a b : Fin 3 → F} {ha : a 0 = 0} {hb : b 0 = 0}
    (h : uelt a ha = uelt b hb) : a = b := by
  ext j
  have := congrFun (congrFun (congrArg Subtype.val h) 0) j
  simpa [rowMat, vecMulVec_apply] using this

theorem single_vecMul' (i : Fin 3) (M : Matrix (Fin 3) (Fin 3) F) :
    (Pi.single i 1 : Fin 3 → F) ᵥ* M = M i := by
  ext j
  simp [vecMul, dotProduct, Pi.single_apply]

theorem exists_commutator_ne_one {c : SpecialLinearGroup (Fin 3) F} (hc : c ∈ vstab F)
    (hcu : c ∉ urad F) : ∃ u ∈ urad F, u * c * u⁻¹ * c⁻¹ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  apply hcu
  rw [← inv_inv c]
  refine (urad F).inv_mem ?_
  have hci : c⁻¹ ∈ vstab F := (vstab F).inv_mem hc
  have hrow : ∀ (a : Fin 3 → F) (ha : a 0 = 0), a ᵥ* ((c⁻¹ : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = a := by
    intro a ha
    have h1 := hcon (uelt a ha) (uelt_mem a ha)
    have h2 : c * uelt a ha * c⁻¹ = uelt a ha := by
      have h3 : uelt a ha * c = c * uelt a ha := by
        have := congrArg (· * c) h1
        simp only [inv_mul_cancel_right, one_mul] at this
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this
      rw [← h3]
      group
    rw [conj_uelt hc a ha] at h2
    exact uelt_injective h2
  have hr1 := hrow (Pi.single 1 1) (by simp)
  have hr2 := hrow (Pi.single 2 1) (by simp)
  rw [single_vecMul'] at hr1 hr2
  rw [mem_urad_iff]
  refine ⟨hci, fun v => ⟨?_, ?_⟩⟩
  · have : (((c⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 1 =
        (Pi.single 1 1 : Fin 3 → F) ⬝ᵥ v := by
      rw [mulVec, ← hr1]
    rw [this, single_dotProduct, one_mul]
  · have : (((c⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 2 =
        (Pi.single 2 1 : Fin 3 → F) ⬝ᵥ v := by
      rw [mulVec, ← hr2]
    rw [this, single_dotProduct, one_mul]

theorem eq_vstab_of_normal [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F)
    {Y : Subgroup (SpecialLinearGroup (Fin 3) F)} (hYv : Y ≤ vstab F)
    (hY : vstab F ≤ Subgroup.normalizer (Y : Set (SpecialLinearGroup (Fin 3) F)))
    {c : SpecialLinearGroup (Fin 3) F} (hcY : c ∈ Y) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    Y = vstab F := by
  have hcv : c ∈ vstab F := hYv hcY
  have hcu := not_mem_urad_of_pow_three hc3 hc1
  have huY : urad F ≤ Y := by
    have hR : Y ⊓ urad F = urad F := by
      refine eq_urad_of_le inf_le_right (fun k hk => ?_) ?_
      · exact Sec20.mem_normalizer_inf_of_mem (hY hk) (Subgroup.mem_normalizer_iff.mpr fun u => by
          constructor
          · exact fun hu => conj_mem_urad (vstab_le_lstab hk) hu
          · intro hu
            have := conj_mem_urad (vstab_le_lstab ((vstab F).inv_mem hk)) hu
            simpa [mul_assoc] using this)
      · obtain ⟨u, hu, hne⟩ := exists_commutator_ne_one hcv hcu
        refine (Subgroup.ne_bot_iff_exists_ne_one).mpr ⟨⟨u * c * u⁻¹ * c⁻¹, ?_, ?_⟩, ?_⟩
        · exact Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (hY (urad_le_vstab hu)) c).mp hcY)
            (Y.inv_mem hcY)
        · have := conj_mem_urad (vstab_le_lstab hcv) ((urad F).inv_mem hu)
          rw [show u * c * u⁻¹ * c⁻¹ = u * (c * u⁻¹ * c⁻¹) by group]
          exact (urad F).mul_mem hu this
        · intro h
          exact hne (congrArg Subtype.val h)
    rw [← hR]
    exact inf_le_left
  have hεc : epsHom 1 F (blkSL hcv) ∈ Y := by
    have h := mul_epsHom_inv_mem_urad hcv
    have := Y.mul_mem (Y.inv_mem (huY h)) hcY
    simpa using this
  have hC1 : blkSL hcv ≠ 1 := blkSL_ne_one_of_not_mem_urad hcv hcu
  set Y' := Y.comap (epsHom 1 F) with hY'
  have hY'n : Y'.Normal := ⟨fun B hB A => by
    show epsHom 1 F (A * B * A⁻¹) ∈ Y
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hY (epsHom_mem_vstab A)) _).mp hB⟩
  have hFc : 4 ≤ Nat.card F := h4
  have : IsSimpleGroup (SpecialLinearGroup (Fin 2) F) :=
    CFSG.CGT.PushingUpLit.A78.isSimpleGroup_SL2_charTwo F hFc
  have hY'top : Y' = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Y' with h | h
    · exfalso
      have hmem : blkSL hcv ∈ Y' := hεc
      rw [h, Subgroup.mem_bot] at hmem
      exact hC1 hmem
    · exact h
  refine le_antisymm hYv fun k hk => ?_
  have h1 := huY (mul_epsHom_inv_mem_urad hk)
  have h2 : epsHom 1 F (blkSL hk) ∈ Y := by
    have : blkSL hk ∈ Y' := hY'top ▸ Subgroup.mem_top _
    exact this
  have := Y.mul_mem h1 h2
  simpa using this

theorem sl2_eq_one_of_fix [CharP F 2] {C : SpecialLinearGroup (Fin 2) F} (hC3 : C ^ 3 = 1)
    {x : Fin 2 → F} (hx : x ≠ 0) (hCx : (C : Matrix (Fin 2) (Fin 2) F) *ᵥ x = x) : C = 1 := by
  set M := (C : Matrix (Fin 2) (Fin 2) F) with hM
  have hdet1 : (M - 1).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx, by rw [sub_mulVec, hCx, one_mulVec, sub_self]⟩
  have hdet : M.det = 1 := C.2
  rw [det_fin_two] at hdet1 hdet
  simp only [Matrix.sub_apply, one_apply_eq, one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), sub_zero] at hdet1
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have htr : M 0 0 + M 1 1 = 0 := by linear_combination hdet - hdet1 + h2
  have hsq : M * M = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination M 0 0 * htr - hdet - h2
    · linear_combination M 0 1 * htr
    · linear_combination M 1 0 * htr
    · linear_combination M 1 1 * htr - hdet - h2
  have hC2 : C ^ 2 = 1 := Subtype.ext (by rw [pow_two]; exact hsq)
  calc C = C ^ 3 * (C ^ 2)⁻¹ := by group
    _ = 1 := by rw [hC3, hC2, inv_one, one_mul]

theorem blkSL_pow_three {c : SpecialLinearGroup (Fin 3) F} (hc : c ∈ vstab F) (hc3 : c ^ 3 = 1) :
    blkSL hc ^ 3 = 1 := by
  apply Subtype.ext
  obtain ⟨-, h10, h20⟩ := col_zero_of_mem_vstab hc
  have hcc : c * c ∈ vstab F := (vstab F).mul_mem hc hc
  obtain ⟨-, h10', h20'⟩ := col_zero_of_mem_vstab hcc
  have h : blkMat (((c * c) * c : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      blkMat (c : Matrix (Fin 3) (Fin 3) F) * blkMat (c : Matrix (Fin 3) (Fin 3) F) *
        blkMat (c : Matrix (Fin 3) (Fin 3) F) := by
    rw [slCoeMul, blkMat_mul h10' h20', slCoeMul, blkMat_mul h10 h20]
  have hc3' : ((c * c) * c : SpecialLinearGroup (Fin 3) F) = 1 := by
    rw [← pow_three', hc3]
  rw [hc3', slCoeOne] at h
  show blkMat (c : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1
  rw [pow_succ, pow_two, ← h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkMat]

theorem eq_zero_or_eq_one_of_card_two [Finite F] (hF : Nat.card F = 2) (a : F) :
    a = 0 ∨ a = 1 := by
  have := Fintype.ofFinite F
  have h2 : a ^ 2 = a := by
    have := FiniteField.pow_card a
    rwa [← Nat.card_eq_fintype_card, hF] at this
  have : a * (a - 1) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp this with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

theorem det_ne_zero_of_card_two [Finite F] (hF : Nat.card F = 2) {a b p q : F}
    (hab : a ≠ 0 ∨ b ≠ 0) (hpq : p ≠ 0 ∨ q ≠ 0) (hne : ¬ (p = a ∧ q = b)) :
    a * q - b * p ≠ 0 := by
  rcases eq_zero_or_eq_one_of_card_two hF a with h1 | h1 <;>
  rcases eq_zero_or_eq_one_of_card_two hF b with h2 | h2 <;>
  rcases eq_zero_or_eq_one_of_card_two hF p with h3 | h3 <;>
  rcases eq_zero_or_eq_one_of_card_two hF q with h4 | h4 <;>
  simp_all

theorem irredModE0_of_card_two [Finite F] (hF : Nat.card F = 2)
    {Y : Subgroup (SpecialLinearGroup (Fin 3) F)} (hYv : Y ≤ vstab F) (huY : urad F ≤ Y)
    {c : SpecialLinearGroup (Fin 3) F} (hcY : c ∈ Y) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    IrredModE0 F Y := by
  have := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 ^ 1 := by rw [← Nat.card_eq_fintype_card, hF, pow_one]
  have : CharP F 2 := charP_of_card_eq_prime_pow hF'
  intro S hS u hu hu'
  have hsmul : ∀ (a : F), ∀ w ∈ S, a • w ∈ S := by
    intro a w hw
    rcases eq_zero_or_eq_one_of_card_two hF a with rfl | rfl
    · rw [zero_smul]
      exact S.zero_mem
    · rw [one_smul]
      exact hw
  have hcv : c ∈ vstab F := hYv hcY
  have he0 : (Pi.single 0 1 : Fin 3 → F) ∈ S := by
    obtain ⟨a, ha0, hau⟩ : ∃ (a : Fin 3 → F) (ha0 : a 0 = 0), a ⬝ᵥ u = 1 := by
      rcases hu' with h1 | h2
      · exact ⟨Pi.single 1 (u 1)⁻¹, by simp, by simp [single_dotProduct, h1]⟩
      · exact ⟨Pi.single 2 (u 2)⁻¹, by simp, by simp [single_dotProduct, h2]⟩
    have h := S.sub_mem (hS _ (huY (uelt_mem a ha0)) u hu) hu
    rwa [coe_rowSL, rowMat_zero_mulVec, hau, one_smul, add_sub_cancel_left] at h
  have hcu := not_mem_urad_of_pow_three hc3 hc1
  set C := blkSL hcv with hC
  have hC1 : C ≠ 1 := blkSL_ne_one_of_not_mem_urad hcv hcu
  have hC3 : C ^ 3 = 1 := blkSL_pow_three hcv hc3
  have hcoords := mulVec_one_two_of_mem_vstab hcv u
  set x : Fin 2 → F := ![u 1, u 2] with hx
  set y : Fin 2 → F := ![((c : Matrix (Fin 3) (Fin 3) F) *ᵥ u) 1,
    ((c : Matrix (Fin 3) (Fin 3) F) *ᵥ u) 2] with hy
  have hx0 : x ≠ 0 := by
    intro h
    rcases hu' with h1 | h2
    · exact h1 (by simpa [hx] using congrFun h 0)
    · exact h2 (by simpa [hx] using congrFun h 1)
  have hCx : (C : Matrix (Fin 2) (Fin 2) F) *ᵥ x = y := by
    ext i
    fin_cases i
    · show ((C : Matrix (Fin 2) (Fin 2) F) *ᵥ x) 0 = ((c : Matrix (Fin 3) (Fin 3) F) *ᵥ u) 1
      rw [hcoords.1]
      simp [hC, blkSL, blkMat, hx, mulVec, dotProduct, Fin.sum_univ_two]
    · show ((C : Matrix (Fin 2) (Fin 2) F) *ᵥ x) 1 = ((c : Matrix (Fin 3) (Fin 3) F) *ᵥ u) 2
      rw [hcoords.2]
      simp [hC, blkSL, blkMat, hx, mulVec, dotProduct, Fin.sum_univ_two]
  have hy0 : y ≠ 0 := by
    intro h
    apply hx0
    have := congrArg (fun z => ((C⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      *ᵥ z) hCx
    simp only [h, mulVec_zero, mulVec_mulVec] at this
    rwa [show ((C⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (C : Matrix (Fin 2) (Fin 2) F) = 1 from congrArg Subtype.val (inv_mul_cancel C),
      one_mulVec] at this
  have hyx : y ≠ x := fun h => hC1 (sl2_eq_one_of_fix hC3 hx0 (hCx.trans h))
  set a := u 1 with ha
  set b := u 2 with hb
  set p := ((c : Matrix (Fin 3) (Fin 3) F) *ᵥ u) 1 with hp
  set q := ((c : Matrix (Fin 3) (Fin 3) F) *ᵥ u) 2 with hq
  have hpq : p ≠ 0 ∨ q ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hy0
    ext i
    fin_cases i <;> simp [hy, hcon.1, hcon.2]
  have hne : ¬ (p = a ∧ q = b) := by
    rintro ⟨h1, h2⟩
    apply hyx
    ext i
    fin_cases i <;> simp [hx, hy, h1, h2]
  have hD0 : a * q - b * p ≠ 0 := det_ne_zero_of_card_two hF hu' hpq hne
  have hcuS : (c : Matrix (Fin 3) (Fin 3) F) *ᵥ u ∈ S := hS c hcY u hu
  set D := a * q - b * p with hD
  set v₁ := (q * D⁻¹) • u - (b * D⁻¹) • ((c : Matrix (Fin 3) (Fin 3) F) *ᵥ u) with hv₁
  set v₂ := (a * D⁻¹) • ((c : Matrix (Fin 3) (Fin 3) F) *ᵥ u) - (p * D⁻¹) • u with hv₂
  have hv₁S : v₁ ∈ S := S.sub_mem (hsmul _ _ hu) (hsmul _ _ hcuS)
  have hv₂S : v₂ ∈ S := S.sub_mem (hsmul _ _ hcuS) (hsmul _ _ hu)
  have hv₁1 : v₁ 1 = 1 := by
    simp only [hv₁, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← ha, ← hp]
    field_simp
    ring
  have hv₁2 : v₁ 2 = 0 := by
    simp only [hv₁, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← hb, ← hq]
    ring
  have hv₂1 : v₂ 1 = 0 := by
    simp only [hv₂, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← ha, ← hp]
    ring
  have hv₂2 : v₂ 2 = 1 := by
    simp only [hv₂, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← hb, ← hq]
    field_simp
    ring
  rw [eq_top_iff]
  intro w _
  have hw : w = w 1 • v₁ + w 2 • v₂ + (w 0 - w 1 * v₁ 0 - w 2 * v₂ 0) •
      (Pi.single 0 1 : Fin 3 → F) := by
    ext i
    fin_cases i <;> simp [hv₁1, hv₁2, hv₂1, hv₂2]
  rw [hw]
  exact S.add_mem (S.add_mem (hsmul _ _ hv₁S) (hsmul _ _ hv₂S)) (hsmul _ _ he0)

end CFSG.RankThree.PartTwo.Sec20.Res2
