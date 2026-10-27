module

public import CFSG.Quasithin.H13.L32AC44c

public section

namespace CFSG.Quasithin.H13.L32A.C.SL3N

open Matrix CFSG.QuasithinUnique.Setup.X7a
open scoped MatrixGroups

variable {F : Type} [Field F] [CharP F 2]

abbrev borel (F : Type) [Field F] [CharP F 2] : Subgroup SL(3, F) :=
  Subgroup.normalizer (upperUni F : Set SL(3, F))

theorem e10 {g : SL(3, F)} (hg : g ∈ borel F) : (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 :=
  (entries_of_mem_normalizer hg).1

theorem e20 {g : SL(3, F)} (hg : g ∈ borel F) : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 :=
  (entries_of_mem_normalizer hg).2.1

theorem e21 {g : SL(3, F)} (hg : g ∈ borel F) : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 :=
  (entries_of_mem_normalizer hg).2.2

theorem mul00 {g h : SL(3, F)} (hh : h ∈ borel F) :
    ((g * h : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 0 0 =
      (g : Matrix (Fin 3) (Fin 3) F) 0 0 * (h : Matrix (Fin 3) (Fin 3) F) 0 0 := by
  rw [← coe_mul_coe, Matrix.mul_apply, Fin.sum_univ_three, e10 hh, e20 hh]
  ring

theorem mul22 {g h : SL(3, F)} (hg : g ∈ borel F) :
    ((g * h : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 2 2 =
      (g : Matrix (Fin 3) (Fin 3) F) 2 2 * (h : Matrix (Fin 3) (Fin 3) F) 2 2 := by
  rw [← coe_mul_coe, Matrix.mul_apply, Fin.sum_univ_three, e20 hg, e21 hg]
  ring

theorem inv00 {g : SL(3, F)} (hg : g ∈ borel F) :
    ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 0 0 = ((g : Matrix (Fin 3) (Fin 3) F) 0 0)⁻¹ := by
  have h := mul00 (g := g⁻¹) hg
  have h1 : ((1 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 := Matrix.one_apply_eq 0
  rw [inv_mul_cancel, h1] at h
  exact (eq_inv_of_mul_eq_one_left h.symm)

theorem inv22 {g : SL(3, F)} (hg : g ∈ borel F) :
    ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 2 2 = ((g : Matrix (Fin 3) (Fin 3) F) 2 2)⁻¹ := by
  have h := mul22 (h := g) (inv_mem hg)
  have h1 : ((1 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := Matrix.one_apply_eq 2
  rw [inv_mul_cancel, h1] at h
  exact (eq_inv_of_mul_eq_one_left h.symm)

theorem upperUni_le_borel : upperUni F ≤ borel F := Subgroup.le_normalizer

theorem upperUni_00 {u : SL(3, F)} (hu : u ∈ upperUni F) :
    (u : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 := by
  obtain ⟨x, y, z, rfl⟩ := mem_upperUni.mp hu
  simp [up3_coe, upMat]

theorem upperUni_22 {u : SL(3, F)} (hu : u ∈ upperUni F) :
    (u : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by
  obtain ⟨x, y, z, rfl⟩ := mem_upperUni.mp hu
  simp [up3_coe, upMat]

theorem mem_upperUni_of {g : SL(3, F)} (hg : g ∈ borel F)
    (h0 : (g : Matrix (Fin 3) (Fin 3) F) 0 0 = 1) (h2 : (g : Matrix (Fin 3) (Fin 3) F) 2 2 = 1) :
    g ∈ upperUni F := by
  have h1 : (g : Matrix (Fin 3) (Fin 3) F) 1 1 = 1 := by
    have := diag_mul_eq_one (e10 hg) (e20 hg) (e21 hg)
    rwa [h0, h2, one_mul, mul_one] at this
  refine mem_upperUni.mpr ⟨(g : Matrix (Fin 3) (Fin 3) F) 1 2, (g : Matrix (Fin 3) (Fin 3) F) 0 2,
    (g : Matrix (Fin 3) (Fin 3) F) 0 1, Subtype.ext ?_⟩
  rw [up3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upMat, h0, h1, h2, e10 hg, e20 hg, e21 hg]

theorem exists_preimage_upperUni [Finite F] (α : SL(3, F) ≃* SL(3, F))
    (hαU : ∀ u ∈ upperUni F, α u ∈ upperUni F) {u : SL(3, F)} (hu : u ∈ upperUni F) :
    ∃ u' ∈ upperUni F, α u' = u := by
  have hle : (upperUni F).map α.toMonoidHom ≤ upperUni F := by
    rintro _ ⟨v, hv, rfl⟩
    exact hαU v hv
  have hc : Nat.card ↥((upperUni F).map α.toMonoidHom) = Nat.card ↥(upperUni F) :=
    Subgroup.card_map_of_injective α.injective
  have heq := Subgroup.eq_of_le_of_card_ge hle hc.ge
  rw [← heq] at hu
  obtain ⟨u', hu', rfl⟩ := hu
  exact ⟨u', hu', rfl⟩

theorem tau_up3 (x y z : F) :
    ((tauSL F (up3 x y z) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = u3Mat z (y + z * x) x := by
  rw [tauSL_coe, trInvMat, up3_inv, up3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upMat, u3Mat]

omit [CharP F 2] in
theorem sq_add_add_one {x : F} [Fintype F] (hF : Fintype.card F = 2 ^ 2) (h0 : x ≠ 0)
    (h1 : x ≠ 1) : x ^ 2 + x + 1 = 0 := by
  have h3 : x ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one x h0
    rwa [hF] at this
  have h : (x - 1) * (x ^ 2 + x + 1) = 0 := by
    linear_combination h3
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd (sub_eq_zero.mp h') h1
  · exact h'

omit [CharP F 2] in
theorem eq_or_eq_sq {x r : F} (hx : x ^ 2 + x + 1 = 0) (hr : r ^ 2 + r + 1 = 0) :
    r = x ∨ r = x ^ 2 := by
  have h : (r - x) * (r - x ^ 2) = 0 := by
    linear_combination hr - r * hx + (x - 1) * hx
  rcases mul_eq_zero.mp h with h' | h'
  · exact Or.inl (sub_eq_zero.mp h')
  · exact Or.inr (sub_eq_zero.mp h')

omit [CharP F 2] in
theorem pow_three_eq_one [Fintype F] (hF : Fintype.card F = 2 ^ 2) {x : F} (h0 : x ≠ 0) :
    x ^ 3 = 1 := by
  have := FiniteField.pow_card_sub_one_eq_one x h0
  rwa [hF] at this

omit [CharP F 2] in
theorem eq_one_of_inv_eq [Fintype F] (hF : Fintype.card F = 2 ^ 2) {x : F} (h0 : x ≠ 0)
    (h : x⁻¹ = x) : x = 1 := by
  have h3 := pow_three_eq_one hF h0
  have h2 : x * x = 1 := by
    calc x * x = x * x⁻¹ := by rw [h]
      _ = 1 := mul_inv_cancel₀ h0
  calc x = x * (x * x) := by rw [h2, mul_one]
    _ = x ^ 3 := by ring
    _ = 1 := h3

omit [CharP F 2] in
theorem mu_cases [Fintype F] (hF : Fintype.card F = 2 ^ 2) {μ : F → F} (hμ1 : μ 1 = 1)
    (hμadd : ∀ a b, μ (a + b) = μ a + μ b) (hμmul : ∀ a b, μ (a * b) = μ a * μ b) :
    (∀ x, x ≠ 0 → μ x = x) ∨ (∀ x, x ≠ 0 → μ x = x⁻¹) := by
  have hμ0 : μ 0 = 0 := by
    have h := hμadd 0 0
    rw [add_zero] at h
    exact (add_eq_left.mp h.symm)
  have hroot : ∀ x, x ≠ 0 → x ≠ 1 → μ x = x ∨ μ x = x ^ 2 := by
    intro x h0 h1
    have hx := sq_add_add_one hF h0 h1
    have hμx : μ x ^ 2 + μ x + 1 = 0 := by
      have := congrArg μ hx
      rw [hμ0, hμadd, hμadd, hμ1, pow_two, hμmul, ← pow_two] at this
      exact this
    exact eq_or_eq_sq hx hμx
  have hsq : ∀ x : F, x ≠ 0 → x ^ 2 = x⁻¹ := by
    intro x h0
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, pow_three_eq_one hF h0])
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨a, ha0, ha⟩, ⟨b, hb0, hb⟩⟩ := hcon
  have ha1 : a ≠ 1 := fun h => ha (by rw [h, hμ1])
  have hb1 : b ≠ 1 := fun h => hb (by rw [h, hμ1, inv_one])
  have hμa : μ a = a ^ 2 := (hroot a ha0 ha1).resolve_left ha
  have hμb : μ b = b := (hroot b hb0 hb1).resolve_right (by rwa [hsq b hb0])
  have ha3 := pow_three_eq_one hF ha0
  rcases eq_or_eq_sq (sq_add_add_one hF ha0 ha1) (sq_add_add_one hF hb0 hb1) with rfl | rfl
  · apply ha1
    have h : b = b ^ 2 := hμb.symm.trans hμa
    have h2 : b * (b - 1) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp h2 with h' | h'
    · exact absurd h' ha0
    · exact sub_eq_zero.mp h'
  · apply ha1
    have h4 : a = a ^ 2 := by
      calc a = a * a ^ 3 := by rw [ha3, mul_one]
        _ = a ^ 2 * a ^ 2 := by ring
        _ = μ a * μ a := by rw [hμa]
        _ = μ (a * a) := (hμmul a a).symm
        _ = μ (a ^ 2) := by rw [pow_two]
        _ = a ^ 2 := hμb
    have h2 : a * (a - 1) = 0 := by linear_combination -h4
    rcases mul_eq_zero.mp h2 with h' | h'
    · exact absurd h' ha0
    · exact sub_eq_zero.mp h'

omit [CharP F 2] in
theorem diag00_ne_zero {g : SL(3, F)} (h10 : (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0)
    (h20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) (h21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) :
    (g : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := by
  intro h
  have := diag_mul_eq_one h10 h20 h21
  rw [h, zero_mul, zero_mul] at this
  exact zero_ne_one this

omit [CharP F 2] in
theorem diag22_ne_zero {g : SL(3, F)} (h10 : (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0)
    (h20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) (h21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) :
    (g : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ 0 := by
  intro h
  have := diag_mul_eq_one h10 h20 h21
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem borel_mulVec_e0 {g : SL(3, F)} (hg : g ∈ borel F) :
    (g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 =
      (g : Matrix (Fin 3) (Fin 3) F) 0 0 • Pi.single 0 1 := by
  funext k
  fin_cases k <;> simp [e10 hg, e20 hg]

theorem borel_fix [Fintype F] (hF : Fintype.card F = 2 ^ 2) (α : SL(3, F) ≃* SL(3, F))
    (hαU : ∀ u ∈ upperUni F, α u ∈ upperUni F) {y : SL(3, F)} (hyB : y ∈ borel F)
    (hyU : y ∉ upperUni F) (hαy : α y * y ∈ upperUni F) {d : SL(3, F)} (hdB : d ∈ borel F)
    (hdU : d ∉ upperUni F) (hαd : α d * d⁻¹ ∈ upperUni F) :
    (d : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 1 := by
  classical
  obtain ⟨ψ, hψ, E, μ, hE, hEμ⟩ := exists_semilinear_of_aut (le_refl 2) hF α
  have ey : α y = (α y * y) * y⁻¹ := by group
  have ed : α d = (α d * d⁻¹) * d := by group
  have hαyB : α y ∈ borel F := by
    rw [ey]
    exact mul_mem (upperUni_le_borel hαy) (inv_mem hyB)
  have hαdB : α d ∈ borel F := by
    rw [ed]
    exact mul_mem (upperUni_le_borel hαd) hdB
  have hy0 : (α y : Matrix (Fin 3) (Fin 3) F) 0 0 = ((y : Matrix (Fin 3) (Fin 3) F) 0 0)⁻¹ := by
    rw [ey, mul00 (inv_mem hyB), upperUni_00 hαy, one_mul, inv00 hyB]
  have hy2 : (α y : Matrix (Fin 3) (Fin 3) F) 2 2 = ((y : Matrix (Fin 3) (Fin 3) F) 2 2)⁻¹ := by
    rw [ey, mul22 (upperUni_le_borel hαy), upperUni_22 hαy, one_mul, inv22 hyB]
  have hd0 : (α d : Matrix (Fin 3) (Fin 3) F) 0 0 = (d : Matrix (Fin 3) (Fin 3) F) 0 0 := by
    rw [ed, mul00 hdB, upperUni_00 hαd, one_mul]
  have hd2 : (α d : Matrix (Fin 3) (Fin 3) F) 2 2 = (d : Matrix (Fin 3) (Fin 3) F) 2 2 := by
    rw [ed, mul22 (upperUni_le_borel hαd), upperUni_22 hαd, one_mul]
  have he0 : (Pi.single 0 1 : Fin 3 → F) ≠ 0 := fun h => by simpa using congrFun h 0
  have hE0 : E (Pi.single 0 1) ≠ 0 := fun h =>
    he0 (E.injective (h.trans (map_zero E).symm))
  have hcancel : ∀ m m' : F, m • E (Pi.single 0 1) = m' • E (Pi.single 0 1) → m = m' :=
    fun m m' h => smul_left_injective F hE0 h
  have hμ1 : μ 1 = 1 := by
    have h := hEμ 1 (Pi.single 0 1)
    rw [one_smul] at h
    exact hcancel _ _ ((one_smul F _).trans h).symm
  have hμadd : ∀ a b, μ (a + b) = μ a + μ b := by
    intro a b
    refine hcancel _ _ ?_
    rw [← hEμ, add_smul, map_add, hEμ, hEμ, add_smul]
  have hμmul : ∀ a b, μ (a * b) = μ a * μ b := by
    intro a b
    refine hcancel _ _ ?_
    rw [← hEμ, mul_smul, hEμ, hEμ, mul_smul]
  have hfixU : ∀ u ∈ upperUni F, ((ψ u : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      E (Pi.single 0 1) = E (Pi.single 0 1) := by
    intro u hu
    rw [← hE, upperUni_mulVec_e0 (hαU u hu)]
  have hchar0 : ∀ g ∈ borel F, α g ∈ borel F →
      μ ((α g : Matrix (Fin 3) (Fin 3) F) 0 0) • E (Pi.single 0 1) =
        ((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ E (Pi.single 0 1) := by
    intro g hg hαg
    rw [← hEμ, ← borel_mulVec_e0 hαg, hE]
  have hy00 := diag00_ne_zero (e10 hyB) (e20 hyB) (e21 hyB)
  have hy22 := diag22_ne_zero (e10 hyB) (e20 hyB) (e21 hyB)
  have hd22 := diag22_ne_zero (e10 hdB) (e20 hdB) (e21 hdB)
  rcases hψ with rfl | rfl
  ·
    obtain ⟨h1, h2⟩ := fix_upperUni (fun u hu => hfixU u hu)
    have hEe0 : E (Pi.single 0 1) = E (Pi.single 0 1) 0 • Pi.single 0 1 := by
      funext k
      fin_cases k <;> simp [h1, h2]
    have hc0 : ∀ g ∈ borel F, α g ∈ borel F →
        μ ((α g : Matrix (Fin 3) (Fin 3) F) 0 0) = (g : Matrix (Fin 3) (Fin 3) F) 0 0 := by
      intro g hg hαg
      apply hcancel
      rw [hchar0 g hg hαg, MonoidHom.id_apply, hEe0, mulVec_smul, borel_mulVec_e0 hg,
        smul_comm]
    have hdecomp : ∀ w : Fin 3 → F, w 2 = 0 → w =
        ((up3 (w 1) (w 0) 0 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 2 1 -
          Pi.single 2 1 := by
      intro w hw
      rw [up3_coe, upMat_mulVec]
      funext k
      fin_cases k <;> simp [hw]
    have hEH : ∀ w : Fin 3 → F, w 2 = 0 → (E w) 2 = 0 := by
      intro w hw
      obtain ⟨u', hu', hu'e⟩ := exists_preimage_upperUni α hαU (u := up3 (w 1) (w 0) 0)
        (mem_upperUni.mpr ⟨_, _, _, rfl⟩)
      rw [hdecomp w hw, ← hu'e, map_sub, hE, Pi.sub_apply, MonoidHom.id_apply,
        upperUni_mulVec_two hu', sub_self]
    have hEH' : ∀ w : Fin 3 → F, w 2 = 0 → (E.symm w) 2 = 0 := by
      intro w hw
      have hu : up3 (w 1) (w 0) 0 ∈ upperUni F := mem_upperUni.mpr ⟨_, _, _, rfl⟩
      have h1 : E.symm (((up3 (w 1) (w 0) 0 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ
          Pi.single 2 1) = ((α (up3 (w 1) (w 0) 0) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ
            E.symm (Pi.single 2 1) := by
        apply E.injective
        rw [AddEquiv.apply_symm_apply, hE, AddEquiv.apply_symm_apply, MonoidHom.id_apply]
      rw [hdecomp w hw, map_sub, h1, Pi.sub_apply, upperUni_mulVec_two (hαU _ hu), sub_self]
    have hE2 : (E (Pi.single 2 1)) 2 ≠ 0 := by
      intro h
      have := hEH' _ h
      rw [AddEquiv.symm_apply_apply] at this
      simp at this
    have hc2 : ∀ g ∈ borel F, α g ∈ borel F →
        μ ((α g : Matrix (Fin 3) (Fin 3) F) 2 2) = (g : Matrix (Fin 3) (Fin 3) F) 2 2 := by
      intro g hg hαg
      set w := (α g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 2 1 -
        (α g : Matrix (Fin 3) (Fin 3) F) 2 2 • Pi.single 2 1 with hw
      have hw2 : w 2 = 0 := by simp [hw]
      have hsplit : (α g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 2 1 =
          (α g : Matrix (Fin 3) (Fin 3) F) 2 2 • Pi.single 2 1 + w := by
        rw [hw]
        abel
      have key := hE g (Pi.single 2 1)
      rw [hsplit, map_add, hEμ, MonoidHom.id_apply] at key
      have k2 := congrFun key 2
      rw [Pi.add_apply, hEH w hw2, add_zero, Pi.smul_apply, smul_eq_mul] at k2
      have hg2 : ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ E (Pi.single 2 1)) 2 =
          (g : Matrix (Fin 3) (Fin 3) F) 2 2 * E (Pi.single 2 1) 2 := by
        simp [mulVec, dotProduct, Fin.sum_univ_three, e20 hg, e21 hg]
      rw [hg2] at k2
      exact mul_right_cancel₀ hE2 k2
    rcases mu_cases hF hμ1 hμadd hμmul with hid | hinv
    ·
      exfalso
      apply hyU
      have h0 := hc0 y hyB hαyB
      rw [hy0, hid _ (inv_ne_zero hy00)] at h0
      have h2 := hc2 y hyB hαyB
      rw [hy2, hid _ (inv_ne_zero hy22)] at h2
      exact mem_upperUni_of hyB (eq_one_of_inv_eq hF hy00 h0) (eq_one_of_inv_eq hF hy22 h2)
    ·
      intro hd1
      apply hdU
      have h2 := hc2 d hdB hαdB
      rw [hd2, hinv _ hd22] at h2
      exact mem_upperUni_of hdB hd1 (eq_one_of_inv_eq hF hd22 h2)
  ·
    have hv0 : E (Pi.single 0 1) 0 = 0 := by
      have h := congrFun (hfixU (up3 0 0 1) (mem_upperUni.mpr ⟨0, 0, 1, rfl⟩)) 1
      rw [tau_up3, u3Mat_mulVec] at h
      simpa using h
    have hv1 : E (Pi.single 0 1) 1 = 0 := by
      have h := congrFun (hfixU (up3 1 0 0) (mem_upperUni.mpr ⟨1, 0, 0, rfl⟩)) 2
      rw [tau_up3, u3Mat_mulVec] at h
      simpa [hv0] using h
    have hEe0 : E (Pi.single 0 1) = E (Pi.single 0 1) 2 • Pi.single 2 1 := by
      funext k
      fin_cases k <;> simp [hv0, hv1]
    have hact : ((tauSL F d : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ E (Pi.single 0 1) =
        ((d : Matrix (Fin 3) (Fin 3) F) 2 2)⁻¹ • E (Pi.single 0 1) := by
      rw [hEe0, mulVec_smul, smul_comm, tauSL_coe, trInvMat]
      congr 1
      funext k
      rw [mulVec_single_one]
      fin_cases k
      · show ((d⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 2 0 =
          (((d : Matrix (Fin 3) (Fin 3) F) 2 2)⁻¹ • (Pi.single 2 1 : Fin 3 → F)) 0
        rw [e20 (inv_mem hdB)]
        simp
      · show ((d⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 2 1 =
          (((d : Matrix (Fin 3) (Fin 3) F) 2 2)⁻¹ • (Pi.single 2 1 : Fin 3 → F)) 1
        rw [e21 (inv_mem hdB)]
        simp
      · show ((d⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 2 2 =
          (((d : Matrix (Fin 3) (Fin 3) F) 2 2)⁻¹ • (Pi.single 2 1 : Fin 3 → F)) 2
        rw [inv22 hdB]
        simp
    intro hd1
    apply hdU
    have h := hchar0 d hdB hαdB
    rw [hact, hd0, hd1, hμ1] at h
    have h' : ((d : Matrix (Fin 3) (Fin 3) F) 2 2)⁻¹ = 1 := hcancel _ _ h.symm
    exact mem_upperUni_of hdB hd1 (inv_eq_one.mp h')

end CFSG.Quasithin.H13.L32A.C.SL3N
