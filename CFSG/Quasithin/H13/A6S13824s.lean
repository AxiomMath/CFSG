module

public import CFSG.Quasithin.H13.A6S13824q

public section

namespace CFSG.Quasithin.H13.A6.S7C

open Equiv

@[expose] def certC : List (ℕ × ℕ × ℕ) :=
  [(0, 1754760, 1718920), (0, 1754760, 1747144), (0, 1754760, 1682184), (0, 1754760, 1645336),
    (0, 1754760, 1641241), (1, 1754760, 1718920), (1, 1754760, 1682016), (1, 1751176, 1714776),
    (1, 1751176, 1710744), (1, 1751176, 1645336), (1, 1718920, 1754760), (1, 1457288, 1747032),
    (1, 1457288, 1714776), (1, 1747144, 1718864), (1, 1747144, 1457232), (1, 1714888, 1747144),
    (1, 1714888, 1457232)]

@[expose] def certD : List (ℕ × ℕ × ℕ) :=
  [(0, 1754760, 1714888), (0, 1754760, 1710800), (0, 1754760, 1706705), (1, 1754760, 1521800),
    (1, 1754760, 1260168), (1, 1751176, 1525384), (1, 1751176, 1260168), (1, 1718920, 1754760),
    (1, 1718920, 1525384), (1, 1718920, 1521800)]

theorem certC_ok : (certC.all fun e => valid e.2.1 && valid e.2.2) = true ∧
    xorL (certC.map (entryKeys keyC c012 c021 v1c v2c)) = [keyC idc] := by
  constructor <;> decide +kernel

theorem certD_ok : (certD.all fun e => valid e.2.1 && valid e.2.2) = true ∧
    xorL (certD.map (entryKeys keyD c456 c465 v1c v2c)) = [keyD idc] := by
  constructor <;> decide +kernel

section CaseS

variable {M : Type*} [CommGroup M] {Φ : Perm (Fin 7) →* MulAut M} {m₀ : M}

theorem eq_one_of_C (hsq : ∀ x : M, x * x = 1)
    (hC : ∀ σ : Perm (Fin 7), inC (cd σ) = true → Φ σ m₀ = m₀)
    (hrel : m₀ * Φ (dec c012) m₀ * Φ (dec c021) m₀ = 1) {E : Set (Perm (Fin 7))}
    (hq : IndQuad.QuadOn Φ E) (hv1 : dec v1c ∈ E) (hv2 : dec v2c ∈ E) : m₀ = 1 := by
  have hμ := mu_eq_val (X := C7) (fun t ht => hC t (mem_C7_iff.mp ht))
    (fun σ τ h => keyC_sound h)
  have h := cert_sound hsq hμ (by decide : valid c012 = true) (by decide : valid c021 = true)
    hrel hq hv1 hv2 (by decide) (by decide) certC certC_ok.1
  rw [certC_ok.2] at h
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  rw [← h, ← cd_one, ← hμ, map_one, MulAut.one_apply]

theorem eq_one_of_D (hsq : ∀ x : M, x * x = 1)
    (hD : ∀ σ : Perm (Fin 7), inD (cd σ) = true → Φ σ m₀ = m₀)
    (hrel : m₀ * Φ (dec c456) m₀ * Φ (dec c465) m₀ = 1) {E : Set (Perm (Fin 7))}
    (hq : IndQuad.QuadOn Φ E) (hv1 : dec v1c ∈ E) (hv2 : dec v2c ∈ E) : m₀ = 1 := by
  have hμ := mu_eq_val (X := D7) (fun t ht => hD t (mem_D7_iff.mp ht))
    (fun σ τ h => keyD_sound h)
  have h := cert_sound hsq hμ (by decide : valid c456 = true) (by decide : valid c465 = true)
    hrel hq hv1 hv2 (by decide) (by decide) certD certD_ok.1
  rw [certD_ok.2] at h
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  rw [← h, ← cd_one, ← hμ, map_one, MulAut.one_apply]

@[expose] def v4OK (x y : ℕ) : Bool :=
  x == idc || y == idc || x == y ||
    ([v1c, v2c].all fun v => v == x || v == y || v == cm x y)

theorem v4OK_all : (V4L.all fun x => V4L.all fun y => v4OK x y) = true := by decide +kernel

theorem mem_of_V4 {E : Subgroup (Perm (Fin 7))} (h4 : 4 ≤ Nat.card E) (hE : ∀ x ∈ E, x ∈ V4) :
    dec v1c ∈ E ∧ dec v2c ∈ E := by
  obtain ⟨a, haE, ha1, -⟩ := exists_mem_ne_ne h4 1 1
  obtain ⟨a', ha'E, ha'1, ha'a⟩ := exists_mem_ne_ne h4 1 a
  have haL := mem_V4_iff.mp (hE a haE)
  have ha'L := mem_V4_iff.mp (hE a' ha'E)
  have hL := listsOK_all a
  have hL' := listsOK_all a'
  simp only [listsOK, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.contains_iff_mem] at hL hL'
  have hm := List.all_eq_true.mp (List.all_eq_true.mp v4OK_all _
    (hL.2.resolve_left (by rw [haL]; simp))) _ (hL'.2.resolve_left (by rw [ha'L]; simp))
  have hc1 : cd a ≠ idc := fun h => ha1 (cd_injective (h.trans cd_one.symm))
  have hc1' : cd a' ≠ idc := fun h => ha'1 (cd_injective (h.trans cd_one.symm))
  have hcne : cd a ≠ cd a' := fun h => ha'a (cd_injective h).symm
  simp only [v4OK, Bool.or_eq_true, beq_iff_eq, hc1, hc1', hcne, false_or, List.all_eq_true,
    List.mem_cons, List.not_mem_nil, or_false] at hm
  have hmem : ∀ v, ((v = cd a ∨ v = cd a') ∨ v = cm (cd a) (cd a')) → dec v ∈ E := by
    rintro v ((rfl | rfl) | rfl)
    · rw [dec_cd a (valid_cd a)]
      exact haE
    · rw [dec_cd a' (valid_cd a')]
      exact ha'E
    · rw [← cd_mul, dec_cd _ (valid_cd _)]
      exact E.mul_mem haE ha'E
  exact ⟨hmem _ (hm v1c (Or.inl rfl)), hmem _ (hm v2c (Or.inr rfl))⟩

theorem eq_one_case_hat (hsq : ∀ x : M, x * x = 1)
    (hT : ∀ t : Perm (Fin 7), inT0 (cd t) = true → Φ t m₀ = m₀) {c c0 : Perm (Fin 7)}
    (hc43 : c ∈ S43) (hcube : cubeConds (cd c) = true) (h1 : Φ c m₀ ≠ m₀)
    (h2 : Φ (c * c) m₀ ≠ m₀) (h12 : Φ c m₀ ≠ Φ (c * c) m₀) (hcc : m₀ * Φ c m₀ = Φ (c * c) m₀)
    (hc03 : c0 ^ 3 = 1) (hc01 : c0 ≠ 1)
    (htn : ∀ t ∈ [t1c, t2c, t3c], c0 * c0 * (dec t * c0 * dec t) ∈ T0 ∨
      c0 * (dec t * c0 * dec t) ∈ T0)
    (hc0fix : Φ c0 m₀ = m₀) (hcomm : c0 * c * c0⁻¹ * c⁻¹ ∈ T0) (hcub1 : (c0 * c) ^ 3 ∈ T0)
    (hcub2 : (c0 * (c * c)) ^ 3 ∈ T0) {E : Subgroup (Perm (Fin 7))}
    (hq : IndQuad.QuadOn Φ (E : Set (Perm (Fin 7)))) (h4 : 4 ≤ Nat.card E)
    (hcore : ∀ x ∈ E, x ∈ T0 ∧ c0 * x * c0⁻¹ ∈ T0 ∧ c0⁻¹ * x * c0 ∈ T0 ∧ c * x * c⁻¹ ∈ T0 ∧
      c⁻¹ * x * c ∈ T0) : m₀ = 1 := by
  have hT' : ∀ t ∈ T0, Φ t m₀ = m₀ := fun t ht => hT t (mem_T0_iff.mp ht)
  have hfixL : ∀ {a b : Perm (Fin 7)}, Φ a m₀ = m₀ → Φ (a⁻¹ * b) m₀ = m₀ → Φ b m₀ = m₀ :=
    fun {a b} ha hab => by
      calc Φ b m₀ = Φ a (Φ (a⁻¹ * b) m₀) := by
            rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel_left]
        _ = m₀ := by rw [hab, ha]
  have hcov : ∀ {σ : Perm (Fin 7)}, (σ ∈ T0 ∨ c0⁻¹ * σ ∈ T0 ∨ c0⁻¹ * (c0⁻¹ * σ) ∈ T0) →
      Φ σ m₀ = m₀ := fun {σ} h => by
    rcases h with h | h | h
    · exact hT' σ h
    · exact hfixL hc0fix (hT' _ h)
    · exact hfixL hc0fix (hfixL hc0fix (hT' _ h))
  have hcT : c ∉ T0 := fun h => h1 (hT' c h)
  have hc0inv : Φ c0⁻¹ m₀ = m₀ := by
    conv_lhs => rw [← hc0fix]
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
  have hc0c : c0 * c ∉ T0 := fun h => h1 (hfixL hc0inv (by rw [inv_inv]; exact hT' _ h))
  have hc00c : c0 * c0 * c ∉ T0 := fun h => h1 (hfixL hc0inv (by
    rw [inv_inv]
    exact hfixL hc0inv (by rw [inv_inv, ← mul_assoc]; exact hT' _ h)))
  have hL := mem_L18 hc03 hc01 htn
  obtain ⟨hCD, hcoreV⟩ := hat_shape hL hc43 hcube hcomm hcT hc0c hc00c hcub1 hcub2
  have hEV : ∀ x ∈ E, x ∈ V4 := fun x hx => by
    obtain ⟨h0, h1', h2', h3', h4'⟩ := hcore x hx
    exact hcoreV x h0 h1' h2' h3' h4'
  obtain ⟨hv1, hv2⟩ := mem_of_V4 h4 hEV
  rcases hCD with hC | hD
  · have hCfix : ∀ σ : Perm (Fin 7), inC (cd σ) = true → Φ σ m₀ = m₀ := fun σ hσ =>
      hcov (cover_C hL hC (mem_C7_iff.mpr hσ))
    have hrel := rel_of_cos hsq (X := C7) (fun t ht => hCfix t (mem_C7_iff.mp ht))
      (cosets_S43_C hc43) (cosets_S43_C (S43.mul_mem hc43 hc43)) h1 h2 h12 hcc
    exact eq_one_of_C hsq hCfix hrel.1 hq hv1 hv2
  · have hDfix : ∀ σ : Perm (Fin 7), inD (cd σ) = true → Φ σ m₀ = m₀ := fun σ hσ =>
      hcov (cover_D hL hD (mem_D7_iff.mpr hσ))
    have hrel := rel_of_cos hsq (X := D7) (fun t ht => hDfix t (mem_D7_iff.mp ht))
      (cosets_S43_D hc43) (cosets_S43_D (S43.mul_mem hc43 hc43)) h1 h2 h12 hcc
    exact eq_one_of_D hsq hDfix hrel.1 hq hv1 hv2

end CaseS

end CFSG.Quasithin.H13.A6.S7C
