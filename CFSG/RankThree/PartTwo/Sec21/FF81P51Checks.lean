module

public import Certificates.Certificate899051

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.P51

open Matrix

theorem mem_nonzeroL : ∀ v : V, v ≠ 0 → v ∈ nonzeroL :=
  Certificates.certificate899051.1

theorem not_zero_mem_nonzeroL : (0 : V) ∉ nonzeroL :=
  Certificates.certificate899051.2.1

theorem mem_allV : ∀ v : V, v ∈ allV :=
  Certificates.certificate899051.2.2.1

theorem H0L_transpose : ∀ A ∈ H0L, mm A Aᵀ = 1 ∧ mm Aᵀ A = 1 :=
  Certificates.certificate899051.2.2.2.1

theorem H0L_comm_T0 : ∀ A ∈ H0L, mm A T0 = mm T0 A :=
  Certificates.certificate899051.2.2.2.2.1

theorem H0L_cols : ∀ c₀ ∈ E0L, ∀ c₁ ∈ SU, ∀ c₂ ∈ SU, ∀ c₃ ∈ SU,
    ofCols ![c₀, c₁, c₂, c₃] ∈ H0L ∨ c₁ = c₂ ∨ c₁ = -c₂ ∨ c₁ = c₃ ∨ c₁ = -c₃ ∨ c₂ = c₃ ∨
      c₂ = -c₃ :=
  Certificates.certificate899051.2.2.2.2.2.1

theorem card_stab : ((H0L.filter fun A => decide (mv A (e 0) = e 0)).toFinset).card = 48 :=
  Certificates.certificate899051.2.2.2.2.2.2.1

theorem tab_spec : ∀ v ∈ nonzeroL, (tab v).2 ∈ H0L ∧ mv (tab v).2 (rep (tab v).1) = v :=
  Certificates.certificate899051.2.2.2.2.2.2.2.1

theorem tab_rep : ∀ k : Fin 7, (tab (rep k)).1 = k :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.1

theorem rep_ne_zero : ∀ k : Fin 7, rep k ≠ 0 :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.1

theorem nonzeroL_eq : nonzeroL = nonzeroD.map V4.toV :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.1

theorem allV_eq : allV = allD.map V4.toV :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.1

theorem H0L_eq : H0L = H0D.map M16.toM :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem mem_allD : ∀ x : V4, x ∈ allD :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem tab_eqD : ∀ x ∈ allD, tab x.toV = ((tabD x).1, (tabD x).2.toM) :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem tab_toV (x : V4) : tab x.toV = ((tabD x).1, (tabD x).2.toM) := tab_eqD x (mem_allD x)

theorem rep_eqD : ∀ k : Fin 7, rep k = (repD k).toV :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem okL_eq : ∀ k : Fin 7, okL k = (okLD k).map V4.toV :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem T0_eqD : T0 = T0D.toM :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem S1_eqD : S1 = S1D.toM :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Tau_eqD : Tau = TauD.toM :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Cyc_eqD : Cyc = CycD.toM :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Sig01_eqD : Sig01 = Sig01D.toM :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem e0_eqD : e 0 = e0D.toV :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem H0D_sub_H0WD : ∀ a ∈ H0D, a ∈ H0WD :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem toM_mem_H0L_iff {m : M16} : m.toM ∈ H0L ↔ m ∈ H0D := by
  rw [H0L_eq, List.mem_map]
  constructor
  · rintro ⟨a, ha, h⟩
    exact M16.toM_inj h ▸ ha
  · exact fun h => ⟨m, h, rfl⟩

theorem okB_iff (w ψ : V4) : OkB w.toV ψ.toV ↔ OkBD w ψ := by
  unfold OkB OkBD
  rw [H0L_eq, List.forall_mem_map]
  simp only [mv_eq, mm_eq, refl_eq, ← M16.toM_refl, ← M16.toV_mulV, ← V4.toV_neg, V4.toV_inj_iff,
    ← M16.toM_mul, M16.toM_inj_iff, e0_eqD, List.mem_map, exists_eq_right]

theorem okD : ∀ k : Fin 7, ∀ y ∈ allD, V4.dot y (repD k) = 1 → OkBD (repD k) y → y ∈ okLD k :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem ok_rep : ∀ k : Fin 7, ∀ ψ ∈ allV, ψ ⬝ᵥ rep k = 1 → OkB (rep k) ψ → ψ ∈ okL k := by
  intro k ψ hψ
  rw [allV_eq, List.mem_map] at hψ
  obtain ⟨y, hy, rfl⟩ := hψ
  rw [rep_eqD k, V4.dot_toV, okB_iff, okL_eq, List.mem_map]
  exact fun hd hok => ⟨y, okD k y hy hd hok, rfl⟩

theorem e0_ne_zero : e 0 ≠ 0 :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem e_ne : ∀ i j : Fin 4, i ≠ j → e i ≠ e j ∧ e i ≠ -e j :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem T0_eq : T0 = 1 + vecMulVec (e 0) (e 0) :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem T0_sq : mm T0 T0 = 1 :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem e0_dot : e 0 ⬝ᵥ e 0 = 1 :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem rep_zero : rep 0 = e 0 :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem vec_e0 : (![1, 0, 0, 0] : V) = e 0 :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem sig01_cyc4 : mm Sig01 Cyc4 ∈ H0L :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem sig01_sq : mm Sig01 Sig01 = 1 :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem sig01_e1 : Sig01 *ᵥ e 1 = e 0 :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem mA_sub_Fr8 : ∀ v ∈ nonzeroL, mA (tab v).1 = true → v ∈ Fr8 :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem mA_e : ∀ j : Fin 4, e j ∈ nonzeroL ∧ mA (tab (e j)).1 = true :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem sig01_Fr8 : ∀ v ∈ Fr8, v ≠ e 1 → v ≠ -e 1 → Sig01 *ᵥ v ∈ SU :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem T0_cols : ofCols ![-e 0, e 1, e 2, e 3] = T0 :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem S1_cols : ofCols ![e 0, -e 1, e 2, e 3] = S1 :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Tau_cols : ofCols ![e 0, e 2, e 1, e 3] = Tau :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Cyc_cols : ofCols ![e 0, e 2, e 3, e 1] = Cyc :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Sig01_cols : Sig01 *ᵥ e 0 = e 1 ∧ Sig01 *ᵥ e 1 = e 0 ∧ Sig01 *ᵥ e 2 = e 2 ∧
    Sig01 *ᵥ e 3 = e 3 :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Cyc4_cols : Cyc4 *ᵥ e 0 = e 1 ∧ Cyc4 *ᵥ e 1 = e 2 ∧ Cyc4 *ᵥ e 2 = e 3 ∧
    Cyc4 *ᵥ e 3 = e 0 :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem T0_e0 : T0 *ᵥ e 0 = -e 0 :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem rep_six : rep 6 = e 0 + e 1 + e 2 + e 3 :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem e_succ_zero : ∀ i : Fin 4, i ≠ 0 → e i 0 = 0 :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem pos_or : ∀ v ∈ nonzeroL, pos v = true ∨ pos (-v) = true :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem not_pos_and : ∀ v ∈ nonzeroL, ¬(pos v = true ∧ pos (-v) = true) :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem lineCount_mA : lineCount mA = 4 :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem lineCount_mB : lineCount mB = 12 :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem lineCount_mC : lineCount mC = 24 :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem lineCount_mD : lineCount mD = 15 :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem lineCount_mE : lineCount mE = 30 :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem vecCount (m : Fin 7 → Bool) (hm : m = mA ∨ m = mB ∨ m = mC ∨ m = mD ∨ m = mE) :
    ((nonzeroL.filter fun v => m (tab v).1).toFinset).card = 2 * lineCount m :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 m hm

theorem classify_allD : ([false, true].all fun m₁ => [false, true].all fun m₂ =>
    [false, true].all fun m₄ => [false, true].all fun m₅ => [false, true].all fun m₆ =>
    (optLD 1 m₁).all fun p₁ => (optLD 2 m₂).all fun p₂ => (optLD 4 m₄).all fun p₄ =>
    (optLD 5 m₅).all fun p₅ => (optLD 6 m₆).all fun p₆ =>
    decide (C1D (mkCfgD m₁ m₂ m₄ m₅ m₆ p₁ p₂ p₄ p₅ p₆) →
      C3D (mkCfgD m₁ m₂ m₄ m₅ m₆ p₁ p₂ p₄ p₅ p₆) →
      C4D (mkCfgD m₁ m₂ m₄ m₅ m₆ p₁ p₂ p₄ p₅ p₆) 2 → C4D (mkCfgD m₁ m₂ m₄ m₅ m₆ p₁ p₂ p₄ p₅ p₆) 4 →
      GoodD (mkCfgD m₁ m₂ m₄ m₅ m₆ p₁ p₂ p₄ p₅ p₆))) = true :=
  Certificates.certificate899051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.RankThree.PartTwo.Sec21.FF81.P51
