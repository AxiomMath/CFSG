module

public import CFSG.RankThree.PartTwo.Sec21.FF81P51Core

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.P51

open Matrix

@[expose] def psi0 : V := ![0, 0, 1, 2]

@[expose] def FiveInv (Γ : Subgroup GL4) : Prop :=
  ∀ g ∈ Γ, ¬ (psi0 ⬝ᵥ ((g : Mat) *ᵥ e 0) = 0 ∧ psi0 ⬝ᵥ ((g : Mat) *ᵥ e 1) = 0 ∧
    psi0 ⬝ᵥ ((g : Mat) *ᵥ e 2) = 0)

@[expose] def Pat (m : Fin 7 → Bool) (v : V) : Prop := v ≠ 0 ∧ m (orbOf v) = true

instance (m : Fin 7 → Bool) (v : V) : Decidable (Pat m v) := by unfold Pat; infer_instance

theorem pat_E : Pat mE (e 2) ∧ Pat mE (e 1 + e 2) ∧ ¬ Pat mE (e 0 + e 2) ∧
    ¬ Pat mE (e 0 + 2 • e 2) := by
  decide +kernel

theorem pat_C : Pat mC (e 0 + e 2) ∧ Pat mC (e 2) ∧ Pat mC (e 0 + 2 • e 2) ∧
    ¬ Pat mC (e 0 + e 1 + e 2) := by
  decide +kernel

theorem wtU_E : ∀ c ∈ nonzeroL, Pat mE c → ¬ Pat mE (c + e 0) → ¬ Pat mE (c + 2 • e 0) →
    wtU c = 1 := by
  decide +kernel

theorem wtU_C : ∀ c ∈ nonzeroL, Pat mC c → Pat mC (e 0 - c) → Pat mC (c + 2 • (e 0 - c)) →
    wtU c = 1 := by
  decide +kernel

theorem wtU_split : ∀ c ∈ nonzeroL, ∀ v ∈ nonzeroL, wtU c = 1 → e 0 ⬝ᵥ v = 0 → c ⬝ᵥ v = 0 →
    wtU v = 1 ∨ wtU v = 2 := by
  decide +kernel

theorem five_norm : ∀ c ∈ nonzeroL, ∀ v ∈ nonzeroL, wtU c = 1 → e 0 ⬝ᵥ v = 0 → c ⬝ᵥ v = 0 →
    wtU v = 2 → ∃ A ∈ H0L, psi0 ⬝ᵥ (A *ᵥ e 0) = 0 ∧ psi0 ⬝ᵥ (A *ᵥ c) = 0 ∧
      psi0 ⬝ᵥ (A *ᵥ v) = 0 := by
  decide +kernel

theorem last_E : ∀ v ∈ nonzeroL, e 0 ⬝ᵥ v = 0 → wtU v = 1 → ¬ Pat mE (v + e 0) := by
  decide +kernel

theorem last_C : ∀ v ∈ nonzeroL, e 0 ⬝ᵥ v = 0 → wtU v = 1 → Pat mC (v + e 0) := by
  decide +kernel

theorem S1_e : S1 *ᵥ e 0 = e 0 ∧ S1 *ᵥ e 1 = -e 1 ∧ S1 *ᵥ e 2 = e 2 := by
  decide +kernel

theorem inv_mulVec_mulVec (g : GL4) (v : V) : ((g⁻¹ : GL4) : Mat) *ᵥ ((g : Mat) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

theorem conj_mulVec (x s : GL4) (w : V) :
    ((x * s * x⁻¹ : GL4) : Mat) *ᵥ ((x : Mat) *ᵥ w) = (x : Mat) *ᵥ ((s : Mat) *ᵥ w) := by
  rw [Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec, mul_assoc, Units.inv_mul, mul_one,
    ← Matrix.mulVec_mulVec]

theorem dot_eq_zero_of_eigen {y : Mat} (hy : yᵀ * y = 1) {u v : V} (hu : y *ᵥ u = u)
    (hv : y *ᵥ v = -v) : u ⬝ᵥ v = 0 := by
  have h1 : (y *ᵥ u) ⬝ᵥ (y *ᵥ v) = u ⬝ᵥ v := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hy,
      Matrix.vecMul_one]
  rw [hu, hv, dotProduct_neg] at h1
  have key : ∀ a : ZMod 3, -a = a → a = 0 := by decide
  exact key _ h1

variable {Γ : Subgroup GL4}

theorem mem_Om_iff_pat (h : Hyp Γ) {m : Fin 7 → Bool} (hm : (cfgOf Γ).1 = m) (v : V) :
    v ∈ Om Γ ↔ Pat m v := by
  rw [om_iff h, hm]
  exact ⟨fun ⟨h1, h2⟩ => ⟨fun h0 => not_zero_mem_nonzeroL (h0 ▸ h1), h2⟩,
    fun ⟨h1, h2⟩ => ⟨mem_nonzeroL v h1, h2⟩⟩

theorem mulVec_mem_Om_iff {x : GL4} (hx : x ∈ Γ) {v : V} : (x : Mat) *ᵥ v ∈ Om Γ ↔ v ∈ Om Γ := by
  refine ⟨fun hv => ?_, mulVec_mem_Om (coe_mem_GM hx)⟩
  have := mulVec_mem_Om (coe_mem_GM (Γ.inv_mem hx)) hv
  rwa [inv_mulVec_mulVec] at this

theorem step (h : Hyp Γ) (h5 : FiveInv Γ) {x : GL4} (hx : x ∈ Γ) {c u : V}
    (hc : (x : Mat) *ᵥ e 0 = c) (hcw : wtU c = 1) (hu : (x : Mat) *ᵥ e 2 = u)
    (hfix : ∀ y : Mat, y *ᵥ c = c → y *ᵥ u = u → y *ᵥ e 0 = e 0)
    (hpsi : ∀ A : Mat, psi0 ⬝ᵥ (A *ᵥ e 0) = 0 → psi0 ⬝ᵥ (A *ᵥ c) = 0 → psi0 ⬝ᵥ (A *ᵥ u) = 0) :
    (x : Mat) *ᵥ e 1 ∈ nonzeroL ∧ e 0 ⬝ᵥ ((x : Mat) *ᵥ e 1) = 0 ∧ wtU ((x : Mat) *ᵥ e 1) = 1 := by
  set v := (x : Mat) *ᵥ e 1 with hvdef
  obtain ⟨s, hs, hsM⟩ := h.s1
  set y : GL4 := x * s * x⁻¹ with hydef
  have hy : y ∈ Γ := Γ.mul_mem (Γ.mul_mem hx hs) (Γ.inv_mem hx)
  obtain ⟨hS0, hS1, hS2⟩ := S1_e
  have hyc : (y : Mat) *ᵥ c = c := by rw [← hc, conj_mulVec, hsM, hS0]
  have hyu : (y : Mat) *ᵥ u = u := by rw [← hu, conj_mulVec, hsM, hS2]
  have hyv : (y : Mat) *ᵥ v = -v := by rw [hvdef, conj_mulVec, hsM, hS1, Matrix.mulVec_neg]
  have hy0 : (y : Mat) *ᵥ e 0 = e 0 := hfix _ hyc hyu
  have hyT : (y : Mat)ᵀ * (y : Mat) = 1 := by
    have := (H0L_transpose _ (stab_H0L h hy (Or.inl hy0))).2
    rwa [mm_eq] at this
  have h0v : e 0 ⬝ᵥ v = 0 := dot_eq_zero_of_eigen hyT hy0 hyv
  have hcv : c ⬝ᵥ v = 0 := dot_eq_zero_of_eigen hyT hyc hyv
  have hc0 : c ≠ 0 := fun h0 => by
    rw [h0, ← Matrix.mulVec_zero (x : Mat)] at hc
    exact e0_ne_zero (mulVec_inj x hc)
  have hv0 : v ≠ 0 := fun h0 => by
    have : e 1 = 0 := mulVec_inj x (by rw [Matrix.mulVec_zero]; exact h0)
    exact absurd this (by decide)
  have hcN := mem_nonzeroL c hc0
  have hvN := mem_nonzeroL v hv0
  rcases wtU_split c hcN v hvN hcw h0v hcv with h1 | h2
  · exact ⟨hvN, h0v, h1⟩
  obtain ⟨A, hA, hA0, hAc, hAv⟩ := five_norm c hcN v hvN hcw h0v hcv h2
  obtain ⟨a, ha, haA⟩ := mem_GM.1 (H0L_sub h A hA)
  refine absurd ?_ (h5 (a * x) (Γ.mul_mem ha hx))
  simp only [Units.val_mul, ← Matrix.mulVec_mulVec, hc, hu, haA]
  exact ⟨hAc, hAv, hpsi A hA0 hAc⟩

theorem ne_mE (h : Hyp Γ) (h5 : FiveInv Γ) : (cfgOf Γ).1 ≠ mE := by
  intro hm
  have hO := mem_Om_iff_pat h hm
  obtain ⟨pE2, pE12, npE02, npE022⟩ := pat_E
  obtain ⟨g, hg, hge⟩ := (hO (e 2)).2 pE2
  set x : GL4 := g⁻¹ with hxdef
  have hx : x ∈ Γ := Γ.inv_mem hg
  have hx2 : (x : Mat) *ᵥ e 2 = e 0 := by rw [← hge, hxdef, inv_mulVec_mulVec]
  set c := (x : Mat) *ᵥ e 0 with hcdef
  have hcO : c ∈ Om Γ := mulVec_mem_Om (coe_mem_GM hx) e0_mem_Om
  have h1 : ¬ Pat mE (c + e 0) := fun hp => by
    have : (x : Mat) *ᵥ (e 0 + e 2) ∈ Om Γ := by
      rw [Matrix.mulVec_add, hx2]; exact (hO _).2 hp
    exact npE02 ((hO _).1 ((mulVec_mem_Om_iff hx).1 this))
  have h2 : ¬ Pat mE (c + 2 • e 0) := fun hp => by
    have : (x : Mat) *ᵥ (e 0 + 2 • e 2) ∈ Om Γ := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, hx2]; exact (hO _).2 hp
    exact npE022 ((hO _).1 ((mulVec_mem_Om_iff hx).1 this))
  have hcw := wtU_E c (mem_nonzeroL c (ne_zero_of_mem_Om hcO)) ((hO c).1 hcO) h1 h2
  obtain ⟨hvN, h0v, hv1⟩ := step h h5 hx rfl hcw hx2 (fun _ _ hyu => hyu) (fun _ hA0 _ => hA0)
  have hmem : (x : Mat) *ᵥ (e 1 + e 2) ∈ Om Γ := (mulVec_mem_Om_iff hx).2 ((hO _).2 pE12)
  rw [Matrix.mulVec_add, hx2] at hmem
  exact last_E _ hvN h0v hv1 ((hO _).1 hmem)

theorem ne_mC (h : Hyp Γ) (h5 : FiveInv Γ) : (cfgOf Γ).1 ≠ mC := by
  intro hm
  have hO := mem_Om_iff_pat h hm
  obtain ⟨pC02, pC2, pC022, npC012⟩ := pat_C
  obtain ⟨g, hg, hge⟩ := (hO (e 0 + e 2)).2 pC02
  set x : GL4 := g⁻¹ with hxdef
  have hx : x ∈ Γ := Γ.inv_mem hg
  have hx02 : (x : Mat) *ᵥ (e 0 + e 2) = e 0 := by rw [← hge, hxdef, inv_mulVec_mulVec]
  set c := (x : Mat) *ᵥ e 0 with hcdef
  have hx2 : (x : Mat) *ᵥ e 2 = e 0 - c := by
    have : c + (x : Mat) *ᵥ e 2 = e 0 := by rw [hcdef, ← Matrix.mulVec_add, hx02]
    exact eq_sub_of_add_eq' this
  have hcO : c ∈ Om Γ := mulVec_mem_Om (coe_mem_GM hx) e0_mem_Om
  have h1 : Pat mC (e 0 - c) := by
    rw [← hx2, ← hO]; exact (mulVec_mem_Om_iff hx).2 ((hO _).2 pC2)
  have h2 : Pat mC (c + 2 • (e 0 - c)) := by
    have := (mulVec_mem_Om_iff hx).2 ((hO _).2 pC022)
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hx2] at this
    exact (hO _).1 this
  have hcw := wtU_C c (mem_nonzeroL c (ne_zero_of_mem_Om hcO)) ((hO c).1 hcO) h1 h2
  have hfix : ∀ y : Mat, y *ᵥ c = c → y *ᵥ (e 0 - c) = e 0 - c → y *ᵥ e 0 = e 0 := by
    intro y hyc hyu
    have := Matrix.mulVec_add y c (e 0 - c)
    rwa [hyc, hyu, add_sub_cancel] at this
  obtain ⟨hvN, h0v, hv1⟩ := step h h5 hx rfl hcw hx2 hfix (fun A hA0 hAc => by
    rw [Matrix.mulVec_sub, dotProduct_sub, hA0, hAc, sub_zero])
  have hx012 : (x : Mat) *ᵥ (e 0 + e 1 + e 2) = (x : Mat) *ᵥ e 1 + e 0 := by
    rw [Matrix.mulVec_add, Matrix.mulVec_add, hx2]; abel
  have hmem : (x : Mat) *ᵥ (e 0 + e 1 + e 2) ∈ Om Γ := by
    rw [hx012]; exact (hO _).2 (last_C _ hvN h0v hv1)
  exact npC012 ((hO _).1 ((mulVec_mem_Om_iff hx).1 hmem))

theorem ne_mC_mE (h : Hyp Γ) (h5 : FiveInv Γ) : (cfgOf Γ).1 ≠ mC ∧ (cfgOf Γ).1 ≠ mE :=
  ⟨ne_mC h h5, ne_mE h h5⟩

end CFSG.RankThree.PartTwo.Sec21.FF81.P51

end
