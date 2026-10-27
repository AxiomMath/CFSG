module

public import CFSG.Quasithin.MS93.S46I466bLin

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.Quasithin.MS93.S46.I466b
open scoped Matrix

variable {F : Type} [Field F]

theorem rootElt_mulVec_add_single {i j : Fin 3} (hij : i ≠ j) (c : F) (v : Fin 3 → F) :
    ((rootElt i j c : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v + Pi.single i (c * v j) := by
  rw [coe_rootElt hij, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  rfl

@[expose] def rotE01 : SL3 F := ⟨!![0, -1, 0; 1, 0, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem rotE01_mulVec (x : Fin 3 → F) :
    ((rotE01 : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = ![-x 1, x 0, x 2] := by
  ext i
  fin_cases i <;> simp [rotE01, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem exists_mulVec_eq_e₁ {v : Fin 3 → F} (hv : v ≠ 0) :
    ∃ y : SL3 F, (y : Matrix (Fin 3) (Fin 3) F) *ᵥ v = ![0, 1, 0] := by
  obtain ⟨w, hw⟩ : ∃ w : Fin 3 → F, w ∉ F ∙ v := by
    by_contra hall
    push Not at hall
    have hle : (⊤ : Submodule F (Fin 3 → F)) ≤ F ∙ v := fun x _ => hall x
    have h1 := Submodule.finrank_mono hle
    rw [finrank_top, Module.finrank_fin_fun, finrank_span_singleton hv] at h1
    omega
  set P : Submodule F (Fin 3 → F) := F ∙ v ⊔ F ∙ w with hPdef
  have hP : Module.finrank F P = 2 := by
    have hw0 : w ≠ 0 := fun h => hw (h ▸ Submodule.zero_mem _)
    have hinf : F ∙ v ⊓ F ∙ w = ⊥ := by
      rw [eq_bot_iff]
      intro x ⟨hxv, hxw⟩
      rw [Submodule.mem_bot]
      by_contra hx0
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxw
      have hc : c ≠ 0 := fun h => hx0 (by rw [h, zero_smul])
      apply hw
      have : w = c⁻¹ • (c • w) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ hxv
    have := Submodule.finrank_sup_add_finrank_inf_eq (F ∙ v) (F ∙ w)
    rw [hinf, finrank_bot, finrank_span_singleton hv, finrank_span_singleton hw0] at this
    omega
  obtain ⟨y, hy, -, -⟩ := exists_flag_conj hP (Submodule.mem_sup_left
    (Submodule.mem_span_singleton_self v)) hv
  refine ⟨rotE01 * y, ?_⟩
  rw [coe_mul_SL3, ← Matrix.mulVec_mulVec, hy, rotE01_mulVec]
  ext i
  fin_cases i <;> simp

theorem exists_map_eq_coordZero {P : Submodule F (Fin 3 → F)} (hP : Module.finrank F P = 2) :
    ∃ y : SL3 F, P.map ((y : Matrix (Fin 3) (Fin 3) F).mulVecLin) = coordZero 0 := by
  obtain ⟨r, hrP, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (by
    intro h; rw [h, finrank_bot] at hP; omega : P ≠ ⊥)
  obtain ⟨y, -, hyP, hyinv⟩ := exists_flag_conj hP hrP hr0
  refine ⟨rotE01 * y, le_antisymm ?_ ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    show (((rotE01 * y : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ p) 0 = 0
    rw [coe_mul_SL3, ← Matrix.mulVec_mulVec, rotE01_mulVec]
    simpa using hyP p hp
  · intro v hv
    have hv0 : v 0 = 0 := hv
    set u : Fin 3 → F := ![v 1, -v 0, v 2] with hu
    have hu1 : u 1 = 0 := by simp [hu, hv0]
    refine ⟨((y⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u, hyinv u hu1, ?_⟩
    show ((rotE01 * y : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      (((y⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u) = v
    rw [coe_mul_SL3, ← Matrix.mulVec_mulVec, mulVec_inv_mulVec_SL3, rotE01_mulVec]
    ext i
    fin_cases i <;> simp [hu]

theorem rootElt_mul_mulVec_e₁ (a b : F) :
    ((rootElt 0 1 a * rootElt 2 1 b : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 1, 0] =
      ![a, 1, b] := by
  rw [coe_mul_SL3, ← Matrix.mulVec_mulVec, rootElt_mulVec_add_single (by decide),
    rootElt_mulVec_add_single (by decide)]
  ext i
  simp only [Pi.add_apply, Pi.single_apply]
  fin_cases i <;> simp

theorem exists_conj_eq_rootGroup [Finite F] {P : Submodule F (Fin 3 → F)}
    (hP : Module.finrank F P = 2) {r : Fin 3 → F} (hrP : r ∈ P) (hr0 : r ≠ 0)
    {E : Subgroup (SL3 F)}
    (hfix : ∀ g ∈ E, ∀ p ∈ P, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ p = p)
    (hcomm : ∀ g ∈ E, ∀ v, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v ∈ F ∙ r)
    (hcard : Nat.card E = Nat.card F) :
    ∃ y : SL3 F, E.map (MulAut.conj y).toMonoidHom = rootGroup 0 1 := by
  obtain ⟨y, hyr, hyP, hyinv⟩ := exists_flag_conj hP hrP hr0
  refine ⟨y, ?_⟩
  have hle : E.map (MulAut.conj y).toMonoidHom ≤ rootGroup 0 1 := by
    rintro _ ⟨g, hg, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    set h := y * g * y⁻¹ with hh
    have hpre : ∀ w : Fin 3 → F, w 1 = 0 →
        ((h : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w := by
      intro w hw
      rw [hh, coe_mul_SL3, coe_mul_SL3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        hfix g hg _ (hyinv w hw), mulVec_inv_mulVec_SL3]
    obtain ⟨c, hc⟩ : ∃ c : F, ((h : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 1, 0] =
        ![c, 1, 0] := by
      set u := ((y⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 1, 0] with hu
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hcomm g hg u)
      refine ⟨c, ?_⟩
      have e1 : ((h : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 1, 0] =
          (y : Matrix (Fin 3) (Fin 3) F) *ᵥ (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u) := by
        rw [hh, coe_mul_SL3, coe_mul_SL3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      rw [e1, show ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u = u + c • r by
        rw [hc]; abel, Matrix.mulVec_add, Matrix.mulVec_smul, hyr, hu,
        mulVec_inv_mulVec_SL3]
      ext i
      fin_cases i <;> simp
    refine ⟨c, ?_⟩
    apply Subtype.ext
    refine Matrix.ext_of_mulVec_single fun j => ?_
    rw [rootElt_mulVec_add_single (by decide)]
    fin_cases j
    · have := hpre (Pi.single 0 1) (by simp)
      simp only [Fin.zero_eta, Fin.isValue] at this ⊢
      rw [this]
      ext i
      fin_cases i <;> simp
    · have e : (Pi.single 1 1 : Fin 3 → F) = ![0, 1, 0] := by
        ext i; fin_cases i <;> simp
      simp only [Fin.mk_one, Fin.isValue]
      rw [e, hc]
      ext i
      fin_cases i <;> simp
    · have := hpre (Pi.single 2 1) (by simp)
      simp only [Fin.reduceFinMk, Fin.isValue] at this ⊢
      rw [this]
      ext i
      fin_cases i <;> simp
  have : Finite ↥(rootGroup 0 1 : Subgroup (SL3 F)) := inferInstance
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_rootGroup (by decide), ← hcard]
  exact (Nat.card_congr (E.equivMapOfInjective _ (MulAut.conj y).injective).toEquiv).le

end CFSG.Quasithin.MS93.S46
