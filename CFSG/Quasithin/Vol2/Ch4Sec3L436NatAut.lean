module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesAlt
public import CFSG.Quasithin.Vol2.Ch4Sec4Inputs

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace L436NA

variable {F : Type} [Field F]

theorem det_eq_one {g : GL (Fin 2) F} (hg : g ∈ StatedSL 2 F) :
    (g : Matrix (Fin 2) (Fin 2) F).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hg

abbrev mat (g : StatedSL 2 F) : Matrix (Fin 2) (Fin 2) F := ((g : GL (Fin 2) F) : Matrix _ _ F)

@[expose] noncomputable def w0 (F : Type) [Field F] : StatedSL 2 F :=
  ⟨⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩,
    Subgroup.subset_closure (by simp [Matrix.det_fin_two_of])⟩

theorem mat_w0 : mat (w0 F) = !![0, 1; -1, 0] := rfl

theorem mat_w0_inv : mat (w0 F)⁻¹ = !![0, -1; 1, 0] := rfl

@[expose] noncomputable def dT (μ : Fˣ) : StatedSL 2 F :=
  ⟨⟨!![(μ : F), 0; 0, ((μ⁻¹ : Fˣ) : F)], !![((μ⁻¹ : Fˣ) : F), 0; 0, (μ : F)], by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩,
    Subgroup.subset_closure (by simp [Matrix.det_fin_two_of])⟩

theorem mat_dT (μ : Fˣ) : mat (dT μ) = !![(μ : F), 0; 0, ((μ⁻¹ : Fˣ) : F)] := rfl

theorem w0_mul_dT_mul_inv (μ : Fˣ) : w0 F * dT μ * (w0 F)⁻¹ = dT μ⁻¹ := by
  apply Subtype.ext
  apply Units.ext
  show mat (w0 F) * mat (dT μ) * mat (w0 F)⁻¹ = mat (dT μ⁻¹)
  rw [mat_w0, mat_dT, mat_w0_inv, mat_dT]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem ext_of_mulVec {g h : StatedSL 2 F}
    (h1 : (mat g).mulVec ![1, 0] = (mat h).mulVec ![1, 0])
    (h2 : (mat g).mulVec ![0, 1] = (mat h).mulVec ![0, 1]) : g = h := by
  apply Subtype.ext
  apply Units.ext
  show mat g = mat h
  ext i j
  fin_cases j
  · have := congrFun h1 i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  · have := congrFun h2 i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this

theorem mat_eq_of_mulVec_e₁ {g : StatedSL 2 F} {μ : Fˣ}
    (h1 : (mat g).mulVec ![1, 0] = ![(μ : F), 0]) :
    mat g = !![(μ : F), mat g 0 1; 0, ((μ⁻¹ : Fˣ) : F)] := by
  have h00 : mat g 0 0 = μ := by
    have := congrFun h1 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have h10 : mat g 1 0 = 0 := by
    have := congrFun h1 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hdet : mat g 0 0 * mat g 1 1 - mat g 0 1 * mat g 1 0 = 1 := by
    have := det_eq_one g.2
    rwa [Matrix.det_fin_two] at this
  have h11 : mat g 1 1 = ((μ⁻¹ : Fˣ) : F) := by
    rw [h00, h10, mul_zero, sub_zero] at hdet
    rw [Units.val_inv_eq_inv_val]
    exact eq_inv_of_mul_eq_one_right hdet
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · rfl
  · exact h10
  · exact h11

end L436NA

open L436NA

variable {G : Type} [Group G]

theorem centralizes_of_natural {L V C Z : Subgroup G} {F : Type} [Field F]
    (α : ↥L →* ↥(StatedSL 2 F)) (hαs : Function.Surjective α)
    (hαk : ∀ ℓ : ↥L, α ℓ = 1 → (ℓ : G) ∈ V)
    (β : ↥V →* Multiplicative (Fin 2 → F)) (hβs : Function.Surjective β)
    (hβk : ∀ v : ↥V, β v = 1 ↔ (v : G) ∈ C)
    (hβ : ∀ (a : ↥L) (u v : ↥V), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) = (mat (α a)).mulVec (Multiplicative.toAdd (β u)))
    (hΛ : ∀ v : ↥V, (v : G) ∈ C ⊔ Z ↔ Multiplicative.toAdd (β v) 1 = 0)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hCV : C ≤ V) (hCL : ∀ c ∈ C, ∀ ℓ ∈ L, c * ℓ = ℓ * c) (hcomm : ⁅V, L⁆ = V)
    {x : G} (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hxCZ : ∀ c ∈ C ⊔ Z, x * c * x⁻¹ = c)
    (v₂ : ↥V) (hv₂ : Multiplicative.toAdd (β v₂) = ![0, 1])
    (hxv₂ : ∀ w : ↥V, (w : G) = x * v₂ * x⁻¹ → Multiplicative.toAdd (β w) = ![0, 1]) :
    ∀ v ∈ V, x * v * x⁻¹ = v := by
  classical
  have hxVm : ∀ v ∈ V, x * v * x⁻¹ ∈ V := fun v hv => (Subgroup.mem_normalizer_iff.mp hxV v).mp hv
  have hxLm : ∀ ℓ ∈ L, x * ℓ * x⁻¹ ∈ L := fun ℓ hℓ =>
    (Subgroup.mem_normalizer_iff.mp hxL ℓ).mp hℓ
  have hLVm : ∀ ℓ ∈ L, ∀ v ∈ V, ℓ * v * ℓ⁻¹ ∈ V := fun ℓ hℓ v hv =>
    (Subgroup.mem_normalizer_iff.mp (hLV hℓ) v).mp hv
  set b : ↥V → (Fin 2 → F) := fun v => Multiplicative.toAdd (β v) with hb
  have hbmul : ∀ u v : ↥V, b (u * v) = b u + b v := fun u v => by
    simp only [hb, map_mul, toAdd_mul]
  have hbinv : ∀ u : ↥V, b u⁻¹ = - b u := fun u => by
    simp only [hb, map_inv, toAdd_inv]
  have hbeq : ∀ u v : ↥V, b u = b v → (u : G) * (v : G)⁻¹ ∈ C := fun u v h => by
    have h1 : β (u * v⁻¹) = 1 := by
      apply Multiplicative.toAdd.injective
      rw [map_mul, map_inv, toAdd_mul, toAdd_inv]
      have := congrArg (fun w => w - b v) h
      simpa [hb, sub_eq_add_neg] using this
    exact (hβk _).mp h1
  let xv : ↥V → ↥V := fun v => ⟨x * v * x⁻¹, hxVm v v.2⟩
  have hxCZ' : ∀ v : ↥V, b v 1 = 0 → xv v = v := fun v hv =>
    Subtype.ext (hxCZ v ((hΛ v).mpr hv))
  let xl : ↥L → ↥L := fun ℓ => ⟨x * ℓ * x⁻¹, hxLm ℓ ℓ.2⟩
  let lv : ↥L → ↥V → ↥V := fun ℓ v => ⟨ℓ * v * (ℓ : G)⁻¹, hLVm ℓ ℓ.2 v v.2⟩
  have hlv : ∀ ℓ v, b (lv ℓ v) = (mat (α ℓ)).mulVec (b v) := fun ℓ v => hβ ℓ v (lv ℓ v) rfl
  have hxlv : ∀ ℓ v, b (xv (lv ℓ v)) = (mat (α (xl ℓ))).mulVec (b (xv v)) := fun ℓ v =>
    hβ (xl ℓ) (xv v) (xv (lv ℓ v)) (by simp only [xv, xl, lv, Subgroup.coe_inv]; group)
  have hv₂' : b v₂ = ![0, 1] := hv₂
  obtain ⟨z, hz⟩ := hβs (Multiplicative.ofAdd ![1, 0])
  have hbz : b z = ![1, 0] := by simp [hb, hz]
  have hxz : xv z = z := hxCZ' z (by rw [hbz]; rfl)
  have hxv2 : b (xv v₂) = ![0, 1] := hxv₂ (xv v₂) rfl
  have hfix : ∀ v : ↥V, b v 1 = 0 → b (xv v) = b v := fun v hv => by rw [hxCZ' v hv]
  have hxvc : ∀ u v : ↥V, b u = b v → b (xv u) = b (xv v) := fun u v h => by
    have hc := hbeq u v h
    have hc' : xv u = ⟨(u : G) * (v : G)⁻¹, mul_mem u.2 (inv_mem v.2)⟩ * xv v := by
      apply Subtype.ext
      have hcx := hxCZ _ (Subgroup.mem_sup_left hc)
      simp only [xv, Subgroup.coe_mul]
      calc x * ↑u * x⁻¹ = (x * (↑u * (↑v)⁻¹) * x⁻¹) * (x * ↑v * x⁻¹) := by group
        _ = ↑u * (↑v)⁻¹ * (x * ↑v * x⁻¹) := by rw [hcx]
    rw [hc', hbmul]
    have h0 : b ⟨(u : G) * (v : G)⁻¹, mul_mem u.2 (inv_mem v.2)⟩ = 0 := by
      have := (hβk ⟨_, mul_mem u.2 (inv_mem v.2)⟩).mpr hc
      simp [hb, this]
    rw [h0, zero_add]
  obtain ⟨ℓ₀, hℓ₀⟩ := hαs (w0 F)
  have hθw : α (xl ℓ₀) = w0 F := by
    apply ext_of_mulVec
    ·
      have h1 : b (lv ℓ₀ z) = b v₂⁻¹ := by
        rw [hlv, hℓ₀, hbz, hbinv, hv₂', mat_w0]
        ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      have h2 := hxvc _ _ h1
      rw [hxlv, hxz, hbz] at h2
      rw [h2, mat_w0]
      have h3 : b (xv v₂⁻¹) = - b (xv v₂) := by
        have : xv v₂⁻¹ = (xv v₂)⁻¹ := Subtype.ext (by simp [xv]; group)
        rw [this, hbinv]
      rw [h3, hxv2]
      ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ·
      have h1 : b (lv ℓ₀ v₂) = b z := by
        rw [hlv, hℓ₀, hv₂', hbz, mat_w0]
        ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      have h2 := hxvc _ _ h1
      rw [hxlv, hxv2, hxz, hbz] at h2
      rw [h2, mat_w0]
      ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hθde : ∀ (ℓ : ↥L) (μ : Fˣ), α ℓ = dT μ →
      (mat (α (xl ℓ))).mulVec ![1, 0] = ![(μ : F), 0] := by
    intro ℓ μ hℓ
    have h1 : b (lv ℓ z) = ![(μ : F), 0] := by
      rw [hlv, hℓ, hbz, mat_dT]
      ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have h2 := hfix (lv ℓ z) (by rw [h1]; rfl)
    rw [hxlv, hxz, hbz, h1] at h2
    exact h2
  have hθd : ∀ (ℓ : ↥L) (μ : Fˣ), α ℓ = dT μ → α (xl ℓ) = dT μ := by
    intro ℓ μ hℓ
    have hm := mat_eq_of_mulVec_e₁ (hθde ℓ μ hℓ)
    set ℓ' : ↥L := ℓ₀ * ℓ * ℓ₀⁻¹ with hℓ'
    have hαℓ' : α ℓ' = dT μ⁻¹ := by
      rw [hℓ', map_mul, map_mul, map_inv, hℓ₀, hℓ, w0_mul_dT_mul_inv]
    have hxl' : xl ℓ' = xl ℓ₀ * xl ℓ * (xl ℓ₀)⁻¹ := Subtype.ext (by
      simp only [xl, hℓ', Subgroup.coe_mul, Subgroup.coe_inv]; group)
    have h1 := hθde ℓ' μ⁻¹ hαℓ'
    rw [hxl', map_mul, map_mul, map_inv, hθw] at h1
    have h2 : (mat (w0 F * α (xl ℓ) * (w0 F)⁻¹)).mulVec ![1, 0] =
        ![((μ⁻¹ : Fˣ) : F), - mat (α (xl ℓ)) 0 1] := by
      show (mat (w0 F) * mat (α (xl ℓ)) * mat (w0 F)⁻¹).mulVec ![1, 0] = _
      rw [mat_w0, mat_w0_inv, hm]
      ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]
    rw [h2] at h1
    have hν : mat (α (xl ℓ)) 0 1 = 0 := by
      have := congrFun h1 1
      simpa using this
    apply ext_of_mulVec
    · rw [hθde ℓ μ hℓ, mat_dT]
      ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · rw [hm, hν, mat_dT]
  have hA : ∀ v : ↥V, b (xv v) = b v := by
    intro v
    by_cases hv1 : b v 1 = 0
    · exact hfix v hv1
    · set μ : Fˣ := Units.mk0 (b v 1) hv1 with hμ
      obtain ⟨ℓ, hℓ⟩ := hαs (dT μ⁻¹)
      have h1 : b (lv ℓ v₂) = ![0, b v 1] := by
        rw [hlv, hℓ, hv₂', mat_dT]
        ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hμ]
      set c : ↥V := v * (lv ℓ v₂)⁻¹ with hc
      have hbc : b c = ![b v 0, 0] := by
        rw [hc, hbmul, hbinv, h1]
        ext i; fin_cases i <;> simp
      have hvc : v = c * lv ℓ v₂ := by rw [hc, inv_mul_cancel_right]
      have hxvmul : xv v = xv c * xv (lv ℓ v₂) := by
        rw [hvc]
        exact Subtype.ext (by simp only [xv, Subgroup.coe_mul]; group)
      rw [hxvmul, hbmul, hfix c (by rw [hbc]; rfl), hbc, hxlv, hθd ℓ μ⁻¹ hℓ, hxv2, mat_dT]
      ext i; fin_cases i <;> simp [hμ]
  have hθ : ∀ ℓ : ↥L, α (xl ℓ) = α ℓ := by
    intro ℓ
    apply ext_of_mulVec
    · have h1 := hxlv ℓ z
      rw [hA, hA, hlv, hbz] at h1
      exact h1.symm
    · have h1 := hxlv ℓ v₂
      rw [hA, hA, hlv, hv₂'] at h1
      exact h1.symm
  have hxlV : ∀ ℓ ∈ L, x * ℓ * x⁻¹ * ℓ⁻¹ ∈ V := by
    intro ℓ hℓ
    have h1 : α (xl ⟨ℓ, hℓ⟩ * (⟨ℓ, hℓ⟩ : ↥L)⁻¹) = 1 := by
      rw [map_mul, map_inv, hθ, mul_inv_cancel]
    exact hαk _ h1
  have hδC : ∀ v : ↥V, x * (v : G) * x⁻¹ * (v : G)⁻¹ ∈ C := fun v => hbeq (xv v) v (hA v)
  have hcomm_x : ∀ v ∈ V, ∀ ℓ ∈ L, x * ⁅v, ℓ⁆ * x⁻¹ = ⁅v, ℓ⁆ := by
    intro v hv ℓ hℓ
    set c := x * v * x⁻¹ * v⁻¹ with hcdef
    set w := x * ℓ * x⁻¹ * ℓ⁻¹ with hwdef
    have hcC : c ∈ C := hδC ⟨v, hv⟩
    have hwV : w ∈ V := hxlV ℓ hℓ
    have hxv' : x * v * x⁻¹ = c * v := by rw [hcdef]; group
    have hxl' : x * ℓ * x⁻¹ = w * ℓ := by rw [hwdef]; group
    have hlv' : ℓ * v⁻¹ * ℓ⁻¹ ∈ V := hLVm ℓ hℓ _ (inv_mem hv)
    have h1 : x * ⁅v, ℓ⁆ * x⁻¹ = (x * v * x⁻¹) * (x * ℓ * x⁻¹) * (x * v * x⁻¹)⁻¹ *
        (x * ℓ * x⁻¹)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [h1, hxv', hxl', commutatorElement_def]
    have hcl : c * ℓ = ℓ * c := hCL c hcC ℓ hℓ
    have hwlv : w * (ℓ * v⁻¹ * ℓ⁻¹) = (ℓ * v⁻¹ * ℓ⁻¹) * w := hVab w hwV _ hlv'
    have e0 : c⁻¹ * ℓ⁻¹ = ℓ⁻¹ * c⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hcl]
    have hX : v * w * (ℓ * v⁻¹ * ℓ⁻¹) ∈ V := mul_mem (mul_mem hv hwV) hlv'
    have hcX : c * (v * w * (ℓ * v⁻¹ * ℓ⁻¹)) = (v * w * (ℓ * v⁻¹ * ℓ⁻¹)) * c :=
      hVab c (hCV hcC) _ hX
    calc c * v * (w * ℓ) * (c * v)⁻¹ * (w * ℓ)⁻¹
        = c * v * w * ℓ * v⁻¹ * (c⁻¹ * ℓ⁻¹) * w⁻¹ := by group
      _ = c * v * w * ℓ * v⁻¹ * (ℓ⁻¹ * c⁻¹) * w⁻¹ := by rw [e0]
      _ = c * (v * w * (ℓ * v⁻¹ * ℓ⁻¹)) * c⁻¹ * w⁻¹ := by group
      _ = (v * w * (ℓ * v⁻¹ * ℓ⁻¹)) * c * c⁻¹ * w⁻¹ := by rw [hcX]
      _ = v * (w * (ℓ * v⁻¹ * ℓ⁻¹)) * w⁻¹ := by group
      _ = v * ((ℓ * v⁻¹ * ℓ⁻¹) * w) * w⁻¹ := by rw [hwlv]
      _ = v * ℓ * v⁻¹ * ℓ⁻¹ := by group
  have hVC : V ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [← hcomm, Subgroup.commutator_def, Subgroup.closure_le]
    rintro _ ⟨v, hv, ℓ, hℓ, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have h := hcomm_x v hv ℓ hℓ
    calc ⁅v, ℓ⁆ * x = (x * ⁅v, ℓ⁆ * x⁻¹) * x := by rw [h]
      _ = x * ⁅v, ℓ⁆ := by group
  intro v hv
  have h := Subgroup.mem_centralizer_singleton_iff.mp (hVC hv)
  rw [← h, mul_inv_cancel_right]

end CFSG.Quasithin.H13.Ch4
