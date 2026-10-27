module

public import CFSG.Quasithin.Vol2.Ch11G2Q8NormS

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.Quasithin.Vol2.Ch11.G2Q8

namespace KC4

variable {F : Type} [Field F] [CharP F 2]

@[expose] def InKer (x : ↥(cayleyGroup F)) : Prop := x ∈ stabV0 F ∧ levi1Mat x = 1

theorem inKer_iff [Finite F] {x : ↥(cayleyGroup F)} : InKer x ↔ x ∈ pCoreOf 2 (stabV0 F) :=
  mem_pCoreOf_stabV0_iff.symm

theorem exists_g2T_mul_of_mem_stabQ_one {γ : ↥(cayleyGroup F)} (hγ : γ ∈ stabQ (stdF F 1)) :
    ∃ a : Fˣ, ∃ s ∈ stabV0 F, γ = g2T (a, 1) * s := by
  have h1 : g2Act γ (eu 0 (1 : F)) ∈ stdF F 1 :=
    (mem_stabQ.mp hγ _).mp (mem_stdF_one_iff.mpr ⟨1, (one_smul _ _).symm⟩)
  obtain ⟨a, ha⟩ := mem_stdF_one_iff.mp h1
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    exact g2Act_eu_ne_zero γ (by rw [ha])
  refine ⟨Units.mk0 a ha0, (g2T (Units.mk0 a ha0, 1))⁻¹ * γ, ?_, by group⟩
  rw [mem_stabV0, ← map_inv, g2Act_mul_apply, ha, G2Q8.g2Act_smul, g2Act_g2T_eu, smul_eu]
  congr 1
  simp [ha0]

theorem conj_kerL1_g2T (s : Fˣ × Fˣ) {x : ↥(cayleyGroup F)} (hx : InKer x) :
    InKer (g2T s * x * (g2T s)⁻¹) := by
  refine ⟨g2T_conj_mem_stabV0 s hx.1, ?_⟩
  rw [levi1Mat_conj_g2T s hx.1, hx.2, Matrix.mul_one, levi1Mat_g2T_mul_inv]

theorem conj_kerL1_stab {s x : ↥(cayleyGroup F)} (hs : s ∈ stabV0 F) (hx : InKer x) :
    InKer (s * x * s⁻¹) := by
  have hsi := (stabV0 F).inv_mem hs
  refine ⟨(stabV0 F).mul_mem ((stabV0 F).mul_mem hs hx.1) hsi, ?_⟩
  rw [levi1Mat_mul ((stabV0 F).mul_mem hs hx.1) hsi, levi1Mat_mul hs hx.1, hx.2, Matrix.mul_one,
    ← levi1Mat_mul hs hsi, mul_inv_cancel, levi1Mat_one]

theorem conj_kerL1 {γ x : ↥(cayleyGroup F)} (hγ : γ ∈ stabQ (stdF F 1)) (hx : InKer x) :
    InKer (γ * x * γ⁻¹) := by
  obtain ⟨a, s, hs, rfl⟩ := exists_g2T_mul_of_mem_stabQ_one hγ
  have h := conj_kerL1_g2T (a, 1) (conj_kerL1_stab hs hx)
  rwa [show g2T (a, 1) * (s * x * s⁻¹) * (g2T (a, 1))⁻¹ = g2T (a, 1) * s * x * (g2T (a, 1) * s)⁻¹
    by group] at h

theorem levi1Mat_conj_torC1 (c : Fˣ) {s : ↥(cayleyGroup F)} (hs : s ∈ stabV0 F) :
    levi1Mat (g2T (torHomC1 F c) * s * (g2T (torHomC1 F c))⁻¹) = levi1Mat s := by
  have hc : (c : F) ≠ 0 := c.ne_zero
  rw [levi1Mat_conj_g2T _ hs, ← map_inv, levi1Mat_g2T_torHomC1, levi1Mat_g2T_torHomC1,
    Units.val_inv_eq_inv_val, inv_inv]
  simp only [smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one, smul_smul]
  rw [mul_inv_cancel₀ hc, one_smul]

theorem comm_torC1_mem (c : Fˣ) {γ : ↥(cayleyGroup F)} (hγ : γ ∈ stabQ (stdF F 1)) :
    InKer (γ * g2T (torHomC1 F c) * γ⁻¹ * (g2T (torHomC1 F c))⁻¹) := by
  obtain ⟨a, s, hs, rfl⟩ := exists_g2T_mul_of_mem_stabQ_one hγ
  set t := g2T (torHomC1 F c) with ht
  have htt : g2T (a, 1) * t = t * g2T (a, 1) := by
    rw [ht, ← map_mul, ← map_mul, mul_comm]
  have hsi := (stabV0 F).inv_mem hs
  have hk : InKer (s * (t * s⁻¹ * t⁻¹)) := by
    have hm : t * s⁻¹ * t⁻¹ ∈ stabV0 F := g2T_conj_mem_stabV0 _ hsi
    refine ⟨(stabV0 F).mul_mem hs hm, ?_⟩
    rw [levi1Mat_mul hs hm, levi1Mat_conj_torC1 c hsi, ← levi1Mat_mul hs hsi, mul_inv_cancel,
      levi1Mat_one]
  have h := conj_kerL1_g2T (a, 1) hk
  have e : g2T (a, 1) * (s * (t * s⁻¹ * t⁻¹)) * (g2T (a, 1))⁻¹ =
      g2T (a, 1) * s * t * (g2T (a, 1) * s)⁻¹ * t⁻¹ := by
    calc g2T (a, 1) * (s * (t * s⁻¹ * t⁻¹)) * (g2T (a, 1))⁻¹ =
        g2T (a, 1) * s * t * s⁻¹ * (t⁻¹ * (g2T (a, 1))⁻¹) := by group
      _ = g2T (a, 1) * s * t * s⁻¹ * ((g2T (a, 1))⁻¹ * t⁻¹) := by
        rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, htt]
      _ = _ := by group
  rwa [e] at h

theorem pCoreOf_stabV0_le [Finite F] :
    pCoreOf 2 (stabV0 F) ≤ pCoreOf 2 (stabQ (stdF F 1)) := by
  have := finite_cayleyGroup (F := F)
  set X := stabQ (stdF F 1) with hX
  set K₀ := pCoreOf 2 (stabV0 F) with hK₀
  have hK₀X : K₀ ≤ X := (Subgroup.map_subtype_le _).trans stabV0_le_stabQ
  have hp : IsPGroup 2 ↥K₀ := by
    rw [hK₀, pCoreOf_stabV0]
    exact isPGroup_ker_levi1.map _
  have hN : (K₀.subgroupOf X).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact inKer_iff.mp (conj_kerL1 g.2 (inKer_iff.mpr hx))⟩
  have hp' : IsPGroup 2 ↥(K₀.subgroupOf X) := fun x => by
    obtain ⟨k, hk⟩ := hp ⟨((x : ↥X) : ↥(cayleyGroup F)), Subgroup.mem_subgroupOf.mp x.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (congrArg (fun y : ↥K₀ => (y : ↥(cayleyGroup F))) hk))⟩
  have hle : K₀.subgroupOf X ≤ CFSG.Open.pCore 2 ↥X :=
    le_sSup ⟨hN, hp'⟩
  intro x hx
  exact ⟨⟨x, hK₀X hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem inner_of_mem_stabQ_one [Finite F] {γ₁ : ↥(cayleyGroup F)} (hγ₁ : γ₁ ∈ stabQ (stdF F 1)) :
    ∃ γ ∈ stabV0 F, ∀ s ∈ stabV0 F, InKer (γ₁ * s * γ₁⁻¹ * (γ * s * γ⁻¹)⁻¹) := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨a, s₁, hs₁, rfl⟩ := exists_g2T_mul_of_mem_stabQ_one hγ₁
  obtain ⟨b₀, hb₀⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) (a : F)
  have hb0 : b₀ ≠ 0 := by
    rintro rfl
    exact a.ne_zero (by rw [hb₀, mul_zero])
  set b := Units.mk0 b₀ hb0 with hb
  have ht' : g2T (1, b) ∈ stabV0 F := (g2T_mem_stabV0_iff (1, b)).mpr rfl
  refine ⟨g2T (1, b) * s₁, (stabV0 F).mul_mem ht' hs₁, fun s hs => ?_⟩
  set h := s₁ * s * s₁⁻¹ with hh
  have hhS : h ∈ stabV0 F := (stabV0 F).mul_mem ((stabV0 F).mul_mem hs₁ hs) ((stabV0 F).inv_mem hs₁)
  have hX : g2T (a, 1) * h * (g2T (a, 1))⁻¹ ∈ stabV0 F := g2T_conj_mem_stabV0 _ hhS
  have hY : g2T (1, b) * h * (g2T (1, b))⁻¹ ∈ stabV0 F := g2T_conj_mem_stabV0 _ hhS
  have hL : levi1Mat (g2T (a, 1) * h * (g2T (a, 1))⁻¹) =
      levi1Mat (g2T (1, b) * h * (g2T (1, b))⁻¹) := by
    rw [levi1Mat_conj_g2T _ hhS, levi1Mat_conj_g2T _ hhS, levi1Mat_g2T, levi1Mat_g2T,
      levi1Mat_g2T, levi1Mat_g2T]
    have ha : (a : F) = b₀ * b₀ := hb₀
    rw [Matrix.eta_fin_two (levi1Mat h)]
    simp only [Matrix.mul_fin_two, Prod.fst_inv, Prod.snd_inv, Units.val_inv_eq_inv_val,
      Units.val_one, hb, Units.val_mk0, ha]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp
  have e1 : g2T (a, 1) * s₁ * s * (g2T (a, 1) * s₁)⁻¹ = g2T (a, 1) * h * (g2T (a, 1))⁻¹ := by
    rw [hh]; group
  have e2 : g2T (1, b) * s₁ * s * (g2T (1, b) * s₁)⁻¹ = g2T (1, b) * h * (g2T (1, b))⁻¹ := by
    rw [hh]; group
  rw [e1, e2]
  have hYi := (stabV0 F).inv_mem hY
  refine ⟨(stabV0 F).mul_mem hX hYi, ?_⟩
  rw [levi1Mat_mul hX hYi, hL, ← levi1Mat_mul hY hYi, mul_inv_cancel, levi1Mat_one]

theorem frobConj_g2T (σ : F ≃+* F) (s : Fˣ × Fˣ) :
    frobConj σ (g2T s) = g2T (Units.map (σ : F →* F) s.1, Units.map (σ : F →* F) s.2) := by
  apply cayley_ext
  intro w
  have h := g2Act_frobConj σ (g2T s) (frobQ (σ.symm : F →+* F) w)
  rw [frobQ_symm] at h
  rw [h]
  funext j
  rw [frobQ, g2Act_g2T_apply, g2Act_g2T_apply, map_mul]
  simp only [frobQ, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  congr 1
  rcases j with j | j <;> fin_cases j <;> simp [chiT]

end KC4

end CFSG.Quasithin.Vol2.Ch11.SecA
