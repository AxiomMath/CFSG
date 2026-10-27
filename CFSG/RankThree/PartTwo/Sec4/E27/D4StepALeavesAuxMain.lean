module

public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxGlue
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL1
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL2
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL3
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepAPlane
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTorus2
public import CFSG.RankThree.PartTwo.Sec4.E27.D4Classify

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.Seitz CFSG.Open TauCeti CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec11
open CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec4.E27

section StepALayerAux


variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem layer_center_facts (P : D4Par n X σ) (hn : 2 ≤ n) {x : C0 σ} (hx : IsClassX σ x) :
    (∀ a ∈ Subgroup.centralizer
        (layerSub σ x : Set (C0 σ)),
      ∀ b ∈ Subgroup.centralizer
        (layerSub σ x : Set (C0 σ)), a * b = b * a) ∧
    (∀ z ∈ Subgroup.centralizer
        (layerSub σ x : Set (C0 σ)), (∃ k : ℕ, z ^ (3 ^ k) = 1) → z ∈ Subgroup.zpowers x) ∧
    (∀ w ∈ layerSub σ x,
      (∀ d ∈ layerSub σ x,
        w * d = d * w) → w ∈ Subgroup.zpowers x) :=
  ⟨layer_centralizer_abelian P hn hx, layer_centralizer_three_part P hn hx,
    fun w hw hc => (classX_layer σ P hn hx).2 w hw (layer_center_cube P hn hx w hw hc) hc⟩

theorem two_pow_mod_three_odd {n : ℕ} (hn : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨m, rfl⟩ := hn
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem layer_conj_mem {K : Type*} [Group K] (C : Subgroup K) {g d : K} (hg : g ∈ C)
    (hd : d ∈ ⁅C, C⁆) : g * d * g⁻¹ ∈ ⁅C, C⁆ := by
  have hle : ⁅C, C⁆ ≤ (⁅C, C⁆).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_comap]
    show (MulAut.conj g) ⁅a, b⁆ ∈ ⁅C, C⁆
    rw [map_commutatorElement]
    exact Subgroup.commutator_mem_commutator
      (C.mul_mem (C.mul_mem hg ha) (C.inv_mem hg)) (C.mul_mem (C.mul_mem hg hb) (C.inv_mem hg))
  have := hle hd
  rwa [Subgroup.mem_comap] at this

theorem shape_of_mem_E (P : D4Par n X σ) {E : Subgroup (MulAut (C0 σ))} (hE : IsElemAbelian 3 E) :
    ∀ y ∈ E, ∃ (g : C0 σ) (j : ℕ), y = MulAut.conj g * tauAut σ ^ j := by
  intro y hy
  obtain ⟨Θ, hΘ, -, hdec⟩ := exists_theta σ n P.one_le P.card P.frob
  obtain ⟨g, δ, hgδ⟩ := hdec y
  have hy3 : y ^ 3 = 1 := hE.2 y hy
  have hδ : δ = Θ y := (hΘ y g δ hgδ).symm
  have hΘ3 : Θ y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  obtain ⟨e, he⟩ : ∃ e : ℕ, δ = σ ^ e := by
    rcases gal_cube_cases σ n P.one_le P.card P.frob (Θ y) hΘ3 with h | h | h
    · exact ⟨0, by rw [hδ, h, pow_zero]⟩
    · exact ⟨1, by rw [hδ, h, pow_one]⟩
    · exact ⟨2, by rw [hδ, h]⟩
  refine ⟨g, e, ?_⟩
  have hpow : fieldActor (t := TwistTag.D4) σ (σ ^ e) = tauAut σ ^ e :=
    map_pow (fieldActorHom (t := TwistTag.D4) σ) σ e
  rw [hgδ, he, hpow]

theorem planeThm_linear {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F)
    (h3 : 3 ∣ Nat.card F - 1) :
    ∀ E' : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 3) F)), IsElemAbelian 3 E' →
      Nat.card E' = 9 → (∀ φ ∈ E', ∃ M : Matrix.GeneralLinearGroup (Fin 3) F, IsConjBy φ M) →
      (¬ FixCube E' → ¬ E' ≤ (MulAut.conj : Matrix.SpecialLinearGroup (Fin 3) F →*
        MulAut (Matrix.SpecialLinearGroup (Fin 3) F)).range) →
      Subgroup.closure (fixSet E') = ⊤ := by
  intro E' hE' hcard hP hout
  by_cases hF : FixCube E'
  · exact closure_fixSet_eq_top_linear h3 E' hE' hcard hF
  · exact sl3_plane_closure_linear h4 h3 E' hE' hcard (hout hF) hP

theorem planeThm_unitary {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F)
    (hq3 : p ^ f % 3 = 2) (hq : 2 < p ^ f) :
    ∀ E' : Subgroup (MulAut (unitarySU p f F 3)), IsElemAbelian 3 E' → Nat.card E' = 9 →
      (∀ φ ∈ E', φ ∈ (CFSG.RankThree.PartTwo.KFacts.suConj h).range) →
      (¬ FixCube E' → ¬ E' ≤ (MulAut.conj : unitarySU p f F 3 →*
        MulAut (unitarySU p f F 3)).range) → Subgroup.closure (fixSet E') = ⊤ := by
  intro E' hE' hcard hP hout
  by_cases hF : FixCube E'
  · exact closure_fixSet_eq_top_unitary_of_conj h (Nat.dvd_of_mod_eq_zero (by omega)) hq E' hE'
      hcard hF (fun e he => by
        obtain ⟨B, hB⟩ := hP e he
        exact ⟨B, hB.symm⟩)
  · exact su3_plane_closure_unitary h hq3 hq E' hE' hcard (hout hF) (fun φ hφ => hP φ hφ)

theorem layer_le_closure_fixed_A0 (hgold : CFSG.Goldschmidt.TopStatement) (P : D4Par n X σ)
    (hn : 2 ≤ n) {E : Subgroup (MulAut (C0 σ))} (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 27)
    (hno : ∀ φ : MulAut (C0 σ), tauAut σ ∉ E.map (MulAut.congr φ).toMonoidHom)
    {x : C0 σ} (hx : MulAut.conj x ∈ E) (hx1 : x ≠ 1) (hxA : x ∈ A0sub σ) :
    layerSub σ x ≤ Subgroup.closure {l | l ∈ layerSub σ x ∧ ∃ y ∈ E,
      y ∉ Subgroup.zpowers (MulAut.conj x : MulAut (C0 σ)) ∧ y l = l} := by
  haveI : Finite (C0 σ) := finite_C0
  have hxX : IsClassX σ x := classX_of_no_conj_tau hgold P hn hE hcard hno hx hx1
  have hinj := conj_injective_C0 σ n P.one_le P.card P.frob
  have hτx : tauAut σ x = x := (Subgroup.mem_inf.1 hxA).2
  have hshape := shape_of_mem_E P hE
  have hτD := tau_fixes_layer P hn hxX hxA
  obtain ⟨hZab, hZ3, hDZ⟩ := layer_center_facts P hn hxX
  rcases Nat.even_or_odd n with hev | hodd
  · obtain ⟨F, _, _, h4, h3, e, hact⟩ := layer_linear_model P hn hev hxX
    refine layer_closure_of_plane (C := cenX σ x) (D := layerSub σ x) hinj (tauAut σ) x hxX.1 hx1
      hτx rfl rfl hE hx hcard hshape hτD hZab hZ3 hDZ
      (fun φ => ∃ M : Matrix.GeneralLinearGroup (Fin 3) F, IsConjBy φ M) e ?_
      (planeThm_linear h4 h3)
    intro g hg φ hφ
    obtain ⟨N, hN⟩ := hact g hg
    refine ⟨N, fun t => ?_⟩
    have hd : g * ((e.symm t : layerSub σ x) : C0 σ) * g⁻¹ ∈ layerSub σ x :=
      layer_conj_mem (cenX σ x) hg (e.symm t).2
    have h1 := hφ (e.symm t) ⟨_, hd⟩ rfl
    rw [MulEquiv.apply_symm_apply] at h1
    rw [h1]
    have h2 := hN (e.symm t) ⟨_, hd⟩ rfl
    rw [MulEquiv.apply_symm_apply] at h2
    exact h2
  · obtain ⟨F, _, hF, e, hact⟩ := layer_unitary_model P hn hodd hxX
    have hq3 : 2 ^ n % 3 = 2 := two_pow_mod_three_odd hodd
    have hn3 : 3 ≤ n := by
      obtain ⟨m, rfl⟩ := hodd
      omega
    have hq : 2 < 2 ^ n := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn3)
    refine layer_closure_of_plane (C := cenX σ x) (D := layerSub σ x) hinj (tauAut σ) x hxX.1 hx1
      hτx rfl rfl hE hx hcard hshape hτD hZab hZ3 hDZ
      (fun φ => φ ∈ (CFSG.RankThree.PartTwo.KFacts.suConj hF).range) e ?_
      (planeThm_unitary hF hq3 hq)
    intro g hg φ hφ
    obtain ⟨A, hA⟩ := hact g hg
    refine ⟨A, ?_⟩
    ext t
    have hd : g * ((e.symm t : layerSub σ x) : C0 σ) * g⁻¹ ∈ layerSub σ x :=
      layer_conj_mem (cenX σ x) hg (e.symm t).2
    have h1 := hφ (e.symm t) ⟨_, hd⟩ rfl
    rw [MulEquiv.apply_symm_apply] at h1
    have h2 := hA (e.symm t) ⟨_, hd⟩ rfl
    rw [MulEquiv.apply_symm_apply] at h2
    rw [h1, h2]

theorem congr_conj_conj {K : Type*} [Group K] (h y : K) :
    (MulAut.congr (MulAut.conj h)) (MulAut.conj y) = MulAut.conj (h * y * h⁻¹) := by
  rw [congr_apply_eq, map_mul, map_mul, map_inv, ← MulAut.conj_apply]

theorem layer_map_conj (σ : X ≃+* X) (h x : C0 σ) :
    (layerSub σ (h * x * h⁻¹)).map (MulAut.conj h⁻¹).toMonoidHom = layerSub σ x := by
  have hC : (cenX σ (h * x * h⁻¹)).map (MulAut.conj h⁻¹).toMonoidHom = cenX σ x := by
    ext k
    constructor
    · rintro ⟨c, hc, rfl⟩
      have := (mem_centralizer_conj_iff h x c).1 hc
      simpa [MulAut.conj_apply, mul_assoc] using this
    · intro hk
      refine ⟨h * k * h⁻¹, (mem_centralizer_conj_iff h x _).2 (by simpa [mul_assoc] using hk), ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  show (⁅cenX σ (h * x * h⁻¹), cenX σ (h * x * h⁻¹)⁆).map _ = ⁅cenX σ x, cenX σ x⁆
  rw [Subgroup.map_commutator, hC]

theorem layer_le_closure_fixed_aux (hgold : CFSG.Goldschmidt.TopStatement) (P : D4Par n X σ)
    (hn : 2 ≤ n) {E : Subgroup (MulAut (C0 σ))} (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 27)
    (hno : ∀ φ : MulAut (C0 σ), tauAut σ ∉ E.map (MulAut.congr φ).toMonoidHom)
    {x : C0 σ} (hx : MulAut.conj x ∈ E) (hx1 : x ≠ 1) :
    ⁅Subgroup.centralizer ({x} : Set (C0 σ)), Subgroup.centralizer ({x} : Set (C0 σ))⁆ ≤
      Subgroup.closure
        {l | l ∈ ⁅Subgroup.centralizer ({x} : Set (C0 σ)),
              Subgroup.centralizer ({x} : Set (C0 σ))⁆ ∧
          ∃ y ∈ E, y ∉ Subgroup.zpowers (MulAut.conj x : MulAut (C0 σ)) ∧ y l = l} := by
  haveI : Finite (C0 σ) := finite_C0
  have hxX : IsClassX σ x := classX_of_no_conj_tau hgold P hn hE hcard hno hx hx1
  obtain ⟨hx3, -, g₀, hg₀⟩ := hxX
  have hx₁3 : (g₀ * x * g₀⁻¹) ^ 3 = 1 := by
    rw [← MulAut.conj_apply, ← map_pow, hx3, map_one]
  have hx₁1 : g₀ * x * g₀⁻¹ ≠ 1 := fun h1 =>
    hx1 ((MulAut.conj g₀).injective (by rw [MulAut.conj_apply, h1, map_one]))
  obtain ⟨g₁, -, hg₁⟩ := exists_conj_A0 P hg₀ hx₁3 hx₁1
  set h : C0 σ := g₁ * g₀ with hh
  have hxh : h * x * h⁻¹ ∈ A0sub σ := by
    have : h * x * h⁻¹ = g₁ * (g₀ * x * g₀⁻¹) * g₁⁻¹ := by rw [hh]; group
    rw [this]
    exact hg₁
  set φ : MulAut (C0 σ) := MulAut.conj h with hφ
  set E' : Subgroup (MulAut (C0 σ)) := E.map (MulAut.congr φ).toMonoidHom with hE'
  have hE'ab : IsElemAbelian 3 E' := CFSG.Open.IsElemAbelian.map hE _
  have hE'card : Nat.card E' = 27 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.congr φ).injective, hcard]
  have hno' : ∀ ψ : MulAut (C0 σ), tauAut σ ∉ E'.map (MulAut.congr ψ).toMonoidHom := by
    intro ψ hψ
    apply hno (ψ * φ)
    rw [congr_mul_toMonoidHom, ← Subgroup.map_map]
    exact hψ
  have hx'E : MulAut.conj (h * x * h⁻¹) ∈ E' := ⟨MulAut.conj x, hx, congr_conj_conj h x⟩
  have hx'1 : h * x * h⁻¹ ≠ 1 := fun h1 =>
    hx1 ((MulAut.conj h).injective (by rw [MulAut.conj_apply, h1, map_one]))
  have key := layer_le_closure_fixed_A0 hgold P hn hE'ab hE'card hno' hx'E hx'1 hxh
  have hback := stepOK_map (MulAut.conj h⁻¹) key
  have ha := layer_map_conj σ h x
  have hb : E'.map (MulAut.congr (MulAut.conj h⁻¹)).toMonoidHom = E := by
    ext z
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      have : (MulAut.congr (MulAut.conj h⁻¹)) ((MulAut.congr φ) y) = y := by
        rw [hφ, congr_apply_eq, congr_apply_eq]
        simp [map_inv]
        group
      show (MulAut.congr (MulAut.conj h⁻¹)) ((MulAut.congr φ) y) ∈ E
      rw [this]
      exact hy
    · intro hz
      refine ⟨(MulAut.congr φ) z, ⟨z, hz, rfl⟩, ?_⟩
      show (MulAut.congr (MulAut.conj h⁻¹)) ((MulAut.congr φ) z) = z
      rw [hφ, congr_apply_eq, congr_apply_eq]
      simp [map_inv]
      group
  have hc : (MulAut.congr (MulAut.conj h⁻¹)) (MulAut.conj (h * x * h⁻¹)) = MulAut.conj x := by
    rw [congr_conj_conj]
    congr 1
    group
  rw [ha, hb, hc] at hback
  exact hback

end StepALayerAux

end CFSG.RankThree.PartTwo.Sec4.E27
