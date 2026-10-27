module

public import CFSG.RankThree.GF2n.Smith81.S81UModelDef

public section

namespace CFSG.RankThree.GF2n.Smith81.U6Cube

open CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.A5Cube Matrix exteriorPower
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
open scoped commutatorElement

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F}

theorem mem_Gcent_conj_iff (g t h : SUid σ 6) :
    h ∈ Gcent σ (g * t * g⁻¹) ↔ g⁻¹ * h * g ∈ Gcent σ t := by
  simp only [Gcent, Set.mem_setOf_eq]
  constructor
  · intro H
    calc g⁻¹ * h * g * t = g⁻¹ * (h * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * t * g⁻¹ * h) * g := by rw [H]
      _ = t * (g⁻¹ * h * g) := by group
  · intro H
    calc h * (g * t * g⁻¹) = g * (g⁻¹ * h * g * t) * g⁻¹ := by group
      _ = g * (t * (g⁻¹ * h * g)) * g⁻¹ := by rw [H]
      _ = g * t * g⁻¹ * h := by group

private theorem h79_Wact_mul3 (a b c : SUid σ 6) (y : Wform σ) :
    Wact σ (a * b * c) y = Wact σ a (Wact σ b (Wact σ c y)) := by
  rw [map_mul, map_mul]
  rfl

private theorem h79_Wact_inv_apply (g : SUid σ 6) (x : Wform σ) :
    Wact σ g⁻¹ (Wact σ g x) = x := by
  have h1 : Wact σ g⁻¹ * Wact σ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  calc Wact σ g⁻¹ (Wact σ g x) = (Wact σ g⁻¹ * Wact σ g) x := rfl
    _ = (1 : Wform σ ≃ₗ[Fσ σ] Wform σ) x := by rw [h1]
    _ = x := rfl

private theorem h79_Wact_apply_inv (g : SUid σ 6) (x : Wform σ) :
    Wact σ g (Wact σ g⁻¹ x) = x := by
  have h1 : Wact σ g * Wact σ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  calc Wact σ g (Wact σ g⁻¹ x) = (Wact σ g * Wact σ g⁻¹) x := rfl
    _ = (1 : Wform σ ≃ₗ[Fσ σ] Wform σ) x := by rw [h1]
    _ = x := rfl

private theorem h79_Wact_conj_apply (g x : SUid σ 6) (w : Wform σ) :
    Wact σ (g * x * g⁻¹) (Wact σ g w) = Wact σ g (Wact σ x w) := by
  rw [h79_Wact_mul3, h79_Wact_inv_apply]

private theorem h79_conj_mem (g t x : SUid σ 6) (hx : x ∈ Gcent σ t) :
    g * x * g⁻¹ ∈ Gcent σ (g * t * g⁻¹) := by
  rw [mem_Gcent_conj_iff]
  have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  rw [e]
  exact hx

theorem mem_Cw_conj_iff (g t : SUid σ 6) (c : Wform σ) :
    c ∈ Cw σ (g * t * g⁻¹) ↔ Wact σ g⁻¹ c ∈ Cw σ t := by
  simp only [Cw, Set.mem_setOf_eq]
  rw [h79_Wact_mul3]
  constructor
  · intro H
    calc Wact σ t (Wact σ g⁻¹ c) = Wact σ g⁻¹ (Wact σ g (Wact σ t (Wact σ g⁻¹ c))) :=
          (h79_Wact_inv_apply g _).symm
      _ = Wact σ g⁻¹ c := by rw [H]
  · intro H
    rw [H, h79_Wact_apply_inv]

theorem mem_Rw_conj_iff (g t : SUid σ 6) (r : Wform σ) :
    r ∈ Rw σ (g * t * g⁻¹) ↔ Wact σ g⁻¹ r ∈ Rw σ t := by
  simp only [Rw, Set.mem_setOf_eq]
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨Wact σ g⁻¹ w, ?_⟩
    rw [map_sub (Wact σ g⁻¹), h79_Wact_mul3, h79_Wact_inv_apply]
  · rintro ⟨w₀, hw₀⟩
    refine ⟨Wact σ g w₀, ?_⟩
    rw [h79_Wact_mul3, h79_Wact_inv_apply, ← map_sub (Wact σ g), ← hw₀, h79_Wact_apply_inv]

private theorem h79_closure_map (e : Wform σ ≃ₗ[Fσ σ] Wform σ) (T T' : Set (Wform σ))
    (hT : ∀ v ∈ T, e v ∈ AddSubgroup.closure T') {w : Wform σ}
    (hw : w ∈ AddSubgroup.closure T) : e w ∈ AddSubgroup.closure T' := by
  let wgHom : Wform σ →+ Wform σ := AddMonoidHom.mk' (fun s => e s) (fun x y => map_add e x y)
  have hle : AddSubgroup.closure T ≤ (AddSubgroup.closure T').comap wgHom := by
    rw [AddSubgroup.closure_le]
    intro v hv
    exact hT v hv
  exact hle hw

private theorem h79_gen_covW (g t : SUid σ 6) :
    ∀ v ∈ {v : Wform σ | ∃ x ∈ Gcent σ t, ∃ w' : Wform σ, v = Wact σ x w' - w'},
      Wact σ g v ∈ AddSubgroup.closure
        {v : Wform σ | ∃ x ∈ Gcent σ (g * t * g⁻¹), ∃ w' : Wform σ, v = Wact σ x w' - w'} := by
  rintro v ⟨x, hx, w', rfl⟩
  apply AddSubgroup.subset_closure
  refine ⟨g * x * g⁻¹, h79_conj_mem g t x hx, Wact σ g w', ?_⟩
  rw [map_sub (Wact σ g), h79_Wact_conj_apply]

private theorem h79_gen_covC (g t : SUid σ 6) :
    ∀ v ∈ {v : Wform σ | ∃ x ∈ Gcent σ t, ∃ c' ∈ Cw σ t, v = Wact σ x c' - c'},
      Wact σ g v ∈ AddSubgroup.closure
        {v : Wform σ | ∃ x ∈ Gcent σ (g * t * g⁻¹), ∃ c' ∈ Cw σ (g * t * g⁻¹),
          v = Wact σ x c' - c'} := by
  rintro v ⟨x, hx, c', hc', rfl⟩
  apply AddSubgroup.subset_closure
  have hc'' : Wact σ g c' ∈ Cw σ (g * t * g⁻¹) := by
    rw [mem_Cw_conj_iff, h79_Wact_inv_apply]
    exact hc'
  refine ⟨g * x * g⁻¹, h79_conj_mem g t x hx, Wact σ g c', hc'', ?_⟩
  rw [map_sub (Wact σ g), h79_Wact_conj_apply]

private theorem h79_covW_conj (g t : SUid σ 6) (h : UInvolModel12 σ t) :
    ∀ w : Wform σ, w ∈ AddSubgroup.closure
      {v | ∃ x ∈ Gcent σ (g * t * g⁻¹), ∃ w' : Wform σ, v = Wact σ x w' - w'} := by
  intro w
  have hw := h79_closure_map (Wact σ g) _ _ (h79_gen_covW g t) (h.covW (Wact σ g⁻¹ w))
  rwa [h79_Wact_apply_inv] at hw

private theorem h79_covC_conj (g t : SUid σ 6) (h : UInvolModel12 σ t) :
    ∀ c ∈ Cw σ (g * t * g⁻¹), ∃ r ∈ Rw σ (g * t * g⁻¹),
      c - r ∈ AddSubgroup.closure
        {v | ∃ x ∈ Gcent σ (g * t * g⁻¹), ∃ c' ∈ Cw σ (g * t * g⁻¹), v = Wact σ x c' - c'} := by
  intro c hc
  have hc₀ : Wact σ g⁻¹ c ∈ Cw σ t := (mem_Cw_conj_iff g t c).mp hc
  obtain ⟨r₀, hr₀, hcr₀⟩ := h.covC _ hc₀
  refine ⟨Wact σ g r₀, ?_, ?_⟩
  · rw [mem_Rw_conj_iff, h79_Wact_inv_apply]
    exact hr₀
  · have hm := h79_closure_map (Wact σ g) _ _ (h79_gen_covC g t) hcr₀
    rw [map_sub (Wact σ g), h79_Wact_apply_inv] at hm
    exact hm

private theorem h79_P3_conj (g t : SUid σ 6) (h : UInvolModel12 σ t) :
    ∃ U : Set (SUid σ 6), (∀ u ∈ U, u ∈ Gcent σ (g * t * g⁻¹)) ∧
      (∀ u ∈ U, ∀ c ∈ Cw σ (g * t * g⁻¹), Wact σ u c - c ∈ Rw σ (g * t * g⁻¹)) ∧
      ∀ c ∈ Cw σ (g * t * g⁻¹), (∀ u ∈ U, Wact σ u c = c) → c ∈ Rw σ (g * t * g⁻¹) := by
  obtain ⟨U, hUc, hUR, hUC⟩ := h.P3
  refine ⟨{u' | g⁻¹ * u' * g ∈ U}, ?_, ?_, ?_⟩
  · intro u' hu'
    exact (mem_Gcent_conj_iff g t u').mpr (hUc (g⁻¹ * u' * g) hu')
  · intro u' hu' c hc
    have hc₀ : Wact σ g⁻¹ c ∈ Cw σ t := (mem_Cw_conj_iff g t c).mp hc
    have e1 : Wact σ (g⁻¹ * u' * g) (Wact σ g⁻¹ c) = Wact σ g⁻¹ (Wact σ u' c) := by
      rw [h79_Wact_mul3, h79_Wact_apply_inv]
    rw [mem_Rw_conj_iff, map_sub (Wact σ g⁻¹), ← e1]
    exact hUR (g⁻¹ * u' * g) hu' (Wact σ g⁻¹ c) hc₀
  · intro c hc hcU
    have hc₀ : Wact σ g⁻¹ c ∈ Cw σ t := (mem_Cw_conj_iff g t c).mp hc
    rw [mem_Rw_conj_iff]
    apply hUC _ hc₀
    intro u hu
    have hu' : g * u * g⁻¹ ∈ {u' : SUid σ 6 | g⁻¹ * u' * g ∈ U} := by
      show g⁻¹ * (g * u * g⁻¹) * g ∈ U
      have e : g⁻¹ * (g * u * g⁻¹) * g = u := by group
      rw [e]
      exact hu
    have hfix : Wact σ (g * u * g⁻¹) c = c := hcU (g * u * g⁻¹) hu'
    have e2 : Wact σ g⁻¹ (Wact σ (g * u * g⁻¹) c) = Wact σ u (Wact σ g⁻¹ c) := by
      rw [h79_Wact_mul3, h79_Wact_inv_apply]
    rw [← e2, hfix]

private theorem h79_P2_conj (g t : SUid σ 6) (h : UInvolModel12 σ t) :
    ∀ S : AddSubgroup (Wform σ), S ≠ ⊥ → (∀ s ∈ S, s ∈ Rw σ (g * t * g⁻¹)) →
      (∀ a ∈ Gcent σ (g * t * g⁻¹), ∀ b ∈ Gcent σ (g * t * g⁻¹), ∀ s ∈ S,
        Wact σ ⁅a, b⁆ s ∈ S) →
      ∃ p ∈ S, p ≠ 0 ∧ (p : Cube F) ∈ RootPt σ := by
  intro S hS hSR hSc
  let wgHom : Wform σ →+ Wform σ :=
    AddMonoidHom.mk' (fun s => Wact σ g s) (fun x y => map_add (Wact σ g) x y)
  let S' : AddSubgroup (Wform σ) := S.comap wgHom
  have hmem : ∀ s, s ∈ S' ↔ Wact σ g s ∈ S := fun s => Iff.rfl
  obtain ⟨s₀, hs₀, hs₀0⟩ : ∃ s₀ ∈ S, s₀ ≠ 0 := by
    by_contra hcon
    apply hS
    ext x
    rw [AddSubgroup.mem_bot]
    constructor
    · intro hx
      by_contra hx0
      exact hcon ⟨x, hx, hx0⟩
    · rintro rfl
      exact S.zero_mem
  have hS'ne : S' ≠ ⊥ := by
    intro hbot
    have hm : Wact σ g⁻¹ s₀ ∈ S' := by
      rw [hmem, h79_Wact_apply_inv]
      exact hs₀
    rw [hbot, AddSubgroup.mem_bot] at hm
    apply hs₀0
    calc s₀ = Wact σ g (Wact σ g⁻¹ s₀) := (h79_Wact_apply_inv g s₀).symm
      _ = Wact σ g 0 := by rw [hm]
      _ = 0 := map_zero (Wact σ g)
  have hS'R : ∀ s ∈ S', s ∈ Rw σ t := by
    intro s hs
    have h1 : Wact σ g s ∈ Rw σ (g * t * g⁻¹) := hSR (Wact σ g s) ((hmem s).mp hs)
    have h2 := (mem_Rw_conj_iff g t (Wact σ g s)).mp h1
    rwa [h79_Wact_inv_apply] at h2
  have hS'comm : ∀ a ∈ Gcent σ t, ∀ b ∈ Gcent σ t, ∀ s ∈ S', Wact σ ⁅a, b⁆ s ∈ S' := by
    intro a ha b hb s hs
    rw [hmem]
    have hcomm : ⁅g * a * g⁻¹, g * b * g⁻¹⁆ = g * ⁅a, b⁆ * g⁻¹ := by
      simp only [commutatorElement_def]
      group
    have e3 : Wact σ g (Wact σ ⁅a, b⁆ s) =
        Wact σ ⁅g * a * g⁻¹, g * b * g⁻¹⁆ (Wact σ g s) := by
      rw [hcomm, h79_Wact_conj_apply]
    rw [e3]
    exact hSc (g * a * g⁻¹) (h79_conj_mem g t a ha) (g * b * g⁻¹) (h79_conj_mem g t b hb)
      (Wact σ g s) ((hmem s).mp hs)
  obtain ⟨p, hpS', hp0, hpR⟩ := h.P2 S' hS'ne hS'R hS'comm
  have hpS : Wact σ g p ∈ S := (hmem p).mp hpS'
  refine ⟨Wact σ g p, hpS, ?_, ?_⟩
  · intro h0
    apply hp0
    calc p = Wact σ g⁻¹ (Wact σ g p) := (h79_Wact_inv_apply g p).symm
      _ = Wact σ g⁻¹ 0 := by rw [h0]
      _ = 0 := map_zero (Wact σ g⁻¹)
  · rw [Wact_apply]
    exact rho_mem_RootPt g.2 hpR

theorem UInvolModel12.conj (hσ : IsUnitaryInvolution σ) (g : SUid σ 6) {t : SUid σ 6}
    (h : UInvolModel12 σ t) : UInvolModel12 σ (g * t * g⁻¹) := by
  exact ⟨h79_covW_conj g t h, h79_covC_conj g t h, h79_P3_conj g t h, h79_P2_conj g t h⟩

theorem UInvolModel3.conj (hσ : IsUnitaryInvolution σ) (g : SUid σ 6) {t : SUid σ 6}
    (h : UInvolModel3 σ t) : UInvolModel3 σ (g * t * g⁻¹) := by
  refine ⟨?_, ?_⟩
  · intro c hc
    exact (mem_Rw_conj_iff g t c).mpr (h.CR _ ((mem_Cw_conj_iff g t c).mp hc))
  · obtain ⟨p₁, p₂, hp₁, hp₂, hp₁₂, hβ⟩ := h.beta_ne
    refine ⟨Wact σ g p₁, Wact σ g p₂, ?_, ?_, ?_, ?_⟩
    · rw [Wact_apply]
      exact rho_mem_RootPt g.2 hp₁
    · rw [Wact_apply]
      exact rho_mem_RootPt g.2 hp₂
    · rw [mem_Rw_conj_iff, ← map_add (Wact σ g), h79_Wact_inv_apply]
      exact hp₁₂
    · have hdet : ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).det = 1 :=
        ((mem_SUid_iff σ).mp g.2).1
      rw [Wact_apply, Wact_apply, beta_rho, hdet, one_mul]
      exact hβ

end CFSG.RankThree.GF2n.Smith81.U6Cube
