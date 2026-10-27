module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL4Ext
public import CFSG.Quasithin.Background.F6GoldschmidtList

public section

namespace CFSG.Quasithin.F6.GoldAmL5

open CFSG.Quasithin.F6.GoldAmL4

variable {P D E : Type*} [Group P] [Group D] [Group E]

open Classical in
noncomputable def coordOf (emb : P →* D) : D → P := Function.invFun emb

theorem coordOf_emb {emb : P →* D} (hinj : Function.Injective emb) (x : P) :
    coordOf emb (emb x) = x :=
  Function.leftInverse_invFun hinj x

theorem emb_coordOf {emb : P →* D} {d : D} (hd : d ∈ emb.range) : emb (coordOf emb d) = d :=
  Function.invFun_eq (by simpa using hd)

theorem coordOf_mul {emb : P →* D} (hinj : Function.Injective emb) {t₁ t₂ : D}
    (h₁ : t₁ ∈ emb.range) (h₂ : t₂ ∈ emb.range) :
    coordOf emb (t₁ * t₂) = coordOf emb t₁ * coordOf emb t₂ := by
  apply hinj
  rw [map_mul, emb_coordOf h₁, emb_coordOf h₂, emb_coordOf (emb.range.mul_mem h₁ h₂)]

structure VertexSpecG (emb : P →* D) (Qc : Subgroup P) (t₀c : P) (y : D) (act : P → P)
    (u₁ u₂ : P) : Prop where
  y_cube : y ^ 3 = 1
  y_not_mem : y ∉ emb.range
  act_mem : ∀ w ∈ Qc, act w ∈ Qc
  conj : ∀ w ∈ Qc, y⁻¹ * emb w * y = emb (act w)
  t₁ : y * emb t₀c * y = emb u₁
  t₂ : y⁻¹ * emb t₀c * y⁻¹ = emb u₂

namespace VertexSpecG

variable {emb : P →* D} {Qc : Subgroup P} {t₀c : P} {y : D} {act : P → P} {u₁ u₂ : P}
  (hv : VertexSpecG emb Qc t₀c y act u₁ u₂)

include hv

theorem yy : y * y = y⁻¹ := by
  rw [eq_inv_iff_mul_eq_one]
  calc y * y * y = y ^ 3 := by rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two]
    _ = 1 := hv.y_cube

theorem yy' : y⁻¹ * y⁻¹ = y := by
  have := congrArg Inv.inv hv.yy
  simpa using this

theorem conj_pos {w : P} (hw : w ∈ Qc) : y * emb w * y⁻¹ = emb (act (act w)) := by
  have e1 := hv.conj w hw
  have e2 := hv.conj _ (hv.act_mem w hw)
  calc y * emb w * y⁻¹ = (y⁻¹ * y⁻¹) * emb w * (y * y) := by rw [hv.yy', hv.yy]
    _ = y⁻¹ * (y⁻¹ * emb w * y) * y := by group
    _ = emb (act (act w)) := by rw [e1, e2]

theorem ext3Data (hQ : ∀ w : P, w ∈ Qc ∨ w * t₀c⁻¹ ∈ Qc) :
    Ext3Data emb.range (Qc.map emb) y (emb t₀c) := by
  have hconj' : ∀ q ∈ Qc.map emb, y⁻¹ * q * y ∈ Qc.map emb := by
    intro q hq
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hq
    rw [hv.conj w hw]
    exact Subgroup.mem_map_of_mem _ (hv.act_mem w hw)
  refine ⟨Subgroup.map_le_range _ _, hv.y_cube, hv.y_not_mem, ⟨t₀c, rfl⟩, ?_, ?_, hconj', ?_, ?_⟩
  · rintro t ⟨w, rfl⟩
    rcases hQ w with hw | hw
    · exact Or.inl (Subgroup.mem_map_of_mem _ hw)
    · refine Or.inr ?_
      rw [← map_inv, ← map_mul]
      exact Subgroup.mem_map_of_mem _ hw
  · intro q hq
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hq
    rw [hv.conj_pos hw]
    exact Subgroup.mem_map_of_mem _ (hv.act_mem _ (hv.act_mem w hw))
  · rw [hv.t₁]; exact ⟨u₁, rfl⟩
  · rw [hv.t₂]; exact ⟨u₂, rfl⟩

end VertexSpecG

namespace VertexSpecG

variable {emb : P →* D} {emb' : P →* E} {Qc : Subgroup P} {t₀c : P} {y : D} {y' : E}
  {act : P → P} {u₁ u₂ : P}

theorem ext3Compat (hinj : Function.Injective emb) (hinj' : Function.Injective emb')
    (hv : VertexSpecG emb Qc t₀c y act u₁ u₂) (hv' : VertexSpecG emb' Qc t₀c y' act u₁ u₂) :
    Ext3Compat emb.range (Qc.map emb) emb'.range y (emb t₀c) y'
      (fun d => emb' (coordOf emb d)) := by
  have hι : ∀ x : P, emb' (coordOf emb (emb x)) = emb' x := fun x => by
    rw [coordOf_emb hinj]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t₁ h₁ t₂ h₂
    show emb' (coordOf emb (t₁ * t₂)) = emb' (coordOf emb t₁) * emb' (coordOf emb t₂)
    rw [coordOf_mul hinj h₁ h₂, map_mul]
  · intro t _
    exact ⟨coordOf emb t, rfl⟩
  · intro t₁ h₁ t₂ h₂ e
    have e' : coordOf emb t₁ = coordOf emb t₂ := hinj' e
    rw [← emb_coordOf h₁, ← emb_coordOf h₂, e']
  · rintro _ ⟨x, rfl⟩
    exact ⟨emb x, ⟨x, rfl⟩, hι x⟩
  · intro q hq
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hq
    show emb' (coordOf emb (y * emb w * y⁻¹)) = y' * emb' (coordOf emb (emb w)) * y'⁻¹
    rw [hv.conj_pos hw, hι, hι, hv'.conj_pos hw]
  · show emb' (coordOf emb (y * emb t₀c * y)) = y' * emb' (coordOf emb (emb t₀c)) * y'
    rw [hv.t₁, hι, hι, hv'.t₁]
  · show emb' (coordOf emb (y⁻¹ * emb t₀c * y⁻¹)) =
      y'⁻¹ * emb' (coordOf emb (emb t₀c)) * y'⁻¹
    rw [hv.t₂, hι, hι, hv'.t₂]

theorem vertex_iso (hinj : Function.Injective emb) (hinj' : Function.Injective emb')
    (hQ : ∀ w : P, w ∈ Qc ∨ w * t₀c⁻¹ ∈ Qc)
    (hv : VertexSpecG emb Qc t₀c y act u₁ u₂) (hv' : VertexSpecG emb' Qc t₀c y' act u₁ u₂) :
    ∃ φ : ↥(Subgroup.closure ((emb.range : Set D) ∪ {y})) ≃*
        ↥(Subgroup.closure ((emb'.range : Set E) ∪ {y'})),
      (∀ w : P, ((φ ⟨emb w, Subgroup.subset_closure (Or.inl ⟨w, rfl⟩)⟩ :
        ↥(Subgroup.closure ((emb'.range : Set E) ∪ {y'}))) : E) = emb' w) ∧
      ((φ ⟨y, Subgroup.subset_closure (Or.inr rfl)⟩ :
        ↥(Subgroup.closure ((emb'.range : Set E) ∪ {y'}))) : E) = y' := by
  obtain ⟨φ, hφ, hφy⟩ := (hv.ext3Data hQ).exists_mulEquiv (ext3Compat hinj hinj' hv hv')
    hv'.y_cube hv'.y_not_mem
  refine ⟨φ, fun w => ?_, hφy⟩
  rw [hφ _ ⟨w, rfl⟩]
  show emb' (coordOf emb (emb w)) = emb' w
  rw [coordOf_emb hinj]

end VertexSpecG

theorem isAmalgamIso_of_specs {emb : P →* D} {emb' : P →* E}
    (hinj : Function.Injective emb) (hinj' : Function.Injective emb')
    {Q₁ Q₂ : Subgroup P} {t₁ t₂ : P} {act₁ act₂ : P → P} {u₁ u₂ v₁ v₂ : P} {y x : D} {y' x' : E}
    (hQ₁ : ∀ w : P, w ∈ Q₁ ∨ w * t₁⁻¹ ∈ Q₁) (hQ₂ : ∀ w : P, w ∈ Q₂ ∨ w * t₂⁻¹ ∈ Q₂)
    (hy : VertexSpecG emb Q₁ t₁ y act₁ u₁ u₂) (hy' : VertexSpecG emb' Q₁ t₁ y' act₁ u₁ u₂)
    (hx : VertexSpecG emb Q₂ t₂ x act₂ v₁ v₂) (hx' : VertexSpecG emb' Q₂ t₂ x' act₂ v₁ v₂)
    (hinf : Subgroup.closure ((emb.range : Set D) ∪ {y}) ⊓
      Subgroup.closure ((emb.range : Set D) ∪ {x}) = emb.range)
    (hinf' : Subgroup.closure ((emb'.range : Set E) ∪ {y'}) ⊓
      Subgroup.closure ((emb'.range : Set E) ∪ {x'}) = emb'.range) :
    CFSG.Quasithin.F6.IsAmalgamIso (Subgroup.closure ((emb.range : Set D) ∪ {y}))
      (Subgroup.closure ((emb.range : Set D) ∪ {x}))
      (Subgroup.closure ((emb'.range : Set E) ∪ {y'}))
      (Subgroup.closure ((emb'.range : Set E) ∪ {x'})) := by
  obtain ⟨φ₁, hφ₁, -⟩ := hy.vertex_iso hinj hinj' hQ₁ hy'
  obtain ⟨φ₂, hφ₂, -⟩ := hx.vertex_iso hinj hinj' hQ₂ hx'
  refine ⟨φ₁, φ₂, ?_, ?_⟩
  · intro g hg₁ hg₂
    have hgT : g ∈ emb.range := by
      rw [← hinf]; exact ⟨hg₁, hg₂⟩
    obtain ⟨w, rfl⟩ := hgT
    rw [hφ₁ w, hφ₂ w]
  · intro g hg₁ hg₂
    have hgT : g ∈ emb'.range := by
      rw [← hinf']; exact ⟨hg₁, hg₂⟩
    obtain ⟨w, rfl⟩ := hgT
    have hm₁ : emb w ∈ Subgroup.closure ((emb.range : Set D) ∪ {y}) :=
      Subgroup.subset_closure (Or.inl ⟨w, rfl⟩)
    have hm₂ : emb w ∈ Subgroup.closure ((emb.range : Set D) ∪ {x}) :=
      Subgroup.subset_closure (Or.inl ⟨w, rfl⟩)
    have e₁ : φ₁.symm ⟨emb' w, hg₁⟩ = ⟨emb w, hm₁⟩ := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext (hφ₁ w).symm
    have e₂ : φ₂.symm ⟨emb' w, hg₂⟩ = ⟨emb w, hm₂⟩ := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext (hφ₂ w).symm
    rw [e₁, e₂]

end CFSG.Quasithin.F6.GoldAmL5
