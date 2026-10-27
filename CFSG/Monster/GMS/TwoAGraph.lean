module

public import CFSG.Monster.GMS.AmalgamIso

public section

namespace CFSG.Monster.GMS

open CFSG.Monster.B.Recog

variable {G : Type*} [Group G]

abbrev ConjVert (a : G) : Type _ := {x : G // IsConj a x}

theorem isConj_conj {a x : G} (h : IsConj a x) (g : G) : IsConj a (g * x * g⁻¹) :=
  h.trans (isConj_iff.mpr ⟨g, rfl⟩)

instance conjVertMulAction (a : G) : MulAction G (ConjVert a) where
  smul g x := ⟨g * x.1 * g⁻¹, isConj_conj x.2 g⟩
  one_smul x := by
    apply Subtype.ext
    show (1 : G) * x.1 * 1⁻¹ = x.1
    simp
  mul_smul g h x := by
    apply Subtype.ext
    show g * h * x.1 * (g * h)⁻¹ = g * (h * x.1 * h⁻¹) * g⁻¹
    group

@[simp]
theorem coe_smul_conjVert {a : G} (g : G) (x : ConjVert a) :
    ((g • x : ConjVert a) : G) = g * x * g⁻¹ := rfl

@[expose] def twoAGraph (a : G) : SimpleGraph (ConjVert a) where
  Adj x y := x ≠ y ∧ IsConj a ((x : G) * y)
  symm := ⟨fun x y h => ⟨h.1.symm, h.2.trans (isConj_iff.mpr ⟨(x : G)⁻¹, by group⟩)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem twoAGraph_adj {a : G} {x y : ConjVert a} :
    (twoAGraph a).Adj x y ↔ x ≠ y ∧ IsConj a ((x : G) * y) := Iff.rfl

theorem twoAGraph_adj_smul {a : G} (g : G) {x y : ConjVert a} (h : (twoAGraph a).Adj x y) :
    (twoAGraph a).Adj (g • x) (g • y) := by
  refine ⟨fun hxy => h.1 (smul_left_cancel g hxy), ?_⟩
  have : (g * x * g⁻¹) * (g * y * g⁻¹) = g * ((x : G) * y) * g⁻¹ := by group
  simp only [coe_smul_conjVert, this]
  exact isConj_conj h.2 g

theorem smul_eq_self_iff {a : G} (g : G) (x : ConjVert a) :
    g • x = x ↔ g ∈ Subgroup.centralizer ({(x : G)} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← Subtype.coe_inj, coe_smul_conjVert]
  constructor
  · intro h
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [h]
  · intro h
    calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [h]
      _ = x := by group

@[expose] def edgeStab {a : G} (v w : ConjVert a) : Subgroup G where
  carrier := {g | (g • v = v ∧ g • w = w) ∨ (g • v = w ∧ g • w = v)}
  one_mem' := Or.inl ⟨one_smul _ _, one_smul _ _⟩
  mul_mem' := by
    rintro g h (⟨hgv, hgw⟩ | ⟨hgv, hgw⟩) (⟨hhv, hhw⟩ | ⟨hhv, hhw⟩)
    · exact Or.inl ⟨by rw [mul_smul, hhv, hgv], by rw [mul_smul, hhw, hgw]⟩
    · exact Or.inr ⟨by rw [mul_smul, hhv, hgw], by rw [mul_smul, hhw, hgv]⟩
    · exact Or.inr ⟨by rw [mul_smul, hhv, hgv], by rw [mul_smul, hhw, hgw]⟩
    · exact Or.inl ⟨by rw [mul_smul, hhv, hgw], by rw [mul_smul, hhw, hgv]⟩
  inv_mem' := by
    rintro g (⟨hv, hw⟩ | ⟨hv, hw⟩)
    · exact Or.inl ⟨by rw [inv_smul_eq_iff, hv], by rw [inv_smul_eq_iff, hw]⟩
    · exact Or.inr ⟨by rw [inv_smul_eq_iff, hw], by rw [inv_smul_eq_iff, hv]⟩

theorem mem_edgeStab {a : G} {v w : ConjVert a} {g : G} :
    g ∈ edgeStab v w ↔ (g • v = v ∧ g • w = w) ∨ (g • v = w ∧ g • w = v) := Iff.rfl

@[expose] def titsData_twoAGraph {a : G} {ι : Type*} (v w : ConjVert a)
    (hvw : (twoAGraph a).Adj v w) (hconn : (twoAGraph a).Preconnected)
    (hΓ : Triangulable (twoAGraph a))
    (harc : ∀ x y x' y', (twoAGraph a).Adj x y → (twoAGraph a).Adj x' y' →
      ∃ g : G, g • x = x' ∧ g • y = y')
    (u : ι → ConjVert a) (Xt : ι → Subgroup G)
    (hXt : ∀ j, ∀ g ∈ Xt j, g • v = v ∨ g • v = w ∨ g • v = u j)
    (hτ : ∀ j, ∃ g ∈ Xt j, g • v = w ∧ g • w = v)
    (hρ : ∀ j, ∃ g ∈ Xt j, g • v = w ∧ g • w = u j ∧ g • u j = v)
    (htri : ∀ y₁ y₂, (twoAGraph a).Adj v y₁ → (twoAGraph a).Adj y₁ y₂ →
      (twoAGraph a).Adj y₂ v → ∃ j, ∃ g : G, g • v = v ∧ g • w = y₁ ∧ g • u j = y₂) :
    TitsData (twoAGraph a) G ι where
  v := v
  w := w
  u := u
  Xv := Subgroup.centralizer ({(v : G)} : Set G)
  Xe := edgeStab v w
  Xt := Xt
  hadj g _ _ h := twoAGraph_adj_smul g h
  hconn := hconn
  hΓ := hΓ
  hvw := hvw
  hloc y hy := harc v w v y hvw hy
  hswap := harc v w w v hvw hvw.symm
  hXv g := (smul_eq_self_iff g v).symm
  hXe _ := mem_edgeStab
  hXt := hXt
  hτ := hτ
  hρ := hρ
  htri := htri

end CFSG.Monster.GMS
