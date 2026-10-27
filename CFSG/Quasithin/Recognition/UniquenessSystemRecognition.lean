module

public import CFSG.Quasithin.Recognition.UniquenessSystemLift
public import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.GroupTheory.GroupAction.Quotient

public section

namespace CFSG.Quasithin.Asc94

open MulAction
open scoped Pointwise

universe u v u' v'

variable {G : Type v} [Group G] {X : Type u} [MulAction G X]
  {Gb : Type v'} [Group Gb] {Xb : Type u'} [MulAction Gb Xb]
  {x y : X} {xb yb : Xb} {I : Subgroup G} {Ib : Subgroup Gb}

section Construction

variable (β : stabilizer G x ≃* stabilizer Gb xb) (ζ : I ≃* Ib)

@[expose] def graphβ : stabilizer G x →* G × Gb :=
  (stabilizer G x).subtype.prod ((stabilizer Gb xb).subtype.comp β.toMonoidHom)

@[expose] def graphζ : I →* G × Gb := I.subtype.prod (Ib.subtype.comp ζ.toMonoidHom)

@[simp] theorem graphβ_apply (a : stabilizer G x) : graphβ β a = ((a : G), (β a : Gb)) := rfl

@[simp] theorem graphζ_apply (i : I) : graphζ ζ i = ((i : G), (ζ i : Gb)) := rfl

@[expose] def recD : Subgroup (G × Gb) := (graphβ β).range ⊔ (graphζ ζ).range

@[expose] def recDx : Subgroup (recD β ζ) := (graphβ β).range.subgroupOf (recD β ζ)

theorem graphβ_mem (a : stabilizer G x) : graphβ β a ∈ recD β ζ :=
  le_sup_left (a := (graphβ β).range) (MonoidHom.mem_range.mpr ⟨a, rfl⟩)

theorem graphζ_mem (i : I) : graphζ ζ i ∈ recD β ζ :=
  le_sup_right (b := (graphζ ζ).range) (MonoidHom.mem_range.mpr ⟨i, rfl⟩)

@[expose] def dβ (a : stabilizer G x) : recD β ζ := ⟨graphβ β a, graphβ_mem β ζ a⟩

@[expose] def dζ (i : I) : recD β ζ := ⟨graphζ ζ i, graphζ_mem β ζ i⟩

theorem dζ_mul (i j : I) : dζ β ζ (i * j) = dζ β ζ i * dζ β ζ j :=
  Subtype.ext (map_mul (graphζ ζ) i j)

theorem dβ_mem_recDx (a : stabilizer G x) : dβ β ζ a ∈ recDx β ζ :=
  Subgroup.mem_subgroupOf.mpr (MonoidHom.mem_range.mpr ⟨a, rfl⟩)

theorem mem_recDx_iff {d : recD β ζ} : d ∈ recDx β ζ ↔ ∃ a : stabilizer G x, dβ β ζ a = d := by
  rw [recDx, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
  constructor
  · rintro ⟨a, ha⟩; exact ⟨a, Subtype.ext ha⟩
  · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩

@[expose] def recP2 : recD β ζ →* Gb := (MonoidHom.snd G Gb).comp (recD β ζ).subtype

@[expose] def recP1 : recD β ζ →* G := (MonoidHom.fst G Gb).comp (recD β ζ).subtype

@[simp] theorem recP2_dβ (a : stabilizer G x) : recP2 β ζ (dβ β ζ a) = β a := rfl

@[simp] theorem recP2_dζ (i : I) : recP2 β ζ (dζ β ζ i) = ζ i := rfl

@[simp] theorem recP1_dβ (a : stabilizer G x) : recP1 β ζ (dβ β ζ a) = a := rfl

@[simp] theorem recP1_dζ (i : I) : recP1 β ζ (dζ β ζ i) = i := rfl

theorem recP2_mem_of_mem_recDx {d : recD β ζ} (hd : d ∈ recDx β ζ) :
    recP2 β ζ d ∈ stabilizer Gb xb := by
  obtain ⟨a, rfl⟩ := (mem_recDx_iff β ζ).mp hd
  exact (β a).2

@[expose] noncomputable def recθ : recD β ζ ⧸ recDx β ζ → Xb :=
  Quotient.lift (fun d : recD β ζ => recP2 β ζ d • xb) (by
    intro a b hab
    have hab' : a⁻¹ * b ∈ recDx β ζ := QuotientGroup.leftRel_apply.mp hab
    have h := recP2_mem_of_mem_recDx β ζ hab'
    rw [map_mul, map_inv, mem_stabilizer_iff, mul_smul, inv_smul_eq_iff] at h
    exact h.symm)

@[simp] theorem recθ_mk (d : recD β ζ) : recθ β ζ (d : recD β ζ ⧸ recDx β ζ) = recP2 β ζ d • xb :=
  rfl

theorem recθ_smul (e : recD β ζ) (q : recD β ζ ⧸ recDx β ζ) :
    recθ β ζ (e • q) = recP2 β ζ e • recθ β ζ q := by
  induction q using QuotientGroup.induction_on with
  | H d => rw [MulAction.Quotient.smul_mk, recθ_mk, recθ_mk, smul_eq_mul, map_mul, mul_smul]

@[expose] def recGraph (t : I) : SimpleGraph (recD β ζ ⧸ recDx β ζ) :=
  SimpleGraph.fromRel fun q₁ q₂ => ∃ d : recD β ζ,
    q₁ = (d : recD β ζ ⧸ recDx β ζ) ∧ q₂ = ((d * dζ β ζ t : recD β ζ) : recD β ζ ⧸ recDx β ζ)

end Construction

section Properties

variable {β : stabilizer G x ≃* stabilizer Gb xb} {ζ : I ≃* Ib}

theorem mk_eq_mk_iff {d e : recD β ζ} :
    (d : recD β ζ ⧸ recDx β ζ) = e ↔ d⁻¹ * e ∈ recDx β ζ := QuotientGroup.eq

theorem zeta_swap (hs : IsSimilarity I x y Ib xb yb β ζ) (hxy : x ≠ y) (hxyb : xb ≠ yb) {t : I}
    (htx : (t : G) • x = y) (hty : (t : G) • y = x) :
    (ζ t : Gb) • xb = yb ∧ (ζ t : Gb) • yb = xb := by
  have ht2 : t ∈ (stabilizer G ({x, y} : Set X)).subgroupOf I := by
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_set]
    intro b
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · right; rw [← hty] at h; exact smul_left_cancel _ h
      · left; rw [← htx] at h; exact smul_left_cancel _ h
    · rintro (rfl | rfl)
      · right; exact htx
      · left; exact hty
  have hζ2 : ζ t ∈ (stabilizer Gb ({xb, yb} : Set Xb)).subgroupOf Ib := by
    rw [← hs.map_edge]; exact ⟨t, ht2, rfl⟩
  rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_set] at hζ2
  have hnx : (ζ t : Gb) • xb ≠ xb := by
    intro h
    have : ζ t ∈ (stabilizer Gb xb).subgroupOf Ib := Subgroup.mem_subgroupOf.mpr h
    rw [← hs.map_stab] at this
    obtain ⟨i, hi, hit⟩ := this
    have : i = t := ζ.injective hit
    subst this
    exact hxy ((mem_stabilizer_iff.mp (Subgroup.mem_subgroupOf.mp hi)).symm.trans htx)
  have h1 := (hζ2 xb).mpr (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  have hx : (ζ t : Gb) • xb = yb := h1.resolve_left hnx
  refine ⟨hx, ?_⟩
  have h2 := (hζ2 yb).mpr (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h2
  rcases h2 with h2 | h2
  · exact h2
  · exact absurd (smul_left_cancel _ (h2.trans hx.symm)) hxyb.symm

theorem dζ_sq_mem (hs : IsSimilarity I x y Ib xb yb β ζ) {t : I} (htx : (t : G) • x = y)
    (hty : (t : G) • y = x) : dζ β ζ t * dζ β ζ t ∈ recDx β ζ := by
  have htt : ((t * t : I) : G) ∈ stabilizer G x := by
    rw [mem_stabilizer_iff, Subgroup.coe_mul, mul_smul, htx, hty]
  rw [mem_recDx_iff]
  refine ⟨⟨_, htt⟩, Subtype.ext ?_⟩
  rw [← dζ_mul]
  simp only [dβ, dζ, graphβ_apply, graphζ_apply]
  rw [hs.eq_on (t * t) htt]

theorem conj_mem_recDx (hs : IsSimilarity I x y Ib xb yb β ζ) {t : I} (htx : (t : G) • x = y)
    (heq : ∀ b c : stabilizer G x, (b : G) • y = y → (c : G) = (t : G)⁻¹ * b * t →
      (β c : Gb) = (ζ t : Gb)⁻¹ * β b * ζ t)
    {e : recD β ζ} (he : e ∈ recDx β ζ) (hey : recP2 β ζ e • yb = yb) :
    (dζ β ζ t)⁻¹ * e * dζ β ζ t ∈ recDx β ζ := by
  obtain ⟨a, rfl⟩ := (mem_recDx_iff β ζ).mp he
  have hay : (a : G) • y = y := by
    have hb : β a ∈ (stabilizer Gb yb).subgroupOf (stabilizer Gb xb) :=
      Subgroup.mem_subgroupOf.mpr hey
    rw [← hs.map_stab_two] at hb
    obtain ⟨a', ha', ha'a⟩ := hb
    have : a' = a := β.injective ha'a
    subst this
    exact Subgroup.mem_subgroupOf.mp ha'
  have hc : (t : G)⁻¹ * a * t ∈ stabilizer G x := by
    rw [mem_stabilizer_iff, mul_smul, mul_smul, htx, hay]
    exact inv_smul_eq_iff.mpr htx.symm
  rw [mem_recDx_iff]
  refine ⟨⟨_, hc⟩, Subtype.ext ?_⟩
  simp only [dβ, dζ, graphβ_apply, Subgroup.coe_mul, Subgroup.coe_inv, graphζ_apply,
    Prod.mk_mul_mk, Prod.inv_mk]
  rw [heq a ⟨_, hc⟩ hay rfl]

end Properties

structure EquivData (I : Subgroup G) (x y : X) (Ib : Subgroup Gb) (xb yb : Xb)
    (β : stabilizer G x ≃* stabilizer Gb xb) (ζ : I ≃* Ib) (t : I) : Prop where
  sim : IsSimilarity I x y Ib xb yb β ζ
  hxy : x ≠ y
  hxyb : xb ≠ yb
  htx : (t : G) • x = y
  hty : (t : G) • y = x
  heq : ∀ b c : stabilizer G x, (b : G) • y = y → (c : G) = (t : G)⁻¹ * b * t →
    (β c : Gb) = (ζ t : Gb)⁻¹ * β b * ζ t

namespace EquivData

variable {β : stabilizer G x ≃* stabilizer Gb xb} {ζ : I ≃* Ib} {t : I}
  (h : EquivData I x y Ib xb yb β ζ t)
include h

theorem zt : (ζ t : Gb) • xb = yb ∧ (ζ t : Gb) • yb = xb :=
  zeta_swap h.sim h.hxy h.hxyb h.htx h.hty

theorem sq_mem : dζ β ζ t * dζ β ζ t ∈ recDx β ζ := dζ_sq_mem h.sim h.htx h.hty

theorem not_mem : dζ β ζ t ∉ recDx β ζ := by
  intro hm
  have := recP2_mem_of_mem_recDx β ζ hm
  rw [recP2_dζ, mem_stabilizer_iff, h.zt.1] at this
  exact h.hxyb this.symm

theorem conj_mem {e : recD β ζ} (he : e ∈ recDx β ζ) (hey : recP2 β ζ e • yb = yb) :
    (dζ β ζ t)⁻¹ * e * dζ β ζ t ∈ recDx β ζ :=
  conj_mem_recDx h.sim h.htx h.heq he hey

theorem adj_iff (d : recD β ζ) (q : recD β ζ ⧸ recDx β ζ) :
    (recGraph β ζ t).Adj (d : recD β ζ ⧸ recDx β ζ) q ↔
      ∃ e ∈ recDx β ζ, q = ((d * e * dζ β ζ t : recD β ζ) : recD β ζ ⧸ recDx β ζ) := by
  constructor
  · rintro ⟨-, ⟨d', h1, rfl⟩ | ⟨d', rfl, h2⟩⟩
    · refine ⟨d⁻¹ * d', mk_eq_mk_iff.mp h1, ?_⟩
      rw [mul_inv_cancel_left]
    · have hf : d⁻¹ * (d' * dζ β ζ t) ∈ recDx β ζ := mk_eq_mk_iff.mp h2
      refine ⟨d⁻¹ * (d' * dζ β ζ t), hf, ?_⟩
      rw [mk_eq_mk_iff]
      have e1 : d'⁻¹ * (d * (d⁻¹ * (d' * dζ β ζ t)) * dζ β ζ t) =
          dζ β ζ t * dζ β ζ t := by group
      rw [e1]
      exact h.sq_mem
  · rintro ⟨e, he, rfl⟩
    refine ⟨?_, Or.inl ⟨d * e, mk_eq_mk_iff.mpr (by simpa using he), rfl⟩⟩
    intro heq
    have := mk_eq_mk_iff.mp heq
    rw [show d⁻¹ * (d * e * dζ β ζ t) = e * dζ β ζ t by group] at this
    exact h.not_mem (by simpa using (recDx β ζ).mul_mem ((recDx β ζ).inv_mem he) this)

theorem adj_mk_mul (d : recD β ζ) :
    (recGraph β ζ t).Adj (d : recD β ζ ⧸ recDx β ζ)
      ((d * dζ β ζ t : recD β ζ) : recD β ζ ⧸ recDx β ζ) :=
  (h.adj_iff d _).mpr ⟨1, (recDx β ζ).one_mem, by rw [mul_one]⟩

end EquivData

theorem recGraph_adj_smul (β : stabilizer G x ≃* stabilizer Gb xb) (ζ : I ≃* Ib) (t : I)
    (e : recD β ζ) {q₁ q₂ : recD β ζ ⧸ recDx β ζ} (hq : (recGraph β ζ t).Adj q₁ q₂) :
    (recGraph β ζ t).Adj (e • q₁) (e • q₂) := by
  obtain ⟨hne, ⟨d, rfl, rfl⟩ | ⟨d, rfl, rfl⟩⟩ := hq
  · refine ⟨fun h => hne (smul_left_cancel e h), Or.inl ⟨e * d, ?_, ?_⟩⟩
    · rw [MulAction.Quotient.smul_mk]; rfl
    · rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_assoc]
  · refine ⟨fun h => hne (smul_left_cancel e h), Or.inr ⟨e * d, ?_, ?_⟩⟩
    · rw [MulAction.Quotient.smul_mk]; rfl
    · rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_assoc]

@[expose] def recGraphSmul (β : stabilizer G x ≃* stabilizer Gb xb) (ζ : I ≃* Ib) (t : I)
    (e : recD β ζ) : recGraph β ζ t →g recGraph β ζ t where
  toFun q := e • q
  map_rel' := recGraph_adj_smul β ζ t e

variable {Γ : SimpleGraph X} {ΓI : Γ.Subgraph} {Γb : SimpleGraph Xb} {ΓIb : Γb.Subgraph}

theorem IsUniquenessSystem.adj (hU : IsUniquenessSystem Γ I ΓI x y) : Γ.Adj x y := by
  have : s(x, y) ∈ Γ.edgeSet := by rw [hU.edgeSet_eq]; exact ⟨1, by simp⟩
  exact this

theorem IsUniquenessSystem.exists_stab_smul (hU : IsUniquenessSystem Γ I ΓI x y)
    {t : G} (htx : t • x = y) (hty : t • y = x) {w : X} (hw : Γ.Adj x w) :
    ∃ g ∈ stabilizer G x, g • y = w := by
  have : s(x, w) ∈ Γ.edgeSet := hw
  rw [hU.edgeSet_eq] at this
  obtain ⟨g, hg⟩ := this
  rcases Sym2.eq_iff.mp hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨g, h1, h2⟩
  · refine ⟨g * t, ?_, ?_⟩
    · rw [mem_stabilizer_iff, mul_smul, htx, h2]
    · rw [mul_smul, hty, h1]

theorem recP2_surjective (hUb : IsUniquenessSystem Γb Ib ΓIb xb yb)
    (β : stabilizer G x ≃* stabilizer Gb xb) (ζ : I ≃* Ib) :
    Function.Surjective (recP2 β ζ) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← hUb.sup_eq_top, sup_le_iff]
  constructor
  · intro g hg
    exact ⟨dβ β ζ (β.symm ⟨g, hg⟩), by simp⟩
  · intro g hg
    exact ⟨dζ β ζ (ζ.symm ⟨g, hg⟩), by simp⟩

theorem recP1_surjective (hU : IsUniquenessSystem Γ I ΓI x y)
    (β : stabilizer G x ≃* stabilizer Gb xb) (ζ : I ≃* Ib) :
    Function.Surjective (recP1 β ζ) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← hU.sup_eq_top, sup_le_iff]
  constructor
  · intro g hg
    exact ⟨dβ β ζ ⟨g, hg⟩, rfl⟩
  · intro g hg
    exact ⟨dζ β ζ ⟨g, hg⟩, rfl⟩

theorem recθ_covering (hUb : IsUniquenessSystem Γb Ib ΓIb xb yb)
    {β : stabilizer G x ≃* stabilizer Gb xb} {ζ : I ≃* Ib} {t : I}
    (h : EquivData I x y Ib xb yb β ζ t) :
    GraphCovering (recGraph β ζ t) Γb (recθ β ζ) := by
  have := hUb.graphAction
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    rintro a b ⟨-, ⟨d, rfl, rfl⟩ | ⟨d, rfl, rfl⟩⟩
    · rw [recθ_mk, recθ_mk, map_mul, mul_smul, recP2_dζ, h.zt.1]
      exact (GraphAction.adj_smul _ _ _).mpr hUb.adj
    · rw [recθ_mk, recθ_mk, map_mul, mul_smul, recP2_dζ, h.zt.1]
      exact (GraphAction.adj_smul _ _ _).mpr hUb.adj.symm
  ·
    intro w
    obtain ⟨g, rfl⟩ := hUb.trans w
    obtain ⟨d, rfl⟩ := recP2_surjective hUb β ζ g
    exact ⟨d, rfl⟩
  ·
    intro q a b ha hb hab
    induction q using QuotientGroup.induction_on with
    | H d =>
      obtain ⟨e, he, rfl⟩ := (h.adj_iff d a).mp ha
      obtain ⟨e', he', rfl⟩ := (h.adj_iff d b).mp hb
      rw [recθ_mk, recθ_mk, map_mul, map_mul, map_mul, map_mul, mul_smul, mul_smul, mul_smul,
        mul_smul, recP2_dζ, h.zt.1, smul_left_cancel_iff] at hab
      have hy : recP2 β ζ (e'⁻¹ * e) • yb = yb := by
        rw [map_mul, map_inv, mul_smul, hab, inv_smul_smul]
      have := h.conj_mem ((recDx β ζ).mul_mem ((recDx β ζ).inv_mem he') he) hy
      rw [mk_eq_mk_iff]
      rw [show (d * e * dζ β ζ t)⁻¹ * (d * e' * dζ β ζ t) =
        (dζ β ζ t)⁻¹ * (e⁻¹ * e') * dζ β ζ t by group]
      have := (recDx β ζ).inv_mem this
      rw [show ((dζ β ζ t)⁻¹ * (e'⁻¹ * e) * dζ β ζ t)⁻¹ =
        (dζ β ζ t)⁻¹ * (e⁻¹ * e') * dζ β ζ t by group] at this
      exact this
  ·
    intro q w hw
    induction q using QuotientGroup.induction_on with
    | H d =>
      rw [recθ_mk] at hw
      have hw' : Γb.Adj xb ((recP2 β ζ d)⁻¹ • w) := by
        rw [← GraphAction.adj_smul (recP2 β ζ d), smul_inv_smul]; exact hw
      obtain ⟨g, hg, hgw⟩ := hUb.exists_stab_smul h.zt.1 h.zt.2 hw'
      set e := dβ β ζ (β.symm ⟨g, hg⟩)
      refine ⟨((d * e * dζ β ζ t : recD β ζ) : recD β ζ ⧸ recDx β ζ),
        (h.adj_iff d _).mpr ⟨e, dβ_mem_recDx β ζ _, rfl⟩, ?_⟩
      rw [recθ_mk, map_mul, map_mul, mul_smul, mul_smul, recP2_dζ, h.zt.1]
      simp only [e, recP2_dβ, MulEquiv.apply_symm_apply]
      rw [hgw, smul_inv_smul]

theorem dζ_mem_recDx_of_mem {β : stabilizer G x ≃* stabilizer Gb xb} {ζ : I ≃* Ib}
    (hs : IsSimilarity I x y Ib xb yb β ζ) {i : I} (hi : (i : G) ∈ stabilizer G x) :
    dζ β ζ i ∈ recDx β ζ := by
  rw [mem_recDx_iff]
  refine ⟨⟨i, hi⟩, Subtype.ext ?_⟩
  simp only [dβ, dζ, graphβ_apply, graphζ_apply]
  rw [hs.eq_on i hi]

theorem mk_eq_one_of_mem {β : stabilizer G x ≃* stabilizer Gb xb} {ζ : I ≃* Ib}
    {d : recD β ζ} (hd : d ∈ recDx β ζ) :
    (d : recD β ζ ⧸ recDx β ζ) = ((1 : recD β ζ) : recD β ζ ⧸ recDx β ζ) :=
  mk_eq_mk_iff.mpr (by simpa using (recDx β ζ).inv_mem hd)

theorem recGraph_reachable (hU : IsUniquenessSystem Γ I ΓI x y)
    {β : stabilizer G x ≃* stabilizer Gb xb} {ζ : I ≃* Ib} {t : I}
    (h : EquivData I x y Ib xb yb β ζ t) (d : recD β ζ) :
    (recGraph β ζ t).Reachable ((1 : recD β ζ) : recD β ζ ⧸ recDx β ζ) d := by
  set Q := recD β ζ ⧸ recDx β ζ
  have tmul : ∀ d e : recD β ζ, (recGraph β ζ t).Reachable ((1 : recD β ζ) : Q) d →
      (recGraph β ζ t).Reachable ((1 : recD β ζ) : Q) e →
      (recGraph β ζ t).Reachable ((1 : recD β ζ) : Q) ((d * e : recD β ζ) : Q) := by
    intro d e hd he
    have := he.map (recGraphSmul β ζ t d)
    simp only [recGraphSmul, RelHom.coeFn_mk, MulAction.Quotient.smul_mk, smul_eq_mul,
      mul_one] at this
    exact hd.trans this
  have tinv : ∀ d : recD β ζ, (recGraph β ζ t).Reachable ((1 : recD β ζ) : Q) d →
      (recGraph β ζ t).Reachable ((1 : recD β ζ) : Q) ((d⁻¹ : recD β ζ) : Q) := by
    intro d hd
    have := hd.map (recGraphSmul β ζ t d⁻¹)
    simp only [recGraphSmul, RelHom.coeFn_mk, MulAction.Quotient.smul_mk, smul_eq_mul,
      mul_one, inv_mul_cancel] at this
    exact this.symm
  have hDx : ∀ e ∈ recDx β ζ, (recGraph β ζ t).Reachable ((1 : recD β ζ) : Q) e := by
    intro e he
    rw [mk_eq_one_of_mem he]
  have htD : (recGraph β ζ t).Reachable ((1 : recD β ζ) : Q) (dζ β ζ t) := by
    have := (h.adj_mk_mul 1).reachable
    rwa [one_mul] at this
  have hI : ∀ i : I, (recGraph β ζ t).Reachable ((1 : recD β ζ) : Q) (dζ β ζ i) := by
    intro i
    have hi : (i : G) ∈ I ⊓ stabilizer G x ⊔ I ⊓ stabilizer G ({x, y} : Set X) := by
      rw [← hU.I_eq]; exact i.2
    rw [Subgroup.sup_eq_closure] at hi
    have key : ∀ g (hg : g ∈ Subgroup.closure ((I ⊓ stabilizer G x : Subgroup G) ∪
        (I ⊓ stabilizer G ({x, y} : Set X) : Subgroup G))), ∀ hgI : g ∈ I,
          (recGraph β ζ t).Reachable ((1 : recD β ζ) : Q) (dζ β ζ ⟨g, hgI⟩) := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem g hg =>
        intro hgI
        rcases hg with hg | hg
        · exact hDx _ (dζ_mem_recDx_of_mem h.sim hg.2)
        · by_cases hgx : g • x = x
          · exact hDx _ (dζ_mem_recDx_of_mem h.sim hgx)
          ·
            have hgy : g • x = y := by
              have := (MulAction.mem_stabilizer_set.mp hg.2 x).mpr (by simp)
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
              exact this.resolve_left hgx
            have hj : ((t⁻¹ * ⟨g, hgI⟩ : I) : G) ∈ stabilizer G x := by
              rw [mem_stabilizer_iff, Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, hgy]
              exact inv_smul_eq_iff.mpr h.htx.symm
            have e1 : dζ β ζ ⟨g, hgI⟩ = dζ β ζ t * dζ β ζ (t⁻¹ * ⟨g, hgI⟩) := by
              rw [← dζ_mul, mul_inv_cancel_left]
            rw [e1]
            have := tmul _ _ htD (hDx _ (dζ_mem_recDx_of_mem h.sim hj))
            exact this
      | one =>
        intro hgI
        have : dζ β ζ (⟨1, hgI⟩ : I) = 1 := Subtype.ext (map_one (graphζ ζ))
        rw [this]
      | mul a b ha hb iha ihb =>
        intro hgI
        have haI : a ∈ I := by
          have : a ∈ I ⊓ stabilizer G x ⊔ I ⊓ stabilizer G ({x, y} : Set X) := by
            rw [Subgroup.sup_eq_closure]; exact ha
          rw [← hU.I_eq] at this; exact this
        have hbI : b ∈ I := by
          have : b ∈ I ⊓ stabilizer G x ⊔ I ⊓ stabilizer G ({x, y} : Set X) := by
            rw [Subgroup.sup_eq_closure]; exact hb
          rw [← hU.I_eq] at this; exact this
        have e1 : dζ β ζ ⟨a * b, hgI⟩ = dζ β ζ ⟨a, haI⟩ * dζ β ζ ⟨b, hbI⟩ := by
          rw [← dζ_mul]; rfl
        rw [e1]
        exact tmul _ _ (iha haI) (ihb hbI)
      | inv a ha iha =>
        intro hgI
        have haI : a ∈ I := by simpa using hgI
        have e1 : dζ β ζ ⟨a⁻¹, hgI⟩ = (dζ β ζ ⟨a, haI⟩)⁻¹ := by
          rw [show (⟨a⁻¹, hgI⟩ : I) = (⟨a, haI⟩ : I)⁻¹ from rfl]
          exact Subtype.ext (map_inv (graphζ ζ) _)
        rw [e1]
        exact tinv _ (iha haI)
    exact key _ hi i.2
  have hd : (d : G × Gb) ∈ (graphβ β).range ⊔ (graphζ ζ).range := d.2
  rw [Subgroup.sup_eq_closure] at hd
  have key : ∀ g (hg : g ∈ Subgroup.closure (((graphβ β).range : Set (G × Gb)) ∪
      (graphζ ζ).range)), ∀ hgD : g ∈ recD β ζ,
        (recGraph β ζ t).Reachable ((1 : recD β ζ) : Q) (⟨g, hgD⟩ : recD β ζ) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      intro hgD
      rcases hg with ⟨a, rfl⟩ | ⟨i, rfl⟩
      · exact hDx _ (dβ_mem_recDx β ζ a)
      · exact hI i
    | one => intro hgD; rfl
    | mul a b ha hb iha ihb =>
      intro hgD
      have haD : a ∈ recD β ζ := by
        rw [recD, Subgroup.sup_eq_closure]; exact ha
      have hbD : b ∈ recD β ζ := by
        rw [recD, Subgroup.sup_eq_closure]; exact hb
      exact tmul ⟨a, haD⟩ ⟨b, hbD⟩ (iha haD) (ihb hbD)
    | inv a ha iha =>
      intro hgD
      have haD : a ∈ recD β ζ := by
        rw [recD, Subgroup.sup_eq_closure]; exact ha
      exact tinv ⟨a, haD⟩ (iha haD)
  exact key _ hd d.2

theorem recθ_fiber {β : stabilizer G x ≃* stabilizer Gb xb} {ζ : I ≃* Ib}
    {q q' : recD β ζ ⧸ recDx β ζ} (hq : recθ β ζ q = recθ β ζ q') :
    ∃ n : recD β ζ, recP2 β ζ n = 1 ∧ q = n • q' := by
  induction q using QuotientGroup.induction_on with
  | H e =>
    induction q' using QuotientGroup.induction_on with
    | H e' =>
      rw [recθ_mk, recθ_mk] at hq
      have hst : recP2 β ζ (e'⁻¹ * e) ∈ stabilizer Gb xb := by
        rw [mem_stabilizer_iff, map_mul, map_inv, mul_smul, hq, inv_smul_smul]
      set f := dβ β ζ (β.symm ⟨_, hst⟩)
      have hf : recP2 β ζ f = recP2 β ζ (e'⁻¹ * e) := by simp [f]
      refine ⟨e * f⁻¹ * e'⁻¹, ?_, ?_⟩
      · rw [map_mul, map_mul, map_inv, map_inv, hf, map_mul, map_inv]; group
      · rw [MulAction.Quotient.smul_mk, smul_eq_mul, mk_eq_mk_iff]
        rw [show e⁻¹ * (e * f⁻¹ * e'⁻¹ * e') = f⁻¹ by group]
        exact (recDx β ζ).inv_mem (dβ_mem_recDx β ζ _)

variable (β : stabilizer G x ≃* stabilizer Gb xb) (ζ : I ≃* Ib) in
@[expose] noncomputable def recσ (v : Xb) : recD β ζ ⧸ recDx β ζ :=
  open Classical in
  if hv : ∃ i : I, (ζ i : Gb) • xb = v then (dζ β ζ hv.choose : recD β ζ ⧸ recDx β ζ) else
    ((1 : recD β ζ) : recD β ζ ⧸ recDx β ζ)

theorem recσ_eq {β : stabilizer G x ≃* stabilizer Gb xb} {ζ : I ≃* Ib}
    (hs : IsSimilarity I x y Ib xb yb β ζ) (i : I) :
    recσ β ζ ((ζ i : Gb) • xb) = (dζ β ζ i : recD β ζ ⧸ recDx β ζ) := by
  classical
  have hv : ∃ j : I, (ζ j : Gb) • xb = (ζ i : Gb) • xb := ⟨i, rfl⟩
  rw [recσ, dite_eq_left hv]
  set j := hv.choose
  have hj : (ζ j : Gb) • xb = (ζ i : Gb) • xb := hv.choose_spec
  have hst : ζ (i⁻¹ * j) ∈ (stabilizer Gb xb).subgroupOf Ib := by
    rw [Subgroup.mem_subgroupOf, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
      mem_stabilizer_iff, mul_smul, hj, inv_smul_smul]
  rw [← hs.map_stab] at hst
  obtain ⟨k, hk, hkij⟩ := hst
  have hk' : k = i⁻¹ * j := ζ.injective hkij
  subst hk'
  rw [mk_eq_mk_iff, show (dζ β ζ j)⁻¹ * dζ β ζ i = (dζ β ζ (i⁻¹ * j))⁻¹ by
    rw [dζ_mul]; simp [dζ, Subtype.ext_iff, graphζ]]
  exact (recDx β ζ).inv_mem (dζ_mem_recDx_of_mem hs (Subgroup.mem_subgroupOf.mp hk))

theorem recθ_recσ {β : stabilizer G x ≃* stabilizer Gb xb} {ζ : I ≃* Ib}
    (hs : IsSimilarity I x y Ib xb yb β ζ) (i : I) :
    recθ β ζ (recσ β ζ ((ζ i : Gb) • xb)) = (ζ i : Gb) • xb := by
  rw [recσ_eq hs, recθ_mk, recP2_dζ]

theorem IsUniquenessSystem.exists_of_mem_verts (hUb : IsUniquenessSystem Γb Ib ΓIb xb yb)
    (ζ : I ≃* Ib) {v : Xb} (hv : v ∈ ΓIb.verts) : ∃ i : I, (ζ i : Gb) • xb = v := by
  rw [hUb.verts_eq] at hv
  obtain ⟨j, hj, rfl⟩ := hv
  exact ⟨ζ.symm ⟨j, hj⟩, by simp⟩

theorem recσ_adj (hUb : IsUniquenessSystem Γb Ib ΓIb xb yb)
    {β : stabilizer G x ≃* stabilizer Gb xb} {ζ : I ≃* Ib} {t : I}
    (h : EquivData I x y Ib xb yb β ζ t) {u v : Xb} (huv : ΓIb.Adj u v) :
    (recGraph β ζ t).Adj (recσ β ζ u) (recσ β ζ v) := by
  have he : s(u, v) ∈ ΓIb.edgeSet := huv
  rw [hUb.edgeSet_I_eq] at he
  obtain ⟨j, hj, hjuv⟩ := he
  set i := ζ.symm ⟨j, hj⟩
  have hji : (ζ i : Gb) = j := by simp [i]
  have hyb : j • yb = (ζ (i * t) : Gb) • xb := by
    rw [map_mul, Subgroup.coe_mul, mul_smul, h.zt.1, hji]
  have hxb : j • xb = (ζ i : Gb) • xb := by rw [hji]
  rcases Sym2.eq_iff.mp hjuv with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h1, ← h2, hxb, hyb, recσ_eq h.sim, recσ_eq h.sim, dζ_mul]
    exact h.adj_mk_mul _
  · rw [← h1, ← h2, hxb, hyb, recσ_eq h.sim, recσ_eq h.sim, dζ_mul]
    exact (h.adj_mk_mul _).symm

theorem IsRotation.of_map {V W : Type*} (f : V → W) {l : List V} {d : List W}
    (hr : IsRotation (l.map f) d) : ∃ d₀, IsRotation l d₀ ∧ d = d₀.map f := by
  obtain ⟨l₁, l₂, w, hl, hw, rfl⟩ := hr
  obtain ⟨m₁, m₂, rfl, rfl, rfl⟩ := List.map_eq_append_iff.mp hl
  rw [List.getLast?_map] at hw
  obtain ⟨w₀, hw₀, rfl⟩ := Option.map_eq_some_iff.mp hw
  exact ⟨w₀ :: (m₂ ++ m₁.tail), ⟨m₁, m₂, w₀, rfl, hw₀, rfl⟩, by simp [List.map_tail]⟩

theorem liftClosed (hUb : IsUniquenessSystem Γb Ib ΓIb xb yb)
    {β : stabilizer G x ≃* stabilizer Gb xb} {ζ : I ≃* Ib} {t : I}
    (h : EquivData I x y Ib xb yb β ζ t) {c₀ : List Xb} (hc₀ : IsSubCycle ΓIb c₀) (g : Gb)
    {w : Xb} (hw : (c₀.map (g • ·)).head? = some w) (q : recD β ζ ⧸ recDx β ζ)
    (hq : recθ β ζ q = w) :
    (c₀.map (g • ·)).foldl (liftStep (recGraph β ζ t) (recθ β ζ)) q = q := by
  have hθ := recθ_covering hUb h
  obtain ⟨⟨⟨hne, hch⟩, hhl⟩, hverts⟩ := hc₀
  obtain ⟨u₀, c₁, rfl⟩ : ∃ u₀ c₁, c₀ = u₀ :: c₁ := by
    cases c₀ with
    | nil => exact absurd rfl hne
    | cons u₀ c₁ => exact ⟨u₀, c₁, rfl⟩
  simp only [List.map_cons, List.head?_cons, Option.some.injEq] at hw
  subst hw
  obtain ⟨i₀, hi₀⟩ := hUb.exists_of_mem_verts ζ (hverts u₀ (by simp))
  obtain ⟨e₀, he₀⟩ := recP2_surjective hUb β ζ g
  have hfib : recθ β ζ q = recθ β ζ (e₀ • recσ β ζ u₀) := by
    rw [hq, recθ_smul, ← hi₀, recθ_recσ h.sim, he₀]
  obtain ⟨n, hn, hqn⟩ := recθ_fiber hfib
  set e := n * e₀
  have he : recP2 β ζ e = g := by simp [e, hn, he₀]
  have hqe : q = e • recσ β ζ u₀ := by rw [hqn, mul_smul]
  have hθσ : ∀ v ∈ u₀ :: c₁, recθ β ζ (e • recσ β ζ v) = g • v := by
    intro v hv
    obtain ⟨i, rfl⟩ := hUb.exists_of_mem_verts ζ (hverts v hv)
    rw [recθ_smul, recθ_recσ h.sim, he]
  have hchL : ((u₀ :: c₁).map fun v => e • recσ β ζ v).IsChain (recGraph β ζ t).Adj := by
    rw [List.isChain_map]
    exact hch.imp fun a b hab => recGraph_adj_smul β ζ t e (recσ_adj hUb h hab)
  have hmap : ((u₀ :: c₁).map fun v => e • recσ β ζ v).map (recθ β ζ) =
      (u₀ :: c₁).map (g • ·) := by
    rw [List.map_map]
    exact List.map_congr_left fun v hv => hθσ v hv
  have hL := foldl_liftStep_map hθ (c₁.map fun v => e • recσ β ζ v) (e • recσ β ζ u₀)
    (by simpa using hchL)
  have hu₀ : (u₀ :: c₁).getLast (List.cons_ne_nil _ _) = u₀ := by
    have hlast : (u₀ :: c₁).getLast? = some u₀ := hhl.symm
    rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)] at hlast
    exact Option.some.inj hlast
  calc ((u₀ :: c₁).map (g • ·)).foldl (liftStep (recGraph β ζ t) (recθ β ζ)) q
      = (((u₀ :: c₁).map fun v => e • recσ β ζ v).map (recθ β ζ)).foldl
          (liftStep (recGraph β ζ t) (recθ β ζ)) q := by rw [hmap]
    _ = ((u₀ :: c₁).map fun v => e • recσ β ζ v).getLast (by simp) := by rw [hqe]; exact hL
    _ = q := by rw [List.getLast_map, hu₀, hqe]

theorem recP2_injective (hU : IsUniquenessSystem Γ I ΓI x y)
    (hUb : IsUniquenessSystem Γb Ib ΓIb xb yb)
    {β : stabilizer G x ≃* stabilizer Gb xb} {ζ : I ≃* Ib} {t : I}
    (h : EquivData I x y Ib xb yb β ζ t) (hbase : IsBase Gb Γb ΓIb) :
    Function.Injective (recP2 β ζ) := by
  have := hUb.graphAction
  have hθ := recθ_covering hUb h
  set C : Set (List Xb) :=
    {d | ∃ (c₀ : List Xb) (g : Gb), IsSubCycle ΓIb c₀ ∧ d = c₀.map (g • ·)}
  have hrot : ∀ d ∈ rotRev C, ∃ (c₀ : List Xb) (g : Gb), IsSubCycle ΓIb c₀ ∧
      d = c₀.map (g • ·) := by
    rintro d ⟨c, ⟨c₀, g, hc₀, rfl⟩, hr | hr⟩
    · obtain ⟨d₀, hd₀, rfl⟩ := IsRotation.of_map (g • ·) hr
      obtain ⟨hcyc, hmem, -⟩ := hd₀.isCycle hc₀.1
      exact ⟨d₀, g, ⟨hcyc, fun v hv => hc₀.2 v (hmem v hv)⟩, rfl⟩
    · rw [← List.map_reverse] at hr
      obtain ⟨d₀, hd₀, rfl⟩ := IsRotation.of_map (g • ·) hr
      obtain ⟨hcyc, hmem, -⟩ := hd₀.isCycle hc₀.1.reverse
      exact ⟨d₀, g, ⟨hcyc, fun v hv => hc₀.2 v (by simpa using hmem v hv)⟩, rfl⟩
  have hC : ∀ d ∈ rotRev C, IsPath Γb d ∧ ∀ w, d.head? = some w →
      ∀ q, recθ β ζ q = w → d.foldl (liftStep (recGraph β ζ t) (recθ β ζ)) q = q := by
    intro d hd
    obtain ⟨c₀, g, hc₀, rfl⟩ := hrot d hd
    refine ⟨⟨by simpa using hc₀.1.1.1, ?_⟩, fun w hw q hq => liftClosed hUb h hc₀ g hw q hq⟩
    rw [List.isChain_map]
    exact hc₀.1.1.2.imp fun a b hab => (GraphAction.adj_smul g a b).mpr (ΓIb.adj_sub hab)
  rw [injective_iff_map_eq_one]
  intro n hn
  obtain ⟨W⟩ := recGraph_reachable hU h n
  set l := W.support
  have hl : l = ((1 : recD β ζ) : recD β ζ ⧸ recDx β ζ) :: W.support.tail :=
    W.cons_tail_support.symm
  have hlch : l.IsChain (recGraph β ζ t).Adj := W.isChain_adj_support
  have hlh : l.head? = some ((1 : recD β ζ) : recD β ζ ⧸ recDx β ζ) := by rw [hl]; rfl
  have hll : l.getLast? = some (n : recD β ζ ⧸ recDx β ζ) := by
    rw [List.getLast?_eq_some_getLast (by rw [hl]; simp), SimpleGraph.Walk.getLast_support]
  have hp : IsCycle Γb (l.map (recθ β ζ)) := by
    refine ⟨⟨by simp [hl], ?_⟩, ?_⟩
    · rw [List.isChain_map]; exact hlch.imp fun a b hab => hθ.adj a b hab
    · rw [List.head?_map, List.getLast?_map, hlh, hll]
      simp [hn]
  obtain ⟨w, hw⟩ := hbase _ hp
  have hw' : w = xb := by
    have h0 := Moves.head?_eq hw
    rw [List.head?_map, hlh] at h0
    simp only [Option.map_some, List.head?_cons, Option.some.injEq, recθ_mk, map_one,
      one_smul] at h0
    exact h0.symm
  rw [hw'] at hw
  have h1 := foldl_liftStep_moves hθ hC hw hp.1
    (q := ((1 : recD β ζ) : recD β ζ ⧸ recDx β ζ)) (by rw [List.head?_map, hlh]; rfl)
  have h2 := foldl_liftStep_map hθ W.support.tail ((1 : recD β ζ) : recD β ζ ⧸ recDx β ζ)
    (by rw [← hl]; exact hlch)
  simp only [SimpleGraph.Walk.cons_tail_support, SimpleGraph.Walk.getLast_support] at h2
  rw [h2, List.foldl_cons, List.foldl_nil] at h1
  have h3 : liftStep (recGraph β ζ t) (recθ β ζ) ((1 : recD β ζ) : recD β ζ ⧸ recDx β ζ) xb =
      ((1 : recD β ζ) : recD β ζ ⧸ recDx β ζ) := by
    have := liftStep_self hθ ((1 : recD β ζ) : recD β ζ ⧸ recDx β ζ)
    simpa using this
  rw [h3] at h1
  have hmem : n ∈ recDx β ζ := by
    have := mk_eq_mk_iff.mp h1.symm
    simpa using this
  obtain ⟨a, rfl⟩ := (mem_recDx_iff β ζ).mp hmem
  rw [recP2_dβ] at hn
  have ha : a = 1 := β.injective (Subtype.ext (by simpa using hn))
  subst ha
  exact Subtype.ext (map_one (graphβ β))

theorem recognition (hU : IsUniquenessSystem Γ I ΓI x y)
    (hUb : IsUniquenessSystem Γb Ib ΓIb xb yb)
    {β : stabilizer G x ≃* stabilizer Gb xb} {ζ : I ≃* Ib}
    (he : IsEquivalence I x y Ib xb yb β ζ) (hbase : IsBase Gb Γb ΓIb)
    (hsimple : IsSimpleGroup Gb) :
    ∃ φ : G ≃* Gb, (∀ a : stabilizer G x, φ a = β a) ∧ ∀ i : I, φ i = ζ i := by
  obtain ⟨hs, t, htx, hty, heq⟩ := he
  have h : EquivData I x y Ib xb yb β ζ t :=
    ⟨hs, hU.adj.ne, hUb.adj.ne, htx, hty, heq⟩
  set e₂ : recD β ζ ≃* Gb := MulEquiv.ofBijective (recP2 β ζ)
    ⟨recP2_injective hU hUb h hbase, recP2_surjective hUb β ζ⟩
  set ψ : Gb →* G := (recP1 β ζ).comp e₂.symm.toMonoidHom
  have hψs : Function.Surjective ψ :=
    (recP1_surjective hU β ζ).comp e₂.symm.surjective
  have hψi : Function.Injective ψ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal ψ.ker with hk | hk
    · exact (MonoidHom.ker_eq_bot_iff ψ).mp hk
    · exfalso
      obtain ⟨g, hg⟩ := hψs (t : G)
      have h1 : ψ g = 1 := by
        rw [← MonoidHom.mem_ker, hk]; exact Subgroup.mem_top g
      rw [hg] at h1
      apply h.hxy
      rw [← h.htx, h1, one_smul]
  set φ' : Gb ≃* G := MulEquiv.ofBijective ψ ⟨hψi, hψs⟩
  have hψβ : ∀ a : stabilizer G x, ψ (β a) = a := by
    intro a
    have : e₂.symm (β a) = dβ β ζ a := by
      rw [MulEquiv.symm_apply_eq]; rfl
    simp only [ψ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, this,
      recP1_dβ]
  have hψζ : ∀ i : I, ψ (ζ i) = i := by
    intro i
    have : e₂.symm (ζ i) = dζ β ζ i := by
      rw [MulEquiv.symm_apply_eq]; rfl
    simp only [ψ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, this,
      recP1_dζ]
  refine ⟨φ'.symm, fun a => ?_, fun i => ?_⟩
  · rw [MulEquiv.symm_apply_eq]; exact (hψβ a).symm
  · rw [MulEquiv.symm_apply_eq]; exact (hψζ i).symm

end CFSG.Quasithin.Asc94
