module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Algebra.Group.Action.Sum
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.CosetGraph

open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def amalgamGraph (A B : Subgroup G) : SimpleGraph ((G ⧸ A) ⊕ (G ⧸ B)) :=
  SimpleGraph.fromRel fun x y => ∃ g : G, x = .inl (g : G ⧸ A) ∧ y = .inr (g : G ⧸ B)

@[expose] def kernelAt {V : Type*} [MulAction G V] (Γ : SimpleGraph V) (ε : V) : Subgroup G :=
  MulAction.stabilizer G ε ⊓ ⨅ w ∈ Γ.neighborSet ε, MulAction.stabilizer G w

@[expose] noncomputable def zAt (A B Z : Subgroup G) : (G ⧸ A) ⊕ (G ⧸ B) → Subgroup G
  | .inl x => Z.map (MulAut.conj (Quotient.out x)).toMonoidHom
  | .inr _ => ⊥

@[expose] def IsCriticalPair {V : Type*} [MulAction G V] (Γ : SimpleGraph V) (Z : V → Subgroup G)
    (P : V → Prop) (δ ε : V) : Prop :=
  P δ ∧ Γ.Reachable δ ε ∧ ¬ Z δ ≤ kernelAt Γ ε ∧
    ∀ δ' ε', P δ' → Γ.Reachable δ' ε' → Γ.dist δ' ε' < Γ.dist δ ε → Z δ' ≤ kernelAt Γ ε'

theorem le_kernelAt_or_exists_isCriticalPair {V : Type*} [MulAction G V] (Γ : SimpleGraph V)
    (Z : V → Subgroup G) (P : V → Prop) :
    (∀ δ ε, P δ → Γ.Reachable δ ε → Z δ ≤ kernelAt Γ ε) ∨
      ∃ δ ε, IsCriticalPair Γ Z P δ ε := by
  classical
  by_cases hall : ∀ δ ε, P δ → Γ.Reachable δ ε → Z δ ≤ kernelAt Γ ε
  · exact Or.inl hall
  right
  push Not at hall
  have hex : ∃ n : ℕ, ∃ δ ε, P δ ∧ Γ.Reachable δ ε ∧ ¬ Z δ ≤ kernelAt Γ ε ∧ Γ.dist δ ε = n := by
    obtain ⟨δ, ε, h1, h2, h3⟩ := hall
    exact ⟨_, δ, ε, h1, h2, h3, rfl⟩
  obtain ⟨δ, ε, h1, h2, h3, h4⟩ := Nat.find_spec hex
  refine ⟨δ, ε, h1, h2, h3, fun δ' ε' hP hR hlt => ?_⟩
  by_contra hn
  exact Nat.find_min hex (h4 ▸ hlt) ⟨δ', ε', hP, hR, hn, rfl⟩

section Basic

variable {A B : Subgroup G}

theorem amalgamGraph_adj_iff (x y : (G ⧸ A) ⊕ (G ⧸ B)) :
    (amalgamGraph A B).Adj x y ↔
      (∃ g : G, x = .inl (g : G ⧸ A) ∧ y = .inr (g : G ⧸ B)) ∨
      (∃ g : G, y = .inl (g : G ⧸ A) ∧ x = .inr (g : G ⧸ B)) := by
  unfold amalgamGraph
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · obtain ⟨g, rfl, rfl⟩ := h
      exact ⟨by simp, Or.inl ⟨g, rfl, rfl⟩⟩
    · obtain ⟨g, rfl, rfl⟩ := h
      exact ⟨by simp, Or.inr ⟨g, rfl, rfl⟩⟩

abbrev alphaV (A B : Subgroup G) : (G ⧸ A) ⊕ (G ⧸ B) := .inl ((1 : G) : G ⧸ A)
abbrev betaV (A B : Subgroup G) : (G ⧸ A) ⊕ (G ⧸ B) := .inr ((1 : G) : G ⧸ B)

theorem adj_alphaV_betaV : (amalgamGraph A B).Adj (alphaV A B) (betaV A B) :=
  (amalgamGraph_adj_iff _ _).mpr (Or.inl ⟨1, rfl, rfl⟩)

theorem smul_adj_iff (h : G) (x y : (G ⧸ A) ⊕ (G ⧸ B)) :
    (amalgamGraph A B).Adj (h • x) (h • y) ↔ (amalgamGraph A B).Adj x y := by
  have key : ∀ (h : G) (x y : (G ⧸ A) ⊕ (G ⧸ B)),
      (amalgamGraph A B).Adj x y → (amalgamGraph A B).Adj (h • x) (h • y) := by
    intro h x y hxy
    rcases (amalgamGraph_adj_iff x y).mp hxy with ⟨g, rfl, rfl⟩ | ⟨g, rfl, rfl⟩
    · exact (amalgamGraph_adj_iff _ _).mpr (Or.inl ⟨h * g, rfl, rfl⟩)
    · exact (amalgamGraph_adj_iff _ _).mpr (Or.inr ⟨h * g, rfl, rfl⟩)
  refine ⟨fun hxy => ?_, key h x y⟩
  have := key h⁻¹ _ _ hxy
  simpa [smul_smul] using this

def smulHom (h : G) : amalgamGraph A B →g amalgamGraph A B where
  toFun := fun x => h • x
  map_rel' := fun {x y} hxy => (smul_adj_iff h x y).mpr hxy

theorem reachable_smul (h : G) {x y : (G ⧸ A) ⊕ (G ⧸ B)}
    (hr : (amalgamGraph A B).Reachable x y) :
    (amalgamGraph A B).Reachable (h • x) (h • y) :=
  hr.map (smulHom h)

theorem mem_stabilizer_alphaV (g : G) : g ∈ MulAction.stabilizer G (alphaV A B) ↔ g ∈ A := by
  rw [MulAction.mem_stabilizer_iff]
  show Sum.inl (g • ((1 : G) : G ⧸ A)) = Sum.inl ((1 : G) : G ⧸ A) ↔ _
  simp [QuotientGroup.eq]

theorem mem_stabilizer_betaV (g : G) : g ∈ MulAction.stabilizer G (betaV A B) ↔ g ∈ B := by
  rw [MulAction.mem_stabilizer_iff]
  show Sum.inr (g • ((1 : G) : G ⧸ B)) = Sum.inr ((1 : G) : G ⧸ B) ↔ _
  simp [QuotientGroup.eq]

def reachSub (A B : Subgroup G) : Subgroup G where
  carrier := {x | (amalgamGraph A B).Reachable (alphaV A B) (x • alphaV A B) ∧
      (amalgamGraph A B).Reachable (alphaV A B) (x • betaV A B)}
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨?_, ?_⟩
    · rw [mul_smul]; exact hx1.trans (reachable_smul x hy1)
    · rw [mul_smul]; exact hx1.trans (reachable_smul x hy2)
  one_mem' := by
    simp only [Set.mem_setOf_eq, one_smul]
    exact ⟨SimpleGraph.Reachable.refl _, adj_alphaV_betaV.reachable⟩
  inv_mem' := by
    rintro x ⟨hx1, -⟩
    have h1 : (amalgamGraph A B).Reachable (alphaV A B) (x⁻¹ • alphaV A B) := by
      have := reachable_smul x⁻¹ hx1
      rw [inv_smul_smul] at this
      exact this.symm
    exact ⟨h1, h1.trans (reachable_smul x⁻¹ adj_alphaV_betaV.reachable)⟩

theorem le_reachSub : A ⊔ B ≤ reachSub A B := by
  refine sup_le (fun x hx => ?_) (fun x hx => ?_)
  · have hxα : x • alphaV A B = alphaV A B := (MulAction.mem_stabilizer_iff).mp
      ((mem_stabilizer_alphaV x).mpr hx)
    refine ⟨by rw [hxα], ?_⟩
    refine SimpleGraph.Adj.reachable ((amalgamGraph_adj_iff _ _).mpr (Or.inl ⟨x, ?_, ?_⟩))
    · show Sum.inl ((1 : G) : G ⧸ A) = Sum.inl ((x : G) : G ⧸ A)
      simp [QuotientGroup.eq, hx]
    · show Sum.inr ((x * 1 : G) : G ⧸ B) = Sum.inr ((x : G) : G ⧸ B)
      simp
  · have hxβ : x • betaV A B = betaV A B := (MulAction.mem_stabilizer_iff).mp
      ((mem_stabilizer_betaV x).mpr hx)
    refine ⟨?_, by rw [hxβ]; exact adj_alphaV_betaV.reachable⟩
    have h1 : (amalgamGraph A B).Adj (x • alphaV A B) (betaV A B) := by
      refine (amalgamGraph_adj_iff _ _).mpr (Or.inl ⟨x, ?_, ?_⟩)
      · show Sum.inl ((x * 1 : G) : G ⧸ A) = Sum.inl ((x : G) : G ⧸ A)
        simp
      · show Sum.inr ((1 : G) : G ⧸ B) = Sum.inr ((x : G) : G ⧸ B)
        simp [QuotientGroup.eq, hx]
    exact adj_alphaV_betaV.reachable.trans h1.reachable.symm

theorem conj_mem_inf_of_forall_reachable_le_kernelAt {Z : Subgroup G}
    (h : ∀ ε, (amalgamGraph A B).Reachable (alphaV A B) ε → Z ≤ kernelAt (amalgamGraph A B) ε)
    {x : G} (hx : x ∈ A ⊔ B) {z : G} (hz : z ∈ Z) : x⁻¹ * z * x ∈ A ⊓ B := by
  obtain ⟨hr1, hr2⟩ := le_reachSub hx
  have h1 : z • (x • alphaV A B) = x • alphaV A B :=
    (MulAction.mem_stabilizer_iff).mp (Subgroup.mem_inf.mp (h _ hr1 hz)).1
  have h2 : z • (x • betaV A B) = x • betaV A B :=
    (MulAction.mem_stabilizer_iff).mp (Subgroup.mem_inf.mp (h _ hr2 hz)).1
  have key : ∀ v : (G ⧸ A) ⊕ (G ⧸ B), z • (x • v) = x • v → (x⁻¹ * z * x) • v = v := by
    intro v hv
    rw [mul_smul, mul_smul, hv, inv_smul_smul]
  exact ⟨(mem_stabilizer_alphaV _).mp ((MulAction.mem_stabilizer_iff).mpr (key _ h1)),
    (mem_stabilizer_betaV _).mp ((MulAction.mem_stabilizer_iff).mpr (key _ h2))⟩

def coreInf (A B : Subgroup G) : Subgroup G where
  carrier := {g | ∀ x ∈ A ⊔ B, x⁻¹ * g * x ∈ A ⊓ B}
  mul_mem' := by
    intro a b ha hb x hx
    have : x⁻¹ * (a * b) * x = (x⁻¹ * a * x) * (x⁻¹ * b * x) := by group
    rw [this]
    exact (A ⊓ B).mul_mem (ha x hx) (hb x hx)
  one_mem' := by
    intro x hx
    simpa using (A ⊓ B).one_mem
  inv_mem' := by
    intro a ha x hx
    have : x⁻¹ * a⁻¹ * x = (x⁻¹ * a * x)⁻¹ := by group
    rw [this]
    exact (A ⊓ B).inv_mem (ha x hx)

theorem coreInf_le (A B : Subgroup G) : coreInf A B ≤ A ⊓ B := by
  intro g hg
  simpa using hg 1 (Subgroup.one_mem _)

theorem sup_le_normalizer_coreInf (A B : Subgroup G) :
    A ⊔ B ≤ Subgroup.normalizer (coreInf A B : Set G) := by
  have key : ∀ y ∈ A ⊔ B, ∀ g ∈ coreInf A B, y * g * y⁻¹ ∈ coreInf A B := by
    intro y hy g hg x hx
    have h1 := hg (y⁻¹ * x) ((A ⊔ B).mul_mem ((A ⊔ B).inv_mem hy) hx)
    have e : x⁻¹ * (y * g * y⁻¹) * x = (y⁻¹ * x)⁻¹ * g * (y⁻¹ * x) := by group
    rw [e]
    exact h1
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => key y hy g hg, fun hg => ?_⟩
  have := key y⁻¹ ((A ⊔ B).inv_mem hy) _ hg
  simpa [mul_assoc] using this

theorem mem_normalizer_coreInf {A B : Subgroup G} {y : G}
    (hS : y ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G))
    (hI : y ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G)) :
    y ∈ Subgroup.normalizer (coreInf A B : Set G) := by
  have key : ∀ y : G, y ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) →
      y ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) →
      ∀ g ∈ coreInf A B, y * g * y⁻¹ ∈ coreInf A B := by
    intro y hS hI g hg x hx
    have hx' : y⁻¹ * x * y ∈ A ⊔ B := (Subgroup.mem_normalizer_iff''.mp hS x).mp hx
    have h1 := hg (y⁻¹ * x * y) hx'
    have e : x⁻¹ * (y * g * y⁻¹) * x = y * ((y⁻¹ * x * y)⁻¹ * g * (y⁻¹ * x * y)) * y⁻¹ := by
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp hI _).mp h1
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => key y hS hI g hg, fun hg => ?_⟩
  have := key y⁻¹ ((Subgroup.normalizer _).inv_mem hS) ((Subgroup.normalizer _).inv_mem hI) _ hg
  simpa [mul_assoc] using this

theorem mem_normalizer_sup {A B : Subgroup G} {y : G}
    (hA : y ∈ Subgroup.normalizer (A : Set G)) (hB : y ∈ Subgroup.normalizer (B : Set G)) :
    y ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  rw [Subgroup.map_sup, Subgroup.mem_normalizer_iff_map_conj_eq.mp hA,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hB]

theorem mem_normalizer_coreInf_of_mem {A B : Subgroup G} {y : G}
    (hA : y ∈ Subgroup.normalizer (A : Set G)) (hB : y ∈ Subgroup.normalizer (B : Set G)) :
    y ∈ Subgroup.normalizer (coreInf A B : Set G) :=
  mem_normalizer_coreInf (mem_normalizer_sup hA hB)
    (Subgroup.inf_normalizer_le_normalizer_inf ⟨hA, hB⟩)

theorem le_coreInf_of_forall_reachable_le_kernelAt {Z : Subgroup G}
    (h : ∀ ε, (amalgamGraph A B).Reachable (alphaV A B) ε → Z ≤ kernelAt (amalgamGraph A B) ε) :
    Z ≤ coreInf A B := fun z hz x hx =>
  conj_mem_inf_of_forall_reachable_le_kernelAt h hx hz

end Basic

end CFSG.Quasithin.CosetGraph
