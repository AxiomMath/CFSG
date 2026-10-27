module

public import CFSG.Quasithin.Recognition.F112Crit.OddFiveQ
public import CFSG.Quasithin.Recognition.F112Crit.OddRho
public import CFSG.Quasithin.Recognition.F112Crit.TorusCompSmul

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open Subgroup
open scoped Pointwise

open CosetGeom (graph stab ballStab nbrs vtype)

section Valency

variable {G : Type} [Group G] {G₀ G₁ G₂ : Subgroup G}

private theorem eq_or_eq_or_eq_of_ncard_eq_three {α : Type*} {s : Set α} (hs : s.ncard = 3)
    {e a b : α} (he : e ∈ s) (ha : a ∈ s) (hb : b ∈ s) (hae : a ≠ e) (hbe : b ≠ e) (hab : a ≠ b)
    {v : α} (hv : v ∈ s) : v = e ∨ v = a ∨ v = b := by
  have hsub : ({e, a, b} : Set α) ⊆ s := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact he
    · exact ha
    · exact hb
  have h3 : ({e, a, b} : Set α).ncard = 3 := by
    rw [Set.ncard_eq_three]
    exact ⟨e, a, b, hae.symm, hbe.symm, hab, rfl⟩
  have hfin : s.Finite := Set.finite_of_ncard_ne_zero (by rw [hs]; norm_num)
  have hset := Set.eq_of_subset_of_ncard_le hsub (hs.trans h3.symm).le hfin
  rw [← hset] at hv
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hv

private theorem exists_two_of_ncard_eq_three {α : Type*} {s : Set α} (hs : s.ncard = 3) {e : α}
    (he : e ∈ s) : ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ e ∧ b ≠ e ∧ a ≠ b := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Set.ncard_eq_three.mp hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
  rcases he with rfl | rfl | rfl
  · exact ⟨y, z, by simp, by simp, hxy.symm, hxz.symm, hyz⟩
  · exact ⟨x, z, by simp, by simp, hxy, hyz.symm, hxz⟩
  · exact ⟨x, y, by simp, by simp, hxz, hyz, hxy⟩

private theorem exists_ne_three_of_four {α : Type*} {P : α → Prop} {q₁ q₂ q₃ q₄ : α}
    (hP₁ : P q₁) (hP₂ : P q₂) (hP₃ : P q₃) (hP₄ : P q₄) (h₁₂ : q₁ ≠ q₂) (h₁₃ : q₁ ≠ q₃)
    (h₁₄ : q₁ ≠ q₄) (h₂₃ : q₂ ≠ q₃) (h₂₄ : q₂ ≠ q₄) (h₃₄ : q₃ ≠ q₄) (f₁ f₂ f₃ : α) :
    ∃ q, P q ∧ q ≠ f₁ ∧ q ≠ f₂ ∧ q ≠ f₃ := by
  by_contra hcon
  have hall : ∀ q, P q → q = f₁ ∨ q = f₂ ∨ q = f₃ := fun q hq => by
    by_contra hq'
    exact hcon ⟨q, hq, fun h => hq' (Or.inl h), fun h => hq' (Or.inr (Or.inl h)),
      fun h => hq' (Or.inr (Or.inr h))⟩
  rcases hall q₁ hP₁ with e₁ | e₁ | e₁ <;> rcases hall q₂ hP₂ with e₂ | e₂ | e₂ <;>
    rcases hall q₃ hP₃ with e₃ | e₃ | e₃ <;> rcases hall q₄ hP₄ with e₄ | e₄ | e₄ <;>
    first
    | exact h₁₂ (e₁.trans e₂.symm) | exact h₁₃ (e₁.trans e₃.symm) | exact h₁₄ (e₁.trans e₄.symm)
    | exact h₂₃ (e₂.trans e₃.symm) | exact h₂₄ (e₂.trans e₄.symm) | exact h₃₄ (e₃.trans e₄.symm)

theorem smul_eq_or_swap_of_ncard_eq_three {y e a b : CosetGeom G₀ G₁ G₂}
    (hy : (nbrs y).ncard = 3) (he : e ∈ nbrs y) (ha : a ∈ nbrs y) (hb : b ∈ nbrs y)
    (hae : a ≠ e) (hbe : b ≠ e) (hab : a ≠ b) {w : ↥G₀} (hwy : w • y = y) (hwe : w • e = e) :
    (w • a = a ∧ w • b = b) ∨ (w • a = b ∧ w • b = a) := by
  have hmem : ∀ v ∈ nbrs y, w • v ∈ nbrs y := fun v hv => by
    have h := (CosetGeom.smul_adj w).mpr hv
    rwa [hwy] at h
  have hinj : ∀ u v : CosetGeom G₀ G₁ G₂, w • u = w • v → u = v := fun u v h =>
    smul_left_cancel w h
  rcases eq_or_eq_or_eq_of_ncard_eq_three hy he ha hb hae hbe hab (hmem a ha) with h1 | h1 | h1
  · exact absurd (hinj a e (h1.trans hwe.symm)) hae
  · rcases eq_or_eq_or_eq_of_ncard_eq_three hy he ha hb hae hbe hab (hmem b hb) with h2 | h2 | h2
    · exact absurd (hinj b e (h2.trans hwe.symm)) hbe
    · exact absurd (hinj a b (h1.trans h2.symm)) hab
    · exact Or.inl ⟨h1, h2⟩
  · rcases eq_or_eq_or_eq_of_ncard_eq_three hy he ha hb hae hbe hab (hmem b hb) with h2 | h2 | h2
    · exact absurd (hinj b e (h2.trans hwe.symm)) hbe
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (hinj a b (h1.trans h2.symm)) hab

theorem mem_ballStab_one_iff_smul_eq (hG : G₀ = G₁ ⊔ G₂) {y e a b : CosetGeom G₀ G₁ G₂}
    (hy : (nbrs y).ncard = 3) (he : e ∈ nbrs y) (ha : a ∈ nbrs y) (hb : b ∈ nbrs y)
    (hae : a ≠ e) (hbe : b ≠ e) (hab : a ≠ b) {w : ↥G₀} (hwy : w • y = y) (hwe : w • e = e) :
    (w : G) ∈ ballStab 1 y ↔ w • a = a := by
  constructor
  · intro hw
    exact CosetGeom.smul_eq_of_mem_stab
      (CosetGeom.mem_ballStab.mp hw a (CosetGeom.dist_eq_one_iff_adj.mpr ha).le)
  · intro hwa
    have hwb : w • b = b := by
      rcases smul_eq_or_swap_of_ncard_eq_three hy he ha hb hae hbe hab hwy hwe with h | h
      · exact h.2
      · exact absurd (hwa.symm.trans h.1) hab
    refine CosetGeom.mem_ballStab.mpr fun v hv => CosetGeom.mem_stab_of_smul_eq ?_
    rcases (CosetGeom.dist_le_one_iff hG).mp hv with rfl | hadj
    · exact hwy
    · rcases eq_or_eq_or_eq_of_ncard_eq_three hy he ha hb hae hbe hab (v := v) hadj with
        rfl | rfl | rfl
      · exact hwe
      · exact hwa
      · exact hwb

theorem smul_swap_of_not_mem_ballStab_one (hG : G₀ = G₁ ⊔ G₂) {y e a b : CosetGeom G₀ G₁ G₂}
    (hy : (nbrs y).ncard = 3) (he : e ∈ nbrs y) (ha : a ∈ nbrs y) (hb : b ∈ nbrs y)
    (hae : a ≠ e) (hbe : b ≠ e) (hab : a ≠ b) {w : ↥G₀} (hwy : w • y = y) (hwe : w • e = e)
    (hw : (w : G) ∉ ballStab 1 y) : w • a = b ∧ w • b = a := by
  rcases smul_eq_or_swap_of_ncard_eq_three hy he ha hb hae hbe hab hwy hwe with h | h
  · exact absurd ((mem_ballStab_one_iff_smul_eq hG hy he ha hb hae hbe hab hwy hwe).mpr h.1) hw
  · exact h

theorem mul_mem_ballStab_one_iff (hG : G₀ = G₁ ⊔ G₂) {y e : CosetGeom G₀ G₁ G₂}
    (hy : (nbrs y).ncard = 3) (he : e ∈ nbrs y) {x z : G} (hx : x ∈ stab y ⊓ stab e)
    (hz : z ∈ stab y ⊓ stab e) :
    x * z ∈ ballStab 1 y ↔ (x ∈ ballStab 1 y ↔ z ∈ ballStab 1 y) := by
  have h := rhoNbrs_mul hG hy he hx hz
  rw [← rhoNbrs_eq_zero_iff, ← rhoNbrs_eq_zero_iff, ← rhoNbrs_eq_zero_iff, h]
  generalize rhoNbrs x y = p
  generalize rhoNbrs z y = q
  revert p q
  decide

private theorem mem_ballStab_iff_conj {v : CosetGeom G₀ G₁ G₂} {g : G} (hg : g ∈ stab v)
    (y : G) : y ∈ ballStab 1 v ↔ g * y * g⁻¹ ∈ ballStab 1 v :=
  mem_normalizer_iff.mp (CosetGeom.le_normalizer_ballStab 1 v hg) y

private theorem mem_pCoreOf_iff_conj {v : CosetGeom G₀ G₁ G₂} {g : G} (hg : g ∈ stab v)
    (y : G) : y ∈ pCoreOf 2 (stab v) ↔ g * y * g⁻¹ ∈ pCoreOf 2 (stab v) :=
  mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (stab v) hg) y

private theorem conj_mem_pCoreOf_smul (g : ↥G₀) {v : CosetGeom G₀ G₁ G₂} {x : G}
    (hx : x ∈ pCoreOf 2 (stab v)) : (g : G) * x * (g : G)⁻¹ ∈ pCoreOf 2 (stab (g • v)) := by
  rw [CosetGeom.stab_smul, pCoreOf_conjSub, mem_conjSub]
  simpa [mul_assoc] using hx

private theorem conj_mem_ballStab_smul (g : ↥G₀) {v : CosetGeom G₀ G₁ G₂} {x : G}
    (hx : x ∈ ballStab 1 v) : (g : G) * x * (g : G)⁻¹ ∈ ballStab 1 (g • v) := by
  rw [CosetGeom.ballStab_smul, mem_conjSub]
  simpa [mul_assoc] using hx

private theorem commutator_mul_mul_mem {N : Subgroup G} {a b α β : G}
    (ha : a ∈ normalizer (N : Set G)) (hb : b ∈ normalizer (N : Set G))
    (h₁ : α * b * α⁻¹ * b⁻¹ ∈ N) (h₂ : α * β * α⁻¹ * β⁻¹ ∈ N) (h₃ : β * a * β⁻¹ * a⁻¹ ∈ N) :
    (a * b * a⁻¹ * b⁻¹)⁻¹ * (a * α * (b * β) * (a * α)⁻¹ * (b * β)⁻¹) ∈ N := by
  have hconj : ∀ g ∈ normalizer (N : Set G), ∀ n ∈ N, g * n * g⁻¹ ∈ N :=
    fun g hg n hn => (mem_normalizer_iff.mp hg n).mp hn
  have hab : a * b ∈ normalizer (N : Set G) := mul_mem ha hb
  have haba : a * b * a⁻¹ ∈ normalizer (N : Set G) := mul_mem hab (inv_mem ha)
  have hc : a * b * a⁻¹ * b⁻¹ ∈ normalizer (N : Set G) := mul_mem haba (inv_mem hb)
  have hm : (a * (α * b * α⁻¹ * b⁻¹) * a⁻¹) * ((a * b) * (α * β * α⁻¹ * β⁻¹) * (a * b)⁻¹) *
      ((a * b * a⁻¹) * (β * a * β⁻¹ * a⁻¹)⁻¹ * (a * b * a⁻¹)⁻¹) ∈ N :=
    mul_mem (mul_mem (hconj a ha _ h₁) (hconj _ hab _ h₂)) (hconj _ haba _ (inv_mem h₃))
  have e : (a * b * a⁻¹ * b⁻¹)⁻¹ * (a * α * (b * β) * (a * α)⁻¹ * (b * β)⁻¹) =
      (a * b * a⁻¹ * b⁻¹)⁻¹ * ((a * (α * b * α⁻¹ * b⁻¹) * a⁻¹) *
        ((a * b) * (α * β * α⁻¹ * β⁻¹) * (a * b)⁻¹) *
        ((a * b * a⁻¹) * (β * a * β⁻¹ * a⁻¹)⁻¹ * (a * b * a⁻¹)⁻¹)) *
        (a * b * a⁻¹ * b⁻¹)⁻¹⁻¹ := by
    group
  rw [e]
  exact hconj _ (inv_mem hc) _ hm

private theorem eq_or_eq_of_two {V : Type} {Γ : SimpleGraph V} {Δ : Set V} {sm : V → Prop}
    (h : Fan86.Tutte.SubdivCubic Γ Δ sm) {e a b v : V} (he : e ∈ Δ) (hesm : ¬ sm e)
    (ha : a ∈ Δ) (hea : Γ.Adj e a) (hb : b ∈ Δ) (heb : Γ.Adj e b) (hab : a ≠ b)
    (hv : v ∈ Δ) (hev : Γ.Adj e v) : v = a ∨ v = b := by
  obtain ⟨y₁, y₂, -, hy⟩ := h.two e he hesm
  rcases (hy a).1 ⟨ha, hea⟩ with h1 | h1 <;> rcases (hy b).1 ⟨hb, heb⟩ with h2 | h2 <;>
    rcases (hy v).1 ⟨hv, hev⟩ with h3 | h3 <;>
    first
    | exact absurd (h1.trans h2.symm) hab | exact Or.inl (h3.trans h1.symm)
    | exact Or.inr (h3.trans h2.symm)

private theorem exists_ne_nbr {V : Type} {Γ : SimpleGraph V} {Δ : Set V} {sm : V → Prop}
    (h : Fan86.Tutte.SubdivCubic Γ Δ sm) {e a : V} (he : e ∈ Δ) (hesm : ¬ sm e) (ha : a ∈ Δ)
    (hea : Γ.Adj e a) : ∃ b, b ∈ Δ ∧ Γ.Adj e b ∧ b ≠ a := by
  obtain ⟨y₁, y₂, hne, hy⟩ := h.two e he hesm
  rcases (hy a).1 ⟨ha, hea⟩ with rfl | rfl
  · exact ⟨y₂, ((hy y₂).2 (Or.inr rfl)).1, ((hy y₂).2 (Or.inr rfl)).2, hne.symm⟩
  · exact ⟨y₁, ((hy y₁).2 (Or.inl rfl)).1, ((hy y₁).2 (Or.inl rfl)).2, hne⟩

private theorem ncard_nbrs_eq_three {X : Subgroup G} {δ y : CosetGeom G₀ G₁ G₂}
    (hT : TorusGraph X δ) (hy : y ∈ torusComp X δ) (hyv : vtype y = true) :
    (nbrs y).ncard = 3 := by
  rw [← Nat.card_coe_set_eq]
  exact hT.subdiv.card_nbrs y hy hyv

end Valency

section Center

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ : Subgroup G}

private theorem mem_stab_inf_of_mem_pCoreOf {T : Subgroup G} (hyp : AmalgamHyp G₀ G₁ G₂ T)
    {μ p : CosetGeom G₀ G₁ G₂} (hp : (graph G₀ G₁ G₂).Adj μ p) {x : G}
    (hx : x ∈ pCoreOf 2 (stab μ)) : x ∈ stab p ⊓ stab μ :=
  mem_inf.mpr ⟨pCoreOf_stab_le_stab hyp (CosetGeom.mem_nbrs_symm hp) hx, pCoreOf_le 2 _ hx⟩

theorem le_ballStab_of_two_stars (hG : G₀ = G₁ ⊔ G₂) {X W : Subgroup G}
    {δ y e₁ e₂ e₃ y₁ y₂ y₃ : CosetGeom G₀ G₁ G₂}
    (hXodd : Odd (Nat.card X)) (hΔ : TorusGraph X δ)
    (hy : y ∈ torusComp X δ) (hyv : vtype y = true)
    (he₁ : (graph G₀ G₁ G₂).Adj y e₁) (he₂ : (graph G₀ G₁ G₂).Adj y e₂)
    (he₃ : (graph G₀ G₁ G₂).Adj y e₃) (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃)
    (hy₁ : y₁ ∈ torusComp X δ) (hy₂ : y₂ ∈ torusComp X δ) (hy₃ : y₃ ∈ torusComp X δ)
    (h₁ : (graph G₀ G₁ G₂).Adj e₁ y₁) (h₂ : (graph G₀ G₁ G₂).Adj e₂ y₂)
    (h₃ : (graph G₀ G₁ G₂).Adj e₃ y₃) (hy₁y : y₁ ≠ y) (hy₂y : y₂ ≠ y) (hy₃y : y₃ ≠ y)
    (hW2 : IsPGroup 2 W) (hXW : X ≤ normalizer (W : Set G))
    (hWy : W ≤ ballStab 1 y) (hWy₁ : W ≤ stab y₁) (hWy₂ : W ≤ ballStab 1 y₂)
    (hWy₃ : W ≤ ballStab 1 y₃) : W ≤ ballStab 1 y₁ := by
  have hy₁v : vtype y₁ = true :=
    vtype_eq_true_of_mem_nbrs (vtype_eq_false_of_mem_nbrs hyv he₁) h₁
  have hXy₁ : X ≤ ballStab 1 y₁ := hΔ.small_le y₁ hy₁ hy₁v
  have hXB : X ≤ normalizer (ballStab 1 y₁ : Set G) :=
    (hXy₁.trans (CosetGeom.ballStab_le_stab 1 y₁)).trans (CosetGeom.le_normalizer_ballStab 1 y₁)
  have hXW₁ : X ≤ normalizer ((W ⊓ ballStab 1 y₁ : Subgroup G) : Set G) :=
    F7.le_normalizer_inf hXW hXB
  intro g hgW
  have hcomm : ∀ x ∈ X, g * x * g⁻¹ * x⁻¹ ∈ W ⊓ ballStab 1 y₁ := by
    intro x hx
    refine mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : x * g⁻¹ * x⁻¹ ∈ W := (mem_normalizer_iff.mp (hXW hx) g⁻¹).mp (inv_mem hgW)
      have e : g * x * g⁻¹ * x⁻¹ = g * (x * g⁻¹ * x⁻¹) := by group
      rw [e]
      exact mul_mem hgW h1
    · have h1 : g * x * g⁻¹ ∈ ballStab 1 y₁ :=
        (mem_normalizer_iff.mp (CosetGeom.le_normalizer_ballStab 1 y₁ (hWy₁ hgW)) x).mp
          (hXy₁ hx)
      exact mul_mem h1 (inv_mem (hXy₁ hx))
  obtain ⟨n, hn, c, hcW, hcX, rfl⟩ :=
    exists_mul_centralizer_of_comm_mem hW2 hXodd inf_le_left hXW hXW₁ hgW hcomm
  refine mul_mem (mem_inf.mp hn).2 ?_
  have hcy : c ∈ ballStab 1 y := hWy hcW
  have hc0 : c ∈ G₀ := CosetGeom.stab_le y (CosetGeom.ballStab_le_stab 1 y hcy)
  obtain ⟨c', rfl⟩ : ∃ c' : ↥G₀, (c' : G) = c := ⟨⟨c, hc0⟩, rfl⟩
  have hcn : (c' : G) ∈ normalizer (X : Set G) := by
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hcX h hh, mul_inv_cancel_right]
      exact hh
    · intro hh
      have e1 := hcX _ hh
      have e : h = (c' : G) * h * (c' : G)⁻¹ :=
        calc h = (c' : G)⁻¹ * (((c' : G) * h * (c' : G)⁻¹) * c') := by group
          _ = (c' : G)⁻¹ * (c' * ((c' : G) * h * (c' : G)⁻¹)) := by rw [← e1]
          _ = (c' : G) * h * (c' : G)⁻¹ := by group
      rw [e]
      exact hh
  have hcy' : c' • y = y := CosetGeom.smul_eq_of_mem_stab (CosetGeom.ballStab_le_stab 1 y hcy)
  have hstab : ∀ m : ↥G₀, (m : G) ∈ normalizer (X : Set G) → ∀ v, v ∈ torusComp X δ →
      m • v ∈ torusComp X δ → m ∈ MulAction.stabilizer (↥G₀) (torusComp X δ) :=
    fun m hm v hv hmv => MulAction.mem_stabilizer_iff.mpr (smul_torusComp_eq hm hv hmv)
  have hfixB : ∀ {z : CosetGeom G₀ G₁ G₂}, (c' : G) ∈ ballStab 1 z →
      ∀ v, (graph G₀ G₁ G₂).Adj z v → c' • v = v := fun hz v hv =>
    CosetGeom.smul_eq_of_mem_stab
      (CosetGeom.mem_ballStab.mp hz v (CosetGeom.dist_eq_one_iff_adj.mpr hv).le)
  have hfix : ∀ v, (graph G₀ G₁ G₂).Adj y₁ v → c' • v = v := by
    refine Fan86.Tutte.SubdivCubic.fixes_nbrs_of_fixes (fun a u v => CosetGeom.smul_adj a)
      (MulAction.stabilizer (↥G₀) (torusComp X δ)) ?_ ?_ ?_ ?_ hΔ.subdiv
      (hstab c' hcn y hy (by rw [hcy']; exact hy)) hy hyv he₁ he₂ he₃ h₁₂ h₁₃ h₂₃ hy₁ hy₂ hy₃
      h₁ h₂ h₃ hy₁y hy₂y hy₃y (hfixB hcy) (hfixB (hWy₂ hcW)) (hfixB (hWy₃ hcW))
    · intro m hm v hv
      rw [← MulAction.mem_stabilizer_iff.mp hm]
      exact Set.smul_mem_smul_set hv
    · intro m _ v
      rw [CosetGeom.vtype_smul]
    · intro z₁ hz₁ hsm₁ z₂ hz₂ hsm₂
      obtain ⟨m, hm, hmz⟩ := hΔ.trans z₁ hz₁ hsm₁ z₂ hz₂ hsm₂
      exact ⟨m, hstab m hm z₁ hz₁ (by rw [hmz]; exact hz₂), hmz⟩
    · intro z₁ hz₁ hsm₁ u u' hu hu'
      obtain ⟨m, hm, hmz, hmu⟩ := hΔ.loc z₁ hz₁ hsm₁ u u' hu hu'
      exact ⟨m, hstab m hm z₁ hz₁ (by rw [hmz]; exact hz₁), hmz, hmu⟩
  refine CosetGeom.mem_ballStab.mpr fun v hv => CosetGeom.mem_stab_of_smul_eq ?_
  rcases (CosetGeom.dist_le_one_iff hG).mp hv with rfl | hadj
  · exact CosetGeom.smul_eq_of_mem_stab (hWy₁ hcW)
  · exact hfix v hadj

theorem not_inf_le_ballStab_of_center {T : Subgroup G} (hyp : AmalgamHyp G₀ G₁ G₂ T)
    {δ μ₁ μ₂ μ₃ : CosetGeom G₀ G₁ G₂} (hδ3 : (nbrs δ).ncard = 3) (hμ₁ : μ₁ ∈ nbrs δ)
    (hμ₂ : μ₂ ∈ nbrs δ) (hμ₃ : μ₃ ∈ nbrs δ) (h₂₁ : μ₂ ≠ μ₁) (h₃₁ : μ₃ ≠ μ₁) (h₂₃ : μ₂ ≠ μ₃)
    (hQ : ¬ pCoreOf 2 (stab μ₁) ≤ ballStab 1 δ)
    (hR1 : ∀ k ∈ pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ₁), ∀ g ∈ pCoreOf 2 (stab δ),
      k * g * k⁻¹ * g⁻¹ ∈ ballStab 1 μ₃)
    (hR2₃₂ : ∀ a ∈ pCoreOf 2 (stab δ), ∀ b ∈ pCoreOf 2 (stab δ),
      ∃ k ∈ pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ₃), k⁻¹ * (a * b * a⁻¹ * b⁻¹) ∈ ballStab 1 μ₂)
    (hR2₂₃ : ∀ a ∈ pCoreOf 2 (stab δ), ∀ b ∈ pCoreOf 2 (stab δ),
      ∃ k ∈ pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ₂), k⁻¹ * (a * b * a⁻¹ * b⁻¹) ∈ ballStab 1 μ₃)
    (hR3 : ∀ k ∈ pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ₂), k * k ∈ ballStab 1 μ₁)
    (hR4 : ∃ a ∈ pCoreOf 2 (stab δ), ∃ b ∈ pCoreOf 2 (stab δ),
      a * b * a⁻¹ * b⁻¹ ∉ ballStab 1 μ₁) :
    ¬ (pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ₂)) ⊓ (pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ₃)) ≤
      ballStab 1 μ₁ := by
  intro hA
  have hG := hyp.gen
  have hQδμ : ∀ {μ : CosetGeom G₀ G₁ G₂}, μ ∈ nbrs δ → pCoreOf 2 (stab δ) ≤ stab μ := fun hμ =>
    pCoreOf_stab_le_stab hyp (CosetGeom.mem_nbrs_symm hμ)
  have hQB : ∀ γ : CosetGeom G₀ G₁ G₂, pCoreOf 2 (stab γ) ≤ ballStab 1 γ :=
    CosetGeom.pCoreOf_stab_le_ballStab_one hyp
  obtain ⟨a, ha, b, hb, hc⟩ := hR4
  have hcQ : a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 (stab δ) :=
    mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  obtain ⟨k₃, hk₃, hk₃c⟩ := hR2₃₂ a ha b hb
  obtain ⟨k₂, hk₂, hk₂c⟩ := hR2₂₃ a ha b hb
  have hk₃δ : k₃ ∈ pCoreOf 2 (stab δ) := (mem_inf.mp hk₃).1
  have hk₃3 : k₃ ∈ pCoreOf 2 (stab μ₃) := (mem_inf.mp hk₃).2
  have hk₂δ : k₂ ∈ pCoreOf 2 (stab δ) := (mem_inf.mp hk₂).1
  have hk₂2 : k₂ ∈ pCoreOf 2 (stab μ₂) := (mem_inf.mp hk₂).2
  have hdB2 : k₃⁻¹ * k₂⁻¹ * (a * b * a⁻¹ * b⁻¹) ∈ ballStab 1 μ₂ := by
    have h1 := (mem_ballStab_iff_conj (inv_mem (hQδμ hμ₂ hk₃δ)) _).mp (inv_mem (hQB μ₂ hk₂2))
    have e : k₃⁻¹ * k₂⁻¹ * (a * b * a⁻¹ * b⁻¹) =
        (k₃⁻¹ * k₂⁻¹ * k₃⁻¹⁻¹) * (k₃⁻¹ * (a * b * a⁻¹ * b⁻¹)) := by group
    rw [e]
    exact mul_mem h1 hk₃c
  have hdB3 : k₃⁻¹ * k₂⁻¹ * (a * b * a⁻¹ * b⁻¹) ∈ ballStab 1 μ₃ := by
    rw [mul_assoc k₃⁻¹ k₂⁻¹ (a * b * a⁻¹ * b⁻¹)]
    exact mul_mem (inv_mem (hQB μ₃ hk₃3)) hk₂c
  have hdδ : k₃⁻¹ * k₂⁻¹ * (a * b * a⁻¹ * b⁻¹) ∈ pCoreOf 2 (stab δ) :=
    mul_mem (mul_mem (inv_mem hk₃δ) (inv_mem hk₂δ)) hcQ
  have hdB1 : k₃⁻¹ * k₂⁻¹ * (a * b * a⁻¹ * b⁻¹) ∈ ballStab 1 μ₁ :=
    hA (mem_inf.mpr ⟨mem_inf.mpr ⟨hdδ, pCoreOf_inf_ballStab_le hμ₂ (mem_inf.mpr ⟨hdδ, hdB2⟩)⟩,
      mem_inf.mpr ⟨hdδ, pCoreOf_inf_ballStab_le hμ₃ (mem_inf.mpr ⟨hdδ, hdB3⟩)⟩⟩)
  obtain ⟨t, htQ, htB⟩ := SetLike.not_le_iff_exists.mp hQ
  have htδ : t ∈ stab δ := pCoreOf_stab_le_stab hyp hμ₁ htQ
  have htμ₁ : t ∈ stab μ₁ := pCoreOf_le 2 _ htQ
  obtain ⟨t₀, rfl⟩ : ∃ t₀ : ↥G₀, (t₀ : G) = t := ⟨⟨t, CosetGeom.stab_le δ htδ⟩, rfl⟩
  obtain ⟨ht₂, ht₃⟩ := smul_swap_of_not_mem_ballStab_one hG hδ3 hμ₁ hμ₂ hμ₃ h₂₁ h₃₁ h₂₃
    (CosetGeom.smul_eq_of_mem_stab htδ) (CosetGeom.smul_eq_of_mem_stab htμ₁) htB
  have hnQδ : ∀ y ∈ pCoreOf 2 (stab δ), (t₀ : G) * y * (t₀ : G)⁻¹ ∈ pCoreOf 2 (stab δ) :=
    fun y hy => (mem_pCoreOf_iff_conj htδ y).mp hy
  have hK₁ : ∀ y ∈ pCoreOf 2 (stab δ), y⁻¹ * ((t₀ : G) * y * (t₀ : G)⁻¹) ∈
      pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ₁) := by
    intro y hy
    refine mem_inf.mpr ⟨mul_mem (inv_mem hy) (hnQδ y hy), ?_⟩
    have h1 := (mem_pCoreOf_iff_conj (inv_mem (hQδμ hμ₁ hy)) _).mp htQ
    have e : y⁻¹ * ((t₀ : G) * y * (t₀ : G)⁻¹) = (y⁻¹ * t₀ * y⁻¹⁻¹) * (t₀ : G)⁻¹ := by group
    rw [e]
    exact mul_mem h1 (inv_mem htQ)
  have he : (a * b * a⁻¹ * b⁻¹)⁻¹ * ((t₀ : G) * (a * b * a⁻¹ * b⁻¹) * (t₀ : G)⁻¹) ∈
      ballStab 1 μ₃ := by
    have hα := hK₁ a ha
    have hβ := hK₁ b hb
    have h1 := commutator_mul_mul_mem (N := ballStab 1 μ₃)
      (CosetGeom.le_normalizer_ballStab 1 μ₃ (hQδμ hμ₃ ha))
      (CosetGeom.le_normalizer_ballStab 1 μ₃ (hQδμ hμ₃ hb))
      (hR1 _ hα b hb) (hR1 _ hα _ (mem_inf.mp hβ).1) (hR1 _ hβ a ha)
    have e : (t₀ : G) * (a * b * a⁻¹ * b⁻¹) * (t₀ : G)⁻¹ =
        a * (a⁻¹ * ((t₀ : G) * a * (t₀ : G)⁻¹)) * (b * (b⁻¹ * ((t₀ : G) * b * (t₀ : G)⁻¹))) *
          (a * (a⁻¹ * ((t₀ : G) * a * (t₀ : G)⁻¹)))⁻¹ *
          (b * (b⁻¹ * ((t₀ : G) * b * (t₀ : G)⁻¹)))⁻¹ := by
      group
    rw [e]
    exact h1
  have hκ : (t₀ : G) * k₃ * (t₀ : G)⁻¹ ∈ pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ₂) := by
    refine mem_inf.mpr ⟨hnQδ k₃ hk₃δ, ?_⟩
    have h1 := conj_mem_pCoreOf_smul t₀ hk₃3
    rwa [ht₃] at h1
  have hκc : ((t₀ : G) * k₃ * (t₀ : G)⁻¹)⁻¹ * ((t₀ : G) * (a * b * a⁻¹ * b⁻¹) * (t₀ : G)⁻¹) ∈
      ballStab 1 μ₃ := by
    have h1 := conj_mem_ballStab_smul t₀ hk₃c
    rw [ht₂] at h1
    have e : ((t₀ : G) * k₃ * (t₀ : G)⁻¹)⁻¹ * ((t₀ : G) * (a * b * a⁻¹ * b⁻¹) * (t₀ : G)⁻¹) =
        (t₀ : G) * (k₃⁻¹ * (a * b * a⁻¹ * b⁻¹)) * (t₀ : G)⁻¹ := by group
    rw [e]
    exact h1
  have hmB3 : k₂⁻¹ * ((t₀ : G) * k₃ * (t₀ : G)⁻¹) ∈ ballStab 1 μ₃ := by
    have e : k₂⁻¹ * ((t₀ : G) * k₃ * (t₀ : G)⁻¹) = (k₂⁻¹ * (a * b * a⁻¹ * b⁻¹)) *
        ((a * b * a⁻¹ * b⁻¹)⁻¹ * ((t₀ : G) * (a * b * a⁻¹ * b⁻¹) * (t₀ : G)⁻¹)) *
        (((t₀ : G) * k₃ * (t₀ : G)⁻¹)⁻¹ *
          ((t₀ : G) * (a * b * a⁻¹ * b⁻¹) * (t₀ : G)⁻¹))⁻¹ := by
      group
    rw [e]
    exact mul_mem (mul_mem hk₂c he) (inv_mem hκc)
  have hmδ : k₂⁻¹ * ((t₀ : G) * k₃ * (t₀ : G)⁻¹) ∈ pCoreOf 2 (stab δ) :=
    mul_mem (inv_mem hk₂δ) (mem_inf.mp hκ).1
  have hmB1 : k₂⁻¹ * ((t₀ : G) * k₃ * (t₀ : G)⁻¹) ∈ ballStab 1 μ₁ :=
    hA (mem_inf.mpr ⟨mem_inf.mpr ⟨hmδ, mul_mem (inv_mem hk₂2) (mem_inf.mp hκ).2⟩,
      mem_inf.mpr ⟨hmδ, pCoreOf_inf_ballStab_le hμ₃ (mem_inf.mpr ⟨hmδ, hmB3⟩)⟩⟩)
  have htB1 : (t₀ : G) ∈ ballStab 1 μ₁ := hQB μ₁ htQ
  have hκk : ((t₀ : G) * k₃ * (t₀ : G)⁻¹)⁻¹ * k₃ ∈ ballStab 1 μ₁ := by
    have h1 := (mem_ballStab_iff_conj (inv_mem (hQδμ hμ₁ hk₃δ)) _).mp (inv_mem htB1)
    have e : ((t₀ : G) * k₃ * (t₀ : G)⁻¹)⁻¹ * k₃ =
        (t₀ : G) * (k₃⁻¹ * (t₀ : G)⁻¹ * k₃⁻¹⁻¹) := by group
    rw [e]
    exact mul_mem htB1 h1
  apply hc
  have e : a * b * a⁻¹ * b⁻¹ = (k₂ * k₂) * ((k₂⁻¹ * ((t₀ : G) * k₃ * (t₀ : G)⁻¹)) *
      (((t₀ : G) * k₃ * (t₀ : G)⁻¹)⁻¹ * k₃)) * (k₃⁻¹ * k₂⁻¹ * (a * b * a⁻¹ * b⁻¹)) := by group
  rw [e]
  exact mul_mem (mul_mem (hR3 k₂ hk₂) (mul_mem hmB1 hκk)) hdB1

theorem mem_ballStab_iff_conj_of_torus {T : Subgroup G} (hyp : AmalgamHyp G₀ G₁ G₂ T)
    {X : Subgroup G} {δ μ₁ μ₂ μ₃ p₁ p₂ p₃ : CosetGeom G₀ G₁ G₂}
    (hXodd : Odd (Nat.card X)) (hXδ : X ≤ stab δ) (hT : TorusGraph X δ) (hδv : vtype δ = true)
    (hμ₁ : μ₁ ∈ nbrs δ) (hμ₂ : μ₂ ∈ nbrs δ) (hμ₃ : μ₃ ∈ nbrs δ)
    (h₁₂ : μ₁ ≠ μ₂) (h₁₃ : μ₁ ≠ μ₃) (h₂₃ : μ₂ ≠ μ₃)
    (hp₁ : p₁ ∈ torusComp X δ) (hp₂ : p₂ ∈ torusComp X δ) (hp₃ : p₃ ∈ torusComp X δ)
    (hμp₁ : (graph G₀ G₁ G₂).Adj μ₁ p₁) (hμp₂ : (graph G₀ G₁ G₂).Adj μ₂ p₂)
    (hμp₃ : (graph G₀ G₁ G₂).Adj μ₃ p₃) (hp₁δ : p₁ ≠ δ) (hp₂δ : p₂ ≠ δ) (hp₃δ : p₃ ≠ δ)
    {k h : G} (hk : k ∈ pCoreOf 2 (stab δ)) (hk₁ : k ∈ pCoreOf 2 (stab μ₁))
    (hk₂ : k ∈ pCoreOf 2 (stab μ₂)) (hk₃ : k ∈ pCoreOf 2 (stab μ₃))
    (hh : h ∈ pCoreOf 2 (stab δ)) (hh₂ : h ∈ pCoreOf 2 (stab μ₂))
    (hh₃ : h ∈ pCoreOf 2 (stab μ₃)) :
    k ∈ ballStab 1 p₁ ↔ h⁻¹ * k * h ∈ ballStab 1 p₁ := by
  have hG := hyp.gen
  have hδΔ : δ ∈ torusComp X δ := mem_torusComp_self X δ
  have hpv : ∀ {μ p : CosetGeom G₀ G₁ G₂}, μ ∈ nbrs δ → (graph G₀ G₁ G₂).Adj μ p →
      vtype p = true := fun hμ hp =>
    vtype_eq_true_of_mem_nbrs (vtype_eq_false_of_mem_nbrs hδv hμ) hp
  have hQp : ∀ {μ p : CosetGeom G₀ G₁ G₂}, (graph G₀ G₁ G₂).Adj μ p →
      pCoreOf 2 (stab μ) ≤ stab p := fun hp =>
    pCoreOf_stab_le_stab hyp (CosetGeom.mem_nbrs_symm hp)
  have hXμ : ∀ {μ : CosetGeom G₀ G₁ G₂}, μ ∈ nbrs δ → X ≤ stab μ := fun hμ =>
    (hT.small_le δ hδΔ hδv).trans
      (CosetGeom.ballStab_le_stab_of_dist_le (CosetGeom.dist_eq_one_iff_adj.mpr hμ).le)
  have hXp : ∀ {μ p : CosetGeom G₀ G₁ G₂}, μ ∈ nbrs δ → (graph G₀ G₁ G₂).Adj μ p →
      p ∈ torusComp X δ → X ≤ normalizer (ballStab 1 p : Set G) := fun hμ hμp hp =>
    ((hT.small_le _ hp (hpv hμ hμp)).trans (CosetGeom.ballStab_le_stab 1 _)).trans
      (CosetGeom.le_normalizer_ballStab 1 _)
  have hz₁ : h⁻¹ * k * h ∈ pCoreOf 2 (stab μ₁) := by
    have h1 := (mem_pCoreOf_iff_conj
      (inv_mem (pCoreOf_stab_le_stab hyp (CosetGeom.mem_nbrs_symm hμ₁) hh)) k).mp hk₁
    rwa [inv_inv] at h1
  have hz₂ : h⁻¹ * k * h ∈ pCoreOf 2 (stab μ₂) := mul_mem (mul_mem (inv_mem hh₂) hk₂) hh₂
  have hz₃ : h⁻¹ * k * h ∈ pCoreOf 2 (stab μ₃) := mul_mem (mul_mem (inv_mem hh₃) hk₃) hh₃
  have hzδ : h⁻¹ * k * h ∈ pCoreOf 2 (stab δ) := mul_mem (mul_mem (inv_mem hh) hk) hh
  have hpar : ∀ {μ p : CosetGeom G₀ G₁ G₂}, (graph G₀ G₁ G₂).Adj μ p → μ ∈ nbrs δ →
      p ∈ torusComp X δ → k ∈ pCoreOf 2 (stab μ) → h⁻¹ * k * h ∈ pCoreOf 2 (stab μ) →
      (k⁻¹ * (h⁻¹ * k * h) ∈ ballStab 1 p ↔
        (k ∈ ballStab 1 p ↔ h⁻¹ * k * h ∈ ballStab 1 p)) := by
    intro μ p hμp hμ hp hkμ hzμ
    rw [mul_mem_ballStab_one_iff hG (ncard_nbrs_eq_three hT hp (hpv hμ hμp))
      (CosetGeom.mem_nbrs_symm hμp) (mem_stab_inf_of_mem_pCoreOf hyp hμp (inv_mem hkμ))
      (mem_stab_inf_of_mem_pCoreOf hyp hμp hzμ), inv_mem_iff]
  have hfixpar : ∀ {μ p : CosetGeom G₀ G₁ G₂}, (graph G₀ G₁ G₂).Adj μ p → μ ∈ nbrs δ →
      p ∈ torusComp X δ → k ∈ pCoreOf 2 (stab μ) → h ∈ pCoreOf 2 (stab μ) →
      k⁻¹ * (h⁻¹ * k * h) ∈ ballStab 1 p := by
    intro μ p hμp hμ hp hkμ hhμ
    refine (hpar hμp hμ hp hkμ (mul_mem (mul_mem (inv_mem hhμ) hkμ) hhμ)).mpr ?_
    have h1 := mem_ballStab_iff_conj (inv_mem (hQp hμp hhμ)) k
    rwa [inv_inv] at h1
  have hW : pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ₁) ⊓ pCoreOf 2 (stab μ₂) ⊓
      pCoreOf 2 (stab μ₃) ⊓ ballStab 1 p₂ ⊓ ballStab 1 p₃ ≤ ballStab 1 p₁ := by
    refine le_ballStab_of_two_stars hG hXodd hT hδΔ hδv hμ₁ hμ₂ hμ₃ h₁₂ h₁₃ h₂₃ hp₁ hp₂ hp₃
      hμp₁ hμp₂ hμp₃ hp₁δ hp₂δ hp₃δ ?_ ?_ ?_ ?_ ?_ ?_
    · exact (pCoreOf_isPGroup 2 (stab δ)).to_le fun x hx => hx.1.1.1.1.1
    · exact F7.le_normalizer_inf (F7.le_normalizer_inf (F7.le_normalizer_inf
        (F7.le_normalizer_inf (F7.le_normalizer_inf (hXδ.trans (le_normalizer_pCoreOf 2 _))
          ((hXμ hμ₁).trans (le_normalizer_pCoreOf 2 _)))
          ((hXμ hμ₂).trans (le_normalizer_pCoreOf 2 _)))
          ((hXμ hμ₃).trans (le_normalizer_pCoreOf 2 _))) (hXp hμ₂ hμp₂ hp₂))
          (hXp hμ₃ hμp₃ hp₃)
    · exact fun x hx => CosetGeom.pCoreOf_stab_le_ballStab_one hyp δ hx.1.1.1.1.1
    · exact fun x hx => hQp hμp₁ hx.1.1.1.1.2
    · exact fun x hx => hx.1.2
    · exact fun x hx => hx.2
  have hcW : k⁻¹ * (h⁻¹ * k * h) ∈ pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ₁) ⊓
      pCoreOf 2 (stab μ₂) ⊓ pCoreOf 2 (stab μ₃) ⊓ ballStab 1 p₂ ⊓ ballStab 1 p₃ :=
    mem_inf.mpr ⟨mem_inf.mpr ⟨mem_inf.mpr ⟨mem_inf.mpr ⟨mem_inf.mpr
      ⟨mul_mem (inv_mem hk) hzδ, mul_mem (inv_mem hk₁) hz₁⟩, mul_mem (inv_mem hk₂) hz₂⟩,
      mul_mem (inv_mem hk₃) hz₃⟩, hfixpar hμp₂ hμ₂ hp₂ hk₂ hh₂⟩, hfixpar hμp₃ hμ₃ hp₃ hk₃ hh₃⟩
  exact (hpar hμp₁ hμ₁ hp₁ hk₁ hz₁).mp (hW hcW)

theorem false_of_pCoreOf_inf_center {T : Subgroup G} (hyp : AmalgamHyp G₀ G₁ G₂ T)
    {δ μ₁ : CosetGeom G₀ G₁ G₂} (hδv : vtype δ = true) (hμ₁ : μ₁ ∈ nbrs δ) {X : Subgroup G}
    (hX : IsEdgeHall μ₁ δ X) (hT : TorusGraph X δ)
    (hQ : ¬ pCoreOf 2 (stab μ₁) ≤ ballStab 1 δ)
    (hreg : ∀ g ∈ pCoreOf 2 (stab δ), ∀ δ' ∈ nbrs μ₁, δ' ≠ δ → g ∈ stab δ' → g ∈ ballStab 1 μ₁)
    (hρ : ∀ δ' ∈ nbrs μ₁, ∀ δ'' ∈ nbrs μ₁, δ' ≠ δ'' → ∃ k ∈ pCoreOf 2 (stab μ₁),
      k ∉ ballStab 1 δ' ∧ k ∉ ballStab 1 δ'' ∧ ∀ x ∈ nbrs μ₁, x ≠ δ' → x ≠ δ'' → k ∈ ballStab 1 x)
    (hZ : ∀ μ ∈ nbrs δ, ∀ μ' ∈ nbrs δ, μ ≠ μ' →
      (∀ k ∈ pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ), ∀ g ∈ pCoreOf 2 (stab δ),
        k * g * k⁻¹ * g⁻¹ ∈ ballStab 1 μ') ∧
      (∀ a ∈ pCoreOf 2 (stab δ), ∀ b ∈ pCoreOf 2 (stab δ),
        ∃ k ∈ pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ), k⁻¹ * (a * b * a⁻¹ * b⁻¹) ∈ ballStab 1 μ') ∧
      (∀ k ∈ pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ), k * k ∈ ballStab 1 μ') ∧
      ∃ a ∈ pCoreOf 2 (stab δ), ∃ b ∈ pCoreOf 2 (stab δ), a * b * a⁻¹ * b⁻¹ ∉ ballStab 1 μ') :
    False := by
  have hG := hyp.gen
  obtain ⟨hXle, hXodd, -⟩ := hX
  have hXμ₁ : X ≤ stab μ₁ := hXle.trans inf_le_left
  have hXδ : X ≤ stab δ := hXle.trans inf_le_right
  have hδΔ : δ ∈ torusComp X δ := mem_torusComp_self X δ
  have hδ3 : (nbrs δ).ncard = 3 := ncard_nbrs_eq_three hT hδΔ hδv
  obtain ⟨μ₂, μ₃, hμ₂, hμ₃, h₂₁, h₃₁, h₂₃⟩ := exists_two_of_ncard_eq_three hδ3 hμ₁
  have hμΔ : ∀ {μ : CosetGeom G₀ G₁ G₂}, μ ∈ nbrs δ → μ ∈ torusComp X δ := fun hμ =>
    hT.subdiv.nbr_mem δ hδΔ hδv _ hμ
  have hμv : ∀ {μ : CosetGeom G₀ G₁ G₂}, μ ∈ nbrs δ → vtype μ = false := fun hμ =>
    vtype_eq_false_of_mem_nbrs hδv hμ
  have hXμ : ∀ {μ : CosetGeom G₀ G₁ G₂}, μ ∈ nbrs δ → X ≤ stab μ := fun hμ =>
    (hT.small_le δ hδΔ hδv).trans
      (CosetGeom.ballStab_le_stab_of_dist_le (CosetGeom.dist_eq_one_iff_adj.mpr hμ).le)
  have hQδμ : ∀ {μ : CosetGeom G₀ G₁ G₂}, μ ∈ nbrs δ → pCoreOf 2 (stab δ) ≤ stab μ := fun hμ =>
    pCoreOf_stab_le_stab hyp (CosetGeom.mem_nbrs_symm hμ)
  have hQδ0 : ∀ {g : G}, g ∈ pCoreOf 2 (stab δ) → g ∈ G₀ := fun hg =>
    CosetGeom.stab_le δ (pCoreOf_le 2 _ hg)
  have hp : ∀ {μ : CosetGeom G₀ G₁ G₂}, μ ∈ nbrs δ →
      ∃ p, p ∈ torusComp X δ ∧ (graph G₀ G₁ G₂).Adj μ p ∧ p ≠ δ := fun hμ =>
    exists_ne_nbr hT.subdiv (hμΔ hμ) (by simp [hμv hμ]) hδΔ (CosetGeom.mem_nbrs_symm hμ)
  obtain ⟨p₁, hp₁, hμp₁, hp₁δ⟩ := hp hμ₁
  obtain ⟨p₂, hp₂, hμp₂, hp₂δ⟩ := hp hμ₂
  obtain ⟨p₃, hp₃, hμp₃, hp₃δ⟩ := hp hμ₃
  have hp₁v : vtype p₁ = true := vtype_eq_true_of_mem_nbrs (hμv hμ₁) hμp₁
  obtain ⟨-, -, hR3, hR4⟩ := hZ μ₂ hμ₂ μ₁ hμ₁ h₂₁
  obtain ⟨hR1, -, -, -⟩ := hZ μ₁ hμ₁ μ₃ hμ₃ h₃₁.symm
  obtain ⟨-, hR2₃₂, -, -⟩ := hZ μ₃ hμ₃ μ₂ hμ₂ h₂₃.symm
  obtain ⟨-, hR2₂₃, -, -⟩ := hZ μ₂ hμ₂ μ₃ hμ₃ h₂₃
  have hfixp : ∀ g : ↥G₀, (g : G) ∈ pCoreOf 2 (stab δ) → g • p₁ = p₁ →
      (g : G) ∈ ballStab 1 μ₁ := fun g hg hgp =>
    hreg _ hg p₁ hμp₁ hp₁δ (CosetGeom.mem_stab_of_smul_eq hgp)
  have hPg : ∀ g : ↥G₀, (g : G) ∈ pCoreOf 2 (stab δ) → (g : G) ∉ ballStab 1 μ₁ →
      g • p₁ ∈ nbrs μ₁ ∧ g • p₁ ≠ δ ∧ g • p₁ ≠ p₁ := by
    intro g hg hgB
    have hgμ : g • μ₁ = μ₁ := CosetGeom.smul_eq_of_mem_stab (hQδμ hμ₁ hg)
    have hgδ : g • δ = δ := CosetGeom.smul_eq_of_mem_stab (pCoreOf_le 2 _ hg)
    refine ⟨?_, fun he => hp₁δ (smul_left_cancel g (he.trans hgδ.symm)),
      fun he => hgB (hfixp g hg he)⟩
    have h := (CosetGeom.smul_adj g).mpr hμp₁
    rwa [hgμ] at h
  have hsep : ∀ g g' : ↥G₀, (g : G) ∈ pCoreOf 2 (stab δ) → (g' : G) ∈ pCoreOf 2 (stab δ) →
      (g : G)⁻¹ * g' ∉ ballStab 1 μ₁ → g • p₁ ≠ g' • p₁ := by
    intro g g' hg hg' hgg' he
    apply hgg'
    have hfix : (g⁻¹ * g') • p₁ = p₁ := by rw [mul_smul, ← he, inv_smul_smul]
    exact hfixp (g⁻¹ * g') (mul_mem (inv_mem hg) hg') hfix
  obtain ⟨h, hhA, hhB⟩ := SetLike.not_le_iff_exists.mp
    (not_inf_le_ballStab_of_center hyp hδ3 hμ₁ hμ₂ hμ₃ h₂₁ h₃₁ h₂₃ hQ hR1 hR2₃₂ hR2₂₃ hR3 hR4)
  have hh : h ∈ pCoreOf 2 (stab δ) := (mem_inf.mp (mem_inf.mp hhA).1).1
  have hh₂ : h ∈ pCoreOf 2 (stab μ₂) := (mem_inf.mp (mem_inf.mp hhA).1).2
  have hh₃ : h ∈ pCoreOf 2 (stab μ₃) := (mem_inf.mp (mem_inf.mp hhA).2).2
  obtain ⟨h₀, rfl⟩ : ∃ h₀ : ↥G₀, (h₀ : G) = h := ⟨⟨h, hQδ0 hh⟩, rfl⟩
  obtain ⟨h', hh'A, hh'B, hhh'B⟩ : ∃ h' ∈ (pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ₂)) ⊓
      (pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ₃)),
      h' ∉ ballStab 1 μ₁ ∧ (h₀ : G)⁻¹ * h' ∉ ballStab 1 μ₁ := by
    by_contra hcon
    have hall : ∀ h' ∈ (pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ₂)) ⊓
        (pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ₃)), h' ∉ ballStab 1 μ₁ →
        (h₀ : G)⁻¹ * h' ∈ ballStab 1 μ₁ :=
      fun h' hh' hh'B => not_not.mp fun hn => hcon ⟨h', hh', hh'B, hn⟩
    have hXh : X ≤ stab (h₀ • p₁) := by
      intro x hx
      rw [CosetGeom.stab_smul, mem_conjSub]
      have hxQ : x * h₀ * x⁻¹ ∈ pCoreOf 2 (stab δ) := (mem_pCoreOf_iff_conj (hXδ hx) _).mp hh
      have hxA : x * h₀ * x⁻¹ ∈ (pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ₂)) ⊓
          (pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ₃)) :=
        mem_inf.mpr ⟨mem_inf.mpr ⟨hxQ, (mem_pCoreOf_iff_conj (hXμ hμ₂ hx) _).mp hh₂⟩,
          mem_inf.mpr ⟨hxQ, (mem_pCoreOf_iff_conj (hXμ hμ₃ hx) _).mp hh₃⟩⟩
      have hxB : x * h₀ * x⁻¹ ∉ ballStab 1 μ₁ := fun hB =>
        hhB ((mem_ballStab_iff_conj (hXμ₁ hx) _).mpr hB)
      have h1 : (h₀ : G)⁻¹ * (x * h₀ * x⁻¹) ∈ stab p₁ :=
        CosetGeom.ballStab_le_stab_of_dist_le (CosetGeom.dist_eq_one_iff_adj.mpr hμp₁).le
          (hall _ hxA hxB)
      have e : (h₀ : G)⁻¹ * x * h₀ = (h₀ : G)⁻¹ * (x * h₀ * x⁻¹) * x := by group
      rw [e]
      exact mul_mem h1 (le_stab_of_mem_torusComp hXδ hp₁ hx)
    have hadj : (graph G₀ G₁ G₂).Adj μ₁ (h₀ • p₁) := (hPg h₀ hh hhB).1
    rcases eq_or_eq_of_two hT.subdiv (hμΔ hμ₁) (by simp [hμv hμ₁]) hδΔ
        (CosetGeom.mem_nbrs_symm hμ₁) hp₁ hμp₁ hp₁δ.symm
        (mem_torusComp_of_adj hXδ (hμΔ hμ₁) hadj hXh) hadj with he | he
    · exact (hPg h₀ hh hhB).2.1 he
    · exact hhB (hfixp h₀ hh he)
  have hh' : h' ∈ pCoreOf 2 (stab δ) := (mem_inf.mp (mem_inf.mp hh'A).1).1
  have hh'₂ : h' ∈ pCoreOf 2 (stab μ₂) := (mem_inf.mp (mem_inf.mp hh'A).1).2
  have hh'₃ : h' ∈ pCoreOf 2 (stab μ₃) := (mem_inf.mp (mem_inf.mp hh'A).2).2
  obtain ⟨h'₀, rfl⟩ : ∃ h'₀ : ↥G₀, (h'₀ : G) = h' := ⟨⟨h', hQδ0 hh'⟩, rfl⟩
  obtain ⟨a, ha, b, hb, hab⟩ := hR4
  obtain ⟨a₀, rfl⟩ : ∃ a₀ : ↥G₀, (a₀ : G) = a := ⟨⟨a, hQδ0 ha⟩, rfl⟩
  obtain ⟨b₀, rfl⟩ : ∃ b₀ : ↥G₀, (b₀ : G) = b := ⟨⟨b, hQδ0 hb⟩, rfl⟩
  have ha1 : (a₀ : G) ∈ stab μ₁ := hQδμ hμ₁ ha
  have hb1 : (b₀ : G) ∈ stab μ₁ := hQδμ hμ₁ hb
  have hnA : (a₀ : G) ∉ ballStab 1 μ₁ := fun hB => hab (by
    have h1 := (mem_ballStab_iff_conj hb1 _).mp (inv_mem hB)
    have e : (a₀ : G) * b₀ * (a₀ : G)⁻¹ * (b₀ : G)⁻¹ =
        a₀ * ((b₀ : G) * (a₀ : G)⁻¹ * (b₀ : G)⁻¹) := by group
    rw [e]
    exact mul_mem hB h1)
  have hnB₀ : (b₀ : G) ∉ ballStab 1 μ₁ := fun hB => hab
    (mul_mem ((mem_ballStab_iff_conj ha1 _).mp hB) (inv_mem hB))
  have hnAB : (a₀ : G) * b₀ ∉ ballStab 1 μ₁ := fun hB => hab (by
    have h1 := (mem_ballStab_iff_conj (inv_mem ha1) _).mp hB
    have e : (a₀ : G) * b₀ * (a₀ : G)⁻¹ * (b₀ : G)⁻¹ =
        ((a₀ : G) * b₀) * ((a₀ : G)⁻¹ * ((a₀ : G) * b₀) * (a₀ : G)⁻¹⁻¹)⁻¹ := by group
    rw [e]
    exact mul_mem hB (inv_mem h1))
  have hnBA : (b₀ : G) * a₀ ∉ ballStab 1 μ₁ := fun hB => hab (by
    have h1 := (mem_ballStab_iff_conj ha1 _).mp hB
    have e : (a₀ : G) * b₀ * (a₀ : G)⁻¹ * (b₀ : G)⁻¹ =
        ((a₀ : G) * ((b₀ : G) * a₀) * (a₀ : G)⁻¹) * ((b₀ : G) * a₀)⁻¹ := by group
    rw [e]
    exact mul_mem h1 (inv_mem hB))
  have hn₁₂ : (a₀ : G)⁻¹ * b₀ ∉ ballStab 1 μ₁ := fun hB => hab (by
    have h1 := (mem_ballStab_iff_conj ha1 _).mp hB
    have h2 := (mem_ballStab_iff_conj ha1 _).mp (mul_mem h1 (inv_mem hB))
    have e : (a₀ : G) * b₀ * (a₀ : G)⁻¹ * (b₀ : G)⁻¹ = (a₀ : G) *
        ((a₀ : G) * ((a₀ : G)⁻¹ * b₀) * (a₀ : G)⁻¹ * ((a₀ : G)⁻¹ * b₀)⁻¹) * (a₀ : G)⁻¹ := by
      group
    rw [e]
    exact h2)
  have hn₁₃ : (a₀ : G)⁻¹ * ((a₀ : G) * b₀) ∉ ballStab 1 μ₁ := by
    rw [inv_mul_cancel_left]
    exact hnB₀
  have hn₁₄ : (a₀ : G)⁻¹ * ((b₀ : G) * a₀) ∉ ballStab 1 μ₁ := fun hB => hnB₀ (by
    have h1 := (mem_ballStab_iff_conj ha1 _).mp hB
    have e : (a₀ : G) * ((a₀ : G)⁻¹ * ((b₀ : G) * a₀)) * (a₀ : G)⁻¹ = b₀ := by group
    rwa [e] at h1)
  have hn₂₃ : (b₀ : G)⁻¹ * ((a₀ : G) * b₀) ∉ ballStab 1 μ₁ := fun hB => hnA (by
    have h1 := (mem_ballStab_iff_conj hb1 _).mp hB
    have e : (b₀ : G) * ((b₀ : G)⁻¹ * ((a₀ : G) * b₀)) * (b₀ : G)⁻¹ = a₀ := by group
    rwa [e] at h1)
  have hn₂₄ : (b₀ : G)⁻¹ * ((b₀ : G) * a₀) ∉ ballStab 1 μ₁ := by
    rw [inv_mul_cancel_left]
    exact hnA
  have hn₃₄ : ((a₀ : G) * b₀)⁻¹ * ((b₀ : G) * a₀) ∉ ballStab 1 μ₁ := fun hB => hab (by
    have h1 := (mem_ballStab_iff_conj (mul_mem ha1 hb1) _).mp (inv_mem hB)
    have e : (a₀ : G) * b₀ * (a₀ : G)⁻¹ * (b₀ : G)⁻¹ =
        ((a₀ : G) * b₀) * (((a₀ : G) * b₀)⁻¹ * ((b₀ : G) * a₀))⁻¹ * ((a₀ : G) * b₀)⁻¹ := by
      group
    rw [e]
    exact h1)
  have hhBi : ((h₀⁻¹ : ↥G₀) : G) ∉ ballStab 1 μ₁ := fun hB => hhB (by simpa using inv_mem hB)
  obtain ⟨x, ⟨hxμ, hxδ, hxp⟩, hxf₁, hxf₂, hxf₃⟩ := exists_ne_three_of_four
    (P := fun q => q ∈ nbrs μ₁ ∧ q ≠ δ ∧ q ≠ p₁)
    (hPg a₀ ha hnA) (hPg b₀ hb hnB₀) (hPg (a₀ * b₀) (mul_mem ha hb) hnAB)
    (hPg (b₀ * a₀) (mul_mem hb ha) hnBA)
    (hsep a₀ b₀ ha hb hn₁₂) (hsep a₀ (a₀ * b₀) ha (mul_mem ha hb) hn₁₃)
    (hsep a₀ (b₀ * a₀) ha (mul_mem hb ha) hn₁₄) (hsep b₀ (a₀ * b₀) hb (mul_mem ha hb) hn₂₃)
    (hsep b₀ (b₀ * a₀) hb (mul_mem hb ha) hn₂₄)
    (hsep (a₀ * b₀) (b₀ * a₀) (mul_mem ha hb) (mul_mem hb ha) hn₃₄)
    (h₀⁻¹ • p₁) (h'₀ • p₁) ((h₀⁻¹ * h'₀) • p₁)
  obtain ⟨k₁, hk₁Q, hk₁p, -, hk₁rest⟩ := hρ p₁ hμp₁ x hxμ hxp.symm
  have hk₁δ : k₁ ∈ pCoreOf 2 (stab δ) :=
    pCoreOf_inf_ballStab_le (CosetGeom.mem_nbrs_symm hμ₁)
      (mem_inf.mpr ⟨hk₁Q, hk₁rest δ (CosetGeom.mem_nbrs_symm hμ₁) hp₁δ.symm hxδ.symm⟩)
  have hP₁ := hPg h₀⁻¹ (inv_mem hh) hhBi
  have hP₂ := hPg h'₀ hh' hh'B
  have hP₃ := hPg (h₀⁻¹ * h'₀) (mul_mem (inv_mem hh) hh') hhh'B
  have hk₁f₁ : k₁ ∈ ballStab 1 (h₀⁻¹ • p₁) := hk₁rest _ hP₁.1 hP₁.2.2 hxf₁.symm
  have hk₁f₂ : k₁ ∈ ballStab 1 (h'₀ • p₁) := hk₁rest _ hP₂.1 hP₂.2.2 hxf₂.symm
  have hk₁f₃ : k₁ ∈ ballStab 1 ((h₀⁻¹ * h'₀) • p₁) := hk₁rest _ hP₃.1 hP₃.2.2 hxf₃.symm
  have hz : (h₀ : G) * k₁⁻¹ * (h₀ : G)⁻¹ ∈ pCoreOf 2 (stab μ₁) :=
    (mem_pCoreOf_iff_conj (hQδμ hμ₁ hh) _).mp (inv_mem hk₁Q)
  have hkδ : k₁ * h₀ * k₁⁻¹ * (h₀ : G)⁻¹ ∈ pCoreOf 2 (stab δ) :=
    mul_mem (mul_mem (mul_mem hk₁δ hh) (inv_mem hk₁δ)) (inv_mem hh)
  have hk₁' : k₁ * h₀ * k₁⁻¹ * (h₀ : G)⁻¹ ∈ pCoreOf 2 (stab μ₁) := by
    have e : k₁ * h₀ * k₁⁻¹ * (h₀ : G)⁻¹ = k₁ * ((h₀ : G) * k₁⁻¹ * (h₀ : G)⁻¹) := by group
    rw [e]
    exact mul_mem hk₁Q hz
  have hk₂ : k₁ * h₀ * k₁⁻¹ * (h₀ : G)⁻¹ ∈ pCoreOf 2 (stab μ₂) :=
    mul_mem ((mem_pCoreOf_iff_conj (hQδμ hμ₂ hk₁δ) _).mp hh₂) (inv_mem hh₂)
  have hk₃ : k₁ * h₀ * k₁⁻¹ * (h₀ : G)⁻¹ ∈ pCoreOf 2 (stab μ₃) :=
    mul_mem ((mem_pCoreOf_iff_conj (hQδμ hμ₃ hk₁δ) _).mp hh₃) (inv_mem hh₃)
  have hkB : k₁ * h₀ * k₁⁻¹ * (h₀ : G)⁻¹ ∉ ballStab 1 p₁ := by
    have hzB : (h₀ : G) * k₁⁻¹ * (h₀ : G)⁻¹ ∈ ballStab 1 p₁ := by
      have h1 := conj_mem_ballStab_smul h₀ (inv_mem hk₁f₁)
      rwa [smul_inv_smul] at h1
    have e : k₁ * h₀ * k₁⁻¹ * (h₀ : G)⁻¹ = k₁ * ((h₀ : G) * k₁⁻¹ * (h₀ : G)⁻¹) := by group
    rw [e, mul_mem_ballStab_one_iff hG (ncard_nbrs_eq_three hT hp₁ hp₁v)
      (CosetGeom.mem_nbrs_symm hμp₁) (mem_stab_inf_of_mem_pCoreOf hyp hμp₁ hk₁Q)
      (mem_stab_inf_of_mem_pCoreOf hyp hμp₁ hz)]
    exact fun hiff => hk₁p (hiff.mpr hzB)
  have hkB' : (h'₀ : G)⁻¹ * (k₁ * h₀ * k₁⁻¹ * (h₀ : G)⁻¹) * h'₀ ∈ ballStab 1 p₁ := by
    have h1 := conj_mem_ballStab_smul h'₀⁻¹ hk₁f₂
    rw [inv_smul_smul] at h1
    have h2 := conj_mem_ballStab_smul (h₀⁻¹ * h'₀)⁻¹ (inv_mem hk₁f₃)
    rw [inv_smul_smul] at h2
    simp only [Subgroup.coe_inv, Subgroup.coe_mul] at h1 h2
    have e : (h'₀ : G)⁻¹ * (k₁ * h₀ * k₁⁻¹ * (h₀ : G)⁻¹) * h'₀ =
        ((h'₀ : G)⁻¹ * k₁ * (h'₀ : G)⁻¹⁻¹) *
          (((h₀ : G)⁻¹ * h'₀)⁻¹ * k₁⁻¹ * ((h₀ : G)⁻¹ * h'₀)⁻¹⁻¹) := by
      group
    rw [e]
    exact mul_mem h1 h2
  exact hkB ((mem_ballStab_iff_conj_of_torus hyp hXodd hXδ hT hδv hμ₁ hμ₂ hμ₃ h₂₁.symm
    h₃₁.symm h₂₃ hp₁ hp₂ hp₃ hμp₁ hμp₂ hμp₃ hp₁δ hp₂δ hp₃δ hkδ hk₁' hk₂ hk₃ hh' hh'₂
    hh'₃).mpr hkB')

end Center

end CFSG.Quasithin.F112Crit

end
