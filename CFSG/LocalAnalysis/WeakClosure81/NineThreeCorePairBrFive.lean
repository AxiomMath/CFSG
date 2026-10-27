module

public import Mathlib.Algebra.Group.Subgroup.Map
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeCoreLinFive

public section

namespace CFSG.LocalAnalysis.WeakClosure81

private lemma nine3_br5_coe_prod_fin_five {G : Type} [Group G] {W : Subgroup G}
    (F : Fin 5 → ↥W) :
    ((F 0 * F 1 * F 2 * F 3 * F 4 : ↥W) : G) =
      ((List.finRange 5).map fun k => (F k : G)).prod := by
  rw [show List.finRange 5 = [0, 1, 2, 3, 4] from rfl]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Subgroup.coe_mul, mul_assoc]

private lemma nine3_br5_subtype_eq_mul_five_of_list {G : Type} [Group G] {W : Subgroup G}
    {b : ↥W} {F : Fin 5 → ↥W} {g : Fin 5 → G}
    (hF : ∀ k, (F k : G) = g k) (hb : (b : G) = ((List.finRange 5).map g).prod) :
    b = F 0 * F 1 * F 2 * F 3 * F 4 := by
  apply Subtype.ext
  rw [hb, nine3_br5_coe_prod_fin_five F]
  rw [show (fun k => (F k : G)) = g from funext hF]

theorem nine3_bridge_five {G : Type} [Group G] {T₁ T₂ W : Subgroup G}
    (hT₁ : ∀ a ∈ T₁, ∀ b ∈ T₁, a * b = b * a) (hT₁sq : ∀ a ∈ T₁, a * a = 1)
    (hT₂ : ∀ a ∈ T₂, ∀ b ∈ T₂, a * b = b * a) (hT₂sq : ∀ a ∈ T₂, a * a = 1)
    (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hWsq : ∀ a ∈ W, a * a = 1)
    (P : Fin 5 → Subgroup G) (hPW : ∀ k, P k ≤ W) (hP : ∀ k l, k ≠ l → P k ⊓ P l = ⊥)
    (φ ψ : Fin 5 → G → G)
    (hφmul : ∀ k, ∀ i ∈ T₁, ∀ i' ∈ T₁, φ k (i * i') = φ k i * φ k i')
    (hψmul : ∀ l, ∀ j ∈ T₂, ∀ j' ∈ T₂, ψ l (j * j') = ψ l j * ψ l j')
    (hφ0 : ∀ i ∈ T₁, φ 0 i = 1) (hψ1 : ∀ j ∈ T₂, ψ 1 j = 1)
    (hφP : ∀ k, ∀ i ∈ T₁, φ k i ∈ P k) (hψP : ∀ l, ∀ j ∈ T₂, ψ l j ∈ P l)
    (iφ : ∀ k, k ≠ 0 → ∀ i ∈ T₁, i ≠ 1 → φ k i ≠ 1)
    (iψ : ∀ l, l ≠ 1 → ∀ j ∈ T₂, j ≠ 1 → ψ l j ≠ 1)
    (hφsum : ∀ i ∈ T₁, ((List.finRange 5).map fun k => φ k i).prod = 1)
    (hψsum : ∀ j ∈ T₂, ((List.finRange 5).map fun l => ψ l j).prod = 1)
    (hrank : ∃ i₁ ∈ T₁, ∃ i₂ ∈ T₁, i₁ ≠ 1 ∧ i₂ ≠ 1 ∧ i₁ ≠ i₂)
    (hrank' : ∃ j₁ ∈ T₂, ∃ j₂ ∈ T₂, j₁ ≠ 1 ∧ j₂ ≠ 1 ∧ j₁ ≠ j₂)
    (β : G → G → G) (hβ : ∀ i ∈ T₁, ∀ j ∈ T₂, β i j ∈ W)
    (hs : ∀ j ∈ T₂, ∃ ε : Fin 5 → Bool, ∀ i ∈ T₁,
      β i j = ((List.finRange 5).map fun k => if ε k then φ k i else 1).prod)
    (hp : ∀ i ∈ T₁, ∃ π : Fin 5 → Bool, ∀ j ∈ T₂,
      β i j = ((List.finRange 5).map fun l => if π l then ψ l j else 1).prod) :
    ∀ j ∈ T₂, ∀ ε : Fin 5 → Bool,
      (∀ i ∈ T₁, β i j = ((List.finRange 5).map fun k => if ε k then φ k i else 1).prod) →
        ε 1 = ε 2 ∧ ε 2 = ε 3 ∧ ε 3 = ε 4 := by
  classical
  letI : CommGroup ↥T₁ :=
    { (inferInstance : Group ↥T₁) with
      mul_comm := fun a b => Subtype.ext (hT₁ a.1 a.2 b.1 b.2) }
  letI : CommGroup ↥T₂ :=
    { (inferInstance : Group ↥T₂) with
      mul_comm := fun a b => Subtype.ext (hT₂ a.1 a.2 b.1 b.2) }
  letI : CommGroup ↥W :=
    { (inferInstance : Group ↥W) with
      mul_comm := fun a b => Subtype.ext (hW a.1 a.2 b.1 b.2) }
  let P' : Fin 5 → Subgroup ↥W := fun k => (P k).subgroupOf W
  let φ' : Fin 5 → ↥T₁ →* ↥W := fun k =>
    MonoidHom.mk' (fun i => ⟨φ k i.1, hPW k (hφP k i.1 i.2)⟩)
      (fun i i' => Subtype.ext (hφmul k i.1 i.2 i'.1 i'.2))
  let ψ' : Fin 5 → ↥T₂ →* ↥W := fun l =>
    MonoidHom.mk' (fun j => ⟨ψ l j.1, hPW l (hψP l j.1 j.2)⟩)
      (fun j j' => Subtype.ext (hψmul l j.1 j.2 j'.1 j'.2))
  let β' : ↥T₁ → ↥T₂ → ↥W := fun i j => ⟨β i.1 j.1, hβ i.1 i.2 j.1 j.2⟩
  have hP' : ∀ k l, k ≠ l → P' k ⊓ P' l = ⊥ := by
    intro k l hkl
    have hsub : P' k ⊓ P' l = (P k ⊓ P l).subgroupOf W := by
      ext x
      change x ∈ (P k).subgroupOf W ⊓ (P l).subgroupOf W ↔
        x ∈ (P k ⊓ P l).subgroupOf W
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    rw [hsub, hP k l hkl, Subgroup.bot_subgroupOf]
  have hT₁sq' : ∀ i : ↥T₁, i * i = 1 := fun i => Subtype.ext (hT₁sq i.1 i.2)
  have hT₂sq' : ∀ j : ↥T₂, j * j = 1 := fun j => Subtype.ext (hT₂sq j.1 j.2)
  have hWsq' : ∀ w : ↥W, w * w = 1 := fun w => Subtype.ext (hWsq w.1 w.2)
  have hφ0' : ∀ i : ↥T₁, φ' 0 i = 1 := by
    intro i
    apply Subtype.ext
    exact hφ0 i.1 i.2
  have hψ1' : ∀ j : ↥T₂, ψ' 1 j = 1 := by
    intro j
    apply Subtype.ext
    exact hψ1 j.1 j.2
  have hφP' : ∀ k (i : ↥T₁), φ' k i ∈ P' k := by
    intro k i
    change φ' k i ∈ (P k).subgroupOf W
    rw [Subgroup.mem_subgroupOf]
    exact hφP k i.1 i.2
  have hψP' : ∀ l (j : ↥T₂), ψ' l j ∈ P' l := by
    intro l j
    change ψ' l j ∈ (P l).subgroupOf W
    rw [Subgroup.mem_subgroupOf]
    exact hψP l j.1 j.2
  have iφ' : ∀ k, k ≠ 0 → Function.Injective (φ' k) := by
    intro k hk
    rw [injective_iff_map_eq_one]
    intro i hi
    have hφi : φ k i.1 = 1 := by
      change ((φ' k i : ↥W) : G) = 1
      rw [hi]
      rfl
    exact Subtype.ext (by
      by_contra hne
      exact (iφ k hk i.1 i.2 hne) hφi)
  have iψ' : ∀ l, l ≠ 1 → Function.Injective (ψ' l) := by
    intro l hl
    rw [injective_iff_map_eq_one]
    intro j hj
    have hψj : ψ l j.1 = 1 := by
      change ((ψ' l j : ↥W) : G) = 1
      rw [hj]
      rfl
    exact Subtype.ext (by
      by_contra hne
      exact (iψ l hl j.1 j.2 hne) hψj)
  have hrankT : ∃ i₁ i₂ : ↥T₁, i₁ ≠ 1 ∧ i₂ ≠ 1 ∧ i₁ ≠ i₂ := by
    obtain ⟨i₁, hi₁, i₂, hi₂, h1, h2, h12⟩ := hrank
    refine ⟨⟨i₁, hi₁⟩, ⟨i₂, hi₂⟩, ?_, ?_, ?_⟩
    · intro h
      exact h1 (by simpa using congrArg Subtype.val h)
    · intro h
      exact h2 (by simpa using congrArg Subtype.val h)
    · intro h
      exact h12 (by simpa using congrArg Subtype.val h)
  have hrankT' : ∃ j₁ j₂ : ↥T₂, j₁ ≠ 1 ∧ j₂ ≠ 1 ∧ j₁ ≠ j₂ := by
    obtain ⟨j₁, hj₁, j₂, hj₂, h1, h2, h12⟩ := hrank'
    refine ⟨⟨j₁, hj₁⟩, ⟨j₂, hj₂⟩, ?_, ?_, ?_⟩
    · intro h
      exact h1 (by simpa using congrArg Subtype.val h)
    · intro h
      exact h2 (by simpa using congrArg Subtype.val h)
    · intro h
      exact h12 (by simpa using congrArg Subtype.val h)
  have hφsum' : ∀ i : ↥T₁, ∏ k : Fin 5, φ' k i = 1 := by
    intro i
    apply Subtype.ext
    rw [Fin.prod_univ_five]
    exact (nine3_br5_coe_prod_fin_five (fun k => φ' k i)).trans (hφsum i.1 i.2)
  have hψsum' : ∀ j : ↥T₂, ∏ l : Fin 5, ψ' l j = 1 := by
    intro j
    apply Subtype.ext
    rw [Fin.prod_univ_five]
    exact (nine3_br5_coe_prod_fin_five (fun l => ψ' l j)).trans (hψsum j.1 j.2)
  have hs' : ∀ j : ↥T₂, ∃ ε : Fin 5 → Bool, ∀ i : ↥T₁,
      β' i j = ∏ k : Fin 5, (if ε k then φ' k i else 1) := by
    intro j
    obtain ⟨ε, hε⟩ := hs j.1 j.2
    refine ⟨ε, fun i => ?_⟩
    rw [Fin.prod_univ_five]
    exact nine3_br5_subtype_eq_mul_five_of_list
      (F := fun k => (if ε k then φ' k i else 1 : ↥W))
      (g := fun k => if ε k then φ k i.1 else 1)
      (fun k => by cases hk : ε k <;> rfl)
      (hε i.1 i.2)
  have hp' : ∀ i : ↥T₁, ∃ π : Fin 5 → Bool, ∀ j : ↥T₂,
      β' i j = ∏ l : Fin 5, (if π l then ψ' l j else 1) := by
    intro i
    obtain ⟨π, hπ⟩ := hp i.1 i.2
    refine ⟨π, fun j => ?_⟩
    rw [Fin.prod_univ_five]
    exact nine3_br5_subtype_eq_mul_five_of_list
      (F := fun l => (if π l then ψ' l j else 1 : ↥W))
      (g := fun l => if π l then ψ l j.1 else 1)
      (fun l => by cases hl : π l <;> rfl)
      (hπ j.1 j.2)
  intro j hj ε hrep
  refine nine3_la_five hT₁sq' hT₂sq' hWsq' P' hP' φ' ψ' hφ0' hψ1' hφP' hψP'
    iφ' iψ' hφsum' hψsum' hrankT hrankT' β' hs' hp' ⟨j, hj⟩ ε ?_
  intro i
  rw [Fin.prod_univ_five]
  exact nine3_br5_subtype_eq_mul_five_of_list
    (F := fun k => (if ε k then φ' k i else 1 : ↥W))
    (g := fun k => if ε k then φ k i.1 else 1)
    (fun k => by cases hk : ε k <;> rfl)
    (hrep i.1 i.2)

end CFSG.LocalAnalysis.WeakClosure81
