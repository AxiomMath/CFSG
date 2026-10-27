module

public import CFSG.Quasithin.H13.NQS134EB
public import CFSG.Quasithin.H13.NQS13412D

public section

namespace CFSG.Quasithin.H13.NQS134

open Equiv Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

namespace End134

variable (S : A6.Setting134 G T L V)
include S

theorem comm_psi {x v : G} (hx : x ∈ normalizer (V : Set G)) (hv : v ∈ V)
    (hc : x * v * x⁻¹ * v⁻¹ ∈ V) :
    (S.frame.ψ ⟨x * v * x⁻¹ * v⁻¹, hc⟩ : P6) =
      G6.permAct 6 (S.frame.ρ ⟨x, hx⟩) (S.frame.ψ ⟨v, hv⟩ : P6) * (S.frame.ψ ⟨v, hv⟩ : P6) := by
  have hxv : x * v * x⁻¹ ∈ V := (mem_normalizer_iff.mp hx v).mp hv
  have h1 : (⟨x * v * x⁻¹ * v⁻¹, hc⟩ : ↥V) = ⟨x * v * x⁻¹, hxv⟩ * (⟨v, hv⟩ : ↥V)⁻¹ := rfl
  have h2 := S.psi_conj ⟨x, hx⟩ ⟨v, hv⟩
  rw [h1, map_mul, map_inv]
  show ((S.frame.ψ ⟨x * v * x⁻¹, hxv⟩ : P6) * ((S.frame.ψ ⟨v, hv⟩)⁻¹ : ↥(G6.coreMod 6))) = _
  have h3 : S.frame.ψ ⟨x * v * x⁻¹, hxv⟩ = G6.coreAct 6 (S.frame.ρ ⟨x, hx⟩) (S.frame.ψ ⟨v, hv⟩) :=
    h2
  rw [h3, G6.coreAct_coe]
  congr 1
  show ((S.frame.ψ ⟨v, hv⟩ : P6))⁻¹ = (S.frame.ψ ⟨v, hv⟩ : P6)
  exact inv_eq_of_mul_eq_one_right (P6_mul_self _)

theorem rho_eq_of_comm {X : Subgroup G} (hXN : X ≤ normalizer (V : Set G))
    (hX2 : ∀ x ∈ X, x * x = 1) {w : ℕ} (hw : w = 2 ∨ w = 4)
    (hcomm : ∀ (x : G) (hx : x ∈ X) (v : G) (hv : v ∈ V), x * v * x⁻¹ * v⁻¹ = 1 ∨
      wtP (G6.permAct 6 (S.frame.ρ ⟨x, hXN hx⟩) (S.frame.ψ ⟨v, hv⟩ : P6) *
        (S.frame.ψ ⟨v, hv⟩ : P6)) = w)
    {x₀ : G} (hx₀ : x₀ ∈ X) (hx₀1 : S.frame.ρ ⟨x₀, hXN hx₀⟩ ≠ 1) :
    (∀ (x : G) (hx : x ∈ X), S.frame.ρ ⟨x, hXN hx⟩ = 1 ∨
      S.frame.ρ ⟨x, hXN hx⟩ = S.frame.ρ ⟨x₀, hXN hx₀⟩) ∧
    (w = 4 → S.frame.ρ ⟨x₀, hXN hx₀⟩ ∈ fpfList) ∧
    (w = 2 → ∃ i j : Fin 6, i ≠ j ∧ S.frame.ρ ⟨x₀, hXN hx₀⟩ = swap i j) := by
  have hinv : ∀ (x : G) (hx : x ∈ X), S.frame.ρ ⟨x, hXN hx⟩ * S.frame.ρ ⟨x, hXN hx⟩ = 1 :=
    fun x hx => by
      rw [← map_mul]
      have : (⟨x, hXN hx⟩ * ⟨x, hXN hx⟩ : ↥(normalizer (V : Set G))) = 1 :=
        Subtype.ext (hX2 x hx)
      rw [this, map_one]
  have hc' : ∀ (x : G) (hx : x ∈ X) (y : P6), ∑ i, Multiplicative.toAdd y i = 0 →
      G6.permAct 6 (S.frame.ρ ⟨x, hXN hx⟩) y * y = 1 ∨
        wtP (G6.permAct 6 (S.frame.ρ ⟨x, hXN hx⟩) y * y) = w := by
    intro x hx y hy
    set v : ↥V := S.frame.ψ.symm ⟨y, G6.mem_coreMod.2 hy⟩ with hvdef
    have hvy : (S.frame.ψ v : P6) = y := by rw [hvdef, MulEquiv.apply_symm_apply]
    rcases hcomm x hx v v.2 with h | h
    · left
      have hc : x * (v : G) * x⁻¹ * (v : G)⁻¹ ∈ V := by rw [h]; exact one_mem _
      have h2 := comm_psi S (hXN hx) v.2 hc
      have h3 : (S.frame.ψ ⟨x * (v : G) * x⁻¹ * (v : G)⁻¹, hc⟩ : P6) = 1 := by
        rw [show (⟨x * (v : G) * x⁻¹ * (v : G)⁻¹, hc⟩ : ↥V) = 1 from Subtype.ext h, map_one]
        rfl
      rw [← hvy]
      exact h2.symm.trans h3
    · right
      rw [← hvy]
      exact h
  have hcases : ∀ (x : G) (hx : x ∈ X), S.frame.ρ ⟨x, hXN hx⟩ = 1 ∨
      ((w = 4 → S.frame.ρ ⟨x, hXN hx⟩ ∈ fpfList) ∧
        (w = 2 → ∃ i j : Fin 6, i ≠ j ∧ S.frame.ρ ⟨x, hXN hx⟩ = swap i j)) := by
    intro x hx
    rcases hw with rfl | rfl
    · rcases eq_swap_of_wt_two _ (hinv x hx) (hc' x hx) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨fun h' => absurd h' (by decide), fun _ => h⟩
    · rcases eq_fpf_of_wt_four _ (hinv x hx) (hc' x hx) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨fun _ => mem_fpfList.2 ⟨hinv x hx, h⟩, fun h' => absurd h' (by decide)⟩
  obtain ⟨h04, h02⟩ := (hcases x₀ hx₀).resolve_left hx₀1
  refine ⟨fun x hx => ?_, h04, h02⟩
  rcases hcases x hx with h | ⟨h4, h2⟩
  · exact Or.inl h
  right
  by_contra hne
  have hcomm' : S.frame.ρ ⟨x, hXN hx⟩ * S.frame.ρ ⟨x₀, hXN hx₀⟩ =
      S.frame.ρ ⟨x₀, hXN hx₀⟩ * S.frame.ρ ⟨x, hXN hx⟩ := by
    have hxx : x * x₀ = x₀ * x := by
      have h1 := hX2 _ (mul_mem hx hx₀)
      have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hX2 x hx)
      have hx0i : x₀⁻¹ = x₀ := inv_eq_of_mul_eq_one_right (hX2 x₀ hx₀)
      have h2 : (x * x₀)⁻¹ = x * x₀ := inv_eq_of_mul_eq_one_right h1
      rw [mul_inv_rev, hxi, hx0i] at h2
      exact h2.symm
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext hxx)
  have hprod := hcases _ (mul_mem hx hx₀)
  have hρprod : S.frame.ρ ⟨x * x₀, hXN (mul_mem hx hx₀)⟩ =
      S.frame.ρ ⟨x, hXN hx⟩ * S.frame.ρ ⟨x₀, hXN hx₀⟩ := by
    rw [← map_mul]
    rfl
  rw [hρprod] at hprod
  have hinvx0 := hinv x₀ hx₀
  rcases hw with rfl | rfl
  · obtain ⟨i, j, hij, hσ⟩ := h2 rfl
    obtain ⟨k, l, hkl, hτ⟩ := h02 rfl
    rcases hprod with h | ⟨-, h⟩
    · apply hne
      have := congrArg (· * S.frame.ρ ⟨x₀, hXN hx₀⟩) h
      simp only [one_mul, mul_assoc, hinvx0, mul_one] at this
      exact this
    · obtain ⟨a, b, hab, he⟩ := h rfl
      rw [hσ, hτ] at he hcomm'
      exact swap_mul_ne_swap i j k l hij hkl (by rw [← hσ, ← hτ]; exact hne) hcomm' a b he
  · have hf1 := h4 rfl
    have hf2 := h04 rfl
    rcases hprod with h | ⟨h, -⟩
    · apply hne
      have := congrArg (· * S.frame.ρ ⟨x₀, hXN hx₀⟩) h
      simp only [one_mul, mul_assoc, hinvx0, mul_one] at this
      exact this
    · obtain ⟨i, hi⟩ := fpf_mul_fixed _ hf1 _ hf2 hcomm' hne
      exact (mem_fpfList.1 (h rfl)).2 i hi

theorem card_inf_centralizer {X : Subgroup G} (hXN : X ≤ normalizer (V : Set G)) {x₀ : G}
    (hx₀ : x₀ ∈ X) (hx₀1 : S.frame.ρ ⟨x₀, hXN hx₀⟩ ≠ 1)
    (hρ : ∀ (x : G) (hx : x ∈ X), S.frame.ρ ⟨x, hXN hx⟩ = 1 ∨
      S.frame.ρ ⟨x, hXN hx⟩ = S.frame.ρ ⟨x₀, hXN hx₀⟩) :
    2 * Nat.card ↥(X ⊓ centralizer (V : Set G)) = Nat.card X := by
  classical
  let f : ↥X →* Perm (Fin 6) := S.frame.ρ.comp (Subgroup.inclusion hXN)
  have hker : f.ker = (X ⊓ centralizer (V : Set G)).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_inf]
    simp only [f, MonoidHom.comp_apply]
    refine ⟨fun h => ⟨x.2, (frame5_ker_iff S.frame _).1 h⟩, fun h => ?_⟩
    exact (frame5_ker_iff S.frame (Subgroup.inclusion hXN x)).2 h.2
  have hrange : Nat.card f.range = 2 := by
    have hset : (f.range : Set (Perm (Fin 6))) = {1, S.frame.ρ ⟨x₀, hXN hx₀⟩} := by
      ext σ
      simp only [SetLike.mem_coe, MonoidHom.mem_range, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨x, rfl⟩
        exact hρ x x.2
      · rintro (rfl | rfl)
        · exact ⟨1, map_one f⟩
        · exact ⟨⟨x₀, hx₀⟩, rfl⟩
    rw [← SetLike.coe_sort_coe, hset, Nat.card_eq_fintype_card, ← Set.toFinset_card,
      Set.toFinset_insert, Set.toFinset_singleton, Finset.card_pair (Ne.symm hx₀1)]
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hrange, hker] at h1
  rw [← h1, mul_comm]
  congr 1
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (inf_le_left : X ⊓ centralizer (V : Set G) ≤ X)).toEquiv).symm

theorem card_V_inf_centralizer {X : Subgroup G} (hXN : X ≤ normalizer (V : Set G)) {x₀ : G}
    (hx₀ : x₀ ∈ X)
    (hρ : ∀ (x : G) (hx : x ∈ X), S.frame.ρ ⟨x, hXN hx⟩ = 1 ∨
      S.frame.ρ ⟨x, hXN hx⟩ = S.frame.ρ ⟨x₀, hXN hx₀⟩) :
    Nat.card ↥(V ⊓ centralizer (X : Set G)) =
      (Finset.univ.filter fun y : P6 => ∑ i, Multiplicative.toAdd y i = 0 ∧
        G6.permAct 6 (S.frame.ρ ⟨x₀, hXN hx₀⟩) y = y).card := by
  classical
  set τ := S.frame.ρ ⟨x₀, hXN hx₀⟩ with hτ
  have hiff : ∀ (v : G) (hv : v ∈ V), v ∈ centralizer (X : Set G) ↔
      G6.permAct 6 τ (S.frame.ψ ⟨v, hv⟩ : P6) = S.frame.ψ ⟨v, hv⟩ := by
    intro v hv
    have hfix : ∀ (x : G) (hx : x ∈ X), x * v * x⁻¹ = v ↔
        G6.permAct 6 (S.frame.ρ ⟨x, hXN hx⟩) (S.frame.ψ ⟨v, hv⟩ : P6) = S.frame.ψ ⟨v, hv⟩ := by
      intro x hx
      rw [S.conj_eq_iff ⟨x, hXN hx⟩ ⟨v, hv⟩]
      constructor
      · intro h
        have := congrArg Subtype.val h
        rwa [G6.coreAct_coe] at this
      · intro h
        exact Subtype.ext (by rw [G6.coreAct_coe]; exact h)
    constructor
    · intro hc
      have h1 : x₀ * v * x₀⁻¹ = v := by
        rw [mem_centralizer_iff.mp hc x₀ hx₀, mul_inv_cancel_right]
      exact (hfix x₀ hx₀).1 h1
    · intro h
      rw [mem_centralizer_iff]
      intro x hx
      have h2 : x * v * x⁻¹ = v := by
        rcases hρ x hx with h3 | h3
        · rw [hfix x hx, h3, map_one]
          rfl
        · rw [hfix x hx, h3]
          exact h
      calc x * v = x * v * x⁻¹ * x := by group
        _ = v * x := by rw [h2]
  let e : ↥(V ⊓ centralizer (X : Set G)) ≃
      {y : P6 // ∑ i, Multiplicative.toAdd y i = 0 ∧ G6.permAct 6 τ y = y} :=
    { toFun := fun v => ⟨S.frame.ψ ⟨v, (mem_inf.1 v.2).1⟩,
        G6.mem_coreMod.1 (S.frame.ψ ⟨v, (mem_inf.1 v.2).1⟩).2,
        (hiff v (mem_inf.1 v.2).1).1 (mem_inf.1 v.2).2⟩
      invFun := fun y => ⟨S.frame.ψ.symm ⟨y.1, G6.mem_coreMod.2 y.2.1⟩, mem_inf.2
        ⟨(S.frame.ψ.symm _).2, (hiff _ (S.frame.ψ.symm _).2).2 (by
          rw [show (⟨((S.frame.ψ.symm ⟨y.1, G6.mem_coreMod.2 y.2.1⟩ : ↥V) : G),
            (S.frame.ψ.symm _).2⟩ : ↥V) = S.frame.ψ.symm ⟨y.1, G6.mem_coreMod.2 y.2.1⟩ from rfl,
            MulEquiv.apply_symm_apply]
          exact y.2.2)⟩⟩
      left_inv := fun v => by
        apply Subtype.ext
        show ((S.frame.ψ.symm ⟨_, _⟩ : ↥V) : G) = v
        rw [show (⟨(S.frame.ψ ⟨v, (mem_inf.1 v.2).1⟩ : P6), _⟩ : ↥(G6.coreMod 6)) =
          S.frame.ψ ⟨v, (mem_inf.1 v.2).1⟩ from rfl, MulEquiv.symm_apply_apply]
      right_inv := fun y => by
        apply Subtype.ext
        show (S.frame.ψ ⟨_, _⟩ : P6) = y.1
        rw [show (⟨((S.frame.ψ.symm ⟨y.1, G6.mem_coreMod.2 y.2.1⟩ : ↥V) : G), _⟩ : ↥V) =
          S.frame.ψ.symm ⟨y.1, G6.mem_coreMod.2 y.2.1⟩ from rfl, MulEquiv.apply_symm_apply] }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]

end End134

end CFSG.Quasithin.H13.NQS134
