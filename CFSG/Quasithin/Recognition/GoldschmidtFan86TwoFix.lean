module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Setting

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem adj_smul_of_mem_stabilizer {α x : V} {m : G} (hm : m ∈ MulAction.stabilizer G α)
    (hx : Γ.Adj α x) : Γ.Adj α (m • x) := by
  have := (F.adj_smul m α x).2 hx
  rwa [MulAction.mem_stabilizer_iff.1 hm] at this

theorem ncard_neighborSet_le (v : V) : (Γ.neighborSet v).ncard ≤ 5 ∧ (Γ.neighborSet v).Finite := by
  have h := F.valence v
  have hpos : 0 < Nat.card (Γ.neighborSet v) := by omega
  refine ⟨?_, Set.finite_of_ncard_pos hpos⟩
  rw [← Nat.card_coe_set_eq]
  omega

theorem no_small_invariant {α u w : V} (hu : Γ.Adj α u) (hw : Γ.Adj α w) (huw : u ≠ w)
    {g₁ g₂ : G} (h₁α : g₁ ∈ MulAction.stabilizer G α) (h₂α : g₂ ∈ MulAction.stabilizer G α)
    (h₁u : g₁ • u = u) (h₁w : g₁ • w ≠ w) (h₂w : g₂ • w = w) (h₂u : g₂ • u ≠ u)
    (S : Set V) (hS : S ⊆ Γ.neighborSet α) (hinv₁ : ∀ x ∈ S, g₁ • x ∈ S)
    (hinv₂ : ∀ x ∈ S, g₂ • x ∈ S) (hne : S.Nonempty) (hle : S.ncard ≤ 2) : False := by
  have hfix₁ : ∀ x y, Γ.Adj α x → Γ.Adj α y → x ≠ y → g₁ • x = x → g₁ • y = y → False :=
    fun x y hx hy hxy h1 h2 => h₁w (F.frobenius_two α x y hx hy hxy g₁ h₁α h1 h2 w hw)
  have hfix₂ : ∀ x y, Γ.Adj α x → Γ.Adj α y → x ≠ y → g₂ • x = x → g₂ • y = y → False :=
    fun x y hx hy hxy h1 h2 => h₂u (F.frobenius_two α x y hx hy hxy g₂ h₂α h1 h2 u hu)
  have hpos : 0 < S.ncard := by
    rcases hne with ⟨x, hx⟩
    exact Set.ncard_pos (Set.Finite.subset (F.ncard_neighborSet_le α).2 hS) |>.2 ⟨x, hx⟩
  have hsize : S.ncard = 1 ∨ S.ncard = 2 := by omega
  rcases hsize with h1 | h2
  · obtain ⟨x, rfl⟩ := Set.ncard_eq_one.1 h1
    have hx : Γ.Adj α x := hS rfl
    have e₁ : g₁ • x = x := by simpa using hinv₁ x rfl
    have e₂ : g₂ • x = x := by simpa using hinv₂ x rfl
    have hxu : x = u := by
      by_contra hxu
      exact hfix₁ x u hx hu hxu e₁ h₁u
    have hxw : x = w := by
      by_contra hxw
      exact hfix₂ x w hx hw hxw e₂ h₂w
    exact huw (hxu.symm.trans hxw)
  · obtain ⟨x, y, hxy, rfl⟩ := Set.ncard_eq_two.1 h2
    have hx : Γ.Adj α x := hS (by simp)
    have hy : Γ.Adj α y := hS (by simp)
    have swap : ∀ g : G, (∀ a b, Γ.Adj α a → Γ.Adj α b → a ≠ b → g • a = a → g • b = b → False) →
        (∀ z ∈ ({x, y} : Set V), g • z ∈ ({x, y} : Set V)) → g • x = y ∧ g • y = x := by
      intro g hg hinv
      have hgx := hinv x (by simp)
      have hgy := hinv y (by simp)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgx hgy
      rcases hgx with hgx | hgx <;> rcases hgy with hgy | hgy
      · exact (hxy (MulAction.injective g (hgx.trans hgy.symm))).elim
      · exact (hg x y hx hy hxy hgx hgy).elim
      · exact ⟨hgx, hgy⟩
      · exact (hxy (MulAction.injective g (hgx.trans hgy.symm))).elim
    obtain ⟨a₁, b₁⟩ := swap g₁ hfix₁ hinv₁
    obtain ⟨a₂, b₂⟩ := swap g₂ hfix₂ hinv₂
    have hprod : ∀ z, z = x ∨ z = y → (g₁ * g₂) • z = z := by
      rintro z (rfl | rfl)
      · rw [mul_smul, a₂, b₁]
      · rw [mul_smul, b₂, a₁]
    have hall := F.frobenius_two α x y hx hy hxy (g₁ * g₂)
      (Subgroup.mul_mem _ h₁α h₂α) (hprod x (Or.inl rfl)) (hprod y (Or.inr rfl)) u hu
    apply h₂u
    have h' : g₁ • (g₂ • u) = g₁ • u := by rw [← mul_smul, hall, h₁u]
    exact MulAction.injective g₁ h'

theorem transitive_of_two_fixers {α u w : V} (hu : Γ.Adj α u) (hw : Γ.Adj α w) (huw : u ≠ w)
    {g₁ g₂ : G} (h₁α : g₁ ∈ MulAction.stabilizer G α) (h₂α : g₂ ∈ MulAction.stabilizer G α)
    (h₁u : g₁ • u = u) (h₁w : g₁ • w ≠ w) (h₂w : g₂ • w = w) (h₂u : g₂ • u ≠ u)
    {a b : V} (ha : Γ.Adj α a) (hb : Γ.Adj α b) :
    ∃ m ∈ Subgroup.closure ({g₁, g₂} : Set G), m • α = α ∧ m • a = b := by
  set M := Subgroup.closure ({g₁, g₂} : Set G) with hM
  have hg₁M : g₁ ∈ M := Subgroup.subset_closure (by simp)
  have hg₂M : g₂ ∈ M := Subgroup.subset_closure (by simp)
  have hMα : M ≤ MulAction.stabilizer G α := by
    rw [hM, Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · exact h₁α
    · simpa using h₂α
  let O : Set V := {x | ∃ m ∈ M, m • a = x}
  have hOsub : O ⊆ Γ.neighborSet α := by
    rintro _ ⟨m, hm, rfl⟩
    exact F.adj_smul_of_mem_stabilizer (hMα hm) ha
  have hOinv : ∀ m ∈ M, ∀ x ∈ O, m • x ∈ O := by
    rintro m hm _ ⟨m', hm', rfl⟩
    exact ⟨m * m', M.mul_mem hm hm', by rw [mul_smul]⟩
  have hDinv : ∀ m ∈ M, ∀ x ∈ Γ.neighborSet α \ O, m • x ∈ Γ.neighborSet α \ O := by
    rintro m hm x ⟨hx, hxO⟩
    refine ⟨F.adj_smul_of_mem_stabilizer (hMα hm) hx, fun hmx => hxO ?_⟩
    have := hOinv m⁻¹ (M.inv_mem hm) _ hmx
    simpa using this
  by_contra hcon
  have hbO : b ∉ O := by
    rintro ⟨m, hm, hmb⟩
    exact hcon ⟨m, hm, MulAction.mem_stabilizer_iff.1 (hMα hm), hmb⟩
  have hfin := F.ncard_neighborSet_le α
  have hsum := Set.ncard_sdiff_add_ncard_of_subset hOsub hfin.2
  have hOne : O.Nonempty := ⟨a, 1, M.one_mem, one_smul _ _⟩
  have hDne : (Γ.neighborSet α \ O).Nonempty := ⟨b, hb, hbO⟩
  by_cases hsmall : O.ncard ≤ 2
  · exact F.no_small_invariant hu hw huw h₁α h₂α h₁u h₁w h₂w h₂u O hOsub
      (fun x hx => hOinv g₁ hg₁M x hx) (fun x hx => hOinv g₂ hg₂M x hx) hOne hsmall
  · exact F.no_small_invariant hu hw huw h₁α h₂α h₁u h₁w h₂w h₂u (Γ.neighborSet α \ O)
      Set.sdiff_subset (fun x hx => hDinv g₁ hg₁M x hx) (fun x hx => hDinv g₂ hg₂M x hx) hDne
      (by omega)

end FanTree

end CFSG.Quasithin.Fan86
