module

public import CFSG.Quasithin.EmptyFaithful.SzC4S8CMat

public section

namespace CFSG.Quasithin.SzC4S8D

open CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.Quasithin.SzC4S8C

section Abstract

variable {F : Type} [Field F] [Fintype F]

@[expose] noncomputable def actN (hF : Fintype.card F = 2) (y : Multiplicative (Fin 3 → F)) :
    Multiplicative (Fin 3 → F) :=
  Multiplicative.ofAdd ((cmF hF).mulVec (Multiplicative.toAdd y))

@[expose] noncomputable def actM (hF : Fintype.card F = 2)
    (y : Multiplicative (Fin 2 → Fin 3 → F)) : Multiplicative (Fin 2 → Fin 3 → F) :=
  Multiplicative.ofAdd fun i => (cmF hF).mulVec (Multiplicative.toAdd y i)

@[expose] def evC (i : Fin 2) : Multiplicative (Fin 2 → Fin 3 → F) →* Multiplicative (Fin 3 → F)
    where
  toFun y := Multiplicative.ofAdd (Multiplicative.toAdd y i)
  map_one' := rfl
  map_mul' _ _ := rfl

omit [Field F] in
theorem natCard_three (hF : Fintype.card F = 2) : Nat.card (Multiplicative (Fin 3 → F)) = 8 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card]
  simp only [Fintype.card_fun, Fintype.card_fin, hF]
  norm_num

theorem eq_bot_or_eq_top_of_invariant (hF : Fintype.card F = 2)
    (S : Subgroup (Multiplicative (Fin 3 → F))) (hS : ∀ y ∈ S, actN hF y ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  rw [eq_top_iff]
  intro w _
  by_cases hw : w = 1
  · rw [hw]
    exact S.one_mem
  · have hv0 : Multiplicative.toAdd (v : Multiplicative (Fin 3 → F)) ≠ 0 := fun h0 =>
      hv1 (Subtype.ext (by simpa using h0))
    have hw0 : Multiplicative.toAdd w ≠ 0 := fun h0 => hw (by simpa using h0)
    obtain ⟨n, hn⟩ := cmF_orbit hF _ _ hv0 hw0
    have key : ∀ m : ℕ, Multiplicative.ofAdd ((fun u => (cmF hF).mulVec u)^[m]
        (Multiplicative.toAdd (v : Multiplicative (Fin 3 → F)))) ∈ S := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Function.iterate_succ_apply']
        exact hS _ ih
    have h1 := key n
    rw [hn] at h1
    simpa using h1

theorem card_invariant_two (hF : Fintype.card F = 2)
    (Y : Subgroup (Multiplicative (Fin 2 → Fin 3 → F))) (hY : ∀ y ∈ Y, actM hF y ∈ Y) :
    Nat.card Y = 1 ∨ Nat.card Y = 8 ∨ Nat.card Y = 64 := by
  let f : ↥Y →* Multiplicative (Fin 3 → F) := (evC 1).comp Y.subtype
  let h : ↥f.ker →* Multiplicative (Fin 3 → F) := (evC 0).comp (Y.subtype.comp f.ker.subtype)
  have hrange : Nat.card f.range = 1 ∨ Nat.card f.range = 8 := by
    rcases eq_bot_or_eq_top_of_invariant hF f.range (by
      intro y hy
      obtain ⟨x, rfl⟩ := hy
      exact ⟨⟨actM hF (x : Multiplicative (Fin 2 → Fin 3 → F)), hY _ x.2⟩, rfl⟩) with hb | ht
    · left
      rw [hb]
      exact Subgroup.card_bot
    · right
      rw [ht, Subgroup.card_top, natCard_three hF]
  have hinj : Function.Injective h := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : (evC 0) ((x : ↥Y) : Multiplicative (Fin 2 → Fin 3 → F)) = 1 := hx
    have h2 : (evC 1) ((x : ↥Y) : Multiplicative (Fin 2 → Fin 3 → F)) = 1 := x.2
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · exact congrArg Multiplicative.toAdd h1
    · exact congrArg Multiplicative.toAdd h2
  have hker : Nat.card f.ker = 1 ∨ Nat.card f.ker = 8 := by
    have e1 := Subgroup.card_ker_mul_card_range h
    rw [(MonoidHom.ker_eq_bot_iff h).mpr hinj, Subgroup.card_bot, one_mul] at e1
    rw [← e1]
    rcases eq_bot_or_eq_top_of_invariant hF h.range (by
      intro y hy
      obtain ⟨x, rfl⟩ := hy
      have hx2 : (evC 1) ((x : ↥Y) : Multiplicative (Fin 2 → Fin 3 → F)) = 1 := x.2
      have hxa : Multiplicative.toAdd ((x : ↥Y) : Multiplicative (Fin 2 → Fin 3 → F)) 1 = 0 :=
        congrArg Multiplicative.toAdd hx2
      refine ⟨⟨⟨actM hF (x : Multiplicative (Fin 2 → Fin 3 → F)), hY _ x.1.2⟩, ?_⟩, rfl⟩
      show (evC 1) (actM hF (x : Multiplicative (Fin 2 → Fin 3 → F))) = 1
      apply Multiplicative.toAdd.injective
      show (cmF hF).mulVec (Multiplicative.toAdd
        ((x : ↥Y) : Multiplicative (Fin 2 → Fin 3 → F)) 1) = 0
      rw [hxa]
      exact Matrix.mulVec_zero _) with hb | ht
    · left
      rw [hb]
      exact Subgroup.card_bot
    · right
      rw [ht, Subgroup.card_top, natCard_three hF]
  have e2 := Subgroup.card_ker_mul_card_range f
  rw [← e2]
  rcases hker with h1 | h1 <;> rcases hrange with h2 | h2 <;> rw [h1, h2] <;> omega

end Abstract

section Sections

variable {G : Type} [Group G] {A V Z : Subgroup G} {F : Type} [Field F] [Fintype F]
  {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F)} {α : ↥A →* ↥Γ}

theorem relIndex_dual_two_top (hF : Fintype.card F = 2)
    (h : IsSumOfNaturalModulesVia A V Z α true 2) : Z.relIndex V = 64 := by
  obtain ⟨-, -, β, hs, hk, -⟩ := h
  rw [Subgroup.relIndex, ← hk, Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective β hs,
    Subgroup.card_top, natCard_mult hF 2]
  norm_num

theorem relIndex_dual_two (hF : Fintype.card F = 2) (h : IsSumOfNaturalModulesVia A V Z α true 2)
    (g : ↥A) (hg : moduleAct true (α g : Matrix.GeneralLinearGroup (Fin 3) F) = cmF hF)
    {X : Subgroup G} (hXV : X ≤ V) (hX : ∀ x ∈ X, (g : G) * x * (g : G)⁻¹ ∈ X) :
    Z.relIndex X = 1 ∨ Z.relIndex X = 8 ∨ Z.relIndex X = 64 := by
  obtain ⟨hAV, -, β, -, hk, he⟩ := h
  have e : Z.relIndex X = Nat.card ((X.subgroupOf V).map β) := by
    rw [← Subgroup.relIndex_subgroupOf hXV, ← hk, Subgroup.relIndex_ker]
  rw [e]
  refine card_invariant_two hF _ ?_
  rintro y ⟨u, hu, rfl⟩
  have hvV : (g : G) * (u : G) * (g : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (hAV g.2) u).mp u.2
  refine ⟨⟨(g : G) * (u : G) * (g : G)⁻¹, hvV⟩, hX _ hu, ?_⟩
  apply Multiplicative.toAdd.injective
  funext i
  rw [he g u ⟨_, hvV⟩ rfl i, hg]
  rfl

end Sections

end CFSG.Quasithin.SzC4S8D
