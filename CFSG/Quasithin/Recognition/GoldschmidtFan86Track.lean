module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Line

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

structure Track (Γ : SimpleGraph V) (G : Type*) [Group G] [MulAction G V] where
  line : Line Γ
  τ : G
  trans : ∀ i, τ • line.vert i = line.vert (i + 2)

namespace Track

@[expose] def rev (T : Track Γ G) : Track Γ G where
  line := T.line.rev
  τ := T.τ⁻¹
  trans i := by
    rw [Line.rev_vert, Line.rev_vert, inv_smul_eq_iff, show -(i + 2) = -i - 2 by omega]
    have := T.trans (-i - 2)
    rw [show -i - 2 + 2 = -i by omega] at this
    exact this.symm

@[expose] def fixSet (T : Track Γ G) (U : Subgroup G) : Set ℤ :=
  {i | ∀ g ∈ U, g • T.line.vert i = T.line.vert i}

end Track

@[expose] def halfStab (ℓ : Line Γ) (a : ℤ) : Subgroup G where
  carrier := {g | ∀ k, a ≤ k → g • ℓ.vert k = ℓ.vert k}
  one_mem' := fun k _ => one_smul _ _
  mul_mem' := fun {g h} hg hh k hk => by rw [mul_smul, hh k hk, hg k hk]
  inv_mem' := fun {g} hg k hk => by rw [inv_smul_eq_iff]; exact (hg k hk).symm

theorem mem_halfStab_conj (T : Track Γ G) (a : ℤ) (g : G) :
    g ∈ halfStab T.line a ↔ T.τ * g * T.τ⁻¹ ∈ halfStab T.line (a + 2) := by
  have hinv : ∀ k, T.τ⁻¹ • T.line.vert (k + 2) = T.line.vert k := fun k => by
    rw [inv_smul_eq_iff]
    exact (T.trans k).symm
  constructor
  · intro hg k hk
    have e : k - 2 + 2 = k := by omega
    have h1 := hinv (k - 2)
    rw [e] at h1
    rw [mul_smul, mul_smul, h1, hg (k - 2) (by omega), T.trans (k - 2), e]
  · intro h k hk
    have h1 := h (k + 2) (by omega)
    rw [mul_smul, mul_smul, hinv k] at h1
    rw [← T.trans k] at h1
    exact MulAction.injective T.τ h1

theorem map_halfStab (T : Track Γ G) (a : ℤ) :
    (halfStab T.line a).map (MulAut.conj T.τ).toMonoidHom = halfStab T.line (a + 2) := by
  ext x
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (mem_halfStab_conj T a g).1 hg
  · intro hx
    refine ⟨T.τ⁻¹ * x * T.τ, (mem_halfStab_conj T a _).2 ?_, by simp [mul_assoc]⟩
    simpa [mul_assoc] using hx

theorem halfStab_le_add_two (ℓ : Line Γ) (a : ℤ) :
    halfStab (G := G) ℓ a ≤ halfStab (G := G) ℓ (a + 2) :=
  fun _ hg k hk => hg k (by omega)

theorem halfStab_eq_add_two (hfin : ∀ v : V, Finite (MulAction.stabilizer G v)) (T : Track Γ G)
    (a : ℤ) : halfStab (G := G) T.line a = halfStab (G := G) T.line (a + 2) := by
  have hle : halfStab (G := G) T.line (a + 2) ≤ MulAction.stabilizer G (T.line.vert (a + 2)) :=
    fun g hg => hg (a + 2) le_rfl
  have : Finite ↥(halfStab (G := G) T.line (a + 2)) :=
    haveI := hfin (T.line.vert (a + 2))
    Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  refine Subgroup.eq_of_le_of_card_ge (halfStab_le_add_two T.line a) ?_
  rw [← map_halfStab T a]
  exact (Subgroup.card_map_of_injective (MulAut.conj T.τ).injective).le

theorem halfStab_fixes_all (hfin : ∀ v : V, Finite (MulAction.stabilizer G v)) (T : Track Γ G)
    {a : ℤ} {g : G} (hg : g ∈ halfStab T.line a) (k : ℤ) : g • T.line.vert k = T.line.vert k := by
  have key : ∀ n : ℕ, halfStab (G := G) T.line (a - 2 * n) = halfStab (G := G) T.line a := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← ih, halfStab_eq_add_two hfin T (a - 2 * ((n + 1 : ℕ) : ℤ))]
      congr 1
      push_cast
      omega
  have hk : g ∈ halfStab (G := G) T.line (a - 2 * ((a - k).toNat : ℕ)) := by
    rw [key]
    exact hg
  exact hk k (by omega)

theorem Track.mem_fixSet_rev (T : Track Γ G) (U : Subgroup G) (i : ℤ) :
    i ∈ T.rev.fixSet U ↔ -i ∈ T.fixSet U := Iff.rfl

theorem Track.fixSet_eq_univ_of_unbounded_above (hT : Γ.IsTree)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (hfin : ∀ v : V, Finite (MulAction.stabilizer G v)) (T : Track Γ G) (U : Subgroup G)
    (hub : ∀ N : ℤ, ∃ i ∈ T.fixSet U, N < i) : T.fixSet U = Set.univ := by
  obtain ⟨i₀, hi₀, -⟩ := hub 0
  have hU : U ≤ halfStab T.line i₀ := fun g hg k hk => by
    obtain ⟨i, hi, hki⟩ := hub k
    exact Line.fixes_between hT hadj T.line hk hki.le (hi₀ g hg) (hi g hg)
  refine Set.eq_univ_of_forall fun k g hg => ?_
  exact halfStab_fixes_all hfin T (hU hg) k

theorem Track.fixSet_eq_univ_or_bounded (hT : Γ.IsTree)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (hfin : ∀ v : V, Finite (MulAction.stabilizer G v)) (T : Track Γ G) (U : Subgroup G) :
    T.fixSet U = Set.univ ∨ ∃ a b : ℤ, ∀ i ∈ T.fixSet U, a ≤ i ∧ i ≤ b := by
  by_cases hup : ∀ N : ℤ, ∃ i ∈ T.fixSet U, N < i
  · exact Or.inl (T.fixSet_eq_univ_of_unbounded_above hT hadj hfin U hup)
  by_cases hlow : ∀ N : ℤ, ∃ i ∈ T.fixSet U, i < N
  · left
    have hrev := T.rev.fixSet_eq_univ_of_unbounded_above hT hadj hfin U fun N => by
      obtain ⟨i, hi, hlt⟩ := hlow (-N)
      exact ⟨-i, (T.mem_fixSet_rev U (-i)).2 (by simpa using hi), by omega⟩
    refine Set.eq_univ_of_forall fun k => ?_
    have : -k ∈ T.rev.fixSet U := by rw [hrev]; trivial
    simpa using (T.mem_fixSet_rev U (-k)).1 this
  · push Not at hup hlow
    obtain ⟨N₁, h1⟩ := hup
    obtain ⟨N₂, h2⟩ := hlow
    exact Or.inr ⟨N₂, N₁, fun i hi => ⟨h2 i hi, h1 i hi⟩⟩

end CFSG.Quasithin.Fan86
