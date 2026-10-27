module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4ZtMono
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PCore

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem Line.valence_add_two_mul (F : FanTree Γ G) (ℓ : Line Γ) (i k : ℤ) :
    valence Γ (ℓ.vert (i + 2 * k)) = valence Γ (ℓ.vert i) := by
  induction k using Int.induction_on with
  | zero => simp
  | succ m ih =>
    rw [show i + 2 * ((m : ℤ) + 1) = i + 2 * m + 2 by omega, ℓ.valence_add_two F, ih]
  | pred m ih =>
    have h := ℓ.valence_add_two F (i + 2 * (-(m : ℤ) - 1))
    rw [show i + 2 * (-(m : ℤ) - 1) + 2 = i + 2 * (-(m : ℤ)) by omega] at h
    exact h.symm.trans ih

theorem Line.mod_two_eq_of_valence_eq (F : FanTree Γ G) (ℓ : Line Γ) {i j : ℤ}
    (h : valence Γ (ℓ.vert i) = valence Γ (ℓ.vert j)) : i % 2 = j % 2 := by
  by_contra hne
  obtain ⟨k, hk⟩ : ∃ k : ℤ, j = i + 1 + 2 * k := ⟨(j - i - 1) / 2, by omega⟩
  have h1 : valence Γ (ℓ.vert j) = valence Γ (ℓ.vert (i + 1)) := by
    rw [hk, ℓ.valence_add_two_mul F]
  exact F.alternating _ _ (ℓ.adj i) (h.trans h1)

theorem zt_mono_five (F : FanTree Γ G) {T₀ T : Track Γ G} (h : TrackPrec T₀ T)
    (hz : ∃ d, valence Γ (T.line.vert d) = 5 ∧ ZT T d = ⊥) :
    ∃ d₀, valence Γ (T₀.line.vert d₀) = 5 ∧ ZT T₀ d₀ = ⊥ := by
  obtain ⟨hle, u, v, huv, ⟨j₁, rfl⟩, ⟨j₂, rfl⟩, ⟨e₁, hu⟩, ⟨e₂, hv⟩⟩ := h
  obtain ⟨d, hd5, hd⟩ := hz
  have hidx := T.index_eq_of_adj F (i := e₁) (j := e₂) (by rw [hu, hv]; exact huv)
  have key : ∀ e j : ℤ, T.line.vert e = T₀.line.vert j → e % 2 = d % 2 →
      valence Γ (T₀.line.vert j) = 5 ∧ ZT T₀ j = ⊥ := by
    intro e j hej hpar
    obtain ⟨k, hk⟩ : ∃ k : ℤ, e = d + 2 * k := ⟨(e - d) / 2, by omega⟩
    have hval : valence Γ (T₀.line.vert j) = 5 := by
      rw [← hej, hk, T.line.valence_add_two_mul F]
      exact hd5
    have hZe : ZT T e = ⊥ := by
      rw [hk]
      exact zt_shift F T hd k
    refine ⟨hval, ?_⟩
    by_contra hne
    have hedge := F.nbrStab_le_edge (T₀.line.vert j) (T₀.line.adj j)
    obtain ⟨z, hz, hz1, hz2⟩ := exists_involution_of_le_edge F (T₀.line.adj j)
      (fun g hg => hedge (T₀.fixer_le_nbrStab F j ((mem_ZT_iff.1 hg).1))) hne
    have hzT : z ∈ T.fixer := (omega1_le _) (hle (Subgroup.subset_closure
      ⟨(mem_ZT_iff.1 hz).1, hz2⟩))
    have : z ∈ ZT T e := by
      rw [mem_ZT_iff]
      refine ⟨hzT, fun k' hk' => ?_⟩
      rw [hej] at hk'
      exact (mem_ZT_iff.1 hz).2 k' hk'
    rw [hZe] at this
    exact hz1 (Subgroup.mem_bot.1 this)
  by_cases h1 : e₁ % 2 = d % 2
  · exact ⟨j₁, key e₁ j₁ hu h1⟩
  · exact ⟨j₂, key e₂ j₂ hv (by omega)⟩

theorem zt_push_five (F : FanTree Γ G) {T₀ T : Track Γ G} (h : PushReach T₀ T) :
    (∃ d, valence Γ (T.line.vert d) = 5 ∧ ZT T d = ⊥) →
      ∃ d₀, valence Γ (T₀.line.vert d₀) = 5 ∧ ZT T₀ d₀ = ⊥ := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact id
  | head hab _ ih => exact fun hz => zt_mono_five F hab (ih hz)

end CFSG.Quasithin.Fan86
