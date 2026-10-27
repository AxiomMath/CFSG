module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4ZtDefs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Arc

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem Track.index_eq_of_adj (F : FanTree Γ G) (T : Track Γ G) {i j : ℤ}
    (h : Γ.Adj (T.line.vert i) (T.line.vert j)) : j = i + 1 ∨ i = j + 1 := by
  have h1 := dist_eq_one_iff_adj.2 h
  rcases le_total i j with hij | hji
  · have := Line.dist_eq F.isTree T.line hij
    omega
  · have := Line.dist_eq F.isTree T.line hji
    rw [dist_comm] at this
    omega

theorem zt_mono (F : FanTree Γ G) {T₀ T : Track Γ G} (h : TrackPrec T₀ T)
    (hz : ∃ d, ZT T d = ⊥) : ∃ d₀, ZT T₀ d₀ = ⊥ := by
  obtain ⟨hle, u, v, huv, ⟨j₁, rfl⟩, ⟨j₂, rfl⟩, ⟨e₁, hu⟩, ⟨e₂, hv⟩⟩ := h
  obtain ⟨d, hd⟩ := hz
  have hidx := T.index_eq_of_adj F (i := e₁) (j := e₂) (by rw [hu, hv]; exact huv)
  have key : ∀ e j : ℤ, T.line.vert e = T₀.line.vert j → e % 2 = d % 2 → ZT T₀ j = ⊥ := by
    intro e j hej hpar
    obtain ⟨k, hk⟩ : ∃ k : ℤ, e = d + 2 * k := ⟨(e - d) / 2, by omega⟩
    have hZe : ZT T e = ⊥ := by
      rw [hk]
      exact zt_shift F T hd k
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

theorem zt_push (F : FanTree Γ G) {T₀ T : Track Γ G} (h : PushReach T₀ T) :
    (∃ d, ZT T d = ⊥) → ∃ d₀, ZT T₀ d₀ = ⊥ := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact id
  | head hab _ ih => exact fun hz => zt_mono F hab (ih hz)

theorem fan49_of_main (F : FanTree Γ G)
    (hpush : ∀ T : Track Γ G, T.fixer ≠ ⊥ → ∃ T' : Track Γ G, PushReach T T' ∧ InPiStar T')
    (hmain : ∀ T : Track Γ G, InPiStar T → ∃ d, ZT T d = ⊥) (T : Track Γ G) (i : ℤ) :
    ∀ z ∈ T.fixer, (∀ g ∈ MulAction.stabilizer G (T.line.vert i) ⊓
      MulAction.stabilizer G (T.line.vert (i + 1)), g * z = z * g) → z = 1 := by
  intro z hz hcomm
  by_cases hT : T.fixer = ⊥
  · rw [hT] at hz
    exact Subgroup.mem_bot.1 hz
  obtain ⟨T', hreach, hstar⟩ := hpush T hT
  obtain ⟨d, hd⟩ := hmain T' hstar
  obtain ⟨d₀, hd₀⟩ := zt_push F hreach ⟨d, hd⟩
  have hedge : ∀ e : ℤ, (e = i ∨ e = i + 1) → ZT T e = ⊥ → z = 1 := by
    intro e he hZ
    have : z ∈ ZT T e := by
      rw [mem_ZT_iff]
      refine ⟨hz, fun k hk => hcomm k ?_⟩
      rcases he with he | he
      · rw [he] at hk
        exact F.nbrStab_le_edge _ (T.line.adj i) hk
      · rw [he] at hk
        exact ⟨MulAction.mem_stabilizer_iff.2 (hk _ (T.line.adj i).symm),
          F.nbrStab_le_stabilizer _ hk⟩
    rw [hZ] at this
    exact Subgroup.mem_bot.1 this
  by_cases hpar : i % 2 = d₀ % 2
  · obtain ⟨k, hk⟩ : ∃ k : ℤ, i = d₀ + 2 * k := ⟨(i - d₀) / 2, by omega⟩
    exact hedge i (Or.inl rfl) (hk ▸ zt_shift F T hd₀ k)
  · obtain ⟨k, hk⟩ : ∃ k : ℤ, i + 1 = d₀ + 2 * k := ⟨(i + 1 - d₀) / 2, by omega⟩
    exact hedge (i + 1) (Or.inr rfl) (hk ▸ zt_shift F T hd₀ k)

end CFSG.Quasithin.Fan86
