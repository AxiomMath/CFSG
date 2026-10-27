module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4ZtDefs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Local
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem dist_le_two_cases (F : FanTree Γ G) {α w : V} (h : Γ.dist α w ≤ 2) :
    w = α ∨ Γ.Adj α w ∨ ∃ γ, Γ.Adj α γ ∧ Γ.Adj γ w := by
  obtain ⟨p, -, hp⟩ := (F.isTree.connected α w).exists_path_of_dist
  rw [← hp] at h
  cases p with
  | nil => exact Or.inl rfl
  | cons h1 p1 =>
    cases p1 with
    | nil => exact Or.inr (Or.inl h1)
    | cons h2 p2 =>
      cases p2 with
      | nil => exact Or.inr (Or.inr ⟨_, h1, h2⟩)
      | cons h3 p3 =>
        simp at h

theorem nbrStab_inf_eq_ballStab (F : FanTree Γ G) {α β : V} (hab : Γ.Adj α β) {N : Subgroup G}
    (hKβN : nbrStab Γ G β ≤ N)
    (hNtr : ∀ u v, Γ.Adj α u → Γ.Adj α v → ∃ g ∈ N ⊓ MulAction.stabilizer G α, g • u = v)
    (hN : N ⊓ MulAction.stabilizer G α ⊓ MulAction.stabilizer G β = N ⊓ nbrStab Γ G β) :
    nbrStab Γ G α ⊓ nbrStab Γ G β = ballStab Γ G 2 α := by
  have hE : N ⊓ nbrStab Γ G α = nbrStab Γ G α ⊓ nbrStab Γ G β := by
    ext g
    constructor
    · rintro ⟨hgN, hgK⟩
      have : g ∈ N ⊓ MulAction.stabilizer G α ⊓ MulAction.stabilizer G β :=
        ⟨⟨hgN, F.nbrStab_le_stabilizer α hgK⟩, MulAction.mem_stabilizer_iff.2 (hgK β hab)⟩
      rw [hN] at this
      exact ⟨hgK, this.2⟩
    · rintro ⟨hgα, hgβ⟩
      exact ⟨hKβN hgβ, hgα⟩
  have hinv : ∀ m ∈ N ⊓ MulAction.stabilizer G α, ∀ g ∈ nbrStab Γ G α ⊓ nbrStab Γ G β,
      m * g * m⁻¹ ∈ nbrStab Γ G α ⊓ nbrStab Γ G β := by
    intro m hm g hg
    rw [← hE]
    exact ⟨N.mul_mem (N.mul_mem hm.1 (hKβN hg.2)) (N.inv_mem hm.1),
      nbrStab_conj_mem F (MulAction.mem_stabilizer_iff.1 hm.2) hg.1⟩
  have hγ : ∀ γ, Γ.Adj α γ →
      nbrStab Γ G α ⊓ nbrStab Γ G γ = nbrStab Γ G α ⊓ nbrStab Γ G β := by
    intro γ hγ
    obtain ⟨n, hn, hnβ⟩ := hNtr β γ hab hγ
    have hKγ : ∀ g, g ∈ nbrStab Γ G γ ↔ n⁻¹ * g * n ∈ nbrStab Γ G β := fun g => by
      rw [← hnβ]
      exact nbrStab_smul_iff F n β g
    ext g
    constructor
    · rintro ⟨hgα, hgγ⟩
      have h1 : n⁻¹ * g * n ∈ nbrStab Γ G α ⊓ nbrStab Γ G β :=
        ⟨by simpa using nbrStab_conj_mem F (MulAction.mem_stabilizer_iff.1
          ((MulAction.stabilizer G α).inv_mem hn.2)) hgα, (hKγ g).1 hgγ⟩
      have := hinv n hn _ h1
      simpa [mul_assoc] using this
    · rintro hg
      have := hinv n⁻¹ ((N ⊓ MulAction.stabilizer G α).inv_mem hn) g hg
      exact ⟨hg.1, (hKγ g).2 (by simpa using this.2)⟩
  ext g
  constructor
  · rintro ⟨hgα, hgβ⟩ w hw
    rcases dist_le_two_cases F hw with rfl | hadj | ⟨γ, hγα, hγw⟩
    · exact MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer _ hgα)
    · exact hgα w hadj
    · have : g ∈ nbrStab Γ G α ⊓ nbrStab Γ G γ := by
        rw [hγ γ hγα]
        exact ⟨hgα, hgβ⟩
      exact this.2 w hγw
  · intro hg
    refine ⟨fun w hw => hg w ?_, fun w hw => hg w ?_⟩
    · show Γ.dist α w ≤ 2
      rw [dist_eq_one_iff_adj.2 hw]
      norm_num
    · show Γ.dist α w ≤ 2
      have h1 := F.isTree.connected.dist_triangle (u := α) (v := β) (w := w)
      have h2 : Γ.dist α β = 1 := dist_eq_one_iff_adj.2 hab
      have h3 : Γ.dist β w = 1 := dist_eq_one_iff_adj.2 hw
      omega

theorem false_of_ball_eq (F : FanTree Γ G) (h33 : Fan33 F) (h40 : Fan40 F) {α β : V}
    (hab : Γ.Adj α β) (h : nbrStab Γ G α ⊓ nbrStab Γ G β = ballStab Γ G 2 α) : False := by
  obtain ⟨x, hx, hxo⟩ := F.exists_orderOf_eq_valence α
  obtain ⟨h1, h2, h3⟩ := h33 α β hab x hx hxo
  exact (singGe_succ_iff 3).1 h40 (h3 (h2.1 (h1.1 h)))

end CFSG.Quasithin.Fan86
