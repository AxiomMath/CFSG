module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5Defs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86LocalChar

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

theorem units_exists_involution {p : ℕ} (hp : p = 5) (a : (ZMod p)ˣ) (ha : a ≠ 1) :
    ∃ j : Fin 4, (a ^ (j : ℕ)) ^ 2 = 1 ∧ a ^ (j : ℕ) ≠ 1 := by
  subst hp
  revert a
  decide

theorem units_three {p : ℕ} (hp : p = 3) (a b : (ZMod p)ˣ) (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  subst hp
  revert a b
  decide

theorem units_five_mem {p : ℕ} (hp : p = 5) (a b : (ZMod p)ˣ) (ha : a ≠ 1) (hb : b ^ 2 = 1) :
    ∃ j : Fin 4, a ^ (j : ℕ) = b := by
  subst hp
  revert a b
  decide

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem mem_Gcirc {α β : V} {g : G} :
    g ∈ Gcirc Γ G α β ↔
      g ∈ MulAction.stabilizer G α ⊓ MulAction.stabilizer G β ∧ g * g ∈ nbrStab Γ G α := Iff.rfl

namespace Line

variable (ℓ : Line Γ)

theorem valence_add_two (F : FanTree Γ G) (i : ℤ) :
    valence Γ (ℓ.vert (i + 2)) = valence Γ (ℓ.vert i) := by
  have h1 := F.alternating _ _ (ℓ.adj i)
  have h2 := F.alternating _ _ (ℓ.adj (i + 1))
  have h3 := F.valence (ℓ.vert i)
  have h4 := F.valence (ℓ.vert (i + 1))
  have h5 := F.valence (ℓ.vert (i + 1 + 1))
  rw [show i + 1 + 1 = i + 2 by omega] at h2 h5
  show Nat.card (Γ.neighborSet (ℓ.vert (i + 2))) = Nat.card (Γ.neighborSet (ℓ.vert i))
  omega

theorem edgeCirc_of_five {i : ℤ} (h : valence Γ (ℓ.vert i) = 5) :
    ℓ.edgeCirc (G := G) i = Gcirc Γ G (ℓ.vert i) (ℓ.vert (i + 1)) := by
  simp [edgeCirc, h]

theorem edgeCirc_of_ne_five {i : ℤ} (h : valence Γ (ℓ.vert i) ≠ 5) :
    ℓ.edgeCirc (G := G) i = Gcirc Γ G (ℓ.vert (i + 1)) (ℓ.vert i) := by
  simp [edgeCirc, h]

theorem edgeCirc_fix {i : ℤ} {g : G} (hg : g ∈ ℓ.edgeCirc (G := G) i) :
    g • ℓ.vert i = ℓ.vert i ∧ g • ℓ.vert (i + 1) = ℓ.vert (i + 1) := by
  by_cases h : valence Γ (ℓ.vert i) = 5
  · rw [ℓ.edgeCirc_of_five h] at hg
    exact ⟨MulAction.mem_stabilizer_iff.1 hg.1.1, MulAction.mem_stabilizer_iff.1 hg.1.2⟩
  · rw [ℓ.edgeCirc_of_ne_five h] at hg
    exact ⟨MulAction.mem_stabilizer_iff.1 hg.1.2, MulAction.mem_stabilizer_iff.1 hg.1.1⟩

theorem nbrStab_subset_edgeCirc (F : FanTree Γ G) {i j : ℤ} (hj : j = i ∨ j = i + 1)
    (h5 : valence Γ (ℓ.vert j) = 5) {g : G} (hg : g ∈ nbrStab Γ G (ℓ.vert j)) :
    g ∈ ℓ.edgeCirc (G := G) i := by
  have hgg : g * g ∈ nbrStab Γ G (ℓ.vert j) := (nbrStab Γ G (ℓ.vert j)).mul_mem hg hg
  have hst : g • ℓ.vert j = ℓ.vert j :=
    MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer _ hg)
  rcases hj with rfl | rfl
  · rw [ℓ.edgeCirc_of_five h5]
    exact ⟨⟨F.nbrStab_le_stabilizer _ hg, MulAction.mem_stabilizer_iff.2 (hg _ (ℓ.adj j))⟩, hgg⟩
  · have hne : valence Γ (ℓ.vert i) ≠ 5 := fun h => F.alternating _ _ (ℓ.adj i) (h.trans h5.symm)
    rw [ℓ.edgeCirc_of_ne_five hne]
    exact ⟨⟨F.nbrStab_le_stabilizer _ hg, MulAction.mem_stabilizer_iff.2 (hg _ (ℓ.adj i).symm)⟩,
      hgg⟩

end Line

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem exists_gcirc_not_mem_right (h40 : Fan40 F) {u w : V} (huw : Γ.Adj u w) :
    ∃ g ∈ Gcirc Γ G u w, g ∉ nbrStab Γ G w := by
  by_contra hcon
  push Not at hcon
  refine F.not_nbrStab_le_nbrStab h40 huw fun g hg => hcon g ?_
  exact ⟨⟨F.nbrStab_le_stabilizer _ hg, MulAction.mem_stabilizer_iff.2 (hg _ huw)⟩,
    (nbrStab Γ G u).mul_mem hg hg⟩

theorem exists_gcirc_not_mem_left {u w : V} (huw : Γ.Adj u w) (h5 : Fan86.valence Γ u = 5) :
    ∃ g ∈ Gcirc Γ G u w, g ∉ nbrStab Γ G u := by
  obtain ⟨φ, key, -⟩ := F.exists_edge_char huw
  obtain ⟨g₀, hg₀, hg₀w, c, hc, hgc⟩ := F.frobenius_nonreg u w huw
  let e₀ : ↥(MulAction.stabilizer G u ⊓ MulAction.stabilizer G w) :=
    ⟨g₀, hg₀, MulAction.mem_stabilizer_iff.2 hg₀w⟩
  have hφ : φ e₀ ≠ 1 := fun h =>
    hgc (mem_nbrStab.1 ((key e₀).2 h) c hc)
  obtain ⟨j, hj2, hj1⟩ := units_exists_involution h5 (φ e₀) hφ
  refine ⟨((e₀ ^ (j : ℕ) : ↥(MulAction.stabilizer G u ⊓ MulAction.stabilizer G w)) : G),
    ⟨(e₀ ^ (j : ℕ)).2, ?_⟩, ?_⟩
  · have h1 : φ (e₀ ^ (j : ℕ) * e₀ ^ (j : ℕ)) = 1 := by
      rw [map_mul, ← pow_two, map_pow]
      exact hj2
    exact (key _).2 h1
  · intro hmem
    exact hj1 (by rw [← map_pow]; exact (key _).1 hmem)

end FanTree

namespace Line

theorem exists_edgeCirc_not_mem (F : FanTree Γ G) (h40 : Fan40 F) (ℓ : Line Γ) (i : ℤ) :
    (∃ g ∈ ℓ.edgeCirc (G := G) i, g ∉ nbrStab Γ G (ℓ.vert i)) ∧
      ∃ g ∈ ℓ.edgeCirc (G := G) i, g ∉ nbrStab Γ G (ℓ.vert (i + 1)) := by
  by_cases h : valence Γ (ℓ.vert i) = 5
  · rw [ℓ.edgeCirc_of_five h]
    exact ⟨F.exists_gcirc_not_mem_left (ℓ.adj i) h, F.exists_gcirc_not_mem_right h40 (ℓ.adj i)⟩
  · rw [ℓ.edgeCirc_of_ne_five h]
    have h5 : valence Γ (ℓ.vert (i + 1)) = 5 := by
      have h1 := F.valence (ℓ.vert i)
      have h2 := F.valence (ℓ.vert (i + 1))
      have h3 := F.alternating _ _ (ℓ.adj i)
      change Nat.card _ = 3 ∨ Nat.card _ = 5 at h1 h2
      change Nat.card _ ≠ Nat.card _ at h3
      change valence Γ (ℓ.vert i) ≠ 5 at h
      change Nat.card _ = 5
      change Nat.card _ ≠ 5 at h
      omega
    exact ⟨F.exists_gcirc_not_mem_right h40 (ℓ.adj i).symm,
      F.exists_gcirc_not_mem_left (ℓ.adj i).symm h5⟩

end Line

end CFSG.Quasithin.Fan86
