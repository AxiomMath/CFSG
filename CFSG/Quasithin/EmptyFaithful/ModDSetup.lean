module

public import CFSG.Quasithin.EmptyFaithful.ModDPencil
public import CFSG.Quasithin.EmptyFaithful.ModDData2

public section

namespace CFSG.Quasithin.ModD

open CFSG.CosetTable CFSG.Quasithin

variable
  {M : Type} [Group M] [Finite M]

theorem pencil_setup (hcard : Nat.card M = 2 ^ 6) (φ : U33G →* MulAut M)
    (hirr : ∀ N : Subgroup M, (∀ g : U33G, ∀ n ∈ N, φ g n ∈ N) → N = ⊥ ∨ N = ⊤)
    {z : M} (hz : z ≠ 1) (hz2 : z ^ 2 = 1) (hzT : ∀ g ∈ u33Data.T, φ g z = z)
    {V : Subgroup M} (hzV : z ∈ V) (hV4 : Nat.card V = 4)
    {Y₁ Y₂ : Subgroup U33G} (hY₁T : u33Data.T ≤ Y₁) (hY₂T : u33Data.T ≤ Y₂)
    (hY₁1 : Y₁ ≠ u33Data.T) (hY₁2 : Y₁ ≠ ⊤) (hY₂1 : Y₂ ≠ u33Data.T) (hY₂2 : Y₂ ≠ ⊤) (hY : Y₁ ≠ Y₂)
    (hV : ∀ g ∈ Y₁, ∀ v ∈ V, φ g v ∈ V) :
    Y₁ = u33Data.B ∧ Y₂ = u33Data.A ∧
    ∃ (ε : M → Fin 63) (m₁ m₂ : M),
      (∀ g, ε (φ g z) = vHom g 0) ∧
      (∀ m n, (∃ g, φ g z = m) → (∃ g, φ g z = n) → ε m = ε n → m = n) ∧
      (∀ g m, (∃ h, φ h z = m) → ε (φ g m) = vHom g (ε m)) ∧
      (∀ m, m ≠ 1 → ∃ g, φ g z = m) ∧
      m₁ ∈ V ∧ m₂ ∈ V ∧ m₁ ≠ 1 ∧ m₂ ≠ 1 ∧ m₁ ≠ z ∧ m₂ ≠ z ∧ m₁ ≠ m₂ ∧
      (∀ v ∈ V, v = 1 ∨ v = z ∨ v = m₁ ∨ v = m₂) ∧
      ((ε m₁ = 37 ∧ ε m₂ = 43) ∨ (ε m₁ = 43 ∧ ε m₂ = 37)) := by
  classical
  have hstab := stab_eq_A hcard φ hirr hz hz2 hzT
  have hst : ∀ g, φ g z = z ↔ vHom g 0 = 0 := by
    intro g
    have h : g ∈ stabSub φ z ↔ g ∈ stabπ vHom := by rw [hstab, stab_vHom]
    exact h.trans mem_stabπ
  obtain ⟨ε, hε1, hε2, hε3⟩ := exists_label φ z vHom 0 hst
  have hsurj : ∀ j, ∃ g, ε (φ g z) = j := fun j => by
    obtain ⟨g, hg⟩ := vHom_trans j
    exact ⟨g, by rw [hε1]; exact hg⟩
  have horb : ∀ m, m ≠ 1 → ∃ g, φ g z = m :=
    orbit_eq_ne_one φ hz (by rw [hcard]; simp) ε hε2 hsurj
  have hεz : ε z = 0 := by
    have h := hε1 1
    simpa using h
  have hzorb : ∃ g, φ g z = z := ⟨1, by simp⟩
  have hVset : (V : Set M).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hV4
  have h1z : ({1, z} : Set M).ncard = 2 := Set.ncard_pair (Ne.symm hz)
  have hsubV : ({1, z} : Set M) ⊆ (V : Set M) := by
    intro x hx
    rcases hx with rfl | rfl
    · exact V.one_mem
    · exact hzV
  have hdiff : ((V : Set M) \ {1, z}).ncard = 2 := by
    rw [Set.ncard_sdiff hsubV, hVset, h1z]
  obtain ⟨m₁, m₂, hm12, hW⟩ := Set.ncard_eq_two.1 hdiff
  have hm₁ : m₁ ∈ (V : Set M) \ {1, z} := by rw [hW]; exact Or.inl rfl
  have hm₂ : m₂ ∈ (V : Set M) \ {1, z} := by rw [hW]; exact Or.inr rfl
  obtain ⟨hm₁V, hm₁n⟩ := hm₁
  obtain ⟨hm₂V, hm₂n⟩ := hm₂
  have hm₁1 : m₁ ≠ 1 := fun h => hm₁n (Or.inl h)
  have hm₁z : m₁ ≠ z := fun h => hm₁n (Or.inr h)
  have hm₂1 : m₂ ≠ 1 := fun h => hm₂n (Or.inl h)
  have hm₂z : m₂ ≠ z := fun h => hm₂n (Or.inr h)
  have hVcases : ∀ v ∈ V, v = 1 ∨ v = z ∨ v = m₁ ∨ v = m₂ := by
    intro v hv
    by_cases h1 : v = 1
    · exact Or.inl h1
    by_cases h2 : v = z
    · exact Or.inr (Or.inl h2)
    have hvW : v ∈ (V : Set M) \ {1, z} := ⟨hv, by simp [h1, h2]⟩
    rw [hW] at hvW
    rcases hvW with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have hp0 : ε m₁ ≠ 0 := fun h =>
    hm₁z (hε2 m₁ z (horb m₁ hm₁1) hzorb (by rw [h, hεz]))
  have hq0 : ε m₂ ≠ 0 := fun h =>
    hm₂z (hε2 m₂ z (horb m₂ hm₂1) hzorb (by rw [h, hεz]))
  have hpq : ε m₁ ≠ ε m₂ := fun h => hm12 (hε2 m₁ m₂ (horb m₁ hm₁1) (horb m₂ hm₂1) h)
  have hinv : ∀ g : U33G, (∀ v ∈ V, φ g v ∈ V) → ∀ v ∈ V, v ≠ 1 →
      (φ g v = z ∨ φ g v = m₁ ∨ φ g v = m₂) := by
    intro g hg v hv hv1
    have h1 : φ g v ∈ V := hg v hv
    have h2 : φ g v ≠ 1 := fun h => hv1 ((φ g).injective (by rw [h, map_one]))
    rcases hVcases _ h1 with h | h | h | h
    · exact absurd h h2
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hone : ∀ k : Fin 5, (∀ v ∈ V, φ (u33GenPG k.val) v ∈ V) → ∀ v ∈ V, v ≠ 1 →
      (vImg k (ε v) = 0 ∨ vImg k (ε v) = ε m₁ ∨ vImg k (ε v) = ε m₂) := by
    intro k hk v hv hv1
    have h1 := hε3 (u33GenPG k.val) v (horb v hv1)
    rw [vHom_gen] at h1
    rcases hinv _ hk v hv hv1 with h | h | h
    · left
      rw [← h1, h, hεz]
    · right; left
      rw [← h1, h]
    · right; right
      rw [← h1, h]
  rcases u33Data.lattice Y₁ hY₁T with h | h | h | h
  · exact absurd h hY₁1
  ·
    exfalso
    apply fl_noPair (ε m₁) (ε m₂) hp0 hq0 hpq
    intro i hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    have hik : i ≠ 4 := by rcases hi with rfl | rfl | rfl | rfl <;> decide
    have hgA : u33GenPG i.val ∈ Y₁ := by rw [h]; exact gen_mem_A i hik
    have hgz : φ (u33GenPG i.val) z = z := by
      have : u33GenPG i.val ∈ stabSub φ z := by rw [hstab]; exact gen_mem_A i hik
      exact this
    have hgV : ∀ v ∈ V, φ (u33GenPG i.val) v ∈ V := hV _ hgA
    have hpt : ∀ v, v ∈ V → v ≠ 1 → v ≠ z →
        (vImg i (ε v) = ε m₁ ∨ vImg i (ε v) = ε m₂) := by
      intro v hv hv1 hvz
      have h1 := hε3 (u33GenPG i.val) v (horb v hv1)
      rw [vHom_gen] at h1
      rcases hinv _ hgV v hv hv1 with h' | h' | h'
      · exact absurd ((φ _).injective (h'.trans hgz.symm)) hvz
      · left; rw [← h1, h']
      · right; rw [← h1, h']
    exact ⟨hpt m₁ hm₁V hm₁1 hm₁z, hpt m₂ hm₂V hm₂1 hm₂z⟩
  ·
    have hlab : (ε m₁ = 37 ∧ ε m₂ = 43) ∨ (ε m₁ = 43 ∧ ε m₂ = 37) := by
      apply fl_line_exact (ε m₁) (ε m₂) hp0 hq0 hpq
      intro i hi
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      have hik : i ≠ 3 := by rcases hi with rfl | rfl | rfl | rfl <;> decide
      have hgB : u33GenPG i.val ∈ Y₁ := by rw [h]; exact gen_mem_B i hik
      have hgV : ∀ v ∈ V, φ (u33GenPG i.val) v ∈ V := hV _ hgB
      refine ⟨?_, hone i hgV m₁ hm₁V hm₁1, hone i hgV m₂ hm₂V hm₂1⟩
      have := hone i hgV z hzV hz
      rwa [hεz] at this
    rcases u33Data.lattice Y₂ hY₂T with h' | h' | h' | h'
    · exact absurd h' hY₂1
    · exact ⟨h, h', ε, m₁, m₂, hε1, hε2, hε3, horb, hm₁V, hm₂V, hm₁1, hm₂1, hm₁z, hm₂z, hm12, hVcases,
        hlab⟩
    · exact absurd (h.trans h'.symm) hY
    · exact absurd h' hY₂2
  · exact absurd h hY₁2

end CFSG.Quasithin.ModD
