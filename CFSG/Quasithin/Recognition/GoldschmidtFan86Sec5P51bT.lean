module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PSing
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PEdge

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Line

variable (ℓ : Line Γ)

theorem exists_t_left (F : FanTree Γ G) (h40 : Fan40 F) (c : ℤ) :
    ∃ t ∈ nbrStab Γ G (ℓ.vert (c + 2)), t • ℓ.vert c = ℓ.vert c ∧
      t • ℓ.vert (c + 1) = ℓ.vert (c + 1) ∧ t ∉ nbrStab Γ G (ℓ.vert c) := by
  obtain ⟨g, hfix, hmove⟩ := ℓ.exists_fixer_left' c 3 0 3
    (lineNSL_of_fan40 h40 ℓ (by norm_num) (by norm_num) c)
  have hf : ∀ m : ℤ, c ≤ m → m ≤ c + 3 → g • ℓ.vert m = ℓ.vert m := fun m h1 h2 =>
    hfix m (by simpa using h1) (by simpa using h2)
  refine ⟨g, ℓ.mem_nbrStab_of_fix F (hf _ (by omega) (by omega)) (hf _ (by omega) (by omega))
    (hf _ (by omega) (by omega)), hf c le_rfl (by omega), hf (c + 1) (by omega) (by omega),
    fun hK => hmove ?_⟩
  simpa using mem_nbrStab.1 hK _ (ℓ.adj_pred c)

theorem exists_t_right (F : FanTree Γ G) (h40 : Fan40 F) (d : ℤ) :
    ∃ t ∈ nbrStab Γ G (ℓ.vert (d - 2)), t • ℓ.vert (d - 1) = ℓ.vert (d - 1) ∧
      t • ℓ.vert d = ℓ.vert d ∧ t ∉ nbrStab Γ G (ℓ.vert d) := by
  obtain ⟨g, hfix, hmove⟩ := ℓ.exists_fixer_right' (d - 3) 3 0 3 (by norm_num)
    (lineNSR_of_fan40 h40 ℓ (by norm_num) (by norm_num) (d - 3))
  have hf : ∀ m : ℤ, d - 3 ≤ m → m ≤ d → g • ℓ.vert m = ℓ.vert m := fun m h1 h2 =>
    hfix m (by simpa using h1) (by simpa using h2 : m ≤ d - 3 + 3)
  have hmove' : g • ℓ.vert (d + 1) ≠ ℓ.vert (d + 1) := by
    rwa [show d - 3 + ((3 : ℕ) : ℤ) + 1 = d + 1 by push_cast; ring] at hmove
  refine ⟨g, ℓ.mem_nbrStab_of_fix F (hf _ (by omega) (by omega)) (hf _ (by omega) (by omega))
    (hf _ (by omega) (by omega)), hf (d - 1) (by omega) (by omega), hf d (by omega) le_rfl,
    fun hK => hmove' (mem_nbrStab.1 hK _ (ℓ.adj d))⟩

theorem exists_t_mid (F : FanTree Γ G) (h40 : Fan40 F) (c : ℤ) :
    ∃ t ∈ nbrStab Γ G (ℓ.vert c), t • ℓ.vert (c + 1) = ℓ.vert (c + 1) ∧
      t • ℓ.vert (c + 2) = ℓ.vert (c + 2) ∧ t ∉ nbrStab Γ G (ℓ.vert (c + 2)) := by
  obtain ⟨g, hfix, hmove⟩ := ℓ.exists_fixer_right' (c - 1) 3 0 3 (by norm_num)
    (lineNSR_of_fan40 h40 ℓ (by norm_num) (by norm_num) (c - 1))
  have hf : ∀ m : ℤ, c - 1 ≤ m → m ≤ c + 2 → g • ℓ.vert m = ℓ.vert m := fun m h1 h2 =>
    hfix m (by simpa using h1) (by push_cast; omega)
  have hmove' : g • ℓ.vert (c + 2 + 1) ≠ ℓ.vert (c + 2 + 1) := by
    rwa [show c - 1 + ((3 : ℕ) : ℤ) + 1 = c + 2 + 1 by push_cast; ring] at hmove
  refine ⟨g, ℓ.mem_nbrStab_of_fix F (hf _ (by omega) (by omega)) (hf _ (by omega) (by omega))
    (hf _ (by omega) (by omega)), hf (c + 1) (by omega) (by omega),
    hf (c + 2) (by omega) le_rfl, fun hK => hmove' (mem_nbrStab.1 hK _ (ℓ.adj (c + 2)))⟩

theorem edgeStab_le_of_ker (F : FanTree Γ G) (h40 : Fan40 F) {M : Subgroup G} {i : ℤ}
    (h0 : ∀ g ∈ nbrStab Γ G (ℓ.vert i), g ∈ M)
    (h1 : ∀ g ∈ nbrStab Γ G (ℓ.vert (i + 1)), g ∈ M) :
    ∀ g ∈ ℓ.edgeStab (G := G) i, g ∈ M := by
  intro g hg
  have hval : ∀ v, valence Γ v = 3 ∨ valence Γ v = 5 := fun v => F.valence v
  have halt : valence Γ (ℓ.vert i) ≠ valence Γ (ℓ.vert (i + 1)) := F.alternating _ _ (ℓ.adj i)
  have hgi := MulAction.mem_stabilizer_iff.1 hg.1
  have hgj := MulAction.mem_stabilizer_iff.1 hg.2
  by_cases h3 : valence Γ (ℓ.vert (i + 1)) = 3
  · exact F.edge_mem_of_ker h40 (ℓ.adj i) h3 h0 h1 hgi hgj
  · have h3' : valence Γ (ℓ.vert i) = 3 := by
      have := hval (ℓ.vert i)
      have := hval (ℓ.vert (i + 1))
      omega
    exact F.edge_mem_of_ker h40 (ℓ.adj i).symm h3' h1 h0 hgj hgi

end Line

end CFSG.Quasithin.Fan86
