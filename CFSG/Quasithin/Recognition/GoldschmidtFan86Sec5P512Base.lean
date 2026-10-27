module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62DCin
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Lbl0
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P51b
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5Stmt

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P512

theorem coreSat2 {F : FanTree Γ G} (h510 : Fan510 F) (h511 : Fan511 F) (h40 : Fan40 F)
    {T : Track Γ G} (hT : InXi T) {z : G} (hz : z ∈ T.line.ZZ) (hz1 : z ≠ 1) :
    T.line.CoreSat z fun a b tL tR => b - a = 2 ∧ tR - b = a - tL := by
  obtain ⟨i, hi⟩ := hT
  by_cases h1 : i = 1
  · subst h1
    obtain ⟨hex, hall⟩ := h510 h40 T hi z hz hz1
    exact ⟨hex, fun a b tL tR hf => ⟨(hall a b tL tR hf).1, (hall a b tL tR hf).2.1⟩⟩
  · exact h511 h40 i T h1 hi z hz hz1

theorem cinv_conj {v : V} {z : G} (hz : z ∈ Cinv G v) (g : G) :
    g * z * g⁻¹ ∈ Cinv G (g • v) := by
  have := P514.Lb_cinv hz ⟨g, rfl⟩
  rwa [P514.Lb_eq hz (g := g) rfl] at this

theorem cinv_cen_left (F : FanTree Γ G) (ℓ : Line Γ) {i : ℤ} {z : G}
    (hz : z ∈ Cinv G (ℓ.vert i)) : z ∈ Cen (ℓ.edgeStab (G := G) i : Set G) := by
  have hK := P62.cinv_mem_nbrStab F hz
  refine ⟨⟨hz.2.2.1, MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hK _ (ℓ.adj i))⟩,
    fun h hh => hz.2.2.2 h hh.1⟩

theorem cinv_cen_right (F : FanTree Γ G) (ℓ : Line Γ) {i : ℤ} {z : G}
    (hz : z ∈ Cinv G (ℓ.vert (i + 1))) : z ∈ Cen (ℓ.edgeStab (G := G) i : Set G) := by
  have hK := P62.cinv_mem_nbrStab F hz
  refine ⟨⟨MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hK _ (ℓ.adj i).symm), hz.2.2.1⟩,
    fun h hh => hz.2.2.2 h hh.2⟩

theorem stab_le_closure_edges (F : FanTree Γ G) (ℓ : Line Γ) (i : ℤ) :
    MulAction.stabilizer G (ℓ.vert (i + 1)) ≤
      Subgroup.closure ((ℓ.edgeStab (G := G) i : Set G) ∪
        (ℓ.edgeStab (G := G) (i + 1) : Set G)) := by
  set M := Subgroup.closure ((ℓ.edgeStab (G := G) i : Set G) ∪
    (ℓ.edgeStab (G := G) (i + 1) : Set G)) with hM
  have hEi : ℓ.edgeStab (G := G) i ≤ M := fun g hg => Subgroup.subset_closure (Or.inl hg)
  have hEi1 : ℓ.edgeStab (G := G) (i + 1) ≤ M := fun g hg => Subgroup.subset_closure (Or.inr hg)
  have hu : Γ.Adj (ℓ.vert (i + 1)) (ℓ.vert i) := (ℓ.adj i).symm
  have hw : Γ.Adj (ℓ.vert (i + 1)) (ℓ.vert (i + 2)) := Line.adj_add_two ℓ i
  have huw : ℓ.vert i ≠ ℓ.vert (i + 2) := ℓ.nb i
  obtain ⟨g₁, hg₁, hg₁u, c₁, hc₁, hg₁c⟩ := F.frobenius_nonreg _ _ hu
  obtain ⟨g₂, hg₂, hg₂w, c₂, hc₂, hg₂c⟩ := F.frobenius_nonreg _ _ hw
  have h₁w : g₁ • ℓ.vert (i + 2) ≠ ℓ.vert (i + 2) := fun h =>
    hg₁c (F.frobenius_two _ _ _ hu hw huw g₁ hg₁ hg₁u h c₁ hc₁)
  have h₂u : g₂ • ℓ.vert i ≠ ℓ.vert i := fun h =>
    hg₂c (F.frobenius_two _ _ _ hw hu huw.symm g₂ hg₂ hg₂w h c₂ hc₂)
  have hg₁M : g₁ ∈ M := hEi ⟨MulAction.mem_stabilizer_iff.2 hg₁u, hg₁⟩
  have hg₂M : g₂ ∈ M := hEi1 ⟨hg₂, MulAction.mem_stabilizer_iff.2 (by
    rw [show i + 1 + 1 = i + 2 by ring]; exact hg₂w)⟩
  intro h hh
  obtain ⟨m, hm, hmα, hmu⟩ := F.transitive_of_two_fixers hu hw huw hg₁ hg₂ hg₁u h₁w hg₂w h₂u hu
    (F.adj_smul_of_mem_stabilizer hh hu)
  have hmM : m ∈ M := by
    have : Subgroup.closure ({g₁, g₂} : Set G) ≤ M := by
      rw [Subgroup.closure_le]
      rintro g (rfl | rfl)
      · exact hg₁M
      · exact hg₂M
    exact this hm
  have hmh : m⁻¹ * h ∈ ℓ.edgeStab (G := G) i :=
    ⟨MulAction.mem_stabilizer_iff.2 (by rw [mul_smul, ← hmu, inv_smul_smul]),
      MulAction.mem_stabilizer_iff.2 (by
        rw [mul_smul, MulAction.mem_stabilizer_iff.1 hh, inv_smul_eq_iff]
        exact hmα.symm)⟩
  have : m * (m⁻¹ * h) ∈ M := M.mul_mem hmM (hEi hmh)
  simpa using this

end P512

end CFSG.Quasithin.Fan86
