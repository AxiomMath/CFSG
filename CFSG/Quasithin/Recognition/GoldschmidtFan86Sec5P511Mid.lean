module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P511Conj
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P51b

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Line

theorem stab_le_closure_two_edges (F : FanTree Γ G) (ℓ : Line Γ) (i : ℤ) :
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

end Line

theorem even_of_core_two (F : FanTree Γ G) (T : Track Γ G) {z : G} {a tL tR : ℤ}
    (hcore : T.line.IsCoreFix z a (a + 2) tL tR) {f : G}
    (hf : IsReflection T.line (a + 1) f) : (tR - tL) % 2 = 0 := by
  obtain ⟨-, hc, -, -⟩ := (T.line.isCore_iff).1 hcore.core
  have hca := hc a le_rfl (by omega)
  have hca1 := hc (a + 1) (by omega) (by omega)
  have hle : Subgroup.closure ((T.line.edgeStab (G := G) a : Set G) ∪
      (T.line.edgeStab (G := G) (a + 1) : Set G)) ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.closure_le]
    rintro g (hg | hg)
    · exact Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff.1 hh]
        exact (hca.2 g hg).symm
    · exact Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff.1 hh]
        exact (hca1.2 g hg).symm
  have hfz : f * z = z * f := by
    have := Subgroup.mem_centralizer_iff.1
      (hle (T.line.stab_le_closure_two_edges F a (MulAction.mem_stabilizer_iff.2 hf.fixes))) z
      (Set.mem_singleton z)
    exact this.symm
  have hfv : ∀ j, f • T.line.vert j = T.line.vert (2 * (a + 1) - j) := fun j => by
    have := hf.2 (j - (a + 1))
    rwa [show a + 1 + (j - (a + 1)) = j by ring, show a + 1 - (j - (a + 1)) = 2 * (a + 1) - j
      by ring] at this
  have hsym : ∀ j, j ∈ T.line.fixIdx z → 2 * (a + 1) - j ∈ T.line.fixIdx z := fun j hj => by
    show z • T.line.vert (2 * (a + 1) - j) = T.line.vert (2 * (a + 1) - j)
    rw [← hfv j, ← mul_smul, ← hfz, mul_smul, hj, hfv]
  have haL := (hcore.fix a).1 ((T.line.mem_edgeStab_iff).1 hca.1).1
  have hLR : tL ≤ tR := by omega
  have h1 := (hcore.fix _).1 (hsym tL ((hcore.fix tL).2 ⟨le_rfl, hLR⟩))
  have h2 := (hcore.fix _).1 (hsym tR ((hcore.fix tR).2 ⟨hLR, le_rfl⟩))
  omega

end CFSG.Quasithin.Fan86
