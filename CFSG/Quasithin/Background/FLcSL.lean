module

public import CFSG.Quasithin.Background.FLcModel
public import CFSG.Quasithin.Background.FLcNat
public import CFSG.GH74.Exceptional.LinearFourTwo

public section

namespace CFSG.Quasithin.FLc

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem nonempty_equiv_SLt_of_isPSL {X : Type} [Group X] {n : ℕ}
    (h : CFSG.Quasithin.IsPSL n 2 1 X) : Nonempty (X ≃* SLt n) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hK
  exact ⟨((e.trans (CFSG.GH74.Exceptional.statedProjStatedSLEquivOfCardTwo hK2 n)).trans
    (CFSG.GH74.Exceptional.glEquivZModTwoOfCardTwo hK2 n)).trans (slEquivGLt n).symm⟩

theorem normalizer_eq_of_sylow_equiv {H : Type} [Group H] [Finite H] {n : ℕ} (hn : 1 ≤ n)
    (e : H ≃* SLt n) (P : Sylow 2 H) :
    Subgroup.normalizer ((P : Subgroup H) : Set H) = (P : Subgroup H) := by
  let Q : Sylow 2 (SLt n) := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective P
  have hQ : (Q : Subgroup (SLt n)) = (P : Subgroup H).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective P
  obtain ⟨g, hg⟩ := exists_conj_eq_unitriangular hn Q
  have hN : Subgroup.normalizer ((Q : Subgroup (SLt n)) : Set (SLt n)) = Q := by
    rw [hg, normalizer_map_conj, normalizer_unitriangular,
      CFSG.LieType.SteinbergBR.BinaryLinear.upperTriangular_eq_unitriangular
        (Nat.card_zmod 2)]
  have h1 := Subgroup.map_equiv_normalizer_eq (P : Subgroup H) e
  rw [← hQ, hN, hQ] at h1
  exact Subgroup.map_injective e.injective h1

theorem normalizer_inf_le_of_isPSL {G : Type} [Group G] [Finite G] {L S' : Subgroup G} {n : ℕ}
    (hn : 1 ≤ n) (h : CFSG.Quasithin.IsPSL n 2 1 (↥L ⧸ CFSG.pCore 2 ↥L))
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S' L) :
    L ⊓ Subgroup.normalizer (S' : Set G) ≤ S' := by
  obtain ⟨e⟩ := nonempty_equiv_SLt_of_isPSL h
  obtain ⟨P, hP⟩ := exists_sylow_of_isSylowTwoOf hS
  have hKP : CFSG.pCore 2 ↥L ≤ (P : Subgroup ↥L) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).le_sylow_of_normal P
  let π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let P' : Sylow 2 (↥L ⧸ CFSG.pCore 2 ↥L) := Sylow.mapSurjective (f := π) hπ P
  have hP' : (P' : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) = (P : Subgroup ↥L).map π :=
    Sylow.coe_mapSurjective (f := π) hπ P
  have hker : π.ker ≤ (P : Subgroup ↥L) := by
    rw [QuotientGroup.ker_mk']
    exact hKP
  have hmemP : ∀ y : ↥L, π y ∈ (P' : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) ↔
      y ∈ (P : Subgroup ↥L) := fun y => by
    rw [hP']
    have := Subgroup.comap_map_eq_self hker
    constructor
    · intro hy
      have h2 : y ∈ Subgroup.comap π (Subgroup.map π (P : Subgroup ↥L)) := hy
      rwa [this] at h2
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hN := normalizer_eq_of_sylow_equiv hn e P'
  intro x hx
  have hxL : x ∈ L := hx.1
  have hxN : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.normalizer ((P : Subgroup ↥L) : Set ↥L) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hyx := Subgroup.mem_normalizer_iff.1 hx.2 (y : G)
    rw [hP, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact hyx
  have hxN' : π ⟨x, hxL⟩ ∈ Subgroup.normalizer ((P' : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) :
      Set (↥L ⧸ CFSG.pCore 2 ↥L)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro yb
    obtain ⟨y, rfl⟩ := hπ yb
    have h1 := Subgroup.mem_normalizer_iff.1 hxN y
    rw [hmemP, ← map_inv, ← map_mul, ← map_mul, hmemP]
    exact h1
  rw [hN] at hxN'
  have h2 := (hmemP ⟨x, hxL⟩).1 hxN'
  rw [hP, Subgroup.mem_subgroupOf] at h2
  exact h2

end CFSG.Quasithin.FLc
