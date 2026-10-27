module

public import CFSG.Quasithin.H13.AS91Sec7Chain
public import CFSG.Quasithin.H13.AS91Sec3Dual
public import CFSG.Quasithin.H13.AS91Sec7Inc

public section

namespace CFSG.Quasithin.H13.AS91.ResM24

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94
open scoped Pointwise
open CFSG.ASVolI.ChH (IsTrio IsSextet M24g S24)

theorem cInc_smul_inv_iff {G : Type} [Group G] {A B : Subgroup G} (g : G) (a : G ⧸ A)
    (b : G ⧸ B) : CInc A B (g • a) b ↔ CInc A B a (g⁻¹ • b) := by
  have h := cInc_smul A B g a (g⁻¹ • b)
  rwa [smul_inv_smul] at h

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (ρ : ResM24 c)

theorem exists_smul_l₀ {t : Finset (Finset (Fin 24))} (ht : IsTrio t) :
    ∃ σ ∈ M24g, σ • ρ.l₀ = t := by
  obtain ⟨a, ha, haT⟩ := M24G.trio_transitive ρ.isTrio_l₀
  obtain ⟨b, hb, hbT⟩ := M24G.trio_transitive ht
  exact ⟨b⁻¹ * a, mul_mem (inv_mem hb) ha, by rw [mul_smul, haT, ← hbT, inv_smul_smul]⟩

theorem isSextet_sext_at {g : G} {x : G ⧸ c.G1} {π : G ⧸ c.G3} (hg : g • c.x0 = x)
    (hπ : c.OnP x π) : IsSextet (ρ.sext (g⁻¹ • π)) := by
  subst hg
  exact ρ.isSextet_sext ((cInc_smul_inv_iff g c.x0 π).1 hπ)

theorem isTrio_trio_at {g : G} {x : G ⧸ c.G1} {n : G ⧸ c.G2} (hg : g • c.x0 = x)
    (hn : c.OnL x n) : IsTrio (ρ.trio (g⁻¹ • n)) := by
  subst hg
  exact ρ.isTrio_trio ((cInc_smul_inv_iff g c.x0 n).1 hn)

theorem eq_of_trio_at {g : G} {x : G ⧸ c.G1} {m n : G ⧸ c.G2} (hg : g • c.x0 = x)
    (hm : c.OnL x m) (hn : c.OnL x n) (h : ρ.trio (g⁻¹ • m) = ρ.trio (g⁻¹ • n)) : m = n := by
  subst hg
  have h' := ρ.trio_injOn ((cInc_smul_inv_iff g c.x0 m).1 hm)
    ((cInc_smul_inv_iff g c.x0 n).1 hn) h
  rw [← smul_inv_smul g m, h', smul_inv_smul]

theorem lnP_iff_trioIn_at {g : G} {x : G ⧸ c.G1} {π : G ⧸ c.G3} {n : G ⧸ c.G2}
    (hg : g • c.x0 = x) (hπ : c.OnP x π) (hn : c.OnL x n) :
    c.LnP n π ↔ M24G.TrioIn (ρ.trio (g⁻¹ • n)) (ρ.sext (g⁻¹ • π)) := by
  subst hg
  have h1 := ρ.cInc_iff_trioIn ((cInc_smul_inv_iff g c.x0 n).1 hn)
    ((cInc_smul_inv_iff g c.x0 π).1 hπ)
  have h2 := cInc_smul c.G2 c.G3 (g⁻¹) n π
  exact h2.symm.trans h1

theorem trio_mem_triosOf {g : G} {x : G ⧸ c.G1} {π : G ⧸ c.G3} {n : G ⧸ c.G2}
    (hg : g • c.x0 = x) (hπ : c.OnP x π) (hn : c.OnL x n) (hnπ : c.LnP n π) :
    ρ.trio (g⁻¹ • n) ∈ M24G.triosOf (ρ.sext (g⁻¹ • π)) :=
  M24G.mem_triosOf.2 ⟨ρ.isTrio_trio_at hg hn, (ρ.lnP_iff_trioIn_at hg hπ hn).1 hnπ⟩

theorem exists_line_of_mem_triosOf {g : G} {x : G ⧸ c.G1} {π : G ⧸ c.G3}
    (hg : g • c.x0 = x) (hπ : c.OnP x π) {t : Finset (Finset (Fin 24))}
    (ht : t ∈ M24G.triosOf (ρ.sext (g⁻¹ • π))) :
    ∃ n, c.OnL x n ∧ c.LnP n π ∧ ρ.trio (g⁻¹ • n) = t := by
  subst hg
  obtain ⟨ht1, ht2⟩ := M24G.mem_triosOf.1 ht
  obtain ⟨σ, hσ, hσt⟩ := ρ.exists_smul_l₀ ht1
  obtain ⟨m, hm, hmt⟩ := ρ.exists_trio_eq hσ
  have hp : CInc c.G1 c.G3 c.x0 (g⁻¹ • π) := (cInc_smul_inv_iff g c.x0 π).1 hπ
  have hmp : CInc c.G2 c.G3 m (g⁻¹ • π) :=
    (ρ.cInc_iff_trioIn hm hp).2 (by rw [hmt, hσt]; exact ht2)
  refine ⟨g • m, (cInc_smul c.G1 c.G2 g c.x0 m).2 hm, (cInc_smul_inv_iff g m π).2 hmp, ?_⟩
  rw [inv_smul_smul, hmt, hσt]

theorem exists_plane_of_trioIn {g : G} {x : G ⧸ c.G1} {n : G ⧸ c.G2} (hg : g • c.x0 = x)
    (hn : c.OnL x n) {U : Finset (Finset (Fin 24))} (hU : IsSextet U)
    (hnU : M24G.TrioIn (ρ.trio (g⁻¹ • n)) U) :
    ∃ π, c.OnP x π ∧ c.LnP n π ∧ ρ.sext (g⁻¹ • π) = U := by
  subst hg
  obtain ⟨a, ha, haU⟩ := M24G.sextet_transitive hU
  obtain ⟨b, hb, hbU⟩ := M24G.sextet_transitive ρ.isSextet_U₀
  obtain ⟨p, hp, hpU⟩ := ρ.exists_sext_eq (σ := a⁻¹ * b) (mul_mem (inv_mem ha) hb)
  have hpU' : ρ.sext p = U := by rw [hpU, mul_smul, hbU, ← haU, inv_smul_smul]
  have hnp : CInc c.G2 c.G3 (g⁻¹ • n) p :=
    (ρ.cInc_iff_trioIn ((cInc_smul_inv_iff g c.x0 n).1 hn) hp).2 (by rw [hpU']; exact hnU)
  refine ⟨g • p, (cInc_smul c.G1 c.G3 g c.x0 p).2 hp, ?_, ?_⟩
  · have h := (cInc_smul c.G2 c.G3 g (g⁻¹ • n) p).2 hnp
    rwa [smul_inv_smul] at h
  · rw [inv_smul_smul]
    exact hpU'

section Delta


theorem mem_deltaAt_one_iff_at {g : G} {x : G ⧸ c.G1} {m n : G ⧸ c.G2} (hg : g • c.x0 = x)
    (hm : c.OnL x m) (hn : c.OnL x n) :
    n ∈ c.deltaAt 1 x m ↔ n ≠ m ∧ ¬ Disjoint (ρ.trio (g⁻¹ • n)) (ρ.trio (g⁻¹ • m)) := by
  rw [ρ.mem_deltaAt_iff 1 hg hm hn]
  change ρ.trio (g⁻¹ • n) ≠ ρ.trio (g⁻¹ • m) ∧
    ¬ Disjoint (ρ.trio (g⁻¹ • n)) (ρ.trio (g⁻¹ • m)) ↔ _
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h1 (by rw [h]), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h1 (ρ.eq_of_trio_at hg hn hm h), h2⟩

theorem mem_deltaAt_two_iff_at {g : G} {x : G ⧸ c.G1} {m n : G ⧸ c.G2} (hg : g • c.x0 = x)
    (hm : c.OnL x m) (hn : c.OnL x n) :
    n ∈ c.deltaAt 2 x m ↔ Disjoint (ρ.trio (g⁻¹ • n)) (ρ.trio (g⁻¹ • m)) ∧ c.CoL m n := by
  rw [ρ.mem_deltaAt_iff 2 hg hm hn]
  change Disjoint (ρ.trio (g⁻¹ • n)) (ρ.trio (g⁻¹ • m)) ∧
    M24G.Coplanar (ρ.trio (g⁻¹ • m)) (ρ.trio (g⁻¹ • n)) ↔ _
  exact and_congr_right fun _ => (ρ.coplanar_iff_at hg hm hn).symm

theorem mem_deltaAt_three_iff_at {g : G} {x : G ⧸ c.G1} {m n : G ⧸ c.G2} (hg : g • c.x0 = x)
    (hm : c.OnL x m) (hn : c.OnL x n) :
    n ∈ c.deltaAt 3 x m ↔ M24G.Delta (ρ.trio (g⁻¹ • m)) (ρ.trio (g⁻¹ • n)) 3 :=
  ρ.mem_deltaAt_iff 3 hg hm hn

end Delta

end CFSG.Quasithin.H13.AS91.ResM24
