module

public import CFSG.Quasithin.H13.AS91Sec5Stmt54Defs
public import CFSG.Quasithin.H13.AS91Sec7Inc
public import CFSG.Quasithin.H13.AS91Sec7Delta

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction
open scoped Pointwise
open CFSG.ASVolI.ChH (IsTrio IsSextet M24g S24)

namespace ResM24

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (ρ : ResM24 c)

theorem exists_smul_l0_eq {t : Finset (Finset (Fin 24))} (ht : IsTrio t) :
    ∃ σ ∈ M24g, σ • ρ.l₀ = t := by
  obtain ⟨a, ha, haT⟩ := M24G.trio_transitive ρ.isTrio_l₀
  obtain ⟨b, hb, hbT⟩ := M24G.trio_transitive ht
  exact ⟨b⁻¹ * a, mul_mem (inv_mem hb) ha, by rw [mul_smul, haT, ← hbT, inv_smul_smul]⟩

theorem trio_image_delta (i : Fin 5) :
    ρ.trio '' c.delta i = {k | IsTrio k ∧ M24G.Delta ρ.l₀ k i} := by
  ext k
  constructor
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨hn1, hn2⟩ := (ρ.mem_delta_iff i).1 hn
    exact ⟨ρ.isTrio_trio hn1, hn2⟩
  · rintro ⟨hk, hki⟩
    obtain ⟨σ, hσ, hσk⟩ := ρ.exists_smul_l0_eq hk
    obtain ⟨m, hm, hmk⟩ := ρ.exists_trio_eq hσ
    refine ⟨m, (ρ.mem_delta_iff i).2 ⟨hm, ?_⟩, hmk.trans hσk⟩
    rw [hmk, hσk]
    exact hki

theorem exists_mem_delta_trio {i : Fin 5} {t : Finset (Finset (Fin 24))} (ht : IsTrio t)
    (hti : M24G.Delta ρ.l₀ t i) : ∃ m ∈ c.delta i, ρ.trio m = t := by
  have hmem : t ∈ ρ.trio '' c.delta i := by
    rw [ρ.trio_image_delta i]
    exact ⟨ht, hti⟩
  obtain ⟨m, hm, hmt⟩ := hmem
  exact ⟨m, hm, hmt⟩

theorem exists_trio_delta (i : Fin 5) : ∃ t, IsTrio t ∧ M24G.Delta ρ.l₀ t i := by
  have hpos : ∀ j : Fin 5, (![1, 42, 56, 1008, 2688] : Fin 5 → ℕ) j ≠ 0 := by decide
  have hne : ({k | IsTrio k ∧ M24G.Delta ρ.l₀ k i} : Set (Finset (Finset (Fin 24)))).ncard ≠ 0 := by
    rw [M24G.ncard_delta ρ.isTrio_l₀ i]
    exact hpos i
  obtain ⟨t, ht⟩ := Set.nonempty_of_ncard_ne_zero hne
  exact ⟨t, ht⟩

include ρ in
theorem ncard_delta_eq (i : Fin 5) :
    (c.delta i).ncard = (![1, 42, 56, 1008, 2688] : Fin 5 → ℕ) i := by
  have hinj : Set.InjOn ρ.trio (c.delta i) := by
    intro n hn n' hn' h
    exact ρ.trio_injOn ((ρ.mem_delta_iff i).1 hn).1 ((ρ.mem_delta_iff i).1 hn').1 h
  rw [← hinj.ncard_image, ρ.trio_image_delta i, M24G.ncard_delta ρ.isTrio_l₀ i]

include ρ in
theorem exists_smul_eq_of_mem_delta {i : Fin 5} {m n : G ⧸ c.G2} (hm : m ∈ c.delta i)
    (hn : n ∈ c.delta i) : ∃ g ∈ c.G1 ⊓ c.G2, g • m = n := by
  obtain ⟨hm1, hm2⟩ := (ρ.mem_delta_iff i).1 hm
  obtain ⟨hn1, hn2⟩ := (ρ.mem_delta_iff i).1 hn
  obtain ⟨σ, hσ, hσl, hσt⟩ := M24G.delta_orbit ρ.isTrio_l₀ (ρ.isTrio_trio hm1)
    (ρ.isTrio_trio hn1) hm2 hn2
  obtain ⟨h, rfl⟩ := ρ.exists_φ_eq hσ
  have h2 : (h : G) ∈ c.G2 := (ρ.stab₂ h).2 hσl
  refine ⟨(h : G), Subgroup.mem_inf.2 ⟨h.2, h2⟩, ?_⟩
  refine ρ.trio_injOn ((c.cInc_x0_smul h.2).2 hm1) hn1 ?_
  rw [ρ.trio_smul_line h hm1]
  exact hσt

include ρ in
theorem exists_rep_delta (i : Fin 5) :
    ∃ m ∈ c.delta i, ∀ n ∈ c.delta i, ∃ g ∈ c.G1 ⊓ c.G2, g • m = n := by
  obtain ⟨t, ht1, ht2⟩ := ρ.exists_trio_delta i
  obtain ⟨m, hm, -⟩ := ρ.exists_mem_delta_trio ht1 ht2
  exact ⟨m, hm, fun _ hn => ρ.exists_smul_eq_of_mem_delta hm hn⟩

include ρ in
theorem exists_mem_delta_of_mem {m : G ⧸ c.G2} (hm : m ∈ c.lnsX) : ∃ i, m ∈ c.delta i := by
  have hx : CInc c.G1 c.G2 c.x0 m := (mem_objOf.1 hm).symm'
  obtain ⟨j, hj, -⟩ := M24G.delta_existsUnique ρ.isTrio_l₀ (ρ.isTrio_trio hx)
  exact ⟨j, (ρ.mem_delta_iff j).2 ⟨hx, hj⟩⟩

include ρ in
theorem delta_zero_eq : c.delta 0 = {c.l0} := by
  have hl0 : CInc c.G1 c.G2 c.x0 c.l0 := by simpa using c.cInc_x0_smul_l0 1
  ext n
  rw [Set.mem_singleton_iff]
  constructor
  · intro hn
    obtain ⟨hn1, hn2⟩ := (ρ.mem_delta_iff 0).1 hn
    have h0 : ρ.trio n = ρ.l₀ := hn2
    exact ρ.trio_injOn hn1 hl0 (h0.trans ρ.trio_l0.symm)
  · rintro rfl
    exact (ρ.mem_delta_iff 0).2 ⟨hl0, ρ.trio_l0⟩

theorem coplanar_symm_trio {l k : Finset (Finset (Fin 24))} :
    M24G.Coplanar l k ↔ M24G.Coplanar k l := by
  unfold M24G.Coplanar
  constructor
  · rintro ⟨S, hS, h1, h2⟩
    exact ⟨S, hS, h2, h1⟩
  · rintro ⟨S, hS, h1, h2⟩
    exact ⟨S, hS, h2, h1⟩

include ρ in
theorem mem_delta_le_two_iff {m : G ⧸ c.G2} (hm : CInc c.G1 c.G2 c.x0 m) :
    m ∈ c.delta 0 ∪ c.delta 1 ∪ c.delta 2 ↔
      ∃ p, CInc c.G2 c.G3 m p ∧ CInc c.G2 c.G3 c.l0 p := by
  have hl0 : CInc c.G1 c.G2 c.x0 c.l0 := by simpa using c.cInc_x0_smul_l0 1
  have hd : ∀ i : Fin 5, m ∈ c.delta i ↔ M24G.Delta ρ.l₀ (ρ.trio m) i := fun i =>
    ⟨fun h => ((ρ.mem_delta_iff i).1 h).2, fun h => (ρ.mem_delta_iff i).2 ⟨hm, h⟩⟩
  have hc : (∃ p, CInc c.G2 c.G3 m p ∧ CInc c.G2 c.G3 c.l0 p) ↔
      M24G.Coplanar ρ.l₀ (ρ.trio m) := by
    have h := ρ.coplanar_iff hm hl0
    rw [ρ.trio_l0] at h
    exact h.trans coplanar_symm_trio
  rw [Set.mem_union, Set.mem_union, hd 0, hd 1, hd 2, or_assoc,
    ← M24G.coplanar_iff_delta ρ.isTrio_l₀ (ρ.isTrio_trio hm)]
  exact hc.symm

include ρ in
theorem delta_le_two_eq :
    c.delta 0 ∪ c.delta 1 ∪ c.delta 2 =
      {m | m ∈ c.lnsX ∧ ∃ p, CInc c.G2 c.G3 m p ∧ CInc c.G2 c.G3 c.l0 p} := by
  ext m
  constructor
  · intro hm
    have hx : CInc c.G1 c.G2 c.x0 m := by
      rcases hm with (h | h) | h
      · exact ((ρ.mem_delta_iff _).1 h).1
      · exact ((ρ.mem_delta_iff _).1 h).1
      · exact ((ρ.mem_delta_iff _).1 h).1
    exact ⟨mem_objOf.2 hx.symm', (ρ.mem_delta_le_two_iff hx).1 hm⟩
  · rintro ⟨hl, hp⟩
    have hx : CInc c.G1 c.G2 c.x0 m := (mem_objOf.1 hl).symm'
    exact (ρ.mem_delta_le_two_iff hx).2 hp

include ρ in
theorem ncard_delta_one : (c.delta 1).ncard = 42 := (ρ.ncard_delta_eq 1).trans rfl

include ρ in
theorem ncard_delta_two : (c.delta 2).ncard = 56 := (ρ.ncard_delta_eq 2).trans rfl

include ρ in
theorem ncard_delta_three : (c.delta 3).ncard = 1008 := (ρ.ncard_delta_eq 3).trans rfl

include ρ in
theorem ncard_delta_four : (c.delta 4).ncard = 2688 := (ρ.ncard_delta_eq 4).trans rfl

end ResM24


theorem stmt5_4_of (hres : ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z)
      (c : Loc49 G z), Nonempty (ResM24 c))
    (h34 : Stmt5_4_34) (h6 : Stmt5_4_6) : Stmt5_4 := by
  intro G _ _ z hz c y hy hyx
  obtain ⟨ρ⟩ := hres G z hz c
  obtain ⟨h3, h4⟩ := h34 G z hz c y hy hyx
  exact ⟨fun _ hm => ρ.exists_mem_delta_of_mem hm, fun i => ρ.exists_rep_delta i,
    ρ.delta_zero_eq, ρ.delta_le_two_eq, ⟨ρ.ncard_delta_one, h3⟩, ⟨ρ.ncard_delta_two, h4⟩,
    ⟨ρ.ncard_delta_three, ρ.ncard_delta_four⟩, h6 G z hz c y hy hyx⟩

end CFSG.Quasithin.H13.AS91
