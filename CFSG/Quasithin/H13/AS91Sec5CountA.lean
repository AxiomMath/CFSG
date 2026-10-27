module

public import CFSG.Quasithin.H13.AS91Sec5KerFacts
public import CFSG.Quasithin.H13.AS91Sec5Stmt54
public import CFSG.Quasithin.H13.AS91Sec7Smul

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94
open scoped Pointwise

theorem ncard_eq_zero_two_four {α : Type*} {T A : Set α} (hT : T.ncard = 4) (hAT : A ⊆ T)
    (h1 : ∀ p ∈ A, ∃ q ∈ A, q ≠ p) (h2 : ∀ p ∈ T \ A, ∃ q ∈ T \ A, q ≠ p) :
    A.ncard = 0 ∨ A.ncard = 2 ∨ A.ncard = 4 := by
  have hTfin : T.Finite := Set.finite_of_ncard_ne_zero (by omega)
  have hsum := Set.ncard_diff_add_ncard_of_subset hAT hTfin
  have hA1 : A.ncard ≠ 1 := by
    intro h
    obtain ⟨a, rfl⟩ := Set.ncard_eq_one.1 h
    obtain ⟨q, hq, hqa⟩ := h1 a (Set.mem_singleton a)
    exact hqa hq
  have hB1 : (T \ A).ncard ≠ 1 := by
    intro h
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h
    obtain ⟨q, hq, hqa⟩ := h2 a (by rw [ha]; exact Set.mem_singleton a)
    rw [ha] at hq
    exact hqa hq
  omega

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

@[expose] def Aset (y : G ⧸ c.G1) (k : G ⧸ c.G2) : Set (G ⧸ c.G1) :=
  {a | c.OnL a k ∧ a ≠ c.x0 ∧ c.Delta.Adj y a}

theorem mem_Aset {y a : G ⧸ c.G1} {k : G ⧸ c.G2} :
    a ∈ c.Aset y k ↔ c.OnL a k ∧ a ≠ c.x0 ∧ c.Delta.Adj y a :=
  Iff.rfl

theorem smul_mem_Aset {g : G} (hx : g • c.x0 = c.x0) {y : G ⧸ c.G1} (hy : g • y = y)
    {k k' : G ⧸ c.G2} (hk : g • k = k') {a : G ⧸ c.G1} :
    g • a ∈ c.Aset y k' ↔ a ∈ c.Aset y k := by
  rw [mem_Aset, mem_Aset, ← hk, c.onL_smul_iff g]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · constructor
    · intro h h'
      exact h (by rw [h', hx])
    · intro h h'
      exact h (smul_left_cancel g (h'.trans hx.symm))
  · have h := c.adj_smul_iff g (a := y) (b := a)
    rwa [hy] at h

theorem ncard_Aset_eq {g : G} (hx : g • c.x0 = c.x0) {y : G ⧸ c.G1} (hy : g • y = y)
    {k k' : G ⧸ c.G2} (hk : g • k = k') : (c.Aset y k').ncard = (c.Aset y k).ncard := by
  have hset : c.Aset y k' = (g • ·) '' c.Aset y k := by
    ext a
    constructor
    · intro ha
      refine ⟨g⁻¹ • a, ?_, smul_inv_smul g a⟩
      rw [← c.smul_mem_Aset hx hy hk, smul_inv_smul]
      exact ha
    · rintro ⟨a', ha', rfl⟩
      exact (c.smul_mem_Aset hx hy hk).2 ha'
  rw [hset, Set.ncard_image_of_injective _ (MulAction.injective g)]

theorem smul_mem_Aset_Eker {e : G} (he : e ∈ c.Eker c.l0) {y : G ⧸ c.G1} (hy : y ∈ c.ptsL)
    {k : G ⧸ c.G2} (hk : c.OnL c.x0 k) {a : G ⧸ c.G1} :
    e • a ∈ c.Aset y k ↔ a ∈ c.Aset y k :=
  c.smul_mem_Aset (c.smul_x0_of_mem (c.E_le_G1 he.1)) (he.2 y hy) (c.E_smul_line hk he.1)

theorem ncard_onL_ne {k : G ⧸ c.G2} (hk : c.OnL c.x0 k) :
    ({a | c.OnL a k} \ {c.x0}).ncard = 4 := by
  have hx : c.x0 ∈ {a | c.OnL a k} := hk
  rw [Set.ncard_diff_singleton_of_mem hx, c.ncard_onL k]

variable {c}

theorem ncard_Aset_delta_one (hK : c.KerFacts) {y : G ⧸ c.G1} (hy : y ∈ c.ptsL)
    {k : G ⧸ c.G2} (hk : k ∈ c.deltaAt 1 c.x0 c.l0) :
    (c.Aset y k).ncard = 0 ∨ (c.Aset y k).ncard = 2 ∨ (c.Aset y k).ncard = 4 := by
  have hl0 : c.OnL c.x0 c.l0 := cInc_mk c.G1 c.G2 1
  have hkx : c.OnL c.x0 k := c.onL_of_mem_deltaAt hk
  refine ncard_eq_zero_two_four (T := {a | c.OnL a k} \ {c.x0}) (c.ncard_onL_ne hkx)
    (fun a ha => ⟨ha.1, ha.2.1⟩) ?_ ?_
  · intro p hp
    obtain ⟨q, -, -, hqp, ⟨e, he, hep⟩, -⟩ := hK.orbit_one hl0 hkx hk hp.1 hp.2.1
    refine ⟨q, ?_, hqp⟩
    rw [← hep]
    exact (c.smul_mem_Aset_Eker he hy hkx).2 hp
  · intro p hp
    obtain ⟨q, hqk, hqx, hqp, ⟨e, he, hep⟩, -⟩ := hK.orbit_one hl0 hkx hk hp.1.1 hp.1.2
    refine ⟨q, ⟨⟨hqk, hqx⟩, fun hqA => hp.2 ?_⟩, hqp⟩
    rw [← hep] at hqA
    exact (c.smul_mem_Aset_Eker he hy hkx).1 hqA

theorem ncard_Aset_delta_two (hK : c.KerFacts) {y : G ⧸ c.G1} (hy : y ∈ c.ptsL)
    {k : G ⧸ c.G2} (hk : k ∈ c.deltaAt 2 c.x0 c.l0) :
    (c.Aset y k).ncard = 0 ∨ (c.Aset y k).ncard = 4 := by
  have hl0 : c.OnL c.x0 c.l0 := cInc_mk c.G1 c.G2 1
  have hkx : c.OnL c.x0 k := c.onL_of_mem_deltaAt hk
  by_cases hne : (c.Aset y k).Nonempty
  · right
    obtain ⟨p, hp⟩ := hne
    have hsub : c.Aset y k ⊆ {a | c.OnL a k} \ {c.x0} := fun a ha => ⟨ha.1, ha.2.1⟩
    have hsup : {a | c.OnL a k} \ {c.x0} ⊆ c.Aset y k := by
      rintro q ⟨hq, hqx⟩
      obtain ⟨e, he, hep⟩ := hK.smul_two hl0 hkx (Or.inl hk) hp.1 hp.2.1 hq hqx
      rw [← hep]
      exact (c.smul_mem_Aset_Eker he hy hkx).2 hp
    rw [Set.Subset.antisymm hsub hsup]
    exact c.ncard_onL_ne hkx
  · left
    rw [Set.not_nonempty_iff_eq_empty.1 hne]
    exact Set.ncard_empty _

end Loc49

namespace ResM24

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (ρ : ResM24 c)

include ρ in
theorem ncard_Aset_delta (i : Fin 5) {y : G ⧸ c.G1} (hy : y ∈ c.ptsL) (hyx : y ≠ c.x0)
    {k k' : G ⧸ c.G2} (hk : k ∈ c.delta i) (hk' : k' ∈ c.delta i) :
    (c.Aset y k).ncard = (c.Aset y k').ncard := by
  obtain ⟨h, ⟨hh1, hh2⟩, hhk⟩ := ρ.exists_smul_eq_of_mem_delta hk hk'
  have hhx : h • c.x0 = c.x0 := c.smul_x0_of_mem hh1
  have hhl : h • c.l0 = c.l0 := by
    have : h ∈ stabilizer G c.l0 := by
      rw [show stabilizer G c.l0 = c.G2 from stabilizer_mk_one c.G2]
      exact hh2
    exact MulAction.mem_stabilizer_iff.1 this
  have hy1 : h • y ∈ c.ptsL := by
    have := (c.onL_smul_iff h (a := y) (m := c.l0)).2 hy
    rwa [hhl] at this
  have hy1x : h • y ≠ c.x0 := by
    intro h'
    exact hyx (smul_left_cancel h (h'.trans hhx.symm))
  obtain ⟨e, he, hey⟩ := c.E_transitive hy1 hy hy1x hyx
  have hk'x : c.OnL c.x0 k' := hk'.1.symm'
  refine (c.ncard_Aset_eq (g := e * h) ?_ ?_ ?_).symm
  · rw [mul_smul, hhx, c.smul_x0_of_mem (c.E_le_G1 he)]
  · rw [mul_smul, hey]
  · rw [mul_smul, hhk, c.E_smul_line hk'x he]

end ResM24

end CFSG.Quasithin.H13.AS91
