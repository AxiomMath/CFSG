module

public import CFSG.Quasithin.H13.AS91Sec5KerFacts
public import CFSG.Quasithin.H13.AS91Sec5PlaneCount
public import CFSG.Quasithin.H13.AS91Sec7FourC

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

private theorem delta_adj_smul_532 (g : G) (a b : G ⧸ c.G1) :
    c.Delta.Adj (g • a) (g • b) ↔ c.Delta.Adj a b :=
  CFSG.Quasithin.GraphAction.adj_smul g a b

theorem inf_stab_le_Epl (h533 : Stmt5_3_3) (hJ : HypJ4 G z) {u : G ⧸ c.G1} {σ : G ⧸ c.G3}
    (hux : u ≠ c.x0) (hnu : ¬ c.Delta.Adj c.x0 u) (huσ : c.OnP u σ) :
    c.E ⊓ stabilizer G u ≤ c.Epl σ := by
  intro e he
  obtain ⟨heE, heu⟩ := Subgroup.mem_inf.mp he
  rw [mem_stabilizer_iff] at heu
  rw [c.mem_Epl]
  refine ⟨heE, fun m hm hmσ => ?_⟩
  have ham : ¬ c.OnL u m := fun hum => hnu (c.adj_of_onL hux.symm hm hum)
  rcases c.stmt5_3_3_at h533 hJ huσ hmσ ham with hall | h3
  · exact absurd (hall c.x0 hm).symm hnu
  ·
    have hN : {b | c.OnL b m ∧ ¬ c.Delta.Adj u b}.ncard = 2 := by
      have hunion : {b | c.OnL b m} = {b | c.OnL b m ∧ c.Delta.Adj u b} ∪
          {b | c.OnL b m ∧ ¬ c.Delta.Adj u b} := by
        ext b
        simp only [Set.mem_setOf_eq, Set.mem_union]
        constructor
        · intro hb
          exact (em (c.Delta.Adj u b)).elim (fun hab => Or.inl ⟨hb, hab⟩)
            (fun hab => Or.inr ⟨hb, hab⟩)
        · rintro (⟨hb, -⟩ | ⟨hb, -⟩) <;> exact hb
      have hdisj : Disjoint {b | c.OnL b m ∧ c.Delta.Adj u b}
          {b | c.OnL b m ∧ ¬ c.Delta.Adj u b} := by
        rw [Set.disjoint_left]
        rintro b ⟨-, h1⟩ ⟨-, h2⟩
        exact h2 h1
      have h5 := c.ncard_onL m
      rw [hunion, Set.ncard_union_eq hdisj, h3] at h5
      omega
    have hx0N : c.x0 ∈ {b | c.OnL b m ∧ ¬ c.Delta.Adj u b} := ⟨hm, fun h => hnu h.symm⟩
    obtain ⟨p, hpset⟩ : ∃ p, {b | c.OnL b m ∧ ¬ c.Delta.Adj u b} \ {c.x0} = {p} :=
      Set.ncard_eq_one.mp (by rw [Set.ncard_diff_singleton_of_mem hx0N, hN])
    have hpN : p ∈ {b | c.OnL b m ∧ ¬ c.Delta.Adj u b} \ {c.x0} := by
      rw [hpset]
      exact Set.mem_singleton p
    have hpx : p ≠ c.x0 := fun h => hpN.2 (Set.mem_singleton_iff.mpr h)
    have hpm : c.OnL p m := hpN.1.1
    have hfixN : ∀ q ∈ {b | c.OnL b m ∧ ¬ c.Delta.Adj u b} \ {c.x0}, q = p := by
      intro q hq
      rw [hpset] at hq
      exact Set.mem_singleton_iff.mp hq
    have hem : e • p ∈ {b | c.OnL b m ∧ ¬ c.Delta.Adj u b} \ {c.x0} := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have h1 := (cInc_smul c.G1 c.G2 e p m).2 hpm
        rwa [c.E_smul_line hm heE] at h1
      · have h1 := c.delta_adj_smul_532 e u p
        rw [heu] at h1
        exact fun h => hpN.1.2 (h1.mp h)
      · intro h
        exact hpx (MulAction.injective e ((Set.mem_singleton_iff.mp h).trans
          (c.smul_x0_of_mem (c.E_le_G1 heE)).symm))
    have hfixp : e • p = p := hfixN _ hem
    rw [← c.E_inf_stab_eq_Eker hm hpm hpx]
    exact Subgroup.mem_inf.mpr ⟨heE, mem_stabilizer_iff.mpr hfixp⟩

theorem smul_mem_farP {e : G} (he : e ∈ c.E) {u : G ⧸ c.G1} (hu : u ∈ c.farP) :
    e • u ∈ c.farP := by
  obtain ⟨huP, hux, hnu⟩ := hu
  have hfix : e • c.x0 = c.x0 := c.smul_x0_of_mem (c.E_le_G1 he)
  have hadj := c.delta_adj_smul_532 e c.x0 u
  rw [hfix] at hadj
  refine ⟨?_, ?_, fun h => hnu (hadj.mp h)⟩
  · have h := (cInc_smul c.G1 c.G3 e u c.pi0).mpr huP
    rw [c.G3_smul_pi0 (c.E_le_G3 he)] at h
    exact h
  · intro h
    exact hux (MulAction.injective e (h.trans hfix.symm))

theorem card_inf_stab_ge (hfar : c.farP.ncard = 16) {u : G ⧸ c.G1} (hu : u ∈ c.farP) :
    2 ^ 7 ≤ Nat.card ↥(c.E ⊓ stabilizer G u) := by
  have horb : MulAction.orbit ↥c.E u ⊆ c.farP := by
    rintro _ ⟨⟨e, he⟩, rfl⟩
    exact c.smul_mem_farP he hu
  have hob : (MulAction.orbit ↥c.E u).ncard ≤ 16 :=
    (Set.ncard_le_ncard horb (Set.toFinite _)).trans_eq hfar
  have hidx : (stabilizer G u).relIndex c.E = (MulAction.orbit ↥c.E u).ncard := by
    rw [Subgroup.relIndex, MulAction.stabilizer_subgroupOf, MulAction.index_stabilizer]
  have hmul := Subgroup.relIndex_mul_card (H := stabilizer G u) (K := c.E)
  rw [hidx, c.card_E, inf_comm (stabilizer G u) c.E] at hmul
  nlinarith [Nat.zero_le (Nat.card ↥(c.E ⊓ stabilizer G u))]

end Loc49

theorem stmt5_3_2_of
    (hres : ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
      Nonempty (ResM24 c))
    (hker : ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
      c.KerFacts)
    (hLU : Stmt5_LineU) (hG2 : Stmt5_Gamma2) (h533 : Stmt5_3_3) : Stmt5_3_2 := by
  intro G _ _ z hJ c u hu p hpx hup
  obtain ⟨ρ⟩ := hres G z hJ c
  have hk := hker G z hJ c
  have hx0 : c.OnP c.x0 c.pi0 := c.x0_mem_ptsP
  have hu1 : c.OnP u c.pi0 := hu.1
  have hfar : c.farP.ncard = 16 := ρ.ncard_far_onP hLU hG2 hJ hx0
  have hcard := c.card_inf_stab_ge hfar hu
  have hpi : c.E ⊓ stabilizer G u = c.Epl c.pi0 :=
    Subgroup.eq_of_le_of_card_ge (c.inf_stab_le_Epl h533 hJ hu.2.1 hu.2.2 hu1)
      (by rw [hk.card_Epl hx0]; exact hcard)
  have hpp : c.E ⊓ stabilizer G u = c.Epl p :=
    Subgroup.eq_of_le_of_card_ge (c.inf_stab_le_Epl h533 hJ hu.2.1 hu.2.2 hup)
      (by rw [hk.card_Epl hpx]; exact hcard)
  exact hk.Epl_inj hpx hx0 (hpp.symm.trans hpi)

end CFSG.Quasithin.H13.AS91
