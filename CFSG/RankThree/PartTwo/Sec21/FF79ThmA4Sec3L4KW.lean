module

public import CFSG.RankThree.PartTwo.Sec21.FF79ThmA4Sec3L4In
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4KLay
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.H4

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G] [Finite G]
variable {b : G} {J B A P D : Subgroup G}

theorem sec34_J_le (h : FF79Sec34In4 b J B A P D) : J ≤ Cen b := by
  rw [h.hJ]; exact Subgroup.map_subtype_le _

theorem sec34_J_conj (h : FF79Sec34In4 b J B A P D) {g y : G} (hg : g ∈ Cen b) (hy : y ∈ J) :
    g * y * g⁻¹ ∈ J := by
  rw [h.hJ] at hy ⊢
  obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
  exact Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * y' * ⟨g, hg⟩⁻¹,
    (Subgroup.normalClosure_normal).conj_mem y' hy' ⟨g, hg⟩, by simp⟩

theorem sec34_cen_quot_solvable (h : FF79Sec34In4 b J B A P D) :
    haveI : (J.subgroupOf (Cen b)).Normal := ⟨fun y hy g => by
      exact sec34_J_conj h g.2 hy⟩
    Group.IsSolvable (↥(Cen b) ⧸ J.subgroupOf (Cen b)) := by
  haveI : (J.subgroupOf (Cen b)).Normal := ⟨fun y hy g => by
    exact sec34_J_conj h g.2 hy⟩
  apply CFSG.FeitThompson.isSolvable_of_odd_natCard _
  have h1 : Nat.card ↥(J.subgroupOf (Cen b)) = Nat.card J :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sec34_J_le h)).toEquiv
  have h2 := Subgroup.card_mul_index (J.subgroupOf (Cen b))
  rw [h1, h.cbSplit.2] at h2
  have hJpos : 0 < Nat.card J := Nat.card_pos
  have h3 : (J.subgroupOf (Cen b)).index = 3 * Nat.card (Opp 3 (Cen b)) := by
    have : Nat.card J * (J.subgroupOf (Cen b)).index
        = Nat.card J * (3 * Nat.card (Opp 3 (Cen b))) := by rw [h2]; ring
    exact Nat.eq_of_mul_eq_mul_left hJpos this
  show Odd (Subgroup.index _)
  rw [h3]
  exact Odd.mul (by decide) h.oddX

theorem sec34_layW (h : FF79Sec34In4 b J B A P D) {a : G} (ha : a ∈ J) :
    Lay (Cen a ⊓ Cen b) = Lay (J ⊓ Cen a) := by
  have hJb := sec34_J_le h
  have hYX : J ⊓ Cen a ≤ Cen a ⊓ Cen b := fun x hx =>
    ⟨hx.2, hJb hx.1⟩
  haveI : ((J ⊓ Cen a).subgroupOf (Cen a ⊓ Cen b)).Normal := by
    refine ⟨fun y hy g => ?_⟩
    have hy' : (y : G) ∈ J ⊓ Cen a := hy
    have hg : (g : G) ∈ Cen a ⊓ Cen b := g.2
    show (g : G) * y * (g : G)⁻¹ ∈ J ⊓ Cen a
    refine ⟨sec34_J_conj h hg.2 hy'.1, ?_⟩
    exact (Cen a).mul_mem ((Cen a).mul_mem hg.1 hy'.2) ((Cen a).inv_mem hg.1)
  refine lay_eq_of_normal hYX fun K hK hperf => ?_
  haveI := hperf
  haveI := sec34_cen_quot_solvable h
  haveI : (J.subgroupOf (Cen b)).Normal := ⟨fun y hy g => by
    exact sec34_J_conj h g.2 hy⟩
  have hKb : K ≤ Cen b := hK.trans inf_le_right
  have := le_of_isPerfect_of_solvable_quot (H := Cen b) (N := J) (K := K) hKb
  exact le_inf this (hK.trans inf_le_left)

theorem sec34_nor_lay (h : FF79Sec34In4 b J B A P D) {a : G} (ha : a ∈ J) {v : G}
    (hv : v ∈ Nor (Subgroup.closure {a, b})) : v ∈ Nor (Lay (J ⊓ Cen a)) := by
  rw [← sec34_layW h ha]
  refine nor_lay_of_nor ?_
  have hW : ∀ x : G, x ∈ Cen a ⊓ Cen b ↔ x ∈ CenS (Subgroup.closure {a, b}) := by
    intro x
    constructor
    · rintro ⟨hxa, hxb⟩
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hsub : Subgroup.closure ({a, b} : Set G) ≤ Cen x := by
        rw [Subgroup.closure_le]
        rintro _ (rfl | rfl)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_singleton_iff.mp hxa).symm
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_singleton_iff.mp hxb).symm
      exact Subgroup.mem_centralizer_singleton_iff.mp (hsub hs)
    · intro hx
      rw [Subgroup.mem_centralizer_iff] at hx
      exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr
          (hx a (Subgroup.subset_closure (by simp))).symm,
        Subgroup.mem_centralizer_singleton_iff.mpr
          (hx b (Subgroup.subset_closure (by simp))).symm⟩
  have key : ∀ {v : G}, v ∈ Nor (Subgroup.closure ({a, b} : Set G)) → ∀ x : G,
      x ∈ CenS (Subgroup.closure ({a, b} : Set G)) →
      v * x * v⁻¹ ∈ CenS (Subgroup.closure ({a, b} : Set G)) := by
    intro v hv x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro s hs
    have hs' : v⁻¹ * s * v ∈ Subgroup.closure ({a, b} : Set G) := by
      have := (Subgroup.mem_normalizer_iff.mp ((Nor _).inv_mem hv) s).mp hs
      simpa using this
    have := hx _ hs'
    calc s * (v * x * v⁻¹) = v * ((v⁻¹ * s * v) * x) * v⁻¹ := by group
      _ = v * (x * (v⁻¹ * s * v)) * v⁻¹ := by rw [this]
      _ = v * x * v⁻¹ * s := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [hW, hW]
  exact ⟨key hv x, fun hx => by
    have := key ((Nor _).inv_mem hv) _ hx
    simpa [mul_assoc] using this⟩

end CFSG.RankThree.PartTwo.Sec21.FF79.H4
