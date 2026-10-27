module

public import CFSG.OddTranspositions.SevenThreeTransitive
public import CFSG.Timmesfeld.Bridge.Asc72Lift

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem pCore_thirdK_le_center_of_commute (hS : Setup G D) (hL : LocalSecond D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n)
    (hord : orderOf (u * v * w) = 2 * n)
    (hcomm : ∀ q ∈ CFSG.pCore 2 (thirdK D ((u * v * w) ^ n)), Commute (q : G) u) :
    CFSG.pCore 2 (thirdK D ((u * v * w) ^ n)) ≤
      Subgroup.center (thirdK D ((u * v * w) ^ n)) := by
  set K := thirdK D ((u * v * w) ^ n)
  intro q hq
  have hKc : thirdK D ((u * v * w) ^ n) ≤ Subgroup.centralizer ({(q : G)} : Set G) := by
    rw [thirdK, Subgroup.closure_le]
    intro x hx
    obtain ⟨k, hk, rfl⟩ := thirdK_transitive hS hL htri hn hord x hx
    set k' : K := ⟨k, hk⟩
    have hq' : k'⁻¹ * q * k'⁻¹⁻¹ ∈ CFSG.pCore 2 K :=
      (CFSG.pCore_normal (p := 2) (G := K)).conj_mem q hq k'⁻¹
    have hcu : Commute (k⁻¹ * (q : G) * k) u := by
      simpa [k'] using hcomm _ hq'
    have h := hcu.conj k
    have hq_eq : k * (k⁻¹ * (q : G) * k) * k⁻¹ = q := by group
    rw [hq_eq] at h
    exact Subgroup.mem_centralizer_singleton_iff.mpr h.eq.symm
  refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
  exact Subgroup.mem_centralizer_singleton_iff.mp (hKc g.2)

theorem exists_pCore_conj_ne (hS : Setup G D) (hL : LocalSecond D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n)
    (hord : orderOf (u * v * w) = 2 * n)
    (hQ : ¬ CFSG.pCore 2 (thirdK D ((u * v * w) ^ n)) ≤
      Subgroup.center (thirdK D ((u * v * w) ^ n))) :
    ∃ q ∈ CFSG.pCore 2 (thirdK D ((u * v * w) ^ n)),
      (q : G) * u * (q : G)⁻¹ ∈ D ∧ (q : G) * u * (q : G)⁻¹ ≠ u ∧
        Commute u ((q : G) * u * (q : G)⁻¹) := by
  set K := thirdK D ((u * v * w) ^ n)
  have hex : ∃ q ∈ CFSG.pCore 2 K, ¬ Commute (q : G) u := by
    by_contra h
    push Not at h
    exact hQ (pCore_thirdK_le_center_of_commute hS hL htri hn hord h)
  obtain ⟨q, hq, hqu⟩ := hex
  have hu : u ∈ D := htri.1
  have huK : u ∈ K := by
    have hzu := (IsTriangle.third_kind hS.oddT hS.normal htri hn hord).2.2.1
    exact Delta_subset_thirdK (mem_Delta_iff.mpr ⟨hu, hzu.symm⟩)
  have ha : (q : G) * u * (q : G)⁻¹ ∈ D := hS.conj_mem _ hu
  have hne : (q : G) * u * (q : G)⁻¹ ≠ u := by
    intro h
    apply hqu
    calc (q : G) * u = (q : G) * u * (q : G)⁻¹ * q := by group
      _ = u * q := by rw [h]
  refine ⟨q, hq, ha, hne, ?_⟩
  set uK : K := ⟨u, huK⟩
  have hr : uK * q * uK⁻¹ * q⁻¹ ∈ CFSG.pCore 2 K :=
    (CFSG.pCore 2 K).mul_mem ((CFSG.pCore_normal (p := 2) (G := K)).conj_mem q hq uK)
      ((CFSG.pCore 2 K).inv_mem hq)
  refine commute_of_inv_mul_mem_two hS.oddT
    ((CFSG.pCore_isPGroup (p := 2) (G := K)).map K.subtype) hu ha ⟨_, hr, ?_⟩
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, uK]
  rw [hS.oddT.inv_eq hu]
  group

end CFSG.OddTranspositions
