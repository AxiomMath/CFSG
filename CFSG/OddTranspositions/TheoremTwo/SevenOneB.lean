module

public import CFSG.OddTranspositions.SevenThreeQuotient
public import CFSG.OddTranspositions.SevenLocalSecond
public import CFSG.OddTranspositions.TheoremTwo.AalphaNonempty
public import CFSG.OddTranspositions.TheoremTwo.Assembly
public import CFSG.Timmesfeld.Bridge.RootSetsConn3

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem not_meetsSq_of_noFirstKind (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hnf : ∀ x w y : G, IsTriangle D x w y →
      ¬ (Odd (orderOf (x * y * w)) ∧ 1 < orderOf (x * y * w))) :
    ¬ ∃ x ∈ D, ∃ y ∈ D, x ≠ y ∧ Commute x y ∧ x * y ∈ D := by
  rintro ⟨u, hu, v, hv, huv, hc, huvD⟩
  obtain ⟨e, he, hue⟩ : ∃ e ∈ D, ¬ Commute u e := by
    by_contra h
    push Not at h
    have hle : Subgroup.closure D ≤ Subgroup.centralizer ({u} : Set G) := by
      rw [Subgroup.closure_le]
      intro e he
      exact Subgroup.mem_centralizer_singleton_iff.mpr (h e he).symm.eq
    have hcent : u ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Subgroup.centralizer ({u} : Set G) := hle (by rw [hS.gen]; trivial)
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    have hZ : Subgroup.center G = ⊥ :=
      hrad _ inferInstance (Group.isSolvable_of_comm fun a b =>
        Subtype.ext (Subgroup.mem_center_iff.mp a.2 b).symm)
    rw [hZ, Subgroup.mem_bot] at hcent
    exact hS.oddT.ne_one hu hcent
  obtain ⟨h1, h2⟩ := centralizer_eq_of_mul_mem hS hu hv huv hc huvD
  have hve : ¬ Commute v e := by
    intro hve
    have hmem : e ∈ D ∩ Subgroup.centralizer ({v} : Set G) :=
      ⟨he, Subgroup.mem_centralizer_singleton_iff.mpr hve.symm.eq⟩
    rw [← h1] at hmem
    exact hue (Subgroup.mem_centralizer_singleton_iff.mp hmem.2).symm
  have huve : ¬ Commute (u * v) e := by
    intro huve
    have hmem : e ∈ D ∩ Subgroup.centralizer ({u * v} : Set G) :=
      ⟨he, Subgroup.mem_centralizer_singleton_iff.mpr huve.symm.eq⟩
    rw [h2] at hmem
    exact hue (Subgroup.mem_centralizer_singleton_iff.mp hmem.2).symm
  have hodd : Odd (orderOf (u * v * e)) := hS.oddT.odd_of_not_commute huvD he huve
  have hgt : 1 < orderOf (u * v * e) := by
    rcases Nat.lt_or_ge 1 (orderOf (u * v * e)) with h | h
    · exact h
    · exfalso
      have h1' : orderOf (u * v * e) = 1 := le_antisymm h (orderOf_pos _)
      rw [orderOf_eq_one_iff] at h1'
      apply huve
      rw [eq_inv_of_mul_eq_one_right h1']
      exact (Commute.refl _).inv_right
  exact hnf u e v ⟨hu, hv, he, huv, hc, hue, hve⟩ ⟨hodd, hgt⟩

theorem not_meetsSq_of_localSecond (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hL : LocalSecond D) (hconn : ¬ Disconnected D) :
    ¬ ∃ x ∈ D, ∃ y ∈ D, x ≠ y ∧ Commute x y ∧ x * y ∈ D := by
  obtain ⟨hC⟩ := nonempty_hypothesisC hS hconn hrad
  refine not_meetsSq_of_noFirstKind hS hrad (no_firstKind_of_H' hC ?_)
  intro x w y hx hw hy htri hfirst
  rw [DalphaStar_triangles_of_localSecond hC hL x hx w hw y hy htri] at hfirst
  exact absurd hfirst.1 (by decide)

theorem exists_meetsSq_DeltaBar (hS : Setup G D) (hL : LocalSecond D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n) :
    ∃ x ∈ DeltaBar D ((u * v * w) ^ n), ∃ y ∈ DeltaBar D ((u * v * w) ^ n),
      x ≠ y ∧ Commute x y ∧ x * y ∈ DeltaBar D ((u * v * w) ^ n) := by
  classical
  set z : G := (u * v * w) ^ n with hzdef
  set K : Subgroup G := thirdK D z with hKdef
  set R : Subgroup K := CFSG.solvableRadical K with hRdef
  set mk := QuotientGroup.mk' R with hmkdef
  obtain ⟨hzz, -, hzu, hzv, hzw, hbD⟩ := IsTriangle.third_kind hS.oddT hS.normal htri hn hord
  have huΔ : u ∈ Delta D z := mem_Delta_iff.mpr ⟨htri.1, hzu.symm⟩
  have hvΔ : v ∈ Delta D z := mem_Delta_iff.mpr ⟨htri.2.1, hzv.symm⟩
  have hwΔ : w ∈ Delta D z := mem_Delta_iff.mpr ⟨htri.2.2.1, hzw.symm⟩
  have hbz : Commute (u * v * z) z :=
    ((hzu.symm.mul_left hzv.symm).symm.mul_right (Commute.refl z)).symm
  have hbΔ : u * v * z ∈ Delta D z := mem_Delta_iff.mpr ⟨hbD, hbz⟩
  have huK : u ∈ K := Delta_subset_thirdK huΔ
  have hvK : v ∈ K := Delta_subset_thirdK hvΔ
  have hwK : w ∈ K := Delta_subset_thirdK hwΔ
  have hbK : u * v * z ∈ K := Delta_subset_thirdK hbΔ
  have hzK : z ∈ K := K.pow_mem (K.mul_mem (K.mul_mem huK hvK) hwK) n
  have hzR : (⟨z, hzK⟩ : K) ∈ R := by
    have hzCenter : (⟨z, hzK⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro k
      have hk := thirdK_le_centralizer k.2
      rw [Subgroup.mem_centralizer_iff] at hk
      exact Subtype.ext (hk z (Set.mem_singleton z)).symm
    exact OddTransp.le_solvableRadical (N := Subgroup.center K) inferInstance inferInstance
      hzCenter
  have hmemBar : ∀ {x : G} (hx : x ∈ Delta D z),
      mk ⟨x, Delta_subset_thirdK hx⟩ ∈ DeltaBar D z := fun hx => ⟨_, hx, rfl⟩
  have hmul : mk ⟨u, huK⟩ * mk ⟨v, hvK⟩ = mk ⟨u * v * z, hbK⟩ := by
    have huv_eq : (⟨u, huK⟩ * ⟨v, hvK⟩ : K) = ⟨u * v * z, hbK⟩ * ⟨z, hzK⟩ := by
      apply Subtype.ext
      show u * v = u * v * z * z
      rw [mul_assoc (u * v), hzz, mul_one]
    have hzR1 : mk ⟨z, hzK⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hzR
    rw [← map_mul, huv_eq, map_mul, hzR1, mul_one]
  have hne : mk ⟨u, huK⟩ ≠ mk ⟨v, hvK⟩ := by
    intro hEq
    have hb1 : mk ⟨u * v * z, hbK⟩ = 1 := by
      rw [← hmul, ← hEq, ← map_mul]
      have huu : (⟨u, huK⟩ : K) * ⟨u, huK⟩ = 1 := Subtype.ext (hS.oddT.mul_self_eq_one htri.1)
      rw [huu, map_one]
    exact DeltaK_mk_ne_one hS hL htri hn hn1 hord ⟨u * v * z, hbK⟩ hbΔ hb1
  have hcomm : Commute (⟨u, huK⟩ : K) ⟨v, hvK⟩ :=
    (commute_iff_eq _ _).mpr (Subtype.ext htri.2.2.2.2.1.eq)
  exact ⟨mk ⟨u, huK⟩, hmemBar huΔ, mk ⟨v, hvK⟩, hmemBar hvΔ, hne, hcomm.map mk,
    hmul ▸ hmemBar hbΔ⟩

theorem thirdK_quotient_normal_solvable_eq_bot (z : G) :
    ∀ N : Subgroup (thirdK D z ⧸ CFSG.solvableRadical (thirdK D z)), N.Normal →
      Group.IsSolvable N → N = ⊥ := by
  intro N hN hsol
  have hle := OddTransp.le_solvableRadical hN hsol
  rw [thirdK_quotient_radical_eq_bot] at hle
  exact eq_bot_iff.mpr hle

theorem disconnected_DeltaBar (hS : Setup G D) (hL : LocalSecond D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n) :
    Disconnected (DeltaBar D ((u * v * w) ^ n)) := by
  by_contra hconn
  exact not_meetsSq_of_localSecond (thirdK_quotient_setup hS hL htri hn hn1 hord)
    (thirdK_quotient_normal_solvable_eq_bot _) (localSecond_DeltaBar hS hL htri hn hn1 hord)
    hconn (exists_meetsSq_DeltaBar hS hL htri hn hn1 hord)

theorem isBenderGroup_thirdK_quotient (hT1 : TheoremOne) (hS : Setup G D) (hL : LocalSecond D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n) :
    CFSG.BenderSuzuki.IsBenderGroup
      (thirdK D ((u * v * w) ^ n) ⧸ CFSG.solvableRadical (thirdK D ((u * v * w) ^ n))) := by
  have hS' := thirdK_quotient_setup hS hL htri hn hn1 hord
  obtain ⟨x, hx, y, hy, -, hxy, hxyD⟩ := exists_meetsSq_DeltaBar hS hL htri hn hn1 hord
  exact isBenderGroup_of_conclusion hS' hx hy hxy hxyD
    (hT1 _ _ hS'.isClass hS'.oddT.1 hS'.oddT.2 hS'.gen
      (thirdK_quotient_normal_solvable_eq_bot _)
      (exists_subgroup_of_disconnected hS' (disconnected_DeltaBar hS hL htri hn hn1 hord)))

end CFSG.OddTranspositions
