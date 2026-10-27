module

public import CFSG.Permutation.FiveTransitive.HallOrbitTransitivity

public section

namespace CFSG

namespace FiveTransitive.Research.HallRegularOrbits

open MulAction
open Research.HallOrbitTransitivity
open Research.HallVFourOrbits
open scoped Pointwise

variable {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]

@[expose] def regularFourSet (a b : G) (x : X) : Set X :=
  {x, a • x, b • x, (a * b) • x}

private theorem smul_exceptionalSet_eq_of_commutes
    (a b g : G) (hga : Commute g a) (hgb : Commute g b) :
    g • exceptionalSet (X := X) a b = exceptionalSet (X := X) a b := by
  have ha : g • MulAction.fixedBy X a = MulAction.fixedBy X a := by
    change g • MulAction.fixedBy X a = MulAction.fixedBy X a
    exact MulAction.fixedBy_mem_fixedBy_of_commute hga.symm
  have hb : g • MulAction.fixedBy X b = MulAction.fixedBy X b := by
    change g • MulAction.fixedBy X b = MulAction.fixedBy X b
    exact MulAction.fixedBy_mem_fixedBy_of_commute hgb.symm
  have hab : g • MulAction.fixedBy X (a * b) =
      MulAction.fixedBy X (a * b) := by
    change g • MulAction.fixedBy X (a * b) =
      MulAction.fixedBy X (a * b)
    exact MulAction.fixedBy_mem_fixedBy_of_commute
      (hga.mul_right hgb).symm
  simp only [exceptionalSet, Set.smul_set_union, ha, hb, hab]

private theorem smul_not_mem_exceptionalSet_of_commutes
    (a b g : G) (hga : Commute g a) (hgb : Commute g b)
    {x : X} (hx : x ∉ exceptionalSet (X := X) a b) :
    g • x ∉ exceptionalSet (X := X) a b := by
  rw [← Set.mem_compl_iff] at hx ⊢
  have hcompl : g • (exceptionalSet (X := X) a b)ᶜ =
      (exceptionalSet (X := X) a b)ᶜ := by
    rw [Set.smul_set_compl, smul_exceptionalSet_eq_of_commutes a b g hga hgb]
  rw [← hcompl]
  exact Set.smul_mem_smul_set hx

theorem regularFourSet_subset_compl_exceptionalSet
    (a b : G) (haTwo : a ^ 2 = 1) (hbTwo : b ^ 2 = 1)
    (hab : Commute a b) (y : X)
    (hy : y ∉ exceptionalSet (X := X) a b) :
    regularFourSet a b y ⊆ (exceptionalSet (X := X) a b)ᶜ := by
  intro z hz
  rw [Set.mem_compl_iff]
  simp only [regularFourSet, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact hy
  · exact smul_not_mem_exceptionalSet_of_commutes a b a
      (Commute.refl a) hab hy
  · exact smul_not_mem_exceptionalSet_of_commutes a b b
      hab.symm (Commute.refl b) hy
  · exact smul_not_mem_exceptionalSet_of_commutes a b (a * b)
      ((Commute.refl a).mul_left hab.symm)
      (hab.mul_left (Commute.refl b)) hy

theorem regularFourSet_ncard_of_not_mem_exceptionalSet
    (a b : G) (haTwo : a ^ 2 = 1) (hbTwo : b ^ 2 = 1)
    (hab : Commute a b) (x : X)
    (hx : x ∉ exceptionalSet (X := X) a b) :
    (regularFourSet a b x).ncard = 4 := by
  have hxa : a • x ≠ x := by
    intro h
    apply hx
    simp [exceptionalSet, h]
  have hxb : b • x ≠ x := by
    intro h
    apply hx
    simp [exceptionalSet, h]
  have hxc : (a * b) • x ≠ x := by
    intro h
    apply hx
    simp [exceptionalSet, h]
  exact regular_four_set_ncard a b haTwo hbTwo hab x hxa hxb hxc

theorem first_smul_mem_regularFourSet
    (a b : G) (haTwo : a ^ 2 = 1) (hab : Commute a b)
    (y z : X) (hz : z ∈ regularFourSet a b y) :
    a • z ∈ regularFourSet a b y := by
  have haa (w : X) : a • (a • w) = w := by
    rw [← mul_smul, ← pow_two, haTwo, one_smul]
  have habAct (w : X) : a • (b • w) = (a * b) • w := by
    rw [mul_smul]
  have haab (w : X) : a • ((a * b) • w) = b • w := by
    rw [← mul_smul, ← mul_assoc, ← pow_two, haTwo, one_mul]
  simp only [regularFourSet, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl (haa y)
  · exact Or.inr (Or.inr (Or.inr (habAct y)))
  · exact Or.inr (Or.inr (Or.inl (haab y)))

theorem second_smul_mem_regularFourSet
    (a b : G) (hbTwo : b ^ 2 = 1) (hab : Commute a b)
    (y z : X) (hz : z ∈ regularFourSet a b y) :
    b • z ∈ regularFourSet a b y := by
  have hbb (w : X) : b • (b • w) = w := by
    rw [← mul_smul, ← pow_two, hbTwo, one_smul]
  have hbaAct (w : X) : b • (a • w) = (a * b) • w := by
    rw [← mul_smul, hab.eq, mul_smul]
  have hbab (w : X) : b • ((a * b) • w) = a • w := by
    rw [← mul_smul]
    congr 1
    calc
      b * (a * b) = (b * a) * b := by rw [mul_assoc]
      _ = (a * b) * b := by rw [hab.eq]
      _ = a * (b * b) := by rw [mul_assoc]
      _ = a := by rw [← pow_two, hbTwo, mul_one]
  simp only [regularFourSet, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (hbaAct y)))
  · exact Or.inl (hbb y)
  · exact Or.inr (Or.inl (hbab y))

private theorem regularFourSet_eq_of_mem
    (a b : G) (haTwo : a ^ 2 = 1) (hbTwo : b ^ 2 = 1)
    (hab : Commute a b) (y z : X)
    (hy : y ∉ exceptionalSet (X := X) a b)
    (hz : z ∈ regularFourSet a b y) :
    regularFourSet a b z = regularFourSet a b y := by
  have hzRegular : z ∉ exceptionalSet (X := X) a b :=
    regularFourSet_subset_compl_exceptionalSet
      a b haTwo hbTwo hab y hy hz
  have hsub : regularFourSet a b z ⊆ regularFourSet a b y := by
    intro w hw
    simp only [regularFourSet, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact hz
    · exact first_smul_mem_regularFourSet a b haTwo hab y z hz
    · exact second_smul_mem_regularFourSet a b hbTwo hab y z hz
    · rw [mul_smul]
      exact first_smul_mem_regularFourSet a b haTwo hab y (b • z)
        (second_smul_mem_regularFourSet a b hbTwo hab y z hz)
  apply Set.eq_of_subset_of_ncard_le hsub
  rw [regularFourSet_ncard_of_not_mem_exceptionalSet
        a b haTwo hbTwo hab z hzRegular,
    regularFourSet_ncard_of_not_mem_exceptionalSet
        a b haTwo hbTwo hab y hy]

private theorem orbit_ncard_smul_eq_of_commutes
    (C : Subgroup G) (g : G)
    (hcomm : ∀ k : C, Commute (k : G) g) (x : X) :
    (MulAction.orbit C (g • x)).ncard =
      (MulAction.orbit C x).ncard := by
  have horbit : MulAction.orbit C (g • x) =
      g • MulAction.orbit C x := by
    ext z
    simp only [MulAction.mem_orbit_iff, Set.mem_smul_set]
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨(k : G) • x, ⟨k, rfl⟩, ?_⟩
      calc
        g • ((k : G) • x) = (g * (k : G)) • x := by rw [mul_smul]
        _ = ((k : G) * g) • x := by rw [(hcomm k).eq]
        _ = (k : G) • (g • x) := by rw [mul_smul]
    · rintro ⟨z, ⟨k, rfl⟩, rfl⟩
      refine ⟨k, ?_⟩
      calc
        (k : G) • (g • x) = ((k : G) * g) • x := by rw [mul_smul]
        _ = (g * (k : G)) • x := by rw [(hcomm k).eq]
        _ = g • ((k : G) • x) := by rw [mul_smul]
  rw [horbit, Set.ncard_smul_set]

private theorem reference_orbit_ncard_eq
    (a b : G) (y z : X)
    (hz : z ∈ regularFourSet a b y) :
    (MulAction.orbit (hallCentralizer (X := X) a b) z).ncard =
      (MulAction.orbit (hallCentralizer (X := X) a b) y).ncard := by
  let C := hallCentralizer (X := X) a b
  have hcommA : ∀ k : C, Commute (k : G) a := by
    intro k
    exact (mem_hallCentralizer_iff a b (k : G)).mp k.prop |>.2.1
  have hcommB : ∀ k : C, Commute (k : G) b := by
    intro k
    exact (mem_hallCentralizer_iff a b (k : G)).mp k.prop |>.2.2
  simp only [regularFourSet, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · rfl
  · exact orbit_ncard_smul_eq_of_commutes C a hcommA y
  · exact orbit_ncard_smul_eq_of_commutes C b hcommB y
  · exact orbit_ncard_smul_eq_of_commutes C (a * b)
      (fun k ↦ (hcommA k).mul_right (hcommB k)) y

private theorem reference_orbits_disjoint
    (a b : G) (haTwo : a ^ 2 = 1) (hbTwo : b ^ 2 = 1)
    (hab : Commute a b)
    (hoddC : Odd (Nat.card (hallCentralizer (X := X) a b)))
    (y r s : X) (hy : y ∉ exceptionalSet (X := X) a b)
    (hr : r ∈ regularFourSet a b y)
    (hs : s ∈ regularFourSet a b y) (hrs : r ≠ s) :
    Disjoint
      (MulAction.orbit (hallCentralizer (X := X) a b) r)
      (MulAction.orbit (hallCentralizer (X := X) a b) s) := by
  rcases MulAction.orbit.eq_or_disjoint
      (G := hallCentralizer (X := X) a b) r s with heq | hdis
  · exfalso
    have hsOrbit : s ∈
        MulAction.orbit (hallCentralizer (X := X) a b) r := by
      rw [heq]
      exact MulAction.mem_orbit_self s
    obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp hsOrbit
    have hkG : (k : G) • r = s := hk
    have hrRegular : r ∉ exceptionalSet (X := X) a b :=
      regularFourSet_subset_compl_exceptionalSet
        a b haTwo hbTwo hab y hy hr
    have hsFour : s ∈ regularFourSet a b r := by
      rw [regularFourSet_eq_of_mem a b haTwo hbTwo hab y r hy hr]
      exact hs
    have hfix := hallCentralizer_smul_eq_self_of_mem_fourSet
      a b haTwo hbTwo hab hoddC r hrRegular k
        (by simpa only [regularFourSet, hkG] using hsFour)
    exact hrs (hfix.symm.trans hkG)
  · exact hdis

private def regularOrbitUnion (a b : G) (y : X) : Set X :=
  (MulAction.orbit (hallCentralizer (X := X) a b) y ∪
      MulAction.orbit (hallCentralizer (X := X) a b) (a • y)) ∪
    (MulAction.orbit (hallCentralizer (X := X) a b) (b • y) ∪
      MulAction.orbit (hallCentralizer (X := X) a b) ((a * b) • y))

private theorem compl_exceptionalSet_eq_regularOrbitUnion
    (a b : G) (haTwo : a ^ 2 = 1) (hbTwo : b ^ 2 = 1)
    (hab : Commute a b) (y : X)
    (hy : y ∉ exceptionalSet (X := X) a b)
    (hconnect : ∀ x : X, x ∉ exceptionalSet (X := X) a b →
      ∃ k : hallCentralizer (X := X) a b,
        (k : G) • x ∈ regularFourSet a b y) :
    (exceptionalSet (X := X) a b)ᶜ = regularOrbitUnion a b y := by
  let C := hallCentralizer (X := X) a b
  have hcommA : ∀ k : C, Commute (k : G) a := by
    intro k
    exact (mem_hallCentralizer_iff a b (k : G)).mp k.prop |>.2.1
  have hcommB : ∀ k : C, Commute (k : G) b := by
    intro k
    exact (mem_hallCentralizer_iff a b (k : G)).mp k.prop |>.2.2
  have hrefRegular : ∀ z ∈ regularFourSet a b y,
      z ∉ exceptionalSet (X := X) a b := by
    intro z hz
    exact regularFourSet_subset_compl_exceptionalSet
      a b haTwo hbTwo hab y hy hz
  ext x
  constructor
  · intro hx
    rw [Set.mem_compl_iff] at hx
    obtain ⟨k, hk⟩ := hconnect x hx
    have hxOrbit : x ∈ MulAction.orbit C ((k : G) • x) := by
      change x ∈ MulAction.orbit C ((k : C) • x)
      exact MulAction.mem_orbit_smul k x
    simp only [regularFourSet, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hk
    simp only [regularOrbitUnion, Set.mem_union]
    rcases hk with hk | hk | hk | hk
    · exact Or.inl (Or.inl (by simpa only [hk] using hxOrbit))
    · exact Or.inl (Or.inr (by simpa only [hk] using hxOrbit))
    · exact Or.inr (Or.inl (by simpa only [hk] using hxOrbit))
    · exact Or.inr (Or.inr (by simpa only [hk] using hxOrbit))
  · intro hx
    rw [Set.mem_compl_iff]
    simp only [regularOrbitUnion, Set.mem_union] at hx
    rcases hx with (hx | hx) | (hx | hx)
    · obtain ⟨k, rfl⟩ := MulAction.mem_orbit_iff.mp hx
      exact smul_not_mem_exceptionalSet_of_commutes a b (k : G)
        (hcommA k) (hcommB k) (hrefRegular y (by simp [regularFourSet]))
    · obtain ⟨k, rfl⟩ := MulAction.mem_orbit_iff.mp hx
      exact smul_not_mem_exceptionalSet_of_commutes a b (k : G)
        (hcommA k) (hcommB k)
        (hrefRegular (a • y) (by simp [regularFourSet]))
    · obtain ⟨k, rfl⟩ := MulAction.mem_orbit_iff.mp hx
      exact smul_not_mem_exceptionalSet_of_commutes a b (k : G)
        (hcommA k) (hcommB k)
        (hrefRegular (b • y) (by simp [regularFourSet]))
    · obtain ⟨k, rfl⟩ := MulAction.mem_orbit_iff.mp hx
      exact smul_not_mem_exceptionalSet_of_commutes a b (k : G)
        (hcommA k) (hcommB k)
        (hrefRegular ((a * b) • y) (by simp [regularFourSet]))

theorem regular_orbit_ncard_eq
    (a b : G) (y : X)
    (hconnect : ∀ x : X, x ∉ exceptionalSet (X := X) a b →
      ∃ k : hallCentralizer (X := X) a b,
        (k : G) • x ∈ regularFourSet a b y) :
    ∀ x : X, x ∉ exceptionalSet (X := X) a b →
      (MulAction.orbit (hallCentralizer (X := X) a b) x).ncard =
        (MulAction.orbit (hallCentralizer (X := X) a b) y).ncard := by
  intro x hx
  obtain ⟨k, hk⟩ := hconnect x hx
  let C := hallCentralizer (X := X) a b
  have horbit : MulAction.orbit C ((k : G) • x) =
      MulAction.orbit C x := by
    change MulAction.orbit C ((k : C) • x) = MulAction.orbit C x
    exact MulAction.orbit_smul k x
  calc
    (MulAction.orbit C x).ncard =
        (MulAction.orbit C ((k : G) • x)).ncard := by rw [horbit]
    _ = (MulAction.orbit C y).ncard :=
      reference_orbit_ncard_eq a b y ((k : G) • x) hk

theorem compl_exceptionalSet_ncard_eq_four_mul_orbit_ncard
    (a b : G) (haTwo : a ^ 2 = 1) (hbTwo : b ^ 2 = 1)
    (hab : Commute a b)
    (hoddC : Odd (Nat.card (hallCentralizer (X := X) a b)))
    (y : X) (hy : y ∉ exceptionalSet (X := X) a b)
    (hconnect : ∀ x : X, x ∉ exceptionalSet (X := X) a b →
      ∃ k : hallCentralizer (X := X) a b,
        (k : G) • x ∈ regularFourSet a b y) :
    (exceptionalSet (X := X) a b)ᶜ.ncard =
      4 * (MulAction.orbit (hallCentralizer (X := X) a b) y).ncard := by
  let C := hallCentralizer (X := X) a b
  let t := (MulAction.orbit C y).ncard
  let O0 := MulAction.orbit C y
  let Oa := MulAction.orbit C (a • y)
  let Ob := MulAction.orbit C (b • y)
  let Oab := MulAction.orbit C ((a * b) • y)
  have hyA : y ≠ a • y := by
    intro h
    apply hy
    simp [exceptionalSet, h.symm]
  have hyB : y ≠ b • y := by
    intro h
    apply hy
    simp [exceptionalSet, h.symm]
  have hyAB : y ≠ (a * b) • y := by
    intro h
    apply hy
    simp [exceptionalSet, h.symm]
  have haB : a • y ≠ b • y := by
    intro h
    apply hyAB
    symm
    calc
      (a * b) • y = a • (b • y) := mul_smul _ _ _
      _ = a • (a • y) := congrArg (fun z : X ↦ a • z) h.symm
      _ = y := by rw [← mul_smul, ← pow_two, haTwo, one_smul]
  have haAB : a • y ≠ (a * b) • y := by
    intro h
    apply hyB
    symm
    calc
      b • y = a • ((a * b) • y) := by
        rw [← mul_smul, ← mul_assoc, ← pow_two, haTwo, one_mul]
      _ = a • (a • y) := congrArg (fun z : X ↦ a • z) h.symm
      _ = y := by rw [← mul_smul, ← pow_two, haTwo, one_smul]
  have hbAB : b • y ≠ (a * b) • y := by
    intro h
    apply hyA
    symm
    calc
      a • y = b • ((a * b) • y) := by
        rw [← mul_smul]
        congr 1
        symm
        calc
          b * (a * b) = (b * a) * b := by rw [mul_assoc]
          _ = (a * b) * b := by rw [hab.eq]
          _ = a * (b * b) := by rw [mul_assoc]
          _ = a := by rw [← pow_two, hbTwo, mul_one]
      _ = b • (b • y) := congrArg (fun z : X ↦ b • z) h.symm
      _ = y := by rw [← mul_smul, ← pow_two, hbTwo, one_smul]
  have hmem0 : y ∈ regularFourSet a b y := by simp [regularFourSet]
  have hmema : a • y ∈ regularFourSet a b y := by simp [regularFourSet]
  have hmemb : b • y ∈ regularFourSet a b y := by simp [regularFourSet]
  have hmemab : (a * b) • y ∈ regularFourSet a b y := by
    simp [regularFourSet]
  have hd0a : Disjoint O0 Oa :=
    reference_orbits_disjoint a b haTwo hbTwo hab hoddC
      y y (a • y) hy hmem0 hmema hyA
  have hd0b : Disjoint O0 Ob :=
    reference_orbits_disjoint a b haTwo hbTwo hab hoddC
      y y (b • y) hy hmem0 hmemb hyB
  have hd0ab : Disjoint O0 Oab :=
    reference_orbits_disjoint a b haTwo hbTwo hab hoddC
      y y ((a * b) • y) hy hmem0 hmemab hyAB
  have hdab : Disjoint Oa Ob :=
    reference_orbits_disjoint a b haTwo hbTwo hab hoddC
      y (a • y) (b • y) hy hmema hmemb haB
  have hdaab : Disjoint Oa Oab :=
    reference_orbits_disjoint a b haTwo hbTwo hab hoddC
      y (a • y) ((a * b) • y) hy hmema hmemab haAB
  have hdbab : Disjoint Ob Oab :=
    reference_orbits_disjoint a b haTwo hbTwo hab hoddC
      y (b • y) ((a * b) • y) hy hmemb hmemab hbAB
  have hcross : Disjoint (O0 ∪ Oa) (Ob ∪ Oab) := by
    rw [Set.disjoint_left]
    intro z hzLeft hzRight
    rcases hzLeft with hz0 | hza
    · rcases hzRight with hzb | hzab
      · exact (Set.disjoint_left.mp hd0b) hz0 hzb
      · exact (Set.disjoint_left.mp hd0ab) hz0 hzab
    · rcases hzRight with hzb | hzab
      · exact (Set.disjoint_left.mp hdab) hza hzb
      · exact (Set.disjoint_left.mp hdaab) hza hzab
  have hO0 : O0.ncard = t := rfl
  have hOa : Oa.ncard = t :=
    reference_orbit_ncard_eq a b y (a • y) hmema
  have hOb : Ob.ncard = t :=
    reference_orbit_ncard_eq a b y (b • y) hmemb
  have hOab : Oab.ncard = t :=
    reference_orbit_ncard_eq a b y ((a * b) • y) hmemab
  rw [compl_exceptionalSet_eq_regularOrbitUnion
      a b haTwo hbTwo hab y hy hconnect]
  change ((O0 ∪ Oa) ∪ (Ob ∪ Oab)).ncard = 4 * t
  rw [Set.ncard_union_eq hcross, Set.ncard_union_eq hd0a,
    Set.ncard_union_eq hdbab, hO0, hOa, hOb, hOab]
  omega

theorem sylow_orbit_eq_of_orbit_ncard_eq_prime_pow
    {C Y : Type} [Group C] [Finite C] [Fintype Y] [MulAction C Y]
    {p w : ℕ} [Fact p.Prime] (P : Sylow p C) (x : Y)
    (horbit : (MulAction.orbit C x).ncard = p ^ w) :
    MulAction.orbit P x = MulAction.orbit C x := by
  let H := MulAction.stabilizer C x
  have hrel : H.relIndex (P : Subgroup C) =
      (MulAction.orbit P x).ncard := by
    rw [Subgroup.relIndex]
    change (MulAction.stabilizer P x).index =
      (MulAction.orbit P x).ncard
    exact MulAction.index_stabilizer P x
  have hdvdIndex : H.index ∣
      H.relIndex (P : Subgroup C) * (P : Subgroup C).index := by
    calc
      H.index ∣ (H ⊓ (P : Subgroup C)).index :=
        Subgroup.index_dvd_of_le inf_le_left
      _ = H.relIndex (P : Subgroup C) * (P : Subgroup C).index := by
        rw [← Subgroup.relIndex_mul_index inf_le_right,
          Subgroup.inf_relIndex_right]
  have hdvd : p ^ w ∣
      (MulAction.orbit P x).ncard * (P : Subgroup C).index := by
    have hindex : H.index = p ^ w := by
      simpa only [H, MulAction.index_stabilizer] using horbit
    rw [← hindex, ← hrel]
    exact hdvdIndex
  have hcoprime : Nat.Coprime (p ^ w) (P : Subgroup C).index :=
    Nat.Coprime.pow_left w
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr P.not_dvd_index)
  have hdvdOrbit : p ^ w ∣ (MulAction.orbit P x).ncard :=
    hcoprime.dvd_mul_right.mp hdvd
  have hsubset : MulAction.orbit P x ⊆ MulAction.orbit C x :=
    MulAction.orbit_subgroup_subset (P : Subgroup C) x
  have hle : (MulAction.orbit P x).ncard ≤ p ^ w := by
    rw [← horbit]
    exact Set.ncard_le_ncard hsubset
  have hpos : 0 < (MulAction.orbit P x).ncard :=
    (MulAction.nonempty_orbit x).ncard_pos
  have hge : p ^ w ≤ (MulAction.orbit P x).ncard :=
    Nat.le_of_dvd hpos hdvdOrbit
  apply Set.eq_of_subset_of_ncard_le hsubset
  rw [horbit]
  omega

end FiveTransitive.Research.HallRegularOrbits

end CFSG
