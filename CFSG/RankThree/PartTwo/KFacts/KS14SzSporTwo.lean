module

public import CFSG.RankThree.PartTwo.KFacts.KS14SzSporTools
import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS14

open TauCeti

section TwoGen

variable {G : Type*} [Group G] [Finite G]

theorem j1_commute (h3 : ¬ 3 ∣ Nat.card G) (e : G ≃* Sporadic.j1Presentation.Group) (i j) :
    Commute (presGen e i) (presGen e j) := by
  have hR := lift_presGen_eq_one e
  simp only [Sporadic.j1Presentation_transcribed, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, Relator.toFreeGroup_pow, Relator.toFreeGroup_mul,
    Relator.toFreeGroup_inv, Relator.toFreeGroup_gen, map_pow, map_mul, map_inv,
    FreeGroup.lift_apply_of] at hR
  obtain ⟨-, hb, -⟩ := hR
  refine commute_of_two (by simp [GroupPresentation.generatorCount]) _ ?_ i j
  rw [eq_one_of_pow_three_eq_one h3 hb]
  exact Commute.one_right _

end TwoGen

section TwoGenB

variable {G : Type*} [Group G] [Finite G]

theorem j3_commute (h3 : ¬ 3 ∣ Nat.card G) (e : G ≃* Sporadic.j3Presentation.Group) (i j) :
    Commute (presGen e i) (presGen e j) := by
  have hR := lift_presGen_eq_one e
  simp only [Sporadic.j3Presentation_transcribed, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, Relator.toFreeGroup_pow, Relator.toFreeGroup_mul,
    Relator.toFreeGroup_inv, Relator.toFreeGroup_gen, Relator.toFreeGroup_comm, map_pow, map_mul,
    map_inv, map_commutatorElement, FreeGroup.lift_apply_of] at hR
  obtain ⟨-, hb, -⟩ := hR
  refine commute_of_two (by simp [GroupPresentation.generatorCount]) _ ?_ i j
  rw [eq_one_of_pow_three_eq_one h3 hb]
  exact Commute.one_right _

theorem m24_commute (h3 : ¬ 3 ∣ Nat.card G) (e : G ≃* Sporadic.m24Presentation.Group) (i j) :
    Commute (presGen e i) (presGen e j) := by
  have hR := lift_presGen_eq_one e
  simp only [Sporadic.m24Presentation_transcribed, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, Relator.toFreeGroup_pow, Relator.toFreeGroup_mul,
    Relator.toFreeGroup_inv, Relator.toFreeGroup_gen, Relator.toFreeGroup_comm, map_pow, map_mul,
    map_inv, map_commutatorElement, FreeGroup.lift_apply_of] at hR
  obtain ⟨-, hb, -⟩ := hR
  refine commute_of_two (by simp [GroupPresentation.generatorCount]) _ ?_ i j
  rw [eq_one_of_pow_three_eq_one h3 hb]
  exact Commute.one_right _

theorem co2_commute (h3 : ¬ 3 ∣ Nat.card G) (e : G ≃* Sporadic.co2Presentation.Group) (i j) :
    Commute (presGen e i) (presGen e j) := by
  have hR := lift_presGen_eq_one e
  simp only [Sporadic.co2Presentation_transcribed, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, Relator.toFreeGroup_pow, Relator.toFreeGroup_mul,
    Relator.toFreeGroup_inv, Relator.toFreeGroup_gen, Relator.toFreeGroup_comm, map_pow, map_mul,
    map_inv, map_commutatorElement, FreeGroup.lift_apply_of] at hR
  obtain ⟨-, -, h9, -⟩ := hR
  refine commute_of_two (by simp [GroupPresentation.generatorCount]) _ ?_ i j
  have h1 := pow_eq_one_of_pow_three_mul_eq_one (k := 3) h3 h9
  have h2 := eq_one_of_pow_three_eq_one h3 h1
  rw [mul_eq_one_iff_eq_inv] at h2
  rw [h2]
  exact ((Commute.refl _).pow_left 2).inv_left

theorem fi22_commute (h3 : ¬ 3 ∣ Nat.card G) (e : G ≃* Sporadic.fi22Presentation.Group) (i j) :
    Commute (presGen e i) (presGen e j) := by
  have hR := lift_presGen_eq_one e
  simp only [Sporadic.fi22Presentation_transcribed, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, Relator.toFreeGroup_pow, Relator.toFreeGroup_mul,
    Relator.toFreeGroup_inv, Relator.toFreeGroup_gen, Relator.toFreeGroup_comm, map_pow, map_mul,
    map_inv, map_commutatorElement, FreeGroup.lift_apply_of] at hR
  obtain ⟨-, -, -, -, hc, -⟩ := hR
  refine commute_of_two (by simp [GroupPresentation.generatorCount]) _ ?_ i j
  have h1 := eq_one_of_pow_three_eq_one h3 hc
  rw [commutatorElement_eq_one_iff_mul_comm] at h1
  exact Commute.inv_inv_iff.1 h1

end TwoGenB

section ThreeGen

variable {G : Type*} [Group G] [Finite G]

theorem j4_commute (h3 : ¬ 3 ∣ Nat.card G) (e : G ≃* Sporadic.j4Presentation.Group) (i j) :
    Commute (presGen e i) (presGen e j) := by
  have hR := lift_presGen_eq_one e
  simp only [Sporadic.j4Presentation_transcribed, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, Relator.toFreeGroup_pow, Relator.toFreeGroup_mul,
    Relator.toFreeGroup_inv, Relator.toFreeGroup_gen, Relator.toFreeGroup_comm, map_pow, map_mul,
    map_inv, map_commutatorElement, FreeGroup.lift_apply_of] at hR
  obtain ⟨hx2, hy3, hxy, -, -, -, -, -, -, -, ht, -⟩ := hR
  have hy := eq_one_of_pow_three_eq_one h3 hy3
  rw [hy, mul_one] at hxy
  have hx : presGen e ⟨0, by simp [GroupPresentation.generatorCount]⟩ = 1 := by
    have h23 : (23 : ℕ) = 2 * 11 + 1 := by norm_num
    rw [h23, pow_succ, pow_mul, hx2, one_pow, one_mul] at hxy
    exact hxy
  rw [hx, hy] at ht
  simp only [one_mul, mul_one, inv_one] at ht
  have htt := eq_one_of_pow_three_eq_one h3 ht
  refine commute_of_forall_eq_one (fun k => ?_) i j
  obtain ⟨k, hk⟩ := k
  have hk3 : k < 3 := by simpa [GroupPresentation.generatorCount] using hk
  interval_cases k
  · exact hx
  · exact hy
  · exact htt

theorem ru_commute (h3 : ¬ 3 ∣ Nat.card G) (e : G ≃* Sporadic.ruPresentation.Group) (i j) :
    Commute (presGen e i) (presGen e j) := by
  have hR := lift_presGen_eq_one e
  simp only [Sporadic.ruPresentation_transcribed, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, Relator.toFreeGroup_pow, Relator.toFreeGroup_mul,
    Relator.toFreeGroup_inv, Relator.toFreeGroup_gen, Relator.toFreeGroup_comm, map_pow, map_mul,
    map_inv, map_commutatorElement, FreeGroup.lift_apply_of] at hR
  obtain ⟨-, ht2, hu4, huv, hu2v, -, -, -, huvut, -⟩ := hR
  set u := presGen e ⟨0, by simp [GroupPresentation.generatorCount]⟩
  set v := presGen e ⟨1, by simp [GroupPresentation.generatorCount]⟩
  set t := presGen e ⟨2, by simp [GroupPresentation.generatorCount]⟩
  have h1 := eq_one_of_pow_three_eq_one h3 hu2v
  have hv : v = (u ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right h1
  rw [hv] at huv huvut
  have hu : u = 1 := by
    have h7 : u ^ 7 = 1 := by
      have : u * (u ^ 2)⁻¹ = u⁻¹ := by group
      rw [this, inv_pow, inv_eq_one] at huv
      exact huv
    have h8 : u ^ 8 = 1 := by
      rw [show (8 : ℕ) = 4 * 2 by norm_num, pow_mul, hu4, one_pow]
    exact eq_one_of_pow_eq_one_of_coprime h7 h8 (by norm_num)
  have hv' : v = 1 := by rw [hv, hu]; simp
  rw [hu] at huvut
  simp only [one_pow, inv_one, mul_one, one_mul] at huvut
  have htt : t = 1 := by
    have h13 : (13 : ℕ) = 2 * 6 + 1 := by norm_num
    rw [h13, pow_succ, pow_mul, ht2, one_pow, one_mul] at huvut
    exact huvut
  refine commute_of_forall_eq_one (fun k => ?_) i j
  obtain ⟨k, hk⟩ := k
  have hk3 : k < 3 := by simpa [GroupPresentation.generatorCount] using hk
  interval_cases k
  · exact hu
  · exact hv'
  · exact htt

end ThreeGen

section M12

variable {G : Type*} [Group G] [Finite G]

theorem m12_commute (h3 : ¬ 3 ∣ Nat.card G) (e : G ≃* Sporadic.m12Presentation.Group) (i j) :
    Commute (presGen e i) (presGen e j) := by
  have hR := lift_presGen_eq_one e
  simp only [Sporadic.m12Presentation_transcribed, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, Relator.toFreeGroup_pow, Relator.toFreeGroup_mul,
    Relator.toFreeGroup_inv, Relator.toFreeGroup_gen, map_pow, map_mul, map_inv,
    FreeGroup.lift_apply_of] at hR
  obtain ⟨h1, -, -⟩ := hR
  refine commute_of_two (by simp [GroupPresentation.generatorCount]) _ ?_ i j
  have hba := eq_one_of_pow_three_eq_one h3 h1
  rw [inv_mul_eq_one] at hba
  rw [← hba]

end M12

section CenterCases

variable {G : Type*} [Group G] [Finite G]

theorem m23_commute [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (h3 : ¬ 3 ∣ Nat.card G) (e : G ≃* Sporadic.m23Presentation.Group) (i j) :
    Commute (presGen e i) (presGen e j) := by
  have hP : Sporadic.m23Presentation.generatorCount = 2 := by
    simp [GroupPresentation.generatorCount]
  have hR := lift_presGen_eq_one e
  simp only [Sporadic.m23Presentation_transcribed, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, Relator.toFreeGroup_pow, Relator.toFreeGroup_mul,
    Relator.toFreeGroup_inv, Relator.toFreeGroup_gen, Relator.toFreeGroup_comm, map_pow, map_mul,
    map_inv, map_commutatorElement, FreeGroup.lift_apply_of] at hR
  obtain ⟨ha2, hb4, hab, hab2, hc, -⟩ := hR
  refine commute_of_two hP _ ?_ i j
  set a := presGen e ⟨0, by omega⟩
  set b := presGen e ⟨1, by omega⟩
  have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact ha2)
  have h2 : (a * b ^ 2) ^ 2 = 1 := pow_eq_one_of_pow_three_mul_eq_one (k := 2) h3 hab2
  have hb2i : (b ^ 2)⁻¹ = b ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_add]; exact hb4)
  have hcomm : Commute (b ^ 2) a := by
    have h' : a * b ^ 2 = (a * b ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← sq]; exact h2)
    rw [mul_inv_rev, hb2i, ha] at h'
    exact h'.symm
  have hb2 : b ^ 2 = 1 :=
    eq_one_of_commute_two hP hnab e hcomm ((Commute.refl b).pow_left 2)
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hb2)
  have hc2 := pow_eq_one_of_pow_three_mul_eq_one (k := 2) h3 hc
  rw [commutatorElement_def, inv_inv, inv_inv, ha, hbi] at hc2
  have h4 : (a * b) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq (a * b), ← hc2]
    group
  have h1 : a * b = 1 := by
    have := pow_gcd_eq_one.2 ⟨hab, h4⟩
    norm_num at this
    exact this
  rw [mul_eq_one_iff_eq_inv] at h1
  rw [h1]
  exact (Commute.refl b).inv_left

theorem hs_commute [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (h3 : ¬ 3 ∣ Nat.card G) (e : G ≃* Sporadic.hsPresentation.Group) (i j) :
    Commute (presGen e i) (presGen e j) := by
  have hP : Sporadic.hsPresentation.generatorCount = 2 := by
    simp [GroupPresentation.generatorCount]
  have hR := lift_presGen_eq_one e
  simp only [Sporadic.hsPresentation_transcribed, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, Relator.toFreeGroup_pow, Relator.toFreeGroup_mul,
    Relator.toFreeGroup_inv, Relator.toFreeGroup_gen, Relator.toFreeGroup_comm, map_pow, map_mul,
    map_inv, map_commutatorElement, FreeGroup.lift_apply_of] at hR
  obtain ⟨ha2, -, hab, -, -, hc, -⟩ := hR
  refine commute_of_two hP _ ?_ i j
  set a := presGen e ⟨0, by omega⟩
  set b := presGen e ⟨1, by omega⟩
  have hc1 := eq_one_of_pow_three_eq_one h3 hc
  rw [commutatorElement_eq_one_iff_mul_comm] at hc1
  have hcab : a * (b * a * b) = b * a * b * a := by
    have := (Commute.inv_inv_iff.1 hc1)
    exact this.eq
  have haa : a * a = 1 := by rw [← sq]; exact ha2
  have hz0 : Commute ((a * b) ^ 2) a := by
    show (a * b) ^ 2 * a = a * (a * b) ^ 2
    rw [sq]
    calc a * b * (a * b) * a = a * (b * a * b) * a := by group
      _ = b * a * b * a * a := by rw [hcab]
      _ = b * a * b := by rw [mul_assoc (b * a * b), haa, mul_one]
      _ = a * a * (b * a * b) := by rw [haa, one_mul]
      _ = a * (a * b * (a * b)) := by group
  have hz1 : Commute ((a * b) ^ 2) b := by
    show (a * b) ^ 2 * b = b * (a * b) ^ 2
    rw [sq]
    calc a * b * (a * b) * b = a * (b * a * b) * b := by group
      _ = b * a * b * a * b := by rw [hcab]
      _ = b * (a * b * (a * b)) := by group
  have hz := eq_one_of_commute_two hP hnab e hz0 hz1
  have h1 : a * b = 1 := by
    have := pow_gcd_eq_one.2 ⟨hab, hz⟩
    norm_num at this
    exact this
  rw [mul_eq_one_iff_eq_inv] at h1
  rw [h1]
  exact (Commute.refl b).inv_left

theorem j2_commute [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (h3 : ¬ 3 ∣ Nat.card G) (e : G ≃* Sporadic.j2Presentation.Group) (i j) :
    Commute (presGen e i) (presGen e j) := by
  have hP : Sporadic.j2Presentation.generatorCount = 2 := by
    simp [GroupPresentation.generatorCount]
  have hR := lift_presGen_eq_one e
  simp only [Sporadic.j2Presentation_transcribed, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, Relator.toFreeGroup_pow, Relator.toFreeGroup_mul,
    Relator.toFreeGroup_inv, Relator.toFreeGroup_gen, map_pow, map_mul,
    map_inv, FreeGroup.lift_apply_of] at hR
  obtain ⟨hbr, -, -⟩ := hR
  refine commute_of_two hP _ ?_ i j
  set a := presGen e ⟨0, by omega⟩
  set b := presGen e ⟨1, by omega⟩
  have hbraid : a * b * a = b * a * b := by
    rw [mul_inv_eq_one] at hbr
    exact hbr
  have hDa : a * b * a * a = b * (a * b * a) := by
    calc a * b * a * a = b * a * b * a := by rw [hbraid]
      _ = b * (a * b * a) := by group
  have hDb : a * b * a * b = a * (a * b * a) := by
    calc a * b * a * b = a * (b * a * b) := by group
      _ = a * (a * b * a) := by rw [hbraid]
  have hz0 : Commute ((a * b * a) ^ 2) a := by
    show (a * b * a) ^ 2 * a = a * (a * b * a) ^ 2
    rw [sq, mul_assoc, hDa, ← mul_assoc, hDb, mul_assoc]
  have hz1 : Commute ((a * b * a) ^ 2) b := by
    show (a * b * a) ^ 2 * b = b * (a * b * a) ^ 2
    rw [sq, mul_assoc, hDb, ← mul_assoc, hDa, mul_assoc]
  have hz := eq_one_of_commute_two hP hnab e hz0 hz1
  have h3ab : (a * b) ^ 3 = 1 := by
    rw [← hz, sq]
    calc (a * b) ^ 3 = a * b * a * (b * a * b) := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = a * b * a * (a * b * a) := by rw [← hbraid]
  have h1 := eq_one_of_pow_three_eq_one h3 h3ab
  rw [mul_eq_one_iff_eq_inv] at h1
  rw [h1]
  exact (Commute.refl b).inv_left

end CenterCases

section HeMcL

variable {G : Type*} [Group G] [Finite G]

theorem he_commute (h3 : ¬ 3 ∣ Nat.card G) (e : G ≃* Sporadic.hePresentation.Group) (i j) :
    Commute (presGen e i) (presGen e j) := by
  have hP : Sporadic.hePresentation.generatorCount = 2 := by
    simp [GroupPresentation.generatorCount]
  have hR := lift_presGen_eq_one e
  simp only [Sporadic.hePresentation_transcribed, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, Relator.toFreeGroup_pow, Relator.toFreeGroup_mul,
    Relator.toFreeGroup_inv, Relator.toFreeGroup_gen, Relator.toFreeGroup_comm, map_pow, map_mul,
    map_inv, map_commutatorElement, FreeGroup.lift_apply_of] at hR
  obtain ⟨ha2, hb7, -, hc6, -, hw, -⟩ := hR
  refine commute_of_two hP _ ?_ i j
  set a := presGen e ⟨0, by omega⟩
  set b := presGen e ⟨1, by omega⟩
  have haa : a * a = 1 := by rw [← sq]; exact ha2
  have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hc2 := pow_eq_one_of_pow_three_mul_eq_one (k := 2) h3 hc6
  rw [commutatorElement_def, inv_inv, inv_inv, ha] at hc2
  have hconj : (b⁻¹ * a * b) * (b⁻¹ * a * b) = 1 := by
    rw [show b⁻¹ * a * b * (b⁻¹ * a * b) = b⁻¹ * (a * a) * b by group, haa]
    group
  have hab : Commute a (b⁻¹ * a * b) :=
    commute_of_involutions haa hconj (by rw [← hc2]; group)
  have h12 : Commute (b * a * b⁻¹) (b ^ 2 * a * (b ^ 2)⁻¹) := by
    have := (commute_conj hab (b ^ 2)).symm
    convert this using 1
    group
  have hsq : (b * a * b⁻¹ * (b ^ 2 * a * (b ^ 2)⁻¹)) ^ 2 = 1 := by
    rw [h12.mul_pow, show (b * a * b⁻¹) ^ 2 = b * (a * a) * b⁻¹ by rw [sq]; group,
      show (b ^ 2 * a * (b ^ 2)⁻¹) ^ 2 = b ^ 2 * (a * a) * (b ^ 2)⁻¹ by rw [sq]; group, haa]
    group
  have hw' : b * a * b * a * b⁻¹ * a * b * a * b = b ^ 3 := by
    calc b * a * b * a * b⁻¹ * a * b * a * b =
        (b * a * b⁻¹ * (b ^ 2 * a * (b ^ 2)⁻¹)) ^ 2 * b ^ 3 := by rw [sq]; group
      _ = b ^ 3 := by rw [hsq, one_mul]
  rw [commutatorElement_eq_one_iff_mul_comm, hw'] at hw
  have hb3 : Commute a (b ^ 3) := (Commute.inv_inv_iff.1 hw)
  have hb : b = (b ^ 3) ^ 5 := by
    rw [← pow_mul, show 3 * 5 = 7 * 2 + 1 by norm_num, pow_succ, pow_mul, hb7, one_pow, one_mul]
  rw [hb]
  exact hb3.pow_right 5

end HeMcL

section McL

variable {G : Type*} [Group G] [Finite G]

theorem mcl_commute (h3 : ¬ 3 ∣ Nat.card G) (e : G ≃* Sporadic.mclPresentation.Group) (i j) :
    Commute (presGen e i) (presGen e j) := by
  have hP : Sporadic.mclPresentation.generatorCount = 2 := by
    simp [GroupPresentation.generatorCount]
  have hR := lift_presGen_eq_one e
  simp only [Sporadic.mclPresentation_transcribed, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, Relator.toFreeGroup_pow, Relator.toFreeGroup_mul,
    Relator.toFreeGroup_inv, Relator.toFreeGroup_gen, Relator.toFreeGroup_comm, map_pow, map_mul,
    map_inv, map_commutatorElement, FreeGroup.lift_apply_of] at hR
  obtain ⟨ha2, hb5, -, -, hs2, hc6, -⟩ := hR
  refine commute_of_two hP _ ?_ i j
  set a := presGen e ⟨0, by omega⟩
  set b := presGen e ⟨1, by omega⟩
  have haa : a * a = 1 := by rw [← sq]; exact ha2
  have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hac : (a * b ^ 2) ^ 4 = 1 := pow_eq_one_of_pow_three_mul_eq_one (k := 4) h3 hs2
  have hc2 := pow_eq_one_of_pow_three_mul_eq_one (k := 2) h3 hc6
  rw [commutatorElement_def, inv_inv, inv_inv, ha] at hc2
  have hconj : ((b ^ 2)⁻¹ * a * b ^ 2) * ((b ^ 2)⁻¹ * a * b ^ 2) = 1 := by
    rw [show (b ^ 2)⁻¹ * a * b ^ 2 * ((b ^ 2)⁻¹ * a * b ^ 2) = (b ^ 2)⁻¹ * (a * a) * b ^ 2 by
      group, haa]
    group
  have hcomm : Commute a ((b ^ 2)⁻¹ * a * b ^ 2) :=
    commute_of_involutions haa hconj (by rw [← hc2]; group)
  have hc5 : (b ^ 2) ^ 5 = 1 := by
    rw [← pow_mul, show 2 * 5 = 5 * 2 by norm_num, pow_mul, hb5, one_pow]
  have hb2 := eq_one_of_pentagon haa hc5 hac hcomm
  have hb : b = 1 := by
    have := pow_gcd_eq_one.2 ⟨hb5, hb2⟩
    norm_num at this
    exact this
  rw [hb]
  exact Commute.one_right a

end McL

end CFSG.RankThree.PartTwo.KFacts.KS14
