module

public import CFSG.RankThree.PartTwo.KFacts.KS14SzSporTools
import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS14

open TauCeti

section Suz

variable {G : Type*} [Group G] [Finite G]

theorem suz_commute (h3 : ¬ 3 ∣ Nat.card G) (e : G ≃* Sporadic.suzPresentation.Group) (i j) :
    Commute (presGen e i) (presGen e j) := by
  have hR := lift_presGen_eq_one e
  simp only [Sporadic.suzPresentation_transcribed, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, Relator.toFreeGroup_pow, Relator.toFreeGroup_mul,
    Relator.toFreeGroup_inv, Relator.toFreeGroup_gen, map_pow, map_mul, map_inv,
    FreeGroup.lift_apply_of] at hR
  obtain ⟨ha2, hb2, -, hd2, -, -, -, hab5, hbc3, -, hde3, hbf3, -, hgb3, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, hfg, -, -, hbcd, -⟩ := hR
  set a := presGen e ⟨0, by simp [GroupPresentation.generatorCount]⟩
  set b := presGen e ⟨1, by simp [GroupPresentation.generatorCount]⟩
  set c := presGen e ⟨2, by simp [GroupPresentation.generatorCount]⟩
  set d := presGen e ⟨3, by simp [GroupPresentation.generatorCount]⟩
  set ee := presGen e ⟨4, by simp [GroupPresentation.generatorCount]⟩
  set f := presGen e ⟨5, by simp [GroupPresentation.generatorCount]⟩
  set g := presGen e ⟨6, by simp [GroupPresentation.generatorCount]⟩
  have hc : c = b := eq_of_mul_pow_three_eq_one h3 hb2 hbc3
  have he : ee = d := eq_of_mul_pow_three_eq_one h3 hd2 hde3
  have hf : f = b := eq_of_mul_pow_three_eq_one h3 hb2 hbf3
  have hg : g = b := by
    have hgb := eq_one_of_pow_three_eq_one h3 hgb3
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hb2)
    rw [← hb']
    exact eq_inv_of_mul_eq_one_left hgb
  have ha : a = 1 := by
    rw [hf, hg, ← sq, hb2, one_pow, mul_one, inv_eq_one] at hfg
    exact hfg
  have hb : b = 1 := by
    rw [ha, one_mul] at hab5
    exact eq_one_of_pow_eq_one_of_coprime hab5 hb2 (by norm_num)
  simp only [hc, hb, one_mul, mul_one] at hbcd
  have hd : ee = 1 := by
    rw [← sq, hd2, one_pow, one_mul] at hbcd
    exact eq_one_of_pow_three_eq_one h3 hbcd
  refine commute_of_forall_eq_one (fun k => ?_) i j
  obtain ⟨k, hk⟩ := k
  have hk7 : k < 7 := by simpa [GroupPresentation.generatorCount] using hk
  interval_cases k
  · exact ha
  · exact hb
  · exact hc.trans hb
  · exact he.symm.trans hd
  · exact hd
  · exact hf.trans hb
  · exact hg.trans hb

end Suz

section ON

variable {G : Type*} [Group G] [Finite G]

theorem on_commute (h3 : ¬ 3 ∣ Nat.card G) (e : G ≃* Sporadic.onanPresentation.Group) (i j) :
    Commute (presGen e i) (presGen e j) := by
  have hR := lift_presGen_eq_one e
  simp only [Sporadic.onanPresentation_transcribed, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, Relator.toFreeGroup_pow, Relator.toFreeGroup_mul,
    Relator.toFreeGroup_inv, Relator.toFreeGroup_gen, Relator.toFreeGroup_conj, map_pow,
    map_mul, map_inv, FreeGroup.lift_apply_of] at hR
  obtain ⟨ha2, hb2, -, hd2, he2, -, hab3, hbc3, -, hde3, hef3, -, -, -, -, -, -, -, -, -, -, -,
    hg2, hcd4, hc24, -, hbcdg, -, -⟩ := hR
  set a := presGen e ⟨0, by simp [GroupPresentation.generatorCount]⟩
  set b := presGen e ⟨1, by simp [GroupPresentation.generatorCount]⟩
  set c := presGen e ⟨2, by simp [GroupPresentation.generatorCount]⟩
  set d := presGen e ⟨3, by simp [GroupPresentation.generatorCount]⟩
  set ee := presGen e ⟨4, by simp [GroupPresentation.generatorCount]⟩
  set f := presGen e ⟨5, by simp [GroupPresentation.generatorCount]⟩
  set g := presGen e ⟨6, by simp [GroupPresentation.generatorCount]⟩
  have hb : b = a := eq_of_mul_pow_three_eq_one h3 ha2 hab3
  have hc : c = a := (eq_of_mul_pow_three_eq_one h3 hb2 hbc3).trans hb
  have he : ee = d := eq_of_mul_pow_three_eq_one h3 hd2 hde3
  have hf : f = d := (eq_of_mul_pow_three_eq_one h3 he2 hef3).trans he
  have haa : a * a = 1 := by rw [← sq]; exact ha2
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  rw [hc, hf, pow_succ', inv_mul_cancel_left] at hcd4
  have hd : d = a := eq_of_mul_pow_three_eq_one h3 ha2 hcd4
  rw [hf, hd, haa, inv_one, one_mul] at hg2
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hg2)
  rw [hc, hd] at hc24
  have haa' : ∀ x, a * (a * x) = x := fun x => by rw [← mul_assoc, haa, one_mul]
  have h4 : (a * g) ^ 4 = 1 := by
    simp only [mul_inv_rev, mul_assoc, hai, hgi, haa'] at hc24
    rw [← hc24]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [hb, hc, hd, haa, one_mul] at hbcdg
  have hag : a * g = 1 := eq_one_of_pow_eq_one_of_coprime h4 hbcdg (by norm_num)
  have hg : g = a := by rw [← hai]; exact eq_inv_of_mul_eq_one_right hag
  refine commute_of_forall_eq_or_eq (Commute.refl a) (fun k => ?_) i j
  obtain ⟨k, hk⟩ := k
  have hk7 : k < 7 := by simpa [GroupPresentation.generatorCount] using hk
  interval_cases k
  · exact .inl rfl
  · exact .inl hb
  · exact .inl hc
  · exact .inl hd
  · exact .inl (he.trans hd)
  · exact .inl (hf.trans hd)
  · exact .inl hg

end ON

section Co

variable {G : Type*} [Group G] [Finite G]

theorem co1_commute (h3 : ¬ 3 ∣ Nat.card G) (e : G ≃* Sporadic.co1Presentation.Group) (i j) :
    Commute (presGen e i) (presGen e j) := by
  have hR := lift_presGen_eq_one e
  simp only [Sporadic.co1Presentation_transcribed, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, Relator.toFreeGroup_pow, Relator.toFreeGroup_mul,
    Relator.toFreeGroup_inv, Relator.toFreeGroup_gen, map_pow, map_mul, map_inv,
    FreeGroup.lift_apply_of] at hR
  obtain ⟨ha2, -, hc2, hd2, -, -, hg2, -, hab3, -, hah3, hbc5, -, -, hcd3, hce3, -, hdf3, -, -,
    -, hac2, -, -, hag2, -⟩ := hR
  set a := presGen e ⟨0, by simp [GroupPresentation.generatorCount]⟩
  set b := presGen e ⟨1, by simp [GroupPresentation.generatorCount]⟩
  set c := presGen e ⟨2, by simp [GroupPresentation.generatorCount]⟩
  set d := presGen e ⟨3, by simp [GroupPresentation.generatorCount]⟩
  set ee := presGen e ⟨4, by simp [GroupPresentation.generatorCount]⟩
  set f := presGen e ⟨5, by simp [GroupPresentation.generatorCount]⟩
  set g := presGen e ⟨6, by simp [GroupPresentation.generatorCount]⟩
  set h := presGen e ⟨7, by simp [GroupPresentation.generatorCount]⟩
  have hb : b = a := eq_of_mul_pow_three_eq_one h3 ha2 hab3
  have hh : h = a := eq_of_mul_pow_three_eq_one h3 ha2 hah3
  have hd : d = c := eq_of_mul_pow_three_eq_one h3 hc2 hcd3
  have he : ee = c := eq_of_mul_pow_three_eq_one h3 hc2 hce3
  have hf : f = c := (eq_of_mul_pow_three_eq_one h3 hd2 hdf3).trans hd
  rw [hb] at hbc5
  have hac : a * c = 1 := eq_one_of_pow_eq_one_of_coprime hbc5 hac2 (by norm_num)
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact ha2)
  have hc : c = a := by rw [← hai]; exact eq_inv_of_mul_eq_one_right hac
  have hga : Commute a g :=
    commute_of_involutions (by rw [← sq]; exact ha2) (by rw [← sq]; exact hg2) hag2
  refine commute_of_forall_eq_or_eq hga (fun k => ?_) i j
  obtain ⟨k, hk⟩ := k
  have hk8 : k < 8 := by simpa [GroupPresentation.generatorCount] using hk
  interval_cases k
  · exact .inl rfl
  · exact .inl hb
  · exact .inl hc
  · exact .inl (hd.trans hc)
  · exact .inl (he.trans hc)
  · exact .inl (hf.trans hc)
  · exact .inr rfl
  · exact .inl hh

theorem co3_commute (h3 : ¬ 3 ∣ Nat.card G) (e : G ≃* Sporadic.co3Presentation.Group) (i j) :
    Commute (presGen e i) (presGen e j) := by
  have hR := lift_presGen_eq_one e
  simp only [Sporadic.co3Presentation_transcribed, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, Relator.toFreeGroup_pow, Relator.toFreeGroup_mul,
    Relator.toFreeGroup_gen, map_pow, map_mul, FreeGroup.lift_apply_of] at hR
  obtain ⟨ha2, -, hc2, hd2, -, hf2, hg2, -, -, -, -, -, hdg2, -, hab3, hcd3, hde3, hfag, -,
    hcfg, -, -, hbcfcf, -⟩ := hR
  set a := presGen e ⟨0, by simp [GroupPresentation.generatorCount]⟩
  set b := presGen e ⟨1, by simp [GroupPresentation.generatorCount]⟩
  set c := presGen e ⟨2, by simp [GroupPresentation.generatorCount]⟩
  set d := presGen e ⟨3, by simp [GroupPresentation.generatorCount]⟩
  set ee := presGen e ⟨4, by simp [GroupPresentation.generatorCount]⟩
  set f := presGen e ⟨5, by simp [GroupPresentation.generatorCount]⟩
  set g := presGen e ⟨6, by simp [GroupPresentation.generatorCount]⟩
  have hb : b = a := eq_of_mul_pow_three_eq_one h3 ha2 hab3
  have hd : d = c := eq_of_mul_pow_three_eq_one h3 hc2 hcd3
  have he : ee = c := (eq_of_mul_pow_three_eq_one h3 hd2 hde3).trans hd
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hc2)
  have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hf2)
  have hcc : c * c = 1 := by rw [← sq]; exact hc2
  have hff : f * f = 1 := by rw [← sq]; exact hf2
  have hg : g = f * c := by
    have h1 := eq_one_of_pow_three_eq_one h3 hcfg
    rw [eq_inv_of_mul_eq_one_right h1, mul_inv_rev, hci, hfi]
  rw [hd] at hdg2
  have hcg : Commute c g :=
    commute_of_involutions hcc (by rw [← sq]; exact hg2) hdg2
  have hcf : c * f = f * c := by
    have h1 : c * (f * c) = f * c * c := by rw [← hg]; exact hcg.eq
    rw [mul_assoc f, hcc, mul_one] at h1
    calc c * f = c * (f * c) * c := by rw [mul_assoc, mul_assoc, hcc, mul_one]
      _ = f * c := by rw [h1]
  have hcfcf : c * f * c * f = 1 := by
    calc c * f * c * f = c * f * (c * f) := by rw [← mul_assoc]
      _ = c * f * (f * c) := by rw [hcf]
      _ = c * (f * f) * c := by simp only [mul_assoc]
      _ = 1 := by rw [hff, mul_one, hcc]
  have ha : a = 1 := by
    have h1 := eq_one_of_pow_three_eq_one h3 hbcfcf
    rw [hb, show a * c * f * c * f = a * (c * f * c * f) by simp only [mul_assoc], hcfcf,
      mul_one] at h1
    exact h1
  rw [ha, one_mul, show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hg2, one_mul] at hfag
  have hgf : g = f := by rw [← hfi]; exact eq_inv_of_mul_eq_one_right hfag
  have hc : c = 1 := by
    have h1 : f * c = f * 1 := by rw [mul_one, ← hg, hgf]
    exact mul_left_cancel h1
  refine commute_of_forall_eq_or_eq (Commute.one_left f) (fun k => ?_) i j
  obtain ⟨k, hk⟩ := k
  have hk7 : k < 7 := by simpa [GroupPresentation.generatorCount] using hk
  interval_cases k
  · exact .inl ha
  · exact .inl (hb.trans ha)
  · exact .inl hc
  · exact .inl (hd.trans hc)
  · exact .inl (he.trans hc)
  · exact .inr rfl
  · exact .inr hgf

end Co

section HN

variable {G : Type*} [Group G] [Finite G]

theorem hn_commute (h3 : ¬ 3 ∣ Nat.card G) (e : G ≃* Sporadic.hnPresentation.Group) (i j) :
    Commute (presGen e i) (presGen e j) := by
  have hR := lift_presGen_eq_one e
  simp only [Sporadic.hnPresentation_transcribed, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, Relator.toFreeGroup_pow, Relator.toFreeGroup_mul,
    Relator.toFreeGroup_inv, Relator.toFreeGroup_gen, Relator.toFreeGroup_comm, map_pow, map_mul,
    map_inv, map_commutatorElement, FreeGroup.lift_apply_of] at hR
  obtain ⟨-, -, -, -, -, -, hca, -, -, hbabc, hd2, -, -, hdconj, ht5, -, -, -, hdt⟩ := hR
  set a := presGen e ⟨0, by simp [GroupPresentation.generatorCount]⟩
  set b := presGen e ⟨1, by simp [GroupPresentation.generatorCount]⟩
  set c := presGen e ⟨2, by simp [GroupPresentation.generatorCount]⟩
  set d := presGen e ⟨3, by simp [GroupPresentation.generatorCount]⟩
  set t := presGen e ⟨4, by simp [GroupPresentation.generatorCount]⟩
  have ht : t = d := eq_of_mul_pow_three_eq_one h3 hd2 hdt
  rw [ht] at ht5
  have hd : d = 1 := eq_one_of_pow_eq_one_of_coprime ht5 hd2 (by norm_num)
  rw [hd, mul_one, mul_one, inv_mul_cancel, one_mul] at hdconj
  have hc : c = 1 := eq_one_of_pow_three_eq_one h3 hdconj
  rw [hc, mul_one] at hbabc
  have h1 := eq_one_of_pow_three_eq_one h3 hbabc
  have ha : a ∈ Subgroup.zpowers b := by
    have h2 : a = b⁻¹ * (b ^ 3)⁻¹ := by
      calc a = b⁻¹ * (b * a * b ^ 3) * (b ^ 3)⁻¹ := by group
        _ = b⁻¹ * (b ^ 3)⁻¹ := by rw [h1, mul_one]
    rw [h2]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers b))
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers b) 3))
  have hmem : ∀ k, presGen e k ∈ Subgroup.zpowers b := by
    intro k
    obtain ⟨k, hk⟩ := k
    have hk5 : k < 5 := by simpa [GroupPresentation.generatorCount] using hk
    interval_cases k
    · exact ha
    · exact Subgroup.mem_zpowers b
    · rw [show presGen e ⟨2, _⟩ = c from rfl, hc]; exact Subgroup.one_mem _
    · rw [show presGen e ⟨3, _⟩ = d from rfl, hd]; exact Subgroup.one_mem _
    · rw [show presGen e ⟨4, _⟩ = t from rfl, ht, hd]; exact Subgroup.one_mem _
  exact commute_of_mem_zpowers (hmem i) (hmem j)

end HN

section ThLy

variable {G : Type*} [Group G] [Finite G]

theorem th_commute (h3 : ¬ 3 ∣ Nat.card G) (e : G ≃* Sporadic.Thompson.presentation.Group) (i j) :
    Commute (presGen e i) (presGen e j) := by
  have hR' : ∀ t ∈ Sporadic.Thompson.relatorList,
      FreeGroup.lift (fun i : Fin 8 => presGen e i) t.toFreeGroup = 1 := lift_presGen_eq_one e
  simp only [Sporadic.Thompson.genA, Sporadic.Thompson.genB, Sporadic.Thompson.genC,
    Sporadic.Thompson.genD, Sporadic.Thompson.genE, Sporadic.Thompson.genS,
    Sporadic.Thompson.genT, Sporadic.Thompson.genU, Sporadic.Thompson.relatorList,
    Sporadic.Thompson.relatorsOne, Sporadic.Thompson.relatorsTwo,
    Sporadic.Thompson.relatorsThree, Sporadic.Thompson.relatorsFour,
    Sporadic.Thompson.relatorsFive, Sporadic.Thompson.relatorsSix, List.cons_append,
    List.nil_append, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
    Relator.toFreeGroup_pow, Relator.toFreeGroup_mul, Relator.toFreeGroup_inv,
    Relator.toFreeGroup_gen, Relator.toFreeGroup_conj, Relator.toFreeGroup_div,
    Relator.toFreeGroup_commInvInv, map_pow, map_mul, map_inv, map_div,
    FreeGroup.lift_apply_of] at hR'
  obtain ⟨ha2, hb2, -, hd2, he2, hab3, -, hbc3, hbd2, -, hacd, -, hde3, -, -, -, -, -, -, -,
    ht3, -, -, -, -, -, hst, hu2, -, -, -, -, hue, -, -, -, hus, -, -⟩ := hR'
  set a := presGen e (0 : Fin 8)
  set b := presGen e (1 : Fin 8)
  set c := presGen e (2 : Fin 8)
  set d := presGen e (3 : Fin 8)
  set ee := presGen e (4 : Fin 8)
  set s := presGen e (5 : Fin 8)
  set t := presGen e (6 : Fin 8)
  set u := presGen e (7 : Fin 8)
  have hb : b = a := eq_of_mul_pow_three_eq_one h3 ha2 hab3
  have hc : c = a := (eq_of_mul_pow_three_eq_one h3 hb2 hbc3).trans hb
  rw [hb] at hbd2
  have had : Commute a d :=
    commute_of_involutions (by rw [← sq]; exact ha2) (by rw [← sq]; exact hd2) hbd2
  have ha : a = 1 := by
    rw [hc, div_eq_one, had.mul_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, ha2,
      hd2, one_pow, mul_one] at hacd
    exact hacd
  have ht : t = 1 := eq_one_of_pow_three_eq_one h3 ht3
  have hs : s = 1 := by
    rw [ht, inv_one, one_mul, mul_one, div_eq_one, sq] at hst
    exact (mul_eq_left.1 hst.symm)
  rw [hc, ha, one_mul, div_one] at hu2
  rw [hb, hc, ha] at hue
  simp only [mul_one, inv_one, inv_mul_cancel, div_eq_one] at hue
  have he : ee = 1 := hue.symm
  have hd : d = 1 := by
    have := eq_of_mul_pow_three_eq_one h3 hd2 hde3
    rw [he] at this
    exact this.symm
  rw [hc, ha, hs, one_mul, mul_one, div_eq_one] at hus
  have hu : u = 1 := eq_one_of_pow_three_eq_one h3 hus.symm
  refine commute_of_forall_eq_one (fun k => ?_) i j
  fin_cases k
  · exact ha
  · exact hb.trans ha
  · exact hc.trans ha
  · exact hd
  · exact he
  · exact hs
  · exact ht
  · exact hu

end ThLy

section Ly

variable {G : Type*} [Group G] [Finite G]

theorem ly_commute (h3 : ¬ 3 ∣ Nat.card G) (e : G ≃* Sporadic.Lyons.presentation.Group) (i j) :
    Commute (presGen e i) (presGen e j) := by
  have hR := lift_presGen_eq_one e
  simp only [Sporadic.Lyons.presentation_transcribed, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, Relator.toFreeGroup_pow, Relator.toFreeGroup_mul,
    Relator.toFreeGroup_inv, Relator.toFreeGroup_gen, Relator.toFreeGroup_conj,
    Relator.toFreeGroup_div, Relator.toFreeGroup_commInvInv, map_pow, map_mul, map_inv, map_div,
    FreeGroup.lift_apply_of] at hR
  obtain ⟨ha8, hb5, hab4, -, hab3, hc5, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h20, -, -, h23,
    -, -, -, -, -, h29, -, -, -, -, h34, -, h36, h37, -, -, -, -, -, -, -, -, -, h47, h48, -, -,
    -, -⟩ := hR
  set a := presGen e ⟨0, by simp [GroupPresentation.generatorCount]⟩
  set b := presGen e ⟨1, by simp [GroupPresentation.generatorCount]⟩
  set c := presGen e ⟨2, by simp [GroupPresentation.generatorCount]⟩
  set d := presGen e ⟨3, by simp [GroupPresentation.generatorCount]⟩
  set ee := presGen e ⟨4, by simp [GroupPresentation.generatorCount]⟩
  set z := presGen e ⟨5, by simp [GroupPresentation.generatorCount]⟩
  have hcab : a * b = b * a := by
    have h := eq_one_of_pow_three_eq_one h3 hab3
    calc a * b = b * a * (a⁻¹ * b⁻¹ * a * b) := by group
      _ = b * a := by rw [h, mul_one]
  rw [(show Commute a b from hcab).mul_pow] at hab4
  have hb4 : b ^ 4 = (a ^ 4)⁻¹ := eq_inv_of_mul_eq_one_right hab4
  have hba : b = a ^ 4 := by
    calc b = (b ^ 4)⁻¹ * b ^ 5 := by rw [pow_succ b 4, inv_mul_cancel_left]
      _ = a ^ 4 := by rw [hb5, mul_one, hb4, inv_inv]
  have ha4 : a ^ 4 = 1 := by
    have h20' : a ^ 20 = 1 := by rw [show 20 = 4 * 5 by norm_num, pow_mul, ← hba, hb5]
    have := pow_gcd_eq_one.2 ⟨h20', ha8⟩
    norm_num at this
    exact this
  have hb : b = 1 := by rw [hba, ha4]
  simp only [hb, inv_one, one_mul, mul_one, div_eq_one, mul_inv_cancel_right] at h20
  have hc2 : c ^ 2 = 1 := by
    rw [mul_assoc (a⁻¹ * c * a), left_eq_mul, ← mul_inv_rev, inv_eq_one] at h20
    rw [sq]
    exact h20
  have hc : c = 1 := eq_one_of_pow_eq_one_of_coprime hc5 hc2 (by norm_num)
  simp only [hc, inv_one, mul_one, inv_mul_cancel] at h37
  rw [ha4, div_one] at h34
  have hd : d = 1 := eq_one_of_pow_eq_one_of_coprime h37 h34 (by norm_num)
  rw [hd, inv_one, one_mul, mul_one, div_eq_one] at h36
  have ha2 : a ^ 2 = 1 := by
    have h1 : 1 * a = a ^ 2 * a := by rw [one_mul, ← pow_succ]; exact h36
    exact (mul_right_cancel h1).symm
  simp only [hb, hc, hd, inv_one, one_pow, one_mul, mul_one, inv_mul_cancel, div_eq_one] at h23
  simp only [hb, hc, h23, inv_one, one_pow, mul_one, inv_mul_cancel, div_eq_one] at h29
  have ha : a = 1 := by
    rw [ha2, mul_one, left_eq_mul] at h29
    exact h29
  simp only [ha, hb, one_pow, inv_one, one_mul, mul_one] at h48
  have hz : z = 1 := eq_one_of_pow_three_eq_one h3 h48
  refine commute_of_forall_eq_one (fun k => ?_) i j
  obtain ⟨k, hk⟩ := k
  have hk6 : k < 6 := by simpa [GroupPresentation.generatorCount] using hk
  interval_cases k
  · exact ha
  · exact hb
  · exact hc
  · exact hd
  · exact h23.trans ha
  · exact hz

end Ly

end CFSG.RankThree.PartTwo.KFacts.KS14
