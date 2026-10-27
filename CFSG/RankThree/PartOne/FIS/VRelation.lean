module

public import CFSG.RankThree.PartOne.FIS.Blocks

public section

namespace CFSG.RankThree.PartOne.FIS

open CFSG.LocalAnalysis.GorensteinLyons (IsThreeTranspositions)
open CFSG.RankThree.PartTwo.Sec7

variable {G : Type*} [Group G] {D : Set G}

theorem eq_one_of_mem_pGroup {p q : ℕ} {N : Subgroup G} (hN : IsPGroup p N)
    (hcop : Nat.Coprime q p) {t : G} (ht : t ∈ N) (hq : t ^ q = 1) : t = 1 := by
  obtain ⟨k, hk⟩ := hN ⟨t, ht⟩
  have hk' : t ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf t ∣ q := orderOf_dvd_of_pow_eq_one hq
  have h2 : orderOf t ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h3 : orderOf t ∣ Nat.gcd q (p ^ k) := Nat.dvd_gcd h1 h2
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k hcop)] at h3
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

theorem noncomm_imp_mem [Finite G] (hD : IsThreeTranspositions D) (N : Subgroup G) [N.Normal]
    {m d y : G} (hm : m ∈ N) (hd : d ∈ D) (hy : y ∈ D) (hyd : y * d = d * y)
    (hnc : y * (m * d * m⁻¹) ≠ (m * d * m⁻¹) * y) :
    y * (m * d * m⁻¹) ∈ N ∧ y * d ∈ N := by
  have ha : m * d * m⁻¹ ∈ D := tt_conj_mem hD hd m
  have h3 := tt_cube hD hy ha hnc
  set a := m * d * m⁻¹ with ha_def
  have hdd := tt_mul_self hD hd
  have hyy := tt_mul_self hD hy
  have hu2 : (y * d) * (y * d) = 1 := by
    calc (y * d) * (y * d) = y * (d * y) * d := by simp only [mul_assoc]
      _ = y * (y * d) * d := by rw [← hyd]
      _ = (y * y) * (d * d) := by simp only [mul_assoc]
      _ = 1 := by rw [hyy, hdd, mul_one]
  have hui : (y * d)⁻¹ = y * d := inv_eq_of_mul_eq_one_right hu2
  have hw : d * a ∈ N := by
    have h1 : d * a = (d * m * d⁻¹) * m⁻¹ := by
      rw [ha_def, tt_inv_eq hD hd]
      simp only [mul_assoc]
    rw [h1]
    exact mul_mem (Subgroup.Normal.conj_mem inferInstance m hm d) (inv_mem hm)
  have ht : y * a = (y * d) * (d * a) := by
    rw [show (y * d) * (d * a) = y * (d * d) * a by simp only [mul_assoc], hdd, mul_one]
  have ht2 : (y * a) ^ 2 ∈ N := by
    rw [ht, pow_two]
    have : (y * d) * (d * a) * ((y * d) * (d * a)) =
        ((y * d) * (d * a) * (y * d)⁻¹) * (d * a) := by
      rw [hui]
      simp only [mul_assoc]
    rw [this]
    exact mul_mem (Subgroup.Normal.conj_mem inferInstance _ hw (y * d)) hw
  have htN : y * a ∈ N := by
    have : y * a = ((y * a) ^ 2)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← pow_succ']
      exact h3
    rw [this]
    exact inv_mem ht2
  refine ⟨htN, ?_⟩
  have : y * d = (y * a) * (d * a)⁻¹ := by
    rw [ht]
    group
  rw [this]
  exact mul_mem htN (inv_mem hw)

theorem comm_conj_of_isPGroup_two [Finite G] (hD : IsThreeTranspositions D) (N : Subgroup G)
    [N.Normal] (hN : IsPGroup 2 N) {m d y : G} (hm : m ∈ N) (hd : d ∈ D) (hy : y ∈ D)
    (hyd : y * d = d * y) : y * (m * d * m⁻¹) = (m * d * m⁻¹) * y := by
  by_contra hnc
  have ha : m * d * m⁻¹ ∈ D := tt_conj_mem hD hd m
  have h3 := tt_cube hD hy ha hnc
  obtain ⟨htN, -⟩ := noncomm_imp_mem hD N hm hd hy hyd hnc
  have h1 : y * (m * d * m⁻¹) = 1 :=
    eq_one_of_mem_pGroup hN (by norm_num : Nat.Coprime 3 2) htN h3
  have : y = m * d * m⁻¹ := by
    rw [← tt_inv_eq hD ha]
    exact eq_inv_of_mul_eq_one_left h1
  exact hnc (by rw [← this])

theorem tt_mem_center_of_comm (hD : IsThreeTranspositions D) {z : G}
    (h : ∀ a ∈ D, a * z = z * a) : z ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.closure D := by rw [tt_closure_eq hD]; trivial
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => simp
  | mul x y _ _ hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
  | inv x _ hx => exact (Commute.inv_left (hx : Commute x z)).eq

theorem tt_eq_of_comm (hD : IsThreeTranspositions D)
    (htr : ∀ d ∈ D, ∀ e ∈ D, ∃ g : G, g * d * g⁻¹ = e) {d x : G} (hd : d ∈ D) (hx : x ∈ D)
    (h : ∀ a ∈ D, a * d = d * a) : x = d := by
  obtain ⟨g, hg⟩ := htr d hd x hx
  have hz := Subgroup.mem_center_iff.1 (tt_mem_center_of_comm hD h) g
  rw [← hg, hz]
  group

theorem vRel_comm {a b : G} (ha : a ∈ D) (hab : VRel D a b) : a * b = b * a := by
  have h1 : a ∈ centralizerIn D a := ⟨ha, rfl⟩
  have h2 : a ∈ centralizerIn D b := by rw [← hab]; exact h1
  exact h2.2

theorem mul_self_of_mem_closure {S : Set G} (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hsq : ∀ x ∈ S, x * x = 1) : ∀ g ∈ Subgroup.closure S, g * g = 1 := by
  have h1 : ∀ g ∈ Subgroup.closure S, ∀ y ∈ S, g * y = y * g := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact fun y hy => hcomm x hx y hy
    | one => exact fun y _ => by rw [one_mul, mul_one]
    | mul a b _ _ iha ihb =>
      exact fun y hy => by rw [mul_assoc, ihb y hy, ← mul_assoc, iha y hy, mul_assoc]
    | inv a _ iha => exact fun y hy => (Commute.inv_left (iha y hy : Commute a y)).eq
  have h2 : ∀ g ∈ Subgroup.closure S, ∀ h ∈ Subgroup.closure S, g * h = h * g := by
    intro g hg h hh
    induction hh using Subgroup.closure_induction with
    | mem y hy => exact h1 g hg y hy
    | one => rw [one_mul, mul_one]
    | mul a b _ _ iha ihb => rw [← mul_assoc, iha, mul_assoc, ihb, ← mul_assoc]
    | inv a _ iha => exact (Commute.inv_right (iha : Commute g a)).eq
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hsq x hx
  | one => rw [one_mul]
  | mul a b ha hb iha ihb =>
    rw [show a * b * (a * b) = a * (b * a) * b by simp only [mul_assoc], ← h2 a ha b hb,
      show a * (a * b) * b = a * a * (b * b) by simp only [mul_assoc], iha, ihb, one_mul]
  | inv a _ iha => rw [← mul_inv_rev, iha, inv_one]

theorem vXgrp_isPGroup (hD : IsThreeTranspositions D) {x : G} (_hx : x ∈ D) :
    IsPGroup 2 (Xgrp (VRel D) D x) := by
  have hc : ∀ u ∈ D, ∀ v ∈ D, VRel D u x → VRel D v x → Commute u v := by
    intro u hu v _ hux hvx
    exact vRel_comm hu (hux.trans hvx.symm)
  have hcomm : ∀ s ∈ prodSet (VRel D) D x, ∀ t ∈ prodSet (VRel D) D x, s * t = t * s := by
    rintro _ ⟨a, ha, b, hb, hax, hbx, rfl⟩ _ ⟨a', ha', b', hb', hax', hbx', rfl⟩
    exact (((hc a ha a' ha' hax hax').mul_right (hc a ha b' hb' hax hbx')).mul_left
      ((hc b hb a' ha' hbx hax').mul_right (hc b hb b' hb' hbx hbx'))).eq
  have hsq : ∀ s ∈ prodSet (VRel D) D x, s * s = 1 := by
    rintro _ ⟨a, ha, b, hb, hax, hbx, rfl⟩
    have hab : a * b = b * a := (hc a ha b hb hax hbx).eq
    calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
      _ = a * (a * b) * b := by rw [← hab]
      _ = (a * a) * (b * b) := by simp only [mul_assoc]
      _ = 1 := by rw [tt_mul_self hD ha, tt_mul_self hD hb, mul_one]
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  have := mul_self_of_mem_closure hcomm hsq g.1 g.2
  simpa [pow_two] using this

theorem vSet_mul_mem_pCore [Finite G] (hD : IsThreeTranspositions D) {v d : G} (hd : d ∈ D)
    (hv : v ∈ vSet D d) : v * d ∈ CFSG.pCore 2 G := by
  have hle := Xgrp_le_pCore hD (VRel D) (fun g _ _ h => VRel.conj hD g h) (fun _ _ h => h.symm)
    (fun _ _ _ h1 h2 => h1.trans h2) (fun _ => rfl)
    (fun a ha b hb hab c hc => vRel_mul_mem hD ha hb hab hc) 2
    (fun x hx => vXgrp_isPGroup hD hx) d hd
  exact hle (Subgroup.subset_closure ⟨v, hv.1, d, hd, hv.2, rfl, rfl⟩)

theorem vSet_subset_conjOrbit [Finite G] (hD : IsThreeTranspositions D)
    (htr : ∀ d ∈ D, ∀ e ∈ D, ∃ g : G, g * d * g⁻¹ = e) {d : G} (hd : d ∈ D) :
    vSet D d ⊆ conjOrbit (CFSG.pCore 2 G) d := by
  intro v hv
  by_cases hvd : v = d
  · exact ⟨1, one_mem _, by simp [hvd]⟩
  have hvD := hv.1
  have hdv : d * v = v * d := by
    have : v ∈ centralizerIn D d := by rw [← hv.2]; exact ⟨hvD, rfl⟩
    exact this.2.symm
  obtain ⟨a, haD, hda⟩ : ∃ a ∈ D, a * d ≠ d * a := by
    by_contra hcon
    push Not at hcon
    exact hvd (tt_eq_of_comm hD htr hd hvD hcon)
  have hav : a * v ≠ v * a := by
    intro h
    apply hda
    have h1 : a ∈ centralizerIn D v := ⟨haD, h⟩
    rw [hv.2] at h1
    exact h1.2
  have hs := tt_sigma4_conj hD haD hd hvD hdv (Ne.symm hda) (Ne.symm hav)
  have hdvN : d * v ∈ CFSG.pCore 2 G := by
    rw [hdv]
    exact vSet_mul_mem_pCore hD hd hv
  have hmem : a * d * v * a ∈ CFSG.pCore 2 G := by
    have := Subgroup.Normal.conj_mem inferInstance _ hdvN a
    rw [tt_inv_eq hD haD] at this
    simpa only [mul_assoc] using this
  exact ⟨a * d * v * a, hmem, hs.symm⟩

theorem conjOrbit_subset_vSet [Finite G] (hD : IsThreeTranspositions D) {d : G} (hd : d ∈ D) :
    conjOrbit (CFSG.pCore 2 G) d ⊆ vSet D d := by
  rintro _ ⟨m, hm, rfl⟩
  have hN : IsPGroup 2 (CFSG.pCore 2 G) := CFSG.pCore_isPGroup
  have ha : m * d * m⁻¹ ∈ D := tt_conj_mem hD hd m
  refine ⟨ha, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, hyc⟩
    refine ⟨hy, ?_⟩
    have := comm_conj_of_isPGroup_two hD (CFSG.pCore 2 G) hN (inv_mem hm) ha hy hyc
    rwa [show m⁻¹ * (m * d * m⁻¹) * m⁻¹⁻¹ = d by group] at this
  · rintro ⟨hy, hyc⟩
    exact ⟨hy, comm_conj_of_isPGroup_two hD (CFSG.pCore 2 G) hN hm hd hy hyc⟩

theorem vSet_eq_conjOrbit [Finite G] (hD : IsThreeTranspositions D)
    (htr : ∀ d ∈ D, ∀ e ∈ D, ∃ g : G, g * d * g⁻¹ = e) {d : G} (hd : d ∈ D) :
    vSet D d = conjOrbit (CFSG.pCore 2 G) d :=
  Set.Subset.antisymm (vSet_subset_conjOrbit hD htr hd) (conjOrbit_subset_vSet hD hd)

end CFSG.RankThree.PartOne.FIS
